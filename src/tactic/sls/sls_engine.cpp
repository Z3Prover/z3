/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_engine.cpp

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Christoph (cwinter) 2014-03-19

Notes:

--*/
#include<float.h> // Need DBL_MAX

#include "util/map.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"
#include "model/model_pp.h"
#include "tactic/tactic.h"
#include "util/luby.h"

#include "tactic/sls/sls_params.hpp"
#include "tactic/sls/sls_engine.h"


sls_engine::sls_engine(ast_manager & m, params_ref const & p) :
    m_manager(m),    
    m_powers(m_mpz_manager),
    m_zero(m_mpz_manager.mk_z(0)),
    m_one(m_mpz_manager.mk_z(1)),
    m_two(m_mpz_manager.mk_z(2)),
    m_bv_util(m),
    m_tracker(m, m_bv_util, m_mpz_manager, m_powers),
    m_evaluator(m, m_bv_util, m_tracker, m_mpz_manager, m_powers)
{
    updt_params(p);
    m_tracker.updt_params(p);
}

sls_engine::~sls_engine() {
    m_mpz_manager.del(m_zero);
    m_mpz_manager.del(m_one);
    m_mpz_manager.del(m_two);
}

void sls_engine::updt_params(params_ref const & _p) {
    sls_params p(_p);
    m_produce_models = _p.get_bool("model", false);
    m_max_restarts = p.max_restarts();
    m_tracker.set_random_seed(p.random_seed());
    m_walksat = p.walksat();
    m_walksat_repick = p.walksat_repick();
    m_paws_sp = p.paws_sp();
    m_paws = m_paws_sp < 1024;
    m_wp = p.wp();
    m_vns_mc = p.vns_mc();
    m_vns_repick = p.vns_repick();

    m_restart_base = p.restart_base();
    m_restart_next = m_restart_base;
    m_restart_init = p.restart_init();

    m_early_prune = p.early_prune();
    m_random_offset = p.random_offset();
    m_rescore = p.rescore();

    // Andreas: Would cause trouble because repick requires an assertion being picked before which is not the case in GSAT.
    if (m_walksat_repick && !m_walksat)
        NOT_IMPLEMENTED_YET();
    if (m_vns_repick && !m_walksat)
        NOT_IMPLEMENTED_YET();
}

void sls_engine::collect_statistics(statistics& st) const {
    double seconds = m_stats.m_stopwatch.get_current_seconds();            
    st.update("sls restarts", m_stats.m_restarts);
    st.update("sls full evals", m_stats.m_full_evals);
    st.update("sls incr evals", m_stats.m_incr_evals);
    st.update("sls incr evals/sec", m_stats.m_incr_evals / seconds);
    st.update("sls FLIP moves", m_stats.m_flips);
    st.update("sls INC moves", m_stats.m_incs);
    st.update("sls DEC moves", m_stats.m_decs);
    st.update("sls INV moves", m_stats.m_invs);
    st.update("sls moves", m_stats.m_moves);
    st.update("sls moves/sec", m_stats.m_moves / seconds);
}

void sls_engine::checkpoint() {
    if (m_manager.canceled())
        throw tactic_exception(m_manager.limit().get_cancel_msg());
}

bool sls_engine::full_eval(model & mdl) {
    model::scoped_model_completion _scm(mdl, true);
    for (expr* a : m_assertions) {
        checkpoint();        
        if (!mdl.is_true(a)) {
            TRACE("sls", tout << "Evaluation: false\n";);
            return false;
        }
    }    
    return true;
}

double sls_engine::top_score() {
    double top_sum = 0.0;
    for (expr* e : m_assertions) {
        top_sum += m_tracker.get_score(e);
    }

    TRACE("sls_top", tout << "Score distribution:";
          for (expr* e : m_assertions) 
              tout << " " << m_tracker.get_score(e);
          tout << " AVG: " << top_sum / (double)m_assertions.size() << std::endl;);

    m_tracker.set_top_sum(top_sum);

    return top_sum;
}

double sls_engine::rescore() {
    m_evaluator.update_all();
    m_stats.m_full_evals++;
    return top_score();
}

double sls_engine::serious_score(func_decl * fd, const mpz & new_value) {
    m_evaluator.serious_update(fd, new_value);
    m_stats.m_incr_evals++;
    return m_tracker.get_top_sum();
}

double sls_engine::incremental_score(func_decl * fd, const mpz & new_value) {
    m_evaluator.update(fd, new_value);
    m_stats.m_incr_evals++;
    return m_tracker.get_top_sum();
}

double sls_engine::incremental_score_prune(func_decl * fd, const mpz & new_value) {
    m_stats.m_incr_evals++;
    if (m_evaluator.update_prune(fd, new_value))
        return m_tracker.get_top_sum();
    else
        return -DBL_MAX;
}

// checks whether the score outcome of a given move is better than the previous score
bool sls_engine::what_if(
    func_decl * fd, 
    const unsigned & fd_inx, 
    const mpz & temp,
    double & best_score, 
    unsigned & best_const, 
    mpz & best_value) {

#ifdef Z3DEBUG
    mpz old_value;
    m_mpz_manager.set(old_value, m_tracker.get_value(fd));
#endif

    double r;
    if (m_early_prune)
        r = incremental_score_prune(fd, temp);
    else
        r = incremental_score(fd, temp);
#ifdef Z3DEBUG
    TRACE("sls_whatif", tout << "WHAT IF " << fd->get_name() << " WERE " << m_mpz_manager.to_string(temp) <<
            " --> " << r << std::endl;);

    m_mpz_manager.del(old_value);
#endif

    // Andreas: Had this idea on my last day. Maybe we could add a noise here similar to the one that worked so well for ucb assertion selection.
    // r += 0.0001 * m_tracker.get_random_uint(8);

    // Andreas: For some reason it is important to use > here instead of >=. Probably related to preferring the LSB.
    if (r > best_score) {
        best_score = r;
        best_const = fd_inx;
        m_mpz_manager.set(best_value, temp);
        return true;
    }

    return false;
}

void sls_engine::mk_add(unsigned bv_sz, const mpz & old_value, mpz & add_value, mpz & result) {
    mpz temp, mask, mask2;
    m_mpz_manager.add(old_value, add_value, temp);
    m_mpz_manager.set(mask, m_powers(bv_sz));
    m_mpz_manager.bitwise_not(bv_sz, mask, mask2);
    m_mpz_manager.bitwise_and(temp, mask2, result);
    m_mpz_manager.del(temp);
    m_mpz_manager.del(mask);
    m_mpz_manager.del(mask2);

}

void sls_engine::mk_inc(unsigned bv_sz, const mpz & old_value, mpz & incremented) {
    unsigned shift;
    m_mpz_manager.add(old_value, m_one, incremented);
    if (m_mpz_manager.is_power_of_two(incremented, shift) && shift == bv_sz)
        m_mpz_manager.set(incremented, m_zero);
}

void sls_engine::mk_dec(unsigned bv_sz, const mpz & old_value, mpz & decremented) {
    if (m_mpz_manager.is_zero(old_value)) {
        m_mpz_manager.set(decremented, m_powers(bv_sz));
        m_mpz_manager.dec(decremented);
    }
    else
        m_mpz_manager.sub(old_value, m_one, decremented);
}

void sls_engine::mk_inv(unsigned bv_sz, const mpz & old_value, mpz & inverted) {
    m_mpz_manager.bitwise_not(bv_sz, old_value, inverted);
}

void sls_engine::mk_flip(sort * s, const mpz & old_value, unsigned bit, mpz & flipped) {
    m_mpz_manager.set(flipped, m_zero);

    if (m_bv_util.is_bv_sort(s)) {
        mpz mask;
        m_mpz_manager.set(mask, m_powers(bit));
        m_mpz_manager.bitwise_xor(old_value, mask, flipped);
        m_mpz_manager.del(mask);
    }
    else if (m_manager.is_bool(s))
        m_mpz_manager.set(flipped, (m_mpz_manager.is_zero(old_value)) ? m_one : m_zero);
    else
        NOT_IMPLEMENTED_YET();
}

void sls_engine::mk_random_move(ptr_vector<func_decl> & unsat_constants)
{
    unsigned rnd_mv = 0;
    unsigned ucc = unsat_constants.size();
    unsigned rc = (m_tracker.get_random_uint((ucc < 16) ? 4 : (ucc < 256) ? 8 : (ucc < 4096) ? 12 : (ucc < 65536) ? 16 : 32)) % ucc;
    func_decl * fd = unsat_constants[rc];

    mpz new_value;

    sort * srt = fd->get_range();
    if (m_manager.is_bool(srt))
        m_mpz_manager.set(new_value, (m_mpz_manager.is_zero(m_tracker.get_value(fd))) ? m_one : m_zero);
    else
    {
        if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv = 2;
        if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv++;

        // Andreas: The other option would be to scale the probability for flips according to the bit-width.
        /* unsigned bv_sz2 = m_bv_util.get_bv_size(srt);
        rnd_mv = m_tracker.get_random_uint(16) % (bv_sz2 + 3);
        if (rnd_mv > 3) rnd_mv = 0; */

        move_type mt = (move_type)rnd_mv;

        // Andreas: Christoph claimed inversion doesn't make sense, let's do a flip instead. Is this really true?
        if (mt == MV_INV) mt = MV_FLIP;
        unsigned bit = 0;

        switch (mt)
        {
        case MV_FLIP: {
            unsigned bv_sz = m_bv_util.get_bv_size(srt);
            bit = (m_tracker.get_random_uint((bv_sz < 16) ? 4 : (bv_sz < 256) ? 8 : (bv_sz < 4096) ? 12 : (bv_sz < 65536) ? 16 : 32)) % bv_sz;
            mk_flip(fd->get_range(), m_tracker.get_value(fd), bit, new_value);
            break;
        }
        case MV_INC:
            mk_inc(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
            break;
        case MV_DEC:
            mk_dec(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
            break;
        case MV_INV:
            mk_inv(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
            break;
        default:
            NOT_IMPLEMENTED_YET();
        }

        TRACE("sls", tout << "Randomization candidates: ";
        for (unsigned i = 0; i < unsat_constants.size(); i++)
            tout << unsat_constants[i]->get_name() << ", ";
        tout << std::endl;
        tout << "Random move: ";
        switch (mt) {
        case MV_FLIP: tout << "Flip #" << bit << " in " << fd->get_name() << std::endl; break;
        case MV_INC: tout << "+1 for " << fd->get_name() << std::endl; break;
        case MV_DEC: tout << "-1 for " << fd->get_name() << std::endl; break;
        case MV_INV: tout << "NEG for " << fd->get_name() << std::endl; break;
        }
        tout << "Locally randomized model: " << std::endl; m_tracker.show_model(tout););
    }

    m_evaluator.serious_update(fd, new_value);
    m_mpz_manager.del(new_value);
}

// finds the move that increased score the most. returns best_const = -1, if no increasing move exists.
double sls_engine::find_best_move(
    ptr_vector<func_decl> & to_evaluate, 
    double score,
    unsigned & best_const, 
    mpz & best_value, 
    unsigned & new_bit, 
    move_type & move) 
{
    mpz old_value, temp;
    unsigned bv_sz;
    double new_score = score;

    // Andreas: Introducting a bit of randomization by using a random offset and a random direction to go through the candidate list.
    unsigned sz = to_evaluate.size();
    unsigned offset = (m_random_offset) ? m_tracker.get_random_uint(16) % sz : 0;
    for (unsigned j = 0; j < sz; j++) {
        unsigned i = j + offset;
        if (i >= sz) i -= sz;
    //for (unsigned i = 0; i < to_evaluate.size(); i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

        // first try to flip every bit
        for (unsigned j = 0; j < bv_sz; j++) {
            // What would happen if we flipped bit #i ?                
            mk_flip(srt, old_value, j, temp);

            if (what_if(fd, i, temp, new_score, best_const, best_value)) {
                new_bit = j;
                move = MV_FLIP;
            }
        }

        if (m_bv_util.is_bv_sort(srt) && bv_sz > 1) {
            if (!m_mpz_manager.is_even(old_value)) {
                // for odd values, try +1
                mk_inc(bv_sz, old_value, temp);
                if (what_if(fd, i, temp, new_score, best_const, best_value))
                    move = MV_INC;
            }
            else {
                // for even values, try -1
                mk_dec(bv_sz, old_value, temp);
                if (what_if(fd, i, temp, new_score, best_const, best_value))
                    move = MV_DEC;
            }
            // try inverting
            mk_inv(bv_sz, old_value, temp);
            if (what_if(fd, i, temp, new_score, best_const, best_value))
                move = MV_INV;
        }
        // reset to what it was before
        incremental_score(fd, old_value);
    }

    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);

    return new_score;
}

// finds the move that increased score the most. returns best_const = -1, if no increasing move exists.
double sls_engine::find_best_move_mc(ptr_vector<func_decl> & to_evaluate, double score,
                        unsigned & best_const, mpz & best_value) {
    mpz old_value, temp, temp2;
    unsigned bv_sz;
    double new_score = score;

    // Andreas: Introducting a bit of randomization by using a random offset and a random direction to go through the candidate list.
    unsigned sz = to_evaluate.size();
    unsigned offset = (m_random_offset) ? m_tracker.get_random_uint(16) % sz : 0;
    for (unsigned j = 0; j < sz; j++) {
        unsigned i = j + offset;
        if (i >= sz) i -= sz;
    //for (unsigned i = 0; i < to_evaluate.size(); i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

        if (m_bv_util.is_bv_sort(srt) && bv_sz > 2) {
            for (unsigned j = 0; j < bv_sz; j++) {
                mk_flip(srt, old_value, j, temp);
                for (unsigned l = 0; l < m_vns_mc && l < bv_sz / 2; l++)
                {
                    unsigned k = m_tracker.get_random_uint(16) % bv_sz;
                    while (k == j)
                        k = m_tracker.get_random_uint(16) % bv_sz;
                    mk_flip(srt, temp, k, temp2);
                    what_if(fd, i, temp2, new_score, best_const, best_value);
                }
            }
        }
        // reset to what it was before
        incremental_score(fd, old_value);
    }

    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);
    m_mpz_manager.del(temp2);

    return new_score;
}

// main search loop
lbool sls_engine::search() {
    lbool res = l_undef;
    double score = 0.0, old_score = 0.0;
    unsigned new_const = (unsigned)-1, new_bit;
    mpz new_value;
    move_type move;

    score = rescore();
    unsigned sz = m_assertions.size();

    while (check_restart(m_stats.m_moves)) {
        checkpoint();
        m_stats.m_moves++;

        // Andreas: Every base restart interval ...
        if (m_stats.m_moves % m_restart_base == 0)
        {
            // ... potentially smooth the touched counters ...
            m_tracker.ucb_forget(m_assertions);
            // ... or normalize the top-level score.
            if (m_rescore) score = rescore();
        }

        // get candidate variables
        ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants(m_assertions);
        if (to_evaluate.empty())
        {
            res = l_true;
            goto bailout;
        }

        // random walk with probability wp / 1024
        if (m_wp && m_tracker.get_random_uint(10) < m_wp)
        {
            mk_random_move(to_evaluate);
            score = m_tracker.get_top_sum();
            continue;
        }

        old_score = score;
        new_const = (unsigned)-1;

        // find best increasing move
        score = find_best_move(to_evaluate, score, new_const, new_value, new_bit, move);

        // use Monte Carlo 2-bit-flip sampling if no increasing move was found previously
        if (m_vns_mc && (new_const == static_cast<unsigned>(-1)))
            score = find_best_move_mc(to_evaluate, score, new_const, new_value);
   
        // repick assertion if no increasing move was found previously
        if (m_vns_repick && (new_const == static_cast<unsigned>(-1)))
        {
            expr * q = m_tracker.get_new_unsat_assertion(m_assertions);
            // only apply if another unsatisfied assertion actually exists
            if (q)
            {
                ptr_vector<func_decl> & to_evaluate2 = m_tracker.get_unsat_constants_walksat(q);
                score = find_best_move(to_evaluate2, score, new_const, new_value, new_bit, move);

                if (new_const != static_cast<unsigned>(-1)) {
                    func_decl * fd = to_evaluate2[new_const];
                    score = serious_score(fd, new_value);
                    continue;
                }
            }
        }

        // randomize if no increasing move was found
        if (new_const == static_cast<unsigned>(-1)) {
            score = old_score;
            if (m_walksat_repick)
                m_evaluator.randomize_local(m_assertions);
            else
                m_evaluator.randomize_local(to_evaluate);

            score = m_tracker.get_top_sum();

            // update assertion weights if a weighting is enabled (sp < 1024)
            if (m_paws)
            {
                for (unsigned i = 0; i < sz; i++)
                {
                    expr * q = m_assertions[i];
                    // smooth weights with probability sp / 1024
                    if (m_tracker.get_random_uint(10) < m_paws_sp)
                    {
                        if (m_mpz_manager.eq(m_tracker.get_value(q),m_one))
                            m_tracker.decrease_weight(q);
                    }
                    // increase weights otherwise
                    else
                    {
                        if (m_mpz_manager.eq(m_tracker.get_value(q),m_zero))
                            m_tracker.increase_weight(q);
                    }
                }
            }
        }
        // otherwise, apply most increasing move
        else {
            func_decl * fd = to_evaluate[new_const];
            score = serious_score(fd, new_value);
        }
    }

bailout:
    m_mpz_manager.del(new_value);

    return res;
}

void sls_engine::operator()(goal_ref const & g, model_converter_ref & mc) {
    if (g->inconsistent()) {
        mc = nullptr;
        return;
    }

    m_produce_models = g->models_enabled();

    for (unsigned i = 0; i < g->size(); i++)
        assert_expr(g->form(i));    

    lbool res = operator()();

    if (res == l_true) {
        report_tactic_progress("Number of flips:", m_stats.m_moves);
        for (unsigned i = 0; i < g->size(); i++)
            if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
            {
                verbose_stream() << "Terminated before all assertions were SAT!" << std::endl;
                NOT_IMPLEMENTED_YET();
            }

        if (m_produce_models) {
            model_ref mdl = m_tracker.get_model();
            mc = model2model_converter(mdl.get());
            TRACE("sls_model", mc->display(tout););
        }
        g->reset();
    }
    else
        mc = nullptr;
}

lbool sls_engine::operator()() {    
    m_tracker.initialize(m_assertions);
    m_tracker.reset(m_assertions);
    if (m_restart_init)
        m_tracker.randomize(m_assertions);

    lbool res = l_undef;

    do {
        checkpoint();

        report_tactic_progress("Searching... restarts left:", m_max_restarts - m_stats.m_restarts);
        res = search();

        if (res == l_undef)
        {
            if (m_restart_init)
                m_tracker.randomize(m_assertions);
            else
                m_tracker.reset(m_assertions);
        }
    } while (res != l_true && m_stats.m_restarts++ < m_max_restarts);

    verbose_stream() << "(restarts: " << m_stats.m_restarts << " flips: " << m_stats.m_moves << " fps: " << (m_stats.m_moves / m_stats.m_stopwatch.get_current_seconds()) << ")" << std::endl;
    
    return res;
}

/* Andreas: Needed for Armin's restart scheme if we don't want to use loops.
double sls_engine::get_restart_armin(unsigned cnt_restarts)
{
    unsigned outer_id = (unsigned)(0.5 + sqrt(0.25 + 2 * cnt_restarts));
    unsigned inner_id = cnt_restarts - (outer_id - 1) * outer_id / 2;
    return pow((double) _RESTART_CONST_ARMIN_, (int) inner_id + 1);
}    
*/

unsigned sls_engine::check_restart(unsigned curr_value)
{
    if (curr_value > m_restart_next)
    {
        /* Andreas: My own scheme (= 1) seems to work best. Other schemes are disabled so that we save one parameter.
        I leave the other versions as comments in case you want to try it again somewhen.
#if _RESTART_SCHEME_ == 5
        m_restart_next += (unsigned)(m_restart_base * pow(_RESTART_CONST_ARMIN_, m_stats.m_restarts));
#elif _RESTART_SCHEME_ == 4
        m_restart_next += (m_stats.m_restarts & (m_stats.m_restarts + 1)) ? m_restart_base : (m_restart_base * m_stats.m_restarts + 1);
#elif _RESTART_SCHEME_ == 3
        m_restart_next += (unsigned)get_restart_armin(m_stats.m_restarts + 1) * m_restart_base;
#elif _RESTART_SCHEME_ == 2
        m_restart_next += get_luby(m_stats.m_restarts + 1) * m_restart_base;
#elif _RESTART_SCHEME_ == 1
        if (m_stats.m_restarts & 1)
            m_restart_next += m_restart_base;
        else
            m_restart_next += (2 << (m_stats.m_restarts >> 1)) * m_restart_base;
#else
        m_restart_limit += m_restart_base;
#endif  */
        if (m_stats.m_restarts & 1)
            m_restart_next += m_restart_base;
        else
            m_restart_next += (2 << (m_stats.m_restarts >> 1)) * m_restart_base;
        return 0;
    }
    return 1;
}
