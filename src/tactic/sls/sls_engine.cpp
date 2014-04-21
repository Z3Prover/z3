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
#include<iomanip>

#include"map.h"
#include"ast_smt2_pp.h"
#include"ast_pp.h"
#include"var_subst.h"
#include"model_pp.h"
#include"tactic.h"
#include"cooperate.h"
#include"luby.h"

#include"sls_compilation_settings.h"
#include"sls_params.hpp"
#include"sls_engine.h"


sls_engine::sls_engine(ast_manager & m, params_ref const & p) :
    m_manager(m),    
    m_powers(m_mpz_manager),
    m_zero(m_mpz_manager.mk_z(0)),
    m_one(m_mpz_manager.mk_z(1)),
    m_two(m_mpz_manager.mk_z(2)),
    m_cancel(false),
    m_bv_util(m),
    m_tracker(m, m_bv_util, m_mpz_manager, m_powers),
    m_evaluator(m, m_bv_util, m_tracker, m_mpz_manager, m_powers)
{
    updt_params(p);
}

sls_engine::~sls_engine() {
    m_mpz_manager.del(m_zero);
    m_mpz_manager.del(m_one);
    m_mpz_manager.del(m_two);
}

double sls_engine::get_restart_armin(unsigned cnt_restarts)
{
    unsigned outer_id = (unsigned)(0.5 + sqrt(0.25 + 2 * cnt_restarts));
    unsigned inner_id = cnt_restarts - (outer_id - 1) * outer_id / 2;
    return pow((double) _RESTART_CONST_ARMIN_, (int) inner_id + 1);
}    

void sls_engine::updt_params(params_ref const & _p) {
    sls_params p(_p);
    m_produce_models = _p.get_bool("model", false);
    m_max_restarts = p.restarts();
    m_tracker.set_random_seed(p.random_seed());
    m_plateau_limit = p.plateau_limit();
}

void sls_engine::checkpoint() {
    if (m_cancel)
        throw tactic_exception(TACTIC_CANCELED_MSG);
    cooperate("sls");
}

bool sls_engine::full_eval(model & mdl) {
    bool res = true;

    unsigned sz = m_assertions.size();
    for (unsigned i = 0; i < sz && res; i++) {
        checkpoint();
        expr_ref o(m_manager);

        if (!mdl.eval(m_assertions[i], o, true))
            exit(ERR_INTERNAL_FATAL);

        res = m_manager.is_true(o.get());
    }

    TRACE("sls", tout << "Evaluation: " << res << std::endl;);

    return res;
}

double sls_engine::top_score() {
    double top_sum = 0.0;
    unsigned sz = m_assertions.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * e = m_assertions[i];
        top_sum += m_tracker.get_score(e);
    }

    TRACE("sls_top", tout << "Score distribution:";
    for (unsigned i = 0; i < sz; i++)
        tout << " " << m_tracker.get_score(m_assertions[i]);
    tout << " AVG: " << top_sum / (double)sz << std::endl;);

#if _CACHE_TOP_SCORE_
    m_tracker.set_top_sum(top_sum);
#endif

    return top_sum / (double)sz;
}

double sls_engine::rescore() {
    m_evaluator.update_all();
    m_stats.m_full_evals++;
    return top_score();
}

double sls_engine::serious_score(func_decl * fd, const mpz & new_value) {
    m_evaluator.serious_update(fd, new_value);
    m_stats.m_incr_evals++;
#if _CACHE_TOP_SCORE_
    return (m_tracker.get_top_sum() / m_assertions.size());
#else
    return top_score();
#endif
}

double sls_engine::incremental_score(func_decl * fd, const mpz & new_value) {
    m_evaluator.update(fd, new_value);
    m_stats.m_incr_evals++;
#if _CACHE_TOP_SCORE_
    return (m_tracker.get_top_sum() / m_assertions.size());
#else
    return top_score();
#endif
}

double sls_engine::incremental_score_prune(func_decl * fd, const mpz & new_value) {
#if _EARLY_PRUNE_
    m_stats.m_incr_evals++;
    if (m_evaluator.update_prune(fd, new_value))
#if _CACHE_TOP_SCORE_
        return (m_tracker.get_top_sum() / m_assertions.size());
#else
        return top_score();
#endif
    else
        return 0.0;
#else
    NOT_IMPLEMENTED_YET();
#endif
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

#if _EARLY_PRUNE_
    double r = incremental_score_prune(fd, temp);
#else
    double r = incremental_score(fd, temp);
#endif   
#ifdef Z3DEBUG
    TRACE("sls_whatif", tout << "WHAT IF " << fd->get_name() << " WERE " << m_mpz_manager.to_string(temp) <<
            " --> " << r << std::endl;);

    m_mpz_manager.del(old_value);
#endif

    // Andreas: For some reason it is important to use > here instead of >=. Probably related to prefering the LSB.
    if (r > best_score) {
        m_tracker.reset_equal_scores();
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
#if _USE_ADDSUB_
        if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv = 2;
        if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv++;
        move_type mt = (move_type)rnd_mv;

        // inversion doesn't make sense, let's do a flip instead.
        if (mt == MV_INV) mt = MV_FLIP;
#else
        mt = MV_FLIP;
#endif
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

    m_evaluator.update(fd, new_value);
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

    m_tracker.reset_equal_scores();

    for (unsigned i = 0; i < to_evaluate.size(); i++) {
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
#if _USE_ADDSUB_
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
#endif
            // try inverting
            mk_inv(bv_sz, old_value, temp);
            if (what_if(fd, i, temp, new_score, best_const, best_value))
                move = MV_INV;
        }

        // reset to what it was before
        double check = incremental_score(fd, old_value);
        // Andreas: does not hold anymore now that we use top level score caching
        //SASSERT(check == score);
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

    for (unsigned i = 0; i < to_evaluate.size(); i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

        if (m_bv_util.is_bv_sort(srt) && bv_sz > 2) {
            for (unsigned j = 0; j < bv_sz; j++) {
                mk_flip(srt, old_value, j, temp);
                for (unsigned l = 0; l < _VNS_MC_TRIES_ && l < bv_sz / 2; l++)
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
        double check = incremental_score(fd, old_value);
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
    unsigned new_const = (unsigned)-1, new_bit = 0;
    mpz new_value;
    move_type move;
    unsigned plateau_cnt = 0;

    score = rescore();
    unsigned sz = m_assertions.size();

#if _RESTARTS_
    while (check_restart(m_stats.m_moves) && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#else
    while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#endif

        checkpoint();
        m_stats.m_moves++;

#if _UCT_FORGET_
        if (m_stats.m_moves % _UCT_FORGET_ == 0)
            m_tracker.uct_forget(g);
#endif

#if _REAL_RS_
        //m_tracker.debug_real(g, m_stats.m_moves);
#endif

#if _FOCUS_
        expr * e = m_tracker.get_unsat_assertion(m_assertions);

        if (!e)
        {
            res = l_true;
            goto bailout;
        }
        ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants_walksat(e);
#else
        ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants_gsat(m_assertions, sz);
        if (!to_evaluate.size())
        {
            res = l_true;
            goto bailout;
        }
#endif

        if (m_tracker.get_random_uint(16) % 1000 < _PERM_RSTEP_)
        {
            mk_random_move(to_evaluate);
#if _CACHE_TOP_SCORE_
            score = m_tracker.get_top_sum() / sz;
#else
            score = top_score(g);
#endif
            continue;
        }

        old_score = score;
        new_const = (unsigned)-1;
        move = MV_FLIP;
        new_bit = 0;

        score = find_best_move(to_evaluate, score, new_const, new_value, new_bit, move);

#if _VNS_MC_ > _VNS_REPICK_
#if _VNS_MC_
        if (new_const == static_cast<unsigned>(-1))
            score = find_best_move_mc(g, to_evaluate, score, new_const, new_value);
#endif
#if _VNS_REPICK_
        if (new_const == static_cast<unsigned>(-1))
        {
            expr * q = m_tracker.get_new_unsat_assertion(g, e);
            if (q)
            {
                ptr_vector<func_decl> & to_evaluate2 = m_tracker.get_unsat_constants_walksat(e);
                score = find_best_move(g, to_evaluate2, score, new_const, new_value, new_bit, move);
            }
        }
#endif
#endif

#if _VNS_MC_ < _VNS_REPICK_
#if _VNS_REPICK_
        if (new_const == static_cast<unsigned>(-1))
        {
            expr * q = m_tracker.get_new_unsat_assertion(g, e);
            if (q)
            {
                ptr_vector<func_decl> & to_evaluate2 = m_tracker.get_unsat_constants_walksat(e);
                score = find_best_move(g, to_evaluate2, score, new_const, new_value, new_bit, move);
            }
        }
#endif
#if _VNS_MC_
        if (new_const == static_cast<unsigned>(-1))
            score = find_best_move_mc(g, to_evaluate, score, new_const, new_value);
#endif
#endif

        if (new_const == static_cast<unsigned>(-1)) {
            score = old_score;
            plateau_cnt++;
#if _REPICK_
                m_evaluator.randomize_local(m_assertions);
#else
                m_evaluator.randomize_local(to_evaluate);
#endif

#if _CACHE_TOP_SCORE_
            score = m_tracker.get_top_sum() / m_assertions.size();
#else
            score = top_score(g);
#endif

#if _PAWS_
            for (unsigned i = 0; i < sz; i++)
            {
                expr * q = m_assertions[i];
                if (m_tracker.get_random_uint(16) % 100 < _PAWS_)
                {
                    if (m_mpz_manager.eq(m_tracker.get_value(q),m_one))
                        m_tracker.decrease_weight(q);
                }
                else
                {
                    if (m_mpz_manager.eq(m_tracker.get_value(q),m_zero))
                        m_tracker.increase_weight(q);
                }
            }
#endif

        }
        else {
            func_decl * fd = to_evaluate[new_const];
#if _REAL_RS_ || _PAWS_
            score = serious_score(fd, new_value);
#else
            score = incremental_score(fd, new_value);
#endif
        }
    }

bailout:
    m_mpz_manager.del(new_value);

    return res;
}

void sls_engine::operator()(goal_ref const & g, model_converter_ref & mc) {
    if (g->inconsistent()) {
        mc = 0;
        return;
    }

    m_produce_models = g->models_enabled();

    for (unsigned i = 0; i < g->size(); i++)
        assert_expr(g->form(i));    

    verbose_stream() << "_FOCUS_ " << _FOCUS_ << std::endl;
    verbose_stream() << "_RESTARTS_ " << _RESTARTS_ << std::endl;
    verbose_stream() << "_RESTART_LIMIT_ " << _RESTART_LIMIT_ << std::endl;
    verbose_stream() << "_RESTART_INIT_ " << _RESTART_INIT_ << std::endl;
    verbose_stream() << "_RESTART_SCHEME_ " << _RESTART_SCHEME_ << std::endl;
    verbose_stream() << "_TIMELIMIT_ " << _TIMELIMIT_ << std::endl;
    verbose_stream() << "_PAWS_ " << _PAWS_ << std::endl;
    verbose_stream() << "_PAWS_INIT_ " << _PAWS_INIT_ << std::endl;
    verbose_stream() << "_VNS_MC_ " << _VNS_MC_ << std::endl;
    verbose_stream() << "_VNS_MC_TRIES_ " << _VNS_MC_TRIES_ << std::endl;
    verbose_stream() << "_VNS_REPICK_ " << _VNS_REPICK_ << std::endl;
    verbose_stream() << "_WEIGHT_DIST_ " << _WEIGHT_DIST_ << std::endl;
    verbose_stream() << "_WEIGHT_DIST_FACTOR_ " << std::fixed << std::setprecision(2) << _WEIGHT_DIST_FACTOR_ << std::endl;
    verbose_stream() << "_REPICK_ " << _REPICK_ << std::endl;
    verbose_stream() << "_UCT_ " << _UCT_ << std::endl;
    verbose_stream() << "_UCT_CONSTANT_ " << std::fixed << std::setprecision(2) << _UCT_CONSTANT_ << std::endl;
    verbose_stream() << "_UCT_INIT_ " << _UCT_INIT_ << std::endl;
    verbose_stream() << "_UCT_FORGET_ " << _UCT_FORGET_ << std::endl;
    verbose_stream() << "_UCT_FORGET_FACTOR_ " << std::fixed << std::setprecision(2) << _UCT_FORGET_FACTOR_ << std::endl;
    verbose_stream() << "_USE_ADDSUB_ " << _USE_ADDSUB_ << std::endl;
    verbose_stream() << "_REAL_RS_ " << _REAL_RS_ << std::endl;
    verbose_stream() << "_PERM_RSTEP_ " << _PERM_RSTEP_ << std::endl;
    verbose_stream() << "_EARLY_PRUNE_ " << _EARLY_PRUNE_ << std::endl;
    verbose_stream() << "_CACHE_TOP_SCORE_ " << _CACHE_TOP_SCORE_ << std::endl;    

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
        mc = 0;
}

lbool sls_engine::operator()() {
    m_tracker.initialize(m_assertions);
    lbool res = l_undef;

    m_restart_limit = _RESTART_LIMIT_;

    do {
        checkpoint();

        report_tactic_progress("Searching... restarts left:", m_max_restarts - m_stats.m_restarts);
        res = search();

        if (res == l_undef)
        {
#if _RESTART_INIT_
            m_tracker.randomize();
#else
            m_tracker.reset(m_assertions);
#endif
        }
    } while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_ && res != l_true && m_stats.m_restarts++ < m_max_restarts);

    verbose_stream() << "(restarts: " << m_stats.m_restarts << " flips: " << m_stats.m_moves << " time: " << std::fixed << std::setprecision(2) << m_stats.m_stopwatch.get_current_seconds() << " fps: " << (m_stats.m_moves / m_stats.m_stopwatch.get_current_seconds()) << ")" << std::endl;
    
    return res;
}

unsigned sls_engine::check_restart(unsigned curr_value)
{
    if (curr_value > m_restart_limit)
    {
#if _RESTART_SCHEME_ == 5
        m_restart_limit += (unsigned)(_RESTART_LIMIT_ * pow(_RESTART_CONST_ARMIN_, m_stats.m_restarts));
#elif _RESTART_SCHEME_ == 4
        m_restart_limit += (m_stats.m_restarts & (m_stats.m_restarts + 1)) ? _RESTART_LIMIT_ : (_RESTART_LIMIT_ * m_stats.m_restarts + 1);
#elif _RESTART_SCHEME_ == 3
        m_restart_limit += (unsigned)get_restart_armin(m_stats.m_restarts + 1) * _RESTART_LIMIT_;
#elif _RESTART_SCHEME_ == 2
        m_restart_limit += get_luby(m_stats.m_restarts + 1) * _RESTART_LIMIT_;
#elif _RESTART_SCHEME_ == 1
        if (m_stats.m_restarts & 1)
            m_restart_limit += _RESTART_LIMIT_;
        else
            m_restart_limit += (2 << (m_stats.m_restarts >> 1)) * _RESTART_LIMIT_;
#else
        m_restart_limit += _RESTART_LIMIT_;
#endif
        return 0;
    }
    return 1;
}
