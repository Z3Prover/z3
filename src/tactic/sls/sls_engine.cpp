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
    //printf("armin: %f\n", pow(1.1, inner_id + 1));
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
#if 0
    double min = m_tracker.get_score(g->form(0));
    unsigned sz = g->size();
    for (unsigned i = 1; i < sz; i++) {
        double q = m_tracker.get_score(g->form(i));
        if (q < min) min = q;
    }
    TRACE("sls_top", tout << "Score distribution:";
    for (unsigned i = 0; i < sz; i++)
        tout << " " << m_tracker.get_score(g->form(i));
    tout << " MIN: " << min << std::endl;);
    return min;
#else
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
#endif
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

    //            if (r >= best_score) {
    if (r > best_score) {
        best_score = r;
        best_const = fd_inx;
        m_mpz_manager.set(best_value, temp);
        return true;
    }

    return false;
}

// same as what_if, but only applied to the score of a specific atom, not the total score
bool sls_engine::what_if_local(
    expr * e, 
    func_decl * fd, 
    const unsigned & fd_inx, 
    const mpz & temp,
    double & best_score, 
    unsigned & best_const, 
    mpz & best_value) 
{
    m_evaluator.update(fd, temp);
    double r = m_tracker.get_score(e);
    if (r >= best_score) {
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

// Andreas: do we really need all those temporary mpzs?
void sls_engine::mk_mul2(unsigned bv_sz, const mpz & old_value, mpz & result) {
    mpz temp, mask, mask2;
    m_mpz_manager.mul(old_value, m_two, temp);
    m_mpz_manager.set(mask, m_powers(bv_sz));
    m_mpz_manager.bitwise_not(bv_sz, mask, mask2);
    m_mpz_manager.bitwise_and(temp, mask2, result);
    m_mpz_manager.del(temp);
    m_mpz_manager.del(mask);
    m_mpz_manager.del(mask2);
}

void sls_engine::mk_div2(unsigned bv_sz, const mpz & old_value, mpz & result) {
    m_mpz_manager.div(old_value, m_two, result);
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

void sls_engine::mk_random_move() {
    mk_random_move(m_tracker.get_unsat_constants(m_assertions, m_stats.m_moves));
}

// will use VNS to ignore some possible moves and increase the flips per second
double sls_engine::find_best_move_vns(
    ptr_vector<func_decl> & to_evaluate, 
    double score,
    unsigned & best_const, 
    mpz & best_value, 
    unsigned & new_bit, 
    move_type & move) 
{
    mpz old_value, temp;
    unsigned bv_sz, max_bv_sz = 0;
    double new_score = score;

    for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0; i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        if (max_bv_sz < bv_sz) max_bv_sz = bv_sz;
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

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

            // try to flip lsb
            mk_flip(srt, old_value, 0, temp);
            if (what_if(fd, i, temp, new_score, best_const, best_value)) {
                new_bit = 0;
                move = MV_FLIP;
            }
        }

        // reset to what it was before
        double check = incremental_score(fd, old_value);
        SASSERT(check == score);
    }

    // we can either check the condition once in the beginning or check it repeatedly after every bit
#if _VNS_ == 1
    for (unsigned j = 1; j < max_bv_sz && new_score <= score; j++)
#else
    if (new_score <= score)
        for (unsigned j = 1; j < max_bv_sz && new_score < 1.0; j++)
#endif
            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                // What would happen if we flipped bit #j ?                
                if (j < bv_sz)
                {
                    mk_flip(srt, old_value, j, temp);

                    if (what_if(fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = j;
                        move = MV_FLIP;
                    }
                }
                // reset to what it was before
                double check = incremental_score(fd, old_value);
                SASSERT(check == score);
            }
    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);
    return new_score;
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
#if _USE_MUL3_ || _USE_UNARY_MINUS_
    mpz temp2;
#endif
    unsigned bv_sz;
    double new_score = score;

    for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0; i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

        // first try to flip every bit
#if _SKIP_BITS_
        for (unsigned j = (i + m_stats.m_moves) % (_SKIP_BITS_ + 1); j < bv_sz && new_score < 1.0; j += (_SKIP_BITS_ + 1)) {
#else
        for (unsigned j = 0; j < bv_sz && new_score < 1.0; j++) {
#endif
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

#if _USE_UNARY_MINUS_
            mk_inc(bv_sz, temp, temp2);
            if (what_if(g, fd, i, temp2, new_score, best_const, best_value))
                move = MV_UMIN;
#endif

#if _USE_MUL2DIV2_
            // try multiplication by 2
            mk_mul2(bv_sz, old_value, temp);
            if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                move = MV_MUL2;

#if _USE_MUL3_
            // try multiplication by 3
            mk_add(bv_sz, old_value, temp, temp2);
            if (what_if(g, fd, i, temp2, new_score, best_const, best_value))
                move = MV_MUL3;
#endif

            // try division by 2
            mk_div2(bv_sz, old_value, temp);
            if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                move = MV_DIV2;
#endif
        }

        // reset to what it was before
        double check = incremental_score(fd, old_value);
        // Andreas: does not hold anymore now that we use top level score caching
        //SASSERT(check == score);
    }

    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);
#if _USE_MUL3_
    m_mpz_manager.del(temp2);
#endif
    return new_score;
}

// same as find_best_move but only considers the score of the current expression instead of the overall score
double sls_engine::find_best_move_local(expr * e, ptr_vector<func_decl> & to_evaluate,
                            unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move) {
    mpz old_value, temp;
    unsigned bv_sz;
    double new_score = m_tracker.get_score(e);
    // Andreas: tie breaking not implemented yet
    // double tie_score = top_score(g);
    for (unsigned i = 0; i < to_evaluate.size(); i++) {
        func_decl * fd = to_evaluate[i];
        sort * srt = fd->get_range();
        bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
        m_mpz_manager.set(old_value, m_tracker.get_value(fd));

        // first try to flip every bit
        for (unsigned j = 0; j < bv_sz; j++) {
            // What would happen if we flipped bit #i ?                
            mk_flip(srt, old_value, j, temp);

            if (what_if_local(e, fd, i, temp, new_score, best_const, best_value)) {
                new_bit = j;
                move = MV_FLIP;
            }
        }

        if (m_bv_util.is_bv_sort(srt) && bv_sz > 1) {
            if (!m_mpz_manager.is_even(old_value)) {
                // for odd values, try +1
                mk_inc(bv_sz, old_value, temp);
                if (what_if_local(e, fd, i, temp, new_score, best_const, best_value))
                    move = MV_INC;
            }
            else {
                // for even values, try -1
                mk_dec(bv_sz, old_value, temp);
                if (what_if_local(e, fd, i, temp, new_score, best_const, best_value))
                    move = MV_DEC;
            }

            // try inverting
            mk_inv(bv_sz, old_value, temp);
            if (what_if_local(e, fd, i, temp, new_score, best_const, best_value))
                move = MV_INV;
        }

        // reset to what it was before
        m_evaluator.update(fd, old_value);
    }

    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);
    return new_score;
}

// first try of intensification ... does not seem to be efficient
bool sls_engine::handle_plateau()
{
    unsigned sz = m_assertions.size();
#if _BFS_
    unsigned pos = m_stats.m_moves % sz;
#else
    unsigned pos = m_tracker.get_random_uint(16) % sz;
#endif
    expr * e = m_tracker.get_unsat_assertion(sz, pos);
    if (!e)
        return 0;

    expr * q = m_tracker.get_unsat_expression(e);
    ptr_vector<func_decl> & to_evaluate = m_tracker.get_constants(q);
    for (unsigned i = 0; i < to_evaluate.size(); i++)
    {
        m_tracker.get_value(to_evaluate[i]);
        m_old_values.push_back(&m_tracker.get_value(to_evaluate[i]));
    }
    unsigned new_const = (unsigned)-1, new_bit = 0;
    mpz new_value;
    move_type move;
    for (unsigned i = 0; i < _INTENSIFICATION_TRIES_; i++)
    {
        // Andreas: Could be extended to use (best) score but this is computationally more expensive.
        find_best_move_local(q, to_evaluate, new_const, new_value, new_bit, move);

        if (new_const == static_cast<unsigned>(-1)) {
            // Andreas: Actually this should never happen.
            NOT_IMPLEMENTED_YET();
        }
        else {
            m_stats.m_moves++;
            func_decl * fd = to_evaluate[new_const];

            switch (move) {
            case MV_FLIP: m_stats.m_flips++; break;
            case MV_INC: m_stats.m_incs++; break;
            case MV_DEC: m_stats.m_decs++; break;
            case MV_INV: m_stats.m_invs++; break;
            case MV_UMIN: m_stats.m_umins++; break;
            case MV_MUL2: m_stats.m_mul2s++; break;
            case MV_MUL3: m_stats.m_mul3s++; break;
            case MV_DIV2: m_stats.m_div2s++; break;
            }

            m_evaluator.update(fd, new_value);
        }

        if (m_mpz_manager.is_one(m_tracker.get_value(q)))
            return 1;
    }

    for (unsigned i = 0; i < to_evaluate.size(); i++)
        m_tracker.set_value(to_evaluate[i], *m_old_values[i]);

    m_old_values.reset();

    return 0;
}

// what_if version needed in the context of 2nd intensification try, combining local and global score
bool sls_engine::what_if(
    expr * e, 
    func_decl * fd, 
    const mpz & temp,
    double & best_score, 
    mpz & best_value, 
    unsigned i) 
{
    double global_score = incremental_score(fd, temp);
    double local_score = m_tracker.get_score(e);
    double new_score = i * local_score / _INTENSIFICATION_TRIES_ + (_INTENSIFICATION_TRIES_ - i) * global_score / _INTENSIFICATION_TRIES_;

    if (new_score >= best_score) {
        best_score = new_score;
        m_mpz_manager.set(best_value, temp);
        return true;
    }

    return false;
}

// find_best_move version needed in the context of 2nd intensification try
double sls_engine::find_best_move_local(expr * e, func_decl * fd, mpz & best_value, unsigned i)
{
    mpz old_value, temp;
    double best_score = 0;

    sort * srt = fd->get_range();
    unsigned bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
    m_mpz_manager.set(old_value, m_tracker.get_value(fd));

    for (unsigned j = 0; j < bv_sz && best_score < 1.0; j++) {
        mk_flip(srt, old_value, j, temp);
        what_if(e, fd, temp, best_score, best_value, i);
    }

    m_mpz_manager.del(old_value);
    m_mpz_manager.del(temp);

    return best_score;
}

// second try to use intensification ... also not very effective
bool sls_engine::handle_plateau(double old_score)
{
    unsigned sz = m_assertions.size();
#if _BFS_
    unsigned new_const = m_stats.m_moves % sz;
#else
    unsigned new_const = m_tracker.get_random_uint(16) % sz;
#endif
    expr * e = m_tracker.get_unsat_assertion(m_assertions, sz, new_const);
    if (!e)
        return 0;

    expr * q = m_tracker.get_unsat_expression(e);
    ptr_vector<func_decl> & to_evaluate = m_tracker.get_constants(q);

    new_const = m_tracker.get_random_uint(16) % to_evaluate.size();
    func_decl * fd = to_evaluate[new_const];

    mpz new_value;
    //m_mpz_manager.set(new_value, m_tracker.get_value(fd));
    unsigned new_bit = 0;
    double global_score = old_score, local_score = m_tracker.get_score(q), new_score = old_score;

    for (unsigned i = 1; i <= _INTENSIFICATION_TRIES_; i++)
    {
        new_score = find_best_move_local(q, fd, new_value, i);

        m_stats.m_moves++;
        m_stats.m_flips++;

        global_score = incremental_score(fd, new_value);
        local_score = m_tracker.get_score(q);

        SASSERT(new_score == i * local_score / _INTENSIFICATION_TRIES_ + (_INTENSIFICATION_TRIES_ - i) * global_score / _INTENSIFICATION_TRIES_);

        if (m_mpz_manager.is_one(m_tracker.get_value(q)))
            return 1;
    }

    return 0;
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
#if _PERC_STICKY_
    expr * e = m_tracker.get_unsat_assertion(g, m_stats.m_moves);
#endif

#if _RESTARTS_ == 1
    while (check_restart(m_stats.m_moves) && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#elif _RESTARTS_ == 2
    while (check_restart(plateau_cnt) && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#elif _RESTARTS_ == 3
    while (check_restart((unsigned)m_stats.m_stopwatch.get_current_seconds()) && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#else
    while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {
#endif
        checkpoint();
        m_stats.m_moves++;

#if _REAL_RS_ || _REAL_PBFS_
        //m_tracker.debug_real(g, m_stats.m_moves);
#endif

#if _FOCUS_
#if _PERC_STICKY_
        if (m_tracker.get_random_uint(16) % 100 >= _PERC_STICKY_ || m_mpz_manager.eq(m_tracker.get_value(e), m_one))
            e = m_tracker.get_unsat_assertion(g, m_stats.m_moves);
#else
        expr * e = m_tracker.get_unsat_assertion(m_assertions, m_stats.m_moves);
#endif
        if (!e)
        {
            res = l_true;
            goto bailout;
        }
        ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants_walksat(e);
#else
        ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants_gsat(g, sz);
        if (!to_evaluate.size())
        {
            res = l_true;
            goto bailout;
        }
#endif

#if _TYPE_RSTEP_
        if (m_tracker.get_random_uint(16) % 1000 < _PERM_RSTEP_)
        {
#if _TYPE_RSTEP_ == 1
            m_evaluator.randomize_local(to_evaluate);
#elif _TYPE_RSTEP_ == 2
            mk_random_move(to_evaluate);
#endif
#if _CACHE_TOP_SCORE_
            score = m_tracker.get_top_sum() / g->size();
#else
            score = top_score(g);
#endif
        }
        continue;
#endif

#if _WEIGHT_DIST_ == 4
        m_tracker.set_weight_dist_factor(m_stats.m_stopwatch.get_current_seconds() / _TIMELIMIT_);
#endif       
        old_score = score;
        new_const = (unsigned)-1;

#if _VNS_
        score = find_best_move_vns(g, to_evaluate, score, new_const, new_value, new_bit, move);
#else
        score = find_best_move(to_evaluate, score, new_const, new_value, new_bit, move);
#endif

        if (new_const == static_cast<unsigned>(-1)) {
            score = old_score;
            plateau_cnt++;
#if _INTENSIFICATION_
            handle_plateau(g, score);
            //handle_plateau(g);
            //e = m_tracker.get_unsat_assertion(g, m_stats.m_moves);    
            //to_evaluate = m_tracker.get_unsat_constants_walksat(e);
#else
#if _PERC_PLATEAU_MOVES_
            if (m_tracker.get_random_uint(8) % 100 < _PERC_PLATEAU_MOVES_)
                mk_random_move(to_evaluate);
            else
#endif
#if _REPICK_
                m_evaluator.randomize_local(m_assertions, m_stats.m_moves);
#else
                m_evaluator.randomize_local(to_evaluate);
#endif
#endif

#if _CACHE_TOP_SCORE_
            score = m_tracker.get_top_sum() / m_assertions.size();
#else
            score = top_score(g);
#endif
        }
        else {
            func_decl * fd = to_evaluate[new_const];
#if _REAL_RS_ || _REAL_PBFS_
            score = serious_score(g, fd, new_value);
#else
            score = incremental_score(fd, new_value);
#endif
        }
    }

bailout:
    m_mpz_manager.del(new_value);

    return res;
}

#if 0 // Old code.
// main search loop
lbool sls_engine::search_old() {
    lbool res = l_undef;
    double score = 0.0, old_score = 0.0;
    unsigned new_const = (unsigned)-1, new_bit = 0;
    mpz new_value;
    move_type move;

    score = rescore();
    TRACE("sls", tout << "Starting search, initial score   = " << std::setprecision(32) << score << std::endl;
    tout << "Score distribution:";
    for (unsigned i = 0; i < m_assertions.size(); i++)
        tout << " " << std::setprecision(3) << m_tracker.get_score(m_assertions[i]);
    tout << " TOP: " << score << std::endl;);

    unsigned plateau_cnt = 0;

    // Andreas: Why do we only allow so few plateaus?
#if _RESTARTS_
    while (m_stats.m_stopwatch.get_current_seconds() < 200 * (m_stats.m_restarts + 1) * 0.2) {
        //while (plateau_cnt < m_plateau_limit && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {                
#else
    while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_ && (_RESTARTS_ == 0 || m_stats.m_moves < _RESTARTS_)) {
#endif
        do {
            checkpoint();

#if _WEIGHT_DIST_ == 4
            m_tracker.set_weight_dist_factor(m_stats.m_stopwatch.get_current_seconds() / _TIMELIMIT_);
#endif

#if _TYPE_RSTEP_
            if (m_tracker.get_random_uint(16) % 1000 < _PERM_RSTEP_)
            {
#if _TYPE_RSTEP_ == 1
                m_evaluator.randomize_local(g, m_stats.m_moves);
#elif _TYPE_RSTEP_ == 2
                mk_random_move(g);
#endif
                score = top_score(g);

                if (score >= 1.0) {
                    bool all_true = true;
                    for (unsigned i = 0; i < g->size() && all_true; i++)
                        if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                            all_true = false;
                    if (all_true) {
                        res = l_true; // sat
                        goto bailout;
                    }
                    else
                        TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
                }
            }
#endif
            old_score = score;
            new_const = (unsigned)-1;

            ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants(m_assertions, m_stats.m_moves);
            if (!to_evaluate.size())
            {
                res = l_true;
                goto bailout;
            }
            TRACE("sls_constants", tout << "Evaluating these constants: " << std::endl;
            for (unsigned i = 0; i < to_evaluate.size(); i++)
                tout << to_evaluate[i]->get_name() << std::endl;);

#if _VNS_
            score = find_best_move_vns(to_evaluate, score, new_const, new_value, new_bit, move);
#else
            score = find_best_move(to_evaluate, score, new_const, new_value, new_bit, move);
#endif
            if (new_const == static_cast<unsigned>(-1)) {
                TRACE("sls", tout << "Local maximum reached; unsatisfied constraints: " << std::endl;
                for (unsigned i = 0; i < m_assertions.size(); i++) {
                    if (!m_mpz_manager.is_one(m_tracker.get_value(m_assertions[i])))
                        tout << mk_ismt2_pp(m_assertions[i], m_manager) << std::endl;
                });

                TRACE("sls_max", m_tracker.show_model(tout);
                tout << "Scores: " << std::endl;
                for (unsigned i = 0; i < m_assertions.size(); i++)
                    tout << mk_ismt2_pp(m_assertions[i], m_manager) << " ---> " <<
                    m_tracker.get_score(m_assertions[i]) << std::endl;);
                // Andreas: If new_const == -1, shouldn't score = old_score anyway?
                score = old_score;
            }
            else {
                // Andreas: Why does randomizing not count as a move? (Now it does.)
                m_stats.m_moves++;
                func_decl * fd = to_evaluate[new_const];

                TRACE("sls", tout << "Setting " << fd->get_name() << " to " << m_mpz_manager.to_string(new_value) << " (Move: ";
                switch (move) {
                case MV_FLIP:
                    tout << "Flip";
                    if (!m_manager.is_bool(fd->get_range())) tout << " #" << new_bit;
                    break;
                case MV_INC:
                    tout << "+1";
                    break;
                case MV_DEC:
                    tout << "-1";
                    break;
                case MV_INV:
                    tout << "NEG";
                    break;
                };
                tout << ") ; new score = " << std::setprecision(32) << score << std::endl;);

                switch (move) {
                case MV_FLIP: m_stats.m_flips++; break;
                case MV_INC: m_stats.m_incs++; break;
                case MV_DEC: m_stats.m_decs++; break;
                case MV_INV: m_stats.m_invs++; break;
                case MV_UMIN: m_stats.m_umins++; break;
                case MV_MUL2: m_stats.m_mul2s++; break;
                case MV_MUL3: m_stats.m_mul3s++; break;
                case MV_DIV2: m_stats.m_div2s++; break;
                }

#if _REAL_RS_ || _REAL_PBFS_
                score = serious_score(fd, new_value);
#else
                score = incremental_score(fd, new_value);
#endif

                TRACE("sls", tout << "Score distribution:";
                for (unsigned i = 0; i < m_assertions.size(); i++)
                    tout << " " << std::setprecision(3) << m_tracker.get_score(m_assertions[i]);
                tout << " TOP: " << score << std::endl;);
            }

            if (score >= 0.99999) {
                //                    if (score >= 1.0) {
                // score could theoretically be imprecise.
                // Andreas: it seems using top level score caching can make the score unprecise also in the other direction!
                bool all_true = true;
                for (unsigned i = 0; i < m_assertions.size() && all_true; i++)
                    if (!m_mpz_manager.is_one(m_tracker.get_value(m_assertions[i])))
                        all_true = false;
                if (all_true) {
                    res = l_true; // sat
                    goto bailout;
                }
                else
                    TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
            }
            /*
            if (m_stats.m_moves % 100 == 0)
            {
            verbose_stream() << "(" << std::fixed << std::setprecision(10) << score << ")" << std::endl;
            verbose_stream() << "(" << std::fixed << std::setprecision(2) << (m_stats.m_moves / m_stats.m_stopwatch.get_current_seconds()) << ")" << std::endl;
            }*/
        } while (score > old_score && res == l_undef);

        // Andreas: Why do you check for old_score? This should always be equal due to the loop invariant.
        if (score != old_score) {
            report_tactic_progress("This should not happen I guess.", plateau_cnt);
            plateau_cnt = 0;
        }
        else {
            m_stats.m_moves++;
            plateau_cnt++;
            //report_tactic_progress("Plateau.", plateau_cnt);
            // Andreas: Right now, a useless assignment is created in case of a restart. But we don't want to use restarts anyway.
            //if (plateau_cnt < m_plateau_limit) {
            TRACE("sls", tout << "In a plateau (" << plateau_cnt << "/" << m_plateau_limit << "); randomizing locally." << std::endl;);
#if _INTENSIFICATION_
            handle_plateau(g, score);
            //handle_plateau();
#else
            m_evaluator.randomize_local(m_assertions, m_stats.m_moves);
#endif
            //mk_random_move();
            score = top_score();

            if (score >= 1.0) {
                bool all_true = true;
                for (unsigned i = 0; i < m_assertions.size() && all_true; i++)
                    if (!m_mpz_manager.is_one(m_tracker.get_value(m_assertions[i])))
                        all_true = false;
                if (all_true) {
                    res = l_true; // sat
                    goto bailout;
                }
                else
                    TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
            }
        }
    }

bailout:
    m_mpz_manager.del(new_value);

    return res;
}
#endif

void sls_engine::init_tracker() {
#if _WEIGHT_DIST_ == 4
    m_tracker.set_weight_dist_factor(m_stats.m_stopwatch.get_current_seconds() / _TIMELIMIT_);
#endif
#if _WEIGHT_TOGGLE_
    m_tracker.set_weight_dist_factor(_WEIGHT_DIST_FACTOR_);
#endif
    m_tracker.initialize(m_assertions);
}

void sls_engine::operator()(goal_ref const & g, model_converter_ref & mc) {
    if (g->inconsistent()) {
        mc = 0;
        return;
    }

    m_produce_models = g->models_enabled();

    for (unsigned i = 0; i < g->size(); i++)
        assert_expr(g->form(i));    

    verbose_stream() << "_BFS_ " << _BFS_ << std::endl;
    verbose_stream() << "_FOCUS_ " << _FOCUS_ << std::endl;
    verbose_stream() << "_PERC_STICKY_ " << _PERC_STICKY_ << std::endl;
    verbose_stream() << "_RESTARTS_ " << _RESTARTS_ << std::endl;
    verbose_stream() << "_RESTART_LIMIT_ " << _RESTART_LIMIT_ << std::endl;
    verbose_stream() << "_RESTART_INIT_ " << _RESTART_INIT_ << std::endl;
    verbose_stream() << "_RESTART_SCHEME_ " << _RESTART_SCHEME_ << std::endl;
    verbose_stream() << "_TIMELIMIT_ " << _TIMELIMIT_ << std::endl;
    verbose_stream() << "_SCORE_AND_AVG_ " << _SCORE_AND_AVG_ << std::endl;
    verbose_stream() << "_SCORE_OR_MUL_ " << _SCORE_OR_MUL_ << std::endl;
    verbose_stream() << "_VNS_ " << _VNS_ << std::endl;
    verbose_stream() << "_WEIGHT_DIST_ " << _WEIGHT_DIST_ << std::endl;
    verbose_stream() << "_WEIGHT_DIST_FACTOR_ " << std::fixed << std::setprecision(2) << _WEIGHT_DIST_FACTOR_ << std::endl;
    verbose_stream() << "_INTENSIFICATION_ " << _INTENSIFICATION_ << std::endl;
    verbose_stream() << "_INTENSIFICATION_TRIES_ " << _INTENSIFICATION_TRIES_ << std::endl;
    verbose_stream() << "_PERC_PLATEAU_MOVES_ " << _PERC_PLATEAU_MOVES_ << std::endl;
    verbose_stream() << "_REPICK_ " << _REPICK_ << std::endl;
    verbose_stream() << "_UCT_ " << _UCT_ << std::endl;
    verbose_stream() << "_UCT_CONSTANT_ " << std::fixed << std::setprecision(2) << _UCT_CONSTANT_ << std::endl;
    verbose_stream() << "_UCT_RESET_ " << _UCT_RESET_ << std::endl;
    verbose_stream() << "_UCT_INIT_ " << _UCT_INIT_ << std::endl;
    verbose_stream() << "_PROBABILISTIC_UCT_ " << _PROBABILISTIC_UCT_ << std::endl;
    verbose_stream() << "_UCT_EPS_ " << std::fixed << std::setprecision(4) << _UCT_EPS_ << std::endl;
    verbose_stream() << "_USE_ADDSUB_ " << _USE_ADDSUB_ << std::endl;
    verbose_stream() << "_USE_MUL2DIV2_ " << _USE_MUL2DIV2_ << std::endl;
    verbose_stream() << "_USE_MUL3_ " << _USE_MUL3_ << std::endl;
    verbose_stream() << "_USE_UNARY_MINUS_ " << _USE_UNARY_MINUS_ << std::endl;
    verbose_stream() << "_UNIFORM_RANDOM_ " << _UNIFORM_RANDOM_ << std::endl;
    verbose_stream() << "_REAL_RS_ " << _REAL_RS_ << std::endl;
    verbose_stream() << "_REAL_PBFS_ " << _REAL_PBFS_ << std::endl;
    verbose_stream() << "_SKIP_BITS_ " << _SKIP_BITS_ << std::endl;
    verbose_stream() << "_PERC_CHANGE_ " << _PERC_CHANGE_ << std::endl;
    verbose_stream() << "_TYPE_RSTEP_ " << _TYPE_RSTEP_ << std::endl;
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
    init_tracker();
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
}

unsigned sls_engine::check_restart(unsigned curr_value)
{
    if (curr_value > m_restart_limit)
    {
#if _RESTART_SCHEME_ == 4
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
#if _WEIGHT_TOGGLE_
        printf("Setting weight: %f\n", _WEIGHT_DIST_FACTOR_ * (((m_stats.m_restarts & 2) == 0) + 1));
        m_tracker.set_weight_dist_factor(_WEIGHT_DIST_FACTOR_ * (((m_stats.m_restarts & 2) == 0) + 1));
#endif
        return 0;
    }
    return 1;
}
