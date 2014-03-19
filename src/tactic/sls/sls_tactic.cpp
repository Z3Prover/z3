/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_tactic.h

Abstract:

    A Stochastic Local Search (SLS) tactic

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/
#include<iomanip>
#include"map.h"
#include"nnf.h"
#include"cooperate.h"
#include"ast_smt2_pp.h"
#include"ast_pp.h"
#include"var_subst.h"
#include"model_pp.h"
#include"model_evaluator.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"simplify_tactic.h"
#include"stopwatch.h"
#include"propagate_values_tactic.h"
#include"sls_tactic.h"
#include"nnf_tactic.h"

// which unsatisfied assertion is selected? only works with _FOCUS_ > 0
// 0 = random, 1 = #moves, 2 = assertion with min score, 3 = assertion with max score
#define _BFS_ 0

// how many terms are considered for variable selection?
// 0 = all terms (GSAT), 1 = only one top level assertion (WSAT), 2 = only one bottom level atom
#define _FOCUS_ 1

// do we use restarts?
// 0 = no, otherwise the value defines the maximum number of moves
#define _RESTARTS_ 0

// timelimit
#define _TIMELIMIT_ 3600

// should score of conjunctions be calculated by average rather than max?
#define _SCORE_AND_AVG_ 0

// should score of discunctions be calculated by multiplication of the inverse score rather than min?
#define _SCORE_OR_MUL_ 0

// do we use some kind of variable neighbourhood-search?
// 0 = no, 1 = only consider flipping bits if no better score can be obtained otherwise, 2 = only consider flipping bits until a better score can be obtained
#define _VNS_ 0

// do we reduce the score of unsatisfied literals?
// 0 = no
// 1 = yes, by multiplying it with some factor
// 2 = yes, by squaring it
// 3 = yes, by setting it to zero
// 4 = by progessively increasing weight (_TIMELIMIT_ needs to be set appropriately!)
#define _WEIGHT_DIST_ 0

// the factor used for _WEIGHT_DIST_ = 1
#define _WEIGHT_DIST_FACTOR_ 0.25

// do we use intensification steps in local minima? if so, how many?
#define _INTENSIFICATION_ 0
#define _INTENSIFICATION_TRIES_ 0

// do we use some UCT-like scheme for assertion-selection? overrides _BFS_
#define _UCT_ 0

// how much diversification is used in the UCT-scheme?
#define _UCT_CONSTANT_ 0.01

// is uct clause selection probabilistic similar to variable selection in sparrow?
#define _PROBABILISTIC_UCT_ 0

// shall we use addition/subtraction?
#define _USE_ADDSUB_ 1

// shall we try multilication and division by 2?
#define _USE_MUL2DIV2_ 1

// shall we try multiplication by 3?
#define _USE_MUL3_ 1

// shall we try unary minus (= inverting and incrementing)
#define _USE_UNARY_MINUS_ 1

// is random selection for assertions uniform? only works with _BFS_ = _UCT_ = 0
#define _UNIFORM_RANDOM_ 1

// should we use unsat-structures as done in SLS 4 SAT instead for random or bfs selection?
#define _REAL_RS_ 0
#define _REAL_PBFS_ 0

// how many bits do we neglect in each iteration?
#define _SKIP_BITS_ 0

// when randomizing local, what is the probability for changing a single bit?
// 0 = use standard scheme and pick a new value at random (= 50), otherwise the value (as int) gives the percentage
#define _PERC_CHANGE_ 0

// do we use random steps for noise?
// 0 = no, 1 = randomize local, 2 = make random move
#define _TYPE_RSTEP_ 0

// with what probability _PERM_STEP_/1000 will the random step happen? 
#define _PERM_RSTEP_ 0

// shall we use early pruning for incremental update?
#define _EARLY_PRUNE_ 1

// shall we use caching for top_score?
#define _CACHE_TOP_SCORE_ 1


#if ((_UCT_ > 0) + _UNIFORM_RANDOM_ + _REAL_RS_ + _REAL_PBFS_ > 1) || _BFS_ && (_UCT_ ||_UNIFORM_RANDOM_ ||_REAL_RS_ ||_REAL_PBFS_)
    InvalidConfiguration;
#endif
#if (_PROBABILISTIC_UCT_ && !_UCT_)
    InvalidConfiguration;
#endif


#include"sls_params.hpp"
#include"sls_evaluator.h"
#include"sls_tracker.h"

class sls_tactic : public tactic {
    class stats {
    public:
        unsigned        m_restarts;
        stopwatch       m_stopwatch;    
        unsigned        m_full_evals;
        unsigned        m_incr_evals;
        unsigned        m_moves, m_flips, m_incs, m_decs, m_invs, m_umins, m_mul2s, m_mul3s, m_div2s;

        stats() :
            m_restarts(0),
            m_full_evals(0),
            m_incr_evals(0),
            m_moves(0),
            m_umins(0),
            m_mul2s(0),
            m_mul3s(0),
            m_div2s(0),
            m_flips(0),
            m_incs(0),
            m_decs(0),
            m_invs(0) {
                m_stopwatch.reset();
                m_stopwatch.start();
            }
        void reset() {
            m_full_evals = m_flips = m_incr_evals = 0;
            m_stopwatch.reset();
            m_stopwatch.start();
        }
    };    

    struct imp {       
        ast_manager   & m_manager;
        stats         & m_stats;
        unsynch_mpz_manager m_mpz_manager;
        powers          m_powers;
        mpz             m_zero, m_one, m_two;            
        bool            m_produce_models;
        volatile bool   m_cancel;    
        bv_util         m_bv_util;
        sls_tracker     m_tracker;
        sls_evaluator   m_evaluator;

        unsigned        m_max_restarts;
        unsigned        m_plateau_limit;

        ptr_vector<mpz> m_old_values;
        
        typedef enum { MV_FLIP = 0, MV_INC, MV_DEC, MV_INV, MV_UMIN, MV_MUL2, MV_MUL3, MV_DIV2 } move_type;        

        imp(ast_manager & m, params_ref const & p, stats & s) : 
            m_manager(m),
            m_stats(s),
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

        ~imp() {
            m_mpz_manager.del(m_zero);
            m_mpz_manager.del(m_one);
            m_mpz_manager.del(m_two);
        }        

        ast_manager & m() const { return m_manager; }

        void set_cancel(bool f) { m_cancel = f; }
        void cancel() { set_cancel(true); }
        void reset_cancel() { set_cancel(false); }

        static void collect_param_descrs(param_descrs & r) {
            sls_params::collect_param_descrs(r);
        }

        void updt_params(params_ref const & _p) {
            sls_params p(_p);
            m_produce_models = _p.get_bool("model", false);
            m_max_restarts = p.restarts();            
            m_tracker.set_random_seed(p.random_seed());
            m_plateau_limit = p.plateau_limit();
        }

        void checkpoint() { 
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            cooperate("sls");
        }

        bool full_eval(goal_ref const & g, model & mdl) {
            bool res = true;

            unsigned sz = g->size();
            for (unsigned i = 0; i < sz && res; i++) {
                checkpoint();
                expr_ref o(m_manager);

                if (!mdl.eval(g->form(i), o, true))
                    exit(ERR_INTERNAL_FATAL);

                res = m_manager.is_true(o.get());
            }        

            TRACE("sls", tout << "Evaluation: " << res << std::endl;);

            return res;
        }

        double top_score(goal_ref const & g) {
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
                                tout << " MIN: " << min << std::endl; );
            return min;
            #else
            double top_sum = 0.0;
            unsigned sz = g->size();
            for (unsigned i = 0; i < sz; i++) {
                expr * e = g->form(i);
                top_sum += m_tracker.get_score(e);
            }

            TRACE("sls_top", tout << "Score distribution:"; 
                                    for (unsigned i = 0; i < sz; i++)
                                        tout << " " << m_tracker.get_score(g->form(i));
                                    tout << " AVG: " << top_sum / (double) sz << std::endl; );

#if _CACHE_TOP_SCORE_
            m_tracker.set_top_sum(top_sum);
#endif

            return top_sum / (double) sz;
            #endif
        }

        double rescore(goal_ref const & g) {
            m_evaluator.update_all();
            m_stats.m_full_evals++;
            return top_score(g);
        }

        double serious_score(goal_ref const & g, func_decl * fd, const mpz & new_value) {
            m_evaluator.serious_update(fd, new_value);
            m_stats.m_incr_evals++;
#if _CACHE_TOP_SCORE_
            return (m_tracker.get_top_sum() / g->size());
#else
            return top_score(g);
#endif
        }

        double incremental_score(goal_ref const & g, func_decl * fd, const mpz & new_value) {
            m_evaluator.update(fd, new_value);
            m_stats.m_incr_evals++;
#if _CACHE_TOP_SCORE_
            return (m_tracker.get_top_sum() / g->size());
#else
            return top_score(g);
#endif
        }

#if _EARLY_PRUNE_
        double incremental_score_prune(goal_ref const & g, func_decl * fd, const mpz & new_value) {
            m_stats.m_incr_evals++;
            if (m_evaluator.update_prune(fd, new_value))
#if _CACHE_TOP_SCORE_
                return (m_tracker.get_top_sum() / g->size());
#else
                return top_score(g);
#endif
            else
                return 0.0;
        }
#endif

        // checks whether the score outcome of a given move is better than the previous score
        bool what_if(goal_ref const & g, func_decl * fd, const unsigned & fd_inx, const mpz & temp, 
                        double & best_score, unsigned & best_const, mpz & best_value) {

            #ifdef Z3DEBUG
            mpz old_value;
            m_mpz_manager.set(old_value, m_tracker.get_value(fd));
            #endif

#if _EARLY_PRUNE_
            double r = incremental_score_prune(g, fd, temp);
#else
            double r = incremental_score(g, fd, temp);
#endif   
            #ifdef Z3DEBUG
            TRACE("sls_whatif", tout << "WHAT IF " << fd->get_name() << " WERE " << m_mpz_manager.to_string(temp) << 
                                        " --> " << r << std::endl; );
        
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
        bool what_if_local(expr * e, func_decl * fd, const unsigned & fd_inx, const mpz & temp, 
                        double & best_score, unsigned & best_const, mpz & best_value) {
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

        void mk_add(unsigned bv_sz, const mpz & old_value, mpz & add_value, mpz & result) {
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
        void mk_mul2(unsigned bv_sz, const mpz & old_value, mpz & result) {
            mpz temp, mask, mask2;
            m_mpz_manager.mul(old_value, m_two, temp);
            m_mpz_manager.set(mask, m_powers(bv_sz));
            m_mpz_manager.bitwise_not(bv_sz, mask, mask2);
            m_mpz_manager.bitwise_and(temp, mask2, result);
            m_mpz_manager.del(temp);
            m_mpz_manager.del(mask);
            m_mpz_manager.del(mask2);
        }

        void mk_div2(unsigned bv_sz, const mpz & old_value, mpz & result) {
            m_mpz_manager.div(old_value, m_two, result);
        }

        void mk_inc(unsigned bv_sz, const mpz & old_value, mpz & incremented) {
            unsigned shift;        
            m_mpz_manager.add(old_value, m_one, incremented);
            if (m_mpz_manager.is_power_of_two(incremented, shift) && shift == bv_sz)
                m_mpz_manager.set(incremented, m_zero);
        }

        void mk_dec(unsigned bv_sz, const mpz & old_value, mpz & decremented) {
            if (m_mpz_manager.is_zero(old_value)) {
                m_mpz_manager.set(decremented, m_powers(bv_sz));
                m_mpz_manager.dec(decremented);
            }
            else
                m_mpz_manager.sub(old_value, m_one, decremented);
        }

        void mk_inv(unsigned bv_sz, const mpz & old_value, mpz & inverted) {
            m_mpz_manager.bitwise_not(bv_sz, old_value, inverted);
        }

        void mk_flip(sort * s, const mpz & old_value, unsigned bit, mpz & flipped) {
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

        void mk_random_move(goal_ref const & g) {
            unsigned rnd_mv = 0;
            if (m_stats.m_moves > 10000)
                rnd_mv = 0;

            ptr_vector<func_decl> & unsat_constants = m_tracker.get_unsat_constants(g, m_stats.m_moves);                
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
                if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv=2;
                if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv++;
                move_type mt = (move_type) rnd_mv;

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
                             tout << "Locally randomized model: " << std::endl; m_tracker.show_model(tout); );            
            }

            m_evaluator.update(fd, new_value);            
            m_mpz_manager.del(new_value);
        }

        // will use VNS to ignore some possible moves and increase the flips per second
        double find_best_move_vns(goal_ref const & g, ptr_vector<func_decl> & to_evaluate, double score, 
                              unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move) {
            mpz old_value, temp;
            unsigned bv_sz, max_bv_sz = 0;
            double new_score = score;

            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0 ; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                if (max_bv_sz < bv_sz) max_bv_sz = bv_sz;
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                if (m_bv_util.is_bv_sort(srt) && bv_sz > 1) {
                    if (!m_mpz_manager.is_even(old_value)) { 
                        // for odd values, try +1
                        mk_inc(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_INC;
                    }
                    else { 
                        // for even values, try -1
                        mk_dec(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_DEC;
                    }

                    // try inverting
                    mk_inv(bv_sz, old_value, temp);
                    if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                        move = MV_INV;

                    // try to flip lsb
                    mk_flip(srt, old_value, 0, temp);                
                    if (what_if(g, fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = 0;
                        move = MV_FLIP;
                    }
                }

                // reset to what it was before
                double check = incremental_score(g, fd, old_value);
                SASSERT(check == score);
            }

            // we can either check the condition once in the beginning or check it repeatedly after every bit
#if _VNS_ == 1
            for (unsigned j = 1; j < max_bv_sz && new_score <= score; j++)
#else
            if (new_score <= score)
            for (unsigned j = 1; j < max_bv_sz && new_score < 1.0; j++)
#endif
            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0 ; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                // What would happen if we flipped bit #j ?                
                if (j < bv_sz)
                {
                    mk_flip(srt, old_value, j, temp);                

                    if (what_if(g, fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = j;
                        move = MV_FLIP;
                    }
                }
                // reset to what it was before
                double check = incremental_score(g, fd, old_value);
                SASSERT(check == score);
            }
            m_mpz_manager.del(old_value);
            m_mpz_manager.del(temp);
            return new_score;
        }        

        // finds the move that increased score the most. returns best_const = -1, if no increasing move exists.
        double find_best_move(goal_ref const & g, ptr_vector<func_decl> & to_evaluate, double score, 
                              unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move) {
            mpz old_value, temp;
#if _USE_MUL3_ || _USE_UNARY_MINUS_
            mpz temp2;
#endif
            unsigned bv_sz;
            double new_score = score;

            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0 ; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                // first try to flip every bit
#if _SKIP_BITS_
                for (unsigned j = (i + m_stats.m_moves) % (_SKIP_BITS_ + 1); j < bv_sz && new_score < 1.0; j+=(_SKIP_BITS_ + 1)) {
#else
                for (unsigned j = 0; j < bv_sz && new_score < 1.0; j++) {
#endif
                    // What would happen if we flipped bit #i ?                
                    mk_flip(srt, old_value, j, temp);                

                    if (what_if(g, fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = j;
                        move = MV_FLIP;
                    }
                }

                if (m_bv_util.is_bv_sort(srt) && bv_sz > 1) {
#if _USE_ADDSUB_
                    if (!m_mpz_manager.is_even(old_value)) { 
                        // for odd values, try +1
                        mk_inc(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_INC;
                    }
                    else { 
                        // for even values, try -1
                        mk_dec(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_DEC;
                    }
#endif
                    // try inverting
                    mk_inv(bv_sz, old_value, temp);
                    if (what_if(g, fd, i, temp, new_score, best_const, best_value))
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
                double check = incremental_score(g, fd, old_value);
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
        double find_best_move_local(expr * e, ptr_vector<func_decl> & to_evaluate,
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
        bool handle_plateau(goal_ref const & g)
        {
            unsigned sz = g->size();
#if _BFS_
            unsigned pos = m_stats.m_moves % sz;
#else
            unsigned pos = m_tracker.get_random_uint(16) % sz;
#endif
            expr * e = m_tracker.get_unsat_assertion(g, sz, pos);
            if (!e)
                return 0;

            expr * q = m_tracker.get_unsat_expression(e);
            ptr_vector<func_decl> & to_evaluate = m_tracker.get_constants(q);
            for (unsigned i = 0; i < to_evaluate.size(); i++)
            {
                m_tracker.get_value(to_evaluate[i]);
                m_old_values.push_back( & m_tracker.get_value(to_evaluate[i]));
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
                } else {
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
                m_tracker.set_value(to_evaluate[i], * m_old_values[i]);

            m_old_values.reset();

            return 0;
        }

        // what_if version needed in the context of 2nd intensification try, combining local and global score
        bool what_if(goal_ref const & g, expr * e, func_decl * fd, const mpz & temp, 
                        double & best_score, mpz & best_value, unsigned i) {
        
            double global_score = incremental_score(g, fd, temp);
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
        double find_best_move_local(goal_ref const & g, expr * e, func_decl * fd, mpz & best_value, unsigned i)
        {
            mpz old_value, temp;
            double best_score = 0;

            sort * srt = fd->get_range();
            unsigned bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
            m_mpz_manager.set(old_value, m_tracker.get_value(fd));

            for (unsigned j = 0; j < bv_sz && best_score < 1.0; j++) {
                mk_flip(srt, old_value, j, temp);                
                what_if(g, e, fd, temp, best_score, best_value, i); 
            }

            m_mpz_manager.del(old_value);
            m_mpz_manager.del(temp);

            return best_score;
        }        

        // second try to use intensification ... also not very effective
        bool handle_plateau(goal_ref const & g, double old_score)
        {
            unsigned sz = g->size();
#if _BFS_
            unsigned new_const = m_stats.m_moves % sz;
#else
            unsigned new_const = m_tracker.get_random_uint(16) % sz;
#endif
            expr * e = m_tracker.get_unsat_assertion(g, sz, new_const);
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
                new_score = find_best_move_local(g, q, fd, new_value, i);

                m_stats.m_moves++;
                m_stats.m_flips++;

                global_score = incremental_score(g, fd, new_value);
                 local_score = m_tracker.get_score(q);

                SASSERT(new_score == i * local_score / _INTENSIFICATION_TRIES_ + (_INTENSIFICATION_TRIES_ - i) * global_score / _INTENSIFICATION_TRIES_);

                if (m_mpz_manager.is_one(m_tracker.get_value(q)))
                    return 1;
            }

            return 0;
        }

        // main search loop
        lbool search(goal_ref const & g) {        
            lbool res = l_undef;
            double score = 0.0, old_score = 0.0;
            unsigned new_const = (unsigned)-1, new_bit = 0;        
            mpz new_value;
            move_type move;
            
            score = rescore(g);
            TRACE("sls", tout << "Starting search, initial score   = " << std::setprecision(32) << score << std::endl;
                         tout << "Score distribution:"; 
                         for (unsigned i = 0; i < g->size(); i++)
                             tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                         tout << " TOP: " << score << std::endl; ); 
        
            unsigned plateau_cnt = 0;

            // Andreas: Why do we only allow so few plateaus?
#if _RESTARTS_
            while (plateau_cnt < m_plateau_limit && m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_) {                
#else
            while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_ && (_RESTARTS_ == 0 || m_stats.m_moves < _RESTARTS_)) {                
#endif
                do {
                    if (m_stats.m_moves == 5590)
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
                                    all_true=false;
                            if (all_true) {
                                res = l_true; // sat
                                goto bailout;
                            } else
                                TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
                        }
                    }
#endif
                    old_score = score;
                    new_const = (unsigned)-1;
                        
                    ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants(g, m_stats.m_moves);
                    if (!to_evaluate.size())
                    {
                        res = l_true;
                        goto bailout;
                    }
                    TRACE("sls_constants", tout << "Evaluating these constants: " << std::endl;
                                            for (unsigned i = 0 ; i < to_evaluate.size(); i++)
                                                tout << to_evaluate[i]->get_name() << std::endl; );

#if _VNS_
                    score = find_best_move_vns(g, to_evaluate, score, new_const, new_value, new_bit, move);
#else
                    score = find_best_move(g, to_evaluate, score, new_const, new_value, new_bit, move);
#endif
                    if (new_const == static_cast<unsigned>(-1)) {
                        TRACE("sls", tout << "Local maximum reached; unsatisfied constraints: " << std::endl; 
                                        for (unsigned i = 0; i < g->size(); i++) {
                                            if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                                                tout << mk_ismt2_pp(g->form(i), m_manager) << std::endl;
                                        });

                        TRACE("sls_max", m_tracker.show_model(tout);
                                        tout << "Scores: " << std::endl;
                                        for (unsigned i = 0; i < g->size(); i++)
                                            tout << mk_ismt2_pp(g->form(i), m_manager) << " ---> " << 
                                            m_tracker.get_score(g->form(i)) << std::endl; );
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
                                        tout << ") ; new score = " << std::setprecision(32) << score << std::endl; );

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
                        score = serious_score(g, fd, new_value);
#else
                        score = incremental_score(g, fd, new_value);    
#endif

                        TRACE("sls", tout << "Score distribution:"; 
                                        for (unsigned i = 0; i < g->size(); i++)
                                            tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                                        tout << " TOP: " << score << std::endl; );                        
                    }

                    if (score >= 0.99999) {
//                    if (score >= 1.0) {
                        // score could theoretically be imprecise.
                        // Andreas: it seems using top level score caching can make the score unprecise also in the other direction!
                        bool all_true = true;
                        for (unsigned i = 0; i < g->size() && all_true; i++)
                            if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                                all_true=false;
                        if (all_true) {
                            res = l_true; // sat
                            goto bailout;
                        } else
                            TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
                    }
                    /*
                    if (m_stats.m_moves % 100 == 0)
                    {
                        verbose_stream() << "(" << std::fixed << std::setprecision(10) << score << ")" << std::endl;
                        verbose_stream() << "(" << std::fixed << std::setprecision(2) << (m_stats.m_moves / m_stats.m_stopwatch.get_current_seconds()) << ")" << std::endl;
                    }*/
                }
                while (score > old_score && res == l_undef);                
                
                // Andreas: Why do you check for old_score? This should always be equal due to the loop invariant.
                if (score != old_score) {
                    report_tactic_progress("This should not happen I guess.", plateau_cnt);
                    plateau_cnt = 0;
                } else {
                    m_stats.m_moves++;
                    plateau_cnt++;
                    //report_tactic_progress("Plateau.", plateau_cnt);
                    // Andreas: Right now, a useless assignment is created in case of a restart. But we don't want to use restarts anyway.
                    //if (plateau_cnt < m_plateau_limit) {
                        TRACE("sls", tout << "In a plateau (" << plateau_cnt << "/" << m_plateau_limit << "); randomizing locally." << std::endl; );
#if _INTENSIFICATION_
                        handle_plateau(g, score);
                        //handle_plateau(g);
#else
                        m_evaluator.randomize_local(g, m_stats.m_moves);
#endif
                        //mk_random_move(g);
                        score = top_score(g);

                        if (score >= 1.0) {
                            bool all_true = true;
                            for (unsigned i = 0; i < g->size() && all_true; i++)
                                if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                                    all_true=false;
                            if (all_true) {
                                res = l_true; // sat
                                goto bailout;
                        } else
                            TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
                    }
                }
            }

            bailout:
            m_mpz_manager.del(new_value);

            return res;
        }    

        void operator()(goal_ref const & g, model_converter_ref & mc) {
            if (g->inconsistent()) {
                mc = 0;
                return;
            }

            verbose_stream() << "_BFS_ " << _BFS_ << std::endl;
            verbose_stream() << "_FOCUS_ " << _FOCUS_ << std::endl;
            verbose_stream() << "_RESTARTS_ " << _RESTARTS_ << std::endl;
            verbose_stream() << "_TIMELIMIT_ " << _TIMELIMIT_ << std::endl;
            verbose_stream() << "_SCORE_AND_AVG_ " << _SCORE_AND_AVG_ << std::endl;
            verbose_stream() << "_SCORE_OR_MUL_ " << _SCORE_OR_MUL_ << std::endl;
            verbose_stream() << "_VNS_ " << _VNS_ << std::endl;
            verbose_stream() << "_WEIGHT_DIST_ " << _WEIGHT_DIST_ << std::endl;
            verbose_stream() << "_WEIGHT_DIST_FACTOR_ " << std::fixed << std::setprecision(2) << _WEIGHT_DIST_FACTOR_ << std::endl;
            verbose_stream() << "_INTENSIFICATION_ " << _INTENSIFICATION_ << std::endl;
            verbose_stream() << "_INTENSIFICATION_TRIES_ " << _INTENSIFICATION_TRIES_ << std::endl;
            verbose_stream() << "_UCT_ " << _UCT_ << std::endl;
            verbose_stream() << "_UCT_CONSTANT_ " << std::fixed << std::setprecision(2) << _UCT_CONSTANT_ << std::endl;
            verbose_stream() << "_PROBABILISTIC_UCT_ " << _PROBABILISTIC_UCT_ << std::endl;
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
            
#if _WEIGHT_DIST_ == 4
                    m_tracker.set_weight_dist_factor(m_stats.m_stopwatch.get_current_seconds() / _TIMELIMIT_);
#endif
            m_tracker.initialize(g);
            lbool res = l_undef;
        
            do {
                checkpoint();
                // Andreas: I think restarts are too impotant to ignore 99% of them are happening...
                //if ((m_stats.m_restarts % 100) == 0)                        
                    report_tactic_progress("Searching... restarts left:", m_max_restarts - m_stats.m_restarts);
                
                res = search(g);

                if (res == l_undef)
                    m_tracker.randomize();
            }
            while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_ && res != l_true && m_stats.m_restarts++ < m_max_restarts);
        
            verbose_stream() << "(restarts: " << m_stats.m_restarts << " flips: " << m_stats.m_moves << " time: " << std::fixed << std::setprecision(2) << m_stats.m_stopwatch.get_current_seconds() << " fps: " << (m_stats.m_moves / m_stats.m_stopwatch.get_current_seconds()) << ")" << std::endl;

            if (res == l_true) {    
                report_tactic_progress("Number of flips:", m_stats.m_moves);
                if (m_produce_models) {
                    model_ref mdl = m_tracker.get_model();
                    mc = model2model_converter(mdl.get());
                    TRACE("sls_model", mc->display(tout); );
                }
                g->reset();
            }
            else
                mc = 0;
        }
    };
    
    ast_manager    & m;
    params_ref       m_params;
    imp            * m_imp;
    stats            m_stats;

public:
    sls_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        m_params(p) {
        m_imp = alloc(imp, m, p, m_stats);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(sls_tactic, m, m_params);
    }

    virtual ~sls_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        imp::collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        m_imp->m_produce_models = g->models_enabled();        
        mc = 0; pc = 0; core = 0; result.reset();
        
        TRACE("sls", g->display(tout););
        tactic_report report("sls", *g);
        
        m_imp->operator()(g, mc);

        g->inc_depth();
        result.push_back(g.get());
        TRACE("sls", g->display(tout););
        SASSERT(g->is_well_sorted());
    }

    virtual void cleanup() {        
        imp * d = alloc(imp, m, m_params, m_stats);
        #pragma omp critical (tactic_cancel)
        {
            std::swap(d, m_imp);
        }
        dealloc(d);
    }
    
    virtual void collect_statistics(statistics & st) const {
        double seconds = m_stats.m_stopwatch.get_current_seconds();            
        st.update("sls restarts", m_stats.m_restarts);
        st.update("sls full evals", m_stats.m_full_evals);
        st.update("sls incr evals", m_stats.m_incr_evals);
        st.update("sls incr evals/sec", m_stats.m_incr_evals/ seconds);
        st.update("sls FLIP moves", m_stats.m_flips);    
        st.update("sls INC moves", m_stats.m_incs);
        st.update("sls DEC moves", m_stats.m_decs);
        st.update("sls INV moves", m_stats.m_invs);
        st.update("sls moves", m_stats.m_moves);
        st.update("sls moves/sec", m_stats.m_moves / seconds);
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_sls_tactic(ast_manager & m, params_ref const & p) {
    return and_then(fail_if_not(mk_is_qfbv_probe()), // Currently only QF_BV is supported.
                    clean(alloc(sls_tactic, m, p)));
}


tactic * mk_preamble(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    // main_p.set_bool("pull_cheap_ite", true);
    main_p.set_bool("push_ite_bv", true);
    main_p.set_bool("blast_distinct", true);
    // main_p.set_bool("udiv2mul", true);
    main_p.set_bool("hi_div0", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref hoist_p;
    hoist_p.set_bool("hoist_mul", true);
    // hoist_p.set_bool("hoist_cmul", true);
    hoist_p.set_bool("som", false);

    params_ref gaussian_p;
    // conservative gaussian elimination. 
    gaussian_p.set_uint("gaussian_max_occs", 2); 

    return and_then(and_then(mk_simplify_tactic(m),                             
                             mk_propagate_values_tactic(m),
                             using_params(mk_solve_eqs_tactic(m), gaussian_p),
                             mk_elim_uncnstr_tactic(m),
                             mk_bv_size_reduction_tactic(m),
                             using_params(mk_simplify_tactic(m), simp2_p)),
                        using_params(mk_simplify_tactic(m), hoist_p),
                        mk_max_bv_sharing_tactic(m),
                        // Andreas: How does a NNF actually look like? Can it contain ITE operators?
                        mk_nnf_tactic(m, p));
}

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p) {
    tactic * t = and_then(mk_preamble(m, p), mk_sls_tactic(m));    
    t->updt_params(p);
    return t;
}
