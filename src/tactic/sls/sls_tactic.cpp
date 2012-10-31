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

class sls_tactic : public tactic {
    class stats {
    public:
        unsigned        m_restarts;
        stopwatch       m_stopwatch;    
        unsigned        m_full_evals;
        unsigned        m_incr_evals;
        unsigned        m_moves, m_flips, m_incs, m_decs, m_invs;
        stats() :
            m_restarts(0),
            m_full_evals(0),
            m_incr_evals(0),
            m_moves(0),
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
        class score_tracker;

        class powers : public u_map<mpz*> {
            unsynch_mpz_manager & m;
        public:
            powers(unsynch_mpz_manager & m) : m(m) {}
            ~powers() {
                for (iterator it = begin(); it != end(); it++) {
                    m.del(*it->m_value);
                    dealloc(it->m_value);
                }
            }

            const mpz & operator()(unsigned n) {
                u_map<mpz*>::iterator it = find_iterator(n);
                if (it != end())
                    return *it->m_value;
                else {
                    mpz * new_obj = alloc(mpz);
                    insert(n, new_obj);
                    m.power(unsynch_mpz_manager::mk_z(2), n, *new_obj);
                    return *new_obj;
                }
            }
        };

        class evaluator {
            ast_manager         & m_manager;
            bv_util             & m_bv_util;
            family_id             m_bv_fid;
            score_tracker       & m_tracker;
            unsynch_mpz_manager & m_mpz_manager;
            mpz                   m_zero, m_one, m_two;
            powers              & m_powers;
        

        public:
            evaluator(ast_manager & m, bv_util & bvu, score_tracker & t, unsynch_mpz_manager & mm, powers & p) : 
                m_manager(m), 
                m_bv_util(bvu), 
                m_tracker(t),
                m_mpz_manager(mm),
                m_zero(m_mpz_manager.mk_z(0)),
                m_one(m_mpz_manager.mk_z(1)),
                m_two(m_mpz_manager.mk_z(2)),
                m_powers(p) {
                m_bv_fid = m_bv_util.get_family_id();
            }

            ~evaluator() {
                m_mpz_manager.del(m_zero);
                m_mpz_manager.del(m_one);
                m_mpz_manager.del(m_two);            
            }        

            void operator()(app * n, mpz & result) {
                func_decl * fd = n->get_decl();            
                unsigned n_args = n->get_num_args();
                expr * const * args = n->get_args(); 
            
                m_mpz_manager.set(result, m_zero);
            
                if (m_manager.is_and(n)) {
                    m_mpz_manager.set(result, m_one);
                    for (unsigned i = 0; i < n_args; i++) {
                        if (m_mpz_manager.neq(m_tracker.get_value(args[i]), result))  {
                            m_mpz_manager.set(result, m_zero);
                            break;
                        }
                    }
                }
                else if (m_manager.is_or(n)) {
                    for (unsigned i = 0; i < n_args; i++) {
                        if (m_mpz_manager.neq(m_tracker.get_value(args[i]), result)) {
                            m_mpz_manager.set(result, m_one);
                            break;
                        }
                    }
                }
                else if (m_manager.is_not(n)) {
                    SASSERT(n_args == 1);
                    const mpz & child = m_tracker.get_value(args[0]);
                    SASSERT(m_mpz_manager.is_one(child) || m_mpz_manager.is_zero(child));                
                    m_mpz_manager.set(result, (m_mpz_manager.is_zero(child)) ? m_one : m_zero);                
                }
                else if (m_manager.is_eq(n)) {
                    SASSERT(n_args >= 2);
                    m_mpz_manager.set(result, m_one);
                    const mpz & first = m_tracker.get_value(args[0]);
                    for (unsigned i = 1; i < n_args; i++) {
                        if (m_mpz_manager.neq(m_tracker.get_value(args[i]), first)) {
                            m_mpz_manager.set(result, m_zero);
                            break;
                        }
                    }
                }
                else if (m_manager.is_distinct(n)) {
                    m_mpz_manager.set(result, m_one);
                    for (unsigned i = 0; i < n_args && m_mpz_manager.is_one(result); i++) {
                        for (unsigned j = i+1; j < n_args && m_mpz_manager.is_one(result); j++) {
                            if (m_mpz_manager.eq(m_tracker.get_value(args[i]), m_tracker.get_value(args[j])))
                                m_mpz_manager.set(result, m_zero);
                        }
                    }
                }
                else if (fd->get_family_id() == m_bv_fid) {
                    bv_op_kind k = static_cast<bv_op_kind>(fd->get_decl_kind());
                    switch(k) {
                    case OP_CONCAT: {
                        SASSERT(n_args >= 2);
                        for (unsigned i = 0; i < n_args; i++) {                        
                            if (i != 0) {
                                const mpz & p = m_powers(m_bv_util.get_bv_size(args[i]));
                                m_mpz_manager.mul(result, p, result);                            
                            }
                            m_mpz_manager.add(result, m_tracker.get_value(args[i]), result);
                        }
                        break;
                    }
                    case OP_EXTRACT: {
                        SASSERT(n_args == 1);
                        const mpz & child = m_tracker.get_value(args[0]);
                        unsigned h = m_bv_util.get_extract_high(n);
                        unsigned l = m_bv_util.get_extract_low(n);
                
                        mpz mask;
                        m_mpz_manager.set(mask, m_powers(h+1));
                        m_mpz_manager.dec(mask);
                        m_mpz_manager.bitwise_and(child, mask, result); // result = [h:0] of child                
                
                        // shift result by l
                        for (; l != 0 ; l--)
                            m_mpz_manager.machine_div(result, m_two, result);

                        m_mpz_manager.del(mask);
                        break;
                    }
                    case OP_BADD: {
                        SASSERT(n_args >= 2);
                        for (unsigned i = 0; i < n_args; i++) {
                            const mpz & next = m_tracker.get_value(args[i]);                    
                            m_mpz_manager.add(result, next, result);
                        }                
                        const mpz & p = m_powers(m_bv_util.get_bv_size(n));                
                        m_mpz_manager.rem(result, p, result);
                        break;
                    }
                    case OP_BSUB: {
                        SASSERT(n_args == 2);
                        const mpz & p = m_powers(m_bv_util.get_bv_size(n));
                        mpz temp;
                        m_mpz_manager.sub(m_tracker.get_value(args[0]), m_tracker.get_value(args[1]), temp);
                        m_mpz_manager.mod(temp, p, result);
                        m_mpz_manager.del(temp);
                        break;
                    }
                    case OP_BMUL: {
                        SASSERT(n_args >= 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++) {
                            const mpz & next = m_tracker.get_value(args[i]);                    
                            m_mpz_manager.mul(result, next, result);
                        }
                        const mpz & p = m_powers(m_bv_util.get_bv_size(n));                    
                        m_mpz_manager.rem(result, p, result);
                        break;
                    }
                    case OP_BNEG: { // 2's complement unary minus
                        SASSERT(n_args == 1);
                        const mpz & child = m_tracker.get_value(args[0]);
                        if (m_mpz_manager.is_zero(child)) {
                            m_mpz_manager.set(result, m_zero);
                        }
                        else {
                            unsigned bv_sz = m_bv_util.get_bv_size(n);
                            m_mpz_manager.bitwise_not(bv_sz, child, result);
                            m_mpz_manager.inc(result); // can't overflow
                        }
                        break;
                    }
                    case OP_BSDIV:
                    case OP_BSDIV0:              
                    case OP_BSDIV_I: {
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));
                        SASSERT(m_mpz_manager.is_nonneg(x) && m_mpz_manager.is_nonneg(y));
                        unsigned bv_sz = m_bv_util.get_bv_size(args[0]);
                        const mpz & p = m_powers(bv_sz);
                        const mpz & p_half = m_powers(bv_sz-1);
                        if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
                        if (y >= p_half) { m_mpz_manager.sub(y, p, y); }

                        if (m_mpz_manager.is_zero(y)) {
                            if (m_mpz_manager.is_neg(x))
                                m_mpz_manager.set(result, m_one);
                            else {
                                m_mpz_manager.set(result, m_powers(m_bv_util.get_bv_size(n)));
                                m_mpz_manager.dec(result);
                            }
                        }
                        else {
                            m_mpz_manager.machine_div(x, y, result);
                        }
                        if (m_mpz_manager.is_neg(result))
                            m_mpz_manager.add(result, p, result);
                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);                    
                        break;
                    }
                    case OP_BUDIV:
                    case OP_BUDIV0:
                    case OP_BUDIV_I: {
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));
                    
                        if (m_mpz_manager.is_zero(y)) {
                            m_mpz_manager.set(result, m_powers(m_bv_util.get_bv_size(n)));
                            m_mpz_manager.dec(result);
                        }
                        else {
                            m_mpz_manager.machine_div(x, y, result);
                        }
                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);
                        break;
                    }
                    case OP_BSREM: 
                    case OP_BSREM0:
                    case OP_BSREM_I: {
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));
                        unsigned bv_sz = m_bv_util.get_bv_size(args[0]);
                        const mpz & p = m_powers(bv_sz);
                        const mpz & p_half = m_powers(bv_sz-1);
                        if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
                        if (y >= p_half) { m_mpz_manager.sub(y, p, y); }

                        if (m_mpz_manager.is_zero(y)) {                        
                            m_mpz_manager.set(result, x);                        
                        }
                        else {
                            m_mpz_manager.rem(x, y, result);
                        }
                        if (m_mpz_manager.is_neg(result))
                            m_mpz_manager.add(result, p, result);
                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);
                        break;
                    }
                    case OP_BUREM: 
                    case OP_BUREM0:
                    case OP_BUREM_I: {
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));                    

                        if (m_mpz_manager.is_zero(y)) {
                            m_mpz_manager.set(result, x);                        
                        }
                        else {
                            m_mpz_manager.mod(x, y, result);
                        }
                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);
                        break;
                    }
                    case OP_BSMOD: 
                    case OP_BSMOD0:
                    case OP_BSMOD_I:{
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));
                        unsigned bv_sz = m_bv_util.get_bv_size(args[0]);
                        const mpz & p = m_powers(bv_sz);
                        const mpz & p_half = m_powers(bv_sz-1);
                        if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
                        if (y >= p_half) { m_mpz_manager.sub(y, p, y); }                    

                        if (m_mpz_manager.is_zero(y))
                            m_mpz_manager.set(result, x);
                        else {
                            bool neg_x = m_mpz_manager.is_neg(x);
                            bool neg_y = m_mpz_manager.is_neg(y);
                            mpz abs_x, abs_y;
                            m_mpz_manager.set(abs_x, x);
                            m_mpz_manager.set(abs_y, y);
                            if (neg_x) m_mpz_manager.neg(abs_x);
                            if (neg_y) m_mpz_manager.neg(abs_y);
                            SASSERT(m_mpz_manager.is_nonneg(abs_x) && m_mpz_manager.is_nonneg(abs_y));

                            m_mpz_manager.mod(abs_x, abs_y, result);

                            if (m_mpz_manager.is_zero(result) || (!neg_x && !neg_y)) {
                                /* Nothing */
                            }
                            else if (neg_x && !neg_y) {
                                m_mpz_manager.neg(result);
                                m_mpz_manager.add(result, y, result);
                            }
                            else if (!neg_x && neg_y) {
                                m_mpz_manager.add(result, y, result);
                            }
                            else {
                                m_mpz_manager.neg(result);                        
                            }

                            m_mpz_manager.del(abs_x);
                            m_mpz_manager.del(abs_y);
                        }

                        if (m_mpz_manager.is_neg(result))
                            m_mpz_manager.add(result, p, result);

                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);                    
                        break;
                    }
                    case OP_BAND: {
                        SASSERT(n_args >= 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++)
                            m_mpz_manager.bitwise_and(result, m_tracker.get_value(args[i]), result);
                        break;
                    }
                    case OP_BOR: {
                        SASSERT(n_args >= 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++) {
                            m_mpz_manager.bitwise_or(result, m_tracker.get_value(args[i]), result);
                        }
                        break;
                    }
                    case OP_BXOR: {
                        SASSERT(n_args >= 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++)
                            m_mpz_manager.bitwise_xor(result, m_tracker.get_value(args[i]), result);
                        break;
                    }
                    case OP_BNAND: {
                        SASSERT(n_args >= 2);
                        mpz temp;
                        unsigned bv_sz = m_bv_util.get_bv_size(n);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++) {
                            m_mpz_manager.bitwise_and(result, m_tracker.get_value(args[i]), temp);
                            m_mpz_manager.bitwise_not(bv_sz, temp, result);
                        }
                        m_mpz_manager.del(temp);
                        break;
                    }
                    case OP_BNOR: {
                        SASSERT(n_args >= 2);
                        mpz temp;
                        unsigned bv_sz = m_bv_util.get_bv_size(n);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        for (unsigned i = 1; i < n_args; i++) {
                            m_mpz_manager.bitwise_or(result, m_tracker.get_value(args[i]), temp);
                            m_mpz_manager.bitwise_not(bv_sz, temp, result);
                        }
                        m_mpz_manager.del(temp);
                        break;
                    }
                    case OP_BNOT: {
                        SASSERT(n_args == 1);
                        m_mpz_manager.bitwise_not(m_bv_util.get_bv_size(args[0]), m_tracker.get_value(args[0]), result);
                        break;
                    }
                    case OP_ULT:
                    case OP_ULEQ:
                    case OP_UGT:
                    case OP_UGEQ: {
                        SASSERT(n_args == 2);
                        const mpz & x = m_tracker.get_value(args[0]);
                        const mpz & y = m_tracker.get_value(args[1]);
                        if ((k == OP_ULT  && m_mpz_manager.lt(x, y)) ||
                            (k == OP_ULEQ && m_mpz_manager.le(x, y)) ||
                            (k == OP_UGT  && m_mpz_manager.gt(x, y)) ||
                            (k == OP_UGEQ && m_mpz_manager.ge(x, y)))
                            m_mpz_manager.set(result, m_one);
                        break;
                    }
                    case OP_SLT:
                    case OP_SLEQ: 
                    case OP_SGT:
                    case OP_SGEQ: {
                        SASSERT(n_args == 2);
                        mpz x; m_mpz_manager.set(x, m_tracker.get_value(args[0]));
                        mpz y; m_mpz_manager.set(y, m_tracker.get_value(args[1]));
                        unsigned bv_sz = m_bv_util.get_bv_size(args[0]);
                        const mpz & p = m_powers(bv_sz);
                        const mpz & p_half = m_powers(bv_sz-1);
                        if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
                        if (y >= p_half) { m_mpz_manager.sub(y, p, y); } 
                        if ((k == OP_SLT  && m_mpz_manager.lt(x, y)) ||
                            (k == OP_SLEQ && m_mpz_manager.le(x, y)) ||
                            (k == OP_SGT  && m_mpz_manager.gt(x, y)) ||
                            (k == OP_SGEQ && m_mpz_manager.ge(x, y)))
                            m_mpz_manager.set(result, m_one);
                        m_mpz_manager.del(x);
                        m_mpz_manager.del(y);                    
                        break;
                    }
                    case OP_BIT2BOOL: {
                        SASSERT(n_args == 1);
                        const mpz & child = m_tracker.get_value(args[0]);
                        m_mpz_manager.set(result, child);
                        break;
                    }            
                    case OP_BASHR: {
                        SASSERT(n_args == 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        mpz first;
                        const mpz & p = m_powers(m_bv_util.get_bv_size(args[0])-1);
                        m_mpz_manager.bitwise_and(result, p, first);
                        mpz shift; m_mpz_manager.set(shift, m_tracker.get_value(args[1]));
                        mpz temp;
                        while (!m_mpz_manager.is_zero(shift)) {
                            m_mpz_manager.machine_div(result, m_two, temp);
                            m_mpz_manager.add(temp, first, result);
                            m_mpz_manager.dec(shift);
                        }
                        m_mpz_manager.del(first);                 
                        m_mpz_manager.del(shift);
                        m_mpz_manager.del(temp);
                        break;
                    }
                    case OP_BLSHR: {
                        SASSERT(n_args == 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        mpz shift; m_mpz_manager.set(shift, m_tracker.get_value(args[1]));
                        while (!m_mpz_manager.is_zero(shift)) {
                            m_mpz_manager.machine_div(result, m_two, result);
                            m_mpz_manager.dec(shift);
                        }
                        m_mpz_manager.del(shift);
                        break;
                    }
                    case OP_BSHL: {
                        SASSERT(n_args == 2);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));                
                        mpz shift; m_mpz_manager.set(shift, m_tracker.get_value(args[1]));
                        while (!m_mpz_manager.is_zero(shift)) {
                            m_mpz_manager.mul(result, m_two, result);
                            m_mpz_manager.dec(shift);
                        }
                        const mpz & p = m_powers(m_bv_util.get_bv_size(n));
                        m_mpz_manager.rem(result, p, result);
                        m_mpz_manager.del(shift);                    
                        break;
                    }
                    case OP_SIGN_EXT: {
                        SASSERT(n_args == 1);
                        m_mpz_manager.set(result, m_tracker.get_value(args[0]));
                        break;
                    }
                    default: 
                        NOT_IMPLEMENTED_YET();
                    }
                }
                else {
                    NOT_IMPLEMENTED_YET();
                }            

                TRACE("sls_eval", tout << "(" << fd->get_name();
                                    for (unsigned i = 0; i < n_args; i++)
                                        tout << " " << m_mpz_manager.to_string(m_tracker.get_value(args[i]));
                                    tout << ") ---> " <<  m_mpz_manager.to_string(result);
                                    if (m_manager.is_bool(fd->get_range())) tout << " [Boolean]";
                                    else tout << " [vector size: " << m_bv_util.get_bv_size(fd->get_range()) << "]";
                                    tout << std::endl; );

                SASSERT(m_mpz_manager.is_nonneg(result));
            }
        };

        class score_tracker {    
            ast_manager         & m_manager;
            unsynch_mpz_manager & m_mpz_manager;
            bv_util             & m_bv_util;
            powers              & m_powers;
            random_gen            m_rng;
            unsigned              m_random_bits;
            unsigned              m_random_bits_cnt;        
            vector<ptr_vector<expr> > m_traversal_stack;        
            evaluator             m_sls_evaluator;
            mpz                   m_zero, m_one, m_two;

            model                 m_dummy_model;
            model_evaluator       m_evaluator;
            expr_ref_buffer       m_temp_exprs;

            struct value_score { 
                value_score() : m(0), value(unsynch_mpz_manager::mk_z(0)), score(0.0), distance(0) { };
                ~value_score() { if (m) m->del(value); }
                unsynch_mpz_manager * m;
                mpz value;
                double score;
                unsigned distance; // max distance from any root
                value_score & operator=(const value_score & other) {
                    SASSERT(m == 0 || m == other.m);
                    if (m) m->set(value, 0); else m = other.m;
                    m->set(value, other.value);
                    score = other.score;
                    distance = other.distance;
                    return *this;
                }
            };

            typedef obj_map<expr, value_score> scores_type;    
            typedef obj_map<expr, ptr_vector<expr> > uplinks_type;
            typedef obj_map<func_decl, expr* > entry_point_type;
            typedef obj_map<expr, ptr_vector<func_decl> > occ_type;
            scores_type           m_scores;
            uplinks_type          m_uplinks;
            entry_point_type      m_entry_points;
            ptr_vector<func_decl> m_constants;
            ptr_vector<func_decl> m_temp_constants;
            occ_type              m_constants_occ;

        public:
            score_tracker(ast_manager & m, bv_util & bvu, unsynch_mpz_manager & mm, powers & p) :
                m_manager(m),
                m_mpz_manager(mm),
                m_bv_util(bvu),
                m_powers(p),
                m_random_bits_cnt(0),
                m_sls_evaluator(m, m_bv_util, *this, m_mpz_manager, p),
                m_zero(m_mpz_manager.mk_z(0)),
                m_one(m_mpz_manager.mk_z(1)),
                m_two(m_mpz_manager.mk_z(2)),
                m_dummy_model(m),
                m_evaluator(m_dummy_model),
                m_temp_exprs(m) {
            }
            
            ~score_tracker() {
                m_mpz_manager.del(m_zero);
                m_mpz_manager.del(m_one);
                m_mpz_manager.del(m_two);            
            }

            void set_value(expr * n, const mpz & r) {
                SASSERT(m_scores.contains(n));
                m_mpz_manager.set(m_scores.find(n).value, r);
            }

            void set_value(func_decl * fd, const mpz & r) {
                SASSERT(m_entry_points.contains(fd));
                expr * ep = get_entry_point(fd);
                set_value(ep, r);
            }

            mpz & get_value(expr * n) {            
                SASSERT(m_scores.contains(n));
                return m_scores.find(n).value;
            }

            mpz & get_value(func_decl * fd) {
                SASSERT(m_entry_points.contains(fd));
                expr * ep = get_entry_point(fd);
                return get_value(ep);
            }        

            void set_score(expr * n, double score) {
                SASSERT(m_scores.contains(n));
                m_scores.find(n).score = score;
            }

            void set_score(func_decl * fd, double score) {            
                SASSERT(m_entry_points.contains(fd));
                expr * ep = get_entry_point(fd);
                set_score(ep, score);    
            }

            double & get_score(expr * n) {
                SASSERT(m_scores.contains(n));
                return m_scores.find(n).score;
            }

            double & get_score(func_decl * fd) {
                SASSERT(m_entry_points.contains(fd));
                expr * ep = get_entry_point(fd);
                return get_score(ep);
            }

            unsigned get_distance(expr * n) {
                SASSERT(m_scores.contains(n));
                return m_scores.find(n).distance;
            }

            void set_distance(expr * n, unsigned d) {
                SASSERT(m_scores.contains(n));
                m_scores.find(n).distance = d;
            }

            expr * get_entry_point(func_decl * fd) {
                SASSERT(m_entry_points.contains(fd));
                return m_entry_points.find(fd);
            }

            bool has_uplinks(expr * n) {
                return m_uplinks.contains(n);
            }

            ptr_vector<expr> & get_uplinks(expr * n) {
                SASSERT(m_uplinks.contains(n));
                return m_uplinks.find(n);
            }

            void initialize(app * n) {
                // Build score table
                if (!m_scores.contains(n)) {
                    value_score vs;
                    vs.m = & m_mpz_manager;
                    m_scores.insert(n, vs);
                }

                // Update uplinks
                unsigned na = n->get_num_args();
                for (unsigned i = 0; i < na; i++) {
                    expr * c = n->get_arg(i); 
                    uplinks_type::obj_map_entry * entry = m_uplinks.insert_if_not_there2(c, ptr_vector<expr>());
                    entry->get_data().m_value.push_back(n);
                }

                func_decl * d = n->get_decl();

                if (n->get_num_args() == 0) {
                    if (d->get_family_id() != null_family_id) {
                        // Interpreted constant
                        mpz t;
                        value2mpz(n, t);
                        set_value(n, t);
                        m_mpz_manager.del(t);
                    }
                    else {
                        // Uninterpreted constant
                        m_entry_points.insert_if_not_there(d, n);
                        m_constants.push_back(d);
                    }
                }            
            }

            struct init_proc {
                ast_manager   & m_manager;        
                score_tracker & m_tracker;

                init_proc(ast_manager & m, score_tracker & tracker):
                    m_manager(m),
                    m_tracker(tracker) {
                }
        
                void operator()(var * n) {}
        
                void operator()(quantifier * n) {}
        
                void operator()(app * n) {
                    m_tracker.initialize(n);
                }
            };

            struct find_func_decls_proc {
                ast_manager   & m_manager;        
                ptr_vector<func_decl> & m_occs;

                find_func_decls_proc (ast_manager & m, ptr_vector<func_decl> & occs):
                    m_manager(m),
                    m_occs(occs) {
                }
        
                void operator()(var * n) {}
        
                void operator()(quantifier * n) {}
        
                void operator()(app * n) {
                    if (n->get_num_args() != 0)
                        return;
                    func_decl * d = n->get_decl();
                    if (d->get_family_id() != null_family_id)
                        return;
                    m_occs.push_back(d);
                }
            };

            void calculate_expr_distances(goal_ref const & g) {
                // precondition: m_scores is set up.
                unsigned sz = g->size();
                ptr_vector<app> stack;
                for (unsigned i = 0; i < sz; i++)
                    stack.push_back(to_app(g->form(i)));
                while (!stack.empty()) {
                    app * cur = stack.back();
                    stack.pop_back();
                
                    unsigned d = get_distance(cur);

                    for (unsigned i = 0; i < cur->get_num_args(); i++) {
                        app * child = to_app(cur->get_arg(i));                    
                        unsigned d_child = get_distance(child);
                        if (d >= d_child) {
                            set_distance(child, d+1);
                            stack.push_back(child);
                        }
                    }
                }
            }

            void initialize(goal_ref const & g) {
                init_proc proc(m_manager, *this);
                expr_mark visited;
                unsigned sz = g->size();
                for (unsigned i = 0; i < sz; i++) {
                    expr * e = g->form(i);                
                    for_each_expr(proc, visited, e);
                }

                visited.reset();

                for (unsigned i = 0; i < sz; i++) {
                    expr * e = g->form(i);
                    ptr_vector<func_decl> t;
                    m_constants_occ.insert_if_not_there(e, t);
                    find_func_decls_proc ffd_proc(m_manager, m_constants_occ.find(e));
                    expr_fast_mark1 visited;
                    quick_for_each_expr(ffd_proc, visited, e);
                }

                calculate_expr_distances(g);

                TRACE("sls", tout << "Initial model:" << std::endl; show_model(tout); );
            }

            void show_model(std::ostream & out) {
                unsigned sz = get_num_constants();
                for (unsigned i = 0; i < sz; i++) {
                    func_decl * fd = get_constant(i);
                    out << fd->get_name() << " = " << m_mpz_manager.to_string(get_value(fd)) << std::endl;
                }
            }

            model_ref get_model() {
                model_ref res = alloc(model, m_manager);
                unsigned sz = get_num_constants();
                for (unsigned i = 0; i < sz; i++) {
                    func_decl * fd = get_constant(i);
                    res->register_decl(fd, mpz2value(fd->get_range(), get_value(fd)));
                }
                return res;
            }

            unsigned get_num_constants() {
                return m_constants.size();
            }

            ptr_vector<func_decl> & get_constants() {
                return m_constants;
            }

            func_decl * get_constant(unsigned i) {
                return m_constants[i];
            }

            void set_random_seed(unsigned s) {
                m_rng.set_seed(s);
            }

            mpz get_random_bv(sort * s) {
                SASSERT(m_bv_util.is_bv_sort(s));
                unsigned bv_size = m_bv_util.get_bv_size(s);
                mpz r; m_mpz_manager.set(r, 0);            

                mpz temp;
                do
                {                
                    m_mpz_manager.mul(r, m_two, temp);                
                    m_mpz_manager.add(temp, get_random_bool(), r);
                } while (--bv_size > 0);            
                m_mpz_manager.del(temp);

                return r;
            }

            mpz & get_random_bool() {
                if (m_random_bits_cnt == 0) {
                    m_random_bits = m_rng();
                    m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
                }

                bool val = (m_random_bits & 0x01) != 0;
                m_random_bits = m_random_bits >> 1;
                m_random_bits_cnt--;

                return (val) ? m_one : m_zero;
            }

            unsigned get_random_uint(unsigned bits) {
                if (m_random_bits_cnt == 0) {
                    m_random_bits = m_rng();
                    m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
                }

                unsigned val = 0;
                while (bits-- > 0) {
                    if ((m_random_bits & 0x01) != 0) val++;
                    val <<= 1;
                    m_random_bits >>= 1;
                    m_random_bits_cnt--;

                    if (m_random_bits_cnt == 0) {
                        m_random_bits = m_rng();
                        m_random_bits_cnt = 15; // random_gen produces 15 bits of randomness.
                    }
                }

                return val;
            }

            mpz get_random(sort * s) {
                if (m_bv_util.is_bv_sort(s))
                    return get_random_bv(s);
                else if (m_manager.is_bool(s))
                    return get_random_bool();
                else
                    NOT_IMPLEMENTED_YET(); // This only works for bit-vectors for now.
            }    

            void randomize() {
                TRACE("sls", tout << "Abandoned model:" << std::endl; show_model(tout); );

                for (entry_point_type::iterator it = m_entry_points.begin(); it != m_entry_points.end(); it++) {
                    func_decl * fd = it->m_key;
                    sort * s = fd->get_range();
                    mpz temp = get_random(s);
                    set_value(it->m_value, temp);
                    m_mpz_manager.del(temp);
                }

                TRACE("sls", tout << "Randomized model:" << std::endl; show_model(tout); );
            }

            void randomize_local(goal_ref const & g) {
                ptr_vector<func_decl> & unsat_constants = get_unsat_constants(g);
                // bool did_something = false;
                for (unsigned i = 0; i < unsat_constants.size(); i++) {
                    func_decl * fd = unsat_constants[i];
                    mpz temp = get_random(fd->get_range());
                    if (m_mpz_manager.neq(temp, get_value(fd))) {
                        // did_something = true;
                    }
                    update(fd, temp);
                    m_mpz_manager.del(temp);
                }
                TRACE("sls", tout << "Randomization candidates: ";
                             for (unsigned i = 0; i < unsat_constants.size(); i++)
                                 tout << unsat_constants[i]->get_name() << ", ";
                             tout << std::endl;
                             tout << "Locally randomized model: " << std::endl; show_model(tout); );
            }            

    #define _SCORE_AND_MIN

            double score_bool(expr * n, bool negated = false) {
                TRACE("sls_score", tout << ((negated)?"NEG ":"") << "BOOL: " << mk_ismt2_pp(n, m_manager) << std::endl; );

                double res = 0.0;
            
                if (is_uninterp_const(n)) {
                    const mpz & r = get_value(n);
                    if (negated)
                        res = (m_mpz_manager.is_one(r)) ? 0.0 : 1.0;
                    else
                        res = (m_mpz_manager.is_one(r)) ? 1.0 : 0.0;
                }            
                else if (m_manager.is_and(n)) {
                    SASSERT(!negated);
                    app * a = to_app(n);
                    expr * const * args = a->get_args();
                    #ifdef _SCORE_AND_MIN
                    double min = 1.0;
                    for (unsigned i = 0; i < a->get_num_args(); i++) {
                        double cur = get_score(args[i]);
                        if (cur < min) min = cur;
                    }
                    res = min;
                    #else 
                    double sum = 0.0;
                    for (unsigned i = 0; i < a->get_num_args(); i++)
                        sum += get_score(args[i]);
                    res = sum / (double) a->get_num_args();
                    #endif
                }
                else if (m_manager.is_or(n)) {
                    SASSERT(!negated);
                    app * a = to_app(n);
                    expr * const * args = a->get_args();
                    double max = 0.0;
                    for (unsigned i = 0; i < a->get_num_args(); i++) {
                        double cur = get_score(args[i]);
                        if (cur > max) max = cur;
                    }
                    res = max;
                }
                else if (m_manager.is_ite(n)) {
                    SASSERT(!negated);
                    app * a = to_app(n);
                    SASSERT(a->get_num_args() == 3);
                    const mpz & cond = get_value(a->get_arg(0));
                    double s_t = get_score(a->get_arg(1));
                    double s_f = get_score(a->get_arg(2));
                    res = (m_mpz_manager.is_one(cond)) ? s_t : s_f;
                }
                else if (m_manager.is_eq(n) || m_manager.is_iff(n)) {                
                    app * a = to_app(n);
                    SASSERT(a->get_num_args() == 2);
                    expr * arg0 = a->get_arg(0);
                    expr * arg1 = a->get_arg(1);
                    const mpz & v0 = get_value(arg0);
                    const mpz & v1 = get_value(arg1);

                    if (negated) {                    
                        res = (m_mpz_manager.eq(v0, v1)) ? 0.0 : 1.0;
                        TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                                m_mpz_manager.to_string(v1) << std::endl; );
                    }
                    else if (m_manager.is_bool(arg0)) {
                        res = m_mpz_manager.eq(v0, v1) ? 1.0 : 0.0;
                        TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                                m_mpz_manager.to_string(v1) << std::endl; );
                    }
                    else if (m_bv_util.is_bv(arg0)) {
                        mpz diff, diff_m1;
                        m_mpz_manager.bitwise_xor(v0, v1, diff);
                        unsigned hamming_distance = 0;
                        unsigned bv_sz = m_bv_util.get_bv_size(arg0);
                        #if 1 // unweighted hamming distance
                        while (!m_mpz_manager.is_zero(diff)) {
                            //m_mpz_manager.set(diff_m1, diff);
                            //m_mpz_manager.dec(diff_m1);
                            //m_mpz_manager.bitwise_and(diff, diff_m1, diff);
                            //hamming_distance++;
                            if (!m_mpz_manager.is_even(diff)) {
                                hamming_distance++;
                            }
                            m_mpz_manager.machine_div(diff, m_two, diff);
                        }
                        res = 1.0 - (hamming_distance / (double) bv_sz);                    
                        #else                    
                        rational r(diff);
                        r /= m_powers(bv_sz);
                        double dbl = r.get_double();
                        res = (dbl < 0.0) ? 1.0 : (dbl > 1.0) ? 0.0 : 1.0 - dbl;
                        #endif
                        TRACE("sls_score", tout << "V0 = " << m_mpz_manager.to_string(v0) << " ; V1 = " << 
                                                m_mpz_manager.to_string(v1) << " ; HD = " << hamming_distance << 
                                                " ; SZ = " << bv_sz << std::endl; );                    
                        m_mpz_manager.del(diff);
                        m_mpz_manager.del(diff_m1);
                    }
                    else
                        NOT_IMPLEMENTED_YET();
                }            
                else if (m_bv_util.is_bv_ule(n)) { // x <= y
                    app * a = to_app(n);
                    SASSERT(a->get_num_args() == 2);
                    const mpz & x = get_value(a->get_arg(0));
                    const mpz & y = get_value(a->get_arg(1));
                    unsigned bv_sz = m_bv_util.get_bv_size(a->get_decl()->get_domain()[0]);

                    if (negated) {
                        if (m_mpz_manager.gt(x, y))
                            res = 1.0; 
                        else {
                            mpz diff;
                            m_mpz_manager.sub(y, x, diff);
                            m_mpz_manager.inc(diff);                            
                            rational n(diff);
                            n /= rational(m_powers(bv_sz));                            
                            double dbl = n.get_double();
                            // In extreme cases, n is 0.9999 but to_double returns something > 1.0
                            res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                            m_mpz_manager.del(diff);
                        }
                    }
                    else {
                        if (m_mpz_manager.le(x, y))                        
                            res = 1.0; 
                        else {
                            mpz diff;
                            m_mpz_manager.sub(x, y, diff);
                            rational n(diff);
                            n /= rational(m_powers(bv_sz));
                            double dbl = n.get_double();
                            res = (dbl > 1.0) ? 1.0 : (dbl < 0.0) ? 0.0 : dbl;
                            m_mpz_manager.del(diff);
                        }
                    }
                    TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                            m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
                }
                else if (m_bv_util.is_bv_sle(n)) { // x <= y
                    app * a = to_app(n);
                    SASSERT(a->get_num_args() == 2);
                    mpz x; m_mpz_manager.set(x, get_value(a->get_arg(0)));
                    mpz y; m_mpz_manager.set(y, get_value(a->get_arg(1)));
                    unsigned bv_sz = m_bv_util.get_bv_size(a->get_decl()->get_domain()[0]);
                    const mpz & p = m_powers(bv_sz);
                    const mpz & p_half = m_powers(bv_sz-1);
                    if (x >= p_half) { m_mpz_manager.sub(x, p, x); } 
                    if (y >= p_half) { m_mpz_manager.sub(y, p, y); }                 

                    if (negated) {
                        if (x > y)
                            res = 1.0;
                        else {
                            mpz diff;
                            m_mpz_manager.sub(y, x, diff);
                            m_mpz_manager.inc(diff);
                            rational n(diff);
                            n /= p;
                            double dbl = n.get_double();
                            res = (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
                            m_mpz_manager.del(diff);
                        }
                        TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                                m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
                    }
                    else {
                        if (x <= y)
                            res = 1.0;
                        else {
                            mpz diff;
                            m_mpz_manager.sub(x, y, diff);
                            rational n(diff);
                            n /= p;
                            double dbl = n.get_double();
                            res = (dbl > 1.0) ? 1.0 : (dbl < 0.0) ? 0.0 : dbl;
                            m_mpz_manager.del(diff);
                        }
                        TRACE("sls_score", tout << "x = " << m_mpz_manager.to_string(x) << " ; y = " << 
                                                m_mpz_manager.to_string(y) << " ; SZ = " << bv_sz << std::endl; );
                    }
                    m_mpz_manager.del(x);
                    m_mpz_manager.del(y);                
                }
                else if (m_manager.is_not(n)) {                
                    SASSERT(!negated);
                    app * a = to_app(n);
                    SASSERT(a->get_num_args() == 1);
                    expr * child = a->get_arg(0);
                    if (m_manager.is_and(child) || m_manager.is_or(child)) // Precondition: Assertion set is in NNF.
                        NOT_IMPLEMENTED_YET();
                    res = score_bool(child, true);
                }
                else if (m_manager.is_distinct(n)) {
                    app * a = to_app(n);
                    unsigned pairs = 0, distinct_pairs = 0;
                    unsigned sz = a->get_num_args();
                    for (unsigned i = 0; i < sz; i++) {
                        for (unsigned j = i+1; j < sz; j++) {
                            // pair i/j
                            const mpz & v0 = get_value(a->get_arg(0));
                            const mpz & v1 = get_value(a->get_arg(1));
                            pairs++;
                            if (v0 != v1)
                                distinct_pairs++;
                        }
                    }                
                    res = (distinct_pairs/(double)pairs);
                    if (negated) res = 1.0 - res;
                }
                else
                    NOT_IMPLEMENTED_YET();

                SASSERT(res >= 0.0 && res <= 1.0);

                TRACE("sls_score", tout << "SCORE = " << res << std::endl; );
                return res;
            }

            double score_bv(expr * n) {
                return 0.0; // a bv-expr is always scored as 0.0; we won't use those scores.
            }

            void value2mpz(expr * n, mpz & result) {
                m_mpz_manager.set(result, m_zero);

                if (m_manager.is_bool(n)) {
                    m_mpz_manager.set(result, m_manager.is_true(n) ? m_one : m_zero);
                }
                else if (m_bv_util.is_bv(n)) {
                    unsigned bv_sz = m_bv_util.get_bv_size(n);
                    rational q;
                    if (!m_bv_util.is_numeral(n, q, bv_sz))
                        NOT_IMPLEMENTED_YET();
                    mpq temp = q.to_mpq();
                    SASSERT(m_mpz_manager.is_one(temp.denominator()));
                    m_mpz_manager.set(result, temp.numerator());
                }
                else
                    NOT_IMPLEMENTED_YET();            
            }

            expr_ref mpz2value(sort * s, const mpz & r) {
                expr_ref res(m_manager);
                if (m_manager.is_bool(s))
                    res = (m_mpz_manager.is_zero(r)) ? m_manager.mk_false() : m_manager.mk_true();
                else if (m_bv_util.is_bv_sort(s)) {
                    rational rat(r);
                    res = m_bv_util.mk_numeral(rat, s);
                }
                else
                    NOT_IMPLEMENTED_YET();
                return res;
            }

            void eval(expr * n, mpz & result) {
                switch(n->get_kind()) {
                case AST_APP: {
                    app * a = to_app(n);
                    unsigned n_args = a->get_num_args();

                    if (n_args == 0) {                    
                        m_mpz_manager.set(result, get_value(n));
                    }
                    else {
                        m_sls_evaluator(a, result);

                    //#define _EVAL_CHECKED
                    #ifdef _EVAL_CHECKED
                        m_temp_exprs.reset();
                        for (unsigned i = 0; i < n_args; i++) {
                            expr * arg = a->get_arg(i);
                            const mpz & v = get_value(arg);
                            m_temp_exprs.push_back(mpz2value(m_manager.get_sort(arg), v));
                        }
                        expr_ref q(m_manager), temp(m_manager);
                        q = m_manager.mk_app(fd, m_temp_exprs.size(), m_temp_exprs.c_ptr());                                
                        m_evaluator(q, temp);
                        mpz check_res;
                        value2mpz(temp, check_res);
                        if (!m_mpz_manager.eq(check_res, result))
                            TRACE("sls", tout << "EVAL BUG: IS " << m_mpz_manager.to_string(result) << 
                                                    " SHOULD BE " << m_mpz_manager.to_string(check_res) << std::endl; );
                        SASSERT(m_mpz_manager.eq(check_res, result));
                        m_mpz_manager.del(check_res);
                    #endif
                    }
                    break;
                }
                default: 
                    NOT_IMPLEMENTED_YET();
                }
                // TRACE("sls", tout << "EVAL: " << mk_ismt2_pp(n, m_manager) << " IS " << res << std::endl;); 
            }

            double score(expr * n) {
                if (m_manager.is_bool(n))
                    return score_bool(n);
                else if (m_bv_util.is_bv(n))
                    return score_bv(n);
                else
                    NOT_IMPLEMENTED_YET();
            }

            void run_update(unsigned cur_depth) {
                // precondition: m_traversal_stack contains the entry point(s)
                expr_fast_mark1 visited;
                mpz new_value;

                SASSERT(cur_depth < m_traversal_stack.size());
                while (cur_depth != static_cast<unsigned>(-1)) {
                    ptr_vector<expr> & cur_depth_exprs = m_traversal_stack[cur_depth];

                    for (unsigned i = 0; i < cur_depth_exprs.size(); i++) {
                        expr * cur = cur_depth_exprs[i];

                        eval(cur, new_value);
                        set_value(cur, new_value);
                        set_score(cur, score(cur));

                        if (has_uplinks(cur)) {
                            ptr_vector<expr> & ups = get_uplinks(cur);
                            for (unsigned j = 0; j < ups.size(); j++) {
                                expr * next = ups[j];
                                unsigned next_d = get_distance(next);
                                SASSERT(next_d < cur_depth);
                                if (!visited.is_marked(next)) {
                                    m_traversal_stack[next_d].push_back(next);
                                    visited.mark(next);
                                }
                            }
                        }
                    }

                    cur_depth_exprs.reset();
                    cur_depth--;
                }

                m_mpz_manager.del(new_value);
            }
        
            void update_all() {
                unsigned max_depth = 0;

                for (entry_point_type::iterator it = m_entry_points.begin(); 
                        it != m_entry_points.end(); 
                        it++) {
                    expr * ep = get_entry_point(it->m_key);
                    unsigned cur_depth = get_distance(ep);
                    if (m_traversal_stack.size() <= cur_depth) 
                        m_traversal_stack.resize(cur_depth+1);
                    m_traversal_stack[cur_depth].push_back(ep);
                    if (cur_depth > max_depth) max_depth = cur_depth;
                }

                run_update(max_depth);
            }

            void update(func_decl * fd, const mpz & new_value) {
                set_value(fd, new_value);
                expr * ep = get_entry_point(fd);
                unsigned cur_depth = get_distance(ep);
                if (m_traversal_stack.size() <= cur_depth) 
                    m_traversal_stack.resize(cur_depth+1);
                m_traversal_stack[cur_depth].push_back(ep);

                run_update(cur_depth);
            }

            ptr_vector<func_decl> & get_unsat_constants(goal_ref const & g) {
                unsigned sz = g->size();

                if (sz == 1) {
                    return get_constants();
                }
                else {
                    m_temp_constants.reset();
                    for (unsigned i = 0; i < sz; i++) {
                        expr * q = g->form(i);
                        if (m_mpz_manager.eq(get_value(q), m_one))
                            continue;
                        ptr_vector<func_decl> const & this_decls = m_constants_occ.find(q);
                        unsigned sz2 = this_decls.size();
                        for (unsigned j = 0; j < sz2; j++) {
                            func_decl * fd = this_decls[j];
                            if (!m_temp_constants.contains(fd))
                                m_temp_constants.push_back(fd);
                        }
                    }
                    return m_temp_constants;
                }
            }
        };

        ast_manager   & m_manager;
        stats         & m_stats;
        unsynch_mpz_manager m_mpz_manager;
        powers          m_powers;
        mpz             m_zero, m_one, m_two;            
        bool            m_produce_models;
        volatile bool   m_cancel;    
        bv_util         m_bv_util;
        score_tracker   m_tracker;

        unsigned        m_max_restarts;
        unsigned        m_plateau_limit;

        typedef enum { MV_FLIP = 0, MV_INC, MV_DEC, MV_INV } move_type;        

        imp(ast_manager & m, params_ref const & p, stats & s) : 
            m_manager(m),
            m_stats(s),
            m_powers(m_mpz_manager),
            m_zero(m_mpz_manager.mk_z(0)),
            m_one(m_mpz_manager.mk_z(1)),
            m_two(m_mpz_manager.mk_z(2)),
            m_bv_util(m),
            m_tracker(m, m_bv_util, m_mpz_manager, m_powers)
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
            insert_produce_models(r);
            r.insert(":sls-restarts", CPK_UINT, "(default: infty) # of SLS restarts.");
            r.insert(":random-seed", CPK_UINT, "(default: 0) random seed.");
            r.insert(":plateau-limit", CPK_UINT, "(default: 100) SLS plateau limit.");
        }

        void updt_params(params_ref const & p) {        
            m_produce_models = p.get_bool(":produce-models", false);        
            m_max_restarts = p.get_uint(":sls-restarts", -1);
            m_tracker.set_random_seed(p.get_uint(":random-seed", 0));
            m_plateau_limit = p.get_uint(":plateau-limit", 100);
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
                top_sum += m_tracker.get_score(g->form(i));
            }
            TRACE("sls_top", tout << "Score distribution:"; 
                                    for (unsigned i = 0; i < sz; i++)
                                        tout << " " << m_tracker.get_score(g->form(i));
                                    tout << " AVG: " << top_sum / (double) sz << std::endl; );
            return top_sum / (double) sz;
            #endif
        }

        double rescore(goal_ref const & g) {
            m_tracker.update_all();
            m_stats.m_full_evals++;
            return top_score(g);
        }

        double incremental_score(goal_ref const & g, func_decl * fd, const mpz & new_value) {
            m_tracker.update(fd, new_value);
            m_stats.m_incr_evals++;
            return top_score(g);
        }

        bool what_if(goal_ref const & g, func_decl * fd, const unsigned & fd_inx, const mpz & temp, 
                        double & best_score, unsigned & best_const, mpz & best_value) {
        
            #ifdef _DEBUG
            mpz old_value;
            m_mpz_manager.set(old_value, m_tracker.get_value(fd));
            #endif

            double r = incremental_score(g, fd, temp);
        
            #ifdef _DEBUG
            TRACE("sls_whatif", tout << "WHAT IF " << fd->get_name() << " WERE " << m_mpz_manager.to_string(temp) << 
                                        " --> " << r << std::endl; );
        
            m_mpz_manager.del(old_value);
            #endif

            if (r >= best_score) {
                best_score = r;
                best_const = fd_inx;            
                m_mpz_manager.set(best_value, temp);
                return true;
            }

            return false;
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
            if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv=2;
            if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv++;
            move_type mt = (move_type) rnd_mv;

            // inversion doesn't make sense, let's do a flip instead.
            if (mt == MV_INV) mt = MV_FLIP;

            ptr_vector<func_decl> & unsat_constants = m_tracker.get_unsat_constants(g);                
            unsigned ucc = unsat_constants.size(); 
            unsigned rc = (m_tracker.get_random_uint((ucc < 16) ? 4 : (ucc < 256) ? 8 : (ucc < 4096) ? 12 : (ucc < 65536) ? 16 : 32)) % ucc;
            func_decl * fd = unsat_constants[rc];
            mpz new_value;
            unsigned bit = 0;

            switch (mt)
            {
            case MV_FLIP: {
                unsigned bv_sz = m_bv_util.get_bv_size(fd->get_range());
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

            m_tracker.update(fd, new_value);            

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

            m_mpz_manager.del(new_value);
        }

        double find_best_move(goal_ref const & g, ptr_vector<func_decl> & to_evaluate, double score, 
                              unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move) {
            mpz old_value, temp;
            unsigned bv_sz;
            double new_score = score;

            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0 ; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                // first try to flip every bit
                for (unsigned j = 0; j < bv_sz && new_score < 1.0; j++) {
                    // What would happen if we flipped bit #i ?                
                    mk_flip(srt, old_value, j, temp);                

                    if (what_if(g, fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = j;
                        move = MV_FLIP;
                    }
                }

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
                }

                // reset to what it was before
                double check = incremental_score(g, fd, old_value);
                SASSERT(check == score);
            }

            m_mpz_manager.del(old_value);
            m_mpz_manager.del(temp);
            return new_score;
        }        

        lbool search(goal_ref const & g) {        
            lbool res = l_undef;
            double score = 0.0, old_score = 0.0;
            unsigned new_const = -1, new_bit = 0;        
            mpz new_value;
            move_type move;
            
            score = rescore(g);
            TRACE("sls", tout << "Starting search, initial score   = " << std::setprecision(32) << score << std::endl;
                         tout << "Score distribution:"; 
                         for (unsigned i = 0; i < g->size(); i++)
                             tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                         tout << " TOP: " << score << std::endl; ); 
        
            unsigned plateau_cnt = 0;

            while (plateau_cnt < m_plateau_limit) {                

                do {
                    checkpoint();
            
                    old_score = score;
                    new_const = -1;
                        
                    ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants(g);

                    TRACE("sls_constants", tout << "Evaluating these constants: " << std::endl;
                                            for (unsigned i = 0 ; i < to_evaluate.size(); i++)
                                                tout << to_evaluate[i]->get_name() << std::endl; );

                    score = find_best_move(g, to_evaluate, score, new_const, new_value, new_bit, move);

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
                        score = old_score;
                    }
                    else {
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
                        }
                    
                        score = incremental_score(g, fd, new_value);    

                        TRACE("sls", tout << "Score distribution:"; 
                                        for (unsigned i = 0; i < g->size(); i++)
                                            tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                                        tout << " TOP: " << score << std::endl; );                        
                    }

                    if (score >= 1.0) {
                        // score could theoretically be imprecise.
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
                while (score > old_score && res == l_undef);                

                if (score != old_score)
                    plateau_cnt = 0;
                else {
                    plateau_cnt++;
                    if (plateau_cnt < m_plateau_limit) {
                        m_tracker.randomize_local(g);
                        //mk_random_move(g);
                        score = top_score(g);
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

            m_tracker.initialize(g);
            lbool res = l_undef;
        
            do {
                checkpoint();
                if ((m_stats.m_restarts % 100) == 0)                        
                    report_tactic_progress("Searching... restarts left:", m_max_restarts - m_stats.m_restarts);
                
                res = search(g);

                if (res == l_undef)
                    m_tracker.randomize();
            }
            while (res != l_true && m_stats.m_restarts++ < m_max_restarts);
        
            if (res == l_true) {                
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
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            d = m_imp;
        }
        dealloc(d);
        d = alloc(imp, m, m_params, m_stats);
        #pragma omp critical (tactic_cancel) 
        {
            m_imp = d;
        }
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
    main_p.set_bool(":elim-and", true);
    // main_p.set_bool(":pull-cheap-ite", true);
    main_p.set_bool(":push-ite-bv", true);
    main_p.set_bool(":blast-distinct", true);
    // main_p.set_bool(":udiv2mul", true);
    main_p.set_bool(":hi-div0", true);

    params_ref simp2_p = p;
    simp2_p.set_bool(":som", true);
    simp2_p.set_bool(":pull-cheap-ite", true);
    simp2_p.set_bool(":push-ite-bv", false);
    simp2_p.set_bool(":local-ctx", true);
    simp2_p.set_uint(":local-ctx-limit", 10000000);

    params_ref hoist_p;
    hoist_p.set_bool(":hoist-mul", true);
    // hoist_p.set_bool(":hoist-cmul", true);
    hoist_p.set_bool(":som", false);

    params_ref gaussian_p;
    // conservative gaussian elimination. 
    gaussian_p.set_uint(":gaussian-max-occs", 2); 

    return and_then(and_then(mk_simplify_tactic(m),                             
                             mk_propagate_values_tactic(m),
                             using_params(mk_solve_eqs_tactic(m), gaussian_p),
                             mk_elim_uncnstr_tactic(m),
                             mk_bv_size_reduction_tactic(m),
                             using_params(mk_simplify_tactic(m), simp2_p)),
                        using_params(mk_simplify_tactic(m), hoist_p),
                        mk_max_bv_sharing_tactic(m),
                        mk_nnf_tactic(m, p));
}

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p) {
    params_ref sls_p(p);
    sls_p.set_uint(":sls-restarts", 10000);
    sls_p.set_uint(":plateau-limit", 100);

    tactic * t = and_then(mk_preamble(m, p),
                          using_params(mk_sls_tactic(m, p), sls_p));
    
    t->updt_params(p);
    return t;
}
