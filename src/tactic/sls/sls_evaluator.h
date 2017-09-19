/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_evaluator.h

Abstract:

    SLS Evaluator

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/

#ifndef SLS_EVALUATOR_H_
#define SLS_EVALUATOR_H_

#include "model/model_evaluator.h"

#include "tactic/sls/sls_powers.h"
#include "tactic/sls/sls_tracker.h"

class sls_evaluator {
    ast_manager         & m_manager;
    bv_util             & m_bv_util;
    family_id             m_basic_fid;
    family_id             m_bv_fid;
    sls_tracker         & m_tracker;
    unsynch_mpz_manager & m_mpz_manager;
    mpz                   m_zero, m_one, m_two;
    powers              & m_powers;
    expr_ref_buffer       m_temp_exprs;
    vector<ptr_vector<expr> > m_traversal_stack;
    vector<ptr_vector<expr> > m_traversal_stack_bool;

public:
    sls_evaluator(ast_manager & m, bv_util & bvu, sls_tracker & t, unsynch_mpz_manager & mm, powers & p) : 
        m_manager(m), 
        m_bv_util(bvu), 
        m_tracker(t),
        m_mpz_manager(mm),
        m_zero(m_mpz_manager.mk_z(0)),
        m_one(m_mpz_manager.mk_z(1)),
        m_two(m_mpz_manager.mk_z(2)),
        m_powers(p),
        m_temp_exprs(m) {
        m_bv_fid = m_bv_util.get_family_id();
        m_basic_fid = m_manager.get_basic_family_id();
    }

    ~sls_evaluator() {
        m_mpz_manager.del(m_zero);
        m_mpz_manager.del(m_one);
        m_mpz_manager.del(m_two);            
    }
    
    void operator()(app * n, mpz & result) {
        family_id nfid = n->get_family_id();
        func_decl * fd = n->get_decl();
        unsigned n_args = n->get_num_args();

        if (n_args == 0) {
            m_mpz_manager.set(result, m_tracker.get_value(n));
            return;
        }

        expr * const * args = n->get_args(); 
            
        m_mpz_manager.set(result, m_zero);
            
        if (nfid == m_basic_fid) {
            switch (n->get_decl_kind()) {
            case OP_AND: {
                m_mpz_manager.set(result, m_one);
                for (unsigned i = 0; i < n_args; i++)
                    if (m_mpz_manager.neq(m_tracker.get_value(args[i]), result))  {
                        m_mpz_manager.set(result, m_zero);
                        break;
                    }
                break;
            }
            case OP_OR: {
                for (unsigned i = 0; i < n_args; i++)
                    if (m_mpz_manager.neq(m_tracker.get_value(args[i]), result)) {
                        m_mpz_manager.set(result, m_one);
                        break;
                    }
                break;
            }
            case OP_NOT: {
                SASSERT(n_args == 1);
                const mpz & child = m_tracker.get_value(args[0]);
                SASSERT(m_mpz_manager.is_one(child) || m_mpz_manager.is_zero(child));                
                m_mpz_manager.set(result, (m_mpz_manager.is_zero(child)) ? m_one : m_zero);
                break;
            }
            case OP_EQ: {
                SASSERT(n_args >= 2);
                m_mpz_manager.set(result, m_one);
                const mpz & first = m_tracker.get_value(args[0]);
                for (unsigned i = 1; i < n_args; i++) 
                    if (m_mpz_manager.neq(m_tracker.get_value(args[i]), first)) {
                        m_mpz_manager.set(result, m_zero);
                        break;
                    }
                break;
            }
            case OP_DISTINCT: {
                m_mpz_manager.set(result, m_one);
                for (unsigned i = 0; i < n_args && m_mpz_manager.is_one(result); i++) {
                    for (unsigned j = i+1; j < n_args && m_mpz_manager.is_one(result); j++) {
                        if (m_mpz_manager.eq(m_tracker.get_value(args[i]), m_tracker.get_value(args[j])))
                            m_mpz_manager.set(result, m_zero);
                    }
                }
                break;
            }
            case OP_ITE: {
                SASSERT(n_args = 3);
                if (m_mpz_manager.is_one(m_tracker.get_value(args[0])))
                    m_mpz_manager.set(result, m_tracker.get_value(args[1]));
                else
                    m_mpz_manager.set(result, m_tracker.get_value(args[2]));
                break;
            }
            default:
                NOT_IMPLEMENTED_YET();
            }
        }
        else if (nfid == m_bv_fid) {
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

                m_mpz_manager.rem(child, m_powers(h+1), result); // result = [h:0] of child
                m_mpz_manager.machine_div2k(result, l, result);
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

    void eval_checked(expr * n, mpz & result) {
        switch(n->get_kind()) {
        case AST_APP: {
            app * a = to_app(n);
            (*this)(a, result);

            unsigned n_args = a->get_num_args();
            m_temp_exprs.reset();
            for (unsigned i = 0; i < n_args; i++) {
                expr * arg = a->get_arg(i);
                const mpz & v = m_tracker.get_value(arg);
                m_temp_exprs.push_back(m_tracker.mpz2value(m_manager.get_sort(arg), v));
            }
            expr_ref q(m_manager), temp(m_manager);
            q = m_manager.mk_app(a->get_decl(), m_temp_exprs.size(), m_temp_exprs.c_ptr());                                
            model dummy_model(m_manager);
            model_evaluator evaluator(dummy_model);
            evaluator(q, temp);
            mpz check_res;
            m_tracker.value2mpz(temp, check_res);
            CTRACE("sls", !m_mpz_manager.eq(check_res, result), 
                            tout << "EVAL BUG: IS " << m_mpz_manager.to_string(result) << 
                            " SHOULD BE " << m_mpz_manager.to_string(check_res) << std::endl; );
            SASSERT(m_mpz_manager.eq(check_res, result));
            m_mpz_manager.del(check_res);
                    
            break;
        }
        default: 
            NOT_IMPLEMENTED_YET();
        }    
    }

    void run_serious_update(unsigned cur_depth) {
        // precondition: m_traversal_stack contains the entry point(s)
        expr_fast_mark1 visited;
        mpz new_value;

        double new_score;

        SASSERT(cur_depth < m_traversal_stack.size());
        while (cur_depth != static_cast<unsigned>(-1)) {
            ptr_vector<expr> & cur_depth_exprs = m_traversal_stack[cur_depth];

            for (unsigned i = 0; i < cur_depth_exprs.size(); i++) {
                expr * cur = cur_depth_exprs[i];

                (*this)(to_app(cur), new_value);
                m_tracker.set_value(cur, new_value);

                new_score = m_tracker.score(cur);
                if (m_tracker.is_top_expr(cur))
                {
                    m_tracker.adapt_top_sum(cur, new_score, m_tracker.get_score(cur));
                    if (m_mpz_manager.eq(new_value,m_one))
                        m_tracker.make_assertion(cur);
                    else
                        m_tracker.break_assertion(cur);
                }

                m_tracker.set_score(cur, new_score);
                m_tracker.set_score_prune(cur, new_score);

                if (m_tracker.has_uplinks(cur)) {
                    ptr_vector<expr> & ups = m_tracker.get_uplinks(cur);
                    for (unsigned j = 0; j < ups.size(); j++) {
                        expr * next = ups[j];
                        unsigned next_d = m_tracker.get_distance(next);
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

    void run_update(unsigned cur_depth) {
        // precondition: m_traversal_stack contains the entry point(s)
        expr_fast_mark1 visited;
        mpz new_value;

        double new_score;

        SASSERT(cur_depth < m_traversal_stack.size());
        while (cur_depth != static_cast<unsigned>(-1)) {
            ptr_vector<expr> & cur_depth_exprs = m_traversal_stack[cur_depth];

            for (unsigned i = 0; i < cur_depth_exprs.size(); i++) {
                expr * cur = cur_depth_exprs[i];

                (*this)(to_app(cur), new_value);
                m_tracker.set_value(cur, new_value);
                new_score = m_tracker.score(cur);
                if (m_tracker.is_top_expr(cur))
                    m_tracker.adapt_top_sum(cur, new_score, m_tracker.get_score(cur));
                m_tracker.set_score(cur, new_score);
                if (m_tracker.has_uplinks(cur)) {
                    ptr_vector<expr> & ups = m_tracker.get_uplinks(cur);
                    for (unsigned j = 0; j < ups.size(); j++) {
                        expr * next = ups[j];
                        unsigned next_d = m_tracker.get_distance(next);
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

        sls_tracker::entry_point_type::iterator start = m_tracker.get_entry_points().begin();
        sls_tracker::entry_point_type::iterator end = m_tracker.get_entry_points().end();
        for (sls_tracker::entry_point_type::iterator it = start; it != end; it++) {
            expr * ep = m_tracker.get_entry_point(it->m_key);
            unsigned cur_depth = m_tracker.get_distance(ep);
            if (m_traversal_stack.size() <= cur_depth) 
                m_traversal_stack.resize(cur_depth+1);
            m_traversal_stack[cur_depth].push_back(ep);
            if (cur_depth > max_depth) max_depth = cur_depth;
        }
        run_serious_update(max_depth);
    }

    void update(func_decl * fd, const mpz & new_value) {
        m_tracker.set_value(fd, new_value);
        expr * ep = m_tracker.get_entry_point(fd);
        unsigned cur_depth = m_tracker.get_distance(ep);
        if (m_traversal_stack.size() <= cur_depth) 
            m_traversal_stack.resize(cur_depth+1);
        m_traversal_stack[cur_depth].push_back(ep);

        run_update(cur_depth);
    }

    void serious_update(func_decl * fd, const mpz & new_value) {
        m_tracker.set_value(fd, new_value);
        expr * ep = m_tracker.get_entry_point(fd);
        unsigned cur_depth = m_tracker.get_distance(ep);
        if (m_traversal_stack.size() <= cur_depth) 
            m_traversal_stack.resize(cur_depth+1);
        m_traversal_stack[cur_depth].push_back(ep);

        run_serious_update(cur_depth);
    }

    unsigned run_update_bool_prune(unsigned cur_depth) {
        expr_fast_mark1 visited;

        double prune_score, new_score;
        unsigned pot_benefits = 0;
        SASSERT(cur_depth < m_traversal_stack_bool.size());
 
        ptr_vector<expr> & cur_depth_exprs = m_traversal_stack_bool[cur_depth];

        for (unsigned i = 0; i < cur_depth_exprs.size(); i++) {
            expr * cur = cur_depth_exprs[i];

            new_score = m_tracker.score(cur); 
            if (m_tracker.is_top_expr(cur))
                m_tracker.adapt_top_sum(cur, new_score, m_tracker.get_score(cur));

            prune_score = m_tracker.get_score_prune(cur);
            m_tracker.set_score(cur, new_score);

            if ((new_score > prune_score) && (m_tracker.has_pos_occ(cur)))
                pot_benefits = 1;
            if ((new_score <= prune_score) && (m_tracker.has_neg_occ(cur)))
                pot_benefits = 1;

            if (m_tracker.has_uplinks(cur)) {
                ptr_vector<expr> & ups = m_tracker.get_uplinks(cur);
                for (unsigned j = 0; j < ups.size(); j++) {
                    expr * next = ups[j];
                    unsigned next_d = m_tracker.get_distance(next);
                    SASSERT(next_d < cur_depth);
                    if (!visited.is_marked(next)) {
                        m_traversal_stack_bool[next_d].push_back(next);
                        visited.mark(next);
                    }
                }
            }
        }

        cur_depth_exprs.reset();
        cur_depth--;
 
        while (cur_depth != static_cast<unsigned>(-1)) {
            ptr_vector<expr> & cur_depth_exprs = m_traversal_stack_bool[cur_depth];
            if (pot_benefits)
            {
                unsigned cur_size = cur_depth_exprs.size();
                for (unsigned i = 0; i < cur_size; i++) {
                    expr * cur = cur_depth_exprs[i];

                    new_score = m_tracker.score(cur); 
                    if (m_tracker.is_top_expr(cur))
                        m_tracker.adapt_top_sum(cur, new_score, m_tracker.get_score(cur));
                    m_tracker.set_score(cur, new_score);

                    if (m_tracker.has_uplinks(cur)) {
                        ptr_vector<expr> & ups = m_tracker.get_uplinks(cur);
                        for (unsigned j = 0; j < ups.size(); j++) {
                            expr * next = ups[j];
                            unsigned next_d = m_tracker.get_distance(next);
                            SASSERT(next_d < cur_depth);
                            if (!visited.is_marked(next)) {
                                m_traversal_stack_bool[next_d].push_back(next);
                                visited.mark(next);
                            }
                        }
                    }
                }
            }
            cur_depth_exprs.reset();
            cur_depth--;
        }

        return pot_benefits;
    }

    void run_update_prune(unsigned max_depth) {
        // precondition: m_traversal_stack contains the entry point(s)
        expr_fast_mark1 visited;
        mpz new_value;

        unsigned cur_depth = max_depth;
        SASSERT(cur_depth < m_traversal_stack.size());
        while (cur_depth != static_cast<unsigned>(-1)) {
            ptr_vector<expr> & cur_depth_exprs = m_traversal_stack[cur_depth];

            for (unsigned i = 0; i < cur_depth_exprs.size(); i++) {
                expr * cur = cur_depth_exprs[i];

                (*this)(to_app(cur), new_value);
                m_tracker.set_value(cur, new_value);
                // Andreas: Should actually always have uplinks ...
                if (m_tracker.has_uplinks(cur)) {
                    ptr_vector<expr> & ups = m_tracker.get_uplinks(cur);
                    for (unsigned j = 0; j < ups.size(); j++) {
                        expr * next = ups[j];
                        unsigned next_d = m_tracker.get_distance(next);
                        SASSERT(next_d < cur_depth);
                        if (!visited.is_marked(next)) {
                            if (m_manager.is_bool(next))
                                m_traversal_stack_bool[max_depth].push_back(next);
                            else
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

    unsigned update_prune(func_decl * fd, const mpz & new_value) {
        m_tracker.set_value(fd, new_value);
        expr * ep = m_tracker.get_entry_point(fd);
        unsigned cur_depth = m_tracker.get_distance(ep);

        if (m_traversal_stack_bool.size() <= cur_depth)
            m_traversal_stack_bool.resize(cur_depth+1);
        if (m_traversal_stack.size() <= cur_depth) 
                m_traversal_stack.resize(cur_depth+1);

        if (m_manager.is_bool(ep))
            m_traversal_stack_bool[cur_depth].push_back(ep);
        else
        {
            m_traversal_stack[cur_depth].push_back(ep);
            run_update_prune(cur_depth);
        }
        return run_update_bool_prune(cur_depth);
    }

    void randomize_local(ptr_vector<func_decl> & unsat_constants) {
        // Randomize _one_ candidate:
        unsigned r = m_tracker.get_random_uint(16) % unsat_constants.size();
        func_decl * fd = unsat_constants[r];
        mpz temp = m_tracker.get_random(fd->get_range());

        serious_update(fd, temp);

        m_mpz_manager.del(temp);

        TRACE("sls",    tout << "Randomization candidate: " << unsat_constants[r]->get_name() << std::endl;
                        tout << "Locally randomized model: " << std::endl; 
                        m_tracker.show_model(tout); );

    }

    void randomize_local(expr * e) {
        randomize_local(m_tracker.get_constants(e));
    } 

    void randomize_local(ptr_vector<expr> const & as) {
        randomize_local(m_tracker.get_unsat_constants(as));
    } 
};

#endif
