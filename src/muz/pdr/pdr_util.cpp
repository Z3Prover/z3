/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.cpp

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:


Notes: 
    

--*/

#include <sstream>
#include "arith_simplifier_plugin.h"
#include "array_decl_plugin.h"
#include "ast_pp.h"
#include "basic_simplifier_plugin.h"
#include "bv_simplifier_plugin.h"
#include "bool_rewriter.h"
#include "dl_util.h"
#include "for_each_expr.h"
#include "smt_params.h"
#include "model.h"
#include "ref_vector.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "util.h"
#include "pdr_manager.h"
#include "pdr_util.h"
#include "arith_decl_plugin.h"
#include "expr_replacer.h"
#include "model_smt2_pp.h"
#include "poly_rewriter.h"
#include "poly_rewriter_def.h"
#include "arith_rewriter.h"
#include "scoped_proof.h"



namespace pdr {

    unsigned ceil_log2(unsigned u) {
        if (u == 0) { return 0; }
        unsigned pow2 = next_power_of_two(u);
        return get_num_1bits(pow2-1);
    }

    std::string pp_cube(const ptr_vector<expr>& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const expr_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(const app_ref_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }
    
    std::string pp_cube(const app_vector& model, ast_manager& m) {
        return pp_cube(model.size(), model.c_ptr(), m);
    }

    std::string pp_cube(unsigned sz, app * const * lits, ast_manager& m) {
        return pp_cube(sz, reinterpret_cast<expr * const *>(lits), m);
    }

    std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& m) {
        std::stringstream res;
        res << "(";
        expr * const * end = lits+sz;
        for (expr * const * it = lits; it!=end; it++) {
            res << mk_pp(*it, m);
            if (it+1!=end) {
                res << ", ";
            }
        }
        res << ")";
        return res.str();
    }



    /////////////////////////
    // model_evaluator
    //
    

    void model_evaluator::assign_value(expr* e, expr* val) {
        rational r;
        if (m.is_true(val)) {
            set_true(e);
        }
        else if (m.is_false(val)) {
            set_false(e);
        }
        else if (m_arith.is_numeral(val, r)) {
            set_number(e, r);
        }
        else if (m.is_value(val)) {
            set_value(e, val);
        }
        else {
            IF_VERBOSE(3, verbose_stream() << "Not evaluated " << mk_pp(e, m) << " := " << mk_pp(val, m) << "\n";);
            TRACE("pdr", tout << "Variable is not tracked: " << mk_pp(e, m) << " := " << mk_pp(val, m) << "\n";);
            set_x(e);
        }
    }

    void model_evaluator::setup_model(model_ref& model) {
        m_numbers.reset();
        m_values.reset();
        m_model = model;
        rational r;
        unsigned sz = model->get_num_constants();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * d = model->get_constant(i); 
            expr* val = model->get_const_interp(d);
            expr* e = m.mk_const(d);
            m_refs.push_back(e);
            assign_value(e, val);
        }
    }
    
    void model_evaluator::reset() {
        m1.reset();
        m2.reset();
        m_values.reset();
        m_visited.reset();
        m_numbers.reset();
        m_refs.reset();
        m_model = 0;
    }
    
    expr_ref_vector model_evaluator::minimize_model(ptr_vector<expr> const & formulas, model_ref& mdl) {
        setup_model(mdl);
        
        TRACE("pdr_verbose", 
              tout << "formulas:\n";
              for (unsigned i = 0; i < formulas.size(); ++i) tout << mk_pp(formulas[i], m) << "\n"; 
              );
        
        expr_ref_vector model = prune_by_cone_of_influence(formulas);
        TRACE("pdr_verbose",
              tout << "pruned model:\n";
              for (unsigned i = 0; i < model.size(); ++i) tout << mk_pp(model[i].get(), m) << "\n";);
        
        reset();
        
        DEBUG_CODE(
            setup_model(mdl);
            VERIFY(check_model(formulas));
            reset(););
        
        return model;
    }
    
    expr_ref_vector model_evaluator::minimize_literals(ptr_vector<expr> const& formulas, model_ref& mdl) {
        
        TRACE("pdr", 
              tout << "formulas:\n";
              for (unsigned i = 0; i < formulas.size(); ++i) tout << mk_pp(formulas[i], m) << "\n"; 
              );
        
        expr_ref_vector result(m);
        expr_ref tmp(m);
        ptr_vector<expr> tocollect;
        
        setup_model(mdl);
        collect(formulas, tocollect);
        for (unsigned i = 0; i < tocollect.size(); ++i) {
            expr* e = tocollect[i];
            expr* e1, *e2;
            SASSERT(m.is_bool(e));
            SASSERT(is_true(e) || is_false(e));
            if (is_true(e)) {
                result.push_back(e);
            }
            // hack to break disequalities for arithmetic variables.
            else if (m.is_eq(e, e1, e2) && m_arith.is_int_real(e1)) {
                if (get_number(e1) < get_number(e2)) {
                    result.push_back(m_arith.mk_lt(e1,e2));
                }
                else {
                    result.push_back(m_arith.mk_lt(e2,e1));
                }
            }
            else {
                result.push_back(m.mk_not(e));
            }
        }
        reset();
        TRACE("pdr", 
              tout << "minimized model:\n";
              for (unsigned i = 0; i < result.size(); ++i) tout << mk_pp(result[i].get(), m) << "\n"; 
              );
        
        return result;
    }
    
    void model_evaluator::process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect) {
        SASSERT(m.is_bool(e));
        SASSERT(is_true(e) || is_false(e));
        unsigned v = is_true(e);
        unsigned sz = e->get_num_args();
        expr* const* args = e->get_args();
        if (e->get_family_id() == m.get_basic_family_id()) {
            switch(e->get_decl_kind()) {
            case OP_TRUE:
                break;
            case OP_FALSE:
                break;
            case OP_EQ:
            case OP_IFF:
                if (args[0] == args[1]) {
                    SASSERT(v);
                    // no-op                    
                }
                else if (m.is_bool(args[0])) {
                    todo.append(sz, args);
                }
                else {
                    tocollect.push_back(e);
                }
                break;                              
            case OP_DISTINCT:
                tocollect.push_back(e);
                break;
            case OP_ITE:
                if (args[1] == args[2]) {
                    tocollect.push_back(args[1]);
                }
                else if (is_true(args[1]) && is_true(args[2])) {
                    todo.append(2, args+1);
                }
                else if (is_false(args[1]) && is_false(args[2])) {
                    todo.append(2, args+1);
                }
                else if (is_true(args[0])) {
                    todo.append(2, args);
                }
                else {
                    SASSERT(is_false(args[0]));
                    todo.push_back(args[0]);
                    todo.push_back(args[2]);
                }
                break;
            case OP_AND:
                if (v) {
                    todo.append(sz, args);
                }
                else {
                    unsigned i = 0;
                    for (; !is_false(args[i]) && i < sz; ++i);     
                    if (i == sz) {
                        fatal_error(1);
                    }
                    VERIFY(i < sz);
                    todo.push_back(args[i]);
                }
                break;
            case OP_OR:
                if (v) {
                    unsigned i = 0;
                    for (; !is_true(args[i]) && i < sz; ++i);
                    if (i == sz) {
                        fatal_error(1);
                    }
                    VERIFY(i < sz);
                    todo.push_back(args[i]);
                }
                else {
                    todo.append(sz, args);
                }
                break;
            case OP_XOR: 
            case OP_NOT:
                todo.append(sz, args);
                break;
            case OP_IMPLIES:
                if (v) {
                    if (is_true(args[1])) {
                        todo.push_back(args[1]);
                    }
                    else if (is_false(args[0])) {
                        todo.push_back(args[0]);
                    }
                    else {
                        IF_VERBOSE(0, verbose_stream() << "Term not handled " << mk_pp(e, m) << "\n";);
                        UNREACHABLE();
                    }
                }
                else {
                    todo.append(sz, args);
                }
                break;
            default:
                IF_VERBOSE(0, verbose_stream() << "Term not handled " << mk_pp(e, m) << "\n";);
                UNREACHABLE();
            }
        }
        else {
            tocollect.push_back(e);
        }
    }
    
    void model_evaluator::collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect) {
        ptr_vector<expr> todo;
        todo.append(formulas);
        m_visited.reset();
        
        VERIFY(check_model(formulas));
        
        while (!todo.empty()) {
            app*  e = to_app(todo.back());
            todo.pop_back();
            if (!m_visited.is_marked(e)) {
                process_formula(e, todo, tocollect);
                m_visited.mark(e, true);
            }
        }
        m_visited.reset();
    }
    
    expr_ref_vector model_evaluator::prune_by_cone_of_influence(ptr_vector<expr> const & formulas) {
        ptr_vector<expr> tocollect;
        collect(formulas, tocollect);
        m1.reset();
        m2.reset();
        for (unsigned i = 0; i < tocollect.size(); ++i) {     
            TRACE("pdr_verbose", tout << "collect: " << mk_pp(tocollect[i], m) << "\n";);
            for_each_expr(*this, m_visited, tocollect[i]);
        }
        unsigned sz = m_model->get_num_constants();
        expr_ref e(m), eq(m), val(m);
        expr_ref_vector model(m);
        for (unsigned i = 0; i < sz; i++) {
            e = m.mk_const(m_model->get_constant(i));
            if (m_visited.is_marked(e)) {
                val = eval(m_model, e);
                eq = m.mk_eq(e, val);
                model.push_back(eq);
            }
        }
        m_visited.reset();
        TRACE("pdr", tout << sz << " ==> " << model.size() << "\n";);
        return model;
        
    }
    
    void model_evaluator::eval_arith(app* e) {
        rational r, r2;
        
#define ARG1 e->get_arg(0)
#define ARG2 e->get_arg(1)     
        
        unsigned arity = e->get_num_args();
        for (unsigned i = 0; i < arity; ++i) {
            expr* arg = e->get_arg(i);
            if (is_x(arg)) {
                set_x(e);
                return;
            }
            SASSERT(!is_unknown(arg));
        }
        switch(e->get_decl_kind()) {
        case OP_NUM: 
            VERIFY(m_arith.is_numeral(e, r));
            set_number(e, r);
            break;                
        case OP_IRRATIONAL_ALGEBRAIC_NUM:  
            set_x(e);
            break;
        case OP_LE:
            set_bool(e, get_number(ARG1) <= get_number(ARG2));
            break;
        case OP_GE:
            set_bool(e, get_number(ARG1) >= get_number(ARG2));
            break;
        case OP_LT:
            set_bool(e, get_number(ARG1) < get_number(ARG2));
            break;
        case OP_GT:
            set_bool(e, get_number(ARG1) > get_number(ARG2));
            break;
        case OP_ADD: 
            r = rational::zero();
            for (unsigned i = 0; i < arity; ++i) {
                r += get_number(e->get_arg(i));
            }
            set_number(e, r);
            break;                                    
        case OP_SUB: 
            r = get_number(e->get_arg(0));
            for (unsigned i = 1; i < arity; ++i) {
                r -= get_number(e->get_arg(i));
            }
            set_number(e, r);
            break;                            
        case OP_UMINUS: 
            SASSERT(arity == 1);
            set_number(e, get_number(e->get_arg(0)));
            break;                
        case OP_MUL: 
            r = rational::one();
            for (unsigned i = 0; i < arity; ++i) {
                r *= get_number(e->get_arg(i));
            }
            set_number(e, r);
            break;                
        case OP_DIV: 
            SASSERT(arity == 2);
            r = get_number(ARG2);
            if (r.is_zero()) {
                set_x(e);
            }
            else {
                set_number(e, get_number(ARG1) / r);
            }
            break;                
        case OP_IDIV: 
            SASSERT(arity == 2);
            r = get_number(ARG2);
            if (r.is_zero()) {
                set_x(e);
            }
            else {
                set_number(e, div(get_number(ARG1), r));
            }
            break;                
        case OP_REM: 
            // rem(v1,v2) = if v2 >= 0 then mod(v1,v2) else -mod(v1,v2)
            SASSERT(arity == 2);
            r = get_number(ARG2);
            if (r.is_zero()) {
                set_x(e);
            }
            else {
                r2 = mod(get_number(ARG1), r);
                if (r.is_neg()) r2.neg();
                set_number(e, r2);
            }
            break;
        case OP_MOD: 
            SASSERT(arity == 2);
            r = get_number(ARG2);
            if (r.is_zero()) {
                set_x(e);
            }
            else {
                set_number(e, mod(get_number(ARG1), r));
            }
            break;                   
        case OP_TO_REAL: 
            SASSERT(arity == 1);
            set_number(e, get_number(ARG1));
            break;                
        case OP_TO_INT: 
            SASSERT(arity == 1);
            set_number(e, floor(get_number(ARG1)));
            break;                
        case OP_IS_INT: 
            SASSERT(arity == 1);
            set_bool(e, get_number(ARG1).is_int());
            break;
        case OP_POWER:
            set_x(e);
            break;
        default:
            IF_VERBOSE(0, verbose_stream() << "Term not handled " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
            break;
        }
    }
    
    void model_evaluator::inherit_value(expr* e, expr* v) {
        expr* w;
        SASSERT(!is_unknown(v));
        SASSERT(m.get_sort(e) == m.get_sort(v));
        if (is_x(v)) {
            set_x(e);
        }
        else if (m.is_bool(e)) {
            SASSERT(m.is_bool(v));
            if (is_true(v)) set_true(e);
            else if (is_false(v)) set_false(e);
            else {
                TRACE("pdr", tout << "not inherited:\n" << mk_pp(e, m) << "\n" << mk_pp(v, m) << "\n";);
                set_x(e);
            }
        }
        else if (m_arith.is_int_real(e)) {
            set_number(e, get_number(v));
        }
        else if (m.is_value(v)) {
            set_value(e, v);
        }
        else if (m_values.find(v, w)) {
            set_value(e, w);
        }
        else {
            TRACE("pdr", tout << "not inherited:\n" << mk_pp(e, m) << "\n" << mk_pp(v, m) << "\n";);
            set_x(e);
        }
    }

    void model_evaluator::eval_exprs(expr_ref_vector& es) {
        model_ref mr(m_model);
        for (unsigned j = 0; j < es.size(); ++j) {
            if (m_array.is_as_array(es[j].get())) {
                es[j] = eval(mr, es[j].get());
            }
        }
    }
    
    bool model_evaluator::extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case) {
        SASSERT(m_array.is_array(a));
        
        TRACE("pdr", tout << mk_pp(a, m) << "\n";);
        while (m_array.is_store(a)) {
            expr_ref_vector store(m);
            store.append(to_app(a)->get_num_args()-1, to_app(a)->get_args()+1);
            eval_exprs(store);
            stores.push_back(store);
            a = to_app(a)->get_arg(0);
        }
        
        if (m_array.is_const(a)) {
            else_case = to_app(a)->get_arg(0);
            return true;
        }
        
        while (m_array.is_as_array(a)) {
            func_decl* f = m_array.get_as_array_func_decl(to_app(a));
            func_interp* g = m_model->get_func_interp(f);
            unsigned sz = g->num_entries();
            unsigned arity = f->get_arity();
            for (unsigned i = 0; i < sz; ++i) {
                expr_ref_vector store(m);
                func_entry const* fe = g->get_entry(i);
                store.append(arity, fe->get_args());
                store.push_back(fe->get_result());
                for (unsigned j = 0; j < store.size(); ++j) {
                    if (!is_ground(store[j].get())) {
                        TRACE("pdr", tout << "could not extract array interpretation: " << mk_pp(a, m) << "\n" << mk_pp(store[j].get(), m) << "\n";);
                        return false;
                    }
                }
                eval_exprs(store);
                stores.push_back(store);
            }        
            else_case = g->get_else();
            if (!else_case) {
                TRACE("pdr", tout << "no else case " << mk_pp(a, m) << "\n";);
                return false;
            }
            if (!is_ground(else_case)) {
                TRACE("pdr", tout << "non-ground else case " << mk_pp(a, m) << "\n" << mk_pp(else_case, m) << "\n";);
                return false;
            }
            if (m_array.is_as_array(else_case)) {
                model_ref mr(m_model);
                else_case = eval(mr, else_case);
            }
            TRACE("pdr", tout << "else case: " << mk_pp(else_case, m) << "\n";);
            return true;
        }
        TRACE("pdr", tout << "no translation: " << mk_pp(a, m) << "\n";);
        
        return false;
    }
    
    /**
       best effort evaluator of extensional array equality.
     */
    void model_evaluator::eval_array_eq(app* e, expr* arg1, expr* arg2) {
        TRACE("pdr", tout << "array equality: " << mk_pp(e, m) << "\n";);
        expr_ref v1(m), v2(m);
        m_model->eval(arg1, v1);
        m_model->eval(arg2, v2);
        if (v1 == v2) {
            set_true(e);
            return;
        }
        sort* s = m.get_sort(arg1);
        sort* r = get_array_range(s);
        // give up evaluating finite domain/range arrays
        if (!r->is_infinite() && !r->is_very_big() && !s->is_infinite() && !s->is_very_big()) {
            TRACE("pdr", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            set_x(e);
            return;
        }
        vector<expr_ref_vector> store;
        expr_ref else1(m), else2(m);
        if (!extract_array_func_interp(v1, store, else1) ||
            !extract_array_func_interp(v2, store, else2)) {
            TRACE("pdr", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            set_x(e);
            return;
        }

        if (else1 != else2) {
            if (m.is_value(else1) && m.is_value(else2)) {
                TRACE("pdr", tout 
                      << "defaults are different: " << mk_pp(e, m) << " " 
                      << mk_pp(else1, m) << " " << mk_pp(else2, m) << "\n";);
                set_false(e);
            }
            else if (m_array.is_array(else1)) {
                eval_array_eq(e, else1, else2);
            }
            else {
                TRACE("pdr", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
                set_x(e);
            }
            return;
        }

        expr_ref s1(m), s2(m), w1(m), w2(m);        
        expr_ref_vector args1(m), args2(m);
        args1.push_back(v1);
        args2.push_back(v2);        
        for (unsigned i = 0; i < store.size(); ++i) {
            args1.resize(1);
            args2.resize(1);
            args1.append(store[i].size()-1, store[i].c_ptr());
            args2.append(store[i].size()-1, store[i].c_ptr());
            s1 = m_array.mk_select(args1.size(), args1.c_ptr());
            s2 = m_array.mk_select(args2.size(), args2.c_ptr());
            m_model->eval(s1, w1);
            m_model->eval(s2, w2);
            if (w1 == w2) {
                continue;
            }
            if (m.is_value(w1) && m.is_value(w2)) {
                TRACE("pdr", tout << "Equality evaluation: " << mk_pp(e, m) << "\n"; 
                      tout << mk_pp(s1, m) << " |-> " << mk_pp(w1, m) << "\n";
                      tout << mk_pp(s2, m) << " |-> " << mk_pp(w2, m) << "\n";);
                set_false(e);
            }
            else if (m_array.is_array(w1)) {
                eval_array_eq(e, w1, w2);
                if (is_true(e)) {
                    continue;
                }
            }
            else {
                TRACE("pdr", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
                set_x(e);
            }
            return;
        }
        set_true(e);
    }

    void model_evaluator::eval_eq(app* e, expr* arg1, expr* arg2) {
        if (arg1 == arg2) {
            set_true(e);
        }
        else if (m_array.is_array(arg1)) {
            eval_array_eq(e, arg1, arg2);
        }
        else if (is_x(arg1) || is_x(arg2)) {
            expr_ref eq(m), vl(m);
            eq = m.mk_eq(arg1, arg2);
            m_model->eval(eq, vl);
            if (m.is_true(vl)) {
                set_bool(e, true);                
            }
            else if (m.is_false(vl)) {
                set_bool(e, false);
            }
            else {
                TRACE("pdr", tout << "cannot evaluate: " << mk_pp(vl, m) <<  "\n";);
                set_x(e);
            }
        }
        else if (m.is_bool(arg1)) {
            bool val = is_true(arg1) == is_true(arg2);
            SASSERT(val == (is_false(arg1) == is_false(arg2)));
            if (val) {
                set_true(e);
            }
            else {
                set_false(e);
            }            
        }
        else if (m_arith.is_int_real(arg1)) {
            set_bool(e, get_number(arg1) == get_number(arg2));
        }
        else {
            expr* e1 = get_value(arg1);
            expr* e2 = get_value(arg2);
            if (m.is_value(e1) && m.is_value(e2)) {
                set_bool(e, e1 == e2);
            }
            else if (e1 == e2) {
                set_bool(e, true);
            }
            else {
                TRACE("pdr", tout << "not value equal:\n" << mk_pp(e1, m) << "\n" << mk_pp(e2, m) << "\n";);
                set_x(e);
            }
        }
    }

    void model_evaluator::eval_basic(app* e) {
        expr* arg1, *arg2;
        expr *argCond, *argThen, *argElse, *arg;
        bool has_x = false;
        unsigned arity = e->get_num_args();
        switch(e->get_decl_kind()) {
        case OP_AND: 
            for (unsigned j = 0; j < arity; ++j) {
                expr * arg = e->get_arg(j);
                if (is_false(arg)) {
                    set_false(e);
                    return;
                }
                else if (is_x(arg)) {
                    has_x = true;
                }
                else {
                    SASSERT(is_true(arg));
                }
            }
            if (has_x) {
                set_x(e);
            }
            else {
                set_true(e);
            }
            break;
        case OP_OR: 
            for (unsigned j = 0; j < arity; ++j) {
                expr * arg = e->get_arg(j);
                if (is_true(arg)) {
                    set_true(e);
                    return;
                }
                else if (is_x(arg)) {
                    has_x = true;
                }
                else {
                    SASSERT(is_false(arg));
                }
            }
            if (has_x) {
                set_x(e);
            }
            else {
                set_false(e);
            }
            break;
        case OP_NOT: 
            VERIFY(m.is_not(e, arg));
            if (is_true(arg)) {
                set_false(e);
            }
            else if (is_false(arg)) {
                set_true(e);
            }
            else {
                SASSERT(is_x(arg));
                set_x(e);
            }
            break;
        case OP_IMPLIES: 
            VERIFY(m.is_implies(e, arg1, arg2));
            if (is_false(arg1) || is_true(arg2)) {
                set_true(e);
            }
            else if (arg1 == arg2) {
                set_true(e);
            }
            else if (is_true(arg1) && is_false(arg2)) {
                set_false(e);
            }
            else {
                SASSERT(is_x(arg1) || is_x(arg2));
                set_x(e);
            }
            break;
        case OP_IFF: 
            VERIFY(m.is_iff(e, arg1, arg2));
            eval_eq(e, arg1, arg2);
            break;
        case OP_ITE: 
            VERIFY(m.is_ite(e, argCond, argThen, argElse));
            if (is_true(argCond)) { 
                inherit_value(e, argThen);
            }
            else if (is_false(argCond)) {
                inherit_value(e, argElse);
            }
            else if (argThen == argElse) {
                inherit_value(e, argThen);
            }
            else if (m.is_bool(e)) {
                SASSERT(is_x(argCond));
                if (is_x(argThen) || is_x(argElse)) {
                    set_x(e);
                }
                else if (is_true(argThen) == is_true(argElse)) {
                    inherit_value(e, argThen);
                }
                else {
                    set_x(e);
                }
            }
            else {
                set_x(e);
            }
            break;
        case OP_TRUE:
            set_true(e);
            break;
        case OP_FALSE:
            set_false(e);
            break;
        case OP_EQ:
            VERIFY(m.is_eq(e, arg1, arg2));
            eval_eq(e, arg1, arg2);
            break;
        case OP_DISTINCT: {
            vector<rational> values;
            for (unsigned i = 0; i < arity; ++i) {
                expr* arg = e->get_arg(i);
                if (is_x(arg)) {
                    set_x(e);
                    return;
                }
                values.push_back(get_number(arg));
            }
            std::sort(values.begin(), values.end());
            for (unsigned i = 0; i + 1 < values.size(); ++i) {
                if (values[i] == values[i+1]) {
                    set_false(e);
                    return;
                }
            }
            set_true(e);
            break;
        }
        default:
            IF_VERBOSE(0, verbose_stream() << "Term not handled " << mk_pp(e, m) << "\n";);
            UNREACHABLE();        
        }
    }
    
    bool model_evaluator::check_model(ptr_vector<expr> const& formulas) {
        ptr_vector<expr> todo(formulas);
        
        while (!todo.empty()) {
            expr * curr_e = todo.back();
            
            if (!is_app(curr_e)) { 
                todo.pop_back();
                continue;
            }
            app * curr = to_app(curr_e);
            
            if (!is_unknown(curr)) { 
                todo.pop_back();
                continue;
            }
            unsigned arity = curr->get_num_args();
            for (unsigned i = 0; i < arity; ++i) {
                if (is_unknown(curr->get_arg(i))) {
                    todo.push_back(curr->get_arg(i));
                }
            }
            if (todo.back() != curr) {
                continue;
            }
            todo.pop_back();
            if (curr->get_family_id() == m_arith.get_family_id()) {
                eval_arith(curr);
            }
            else if (curr->get_family_id() == m.get_basic_family_id()) {
                eval_basic(curr);
            }
            else {
                expr_ref vl(m);
                m_model->eval(curr, vl);
                assign_value(curr, vl);
            }
            
            IF_VERBOSE(35,verbose_stream() << "assigned "<<mk_pp(curr_e,m) 
                       <<(is_true(curr_e) ? "true" : is_false(curr_e) ? "false" : "unknown") << "\n";);
            SASSERT(!is_unknown(curr));
        }
        
        bool has_x = false;
        for (unsigned i = 0; i < formulas.size(); ++i) {
            expr * form = formulas[i];
            SASSERT(!is_unknown(form));
            TRACE("pdr_verbose", 
                  tout << "formula is " << (is_true(form) ? "true" : is_false(form) ? "false" : "unknown") << "\n" <<mk_pp(form, m)<< "\n";);
            
            if (is_false(form)) {
                IF_VERBOSE(0, verbose_stream() << "formula false in model: " << mk_pp(form, m) << "\n";);
                UNREACHABLE();
            }
            if (is_x(form)) {
                IF_VERBOSE(0, verbose_stream() << "formula undetermined in model: " << mk_pp(form, m) << "\n";);
                TRACE("pdr", model_smt2_pp(tout, m, *m_model, 0);); 
                has_x = true;
            }
        }
        return !has_x;
    }

    expr_ref model_evaluator::eval(model_ref& model, func_decl* d) {
        SASSERT(d->get_arity() == 0);
        expr_ref result(m);
        if (m_array.is_array(d->get_range())) {
            expr_ref e(m);
            e = m.mk_const(d);
            result = eval(model, e);
        }
        else {
            result = model->get_const_interp(d);
        }
        return result;
    }

    expr_ref model_evaluator::eval(model_ref& model, expr* e) {
        expr_ref result(m);
        m_model = model;
        VERIFY(m_model->eval(e, result, true));
        if (m_array.is_array(e)) {
            vector<expr_ref_vector> stores;
            expr_ref_vector args(m);
            expr_ref else_case(m);
            if (extract_array_func_interp(result, stores, else_case)) {
                result = m_array.mk_const_array(m.get_sort(e), else_case);
                while (!stores.empty() && stores.back().back() == else_case) {
                    stores.pop_back();
                }
                for (unsigned i = stores.size(); i > 0; ) {
                    --i;
                    args.resize(1);
                    args[0] = result;
                    args.append(stores[i]);
                    result = m_array.mk_store(args.size(), args.c_ptr());
                }
                return result;
            }
        }
        return result;
    }


    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        expr_ref_vector conjs(m);
        qe::flatten_and(fml, conjs);
        obj_map<expr, unsigned> diseqs;
        expr* n, *lhs, *rhs;
        for (unsigned i = 0; i < conjs.size(); ++i) {
            if (m.is_not(conjs[i].get(), n) &&
                m.is_eq(n, lhs, rhs)) {
                if (!m.is_value(rhs)) {
                    std::swap(lhs, rhs);
                }
                if (!m.is_value(rhs)) {
                    continue;
                }
                diseqs.insert_if_not_there2(lhs, 0)->get_data().m_value++;
            }
        }
        expr_substitution sub(m);

        unsigned orig_size = conjs.size();
        unsigned num_deleted = 0;
        expr_ref val(m), tmp(m);
        proof_ref pr(m);
        pr = m.mk_asserted(m.mk_true());
        obj_map<expr, unsigned>::iterator it  = diseqs.begin();
        obj_map<expr, unsigned>::iterator end = diseqs.end();
        for (; it != end; ++it) {
            if (it->m_value >= threshold) {
                model.eval(it->m_key, val);
                sub.insert(it->m_key, val, pr);
                conjs.push_back(m.mk_eq(it->m_key, val));
                num_deleted += it->m_value;
            }
        }
        if (orig_size < conjs.size()) {
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
            rep->set_substitution(&sub);
            for (unsigned i = 0; i < orig_size; ++i) {
                tmp = conjs[i].get();
                (*rep)(tmp);
                if (m.is_true(tmp)) {
                    conjs[i] = conjs.back();
                    SASSERT(orig_size <= conjs.size());
                    conjs.pop_back();
                    SASSERT(orig_size <= 1 + conjs.size());
                    if (i + 1 == orig_size) {
                        // no-op.
                    }
                    else if (orig_size <= conjs.size()) {
                        // no-op
                    }
                    else {
                        SASSERT(orig_size == 1 + conjs.size());
                        --orig_size;
                        --i;
                    }
                }
                else {
                    conjs[i] = tmp;
                }
            }            
            IF_VERBOSE(2, verbose_stream() << "Deleted " << num_deleted << " disequalities " << conjs.size() << " conjuncts\n";);
        }
        fml = m.mk_and(conjs.size(), conjs.c_ptr());        
    }

    // 
    // (f (if c1 (if c2 e1 e2) e3) b c) -> 
    // (if c1 (if c2 (f e1 b c)

    class ite_hoister {
        ast_manager& m;
    public:
        ite_hoister(ast_manager& m): m(m) {}

        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            if (m.is_ite(f)) {
                return BR_FAILED;
            }
            for (unsigned i = 0; i < num_args; ++i) {
                expr* c, *t, *e;
                if (!m.is_bool(args[i]) && m.is_ite(args[i], c, t, e)) {
                    expr_ref e1(m), e2(m);
                    ptr_vector<expr> args1(num_args, args);
                    args1[i] = t;
                    e1 = m.mk_app(f, num_args, args1.c_ptr());
                    if (t == e) {
                        result = e1;
                        return BR_REWRITE1;
                    }
                    args1[i] = e;
                    e2 = m.mk_app(f, num_args, args1.c_ptr());
                    result = m.mk_app(f, num_args, args);
                    result = m.mk_ite(c, e1, e2);
                    return BR_REWRITE3;
                }
            }
            return BR_FAILED;
        }
    };

    struct ite_hoister_cfg: public default_rewriter_cfg {
        ite_hoister m_r;
        bool rewrite_patterns() const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            return m_r.mk_app_core(f, num, args, result);
        }
        ite_hoister_cfg(ast_manager & m, params_ref const & p):m_r(m) {}        
    };

    class ite_hoister_star : public rewriter_tpl<ite_hoister_cfg> {
        ite_hoister_cfg m_cfg;
    public:
        ite_hoister_star(ast_manager & m, params_ref const & p):
            rewriter_tpl<ite_hoister_cfg>(m, false, m_cfg),
            m_cfg(m, p) {}
    };

    void hoist_non_bool_if(expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        ite_hoister_star ite_rw(m, p);
        expr_ref tmp(m);
        ite_rw(fml, tmp);
        fml = tmp;        
    }

    class test_diff_logic {
        ast_manager& m;
        arith_util a;
        bv_util    bv;
        bool m_is_dl;
        bool m_test_for_utvpi;

        bool is_numeric(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el;
            if (m.is_ite(e, cond, th, el)) {
                return is_numeric(th) && is_numeric(el);
            }
            return false;
        }
        
        bool is_arith_expr(expr *e) const {
            return is_app(e) && a.get_family_id() == to_app(e)->get_family_id();
        }

        bool is_offset(expr* e) const {
            if (a.is_numeral(e)) {
                return true;
            }
            expr* cond, *th, *el, *e1, *e2;
            if (m.is_ite(e, cond, th, el)) {
                return is_offset(th) && is_offset(el);
            }
            // recognize offsets.
            if (a.is_add(e, e1, e2)) {
                if (is_numeric(e1)) {
                    return is_offset(e2);
                }
                if (is_numeric(e2)) {
                    return is_offset(e1);
                }
                return false;
            }
            if (m_test_for_utvpi) {
                if (a.is_mul(e, e1, e2)) {
                    if (is_minus_one(e1)) {
                        return is_offset(e2);
                    }
                    if (is_minus_one(e2)) {
                        return is_offset(e1);
                    }
                }
            }
            return !is_arith_expr(e);
        }

        bool is_minus_one(expr const * e) const { 
            rational r; return a.is_numeral(e, r) && r.is_minus_one(); 
        }

        bool test_ineq(expr* e) const {
            SASSERT(a.is_le(e) || a.is_ge(e) || m.is_eq(e));
            SASSERT(to_app(e)->get_num_args() == 2);
            expr * lhs = to_app(e)->get_arg(0);
            expr * rhs = to_app(e)->get_arg(1);
            if (is_offset(lhs) && is_offset(rhs)) 
                return true;    
            if (!is_numeric(rhs)) 
                std::swap(lhs, rhs);
            if (!is_numeric(rhs)) 
                return false;    
            // lhs can be 'x' or '(+ x (* -1 y))'
            if (is_offset(lhs))
                return true;
            expr* arg1, *arg2;
            if (!a.is_add(lhs, arg1, arg2)) 
                return false;    
            // x
            if (m_test_for_utvpi) {
                return is_offset(arg1) && is_offset(arg2);
            }
            if (is_arith_expr(arg1)) 
                std::swap(arg1, arg2);
            if (is_arith_expr(arg1))
                return false;
            // arg2: (* -1 y)
            expr* m1, *m2;
            if (!a.is_mul(arg2, m1, m2))
                return false;
            return is_minus_one(m1) && is_offset(m2);
        }

        bool test_eq(expr* e) const {
            expr* lhs, *rhs;
            VERIFY(m.is_eq(e, lhs, rhs));
            if (!a.is_int_real(lhs)) {
                return true;
            }
            if (a.is_numeral(lhs) || a.is_numeral(rhs)) {
                return test_ineq(e);
            }
            return 
                test_term(lhs) && 
                test_term(rhs) &&
                !a.is_mul(lhs) &&
                !a.is_mul(rhs);
        }

        bool test_term(expr* e) const {
            if (m.is_bool(e)) {
                return true;
            }
            if (a.is_numeral(e)) {
                return true;
            }
            if (is_offset(e)) {
                return true;
            }
            expr* lhs, *rhs;
            if (a.is_add(e, lhs, rhs)) {
                if (!a.is_numeral(lhs)) {
                    std::swap(lhs, rhs);
                }
                return a.is_numeral(lhs) && is_offset(rhs);
            }
            if (a.is_mul(e, lhs, rhs)) {
                return is_minus_one(lhs) || is_minus_one(rhs);
            }
            return false;
        }

        bool is_non_arith_or_basic(expr* e) {
            if (!is_app(e)) {
                return false;
            }
            family_id fid = to_app(e)->get_family_id();

            if (fid == null_family_id && 
                !m.is_bool(e) && 
                to_app(e)->get_num_args() > 0) {
                return true;
            }
            return 
                fid != m.get_basic_family_id() &&
                fid != null_family_id &&
                fid != a.get_family_id() &&
                fid != bv.get_family_id();
        }

    public:
        test_diff_logic(ast_manager& m): m(m), a(m), bv(m), m_is_dl(true), m_test_for_utvpi(false) {}
       
        void test_for_utvpi() { m_test_for_utvpi = true; }

        void operator()(expr* e) {
            if (!m_is_dl) {
                return;
            }
            if (a.is_le(e) || a.is_ge(e)) {
                m_is_dl = test_ineq(e);
            }
            else if (m.is_eq(e)) {
                m_is_dl = test_eq(e);
            }
            else if (is_non_arith_or_basic(e)) {
                m_is_dl = false;
            }
            else if (is_app(e)) {
                app* a = to_app(e);                
                for (unsigned i = 0; m_is_dl && i < a->get_num_args(); ++i) {
                    m_is_dl = test_term(a->get_arg(i));
                }
            }

            if (!m_is_dl) {
                char const* msg = "non-diff: ";
                if (m_test_for_utvpi) {
                    msg = "non-utvpi: ";
                }
                IF_VERBOSE(1, verbose_stream() << msg << mk_pp(e, m) << "\n";);
            }
        }

        bool is_dl() const { return m_is_dl; }
    };

    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        test_diff_logic test(m);
        test.test_for_utvpi();
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

    class arith_normalizer : public poly_rewriter<arith_rewriter_core> {
        ast_manager& m;
        arith_util   m_util;
        enum op_kind { LE, GE, EQ };
    public:
        arith_normalizer(ast_manager& m, params_ref const& p = params_ref()): poly_rewriter<arith_rewriter_core>(m, p), m(m), m_util(m) {}
        
        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            br_status st = BR_FAILED;
            if (m.is_eq(f)) {
                SASSERT(num_args == 2); return mk_eq_core(args[0], args[1], result);
            }

            if (f->get_family_id() != get_fid()) {
                return st;
            }
            switch (f->get_decl_kind()) {
            case OP_NUM: st = BR_FAILED; break;
            case OP_IRRATIONAL_ALGEBRAIC_NUM: st = BR_FAILED; break;
            case OP_LE:  SASSERT(num_args == 2); st = mk_le_core(args[0], args[1], result); break;
            case OP_GE:  SASSERT(num_args == 2); st = mk_ge_core(args[0], args[1], result); break;
            case OP_LT:  SASSERT(num_args == 2); st = mk_lt_core(args[0], args[1], result); break;
            case OP_GT:  SASSERT(num_args == 2); st = mk_gt_core(args[0], args[1], result); break;
            default: st = BR_FAILED; break;
            }
            return st;
        }      

    private:
        
        br_status mk_eq_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, EQ, result);
        }
        br_status mk_le_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, LE, result);
        }
        br_status mk_ge_core(expr* arg1, expr* arg2, expr_ref& result) {
            return mk_le_ge_eq_core(arg1, arg2, GE, result);
        }
        br_status mk_lt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_ge(arg1, arg2));
            return BR_REWRITE2;
        }
        br_status mk_gt_core(expr* arg1, expr* arg2, expr_ref& result) {
            result = m.mk_not(m_util.mk_le(arg1, arg2));
            return BR_REWRITE2;
        }

        br_status mk_le_ge_eq_core(expr* arg1, expr* arg2, op_kind kind, expr_ref& result) {
            if (m_util.is_real(arg1)) {
                numeral g(0);
                get_coeffs(arg1, g);
                get_coeffs(arg2, g);
                if (!g.is_one() && !g.is_zero()) {
                    SASSERT(g.is_pos());
                    expr_ref new_arg1 = rdiv_polynomial(arg1, g);
                    expr_ref new_arg2 = rdiv_polynomial(arg2, g);
                    switch(kind) {
                    case LE: result = m_util.mk_le(new_arg1, new_arg2); return BR_DONE;
                    case GE: result = m_util.mk_ge(new_arg1, new_arg2); return BR_DONE;
                    case EQ: result = m_util.mk_eq(new_arg1, new_arg2); return BR_DONE;
                    }
                }
            }
            return BR_FAILED;
        }

        void update_coeff(numeral const& r, numeral& g) {
            if (g.is_zero() || abs(r) < g) {
                g = abs(r);
            }
        }        

        void get_coeffs(expr* e, numeral& g) {
            rational r;
            unsigned sz;
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (!m_util.is_numeral(arg, r)) {
                    get_power_product(arg, r);
                }
                update_coeff(r, g);
            }
        }

        expr_ref rdiv_polynomial(expr* e, numeral const& g) {
            rational r;
            SASSERT(g.is_pos());
            SASSERT(!g.is_one());
            expr_ref_vector monomes(m);
            unsigned sz;           
            expr* const* args = get_monomials(e, sz);
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = args[i];
                if (m_util.is_numeral(arg, r)) {
                    monomes.push_back(m_util.mk_numeral(r/g, false));
                }
                else {
                    expr* p = get_power_product(arg, r);
                    r /= g;
                    if (r.is_one()) {
                        monomes.push_back(p);
                    }
                    else {
                        monomes.push_back(m_util.mk_mul(m_util.mk_numeral(r, false), p));
                    }
                }
            }
            expr_ref result(m);
            mk_add(monomes.size(), monomes.c_ptr(), result);
            return result;
        }
                
    };
    

    struct arith_normalizer_cfg: public default_rewriter_cfg {
        arith_normalizer m_r;
        bool rewrite_patterns() const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            return m_r.mk_app_core(f, num, args, result);
        }
        arith_normalizer_cfg(ast_manager & m, params_ref const & p):m_r(m,p) {}        
    };

    class arith_normalizer_star : public rewriter_tpl<arith_normalizer_cfg> {
        arith_normalizer_cfg m_cfg;
    public:
        arith_normalizer_star(ast_manager & m, params_ref const & p):
            rewriter_tpl<arith_normalizer_cfg>(m, false, m_cfg),
            m_cfg(m, p) {}
    };


    void normalize_arithmetic(expr_ref& t) {
        ast_manager& m = t.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        arith_normalizer_star rw(m, p);
        expr_ref tmp(m);
        rw(t, tmp);
        t = tmp;                
    }

}

template class rewriter_tpl<pdr::ite_hoister_cfg>;
template class rewriter_tpl<pdr::arith_normalizer_cfg>;


