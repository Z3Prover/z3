/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_implicant.cpp

Abstract:

    Facility to extract prime implicant from model.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:


Notes: 
    

--*/

#include <sstream>
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/for_each_expr.h"
#include "model/model.h"
#include "util/ref_vector.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/util.h"
#include "model/model_implicant.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"
#include "model/model_smt2_pp.h"
#include "ast/rewriter/poly_rewriter.h"
#include "ast/rewriter/poly_rewriter_def.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/scoped_proof.h"



/////////////////////////
// model_implicant
//


void model_implicant::assign_value(expr* e, expr* val) {
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

void model_implicant::setup_model(model_ref& model) {
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

void model_implicant::reset() {
    m1.reset();
    m2.reset();
    m_values.reset();
    m_visited.reset();
    m_numbers.reset();
    m_refs.reset();
    m_model = nullptr;
}

expr_ref_vector model_implicant::minimize_model(ptr_vector<expr> const & formulas, model_ref& mdl) {
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

expr_ref_vector model_implicant::minimize_literals(ptr_vector<expr> const& formulas, model_ref& mdl) {
    
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

void model_implicant::process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect) {
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
    
void model_implicant::collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect) {
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

expr_ref_vector model_implicant::prune_by_cone_of_influence(ptr_vector<expr> const & formulas) {
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

void model_implicant::eval_arith(app* e) {
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

void model_implicant::inherit_value(expr* e, expr* v) {
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

void model_implicant::eval_exprs(expr_ref_vector& es) {
    model_ref mr(m_model);
    for (unsigned j = 0; j < es.size(); ++j) {
        if (m_array.is_as_array(es[j].get())) {
            es[j] = eval(mr, es[j].get());
        }
    }
}

bool model_implicant::extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case) {
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
void model_implicant::eval_array_eq(app* e, expr* arg1, expr* arg2) {
    TRACE("pdr", tout << "array equality: " << mk_pp(e, m) << "\n";);
    expr_ref v1 = (*m_model)(arg1);
    expr_ref v2 = (*m_model)(arg2);
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
        w1 = (*m_model)(s1);
        w2 = (*m_model)(s2);
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

void model_implicant::eval_eq(app* e, expr* arg1, expr* arg2) {
    if (arg1 == arg2) {
        set_true(e);
    }
    else if (m_array.is_array(arg1)) {
        eval_array_eq(e, arg1, arg2);
    }
    else if (is_x(arg1) || is_x(arg2)) {
        expr_ref eq(m);
        eq = m.mk_eq(arg1, arg2);
        expr_ref vl = (*m_model)(eq);
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

void model_implicant::eval_basic(app* e) {
    expr* arg1 = nullptr, *arg2 = nullptr;
    expr *argCond = nullptr, *argThen = nullptr, *argElse = nullptr, *arg = nullptr;
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
    
bool model_implicant::check_model(ptr_vector<expr> const& formulas) {
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
            expr_ref vl = (*m_model)(curr);
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

expr_ref model_implicant::eval(model_ref& model, func_decl* d) {
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

expr_ref model_implicant::eval(model_ref& model, expr* e) {
    expr_ref result(m);
    m_model = model;
    result = (*m_model)(e);
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
                result = m_array.mk_store(args);
            }
            return result;
        }
    }
    return result;
}




