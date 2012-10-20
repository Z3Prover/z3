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
#include "front_end_params.h"
#include "model.h"
#include "model_v2_pp.h"
#include "ref_vector.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "util.h"
#include "pdr_manager.h"
#include "pdr_prop_solver.h"
#include "pdr_util.h"
#include "arith_decl_plugin.h"
#include "expr_replacer.h"
#include "static_features.h"


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
        IF_VERBOSE(3, verbose_stream() << "Not evaluated " << mk_pp(e, m) << "\n";);
        TRACE("pdr", tout << "Variable is not tracked: " << mk_pp(e, m) << "\n";);
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

    m_level1 = m1.get_level();
    m_level2 = m2.get_level();
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
    
    setup_model(mdl);
    expr_ref_vector result(m);
    ptr_vector<expr> tocollect;

    collect(formulas, tocollect);
    for (unsigned i = 0; i < tocollect.size(); ++i) {
        expr* e = tocollect[i];
        SASSERT(m.is_bool(e));
        SASSERT(is_true(e) || is_false(e));
        if (is_true(e)) {
            result.push_back(e);
        }
        else {
            result.push_back(m.mk_not(e));
        }
    }
    reset();
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
            else if (!m.is_bool(args[0])) {
                tocollect.push_back(e);
            }
            else {
                todo.append(sz, args);
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
    m1.set_level(m_level1);
    m2.set_level(m_level2);
    
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
    expr_ref e(m), eq(m);
    expr_ref_vector model(m);
    bool_rewriter rw(m);
    for (unsigned i = 0; i < sz; i++) {
        func_decl * d = m_model->get_constant(i); 
        expr* val = m_model->get_const_interp(d);
        e = m.mk_const(d);
        if (m_visited.is_marked(e)) {
            rw.mk_eq(e, val, eq);
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
    SASSERT(!is_unknown(v));
    SASSERT(m.get_sort(e) == m.get_sort(v));
    if (m.is_bool(e)) {
        SASSERT(m.is_bool(v));
        if (is_true(v)) set_true(e);
        else if (is_false(v)) set_false(e);
        else set_x(e);
    }
    else if (m_arith.is_int_real(e)) {
        set_number(e, get_number(v));
    }
    else if (m.is_value(v)) {
        set_value(e, v);
    }
    else {
        set_x(e);
    }
}

void model_evaluator::eval_iff(app* e, expr* arg1, expr* arg2) {
    if (arg1 == arg2) {
        set_true(e);
    }
    else if (is_x(arg1) || is_x(arg2)) {
        set_x(e);
    }
    else {
        bool val = is_true(arg1) == is_true(arg2);
        SASSERT(val == (is_false(arg1) == is_false(arg2)));
        if (val) {
            set_true(e);
        }
        else {
            set_false(e);
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
        eval_iff(e, arg1, arg2);
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
        if (m.is_bool(arg1)) {
            eval_iff(e, arg1, arg2);
        }
        else if (arg1 == arg2) {
            set_true(e);
        }
        else if (is_x(arg1) || is_x(arg2)) {
            set_x(e);
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
            else {
                set_x(e);
            }
        }
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
            has_x = true;
        }
    }
    return !has_x;
}

    func_decl * mk_store(ast_manager& m, sort * arr_sort)
    {
        family_id array_fid = m.get_family_id(symbol("array"));
        
        unsigned num_params = arr_sort->get_num_parameters();
        
        ptr_vector<sort> domain;
        domain.push_back(arr_sort);
        
        //we push params of the array as remaining arguments of the store. The first 
        //num_params-1 parameters are indices and the last one is the range of the array
        for (unsigned i=0; i<num_params; ++i) {
            domain.push_back(to_sort(arr_sort->get_parameter(i).get_ast()));
        }
        
        return m.mk_func_decl(array_fid, OP_STORE, 
                              arr_sort->get_num_parameters(), arr_sort->get_parameters(), 
                              domain.size(), domain.c_ptr(), arr_sort);
    }

    void get_as_array_value(const model_core & mdl, expr * arr_e, expr_ref& res) {
        ast_manager& m = mdl.get_manager();
        array_util pl(m);
        SASSERT(pl.is_as_array(arr_e));
        
        app * arr = to_app(arr_e);
    
        unsigned sz = 0;
        func_decl_ref f(pl.get_as_array_func_decl(arr), m);
        sort * arr_sort = arr->get_decl()->get_range();
        func_interp* g = mdl.get_func_interp(f);
        
        res = pl.mk_const_array(arr_sort, g->get_else());

        unsigned arity = f->get_arity();
        
        sz = g->num_entries();
        if (sz) {
            func_decl_ref store_fn(mk_store(m, arr_sort), m);
            ptr_vector<expr> store_args;
            for (unsigned i = 0; i < sz; ++i) {
                const func_entry * fe = g->get_entry(i);
                store_args.reset();
                store_args.push_back(res);
                store_args.append(arity, fe->get_args());
                store_args.push_back(fe->get_result());
                res = m.mk_app(store_fn, store_args.size(), store_args.c_ptr());
            }
        }
    }

    void get_value_from_model(const model_core & mdl, func_decl * f, expr_ref& res) {
        SASSERT(f->get_arity()==0);
        ast_manager& m = mdl.get_manager();
        
        res = mdl.get_const_interp(f);
        
        array_util pl(m);
        
        if (pl.is_as_array(res)) {
            get_as_array_value(mdl, res, res);
        }
    }
    
    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        expr_ref_vector conjs(m);
        datalog::flatten_and(fml, conjs);
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

    class ite_hoister {
        ast_manager& m;
    public:
        ite_hoister(ast_manager& m): m(m) {}

        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            for (unsigned i = 0; i < num_args; ++i) {
                expr* c, *t, *e;
                if (!m.is_bool(args[i]) && m.is_ite(args[i], c, t, e)) {
                    expr_ref e1(m), e2(m);
                    ptr_vector<expr> args1(num_args, args);
                    args1[i] = t;
                    e1 = m.mk_app(f, num_args, args1.c_ptr());
                    args1[i] = e;
                    e2 = m.mk_app(f, num_args, args1.c_ptr());
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

    template class rewriter_tpl<ite_hoister_cfg>;


    class scoped_no_proof {
        ast_manager& m;
        proof_gen_mode m_mode;
    public:
        scoped_no_proof(ast_manager& m): m(m) {
            m_mode = m.proof_mode();
            m.toggle_proof_mode(PGM_DISABLED);
        }
        ~scoped_no_proof() {
            m.toggle_proof_mode(m_mode);            
        }
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
        bool m_is_dl;
    public:
        test_diff_logic(ast_manager& m): m(m), a(m), m_is_dl(true) {}
        
        void operator()(expr* e) {
            if (m_is_dl && a.is_arith_expr(e) && !a.is_numeral(e) && 
                !a.is_add(e) && !a.is_mul(e) && !m.is_bool(e)) {
                m_is_dl = false;
            }
        }

        bool is_dl() const { return m_is_dl; }
    };

    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls) {
        static_features st(m);
        st.collect(num_fmls, fmls);
        if (st.m_num_arith_eqs != st.m_num_diff_eqs ||
            st.m_num_arith_terms != st.m_num_diff_terms ||
            st.m_num_arith_ineqs != st.m_num_diff_ineqs) {     
            return false;
        }
        test_diff_logic test(m);
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < num_fmls; ++i) {
            quick_for_each_expr(test, mark, fmls[i]);
        } 
        return test.is_dl();
    }  

}
