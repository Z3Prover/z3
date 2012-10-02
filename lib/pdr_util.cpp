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

namespace pdr {

unsigned ceil_log2(unsigned u)
{
    if (u==0) { return 0; }
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
// model_evaluator_base
//


void model_evaluator_base::minimize_model(ptr_vector<expr> const & formulas, expr_ref_vector & model)
{
    ast_manager & m = model.get_manager();
    bool has_unknown, has_false;
    DEBUG_CODE( 
        check_model(formulas, model, has_unknown, has_false);
        if (has_false) {
            std::cout<<"formulas: "<<pdr::pp_cube(formulas, m)<<"\n";
            std::cout<<"model: "<<pdr::pp_cube(model, m)<<"\n";
        }
        SASSERT(!has_false);
        );

    unsigned i=0;
    while(i<model.size()) {
        expr_ref removed(m);
        removed = model[i].get();
        if (i<model.size()-1) {
            model[i] = model.back();
        }
        model.pop_back();

        check_model(formulas, model, has_unknown, has_false);
        SASSERT(!has_false);

        if (has_unknown) {
            //if we introduced unknown, we restore the removed element
            if (i<model.size()) {
                model.push_back(model[i].get());
                model[i] = removed;
            }
            else {
                model.push_back(removed);
            }
            i++;
        }
    }
}

/////////////////////////////////////
// th_rewriter_model_evaluator_base
//


class th_rewriter_model_evaluator::expr_rewriter_cfg : public default_rewriter_cfg
{
    const obj_map<expr,expr *>& m_assignment;
public:
    expr_rewriter_cfg(const obj_map<expr,expr *>& assignment)
        : m_assignment(assignment)
    {
    }

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        return m_assignment.find(s,t);
    }
};

void th_rewriter_model_evaluator::setup_assignment(expr_ref_vector const& model, obj_map<expr,expr*>& assignment) {

    for (unsigned i = 0; i < model.size(); ++i) {        
        expr * mlit = model[i]; //model literal
        if (is_uninterp(mlit)) {
            assignment.insert(mlit, m.mk_true());
        }
        expr * arg1;
        expr * arg2;
        if (m.is_not(mlit, arg1)) {
            assignment.insert(arg1, m.mk_false());
        }
        else if (m.is_eq(mlit, arg1, arg2)) {
            if (!is_uninterp(arg1)) {
                std::swap(arg1, arg2);
            }
            if (is_uninterp(arg1)) {
                assignment.insert(arg1, arg2);
            }
            else {
                assignment.insert(mlit, m.mk_true());
            }
        }
    }
}

void th_rewriter_model_evaluator::check_model(ptr_vector<expr> const & formulas, expr_ref_vector & model, 
                                              bool & has_unknown, bool & has_false)
{
    obj_map<expr,expr *> assignment;

    setup_assignment(model, assignment);

    expr_rewriter_cfg r_cfg(assignment);
    rewriter_tpl<expr_rewriter_cfg> rwr(m, false, r_cfg);

    has_false   = false;
    has_unknown = false;

    for (unsigned i = 0; i < formulas.size(); ++i) {
        expr * form = formulas[i];
        expr_ref asgn_form(m);
        rwr(form, asgn_form);
        expr_ref simpl_form(m);                
        m_rewriter(asgn_form, simpl_form);
        if (m.is_false(simpl_form)) {
            has_false = true;
        }
        else if (!m.is_true(simpl_form)) {
            IF_VERBOSE(7, verbose_stream() << "formula evaluated as unknown:\noriginal: "
                 << mk_pp(form, m) << "\n"
                 << "simplified: " << mk_pp(simpl_form,m) << "\n";);
            has_unknown = true;
        }
    }
    m_rewriter.reset();
}

    //00 -- non-visited
    //01 -- X
    //10 -- false
    //11 -- true

#define UNKNOWN(x) (!m1.is_marked(x) && !m2.is_marked(x))
#define SET_UNKNOWN(x) { TRACE("pdr_verbose", tout << "unknown: " << mk_pp(x,m) << "\n";); m1.reset_mark(x); m2.reset_mark(x); }
#define IS_X(x) (!m1.is_marked(x) && m2.is_marked(x))
#define IS_FALSE(x) (m1.is_marked(x) && !m2.is_marked(x))
#define IS_TRUE(x) (m1.is_marked(x) && m2.is_marked(x))
#define SET_X(x) { SASSERT(UNKNOWN(x)); m2.mark(x); }
#define SET_V(x) { SASSERT(UNKNOWN(x)); m1.mark(x); }
#define SET_FALSE(x) { SASSERT(UNKNOWN(x)); m1.mark(x); }
#define SET_TRUE(x) { SASSERT(UNKNOWN(x)); m1.mark(x); m2.mark(x); }
#define SET_BOOL(x, v) { if (v) { SET_TRUE(x); } else { SET_FALSE(x); } }
#define GET_VALUE(x)  m_values.find(x)
#define SET_VALUE(x,y) { SET_V(x); TRACE("pdr_verbose", tout << mk_pp(x,m) << " " << y << "\n";); m_values.insert(x, y); }

void ternary_model_evaluator::add_model(expr* e) {
    expr* nlit, *var, *val;
    rational r;
    // SASSERT(UNKNOWN(e));
    if (m.is_eq(e, var, val)) {
        if (!is_uninterp(var)) {
            std::swap(var, val);
        }
        if (m.is_true(val) && UNKNOWN(var)) {
            SET_TRUE(var);
        }
        else if (m.is_false(val) && UNKNOWN(var)) {
            SET_FALSE(var);
        }
        else if (m_arith.is_numeral(val, r) && UNKNOWN(var)) {
            SET_VALUE(var, r);
        }
        else {
            TRACE("pdr_verbose", tout << "no value for " << mk_pp(val, m) << "\n";);
        }
    }
    else if (m.is_not(e, nlit)) {
        SET_FALSE(nlit);
    }
    else if (m.is_bool(e)) {
        SET_TRUE(e);
    }
    else {
        TRACE("pdr_verbose", tout << "no value set of " << mk_pp(e, m) << "\n";);
    }
}

void ternary_model_evaluator::del_model(expr* e) {
    expr* nlit, *var, *val;
    if (m.is_eq(e, var, val)) {
        if (!is_uninterp(var)) {
            std::swap(var, val);
        }
        SET_UNKNOWN(var);
        m_values.remove(var);
    }
    else if (m.is_not(e, nlit)) {
        SET_UNKNOWN(nlit);
    }
    else if (m.is_bool(e)) {
        SET_UNKNOWN(e);
    }
    else {
        TRACE("pdr_verbose", tout << "no value set of " << mk_pp(e, m) << "\n";);
    }
}

void ternary_model_evaluator::setup_model(expr_ref_vector const& model) {
    m_values.reset();
    for (unsigned i = 0; i < model.size(); ++i) {
        expr* e = model[i]; 
        if (UNKNOWN(e)) {
            add_model(e);
        }
    }
    m_level1 = m1.get_level();
    m_level2 = m2.get_level();
}

void ternary_model_evaluator::minimize_model(ptr_vector<expr> const & formulas, expr_ref_vector & model)
{
    setup_model(model);

    TRACE("pdr_verbose", 
        for (unsigned i = 0; i < model.size(); ++i) tout << mk_pp(model[i].get(), m) << "\n"; 
        tout << "formulas\n";
        for (unsigned i = 0; i < formulas.size(); ++i) tout << mk_pp(formulas[i], m) << "\n"; 
    );
    for (unsigned i = 0; i < model.size(); ) {
        expr_ref removed(model[i].get(), m);
        if (i + 1 < model.size()) {
            model[i] = model.back();
        }
        model.pop_back();        
        del_model(removed);
        m1.set_level(m_level1);
        m2.set_level(m_level2);

        bool formulas_hold = check_model(formulas);
        m1.set_level(m_level1);
        m2.set_level(m_level2);


        if (!formulas_hold) {
            // if we introduced unknown, we restore the removed element
            add_model(removed);
            m_level1 = m1.get_level();
            m_level2 = m2.get_level();
            if (i < model.size()) {
                model.push_back(model[i].get());
                model[i] = removed;
            }
            else {
                model.push_back(removed);
            }
            i++;
        }
    }
    m1.reset();
    m2.reset();
    m_values.reset();
}


bool ternary_model_evaluator::check_model(ptr_vector<expr> const& formulas) {
    ptr_vector<expr> todo;
    assign_vector_with_casting(todo, formulas);

    expr *argCond, *argThen, *argElse, *arg;
    rational r, r2;

    while(!todo.empty()) {
        expr * curr_e = todo.back();
        unsigned pre_curr_depth  = todo.size()-1;

        if (!is_app(curr_e)) { 
            todo.pop_back();
            continue;
        }
        app * curr = to_app(curr_e);
                
#define ARG1 curr->get_arg(0)
#define ARG2 curr->get_arg(1)        

        if (!UNKNOWN(curr)) { 
            todo.pop_back();
            continue;
        }
        unsigned arity = curr->get_num_args();

        if (curr->get_family_id() == m_arith.get_family_id()) {
            bool all_set = true, some_x = false;
            for (unsigned i = 0; !some_x && i < arity; ++i) {
                expr* arg = curr->get_arg(i);
                if (UNKNOWN(arg)) {
                    todo.push_back(arg);
                    all_set = false;
                }
                else if (IS_X(arg)) {
                    some_x = true;
                }
            }
            if (some_x) {
                SET_X(curr);                
            }
            else if (!all_set) {
                continue;
            }
            else {
                switch(curr->get_decl_kind()) {
                case OP_NUM: 
                    VERIFY(m_arith.is_numeral(curr,r));
                    SET_VALUE(curr, r);
                    break;                
                case OP_IRRATIONAL_ALGEBRAIC_NUM:  
                    SET_X(curr);
                    break;
                case OP_LE:
                    SET_BOOL(curr, GET_VALUE(ARG1) <= GET_VALUE(ARG2));
                    break;
                case OP_GE:
                    SET_BOOL(curr, GET_VALUE(ARG1) >= GET_VALUE(ARG2));
                    break;
                case OP_LT:
                    SET_BOOL(curr, GET_VALUE(ARG1) < GET_VALUE(ARG2));
                    break;
                case OP_GT:
                    SET_BOOL(curr, GET_VALUE(ARG1) > GET_VALUE(ARG2));
                    break;
                case OP_ADD: 
                    r = rational::zero();
                    for (unsigned i = 0; i < arity; ++i) {
                        r += GET_VALUE(curr->get_arg(i));
                    }
                    SET_VALUE(curr, r);
                    break;                                    
                case OP_SUB: 
                    r = GET_VALUE(curr->get_arg(0));
                    for (unsigned i = 1; i < arity; ++i) {
                        r -= GET_VALUE(curr->get_arg(i));
                    }
                    SET_VALUE(curr, r);
                    break;                            
                case OP_UMINUS: 
                    SASSERT(arity == 1);
                    SET_VALUE(curr, GET_VALUE(curr->get_arg(0)));
                    break;                
                case OP_MUL: 
                    r = rational::one();
                    for (unsigned i = 0; i < arity; ++i) {
                        r *= GET_VALUE(curr->get_arg(i));
                    }
                    SET_VALUE(curr, r);
                    break;                
                case OP_DIV: 
                    SASSERT(arity == 2);
                    r = GET_VALUE(ARG2);
                    if (r.is_zero()) {
                        SET_X(curr);
                    }
                    else {
                        SET_VALUE(curr, GET_VALUE(ARG1) / r);
                    }
                    break;                
                case OP_IDIV: 
                    SASSERT(arity == 2);
                    r = GET_VALUE(ARG2);
                    if (r.is_zero()) {
                        SET_X(curr);
                    }
                    else {
                        SET_VALUE(curr, div(GET_VALUE(ARG1), r));
                    }
                    break;                
                case OP_REM: 
                    // rem(v1,v2) = if v2 >= 0 then mod(v1,v2) else -mod(v1,v2)
                    SASSERT(arity == 2);
                    r = GET_VALUE(ARG2);
                    if (r.is_zero()) {
                        SET_X(curr);
                    }
                    else {
                        r2 = mod(GET_VALUE(ARG1), r);
                        if (r.is_neg()) r2.neg();
                        SET_VALUE(curr, r2);
                    }
                    break;
                case OP_MOD: 
                    SASSERT(arity == 2);
                    r = GET_VALUE(ARG2);
                    if (r.is_zero()) {
                        SET_X(curr);
                    }
                    else {
                        SET_VALUE(curr, mod(GET_VALUE(ARG1), r));
                    }
                    break;                   
                case OP_TO_REAL: 
                    SASSERT(arity == 1);
                    SET_VALUE(curr, GET_VALUE(ARG1));
                    break;                
                case OP_TO_INT: 
                    SASSERT(arity == 1);
                    SET_VALUE(curr, floor(GET_VALUE(ARG1)));
                    break;                
                case OP_IS_INT: 
                    SASSERT(arity == 1);
                    SET_BOOL(curr, GET_VALUE(ARG1).is_int());
                    break;
                case OP_POWER:
                    SET_X(curr);
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
        }
        else if (curr->get_family_id() == m_bv.get_family_id()) {
            throw default_exception("PDR engine currently does not support bit-vectors");
        }
        else if (curr->get_family_id() == m.get_basic_family_id()) {
            expr* arg1, *arg2;
            if (m.is_and(curr)) {
                // we're adding unknowns on the top of the todo stack, if there is none added, 
                // all arguments were known
                bool has_x = false, has_false = false;
                for (unsigned j = 0; !has_false && j < arity; ++j) {
                    expr * arg = curr->get_arg(j);
                    if (IS_FALSE(arg)) {
                        has_false = true;
                    }
                    else if (IS_X(arg)) {
                        has_x = true;
                    }
                    else if (UNKNOWN(arg)) {
                        todo.push_back(arg);
                    }
                }
                if (has_false) {
                    SET_FALSE(curr);
                }
                else {
                    if (todo.back() != curr) {
                        continue;
                    }
                    else if (has_x) {
                        SET_X(curr);
                    }                
                    else {
                        SET_TRUE(curr);
                    }
                }
            }
            else if (m.is_or(curr)) {
                bool has_x = false, has_true = false;
                for (unsigned j = 0; !has_true && j < arity; ++j) {
                    expr * arg = curr->get_arg(j);
                    if (IS_TRUE(arg)) {
                        has_true = true;
                    }
                    else if (IS_X(arg)) {
                        has_x = true;
                    }
                    else if (UNKNOWN(arg)) {
                        todo.push_back(arg);
                    }
                }
                if (has_true) {
                    SET_TRUE(curr);
                }
                else {
                    if (todo.back() != curr) {
                        continue;
                    }
                    else if (has_x) {
                        SET_X(curr);
                    }
                    else {
                        SET_FALSE(curr);
                    }
                }
            }
            else if (m.is_not(curr, arg)) {
                if (UNKNOWN(arg)) {
                    todo.push_back(arg);
                    continue;
                }
                if (IS_TRUE(arg)) {
                    SET_FALSE(curr);
                }
                else if (IS_FALSE(arg)) {
                    SET_TRUE(curr);
                }
                else {
                    SASSERT(IS_X(arg));
                    SET_X(curr);
                }
            }
            else if (m.is_implies(curr, arg1, arg2)) {
                if (IS_FALSE(arg1) || IS_TRUE(arg2)) {
                    SET_TRUE(curr);
                }
                else if (UNKNOWN(arg1) || UNKNOWN(arg2)) {
                    if (UNKNOWN(arg1)) { todo.push_back(arg1); }
                    if (UNKNOWN(arg2)) { todo.push_back(arg2); }
                    continue;
                }
                else if (IS_TRUE(arg1) && IS_FALSE(arg2)) {
                    SET_FALSE(curr);
                }
                else {
                    SASSERT(IS_X(arg1) || IS_X(arg2));
                    SET_X(curr);
                }
            }
            else if (m.is_iff(curr, arg1, arg2) ||
                     (m.is_eq(curr, arg1, arg2) && m.is_bool(arg1))) {
                if (IS_X(arg1) || IS_X(arg2)) {
                    SET_X(curr);
                }
                else if (UNKNOWN(arg1) || UNKNOWN(arg2)) {
                    if (UNKNOWN(arg1)) { todo.push_back(arg1); }
                    if (UNKNOWN(arg2)) { todo.push_back(arg2); }
                    continue;
                }
                else {
                    bool val = IS_TRUE(arg1)==IS_TRUE(arg2);
                    SASSERT(val == (IS_FALSE(arg1)==IS_FALSE(arg2)));
                    if (val) {
                        SET_TRUE(curr);
                    }
                    else {
                        SET_FALSE(curr);
                    }            
                }    
            }
            else if (m.is_ite(curr, argCond, argThen, argElse) && m.is_bool(argThen)) {
                if (IS_TRUE(argCond)) {
                    if (IS_TRUE(argThen)) { SET_TRUE(curr); }
                    else if (IS_FALSE(argThen)) { SET_FALSE(curr); }
                    else if (IS_X(argThen)) { SET_X(curr); }
                    else {
                        todo.push_back(argThen);
                        continue;
                    }
                }
                else if (IS_FALSE(argCond)) {
                    if (IS_TRUE(argElse)) { SET_TRUE(curr); }
                    else if (IS_FALSE(argElse)) { SET_FALSE(curr); }
                    else if (IS_X(argElse)) { SET_X(curr); }
                    else {
                        todo.push_back(argElse);
                        continue;
                    }
                }
                else if (IS_TRUE(argThen) && IS_TRUE(argElse)) {
                    SET_TRUE(curr);
                }
                else if (IS_FALSE(argThen) && IS_FALSE(argElse)) {
                    SET_FALSE(curr);
                }
                else if (IS_X(argCond) && (IS_X(argThen) || IS_X(argElse)) ) {
                    SET_X(curr);
                } else if (UNKNOWN(argCond) || UNKNOWN(argThen) || UNKNOWN(argElse)) {
                    if (UNKNOWN(argCond)) { todo.push_back(argCond); }
                    if (UNKNOWN(argThen)) { todo.push_back(argThen); }
                    if (UNKNOWN(argElse)) { todo.push_back(argElse); }
                    continue;
                }
                else {
                    SASSERT(IS_X(argCond));
                    SASSERT((IS_TRUE(argThen) && IS_FALSE(argElse)) ||
                            (IS_FALSE(argThen) && IS_TRUE(argElse)));
                    SET_X(curr);
                }
            }
            else if (m.is_true(curr)) {
                SET_TRUE(curr);
            }
            else if (m.is_false(curr)) {
                SET_FALSE(curr);
            }
            else if (m.is_eq(curr, arg1, arg2) && arg1 == arg2) {
                SET_TRUE(curr);
            }
            else if (m.is_eq(curr, arg1, arg2)) {
                if (UNKNOWN(arg1)) {
                    todo.push_back(arg1);
                }
                if (UNKNOWN(arg2)) {
                    todo.push_back(arg2);
                }
                if (curr != todo.back()) {
                    continue;
                }
                if (IS_X(arg1) || IS_X(arg2)) {
                    SET_X(curr);
                }
                else {
                    SET_BOOL(curr, GET_VALUE(arg1) == GET_VALUE(arg2));
                }
            }
            else if (m.is_ite(curr, argCond, argThen, argElse) && m_arith.is_int_real(argThen)) {
                if (IS_TRUE(argCond) || (argThen == argElse)) {
                    if (UNKNOWN(argThen)) {
                        todo.push_back(argThen);
                        continue;
                    }
                    if (IS_X(argThen)) {
                        SET_X(curr);
                    }
                    else {
                        SET_VALUE(curr, GET_VALUE(argThen));
                    }
                }
                else if (IS_FALSE(argCond)) {
                    if (UNKNOWN(argElse)) {
                        todo.push_back(argElse);
                        continue;
                    }
                    if (IS_X(argElse)) {
                        SET_X(curr);
                    }
                    else {
                        SET_VALUE(curr, GET_VALUE(argElse));
                    }
                }
                else if (UNKNOWN(argCond)) {
                    todo.push_back(argCond);
                    continue;
                }
                else {
                    SET_X(curr);
                }
            }
            else {
                UNREACHABLE();
            }
        }
        else {
            TRACE("pdr_verbse", tout << "Not evaluated " << mk_pp(curr, m) << "\n";);
            SET_X(curr);
        }

        IF_VERBOSE(35,verbose_stream() << "assigned "<<mk_pp(curr_e,m) 
            <<(IS_TRUE(curr_e) ? "true" : IS_FALSE(curr_e) ? "false" : "unknown") << "\n";);
        SASSERT(!UNKNOWN(curr));
        todo.shrink(pre_curr_depth);
    }
    
    bool has_unknown = false;
    for (unsigned i = 0; i < formulas.size(); ++i) {
        expr * form = formulas[i];
        SASSERT(!UNKNOWN(form));
        TRACE("pdr_verbose", 
            tout << "formula is " << (IS_TRUE(form) ? "true" : IS_FALSE(form) ? "false" : "unknown") << "\n" <<mk_pp(form, m)<< "\n";);

        if (IS_FALSE(form)) {
            IF_VERBOSE(2, verbose_stream() << "formula false in model: "<<mk_pp(form, m) << "\n";);
            UNREACHABLE();
        }
        if (IS_X(form)) {
            has_unknown = true;
        }
    }
    return !has_unknown;
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

void get_cube_from_model(const model_core & mdl, expr_ref_vector & res, pdr::prop_solver& solver)
{
    ast_manager& m = res.get_manager();

    res.reset();
    unsigned sz = mdl.get_num_constants();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * d = mdl.get_constant(i);

        if (solver.is_aux_symbol(d)) {
            continue;
        }

        SASSERT(d->get_arity()==0);
        expr_ref interp(m);
        pdr::get_value_from_model(mdl, d, interp);

        app_ref constant(m.mk_const(d), m);
        app_ref lit(m);
        if (m.is_bool(d->get_range())) {
            if (m.is_true(interp)) {
                lit = constant;
            }
            else {
                SASSERT(m.is_false(interp));
                lit = m.mk_not(constant);
            }
        }
        else {
            lit = m.mk_eq(constant, interp);
        }
        res.push_back(lit);
    }
}

}
