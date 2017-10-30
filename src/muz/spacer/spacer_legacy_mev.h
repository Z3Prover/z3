/**
Copyright (c) 2017 Arie Gurfinkel

 Deprecated implementation of model evaluator. To be removed.
*/
#ifndef OLD_MEV_H
#define OLD_MEV_H

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include "util/ref_vector.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"

namespace old {
class model_evaluator {
    ast_manager&           m;
    arith_util             m_arith;
    array_util             m_array;
    obj_map<expr, rational> m_numbers;
    expr_ref_vector        m_refs;
    obj_map<expr, expr*>   m_values;
    model_ref              m_model;

    //00 -- non-visited
    //01 -- X
    //10 -- false
    //11 -- true
    expr_mark      m1;
    expr_mark      m2;

    /// used by collect()
    expr_mark      m_visited;



    void reset();

    /// caches the values of all constants in the given model
    void setup_model(const model_ref& model);
    /// caches the value of an expression
    void assign_value(expr* e, expr* v);

    /// extracts an implicant of the conjunction of formulas
    void collect(ptr_vector<expr> const& formulas, ptr_vector<expr>& tocollect);

    /// one-round of extracting an implicant of e. The implicant
    /// literals are stored in tocollect. The worklist is stored in todo
    void process_formula(app* e, ptr_vector<expr>& todo, ptr_vector<expr>& tocollect);
    void eval_arith(app* e);
    void eval_basic(app* e);
    void eval_eq(app* e, expr* arg1, expr* arg2);
    void eval_array_eq(app* e, expr* arg1, expr* arg2);
    void inherit_value(expr* e, expr* v);

    bool is_unknown(expr* x)  { return !m1.is_marked(x) && !m2.is_marked(x); }
    void set_unknown(expr* x)  { m1.mark(x, false); m2.mark(x, false); }
    bool is_x(expr* x)  { return !m1.is_marked(x) && m2.is_marked(x); }
    bool is_false(expr* x)  { return m1.is_marked(x) && !m2.is_marked(x); }
    bool is_true(expr* x)  { return m1.is_marked(x) && m2.is_marked(x); }
    void set_x(expr* x) { SASSERT(is_unknown(x)); m2.mark(x); }
    void set_v(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    void set_false(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); }
    void set_true(expr* x) { SASSERT(is_unknown(x)); m1.mark(x); m2.mark(x); }
    void set_bool(expr* x, bool v) { if(v) { set_true(x); } else { set_false(x); } }
    rational const& get_number(expr* x) const { return m_numbers.find(x); }
    void set_number(expr* x, rational const& v)
    {
        set_v(x);
        m_numbers.insert(x, v);
        TRACE("spacer_verbose", tout << mk_pp(x, m) << " " << v << "\n";);
    }
    expr* get_value(expr* x) { return m_values.find(x); }
    void set_value(expr* x, expr* v)
    { set_v(x); m_refs.push_back(v); m_values.insert(x, v); }


    /// evaluates all sub-formulas and terms of the input in the current model.
    /// Caches the result
    void eval_fmls(ptr_vector<expr> const & formulas);

    /// calls eval_fmls(). Then checks whether all formulas are
    /// TRUE. Returns false if at lest one formula is unknown (X)
    bool check_model(ptr_vector<expr> const & formulas);

    bool extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores,
                                   expr_ref& else_case);

    void eval_exprs(expr_ref_vector& es);

public:
    model_evaluator(ast_manager& m) : m(m), m_arith(m), m_array(m), m_refs(m) {}


    /**
       \brief extract literals from formulas that satisfy formulas.

       \pre model satisfies formulas
    */
    void minimize_literals(ptr_vector<expr> const & formulas, const model_ref& mdl,
                           expr_ref_vector& result);

    expr_ref eval_heavy(const model_ref& mdl, expr* fml);

    expr_ref eval(const model_ref& mdl, expr* e);
    expr_ref eval(const model_ref& mdl, func_decl* d);
};
}



#endif /* OLD_MEV_H */
