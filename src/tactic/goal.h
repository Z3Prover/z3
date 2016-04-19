/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal.h

Abstract:

    A goal is essentially a set of formulas. Tactics are used to build 
    proof and model finding procedures for these sets.
    
    Remark: In a previous version of Z3, goals were called assertion_sets.
    Here is a summary of the main changes:
       - Goals track whether they are the result of applying over/under approximation steps.
         This prevent users from creating unsound strategies (e.g., user uses nia2sat, but does not check the sat_preserving flag).
       - Goals track dependencies (aka light proofs) for unsat core extraction, and building multi-tier solvers.
         This kind of dependency tracking is more powerful than the one used in the current Z3, since
         it does not prevent the use of preprocessing steps such as "Gaussian Elimination".
    
Author:

    Leonardo de Moura (leonardo) 2011-10-12

Revision History:

--*/
#ifndef GOAL_H_
#define GOAL_H_

#include"ast.h"
#include"ast_translation.h"
#include"ast_printer.h"
#include"for_each_expr.h"
#include"ref.h"
#include"ref_vector.h"
#include"ref_buffer.h"

class goal {
public:
    enum precision {
        PRECISE,      
        UNDER,   // goal is the product of an under-approximation 
        OVER,    // goal is the product of an over-approximation
        UNDER_OVER // goal is garbage: the produce of combined under and over approximation steps.
    };

    static precision mk_union(precision p1, precision p2);
    
protected:
    ast_manager &         m_manager;
    unsigned              m_ref_count;
    expr_array            m_forms;
    expr_array            m_proofs;
    expr_dependency_array m_dependencies;
    // attributes
    unsigned              m_depth:26;          // depth of the goal in the goal tree.
    unsigned              m_models_enabled:1;  // model generation is enabled.
    unsigned              m_proofs_enabled:1;  // proof production is enabled. m_manager.proofs_enabled() must be true if m_proofs_enabled == true
    unsigned              m_core_enabled:1;    // unsat core extraction is enabled.
    unsigned              m_inconsistent:1;    // true if the goal is known to be inconsistent. 
    unsigned              m_precision:2;       // PRECISE, UNDER, OVER.

    void push_back(expr * f, proof * pr, expr_dependency * d);
    void quick_process(bool save_first, expr_ref & f, expr_dependency * d);
    void process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(expr * f, proof * pr, expr_dependency * d);
    unsigned get_idx(expr * f) const;
    unsigned get_not_idx(expr * f) const;
    void shrink(unsigned j);
    void reset_core();
    
public:
    goal(ast_manager & m, bool models_enabled = true, bool core_enabled = false);
    goal(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled);
    goal(goal const & src);
    // Copy configuration: depth, models/proofs/cores flags, and precision from src.
    // The assertions are not copied
    goal(goal const & src, bool);
    ~goal();

    void inc_ref() { ++m_ref_count; }
    void dec_ref() { --m_ref_count; if (m_ref_count == 0) dealloc(this); }

    ast_manager & m() const { return m_manager; }

    unsigned depth() const { return m_depth; }
    bool models_enabled() const { return m_models_enabled; }
    bool proofs_enabled() const { return m_proofs_enabled; }
    bool unsat_core_enabled() const { return m_core_enabled; }
    bool inconsistent() const { return m_inconsistent; }
    precision prec() const { return static_cast<precision>(m_precision); }
    
    void set_depth(unsigned d) { m_depth = d; }
    void inc_depth() { m_depth++; }
    void set_prec(precision d) { m_precision = d; }
    void updt_prec(precision d) { m_precision = mk_union(prec(), d); }

    void reset_all(); // reset goal and precision and depth attributes.
    void reset(); // reset goal but preserve precision and depth attributes.

    void copy_to(goal & target) const;
    void copy_from(goal const & src) { src.copy_to(*this); }
    
    void assert_expr(expr * f, proof * pr, expr_dependency * d);
    void assert_expr(expr * f, expr_dependency * d);
    void assert_expr(expr * f, expr * d) { assert_expr(f, m().mk_leaf(d)); }
    void assert_expr(expr * f) { assert_expr(f, static_cast<expr_dependency*>(0)); }
    
    unsigned size() const { return m().size(m_forms); }

    unsigned num_exprs() const;
  
    expr * form(unsigned i) const { return m().get(m_forms, i); }
    proof * pr(unsigned i) const { return proofs_enabled() ? static_cast<proof*>(m().get(m_proofs, i)) : 0; }
    expr_dependency * dep(unsigned i) const { return unsat_core_enabled() ? m().get(m_dependencies, i) : 0; }

    void update(unsigned i, expr * f, proof * pr = 0, expr_dependency * dep = 0);

    void get_formulas(ptr_vector<expr> & result);
    
    void elim_true();
    void elim_redundancies();

    void display(ast_printer & prn, std::ostream & out) const;
    void display(ast_printer_context & ctx) const;
    void display(std::ostream & out) const;
    void display_ll(std::ostream & out) const;
    void display_as_and(std::ostream & out) const;
    void display_dimacs(std::ostream & out) const;
    void display_with_dependencies(ast_printer & prn, std::ostream & out) const;
    void display_with_dependencies(ast_printer_context & ctx) const;
    void display_with_dependencies(std::ostream & out) const;

    bool sat_preserved() const;
    bool unsat_preserved() const;
    bool is_decided_sat() const;
    bool is_decided_unsat() const;
    bool is_decided() const;
    bool is_well_sorted() const;

    goal * translate(ast_translation & translator) const;
};

std::ostream & operator<<(std::ostream & out, goal::precision p);

typedef ref<goal> goal_ref;
typedef sref_vector<goal> goal_ref_vector;
typedef sref_buffer<goal> goal_ref_buffer;

template<typename GoalCollection>
inline bool is_decided(GoalCollection const & c) { return c.size() == 1 && c[0]->is_decided(); }
template<typename GoalCollection>
inline bool is_decided_sat(GoalCollection const & c) { return c.size() == 1 && c[0]->is_decided_sat(); }
template<typename GoalCollection>
inline bool is_decided_unsat(GoalCollection const & c) { return c.size() == 1 && c[0]->is_decided_unsat(); }

template<typename ForEachProc>
void for_each_expr_at(ForEachProc& proc, goal const & s) {
    expr_mark visited;
    for (unsigned i = 0; i < s.size(); ++i) {
        for_each_expr(proc, visited, s.form(i));
    }
}

bool is_equal(goal const & g1, goal const & g2);

template<typename Predicate>
bool test(goal const & g, Predicate & proc) {
    expr_fast_mark1 visited;
    try {
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++)
            quick_for_each_expr(proc, visited, g.form(i));
    }
    catch (typename Predicate::found) {
        return true;
    }
    return false;
}

template<typename Predicate>
bool test(goal const & g) {
    Predicate proc(g.m());
    return test(g, proc);
}

#endif
