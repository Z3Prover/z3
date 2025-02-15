/**++
Copyright (c) Arie Gurfinkel

Module Name:

    mbp_term_graph.h

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel
    Hari Govind V K (hgvk94)
    Isabel Garcia (igcontreras)

Revision History:

    Added implementation of qe_lite using term graph

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/expr_functors.h"
#include "ast/is_variable_test.h"
#include "model/model.h"
#include "qe/mbp/mbp_solve_plugin.h"
#include "util/plugin_manager.h"

namespace mbp {
    namespace is_ground_ns {
        struct proc;
        struct found;
    } // namespace is_ground_ns
class term;

class term_graph {
    class projector;
    friend struct is_ground_ns::proc;
    friend struct is_ground_ns::found;

    class is_variable_proc : public ::is_variable_proc {
        bool m_exclude;
        obj_hashtable<func_decl> m_decls, m_solved;

    public:
        bool operator()(const expr *e) const override;
        bool operator()(const term &t) const;

        void set_decls(const func_decl_ref_vector &decls, bool exclude);
        void set_decls(const app_ref_vector &vars, bool exclude);
        void add_decls(const app_ref_vector &vars);
        void add_decl(app *var);
        void mark_solved(const expr *e);
        void reset_solved() { m_solved.reset(); }
        void reset() {
            m_decls.reset();
            m_solved.reset();
            m_exclude = true;
        }
        bool contains(func_decl *f) { return m_decls.contains(f) == m_exclude; }
    };

    class is_non_core : public i_expr_pred {
        std::function<bool(expr *)> *m_non_core;

    public:
        is_non_core(std::function<bool(expr *)> *nc) : m_non_core(nc) {}
        bool operator()(expr *n) override {
            if (m_non_core == nullptr) return false;
            return (*m_non_core)(n);
        }
    };

    struct term_hash {
        unsigned operator()(term const *t) const;
    };
    struct term_eq {
        bool operator()(term const *a, term const *b) const;
    };
    ast_manager &           m;
    ptr_vector<term>        m_terms;
    expr_ref_vector         m_lits;
    u_map<term*>            m_app2term;
    ast_ref_vector          m_pinned;
    projector *             m_projector = nullptr;
    bool                    m_explicit_eq = false;
    bool                    m_repick_repr = false;
    u_map<expr *>           m_term2app; // any representative change invalidates this cache
    plugin_manager<solve_plugin> m_plugins;
    ptr_hashtable<term, term_hash, term_eq> m_cg_table;
    vector<std::pair<term *, term *>> m_merge;

    term_graph::is_variable_proc m_is_var;

    void merge(term &t1, term &t2);
    void merge_flush();

    term *mk_term(expr *t);
    term *get_term(expr *t);
    term *get_term(func_decl *f);

    term *internalize_term(expr *t);
    void internalize_eq(expr *a1, expr *a2);
    void internalize_lit(expr *lit);
    void internalize_distinct(expr *d);
    void internalize_deq(expr *a1, expr *a2);

    bool is_internalized(expr *a);
    bool is_ground(expr *e);

    bool term_lt(term const &t1, term const &t2);
    void pick_repr_percolate_up(ptr_vector<term> &todo);
    void pick_repr_class(term *t);
    void pick_repr();

    void reset_marks();
    void reset_marks2();
    bool marks_are_clear();

    expr *mk_app_core(expr *a);
    expr_ref mk_app(term &t);
    expr *mk_pure(term &t);
    expr_ref mk_app(expr *a);
    void mk_equalities(term &t, expr_ref_vector &out);
    void mk_all_equalities(term &t, expr_ref_vector &out);
    void mk_qe_lite_equalities(term &t, expr_ref_vector &out,
                               check_pred &not_in_core);
    void display(std::ostream &out);

    bool is_pure_def(expr *atom, expr *&v);
    void cground_percolate_up(ptr_vector<term> &);
    void cground_percolate_up(term *t);
    void compute_cground();

public:
    term_graph(ast_manager &m);
    ~term_graph();

    const expr_ref_vector &get_lits() const { return m_lits; }
    void get_terms(expr_ref_vector &res, bool exclude_cground = true);
    bool is_cgr(expr *e);
    unsigned size() { return m_terms.size(); }

    void set_vars(func_decl_ref_vector const &decls, bool exclude = true);
    void set_vars(app_ref_vector const &vars, bool exclude = true);
    void add_vars(app_ref_vector const &vars);
    void add_var(app *var);

    ast_manager &get_ast_manager() const { return m; }

    void add_lit(expr *lit);
    void add_lits(expr_ref_vector const &lits) {
        for (expr *e : lits) add_lit(e);
    }
    void add_eq(expr *a, expr *b) { internalize_eq(a, b); }
    void add_deq(expr *a, expr *b) { internalize_deq(a, b); }

    void reset();

    // deprecate?
    void to_lits(expr_ref_vector &lits, bool all_equalities = false,
                 bool repick_repr = true);
    void to_lits_qe_lite(expr_ref_vector &lits,
                         std::function<bool(expr *)> *non_core = nullptr);
    expr_ref to_expr(bool repick_repr = true);

    /**
     * Return literals obtained by projecting added literals
     * onto the vocabulary of decls (if exclude is false) or outside the
     * vocabulary of decls (if exclude is true).
     */
    expr_ref_vector project();
    expr_ref_vector solve();
    expr_ref_vector project(model &mdl);

    /**
     * Return disequalities to ensure that disequalities between
     * excluded functions are preserved.
     * For example if f(a) = b, f(c) = d, and b and d are not
     * congruent, then produce the disequality a != c.
     */
    expr_ref_vector get_ackerman_disequalities();

    /**
     * Produce model-based disequality
     * certificate corresponding to
     * definition in BGVS 2020.
     * A disequality certificate is a reduced set of
     * disequalities, true under mdl, such that the literals
     * can be satisfied when non-shared symbols are projected.
     */
    expr_ref_vector dcert(model &mdl, expr_ref_vector const &lits);

    /**
     * Produce a model-based partition.
     */
    vector<expr_ref_vector> get_partition(model &mdl);

    /**
     * Extract shared occurrences of terms whose sort are
     * fid, but appear in a context that is not fid.
     * for example f(x + y) produces the shared occurrence
     * x + y when f is uninterpreted and x + y has sort Int or Real.
     */
    expr_ref_vector shared_occurrences(family_id fid);

    /**
     * Map expression that occurs in added literals into representative if it
     * exists.
     */
    void add_model_based_terms(model &mdl, expr_ref_vector const &terms);
    expr *rep_of(expr *e);

    using deqs = bit_vector;
    struct add_deq_proc {        
        unsigned m_deq_cnt = 0;
        void inc_count();
        void operator()(term *t1, term *t2);
        void operator()(ptr_vector<term> &ts);
    };

    // -- disequalities added for output
    vector<std::pair<term *, term *>> m_deq_pairs;
    // -- maybe they are not necessary since they are in the original formula
    vector<ptr_vector<term>> m_deq_distinct;

    expr_ref_vector non_ground_terms();
    void gr_terms_to_lits(expr_ref_vector &lits, bool all_equalities);
    // produce a quantifier reduction of the formula stored in the term graph
    // output of qel will not contain expression e s.t. non_core(e) == true
    void qel(app_ref_vector &vars, expr_ref &fml,
             std::function<bool(expr *)> *non_core = nullptr);
    bool has_val_in_class(expr *e);
    app *get_const_in_class(expr *e);
    void set_explicit_eq() { m_explicit_eq = true; }

private:
    add_deq_proc m_add_deq;
    void refine_repr_class(term *t);
    void refine_repr();
    bool makes_cycle(term *t);
};

    namespace is_ground_ns {
        struct found {};
        struct proc {
            term_graph::is_variable_proc &m_is_var;
            proc(term_graph::is_variable_proc &is_var) : m_is_var(is_var) {}
            void operator()(var *n) const {}
            void operator()(app const *n) const {
                if (m_is_var.contains(n->get_decl())) throw found();
            }
            void operator()(quantifier *n) const {}
        };
    } // namespace is_ground_ns
} // namespace mbp
