/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_solver.h

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/arith_decl_plugin.h"
#include "math/lp/lp_solver.h"
#include "math/lp/lp_primal_simplex.h"
#include "math/lp/lp_dual_simplex.h"
#include "math/lp/indexed_value.h"
#include "math/lp/lar_solver.h"
#include "math/lp/nla_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/lp_api.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace arith {

    typedef ptr_vector<lp_api::bound<sat::literal>> lp_bounds;
    typedef lp::var_index lpvar;
    typedef euf::theory_var theory_var;
    typedef euf::theory_id theory_id;
    typedef euf::enode enode;
    typedef euf::enode_pair enode_pair;
    typedef sat::literal literal;
    typedef sat::bool_var bool_var;
    typedef sat::literal_vector literal_vector;
    typedef lp_api::bound<sat::literal> api_bound;

    class solver : public euf::th_euf_solver {

        struct scope {
            unsigned m_bounds_lim;
            unsigned m_idiv_lim;
            unsigned m_asserted_qhead;
            unsigned m_asserted_lim;
            unsigned m_underspecified_lim;
            expr* m_not_handled;
        };

        class resource_limit : public lp::lp_resource_limit {
            solver& m_imp;
        public:
            resource_limit(solver& i) : m_imp(i) { }
            bool get_cancel_flag() override { return !m_imp.m.inc(); }
        };

        struct var_value_eq {
            solver& m_th;
            var_value_eq(solver& th) :m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const {
                if (m_th.is_int(v1) != m_th.is_int(v2)) {
                    return false;
                }
                return m_th.is_eq(v1, v2);
            }
        };

        struct var_value_hash {
            solver& m_th;
            var_value_hash(solver& th) :m_th(th) {}
            unsigned operator()(theory_var v) const {
                if (m_th.use_nra_model()) {
                    return m_th.is_int(v);
                }
                else {
                    return (unsigned)std::hash<lp::impq>()(m_th.get_ivalue(v));
                }
            }
        };
        int_hashtable<var_value_hash, var_value_eq>   m_model_eqs;

        bool                m_new_eq { false };


        // temporary values kept during internalization
        struct internalize_state {
            expr_ref_vector     m_terms;
            vector<rational>    m_coeffs;
            svector<theory_var> m_vars;
            rational            m_offset;
            ptr_vector<expr>    m_to_ensure_enode, m_to_ensure_var;
            internalize_state(ast_manager& m) : m_terms(m) {}
            void reset() {
                m_terms.reset();
                m_coeffs.reset();
                m_offset.reset();
                m_vars.reset();
                m_to_ensure_enode.reset();
                m_to_ensure_var.reset();
            }
        };
        scoped_ptr_vector<internalize_state> m_internalize_states;
        unsigned                      m_internalize_head = 0;

        class scoped_internalize_state {
            solver& m_imp;
            internalize_state& m_st;

            internalize_state& push_internalize(solver& i) {
                if (i.m_internalize_head == i.m_internalize_states.size()) {
                    i.m_internalize_states.push_back(alloc(internalize_state, i.m));
                }
                internalize_state& st = *i.m_internalize_states[i.m_internalize_head++];
                st.reset();
                return st;
            }
        public:
            scoped_internalize_state(solver& i) : m_imp(i), m_st(push_internalize(i)) {}
            ~scoped_internalize_state() { --m_imp.m_internalize_head; }
            expr_ref_vector& terms() { return m_st.m_terms; }
            vector<rational>& coeffs() { return m_st.m_coeffs; }
            svector<theory_var>& vars() { return m_st.m_vars; }
            rational& offset() { return m_st.m_offset; }
            ptr_vector<expr>& to_ensure_enode() { return m_st.m_to_ensure_enode; }
            ptr_vector<expr>& to_ensure_var() { return m_st.m_to_ensure_var; }
            void push(expr* e, rational c) { m_st.m_terms.push_back(e); m_st.m_coeffs.push_back(c); }
            void set_back(unsigned i) {
                if (terms().size() == i + 1) return;
                terms()[i] = terms().back();
                coeffs()[i] = coeffs().back();
                terms().pop_back();
                coeffs().pop_back();
            }
        };

        typedef vector<std::pair<rational, lpvar>> var_coeffs;
        vector<rational>         m_columns;
        var_coeffs               m_left_side;              // constraint left side

        lpvar m_one_var   = UINT_MAX;
        lpvar m_zero_var  = UINT_MAX;
        lpvar m_rone_var  = UINT_MAX;
        lpvar m_rzero_var = UINT_MAX;

        enum constraint_source {
            inequality_source,
            equality_source,
            definition_source,
            null_source
        };
        svector<constraint_source>                    m_constraint_sources;
        svector<literal>                              m_inequalities;    // asserted rows corresponding to inequality literals.
        svector<euf::enode_pair>                      m_equalities;      // asserted rows corresponding to equalities.
        svector<theory_var>                           m_definitions;     // asserted rows corresponding to definitions
        svector<std::pair<euf::th_eq, bool>>          m_delayed_eqs;

        literal_vector  m_asserted;
        expr* m_not_handled{ nullptr };
        ptr_vector<app>        m_underspecified;
        ptr_vector<expr>       m_idiv_terms;
        vector<ptr_vector<api_bound> > m_use_list;        // bounds where variables are used.

        // attributes for incremental version:
        u_map<api_bound*>      m_bool_var2bound;
        vector<lp_bounds>      m_bounds;
        unsigned_vector        m_unassigned_bounds;
        unsigned_vector        m_bounds_trail;
        unsigned               m_asserted_qhead = 0;

        svector<std::pair<theory_var, theory_var> >       m_assume_eq_candidates;
        unsigned                                          m_assume_eq_head{ 0 };
        lp::u_set                                         m_tmp_var_set;

        unsigned                                          m_num_conflicts{ 0 };
        lp_api::stats                                     m_stats;
        svector<scope>                                    m_scopes;

        // non-linear arithmetic
        scoped_ptr<nla::solver>  m_nla;
        scoped_ptr<scoped_anum>  m_a1, m_a2;

        // integer arithmetic
        scoped_ptr<lp::int_solver>   m_lia;


        scoped_ptr<lp::lar_solver>   m_solver;
        resource_limit               m_resource_limit;
        lp_bounds                    m_new_bounds;
        symbol                       m_farkas;
        lp::lp_bound_propagator<solver> m_bp;
        mutable vector<std::pair<lp::tv, rational>> m_todo_terms;

        // lemmas
        lp::explanation     m_explanation;
        vector<nla::lemma>  m_nla_lemma_vector;
        literal_vector      m_core, m_core2;
        svector<enode_pair> m_eqs;
        vector<parameter>   m_params;
        nla::lemma          m_lemma;
        arith_util          a;

        bool is_int(theory_var v) const { return is_int(var2enode(v)); }
        bool is_int(euf::enode* n) const { return a.is_int(n->get_expr()); }
        bool is_real(theory_var v) const { return is_real(var2enode(v)); }
        bool is_real(euf::enode* n) const { return a.is_real(n->get_expr()); }
        bool is_bool(theory_var v) const { return is_bool(var2enode(v)); }
        bool is_bool(euf::enode* n) const { return m.is_bool(n->get_expr()); }
        

        // internalize
        bool m_internalize_initialized { false };
        void init_internalize();
        lpvar add_const(int c, lpvar& var, bool is_int);
        lpvar get_one(bool is_int);
        lpvar get_zero(bool is_int);
        void ensure_nla();
        void found_unsupported(expr* n);
        void found_underspecified(expr* n);

        void linearize_term(expr* term, scoped_internalize_state& st);
        void linearize_ineq(expr* lhs, expr* rhs, scoped_internalize_state& st);
        void linearize(scoped_internalize_state& st);

        void add_eq_constraint(lp::constraint_index index, enode* n1, enode* n2);
        void add_ineq_constraint(lp::constraint_index index, literal lit);
        void add_def_constraint(lp::constraint_index index);
        void add_def_constraint(lp::constraint_index index, theory_var v);
        void add_def_constraint_and_equality(lpvar vi, lp::lconstraint_kind kind, const rational& bound);
        void internalize_args(app* t, bool force = false);
        theory_var internalize_power(app* t, app* n, unsigned p);
        theory_var internalize_mul(app* t);
        theory_var internalize_def(expr* term);
        theory_var internalize_def(expr* term, scoped_internalize_state& st);
        theory_var internalize_linearized_def(expr* term, scoped_internalize_state& st);
        void init_left_side(scoped_internalize_state& st);
        bool internalize_term(expr* term);
        bool internalize_atom(expr* atom);
        bool is_unit_var(scoped_internalize_state& st);
        bool is_one(scoped_internalize_state& st);
        bool is_zero(scoped_internalize_state& st);
        enode* mk_enode(expr* e);

        lpvar register_theory_var_in_lar_solver(theory_var v);
        theory_var mk_evar(expr* e);
        bool has_var(expr* e);
        bool reflect(expr* n) const;

        lpvar get_lpvar(theory_var v) const;
        lp::tv get_tv(theory_var v) const;

        // axioms
        void mk_div_axiom(expr* p, expr* q);
        void mk_to_int_axiom(app* n);
        void mk_is_int_axiom(expr* n);
        void mk_idiv_mod_axioms(expr* p, expr* q);
        void mk_rem_axiom(expr* dividend, expr* divisor);
        void mk_bound_axioms(api_bound& b);
        void mk_bound_axiom(api_bound& b1, api_bound& b2);
        void mk_power0_axioms(app* t, app* n);
        void flush_bound_axioms();

        // bounds
        struct compare_bounds {
            bool operator()(api_bound* a1, api_bound* a2) const { return a1->get_value() < a2->get_value(); }
        };

        typedef lp_bounds::iterator iterator;

        lp_bounds::iterator first(
            lp_api::bound_kind kind,
            iterator it,
            iterator end);

        lp_bounds::iterator next_inf(
            api_bound* a1,
            lp_api::bound_kind kind,
            iterator it,
            iterator end,
            bool& found_compatible);

        lp_bounds::iterator next_sup(
            api_bound* a1,
            lp_api::bound_kind kind,
            iterator it,
            iterator end,
            bool& found_compatible);

        void propagate_eqs(lp::tv t, lp::constraint_index ci, lp::lconstraint_kind k, api_bound& b, rational const& value);
        void propagate_basic_bounds(unsigned qhead);
        void propagate_bounds_with_lp_solver();
        void propagate_bound(literal lit, api_bound& b);
        void propagate_lp_solver_bound(const lp::implied_bound& be);
        void refine_bound(theory_var v, const lp::implied_bound& be);
        literal is_bound_implied(lp::lconstraint_kind k, rational const& value, api_bound const& b) const;
        void assert_bound(bool is_true, api_bound& b);
        void mk_eq_axiom(bool is_eq, euf::th_eq const& eq);
        void mk_diseq_axiom(euf::th_eq const& eq);
        void assert_idiv_mod_axioms(theory_var u, theory_var v, theory_var w, rational const& r);
        api_bound* mk_var_bound(sat::literal lit, theory_var v, lp_api::bound_kind bk, rational const& bound);
        lp::lconstraint_kind bound2constraint_kind(bool is_int, lp_api::bound_kind bk, bool is_true);
        void fixed_var_eh(theory_var v1, lp::constraint_index ci1, lp::constraint_index ci2, rational const& bound);
        bool set_upper_bound(lp::tv t, lp::constraint_index ci, rational const& v) { return set_bound(t, ci, v, false); }
        bool set_lower_bound(lp::tv t, lp::constraint_index ci, rational const& v) { return set_bound(t, ci, v, true); }
        bool set_bound(lp::tv tv, lp::constraint_index ci, rational const& v, bool is_lower);

        typedef std::pair<lp::constraint_index, rational> constraint_bound;
        vector<constraint_bound>        m_lower_terms;
        vector<constraint_bound>        m_upper_terms;
        vector<constraint_bound>        m_history;

        bool can_get_value(theory_var v) const {
            return is_registered_var(v) && m_model_is_initialized;
        }

        vector<rational>     m_fixed_values;
        map<rational, theory_var, rational::hash_proc, rational::eq_proc> m_value2var;
        struct undo_value;
        void register_fixed_var(theory_var v, rational const& value);

        // solving
        void report_equality_of_fixed_vars(unsigned vi1, unsigned vi2);
        void reserve_bounds(theory_var v);

        void updt_unassigned_bounds(theory_var v, int inc);

        void pop_core(unsigned n) override;
        void push_core() override;
        void del_bounds(unsigned old_size);

        bool all_zeros(vector<rational> const& v) const;

        bound_prop_mode propagation_mode() const;

        bool is_registered_var(theory_var v) const;
        void ensure_column(theory_var v);
        lp::impq get_ivalue(theory_var v) const;
        rational get_value(theory_var v) const;

        void random_update();
        bool assume_eqs();
        bool delayed_assume_eqs();
        bool is_eq(theory_var v1, theory_var v2);
        bool use_nra_model();

        lbool make_feasible();
        bool  check_delayed_eqs();
        lbool check_lia();
        lbool check_nla();
        bool is_infeasible() const;

        nlsat::anum const& nl_value(theory_var v, scoped_anum& r) const;


        bool has_bound(lpvar vi, lp::constraint_index& ci, rational const& bound, bool is_lower);
        bool has_lower_bound(lpvar vi, lp::constraint_index& ci, rational const& bound);
        bool has_upper_bound(lpvar vi, lp::constraint_index& ci, rational const& bound);

        /*
         * Facility to put a small box around integer variables used in branch and bounds.
         */

        struct bound_info {
            rational m_offset;
            unsigned m_range;
            bound_info() {}
            bound_info(rational const& o, unsigned r) :m_offset(o), m_range(r) {}
        };
        unsigned                  m_bounded_range_idx;  // current size of bounded range.
        literal                   m_bounded_range_lit;  // current bounded range literal
        expr_ref_vector           m_bound_terms; // predicates used for bounds
        expr_ref                  m_bound_predicate;

        obj_map<expr, expr*>      m_predicate2term;
        obj_map<expr, bound_info> m_term2bound_info;
        bool                      m_model_is_initialized = false;

        unsigned small_lemma_size() const { return get_config().m_arith_small_lemma_size; }
        bool propagate_eqs() const { return get_config().m_arith_propagate_eqs && m_num_conflicts < get_config().m_arith_propagation_threshold; }
        bool should_propagate() const { return bound_prop_mode::BP_NONE != propagation_mode(); }
        bool should_refine_bounds() const { return bound_prop_mode::BP_REFINE == propagation_mode() && s().at_search_lvl(); }

        unsigned init_range() const { return 5; }
        unsigned max_range() const { return 20; }

        void reset_evidence();
        bool check_idiv_bounds();
        bool is_bounded(expr* n);

        app_ref mk_bound(lp::lar_term const& term, rational const& k, bool lower_bound);
        app_ref mk_bound(lp::lar_term const& term, rational const& k, bool lower_bound, rational& offset, expr_ref& t);
        literal mk_eq(lp::lar_term const& term, rational const& offset);

        rational gcd_reduce(u_map<rational>& coeffs);
        app_ref mk_term(lp::lar_term const& term, bool is_int);
        app_ref coeffs2app(u_map<rational> const& coeffs, rational const& offset, bool is_int);
        void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs, rational const& coeff);
        void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs);

        void get_infeasibility_explanation_and_set_conflict();
        void set_conflict();
        void set_conflict_or_lemma(literal_vector const& core, bool is_conflict);
        void set_evidence(lp::constraint_index idx, literal_vector& core, svector<enode_pair>& eqs);
        void assign(literal lit, literal_vector const& core, svector<enode_pair> const& eqs, vector<parameter> const& params);

        void false_case_of_check_nla(const nla::lemma& l);        
        void dbg_finalize_model(model& mdl);

    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override;
        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override;
        void asserted(literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool use_diseqs() const override { return true; }
        void new_eq_eh(euf::th_eq const& eq) override;
        void new_diseq_eh(euf::th_eq const& de) override;
        bool unit_propagate() override;
        void init_model() override;
        void finalize_model(model& mdl) override { DEBUG_CODE(dbg_finalize_model(mdl);); }
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        void eq_internalized(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override {}
        bool is_shared(theory_var v) const override;
        lbool get_phase(bool_var v) override;
        bool include_func_interp(func_decl* f) const override;

        // bounds and equality propagation callbacks
        lp::lar_solver& lp() { return *m_solver; }
        lp::lar_solver const& lp() const { return *m_solver; }
        bool is_equal(theory_var x, theory_var y) const;
        void add_eq(lpvar u, lpvar v, lp::explanation const& e);
        void consume(rational const& v, lp::constraint_index j);
        bool bound_is_interesting(unsigned vi, lp::lconstraint_kind kind, const rational& bval) const;
    };
}
