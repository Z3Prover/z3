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

#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"
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

namespace euf {
    class solver;
}

namespace arith {

    typedef ptr_vector<lp_api::bound> lp_bounds;
    typedef lp::var_index lpvar;
    typedef euf::theory_var theory_var;
    typedef euf::theory_id theory_id;
    typedef euf::enode enode;
    typedef euf::enode_pair enode_pair;
    typedef sat::literal literal;
    typedef sat::bool_var bool_var;
    typedef sat::literal_vector literal_vector;

    class solver : public euf::th_euf_solver {

        struct scope {
            unsigned m_bounds_lim;
            unsigned m_idiv_lim;
            unsigned m_asserted_qhead;
            unsigned m_asserted_atoms_lim;
            unsigned m_underspecified_lim;
            expr* m_not_handled;
        };

        struct delayed_atom {
            unsigned m_bv;
            bool     m_is_true;
            delayed_atom(unsigned b, bool t) : m_bv(b), m_is_true(t) {}
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



        vector<rational>             m_columns;


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
        ptr_vector<internalize_state> m_internalize_states;
        unsigned                      m_internalize_head;

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

        var_coeffs               m_left_side;              // constraint left side
        mutable std::unordered_map<lpvar, rational> m_variable_values; // current model
        lpvar m_one_var   { UINT_MAX };
        lpvar m_zero_var  { UINT_MAX };
        lpvar m_rone_var  { UINT_MAX };
        lpvar m_rzero_var { UINT_MAX };

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

        svector<delayed_atom>  m_asserted_atoms;
        expr* m_not_handled{ nullptr };
        ptr_vector<app>        m_underspecified;
        ptr_vector<expr>       m_idiv_terms;
        vector<ptr_vector<lp_api::bound> > m_use_list;        // bounds where variables are used.

        // attributes for incremental version:
        u_map<lp_api::bound*>      m_bool_var2bound;
        vector<lp_bounds>      m_bounds;
        unsigned_vector        m_unassigned_bounds;
        unsigned_vector        m_bounds_trail;
        unsigned               m_asserted_qhead{ 0 };

        svector<unsigned>       m_to_check;    // rows that should be checked for theory propagation

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
        literal_vector      m_core;
        svector<enode_pair> m_eqs;
        vector<parameter>   m_params;

        arith_util        a;



        lp::lar_solver& lp() { return *m_solver; }
        lp::lar_solver const& lp() const { return *m_solver; }

        bool is_int(theory_var v) const { return is_int(var2enode(v)); }
        bool is_int(euf::enode* n) const { return a.is_int(n->get_expr()); }
        bool is_real(theory_var v) const { return is_real(var2enode(v)); }
        bool is_real(euf::enode* n) const { return a.is_real(n->get_expr()); }
        

        // internalize
        lpvar add_const(int c, lpvar& var, bool is_int);
        lpvar get_one(bool is_int);
        lpvar get_zero(bool is_int);
        void ensure_nla();
        void found_unsupported(expr* n);
        void found_underspecified(expr* n);
        bool is_numeral(expr* term, rational& r);
        bool is_underspecified(app* n) const;

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
        enode* mk_enode(app* e);

        lpvar register_theory_var_in_lar_solver(theory_var v);
        theory_var mk_var(expr* e);
        bool has_var(expr* e);
        bool reflect(app* n) const;
        void ensure_var(euf::enode* n);

        lpvar get_lpvar(theory_var v) const;
        lp::tv get_tv(theory_var v) const;

        // axioms
        void mk_div_axiom(expr* p, expr* q);
        void mk_to_int_axiom(app* n);
        void mk_is_int_axiom(expr* n);
        void mk_idiv_mod_axioms(expr* p, expr* q);
        void mk_rem_axiom(expr* dividend, expr* divisor);
        void mk_bound_axioms(lp_api::bound& b);
        void mk_bound_axiom(lp_api::bound& b1, lp_api::bound& b2);
        void mk_eq_axiom(theory_var v1, theory_var v2);
        void assert_idiv_mod_axioms(theory_var u, theory_var v, theory_var w, rational const& r);
        lp_api::bound* mk_var_bound(bool_var bv, theory_var v, lp_api::bound_kind bk, rational const& bound);
        lp::lconstraint_kind bound2constraint_kind(bool is_int, lp_api::bound_kind bk, bool is_true);
        

        // solving
        void report_equality_of_fixed_vars(unsigned vi1, unsigned vi2);
        void reserve_bounds(theory_var v);

        void updt_unassigned_bounds(theory_var v, int inc);

        void pop_core(unsigned n) override;
        void push_core() override;
        void del_bounds(unsigned old_size);

        bool all_zeros(vector<rational> const& v) const;

        bound_prop_mode propagation_mode() const;
        void init_variable_values();
        void reset_variable_values();

        bool can_get_value(theory_var v) const;
        bool can_get_bound(theory_var v) const;
        bool can_get_ivalue(theory_var v) const;
        void ensure_column(theory_var v);
        lp::impq get_ivalue(theory_var v) const;
        rational get_value(theory_var v) const;

        void random_update();
        bool assume_eqs();
        bool delayed_assume_eqs();
        bool is_eq(theory_var v1, theory_var v2);
        bool use_nra_model();
        bool has_delayed_constraints() const;

        lbool make_feasible();
        lbool check_lia();
        lbool check_nla();
        void add_variable_bound(expr* t, rational const& offset);
        bool is_infeasible() const;

        nlsat::anum const& nl_value(theory_var v, scoped_anum& r);


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

        bool use_bounded_expansion() const {
            return get_config().m_arith_bounded_expansion;
        }

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


        nla::lemma m_lemma;
        void false_case_of_check_nla(const nla::lemma& l);


    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override;
        bool is_external(bool_var v) override { return false; }
        bool propagate(literal l, sat::ext_constraint_idx idx) override { UNREACHABLE(); return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(sat::solver* s, euf::solver& ctx) override;
        bool use_diseqs() const override { return true; }
        void new_eq_eh(euf::th_eq const& eq) override { mk_eq_axiom(eq.v1(), eq.v2()); }
        void new_diseq_eh(euf::th_eq const& de) override { mk_eq_axiom(de.v1(), de.v2()); }
        bool unit_propagate() override;
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        void add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override {}
        bool is_shared(theory_var v) const override;
        lbool get_phase(bool_var v) override;
    };
}
