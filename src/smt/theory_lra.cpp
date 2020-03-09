/*++
  Copyright (c) 2016 Microsoft Corporation

  Module Name:

  theory_lra.cpp

  Abstract:

  <abstract>

  Author:

  Lev Nachmanson (levnach) 2016-25-3
  Nikolaj Bjorner (nbjorner)

  Revision History:


  --*/
#include "util/stopwatch.h"
#include "math/lp/lp_solver.h"
#include "math/lp/lp_primal_simplex.h"
#include "math/lp/lp_dual_simplex.h"
#include "math/lp/indexed_value.h"
#include "math/lp/lar_solver.h"
#include "util/nat_set.h"
#include "util/optional.h"
#include "util/inf_rational.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "util/nat_set.h"
#include "ast/ast_pp.h"
#include "model/numeral_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "smt/theory_lra.h"
#include "smt/smt_model_generator.h"
#include "smt/arith_eq_adapter.h"
#include "util/nat_set.h"
#include "math/lp/nra_solver.h"
#include "tactic/generic_model_converter.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "ast/ast_pp.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "math/lp/nla_solver.h"

typedef lp::var_index lpvar;

namespace lp_api {
enum bound_kind { lower_t, upper_t };

std::ostream& operator<<(std::ostream& out, bound_kind const& k) {
    switch (k) {
    case lower_t: return out << "<=";
    case upper_t: return out << ">=";
    }
    return out;
}

class bound { 
    smt::bool_var    m_bv;
    smt::theory_var  m_var;
    lpvar            m_vi;
    bool             m_is_int;
    rational         m_value;
    bound_kind       m_bound_kind;
    lp::constraint_index m_constraints[2];

public:
    bound(smt::bool_var bv, smt::theory_var v, lpvar vi, bool is_int, rational const & val, bound_kind k, lp::constraint_index ct, lp::constraint_index cf):
        m_bv(bv),
        m_var(v),
        m_vi(vi),
        m_is_int(is_int),
        m_value(val),
        m_bound_kind(k) {
        m_constraints[0] = cf;
        m_constraints[1] = ct;
    }
    virtual ~bound() {}
    smt::theory_var get_var() const { return m_var; }
    lpvar lp_solver_var() const { return m_vi; }
    smt::bool_var get_bv() const { return m_bv; }
    bound_kind get_bound_kind() const { return m_bound_kind; }
    bool is_int() const { return m_is_int; }
    rational const& get_value() const { return m_value; }
    lp::constraint_index get_constraint(bool b) const { return m_constraints[b]; }
    inf_rational get_value(bool is_true) const { 
        if (is_true) return inf_rational(m_value);                         // v >= value or v <= value
        if (m_is_int) {
            SASSERT(m_value.is_int());
            if (m_bound_kind == lower_t) return inf_rational(m_value - rational::one()); // v <= value - 1
            return inf_rational(m_value + rational::one());                              // v >= value + 1
        }
        else {
            if (m_bound_kind == lower_t) return inf_rational(m_value, false);  // v <= value - epsilon
            return inf_rational(m_value, true);                                // v >= value + epsilon
        }
    } 
    virtual std::ostream& display(std::ostream& out) const {
        return out << m_value << "  " << get_bound_kind() << " v" << get_var();
    }
};

std::ostream& operator<<(std::ostream& out, bound const& b) {
    return b.display(out);
}

struct stats {
    unsigned m_assert_lower;
    unsigned m_assert_upper;
    unsigned m_add_rows;
    unsigned m_bounds_propagations;
    unsigned m_num_iterations;
    unsigned m_num_iterations_with_no_progress;
    unsigned m_need_to_solve_inf;
    unsigned m_fixed_eqs;
    unsigned m_conflicts;
    unsigned m_bound_propagations1;
    unsigned m_bound_propagations2;
    unsigned m_assert_diseq;
    unsigned m_gomory_cuts;
    unsigned m_nla_explanations;
    unsigned m_nla_lemmas;
    unsigned m_assume_eqs;
    unsigned m_branch;
    stats() { reset(); }
    void reset() {
        memset(this, 0, sizeof(*this));
    }
};

typedef optional<inf_rational> opt_inf_rational;


}

namespace smt {

typedef ptr_vector<lp_api::bound> lp_bounds;
    
class theory_lra::imp {        

    struct scope {
        unsigned m_bounds_lim;
        unsigned m_idiv_lim;
        unsigned m_asserted_qhead;            
        unsigned m_asserted_atoms_lim;
        unsigned m_underspecified_lim;
        expr*    m_not_handled;
    };

    struct delayed_atom {
        unsigned m_bv;
        bool     m_is_true;
        delayed_atom(unsigned b, bool t): m_bv(b), m_is_true(t) {}
    };

    class resource_limit : public lp::lp_resource_limit {
        imp& m_imp;
    public:
        resource_limit(imp& i): m_imp(i) { }
        bool get_cancel_flag() override { return m_imp.m.canceled(); }
    };


    theory_lra&          th;
    ast_manager&         m;
    theory_arith_params& m_arith_params;
    arith_util           a;
    arith_eq_adapter     m_arith_eq_adapter;
    vector<rational>     m_columns;
      

    // temporary values kept during internalization
    struct internalize_state {
        expr_ref_vector     m_terms;                     
        vector<rational>    m_coeffs;
        svector<theory_var> m_vars;
        rational            m_offset;
        ptr_vector<expr>    m_terms_to_internalize;
        internalize_state(ast_manager& m): m_terms(m) {}
        void reset() {
            m_terms.reset();
            m_coeffs.reset();
            m_offset.reset();
            m_vars.reset();
            m_terms_to_internalize.reset();
        }
    };
    ptr_vector<internalize_state> m_internalize_states;
    unsigned                      m_internalize_head;

    class scoped_internalize_state {
        imp& m_imp;
        internalize_state& m_st;

        internalize_state& push_internalize(imp& i) {
            if (i.m_internalize_head == i.m_internalize_states.size()) {
                i.m_internalize_states.push_back(alloc(internalize_state, i.m));
            }
            internalize_state& st = *i.m_internalize_states[i.m_internalize_head++];
            st.reset();
            return st;
        }
    public:
        scoped_internalize_state(imp& i): m_imp(i), m_st(push_internalize(i)) {}
        ~scoped_internalize_state() { --m_imp.m_internalize_head; }
        expr_ref_vector&     terms() { return m_st.m_terms; }                     
        vector<rational>&    coeffs() { return m_st.m_coeffs; }
        svector<theory_var>& vars() { return m_st.m_vars; }
        rational&            offset() { return m_st.m_offset; }
        ptr_vector<expr>&    terms_to_internalize() { return m_st.m_terms_to_internalize; }            
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
    lpvar m_one_var;
    lpvar m_zero_var;
    lpvar m_rone_var;
    lpvar m_rzero_var;

    enum constraint_source {
        inequality_source,
        equality_source,
        definition_source,
        null_source
    };
    svector<constraint_source>                    m_constraint_sources;
    svector<literal>                              m_inequalities;    // asserted rows corresponding to inequality literals.
    svector<enode_pair>                           m_equalities;      // asserted rows corresponding to equalities.
    svector<theory_var>                           m_definitions;     // asserted rows corresponding to definitions

    svector<delayed_atom>  m_asserted_atoms;        
    expr*                  m_not_handled;
    ptr_vector<app>        m_underspecified;
    ptr_vector<expr>       m_idiv_terms;
    vector<ptr_vector<lp_api::bound> > m_use_list;        // bounds where variables are used.

    // attributes for incremental version:
    u_map<lp_api::bound*>      m_bool_var2bound;
    vector<lp_bounds>      m_bounds;
    unsigned_vector        m_unassigned_bounds;
    unsigned_vector        m_bounds_trail;
    unsigned               m_asserted_qhead;

    svector<unsigned>       m_to_check;    // rows that should be checked for theory propagation

    svector<std::pair<theory_var, theory_var> >       m_assume_eq_candidates; 
    unsigned                                          m_assume_eq_head;

    unsigned                 m_num_conflicts;

    // non-linear arithmetic
    scoped_ptr<nra::solver>  m_nra;
    scoped_ptr<nla::solver>  m_nla;
    bool                     m_use_nra_model;
    scoped_ptr<scoped_anum>  m_a1, m_a2;

    struct switcher {
        theory_lra::imp& m_th_imp;
        scoped_ptr<nra::solver>*  m_nra;
        scoped_ptr<nla::solver>*  m_nla;
        bool                      m_use_nla;
        switcher(theory_lra::imp& i): m_th_imp(i), m_nra(nullptr), m_nla(nullptr) {
        }

        bool need_check() {
            if (m_use_nla) {
                if (m_nla != nullptr)
                    return (*m_nla)->need_check();
            }
            else {
                if (m_nra != nullptr)
                    return (*m_nra)->need_check();
            }
            return false;
        }
        
        void push() {
            if (m_nla != nullptr)
                (*m_nla)->push();
            if (m_nra != nullptr)
                (*m_nra)->push();
        }

        void pop(unsigned scopes) {
            if (m_nla != nullptr)
                (*m_nla)->pop(scopes);
            if (m_nra != nullptr)
                (*m_nra)->pop(scopes);
        }

        
        void add_monic(lpvar v, unsigned sz, lpvar const* vs) {
            if (m_use_nla) {
                m_th_imp.ensure_nla();
                (*m_nla)->add_monic(v, sz, vs);
            }
            else {
                m_th_imp.ensure_nra();
                (*m_nra)->add_monic(v, sz, vs);
            }
        }
 
    };

    // integer arithmetic
    scoped_ptr<lp::int_solver> m_lia;


    struct var_value_eq {
        imp & m_th;
        var_value_eq(imp & th):m_th(th) {}
        bool operator()(theory_var v1, theory_var v2) const { 
            if (m_th.is_int(v1) != m_th.is_int(v2)) {
                return false;
            }
            return m_th.is_eq(v1, v2);
        }
    };
    struct var_value_hash {
        imp & m_th;
        var_value_hash(imp & th):m_th(th) {}
        unsigned operator()(theory_var v) const { 
            if (m_th.m_use_nra_model) {
                return m_th.is_int(v);
            }
            else {
                return (unsigned)std::hash<lp::mpq>()(m_th.get_value(v)); 
            }
        }
    };
    int_hashtable<var_value_hash, var_value_eq>   m_model_eqs;


    svector<scope>         m_scopes;
    lp_api::stats          m_stats;
    arith_factory*         m_factory;       
    scoped_ptr<lp::lar_solver> m_solver;
    resource_limit         m_resource_limit;
    lp_bounds              m_new_bounds;
    switcher               m_switcher;
    symbol                 m_farkas;

    context& ctx() const { return th.get_context(); }
    theory_id get_id() const { return th.get_id(); }
    bool is_int(theory_var v) const {  return is_int(get_enode(v));  }
    bool is_int(enode* n) const { return a.is_int(n->get_owner()); }
    enode* get_enode(theory_var v) const { return th.get_enode(v); }
    enode* get_enode(expr* e) const { return ctx().get_enode(e); }
    expr*  get_owner(theory_var v) const { return get_enode(v)->get_owner(); }        

    lp::lar_solver& lp(){ return *m_solver.get(); }
    const lp::lar_solver& lp() const { return *m_solver.get(); }
    
    void init_solver() {
        if (m_solver) return;

        reset_variable_values();
        m_solver = alloc(lp::lar_solver); 

        // initialize 0, 1 variables:
        get_one(true);
        get_one(false);
        get_zero(true);
        get_zero(false);

        smt_params_helper lpar(ctx().get_params());
        lp().settings().set_resource_limit(m_resource_limit);
        lp().settings().simplex_strategy() = static_cast<lp::simplex_strategy_enum>(lpar.arith_simplex_strategy());
        lp().settings().bound_propagation() = BP_NONE != propagation_mode();
        lp().settings().m_enable_hnf = lpar.arith_enable_hnf();
        lp().settings().m_print_external_var_name = lpar.arith_print_ext_var_names();
        lp().set_track_pivoted_rows(lpar.arith_bprop_on_pivoted_rows());
        lp().settings().report_frequency = lpar.arith_rep_freq();
        lp().settings().print_statistics = lpar.arith_print_stats();

        // todo : do not use m_arith_branch_cut_ratio for deciding on cheap cuts
        unsigned branch_cut_ratio = ctx().get_fparams().m_arith_branch_cut_ratio;
        lp().set_cut_strategy(branch_cut_ratio);

        lp().settings().m_int_run_gcd_test = ctx().get_fparams().m_arith_gcd_test;
        lp().settings().set_random_seed(ctx().get_fparams().m_random_seed);
        m_switcher.m_use_nla = lpar.arith_nla();
        m_lia = alloc(lp::int_solver, *m_solver.get());
        get_one(true);
        get_zero(true);
        get_one(false);
        get_zero(false);
    }

    void ensure_nra() {
        if (!m_nra) {
            m_nra = alloc(nra::solver, *m_solver.get(), m.limit(), ctx().get_params());
            m_switcher.m_nra = &m_nra;
            for (auto const& _s : m_scopes) {
                (void)_s;
                m_nra->push();
            }
        }
    }

    lpvar add_const(int c, lpvar& var, bool is_int) {
        if (var != UINT_MAX) {
            return var;
        }
        app_ref cnst(a.mk_numeral(rational(c), is_int), m);
        mk_enode(cnst);
        theory_var v = mk_var(cnst);
        var = lp().add_var(v, true);
        lp().push();
        add_def_constraint(lp().add_var_bound(var, lp::GE, rational(c)));
        add_def_constraint(lp().add_var_bound(var, lp::LE, rational(c)));
        TRACE("arith", tout << "add " << cnst << ", var = " << var << "\n";);
        return var;
    }

    lpvar get_one(bool is_int) {
        return add_const(1, is_int ? m_one_var : m_rone_var, is_int);
    }

     lpvar get_zero(bool is_int) {
        return add_const(0, is_int ? m_zero_var : m_rzero_var, is_int);
    }

    void ensure_nla() {
        if (!m_nla) {
            m_nla = alloc(nla::solver, *m_solver.get());
            m_switcher.m_nla = &m_nla;
            for (auto const& _s : m_scopes) {
                (void)_s;
                m_nla->push();
            }
            smt_params_helper prms(ctx().get_params());
            m_nla->get_core()->m_nla_settings.run_order() = prms.arith_nl_order();
            m_nla->get_core()->m_nla_settings.run_tangents() = prms.arith_nl_tangents();
            m_nla->get_core()->m_nla_settings.run_horner() = prms.arith_nl_horner();
            m_nla->get_core()->m_nla_settings.horner_subs_fixed() = prms.arith_nl_horner_subs_fixed();
            
            m_nla->get_core()->m_nla_settings.horner_frequency() = prms.arith_nl_horner_frequency();
            m_nla->get_core()->m_nla_settings.horner_row_length_limit() = prms.arith_nl_horner_row_length_limit();
            m_nla->get_core()->m_nla_settings.run_grobner() = prms.arith_nl_grobner();
            m_nla->get_core()->m_nla_settings.grobner_subs_fixed() = prms.arith_nl_grobner_subs_fixed();
            m_nla->get_core()->m_nla_settings.grobner_eqs_growth() =  prms.arith_nl_grobner_eqs_growth();
            m_nla->get_core()->m_nla_settings.grobner_expr_size_growth() =  prms.arith_nl_grobner_expr_size_growth();
            m_nla->get_core()->m_nla_settings.grobner_expr_degree_growth() =  prms.arith_nl_grobner_expr_degree_growth();
            m_nla->get_core()->m_nla_settings.grobner_max_simplified() =      prms.arith_nl_grobner_max_simplified();
            m_nla->get_core()->m_nla_settings.grobner_number_of_conflicts_to_report() =      prms.arith_nl_grobner_cnfl_to_report();
            m_nla->get_core()->m_grobner_quota = prms.arith_nl_gr_q();
        }
    }

    void found_unsupported(expr* n) {
        ctx().push_trail(value_trail<context, expr*>(m_not_handled));
        m_not_handled = n;    
    }

    void found_underspecified(expr* n) {
        if (is_app(n) && is_underspecified(to_app(n))) {
            TRACE("arith", tout << "Unhandled: " << mk_pp(n, m) << "\n";);
            m_underspecified.push_back(to_app(n));
        }
        expr* e = nullptr;
        if (a.is_div(n)) {                
            e = a.mk_div0(to_app(n)->get_arg(0), to_app(n)->get_arg(1));
        }
        else if (a.is_idiv(n)) {                
            e = a.mk_idiv0(to_app(n)->get_arg(0), to_app(n)->get_arg(1));
        }
        else if (a.is_rem(n)) {                
            e = a.mk_rem0(to_app(n)->get_arg(0), to_app(n)->get_arg(1));
        }
        else if (a.is_mod(n)) {                
            e = a.mk_mod0(to_app(n)->get_arg(0), to_app(n)->get_arg(1));
        }
        else if (a.is_power(n)) {                
            e = a.mk_power0(to_app(n)->get_arg(0), to_app(n)->get_arg(1));
        }
        if (e) {
            literal lit = th.mk_eq(e, n, false);
            ctx().mark_as_relevant(lit);
            ctx().assign(lit, nullptr);
        }

    }

    bool is_numeral(expr* term, rational& r) {
        rational mul(1);
        do {
            if (a.is_numeral(term, r)) {
                r *= mul;
                return true;
            }
            if (a.is_uminus(term, term)) {
                mul.neg();
                continue;
            }
            if (a.is_to_real(term, term)) {
                continue;
            }                
            return false;
        }
        while (false);
        return false;
    }

    void linearize_term(expr* term, scoped_internalize_state& st) {
        st.push(term, rational::one());
        linearize(st);
    } 
        
    void linearize_ineq(expr* lhs, expr* rhs, scoped_internalize_state& st) {
        st.push(lhs, rational::one());
        st.push(rhs, rational::minus_one());
        linearize(st);
    }
        
    void linearize(scoped_internalize_state& st) { 
        expr_ref_vector & terms = st.terms();
        svector<theory_var>& vars = st.vars();
        vector<rational>& coeffs = st.coeffs();
        rational& offset = st.offset();
        rational r;
        expr* n1, *n2;
        unsigned index = 0;
        while (index < terms.size()) {
            SASSERT(index >= vars.size());
            expr* n = terms[index].get();
            st.terms_to_internalize().push_back(n);
            if (a.is_add(n)) {
                for (expr* arg : *to_app(n)) {
                    st.push(arg, coeffs[index]);
                }
                st.set_back(index);
            }
            else if (a.is_sub(n)) {
                unsigned sz = to_app(n)->get_num_args();
                terms[index] = to_app(n)->get_arg(0);                    
                for (unsigned i = 1; i < sz; ++i) {
                    st.push(to_app(n)->get_arg(i), -coeffs[index]);
                }
            }
            else if (a.is_mul(n, n1, n2) && is_numeral(n1, r)) {
                coeffs[index] *= r;
                terms[index] = n2;
                st.terms_to_internalize().push_back(n1);
            }
            else if (a.is_mul(n, n1, n2) && is_numeral(n2, r)) {
                coeffs[index] *= r;
                terms[index] = n1;
                st.terms_to_internalize().push_back(n2);
            }
            else if (a.is_mul(n)) {
                theory_var v;
                internalize_mul(to_app(n), v, r);
                coeffs[index] *= r;
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
            }
            else if (a.is_numeral(n, r)) {
                offset += coeffs[index]*r;
                ++index;
            }
            else if (a.is_uminus(n, n1)) {
                coeffs[index].neg();
                terms[index] = n1;
            }
            else if (is_app(n) && a.get_family_id() == to_app(n)->get_family_id()) {
                bool is_first = !ctx().e_internalized(n);
                app* t = to_app(n);
                internalize_args(t);
                mk_enode(t);
                theory_var v;
                if (a.is_to_real(n, n1)) {
                    v = mk_var(n1);
                }
                else {
                    v = mk_var(n);
                }
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
                if (!is_first) {
                    // skip recursive internalization
                }
                else if (a.is_to_int(n, n1)) {
                    if (!ctx().relevancy())
                        mk_to_int_axiom(t);
                }
                else if (a.is_to_real(n, n1)) {
                    // already handled
                }
                else if (a.is_idiv(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    m_idiv_terms.push_back(n);
                    app * mod = a.mk_mod(n1, n2);
                    ctx().internalize(mod, false);
                    if (ctx().relevancy()) ctx().add_relevancy_dependency(n, mod);
                }
                else if (a.is_mod(n, n1, n2)) {
                    if (!ctx().relevancy()) mk_idiv_mod_axioms(n1, n2);                    
                }
                else if (a.is_rem(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    if (!ctx().relevancy()) mk_rem_axiom(n1, n2);                    
                }
                else if (a.is_div(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    if (!ctx().relevancy()) mk_div_axiom(n1, n2);                    
                }
                else if (!a.is_div0(n) && !a.is_mod0(n) && !a.is_idiv0(n) && !a.is_rem0(n)) {
                    found_unsupported(n);
                }
                else {
                    // no-op
                }
            }
            else {
                if (is_app(n)) {
                    internalize_args(to_app(n));
                }
                theory_var v = mk_var(n);
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
            }
        }
        for (unsigned i = st.terms_to_internalize().size(); i-- > 0; ) {
            expr* n = st.terms_to_internalize()[i];
            if (is_app(n)) {
                mk_enode(to_app(n));
            }
        }
        st.terms_to_internalize().reset();
    }

    void internalize_args(app* t) {
        for (unsigned i = 0; reflect(t) && i < t->get_num_args(); ++i) {
            if (!ctx().e_internalized(t->get_arg(i))) {
                ctx().internalize(t->get_arg(i), false);
            }
        }
    }

    void internalize_mul(app* t, theory_var& v, rational& r) {
        SASSERT(a.is_mul(t));
        bool _has_var = has_var(t);
        if (!_has_var) {
            internalize_args(t);
            mk_enode(t);
        }
        r = rational::one();
        rational r1;
        v = mk_var(t);
        svector<lpvar> vars;
        ptr_buffer<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            expr* n = todo.back();
            todo.pop_back();
            if (a.is_mul(n)) {
                for (expr* arg : *to_app(n)) {
                    todo.push_back(arg);
                }
            }
            else if (a.is_numeral(n, r1)) {
                r *= r1;
            }
            else {
                if (!ctx().e_internalized(n)) {
                    ctx().internalize(n, false);
                }
                vars.push_back(register_theory_var_in_lar_solver(mk_var(n)));
            }
        }
        TRACE("arith", tout << "v" << v << " := " << mk_pp(t, m) << " " << _has_var << "\n";);
        if (!_has_var) {
            if (m_solver->m_need_register_terms == false) {
                m_solver->m_need_register_terms = true;
                m_solver->register_existing_terms();
            }
            m_switcher.add_monic(register_theory_var_in_lar_solver(v), vars.size(), vars.c_ptr());
        }
    }

    enode * mk_enode(app * n) {
        TRACE("arith", tout << expr_ref(n, m) << "\n";);
        if (ctx().e_internalized(n)) {
            return get_enode(n);
        }
        else {
            return ctx().mk_enode(n, !reflect(n), false, enable_cgc_for(n));       
        }
    }

    bool enable_cgc_for(app * n) const {
        // Congruence closure is not enabled for (+ ...) and (* ...) applications.
        return !(n->get_family_id() == get_id() && (n->get_decl_kind() == OP_ADD || n->get_decl_kind() == OP_MUL));
    }


    void mk_clause(literal l1, literal l2, unsigned num_params, parameter * params) {
        TRACE("arith", literal lits[2]; lits[0] = l1; lits[1] = l2; ctx().display_literals_verbose(tout, 2, lits); tout << "\n";);
        ctx().mk_th_axiom(get_id(), l1, l2, num_params, params);
    }

    void mk_clause(literal l1, literal l2, literal l3, unsigned num_params, parameter * params) {
        TRACE("arith", literal lits[3]; lits[0] = l1; lits[1] = l2; lits[2] = l3; ctx().display_literals_verbose(tout, 3, lits); tout << "\n";);
        ctx().mk_th_axiom(get_id(), l1, l2, l3, num_params, params);
    }

    bool is_underspecified(app* n) const {
        if (n->get_family_id() == get_id()) {
            switch (n->get_decl_kind()) {
            case OP_DIV:
            case OP_IDIV:
            case OP_REM:
            case OP_MOD:
            case OP_DIV0:
            case OP_IDIV0:
            case OP_REM0:
            case OP_MOD0:
                return true;
            default:
                break;
            }
        }
        return false;
    }

    bool reflect(app* n) const {
        return m_arith_params.m_arith_reflect || is_underspecified(n);          
    }

    bool has_var(expr* n) {
        if (!ctx().e_internalized(n)) {
            return false;
        }
        enode* e = get_enode(n);
        return th.is_attached_to_var(e);
    }

    theory_var mk_var(expr* n, bool internalize = true) {
        if (!ctx().e_internalized(n)) {
            ctx().internalize(n, false);                
        }
        enode* e = get_enode(n);
        theory_var v;
        if (!th.is_attached_to_var(e)) {
            v = th.mk_var(e);
            SASSERT(m_bounds.size() <= static_cast<unsigned>(v) || m_bounds[v].empty());
            if (m_bounds.size() <= static_cast<unsigned>(v)) {
                m_bounds.push_back(lp_bounds());
                m_unassigned_bounds.push_back(0);
            }
            ctx().attach_th_var(e, &th, v);
        }
        else {
            v = e->get_th_var(get_id());                
        }
        SASSERT(null_theory_var != v);
        return v;
    }

    bool theory_var_is_registered_in_lar_solver(theory_var v) const {
        return lp().external_is_used(v);
    }

    bool const has_int() const { return lp().has_int_var(); }
    
    lpvar register_theory_var_in_lar_solver(theory_var v) {
        lpvar lpv = lp().external_to_local(v);
        if (lpv != lp::null_lpvar)
            return lpv;
        return lp().add_var(v, is_int(v));
    }
        
    void init_left_side(scoped_internalize_state& st) {
        SASSERT(all_zeros(m_columns));
        svector<theory_var> const& vars = st.vars();
        vector<rational> const& coeffs = st.coeffs();
        for (unsigned i = 0; i < vars.size(); ++i) {
            theory_var var = vars[i];
            rational const& coeff = coeffs[i];
            if (m_columns.size() <= static_cast<unsigned>(var)) {
                m_columns.setx(var, coeff, rational::zero());
            }
            else {
                m_columns[var] += coeff;
            }                
        }
        m_left_side.clear();
        // reset the coefficients after they have been used.
        for (unsigned i = 0; i < vars.size(); ++i) {
            theory_var var = vars[i];
            rational const& r = m_columns[var];
            if (!r.is_zero()) {
                m_left_side.push_back(std::make_pair(r, register_theory_var_in_lar_solver(var)));
                m_columns[var].reset();                    
            }
        }
        SASSERT(all_zeros(m_columns));
    }
        
    bool all_zeros(vector<rational> const& v) const {
        for (rational const& r : v) {
            if (!r.is_zero()) {
                return false;
            }
        }
        return true;
    }
        
    void add_eq_constraint(lp::constraint_index index, enode* n1, enode* n2) {
        m_constraint_sources.setx(index, equality_source, null_source);
        m_equalities.setx(index, enode_pair(n1, n2), enode_pair(0, 0));
        ++m_stats.m_add_rows;
    }
        
    void add_ineq_constraint(lp::constraint_index index, literal lit) {
        m_constraint_sources.setx(index, inequality_source, null_source);
        m_inequalities.setx(index, lit, null_literal);
        ++m_stats.m_add_rows;
        TRACE("arith", lp().constraints().display(tout, index) << " m_stats.m_add_rows = " << m_stats.m_add_rows << "\n";);
    }

    void add_def_constraint(lp::constraint_index index) {
        m_constraint_sources.setx(index, definition_source, null_source);
        m_definitions.setx(index, null_theory_var, null_theory_var);
        ++m_stats.m_add_rows;
    }
        
    void add_def_constraint(lp::constraint_index index, theory_var v) {
        m_constraint_sources.setx(index, definition_source, null_source);
        m_definitions.setx(index, v, null_theory_var);
        ++m_stats.m_add_rows;
    }


    bool is_infeasible() const {
        return lp().get_status() == lp::lp_status::INFEASIBLE;
    }
    
    void internalize_eq(theory_var v1, theory_var v2) {  
        app_ref term(m.mk_fresh_const("eq", a.mk_real()), m);
        scoped_internalize_state st(*this);
        st.vars().push_back(v1);
        st.vars().push_back(v2);        
        st.coeffs().push_back(rational::one());
        st.coeffs().push_back(rational::minus_one());
        theory_var z = internalize_linearized_def(term, st);      
        lpvar vi = register_theory_var_in_lar_solver(z);
        add_def_constraint(lp().add_var_bound(vi, lp::LE, rational::zero()));
        // if (is_infeasible()) {
        //     process_conflict(); // exit here?
        // }
        add_def_constraint(lp().add_var_bound(vi, lp::GE, rational::zero()));
        // if (is_infeasible()) {
        //     process_conflict();
        // }
        TRACE("arith", 
              {
                  expr*  o1 = get_enode(v1)->get_owner();
                  expr*  o2 = get_enode(v2)->get_owner();                  
                  tout << "v" << v1 << " = " << "v" << v2 << ": "
                       << mk_pp(o1, m) << " = " << mk_pp(o2, m) << "\n";
              });
    }

    void del_bounds(unsigned old_size) {
        for (unsigned i = m_bounds_trail.size(); i > old_size; ) {
            --i;
            unsigned v = m_bounds_trail[i];
            lp_api::bound* b = m_bounds[v].back();
            // del_use_lists(b);
            dealloc(b);
            m_bounds[v].pop_back();                        
        }
        m_bounds_trail.shrink(old_size);
    }

    void updt_unassigned_bounds(theory_var v, int inc) {
        TRACE("arith", tout << "v" << v << " " << m_unassigned_bounds[v] << " += " << inc << "\n";);
        ctx().push_trail(vector_value_trail<smt::context, unsigned, false>(m_unassigned_bounds, v));
        m_unassigned_bounds[v] += inc;            
    }
       
    bool is_unit_var(scoped_internalize_state& st) {
        return st.offset().is_zero() && st.vars().size() == 1 && st.coeffs()[0].is_one();
    }

    bool is_one(scoped_internalize_state& st) {
        return st.offset().is_one() && st.vars().empty();
    }

    bool is_zero(scoped_internalize_state& st) {
        return st.offset().is_zero() && st.vars().empty();
    }

    theory_var internalize_def(app* term, scoped_internalize_state& st) {
        TRACE("arith", tout << expr_ref(term, m) << "\n";);
        if (ctx().e_internalized(term)) {
            IF_VERBOSE(0, verbose_stream() << "repeated term\n";);
            return mk_var(term, false);
        }
        linearize_term(term, st);
        if (is_unit_var(st)) {
            return st.vars()[0];
        }
        else {
            theory_var v = mk_var(term);
            SASSERT(null_theory_var != v);
            st.coeffs().resize(st.vars().size() + 1);
            st.coeffs()[st.vars().size()] = rational::minus_one();
            st.vars().push_back(v);
            return v;
        }
    }

    // term - v = 0
    theory_var internalize_def(app* term) {
        scoped_internalize_state st(*this);
        linearize_term(term, st);
        return internalize_linearized_def(term, st);
    }

    lpvar get_lpvar(theory_var v) const {
        return lp().external_to_local(v);
    }
    
    theory_var internalize_linearized_def(app* term, scoped_internalize_state& st) {
        if (is_unit_var(st)) {
            return st.vars()[0];
        }
        else if (is_one(st)) {
            return get_one(a.is_int(term));
        }
        else if (is_zero(st)) {
            return get_zero(a.is_int(term));
        }
        else {
            init_left_side(st);
            if (m_left_side.empty() && st.offset().is_zero()) {
                return get_zero(a.is_int(term));
            }
            theory_var v = mk_var(term);
            lpvar vi = get_lpvar(v);
            TRACE("arith", tout << mk_pp(term, m) << " v" << v << " vi " << vi << "\n";);
            if (vi == UINT_MAX) {
                rational const& offset = st.offset();
                if (!offset.is_zero()) {
                    m_left_side.push_back(std::make_pair(offset, get_one(a.is_int(term))));
                }
                SASSERT(!m_left_side.empty());
                vi = lp().add_term(m_left_side, v);
                SASSERT (lp().is_term(vi));
                TRACE("arith_verbose", tout << "v" << v << " := " << mk_pp(term, m) << " slack: " << vi << " scopes: " << m_scopes.size() << "\n";
                      lp().print_term(lp().get_term(vi), tout) << "\n";);
            }
            rational val;
            if (a.is_numeral(term, val)) {
                m_fixed_var_table.insert(value_sort_pair(val, is_int(v)), v);
            }
            return v;
        }
    }
        

public:
    imp(theory_lra& th, ast_manager& m, theory_arith_params& ap): 
        th(th), m(m), 
        m_arith_params(ap), 
        a(m), 
        m_arith_eq_adapter(th, ap, a),            
        m_internalize_head(0),
        m_one_var(UINT_MAX),
        m_zero_var(UINT_MAX),
        m_rone_var(UINT_MAX),
        m_rzero_var(UINT_MAX),
        m_not_handled(nullptr),
        m_asserted_qhead(0), 
        m_assume_eq_head(0),
        m_num_conflicts(0),
        m_use_nra_model(false),
        m_model_eqs(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)),
        m_solver(nullptr),
        m_resource_limit(*this),
        m_switcher(*this),
        m_farkas("farkas") {
    }
        
    ~imp() {
        del_bounds(0);
        std::for_each(m_internalize_states.begin(), m_internalize_states.end(), delete_proc<internalize_state>());
    }

    void init(context* ctx) {
        init_solver();
    }
        
    void internalize_is_int(app * n) {
        SASSERT(a.is_is_int(n));
        (void) mk_enode(n);
        if (!ctx().relevancy())
            mk_is_int_axiom(n);        
    }

    bool internalize_atom(app * atom, bool gate_ctx) {
        SASSERT(!ctx().b_internalized(atom));
        bool_var bv = ctx().mk_bool_var(atom);
        ctx().set_var_theory(bv, get_id());
        expr* n1, *n2;
        rational r;
        lp_api::bound_kind k;
        theory_var v = null_theory_var;
        if (a.is_le(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
            v = internalize_def(to_app(n1));
            k = lp_api::upper_t;
        }
        else if (a.is_ge(atom, n1, n2) && is_numeral(n2, r) && is_app(n1)) {
            v = internalize_def(to_app(n1));
            k = lp_api::lower_t;
        }    
        else if (a.is_is_int(atom)) {
            internalize_is_int(atom);
            return true;
        }
        else {
            TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
            found_unsupported(atom);
            return true;
        }
        if (is_int(v) && !r.is_int()) {
            r = (k == lp_api::upper_t) ? floor(r) : ceil(r);
        }
        lp_api::bound* b = mk_var_bound(bv, v, k, r);
        m_bounds[v].push_back(b);
        updt_unassigned_bounds(v, +1);
        m_bounds_trail.push_back(v);
        m_bool_var2bound.insert(bv, b);
        TRACE("arith_verbose", tout << "Internalized " << mk_pp(atom, m) << "\n";);
        mk_bound_axioms(*b);
        //add_use_lists(b);
        return true;
    }
        
    bool internalize_term(app * term) {
        if (ctx().e_internalized(term) && th.is_attached_to_var(ctx().get_enode(term))) {
            // skip
        }
        else {
            internalize_def(term);
        }
        return true;
    }

    bool is_arith(enode* n) {
        return n && n->get_th_var(get_id()) != null_theory_var;
    }
        
    void internalize_eq_eh(app * atom, bool_var) {
        TRACE("arith_verbose", tout << mk_pp(atom, m) << "\n";);
        expr* lhs = nullptr, *rhs = nullptr;
        VERIFY(m.is_eq(atom, lhs, rhs));
        enode * n1 = get_enode(lhs);
        enode * n2 = get_enode(rhs);
        if (is_arith(n1) && is_arith(n2) && n1 != n2) {
            m_arith_eq_adapter.mk_axioms(n1, n2);
        }
        // internalization of ite expressions produces equalities of the form
        // (= x (ite c x y)) and (= y (ite c x y))
        // this step ensures that a shared enode is attached
        // with the ite expression.
        else if (m.is_ite(lhs) || m.is_ite(rhs)) {
            // std::cout << "eq\n";
            m_arith_eq_adapter.mk_axioms(n1, n2);
        }
    }

    void assign_eh(bool_var v, bool is_true) {
        TRACE("arith", tout << mk_pp(ctx().bool_var2expr(v), m) << " " << (is_true?"true":"false") << "\n";);
        m_asserted_atoms.push_back(delayed_atom(v, is_true));
    }

    lbool get_phase(bool_var v) {
        lp_api::bound* b;
        if (!m_bool_var2bound.find(v, b)) {
            return l_undef;
        }
        lp::lconstraint_kind k = lp::EQ;
        switch (b->get_bound_kind()) {
        case lp_api::lower_t:
            k = lp::GE;
            break;
        case lp_api::upper_t:
            k = lp::LE;
            break;
        default:
            break;
        }         
        auto vi = register_theory_var_in_lar_solver(b->get_var());
        if (vi == lp::null_lpvar) {
            return l_undef;
        }
        return m_solver->compare_values(vi, k, b->get_value()) ? l_true : l_false;
    }

    void new_eq_eh(theory_var v1, theory_var v2) {
        // or internalize_eq(v1, v2);
        m_arith_eq_adapter.new_eq_eh(v1, v2);            
    }

    bool use_diseqs() const {
        return true;
    }

    void new_diseq_eh(theory_var v1, theory_var v2) {
        TRACE("arith", tout << "v" << v1 << " != " << "v" << v2 << "\n";);
        ++m_stats.m_assert_diseq;
        m_arith_eq_adapter.new_diseq_eh(v1, v2);
    }

    void apply_sort_cnstr(enode* n, sort*) {
        TRACE("arith", tout << "sort constraint: " << mk_pp(n->get_owner(), m) << "\n";);
#if 0
        if (!th.is_attached_to_var(n)) {
            theory_var v = mk_var(n->get_owner(), false);
            auto vi = register_theory_var_in_lar_solver(v);
            expr* e = nullptr;
            if (a.is_to_real(n->get_owner(), e)) {
                // TBD: add a way to bind equality between vi and wi in m_solver
            }
        }
#endif
    }

    void push_scope_eh() {
        TRACE("arith", tout << "push\n";);
        m_scopes.push_back(scope());
        scope& sc = m_scopes.back();
        sc.m_bounds_lim = m_bounds_trail.size();
        sc.m_asserted_qhead = m_asserted_qhead;
        sc.m_idiv_lim = m_idiv_terms.size();
        sc.m_asserted_atoms_lim = m_asserted_atoms.size();
        sc.m_not_handled = m_not_handled;
        sc.m_underspecified_lim = m_underspecified.size();
        lp().push();
        m_switcher.push();
    }

    void pop_scope_eh(unsigned num_scopes) {
        TRACE("arith", tout << "pop " << num_scopes << "\n";);
        if (num_scopes == 0) {
            return;
        }
        unsigned old_size = m_scopes.size() - num_scopes;
        del_bounds(m_scopes[old_size].m_bounds_lim);
        m_idiv_terms.shrink(m_scopes[old_size].m_idiv_lim);
        m_asserted_atoms.shrink(m_scopes[old_size].m_asserted_atoms_lim);
        m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
        m_underspecified.shrink(m_scopes[old_size].m_underspecified_lim);
        m_not_handled = m_scopes[old_size].m_not_handled;
        m_scopes.resize(old_size);            
        lp().pop(num_scopes);
        // VERIFY(l_false != make_feasible());
        m_new_bounds.reset();
        m_to_check.reset();
        m_switcher.pop(num_scopes);
        TRACE("arith", tout << "num scopes: " << num_scopes << " new scope level: " << m_scopes.size() << "\n";);
    }

    void restart_eh() {
        m_arith_eq_adapter.restart_eh();
    }

    void relevant_eh(app* n) {
        TRACE("arith", tout << mk_pp(n, m) << "\n";);
        expr* n1, *n2;
        if (a.is_mod(n, n1, n2)) 
            mk_idiv_mod_axioms(n1, n2);
        else if (a.is_rem(n, n1, n2))
            mk_rem_axiom(n1, n2);
        else if (a.is_div(n, n1, n2)) 
            mk_div_axiom(n1, n2);
        else if (a.is_to_int(n)) 
            mk_to_int_axiom(n);
        else if (a.is_is_int(n))
            mk_is_int_axiom(n);            
    }

    //  n < 0 || rem(a, n) =  mod(a, n)
    // !n < 0 || rem(a, n) = -mod(a, n)
    void mk_rem_axiom(expr* dividend, expr* divisor) {
        expr_ref zero(a.mk_int(0), m);
        expr_ref rem(a.mk_rem(dividend, divisor), m);
        expr_ref mod(a.mk_mod(dividend, divisor), m);
        expr_ref mmod(a.mk_uminus(mod), m);
        expr_ref degz_expr(a.mk_ge(divisor, zero), m);
        literal dgez = mk_literal(degz_expr);
        literal pos = th.mk_eq(rem, mod,  false);
        literal neg = th.mk_eq(rem, mmod, false);
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_ite(degz_expr, ctx().bool_var2expr(pos.var()), ctx().bool_var2expr(neg.var()));
            th.log_axiom_instantiation(body);
        }
        mk_axiom(~dgez, pos);
        mk_axiom( dgez, neg);                    
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    // q = 0 or q * (p div q) = p
    void mk_div_axiom(expr* p, expr* q) {
        if (a.is_zero(q)) return;
        literal eqz = th.mk_eq(q, a.mk_real(0), false);
        literal eq  = th.mk_eq(a.mk_mul(q, a.mk_div(p, q)), p, false);
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(m.mk_not(ctx().bool_var2expr(eqz.var())), ctx().bool_var2expr(eq.var()));
            th.log_axiom_instantiation(body);
        }
        mk_axiom(eqz, eq);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    // to_int (to_real x) = x
    // to_real(to_int(x)) <= x < to_real(to_int(x)) + 1
    void mk_to_int_axiom(app* n) {
        expr* x = nullptr, *y = nullptr;
        VERIFY (a.is_to_int(n, x));            
        if (a.is_to_real(x, y)) {
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_eq(n, y);
                th.log_axiom_instantiation(body);
            }
            mk_axiom(th.mk_eq(y, n, false));
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
        else {
            expr_ref to_r(a.mk_to_real(n), m);
            expr_ref lo(a.mk_le(a.mk_sub(to_r, x), a.mk_real(0)), m);
            expr_ref hi(a.mk_ge(a.mk_sub(x, to_r), a.mk_real(1)), m);
            if (m.has_trace_stream()) th.log_axiom_instantiation(lo);
            mk_axiom(mk_literal(lo));
            if (m.has_trace_stream()) {
                m.trace_stream() << "[end-of-instance]\n";
                expr_ref body(m);
                body = m.mk_not(hi);
                th.log_axiom_instantiation(body);
            }
            mk_axiom(~mk_literal(hi));
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
    }

    // is_int(x) <=> to_real(to_int(x)) = x
    void mk_is_int_axiom(app* n) {
        expr* x = nullptr;
        VERIFY(a.is_is_int(n, x));
        literal eq = th.mk_eq(a.mk_to_real(a.mk_to_int(x)), x, false);
        literal is_int = ctx().get_literal(n);
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_iff(n, ctx().bool_var2expr(eq.var()));
            th.log_axiom_instantiation(body);
        }
        mk_axiom(~is_int, eq);
        mk_axiom(is_int, ~eq);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    // create axiom for 
    //    u = v + r*w,
    ///   abs(r) > r >= 0
    void assert_idiv_mod_axioms(theory_var u, theory_var v, theory_var w, rational const& r) {
        app_ref term(m);
        term = a.mk_sub(get_enode(u)->get_owner(), 
                        a.mk_add(get_enode(v)->get_owner(),
                                 a.mk_mul(a.mk_numeral(r, true), 
                                          get_enode(w)->get_owner())));
        theory_var z = internalize_def(term);
        lpvar vi = register_theory_var_in_lar_solver(z);
        add_def_constraint(lp().add_var_bound(vi, lp::GE, rational::zero()));
        add_def_constraint(lp().add_var_bound(vi, lp::LE, rational::zero()));
        add_def_constraint(lp().add_var_bound(register_theory_var_in_lar_solver(v), lp::GE, rational::zero()));
        add_def_constraint(lp().add_var_bound(register_theory_var_in_lar_solver(v), lp::LT, abs(r)));
        SASSERT(!is_infeasible());
        TRACE("arith", tout << term << "\n" << lp().constraints(););
    }

    void mk_idiv_mod_axioms(expr * p, expr * q) {
        if (a.is_zero(q)) {
            return;
        }
        TRACE("arith", tout << expr_ref(p, m) << " " << expr_ref(q, m) << "\n";);
        // if q is zero, then idiv and mod are uninterpreted functions.
        expr_ref div(a.mk_idiv(p, q), m);
        expr_ref mod(a.mk_mod(p, q), m);
        expr_ref zero(a.mk_int(0), m);
        literal eq         = th.mk_eq(a.mk_add(a.mk_mul(q, div), mod), p, false);
        literal mod_ge_0   = mk_literal(a.mk_ge(mod, zero));
        literal div_ge_0   = mk_literal(a.mk_ge(div, zero));
        literal div_le_0   = mk_literal(a.mk_le(div, zero));
        literal p_ge_0     = mk_literal(a.mk_ge(p, zero));
        literal p_le_0     = mk_literal(a.mk_le(p, zero));

        rational k(0);
        expr_ref upper(m);

        if (a.is_numeral(q, k)) {
            if (k.is_pos()) { 
                upper = a.mk_numeral(k - 1, true);
            }
            else if (k.is_neg()) {
                upper = a.mk_numeral(-k - 1, true);
            }
        }
        else {
            k = rational::zero();
        }

        context& c = ctx();
        if (!k.is_zero()) {
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(eq.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(eq);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(mod_ge_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(mod_ge_0);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(m.mk_eq(q, zero)), a.mk_le(mod, upper));
                th.log_axiom_instantiation(body);
            }
            expr_ref le(a.mk_le(mod, upper), m);
            mk_axiom(mk_literal(le));
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (k.is_pos()) {
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(m.mk_and(a.mk_gt(q, zero), c.bool_var2expr(p_ge_0.var())), c.bool_var2expr(div_ge_0.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_ge_0, div_ge_0);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(m.mk_and(a.mk_gt(q, zero), c.bool_var2expr(p_le_0.var())), c.bool_var2expr(div_le_0.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_le_0, div_le_0);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            }
            else {
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(m.mk_and(a.mk_lt(q, zero), c.bool_var2expr(p_ge_0.var())), c.bool_var2expr(div_le_0.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_ge_0, div_le_0);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(m.mk_and(a.mk_lt(q, zero), c.bool_var2expr(p_le_0.var())), c.bool_var2expr(div_ge_0.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_le_0, div_ge_0);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            }
        }
        else {
            // q >= 0 or p = (p mod q) + q * (p div q)
            // q <= 0 or p = (p mod q) + q * (p div q)
            // q >= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) <  q
            // q >= 0 or (p mod q) < -q
            literal q_ge_0 = mk_literal(a.mk_ge(q, zero));
            literal q_le_0 = mk_literal(a.mk_le(q, zero));
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(eq.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_ge_0, eq);
            mk_axiom(q_le_0, eq);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(mod_ge_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_ge_0, mod_ge_0);
            mk_axiom(q_le_0, mod_ge_0);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(a.mk_lt(q, zero), a.mk_lt(a.mk_sub(mod, q), zero));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_le_0, ~mk_literal(a.mk_ge(a.mk_sub(mod, q), zero)));
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(a.mk_lt(q, zero), a.mk_lt(a.mk_add(mod, q), zero));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_ge_0, ~mk_literal(a.mk_ge(a.mk_add(mod, q), zero)));        
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_and(a.mk_gt(q, zero), c.bool_var2expr(p_ge_0.var())), c.bool_var2expr(div_ge_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_le_0, ~p_ge_0, div_ge_0); 
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_and(a.mk_gt(q, zero), c.bool_var2expr(p_le_0.var())), c.bool_var2expr(div_le_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_le_0, ~p_le_0, div_le_0); 
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_and(a.mk_lt(q, zero), c.bool_var2expr(p_ge_0.var())), c.bool_var2expr(div_le_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_ge_0, ~p_ge_0, div_le_0); 
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_and(a.mk_lt(q, zero), c.bool_var2expr(p_le_0.var())), c.bool_var2expr(div_ge_0.var()));
                th.log_axiom_instantiation(body);
            }
            mk_axiom(q_ge_0, ~p_le_0, div_ge_0); 
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
        if (m_arith_params.m_arith_enum_const_mod && k.is_pos() && k < rational(8)) {
            unsigned _k = k.get_unsigned();
            literal_buffer lits;
            expr_ref_vector exprs(m);
            for (unsigned j = 0; j < _k; ++j) {
                literal mod_j = th.mk_eq(mod, a.mk_int(j), false);
                lits.push_back(mod_j);
                exprs.push_back(c.bool_var2expr(mod_j.var()));
                ctx().mark_as_relevant(mod_j);
            }
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_or(exprs.size(), exprs.c_ptr());
                th.log_axiom_instantiation(body);
            }
            ctx().mk_th_axiom(get_id(), lits.size(), lits.begin());                
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }            
    }

    void mk_axiom(literal l) {
        ctx().mk_th_axiom(get_id(), false_literal, l);
        if (ctx().relevancy()) {
            ctx().mark_as_relevant(l);
        }
    }

    void mk_axiom(literal l1, literal l2) {
        if (l1 == false_literal) {
            mk_axiom(l2);
            return;
        }
        ctx().mk_th_axiom(get_id(), l1, l2);
        if (ctx().relevancy()) {
            ctx().mark_as_relevant(l1);
            ctx().add_rel_watch(~l1, ctx().bool_var2expr(l2.var()));
        }
    }

    void mk_axiom(literal l1, literal l2, literal l3) {
        ctx().mk_th_axiom(get_id(), l1, l2, l3);
        if (ctx().relevancy()) {
            ctx().mark_as_relevant(l1);
            ctx().add_rel_watch(~l1, ctx().bool_var2expr(l2.var()));
            ctx().add_rel_watch(~l2, ctx().bool_var2expr(l3.var()));
        }
    }

    literal mk_literal(expr* e) {
        expr_ref pinned(e, m);
        TRACE("mk_bool_var", tout << pinned << " " << pinned->get_id() << "\n";);
        if (!ctx().e_internalized(e)) {
            ctx().internalize(e, false);
        }
        return ctx().get_literal(e);
    }


    void init_search_eh() {
        m_arith_eq_adapter.init_search_eh();
        m_num_conflicts = 0;
    }

    bool can_get_value(theory_var v) const {
        return can_get_bound(v) && !m_variable_values.empty();
    }

    bool can_get_bound(theory_var v) const {
        return v != null_theory_var && lp().external_is_used(v);
    }

    bool can_get_ivalue(theory_var v) const {
        return can_get_bound(v);
    }

    mutable vector<std::pair<lpvar, rational>> m_todo_terms;
 
    lp::impq get_ivalue(theory_var v) const {
        SASSERT(can_get_ivalue(v));
        lpvar vi = get_lpvar(v);
        if (!lp().is_term(vi))
            return lp().get_column_value(vi);
        m_todo_terms.push_back(std::make_pair(vi, rational::one()));
        lp::impq result(0);
        while (!m_todo_terms.empty()) {
            vi = m_todo_terms.back().first;
            rational coeff = m_todo_terms.back().second;
            m_todo_terms.pop_back();
            if (lp().is_term(vi)) {
                const lp::lar_term& term = lp().get_term(vi);
                for (const auto & i:  term) {
                    m_todo_terms.push_back(std::make_pair(i.var(), coeff * i.coeff()));
                }                    
            }
            else {
                result += lp().get_column_value(vi) * coeff;
            }
        }
        return result;
    }
        
    rational get_value(theory_var v) const {
        if (v == null_theory_var || !lp().external_is_used(v)) {
            TRACE("arith", tout << "Variable v" << v << " not internalized\n";);
            return rational::zero();
        }
            
        lpvar vi = get_lpvar(v);
        if (m_variable_values.count(vi) > 0)
            return m_variable_values[vi];
        
        if (!lp().is_term(vi)) {
            TRACE("arith", tout << "not a term v" << v << "\n";);
            return rational::zero();
        }
        
        m_todo_terms.push_back(std::make_pair(vi, rational::one()));
        rational result(0);
        while (!m_todo_terms.empty()) {
            lpvar wi = m_todo_terms.back().first;
            rational coeff = m_todo_terms.back().second;
            m_todo_terms.pop_back();
            if (lp().is_term(wi)) {
                const lp::lar_term& term = lp().get_term(wi);
                for (const auto & i : term) {
                    if (m_variable_values.count(i.var()) > 0) {
                        result += m_variable_values[i.var()] * coeff * i.coeff();
                    }
                    else {
                        m_todo_terms.push_back(std::make_pair(i.var(), coeff * i.coeff()));
                    }
                }                    
            }
            else {
                result += m_variable_values[wi] * coeff;
            }
        }
        m_variable_values[vi] = result;
        return result;
    }

    void init_variable_values() {
        reset_variable_values();
        if (!m.canceled() && m_solver.get() && th.get_num_vars() > 0) {
            TRACE("arith", tout << "update variable values\n";);
            lp().get_model(m_variable_values);
        }
    }

    void reset_variable_values() {
        m_variable_values.clear();
    }

    bool influences_nl_var(theory_var v) const {
        return m_nla && m_nla->influences_nl_var(get_lpvar(v));
    }
    
    bool can_be_used_in_random_update(theory_var v) const {
        if (!th.is_relevant_and_shared(get_enode(v)))
            return false;

        if (is_int(v))
            return false;

        if (influences_nl_var(v))
            return false;
        
        return true;
    }
    
    bool assume_eqs() {        
        svector<lpvar> vars;
        theory_var sz = static_cast<theory_var>(th.get_num_vars());
        for (theory_var v = 0; v < sz; ++v) {
            if (th.is_relevant_and_shared(get_enode(v))) 
                vars.push_back(get_lpvar(v));
        }
        if (vars.empty()) {
            return false;
        }
        if (!m_use_nra_model) {
            lp().random_update(vars.size(), vars.c_ptr());
        }
        init_variable_values();
        TRACE("arith", 
              for (theory_var v = 0; v < sz; ++v) {
                  if (th.is_relevant_and_shared(get_enode(v))) { 
                      tout << "v" << v << " ";
                  }
              }
              tout << "\n"; );
        m_model_eqs.reset();
        TRACE("arith", display(tout););
            
        unsigned old_sz = m_assume_eq_candidates.size();
        bool result = false;
        int start = ctx().get_random_value();
        for (theory_var i = 0; i < sz; ++i) {
            theory_var v = (i + start) % sz;
            enode* n1 = get_enode(v);
            if (!th.is_relevant_and_shared(n1)) {                    
                continue;
            }
            if (!can_get_value(v)) {
                continue;
            }
            theory_var other = m_model_eqs.insert_if_not_there(v);
            TRACE("arith", tout << "insert: v" << v << " := " << get_value(v) << " found: v" << other << "\n";);
            if (other == v) {
                continue;
            }
            enode* n2 = get_enode(other);
            if (n1->get_root() != n2->get_root()) {
                TRACE("arith", tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";
                      tout << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << "\n";
                      tout << "v" << v << " = " << "v" << other << "\n";);
                m_assume_eq_candidates.push_back(std::make_pair(v, other));
                result = true;
            }
        }
            
        if (result) {
            ctx().push_trail(restore_size_trail<context, std::pair<theory_var, theory_var>, false>(m_assume_eq_candidates, old_sz));
        }

        return delayed_assume_eqs();
    }

    bool delayed_assume_eqs() {
        if (m_assume_eq_head == m_assume_eq_candidates.size())
            return false;
            
        ctx().push_trail(value_trail<context, unsigned>(m_assume_eq_head));
        while (m_assume_eq_head < m_assume_eq_candidates.size()) {
            std::pair<theory_var, theory_var> const & p = m_assume_eq_candidates[m_assume_eq_head];
            theory_var v1 = p.first;
            theory_var v2 = p.second;
            enode* n1 = get_enode(v1);
            enode* n2 = get_enode(v2);
            m_assume_eq_head++;
            CTRACE("arith", 
                   is_eq(v1, v2) && n1->get_root() != n2->get_root(),
                   tout << "assuming eq: v" << v1 << " = v" << v2 << "\n";);
            if (is_eq(v1, v2) &&  n1->get_root() != n2->get_root() && th.assume_eq(n1, n2)) {
                return true;
            }
        }
        return false;
    }

    bool is_eq(theory_var v1, theory_var v2) {
        if (m_use_nra_model) {
            SASSERT(!m_switcher.m_use_nla);
            return m_nra->am().eq(nl_value(v1, *m_a1), nl_value(v2, *m_a2));
        }
        else {
            return get_value(v1) == get_value(v2); 
        }
    }

    bool has_delayed_constraints() const {
        return !m_asserted_atoms.empty();
    }

    final_check_status final_check_eh() {
        IF_VERBOSE(12, verbose_stream() << "final-check " << m_solver->get_status() << "\n");
        m_use_nra_model = false;
        lbool is_sat = l_true;
        SASSERT(lp().ax_is_correct());
        if (lp().get_status() != lp::lp_status::OPTIMAL) {
            is_sat = make_feasible();
        }
        final_check_status st = FC_DONE;
        switch (is_sat) {
        case l_true:
                
            TRACE("arith", display(tout););
            switch (check_lia()) {
            case l_true:
                break;
            case l_false:
                return FC_CONTINUE;
            case l_undef:
                TRACE("arith", tout << "check-lia giveup\n";);
                st = FC_CONTINUE;
                break;
            }
            
            switch (check_nra()) {
            case l_true:
                break;
            case l_false:
                return FC_CONTINUE;
            case l_undef:
                TRACE("arith", tout << "check-nra giveup\n";);
                st = FC_GIVEUP;
                break;
            }
            if (assume_eqs()) {
                ++m_stats.m_assume_eqs;
                return FC_CONTINUE;
            }    
            if (delayed_assume_eqs()) {
                ++m_stats.m_assume_eqs;
                return FC_CONTINUE;
            }
            if (m_not_handled != nullptr) {
                TRACE("arith", tout << "unhandled operator " << mk_pp(m_not_handled, m) << "\n";);        
                st = FC_GIVEUP;
            }                
            return st;
        case l_false:
            get_infeasibility_explanation_and_set_conflict();
            return FC_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check feasiable is undef\n";);
            return m.canceled() ? FC_CONTINUE : FC_GIVEUP;
        default:
            UNREACHABLE();
            break;
        }
        TRACE("arith", tout << "default giveup\n";);
        return FC_GIVEUP;
    }

        // create an eq atom representing "term = offset"
    app_ref mk_eq(lp::lar_term const& term, rational const& offset) {
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        bool isint = offset.is_int();
        for (auto const& kv : coeffs) isint &= is_int(kv.m_key) && kv.m_value.is_int();
        app_ref t = coeffs2app(coeffs, rational::zero(), isint);
        app_ref s(a.mk_numeral(offset, isint), m);
        if (s == t) {
            return app_ref(m.mk_true(), m);
        }
        else {
            app_ref atom(m.mk_eq(t, s), m);
            ctx().internalize(atom, true);
            ctx().mark_as_relevant(atom.get());
            return atom;
        }
    }
    // create a bound atom representing term >= k is lower_bound is true, and term <= k if it is false
    app_ref mk_bound(lp::lar_term const& term, rational const& k, bool lower_bound) {
        rational offset = k;
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        bool is_int = true;
        rational lc = denominator(k);
        for (auto const& kv : coeffs) {
            theory_var w = kv.m_key;
            expr* o = get_enode(w)->get_owner();
            is_int = a.is_int(o);
            if (!is_int) break;
            lc = lcm(lc, denominator(kv.m_value));
        }

        // ensure that coefficients are integers when all variables are integers as well.
        if (is_int && !lc.is_one()) {
            SASSERT(lc.is_pos());
            offset *= lc;
            for (auto& kv : coeffs) kv.m_value *= lc;
        }       

        if (is_int) {
            // 3x + 6y >= 5 -> x + 3y >= 5/3, then x + 3y >= 2
            // 3x + 6y <= 5 -> x + 3y <= 1
            rational g = gcd_reduce(coeffs);
            if (!g.is_one()) {
                if (lower_bound) {
                    TRACE("arith", tout << "lower: " << offset << " / " << g << " = " << offset / g << " >= " << ceil(offset / g) << "\n";);
                    offset = ceil(offset / g);
                }
                else {
                    TRACE("arith", tout << "upper: " << offset << " / " << g << " = " << offset / g << " <= " << floor(offset / g) << "\n";);
                    offset = floor(offset / g);
                }
            }
        }
        if (!coeffs.empty() && coeffs.begin()->m_value.is_neg()) {
            offset.neg();
            lower_bound = !lower_bound;
            for (auto& kv : coeffs) kv.m_value.neg();
        }

        // CTRACE("arith", is_int,
        //        lp().print_term(term, tout << "term: ") << "\n";
        //        tout << "offset: " << offset << " gcd: " << g << "\n";);

        app_ref atom(m);
        app_ref t = coeffs2app(coeffs, rational::zero(), is_int);
        if (lower_bound) {
            atom = a.mk_ge(t, a.mk_numeral(offset, is_int));
        }
        else {
            atom = a.mk_le(t, a.mk_numeral(offset, is_int));
        }

        TRACE("arith", tout << t << ": " << atom << "\n";
              lp().print_term(term, tout << "bound atom: ") << (lower_bound?" >= ":" <= ") << k << "\n";);
        ctx().internalize(atom, true);
        ctx().mark_as_relevant(atom.get());
        return atom;
    }


    /**
     * n = (div p q)
     *
     * (div p q) * q + (mod p q) = p, (mod p q) >= 0
     *
     * 0 < q => (p/q <= v(p)/v(q) => n <= floor(v(p)/v(q)))
     * 0 < q => (v(p)/v(q) <= p/q => v(p)/v(q) - 1 < n) 
     * 
     */

    bool is_bounded(expr* n) {
        expr* x = nullptr, *y = nullptr;
        while (true) {
            if (a.is_idiv(n, x, y) && a.is_numeral(y)) {
                n = x;
            }
            else if (a.is_mod(n, x, y) && a.is_numeral(y)) {
                return true;
            }
            else if (a.is_numeral(n)) {
                return true;
            }
            else {
                return false;
            }
        }
    }

    bool check_idiv_bounds() {
        if (m_idiv_terms.empty()) {
            return true;
        }
        bool all_divs_valid = true;        
        for (expr* n : m_idiv_terms) {
            expr* p = nullptr, *q = nullptr;
            VERIFY(a.is_idiv(n, p, q));
            theory_var v  = mk_var(n);
            theory_var v1 = mk_var(p);
            lp::impq r1 = get_ivalue(v1);
            rational r2;

            if (!r1.x.is_int() || r1.x.is_neg() || !r1.y.is_zero()) {
                // TBD
                // r1 = 223/4, r2 = 2, r = 219/8 
                // take ceil(r1), floor(r1), ceil(r2), floor(r2), for floor(r2) > 0
                // then 
                //      p/q <= ceil(r1)/floor(r2) => n <= div(ceil(r1), floor(r2))
                //      p/q >= floor(r1)/ceil(r2) => n >= div(floor(r1), ceil(r2))
                continue;
            }

            if (a.is_numeral(q, r2) && r2.is_pos()) {
                if (!is_bounded(n)) {
                    TRACE("arith", tout << "unbounded " << expr_ref(n, m) << "\n";);
                    continue;
                }
                lp::impq val_v = get_ivalue(v);
                if (val_v.y.is_zero() && val_v.x == div(r1.x, r2)) continue;
            
                TRACE("arith", tout << get_value(v) << " != " << r1 << " div " << r2 << "\n";);
                rational div_r = div(r1.x, r2);
                // p <= q * div(r1, q) + q - 1 => div(p, q) <= div(r1, r2)
                // p >= q * div(r1, q) => div(r1, q) <= div(p, q)
                rational mul(1);
                rational hi = r2 * div_r + r2 - 1;
                rational lo = r2 * div_r;

                // used to normalize inequalities so they 
                // don't appear as 8*x >= 15, but x >= 2
                expr *n1 = nullptr, *n2 = nullptr;
                if (a.is_mul(p, n1, n2) && is_numeral(n1, mul) && mul.is_pos()) {
                    p = n2;
                    hi = floor(hi/mul);
                    lo = ceil(lo/mul);
                }
                literal p_le_r1  = mk_literal(a.mk_le(p, a.mk_numeral(hi, true)));
                literal p_ge_r1  = mk_literal(a.mk_ge(p, a.mk_numeral(lo, true)));
                literal n_le_div = mk_literal(a.mk_le(n, a.mk_numeral(div_r, true)));
                literal n_ge_div = mk_literal(a.mk_ge(n, a.mk_numeral(div_r, true)));
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(ctx().bool_var2expr(p_le_r1.var()), ctx().bool_var2expr(n_le_div.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_le_r1, n_le_div); 
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(ctx().bool_var2expr(p_ge_r1.var()), ctx().bool_var2expr(n_ge_div.var()));
                    th.log_axiom_instantiation(body);
                }
                mk_axiom(~p_ge_r1, n_ge_div);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

                all_divs_valid = false;

                TRACE("arith",
                      tout << r1 << " div " << r2 << "\n";
                      literal_vector lits;
                      lits.push_back(~p_le_r1);
                      lits.push_back(n_le_div);
                      ctx().display_literals_verbose(tout, lits) << "\n\n";
                      lits[0] = ~p_ge_r1;
                      lits[1] = n_ge_div;
                      ctx().display_literals_verbose(tout, lits) << "\n";);                      
                continue;
            }
        }
        
        return all_divs_valid;
    }

    expr_ref var2expr(lpvar v) {
        std::ostringstream name;
        name << "v" << lp().local_to_external(v);
        return expr_ref(m.mk_const(symbol(name.str().c_str()), a.mk_int()), m);
    }

    expr_ref multerm(rational const& r, expr* e) {
        if (r.is_one()) return expr_ref(e, m);
        return expr_ref(a.mk_mul(a.mk_numeral(r, true), e), m);
    }

    expr_ref term2expr(lp::lar_term const& term) {
        expr_ref t(m);
        expr_ref_vector ts(m);
        for (auto const& p : term) {
            lpvar wi = p.var();
            if (lp().is_term(wi)) {
                ts.push_back(multerm(p.coeff(), term2expr(lp().get_term(wi))));
            }
            else {
                ts.push_back(multerm(p.coeff(), var2expr(wi)));
            }
        }
        if (ts.size() == 1) {
            t = ts.back();
        }
        else {
            t = a.mk_add(ts.size(), ts.c_ptr());
        }
        return t;
    }

    expr_ref constraint2fml(lp::constraint_index ci) {
        lp::lar_base_constraint const& c = lp().constraints()[ci];
        expr_ref fml(m);
        expr_ref_vector ts(m);
        rational rhs = c.rhs();
        for (auto cv : c.coeffs()) {
            ts.push_back(multerm(cv.first, var2expr(cv.second)));
        }
        switch (c.kind()) {
        case lp::LE: fml = a.mk_le(a.mk_add(ts.size(), ts.c_ptr()), a.mk_numeral(rhs, true)); break;
        case lp::LT: fml = a.mk_lt(a.mk_add(ts.size(), ts.c_ptr()), a.mk_numeral(rhs, true)); break;
        case lp::GE: fml = a.mk_ge(a.mk_add(ts.size(), ts.c_ptr()), a.mk_numeral(rhs, true)); break;
        case lp::GT: fml = a.mk_gt(a.mk_add(ts.size(), ts.c_ptr()), a.mk_numeral(rhs, true)); break;
        case lp::EQ: fml = m.mk_eq(a.mk_add(ts.size(), ts.c_ptr()), a.mk_numeral(rhs, true)); break;
        case lp::NE:
            SASSERT(false); // unexpected
            break;
        }
        return fml;
    }

    void dump_cut_lemma(std::ostream& out, lp::lar_term const& term, lp::mpq const& k, lp::explanation const& ex, bool upper) {
        lp().print_term(term, out << "bound: "); 
        out << (upper?" <= ":" >= ") << k << "\n";
        for (auto const& p : term) {
            lpvar wi = p.var();
            out << p.coeff() << " * ";
            if (lp().is_term(wi)) {
                lp().print_term(lp().get_term(wi), out) << "\n";
            }
            else {
                out << "v" << lp().local_to_external(wi) << "\n";
            }
        }
        for (auto const& ev : ex) {
            lp().constraints().display(out << ev.first << ": ", ev.second);
        }
        expr_ref_vector fmls(m);
        for (auto const& ev : ex) {
            fmls.push_back(constraint2fml(ev.second));
        }        
        expr_ref t(term2expr(term), m);
        if (upper) {
            fmls.push_back(m.mk_not(a.mk_ge(t, a.mk_numeral(k, true))));
        }
        else {
            fmls.push_back(m.mk_not(a.mk_le(t, a.mk_numeral(k, true))));
        }
        ast_pp_util visitor(m);
        visitor.collect(fmls);
        visitor.display_decls(out);
        visitor.display_asserts(out, fmls, true);
        out << "(check-sat)\n";            
    }

    lbool check_lia() {
        TRACE("arith",);
        if (m.canceled()) {
            TRACE("arith", tout << "canceled\n";);
            return l_undef;
        }
        lbool lia_check = l_undef;
        if (!check_idiv_bounds()) {
            return l_false;
        }
        switch (m_lia->check(&m_explanation)) {
        case lp::lia_move::sat:
            lia_check = l_true;
            break;

        case lp::lia_move::branch: {
            TRACE("arith", tout << "branch\n";);
            app_ref b(m);
            bool u = m_lia->is_upper();
            auto const & k = m_lia->get_offset();
            if (0 == ctx().get_random_value() % 2) {
                b = mk_bound(m_lia->get_term(), k, !u);
            }
            else {
                b = mk_bound(m_lia->get_term(), u ? k - 1 : k + 1, u);
            }
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_or(b, m.mk_not(b));
                th.log_axiom_instantiation(body);
                m.trace_stream() << "[end-of-instance]\n";
            }
            IF_VERBOSE(4, verbose_stream() << "branch " << b << "\n";);
            // branch on term >= k + 1
            // branch on term <= k
            // TBD: ctx().force_phase(ctx().get_literal(b));
            // at this point we have a new unassigned atom that the 
            // SAT core assigns a value to
            lia_check = l_false;
            ++m_stats.m_branch;
            break;
        }
        case lp::lia_move::cut: {
            TRACE("arith", tout << "cut\n";);
            ++m_stats.m_gomory_cuts;
            // m_explanation implies term <= k
            app_ref b = mk_bound(m_lia->get_term(), m_lia->get_offset(), !m_lia->is_upper());
            if (m.has_trace_stream()) {
                th.log_axiom_instantiation(b);
                m.trace_stream() << "[end-of-instance]\n";
            }
            IF_VERBOSE(4, verbose_stream() << "cut " << b << "\n");
            TRACE("arith", dump_cut_lemma(tout, m_lia->get_term(), m_lia->get_offset(), m_explanation, m_lia->is_upper()););
            m_eqs.reset();
            m_core.reset();
            m_params.reset();
            for (auto const& ev : m_explanation) {
                if (!ev.first.is_zero()) { 
                    set_evidence(ev.second);
                }
            }
            literal lit(ctx().get_bool_var(b), false);
            TRACE("arith", 
                  ctx().display_lemma_as_smt_problem(tout << "new cut:\n", m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), lit);
                  display(tout););
            assign(lit);
            lia_check = l_false;
            break;
        }
        case lp::lia_move::conflict:
            TRACE("arith", tout << "conflict\n";);
            // ex contains unsat core
            set_conflict();
            return l_false;
        case lp::lia_move::undef:
            TRACE("arith", tout << "lia undef\n";);
            lia_check = l_undef;
            break;
        case lp::lia_move::continue_with_check:
            lia_check = l_undef;
            break;
        default:
            UNREACHABLE();
        }
        return lia_check;
    }

    lbool check_aftermath_nra(lbool r) {
        m_a1 = alloc(scoped_anum, m_nra->am());
        m_a2 = alloc(scoped_anum, m_nra->am());
        switch (r) {
        case l_false:
            set_conflict();
            break;
        case l_true:
            m_use_nra_model = true;
            if (assume_eqs()) {
                return l_false;
            }
            break;
        case l_undef:
            TRACE("arith", tout << "nra-undef\n";);
        default:
            break;
        }
        return r;
    }

    nla::lemma m_lemma;
 
    void false_case_of_check_nla() {
        literal_vector core;
        for (auto const& ineq : m_lemma.ineqs()) {
            bool is_lower = true, pos = true, is_eq = false;
            switch (ineq.m_cmp) {
            case lp::LE: is_lower = false; pos = false;  break;
            case lp::LT: is_lower = true;  pos = true; break;
            case lp::GE: is_lower = true;  pos = false;  break;
            case lp::GT: is_lower = false; pos = true; break;
            case lp::EQ: is_eq = true; pos = false; break;
            case lp::NE: is_eq = true; pos = true; break;
            default: UNREACHABLE();
            }
            TRACE("arith", tout << "is_lower: " << is_lower << " pos " << pos << "\n";);
            app_ref atom(m);
            // TBD utility: lp::lar_term term = mk_term(ineq.m_poly);
            // then term is used instead of ineq.m_term
            if (is_eq) {
                atom = mk_eq(ineq.m_term, ineq.m_rs);
            }
            else {
                // create term >= 0 (or term <= 0)
                atom = mk_bound(ineq.m_term, ineq.m_rs, is_lower);
            }
            literal lit(ctx().get_bool_var(atom), pos);
            core.push_back(~lit);
        }
        set_conflict_or_lemma(core, false);
    }
    
    lbool check_aftermath_nla(lbool r, const vector<nla::lemma>& lv) {
        switch (r) {
        case l_false: {
            m_stats.m_nla_lemmas += lv.size();
            for(const nla::lemma & l : lv) {
                m_lemma = l; //todo avoid the copy
                m_explanation = l.expl();
                m_stats.m_nla_explanations += static_cast<unsigned>(l.expl().size());
                false_case_of_check_nla();
            }
            break;
        }
        case l_true:
            if (assume_eqs()) {
                return l_false;
            }
            break;
        case l_undef:
            break;
        }
        return r;
    }

    lbool check_nra() {
        m_use_nra_model = false;
        if (m.canceled()) {
            TRACE("arith", tout << "canceled\n";);
            return l_undef;
        }
        if (!m_nra && !m_nla) return l_true;
        if (!m_switcher.need_check()) return l_true;
        m_a1 = nullptr; m_a2 = nullptr;
        if (m_nra) {
            m_explanation.clear();
            return check_aftermath_nra(m_nra->check(m_explanation));
        }
        vector<nla::lemma> lv;
        return check_aftermath_nla(m_nla->check(lv), lv);
    }

    /**
       \brief We must redefine this method, because theory of arithmetic contains
       underspecified operators such as division by 0.
       (/ a b) is essentially an uninterpreted function when b = 0.
       Thus, 'a' must be considered a shared var if it is the child of an underspecified operator.

       if merge(a / b, x + y) and a / b is root, then x + y become shared and all z + u in equivalence class of x + y.
                      

       TBD: when the set of underspecified subterms is small, compute the shared variables below it.
       Recompute the set if there are merges that invalidate it.
       Use the set to determine if a variable is shared.
    */
    bool is_shared(theory_var v) const {
        if (m_underspecified.empty()) {
            return false;
        }
        enode * n      = get_enode(v);
        enode * r      = n->get_root();
        unsigned usz   = m_underspecified.size();
        TRACE("shared", tout << ctx().get_scope_level() << " " <<  v << " " << r->get_num_parents() << "\n";);
        if (r->get_num_parents() > 2*usz) {
            for (unsigned i = 0; i < usz; ++i) {
                app* u = m_underspecified[i];
                unsigned sz = u->get_num_args();
                for (unsigned j = 0; j < sz; ++j) {
                    if (ctx().get_enode(u->get_arg(j))->get_root() == r) {
                        return true;
                    }
                }
            }
        }
        else {
            for (enode * parent : r->get_const_parents()) {
                if (is_underspecified(parent->get_owner())) {
                    return true;
                }
            }
        }
        return false;
    }

    bool can_propagate() {
        return m_asserted_atoms.size() > m_asserted_qhead;
    }

    void propagate() {
        flush_bound_axioms();
        if (!can_propagate()) {
            return;
        }
        while (m_asserted_qhead < m_asserted_atoms.size() && !ctx().inconsistent()) {
            bool_var bv  = m_asserted_atoms[m_asserted_qhead].m_bv;
            bool is_true = m_asserted_atoms[m_asserted_qhead].m_is_true;                
            m_to_check.push_back(bv);
            lp_api::bound& b = *m_bool_var2bound.find(bv);
            assert_bound(bv, is_true, b);                
            ++m_asserted_qhead;
        }
        if (ctx().inconsistent()) {
            m_to_check.reset();
            return;
        }

        lbool lbl = make_feasible();
        if (m.canceled())
            return;
        
        switch(lbl) {
        case l_false:
            TRACE("arith", tout << "propagation conflict\n";);
            get_infeasibility_explanation_and_set_conflict();
            break;
        case l_true:
            propagate_basic_bounds();
            propagate_bounds_with_lp_solver();
            break;
        case l_undef:
            break;
        }
            
    }

    bool should_propagate() {
        return BP_NONE != propagation_mode();
    }

    // void update_propagation_threshold(bool  made_progress) {
    //      if (made_progress) {
    //         m_propagation_delay = std::max(1u, m_propagation_delay-1u);
    //     }
    //     else {
    //         m_propagation_delay += 2;
    //     }
    // }

    void propagate_bounds_with_lp_solver() {
        if (!should_propagate()) 
            return;
        local_bound_propagator bp(*this);

        lp().propagate_bounds_for_touched_rows(bp);
        if (m.canceled()) {
            return;
        }

        if (is_infeasible()) {
            get_infeasibility_explanation_and_set_conflict();
        }
        else {
            for (unsigned i = 0; !m.canceled() && !ctx().inconsistent() && i < bp.m_ibounds.size(); ++i) {
                propagate_lp_solver_bound(bp.m_ibounds[i]);
            }
        }
    }

    bool bound_is_interesting(unsigned vi, lp::lconstraint_kind kind, const rational & bval) const {
        theory_var v = lp().local_to_external(vi);
        if (v == null_theory_var) {
            return false;
        }
        if (m_unassigned_bounds[v] == 0 || m_bounds.size() <= static_cast<unsigned>(v)) {
            return false;
        }
        for (lp_api::bound* b : m_bounds[v]) {
            if (ctx().get_assignment(b->get_bv()) == l_undef &&
                null_literal != is_bound_implied(kind, bval, *b)) {
                return true;
            }
        }
        return false;
    }

    struct local_bound_propagator: public lp::lp_bound_propagator {
        imp & m_imp;
        local_bound_propagator(imp& i) : lp_bound_propagator(*i.m_solver), m_imp(i) {}

        bool bound_is_interesting(unsigned j, lp::lconstraint_kind kind, const rational & v) override {
            return m_imp.bound_is_interesting(j, kind, v);
        }

        void consume(rational const& v, lp::constraint_index j) override {
            m_imp.set_evidence(j);
            m_imp.m_explanation.push_justification(j, v);
        }
    };

        
    void propagate_lp_solver_bound(lp::implied_bound& be) {
        lpvar vi = be.m_j;
        theory_var v = lp().local_to_external(vi);

        if (v == null_theory_var) return;
        TRACE("arith", tout << "v" << v << " " << be.kind() << " " << be.m_bound << "\n";
              // if (m_unassigned_bounds[v] == 0) lp().print_bound_evidence(be, tout);
              );

            
        if (m_unassigned_bounds[v] == 0 || m_bounds.size() <= static_cast<unsigned>(v)) {
            TRACE("arith", tout << "return\n";);
            return;
        }
        lp_bounds const& bounds = m_bounds[v];
        bool first = true;
        for (unsigned i = 0; i < bounds.size(); ++i) {
            lp_api::bound* b = bounds[i];
            if (ctx().get_assignment(b->get_bv()) != l_undef) {
                continue;
            }
            literal lit = is_bound_implied(be.kind(), be.m_bound, *b);
            if (lit == null_literal) {
                continue;
            }
            TRACE("arith", tout << lit << " bound: " << *b << " first: " << first << "\n";);

            lp().settings().stats().m_num_of_implied_bounds ++;
            if (first) {
                first = false;
                m_core.reset();
                m_eqs.reset();
                m_params.reset();
                m_explanation.clear();
                local_bound_propagator bp(*this);
                lp().explain_implied_bound(be, bp);
            }
            CTRACE("arith", m_unassigned_bounds[v] == 0, tout << "missed bound\n";);
            updt_unassigned_bounds(v, -1);
            TRACE("arith",
                  ctx().display_literals_verbose(tout, m_core);
                  tout << "\n --> ";
                  ctx().display_literal_verbose(tout, lit);
                  tout << "\n";
                  display_evidence(tout, m_explanation);
                  lp().print_implied_bound(be, tout);
                  );
            DEBUG_CODE(
                for (auto& lit : m_core) {
                    VERIFY(ctx().get_assignment(lit) == l_true);
                });
            ++m_stats.m_bound_propagations1;
            assign(lit);
        }
    }

    literal_vector m_core2;

    void assign(literal lit) {
        //        SASSERT(validate_assign(lit));
        dump_assign(lit);
        if (m_core.size() < small_lemma_size() && m_eqs.empty()) {
            m_core2.reset();
            for (auto const& c : m_core) {
                m_core2.push_back(~c);
            }
            m_core2.push_back(lit);
            justification * js = nullptr;
            if (proofs_enabled()) {
                js = alloc(theory_lemma_justification, get_id(), ctx(), m_core2.size(), m_core2.c_ptr(),
                           m_params.size(), m_params.c_ptr());
            }
            ctx().mk_clause(m_core2.size(), m_core2.c_ptr(), js, CLS_TH_LEMMA, nullptr);
        }
        else {
            ctx().assign(
                lit, ctx().mk_justification(
                    ext_theory_propagation_justification(
                        get_id(), ctx().get_region(), m_core.size(), m_core.c_ptr(), 
                        m_eqs.size(), m_eqs.c_ptr(), lit, m_params.size(), m_params.c_ptr())));            
        }
    }

    literal is_bound_implied(lp::lconstraint_kind k, rational const& value, lp_api::bound const& b) const {
        if ((k == lp::LE || k == lp::LT) && b.get_bound_kind() == lp_api::upper_t && value <= b.get_value()) {
            TRACE("arith", tout << "v <= value <= b.get_value() => v <= b.get_value() \n";);
            return literal(b.get_bv(), false);
        }
        if ((k == lp::GE || k == lp::GT) && b.get_bound_kind() == lp_api::lower_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value <= v => b.get_value() <= v \n";);
            return literal(b.get_bv(), false);
        }
        if (k == lp::LE && b.get_bound_kind() == lp_api::lower_t && value < b.get_value()) {
            TRACE("arith", tout << "v <= value < b.get_value() => v < b.get_value()\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::LT && b.get_bound_kind() == lp_api::lower_t && value <= b.get_value()) {
            TRACE("arith", tout << "v < value <= b.get_value() => v < b.get_value()\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::GE && b.get_bound_kind() == lp_api::upper_t && b.get_value() < value) {
            TRACE("arith", tout << "b.get_value() < value <= v => b.get_value() < v\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::GT && b.get_bound_kind() == lp_api::upper_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value < v => b.get_value() < v\n";);
            return literal(b.get_bv(), true);
        }

        return null_literal;
    }

    void mk_bound_axioms(lp_api::bound& b) {
        if (!ctx().is_searching()) {
            //
            // NB. We make an assumption that user push calls propagation 
            // before internal scopes are pushed. This flushes all newly 
            // asserted atoms into the right context.
            //
            m_new_bounds.push_back(&b);
            return;
        }
        theory_var v = b.get_var();
        lp_api::bound_kind kind1 = b.get_bound_kind();
        rational const& k1 = b.get_value();
        lp_bounds & bounds = m_bounds[v];

        lp_api::bound* end = nullptr;
        lp_api::bound* lo_inf = end, *lo_sup = end;
        lp_api::bound* hi_inf = end, *hi_sup = end;
            
        for (lp_api::bound* other : bounds) {
            if (other == &b) continue;
            if (b.get_bv() == other->get_bv()) continue;
            lp_api::bound_kind kind2 = other->get_bound_kind();
            rational const& k2 = other->get_value();
            if (k1 == k2 && kind1 == kind2) {
                // the bounds are equivalent.
                continue;
            }

            SASSERT(k1 != k2 || kind1 != kind2);
            if (kind2 == lp_api::lower_t) {
                if (k2 < k1) {
                    if (lo_inf == end || k2 > lo_inf->get_value()) {
                        lo_inf = other;
                    }
                }
                else if (lo_sup == end || k2 < lo_sup->get_value()) {
                    lo_sup = other;
                }
            }
            else if (k2 < k1) {
                if (hi_inf == end || k2 > hi_inf->get_value()) {
                    hi_inf = other;
                }
            }
            else if (hi_sup == end || k2 < hi_sup->get_value()) {
                hi_sup = other;
            }
        }        
        if (lo_inf != end) mk_bound_axiom(b, *lo_inf);
        if (lo_sup != end) mk_bound_axiom(b, *lo_sup);
        if (hi_inf != end) mk_bound_axiom(b, *hi_inf);
        if (hi_sup != end) mk_bound_axiom(b, *hi_sup);
    }


    void mk_bound_axiom(lp_api::bound& b1, lp_api::bound& b2) {
        theory_var v = b1.get_var();
        literal   l1(b1.get_bv());
        literal   l2(b2.get_bv());
        rational const& k1 = b1.get_value();
        rational const& k2 = b2.get_value();
        lp_api::bound_kind kind1 = b1.get_bound_kind();
        lp_api::bound_kind kind2 = b2.get_bound_kind();
        bool v_is_int = b1.is_int();
        SASSERT(v == b2.get_var());
        if (k1 == k2 && kind1 == kind2) return;
        SASSERT(k1 != k2 || kind1 != kind2);
        parameter coeffs[3] = { parameter(symbol("farkas")), 
                                parameter(rational(1)), parameter(rational(1)) };
            
        if (kind1 == lp_api::lower_t) {
            if (kind2 == lp_api::lower_t) {
                if (k2 <= k1) {
                    mk_clause(~l1, l2, 3, coeffs);
                }
                else {
                    mk_clause(l1, ~l2, 3, coeffs);
                }
            }
            else if (k1 <= k2) {
                // k1 <= k2, k1 <= x or x <= k2
                mk_clause(l1, l2, 3, coeffs);
            }
            else {
                // k1 > hi_inf, k1 <= x => ~(x <= hi_inf)
                mk_clause(~l1, ~l2, 3, coeffs);
                if (v_is_int && k1 == k2 + rational(1)) {
                    // k1 <= x or x <= k1-1
                    mk_clause(l1, l2, 3, coeffs);
                }
            }
        }
        else if (kind2 == lp_api::lower_t) {
            if (k1 >= k2) {
                // k1 >= lo_inf, k1 >= x or lo_inf <= x
                mk_clause(l1, l2, 3, coeffs);
            }
            else {
                // k1 < k2, k2 <= x => ~(x <= k1)
                mk_clause(~l1, ~l2, 3, coeffs); 
                if (v_is_int && k1 == k2 - rational(1)) {
                    // x <= k1 or k1+l <= x
                    mk_clause(l1, l2, 3, coeffs);
                }
                    
            }
        }
        else {
            // kind1 == A_UPPER, kind2 == A_UPPER
            if (k1 >= k2) {
                // k1 >= k2, x <= k2 => x <= k1
                mk_clause(l1, ~l2, 3, coeffs);
            }
            else {
                // k1 <= hi_sup , x <= k1 =>  x <= hi_sup
                mk_clause(~l1, l2, 3, coeffs);
            }
        }        
    }

    typedef lp_bounds::iterator iterator;

    void flush_bound_axioms() {
        CTRACE("arith", !m_new_bounds.empty(), tout << "flush bound axioms\n";);

        while (!m_new_bounds.empty()) {
            lp_bounds atoms;            
            atoms.push_back(m_new_bounds.back());
            m_new_bounds.pop_back();
            theory_var v = atoms.back()->get_var();
            for (unsigned i = 0; i < m_new_bounds.size(); ++i) {
                if (m_new_bounds[i]->get_var() == v) {
                    atoms.push_back(m_new_bounds[i]);
                    m_new_bounds[i] = m_new_bounds.back();
                    m_new_bounds.pop_back();
                    --i;
                }
            }            
            CTRACE("arith_verbose", !atoms.empty(),  
                   for (unsigned i = 0; i < atoms.size(); ++i) {
                       atoms[i]->display(tout); tout << "\n";
                   });
            lp_bounds occs(m_bounds[v]);
                
            std::sort(atoms.begin(), atoms.end(), compare_bounds());
            std::sort(occs.begin(), occs.end(), compare_bounds());
                
            iterator begin1 = occs.begin();
            iterator begin2 = occs.begin();
            iterator end = occs.end();
            begin1 = first(lp_api::lower_t, begin1, end);
            begin2 = first(lp_api::upper_t, begin2, end);
                
            iterator lo_inf = begin1, lo_sup = begin1;
            iterator hi_inf = begin2, hi_sup = begin2;
            bool flo_inf, fhi_inf, flo_sup, fhi_sup;
            ptr_addr_hashtable<lp_api::bound> visited;
            for (unsigned i = 0; i < atoms.size(); ++i) {
                lp_api::bound* a1 = atoms[i];
                iterator lo_inf1 = next_inf(a1, lp_api::lower_t, lo_inf, end, flo_inf);
                iterator hi_inf1 = next_inf(a1, lp_api::upper_t, hi_inf, end, fhi_inf);
                iterator lo_sup1 = next_sup(a1, lp_api::lower_t, lo_sup, end, flo_sup);
                iterator hi_sup1 = next_sup(a1, lp_api::upper_t, hi_sup, end, fhi_sup);
                if (lo_inf1 != end) lo_inf = lo_inf1; 
                if (lo_sup1 != end) lo_sup = lo_sup1; 
                if (hi_inf1 != end) hi_inf = hi_inf1; 
                if (hi_sup1 != end) hi_sup = hi_sup1; 
                if (!flo_inf) lo_inf = end;
                if (!fhi_inf) hi_inf = end;
                if (!flo_sup) lo_sup = end;
                if (!fhi_sup) hi_sup = end;
                visited.insert(a1);
                if (lo_inf1 != end && lo_inf != end && !visited.contains(*lo_inf)) mk_bound_axiom(*a1, **lo_inf);
                if (lo_sup1 != end && lo_sup != end && !visited.contains(*lo_sup)) mk_bound_axiom(*a1, **lo_sup);
                if (hi_inf1 != end && hi_inf != end && !visited.contains(*hi_inf)) mk_bound_axiom(*a1, **hi_inf);
                if (hi_sup1 != end && hi_sup != end && !visited.contains(*hi_sup)) mk_bound_axiom(*a1, **hi_sup);
            }                            
        }
    }

    struct compare_bounds {
        bool operator()(lp_api::bound* a1, lp_api::bound* a2) const { return a1->get_value() < a2->get_value(); }
    };


    lp_bounds::iterator first(
        lp_api::bound_kind kind, 
        iterator it, 
        iterator end) {
        for (; it != end; ++it) {
            lp_api::bound* a = *it;
            if (a->get_bound_kind() == kind) return it;
        }
        return end;
    }

    lp_bounds::iterator next_inf(
        lp_api::bound* a1, 
        lp_api::bound_kind kind, 
        iterator it, 
        iterator end,
        bool& found_compatible) {
        rational const & k1(a1->get_value());
        iterator result = end;
        found_compatible = false;
        for (; it != end; ++it) {
            lp_api::bound * a2 = *it;            
            if (a1 == a2) continue;
            if (a2->get_bound_kind() != kind) continue;
            rational const & k2(a2->get_value());
            found_compatible = true;
            if (k2 <= k1) {
                result = it;
            }
            else {
                break;
            }
        }
        return result;
    }

    lp_bounds::iterator next_sup(
        lp_api::bound* a1, 
        lp_api::bound_kind kind, 
        iterator it, 
        iterator end,
        bool& found_compatible) {
        rational const & k1(a1->get_value());
        found_compatible = false;
        for (; it != end; ++it) {
            lp_api::bound * a2 = *it;            
            if (a1 == a2) continue;
            if (a2->get_bound_kind() != kind) continue;
            rational const & k2(a2->get_value());
            found_compatible = true;
            if (k1 < k2) {
                return it;
            }
        }
        return end;
    }

    void propagate_basic_bounds() {
        for (auto const& bv : m_to_check) {                
            lp_api::bound& b = *m_bool_var2bound.find(bv);
            propagate_bound(bv, ctx().get_assignment(bv) == l_true, b);
            if (ctx().inconsistent()) break;

        }
        m_to_check.reset();
    }
        
    // for glb lo': lo' < lo:
    //   lo <= x -> lo' <= x 
    //   lo <= x -> ~(x <= lo')
    // for lub hi': hi' > hi
    //   x <= hi -> x <= hi'
    //   x <= hi -> ~(x >= hi')

    void propagate_bound(bool_var bv, bool is_true, lp_api::bound& b) {
        if (BP_NONE == propagation_mode()) {
            return;
        }
        lp_api::bound_kind k = b.get_bound_kind();
        theory_var v = b.get_var();
        inf_rational val = b.get_value(is_true);
        lp_bounds const& bounds = m_bounds[v];
        SASSERT(!bounds.empty());
        if (bounds.size() == 1) return;
        if (m_unassigned_bounds[v] == 0) return;
        bool v_is_int = b.is_int();
        literal lit1(bv, !is_true);
        literal lit2 = null_literal;
        bool find_glb = (is_true == (k == lp_api::lower_t));
        TRACE("arith", tout << "find_glb: " << find_glb << " is_true: " << is_true << " k: " << k << " is_lower: " << (k == lp_api::lower_t) << "\n";);
        if (find_glb) {
            rational glb;
            lp_api::bound* lb = nullptr;
            for (lp_api::bound* b2 : bounds) {
                if (b2 == &b) continue;
                rational const& val2 = b2->get_value();
                if (((is_true || v_is_int) ? val2 < val : val2 <= val) && (!lb || glb < val2)) {
                    lb = b2;
                    glb = val2;
                }
            }
            if (!lb) return;
            bool sign = lb->get_bound_kind() != lp_api::lower_t;
            lit2 = literal(lb->get_bv(), sign);                    
        }
        else {
            rational lub;
            lp_api::bound* ub = nullptr;
            for (lp_api::bound* b2 : bounds) {
                if (b2 == &b) continue;
                rational const& val2 = b2->get_value();
                if (((is_true || v_is_int) ? val < val2 : val <= val2) && (!ub || val2 < lub)) {
                    ub = b2;
                    lub = val2;
                }
            }
            if (!ub) return;
            bool sign = ub->get_bound_kind() != lp_api::upper_t;
            lit2 = literal(ub->get_bv(), sign);
        }
        TRACE("arith", 
              ctx().display_literal_verbose(tout, lit1);
              ctx().display_literal_verbose(tout << " => ", lit2);
              tout << "\n";);
        updt_unassigned_bounds(v, -1);
        ++m_stats.m_bound_propagations2;
        m_params.reset();
        m_core.reset();
        m_eqs.reset();
        m_core.push_back(lit1);
        m_params.push_back(parameter(m_farkas));
        m_params.push_back(parameter(rational(1)));
        m_params.push_back(parameter(rational(1)));
        assign(lit2);
        ++m_stats.m_bounds_propagations;
    }

    svector<lpvar> m_todo_vars;

    void add_use_lists(lp_api::bound* b) {
        theory_var v = b->get_var();
        lpvar vi = register_theory_var_in_lar_solver(v);
        if (!lp().is_term(vi)) {
            return;
        }
        m_todo_vars.push_back(vi);
        while (!m_todo_vars.empty()) {
            vi = m_todo_vars.back();
            m_todo_vars.pop_back();
            lp::lar_term const& term = lp().get_term(vi);
            for (auto const& p : term) {
                lpvar wi = p.var();
                if (lp().is_term(wi)) {
                    m_todo_vars.push_back(wi);
                }
                else {
                    unsigned w = lp().local_to_external(wi);
                    m_use_list.reserve(w + 1, ptr_vector<lp_api::bound>());
                    m_use_list[w].push_back(b);
                }
            }
        }
    }

    void del_use_lists(lp_api::bound* b) {
        theory_var v = b->get_var();
        lpvar vi = get_lpvar(v);
        if (!lp().is_term(vi)) {
            return;
        }
        m_todo_vars.push_back(vi);
        while (!m_todo_vars.empty()) {
            vi = m_todo_vars.back();
            m_todo_vars.pop_back();
            lp::lar_term const& term = lp().get_term(vi);
            for (auto const& coeff : term) {
                lpvar wi = coeff.var();
                if (lp().is_term(wi)) {
                    m_todo_vars.push_back(wi);
                }
                else {
                    unsigned w = lp().local_to_external(wi);
                    SASSERT(m_use_list[w].back() == b);
                    m_use_list[w].pop_back();
                }
            }
        }
    }

    //
    // propagate bounds to compound terms
    // The idea is that if bounds on all variables in an inequality ax + by + cz >= k
    // have been assigned we may know the truth value of the inequality by using simple
    // bounds propagation.
    // 
    void propagate_bound_compound(bool_var bv, bool is_true, lp_api::bound& b) {
        theory_var v = b.get_var();
        TRACE("arith", tout << mk_pp(get_owner(v), m) << "\n";);
        if (static_cast<unsigned>(v) >= m_use_list.size()) {
            return;
        }
        for (auto const& vb : m_use_list[v]) {
            if (ctx().get_assignment(vb->get_bv()) != l_undef) {
                TRACE("arith_verbose", display_bound(tout << "assigned ", *vb) << "\n";);
                continue;
            }
            inf_rational r;
            // x + y
            // x >= 0, y >= 1 -> x + y >= 1
            // x <= 0, y <= 2 -> x + y <= 2
            literal lit = null_literal;
            if (lp_api::lower_t == vb->get_bound_kind()) {
                if (get_glb(*vb, r) && r >= vb->get_value()) {        // vb is assigned true
                    lit = literal(vb->get_bv(), false);
                }
                else if (get_lub(*vb, r) && r < vb->get_value()) {    // vb is assigned false
                    lit = literal(vb->get_bv(), true);
                }
            }
            else {                     
                if (get_glb(*vb, r) && r > vb->get_value()) {         // VB <= value < val(VB)
                    lit = literal(vb->get_bv(), true);
                }
                else if (get_lub(*vb, r) && r <= vb->get_value()) {   // val(VB) <= value
                    lit = literal(vb->get_bv(), false);
                }
            }                
                
            if (lit != null_literal) {
                TRACE("arith",
                      ctx().display_literals_verbose(tout, m_core);
                      tout << "\n --> ";
                      ctx().display_literal_verbose(tout, lit);
                      tout << "\n";
                      );
                

                assign(lit);
            }
            else {
                TRACE("arith_verbose", display_bound(tout << "skip ", *vb) << "\n";);
            }
        }
    }

    bool get_lub(lp_api::bound const& b, inf_rational& lub) {
        return get_bound(b, lub, true);
    }

    bool get_glb(lp_api::bound const& b, inf_rational& glb) {
        return get_bound(b, glb, false);
    }

    std::ostream& display_bound(std::ostream& out, lp_api::bound const& b) {
        return out << mk_pp(ctx().bool_var2expr(b.get_bv()), m);
    }

    bool get_bound(lp_api::bound const& b, inf_rational& r, bool is_lub) {
        m_core.reset();
        m_eqs.reset();
        m_params.reset();
        r.reset();
        theory_var v = b.get_var();
        lpvar vi = get_lpvar(v);
        SASSERT(m_solver->is_term(vi));
        lp::lar_term const& term = m_solver->get_term(vi);
        for (auto const mono : term) {
            lp::var_index wi = mono.var();
            lp::constraint_index ci;
            rational value;
            bool is_strict;
            if (lp().is_term(wi)) {
                return false;
            }
            if (mono.coeff().is_neg() == is_lub) {
                // -3*x ... <= lub based on lower bound for x.
                if (!lp().has_lower_bound(wi, ci, value, is_strict)) {
                    return false;
                }
                if (is_strict) {
                    r += inf_rational(rational::zero(), mono.coeff().is_pos());
                }
            }
            else {
                if (!lp().has_upper_bound(wi, ci, value, is_strict)) {
                    return false;
                }
                if (is_strict) {
                    r += inf_rational(rational::zero(), mono.coeff().is_pos());
                }
            }                
            r += value * mono.coeff();
            set_evidence(ci);                    
        }
        TRACE("arith_verbose", tout << (is_lub?"lub":"glb") << " is " << r << "\n";);
        return true;
    }

    lp::lconstraint_kind bound2constraint_kind(bool is_int, lp_api::bound_kind bk, bool is_true) {
        switch (bk) {
        case lp_api::lower_t:
            return is_true ? lp::GE : (is_int ? lp::LE : lp::LT);
        case lp_api::upper_t:
            return is_true ? lp::LE : (is_int ? lp::GE : lp::GT);
        }
        UNREACHABLE();
        return lp::EQ;
    }

    void assert_bound(bool_var bv, bool is_true, lp_api::bound& b) {
        lp::constraint_index ci = b.get_constraint(is_true);
        m_solver->activate(ci);
        if (is_infeasible()) {
            return;
        }
        lp::lconstraint_kind k = bound2constraint_kind(b.is_int(), b.get_bound_kind(), is_true);
        if (k == lp::LT || k == lp::LE) {
            ++m_stats.m_assert_lower;
        }
        else {
            ++m_stats.m_assert_upper;
        }
        propagate_eqs(b.lp_solver_var(), ci, k, b);
    }

    lp_api::bound* mk_var_bound(bool_var bv, theory_var v, lp_api::bound_kind bk, rational const& bound) {
        scoped_internalize_state st(*this);
        st.vars().push_back(v);
        st.coeffs().push_back(rational::one());
        init_left_side(st);
        lp::constraint_index cT, cF;
        bool v_is_int = is_int(v);
        auto vi = register_theory_var_in_lar_solver(v);

        lp::lconstraint_kind kT = bound2constraint_kind(v_is_int, bk, true);
        lp::lconstraint_kind kF = bound2constraint_kind(v_is_int, bk, false);
        
        cT = m_solver->mk_var_bound(vi, kT, bound);
        if (v_is_int) {
            rational boundF = (bk == lp_api::lower_t) ? bound - 1 : bound + 1;
            cF = m_solver->mk_var_bound(vi, kF, boundF);
        }
        else {
            cF = m_solver->mk_var_bound(vi, kF, bound);
        }
        add_ineq_constraint(cT, literal(bv, false));
        add_ineq_constraint(cF, literal(bv, true));

        return alloc(lp_api::bound, bv, v, vi, v_is_int, bound, bk, cT, cF);
    }

    //
    // fixed equalities.
    // A fixed equality is inferred if there are two variables v1, v2 whose
    // upper and lower bounds coincide.
    // Then the equality v1 == v2 is propagated to the core.
    // 

    typedef std::pair<lp::constraint_index, rational> constraint_bound;
    vector<constraint_bound>        m_lower_terms;
    vector<constraint_bound>        m_upper_terms;
    typedef std::pair<rational, bool> value_sort_pair;
    typedef pair_hash<obj_hash<rational>, bool_hash> value_sort_pair_hash;
    typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
    value2var               m_fixed_var_table;

    void propagate_eqs(lpvar vi, lp::constraint_index ci, lp::lconstraint_kind k, lp_api::bound& b) {
        if (propagate_eqs()) {
            rational const& value = b.get_value();
            if (k == lp::GE) {
                if (set_lower_bound(vi, ci, value) && has_upper_bound(vi, ci, value)) {
                    fixed_var_eh(b.get_var(), value);
                }
            }
            else if (k == lp::LE) {
                if (set_upper_bound(vi, ci, value) && has_lower_bound(vi, ci, value)) {
                    fixed_var_eh(b.get_var(), value);
                }
            }
        }
    }

    bool dump_lemmas() const { return m_arith_params.m_arith_dump_lemmas; }

    bool propagate_eqs() const { return m_arith_params.m_arith_propagate_eqs && m_num_conflicts < m_arith_params.m_arith_propagation_threshold; }

    bound_prop_mode propagation_mode() const { return m_num_conflicts < m_arith_params.m_arith_propagation_threshold ? m_arith_params.m_arith_bound_prop : BP_NONE; }

    unsigned small_lemma_size() const { return m_arith_params.m_arith_small_lemma_size; }

    bool proofs_enabled() const { return m.proofs_enabled(); }

    bool set_upper_bound(lpvar vi, lp::constraint_index ci, rational const& v) { return set_bound(vi, ci, v, false);  }

    bool set_lower_bound(lpvar vi, lp::constraint_index ci, rational const& v) { return set_bound(vi, ci, v, true);   }

    vector<constraint_bound> m_history;
    template<typename Ctx, typename T, bool CallDestructors=true>
    class history_trail : public trail<Ctx> {
        vector<T, CallDestructors> & m_dst;
        unsigned                     m_idx;
        vector<T, CallDestructors> & m_hist;
    public:
        history_trail(vector<T, CallDestructors> & v, unsigned idx, vector<T, CallDestructors> & hist):
            m_dst(v),
            m_idx(idx),
            m_hist(hist) {}

        ~history_trail() override {
        }

        void undo(Ctx & ctx) override {
            m_dst[m_idx] = m_hist.back();
            m_hist.pop_back();
        }
    };


    bool set_bound(lpvar vi, lp::constraint_index ci, rational const& v, bool is_lower) {

        if (lp().is_term(vi)) {
            lpvar ti = lp().adjust_term_index(vi);
            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            if (vec.size() <= ti) {
                vec.resize(ti + 1, constraint_bound(UINT_MAX, rational()));
            }
            constraint_bound& b = vec[ti];
            if (b.first == UINT_MAX || (is_lower? b.second < v : b.second > v)) {
                TRACE("arith", tout << "tighter bound " << vi << "\n";);
                m_history.push_back(vec[ti]);
                ctx().push_trail(history_trail<context, constraint_bound>(vec, ti, m_history));
                b.first = ci;
                b.second = v;
            }
            return true;
        }
        else {
            TRACE("arith", tout << "not a term " << vi << "\n";);
            // m_solver already tracks bounds on proper variables, but not on terms.
            bool is_strict = false;
            rational b;
            if (is_lower) {
                return lp().has_lower_bound(vi, ci, b, is_strict) && !is_strict && b == v;
            }
            else {
                return lp().has_upper_bound(vi, ci, b, is_strict) && !is_strict && b == v;
            }
            
        }
    }

    bool var_has_bound(lpvar vi, bool is_lower) {
        bool is_strict = false;
        rational b;
        lp::constraint_index ci;
        if (is_lower) {
            return lp().has_lower_bound(vi, ci, b, is_strict);
        }
        else {
            return lp().has_upper_bound(vi, ci, b, is_strict);
        }        
    }

    bool has_upper_bound(lpvar vi, lp::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, false); }

    bool has_lower_bound(lpvar vi, lp::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, true); }
       
    bool has_bound(lpvar vi, lp::constraint_index& ci, rational const& bound, bool is_lower) {
        if (lp().is_term(vi)) {
            theory_var v = lp().local_to_external(vi);
            rational val;
            TRACE("arith", tout << vi << " " << v << "\n";);
            if (v != null_theory_var && a.is_numeral(get_owner(v), val) && bound == val) {
                ci = UINT_MAX;
                return bound == val;
            }

            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            lpvar ti = lp().adjust_term_index(vi);
            if (vec.size() > ti) {
                constraint_bound& b = vec[ti];
                ci = b.first;
                return ci != UINT_MAX && bound == b.second;
            }
            else {
                return false;
            }
        }
        else {
            bool is_strict = false;
            rational b;
            if (is_lower) {
                return lp().has_lower_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
            }
            else {
                return lp().has_upper_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
            }
        }
    }


    bool is_equal(theory_var x, theory_var y) const { return get_enode(x)->get_root() == get_enode(y)->get_root(); }


    void fixed_var_eh(theory_var v1, rational const& bound) {
        theory_var v2;
        value_sort_pair key(bound, is_int(v1));
        if (m_fixed_var_table.find(key, v2)) {
            if (static_cast<unsigned>(v2) < th.get_num_vars() && !is_equal(v1, v2)) {
                auto vi1 = register_theory_var_in_lar_solver(v1);
                auto vi2 = register_theory_var_in_lar_solver(v2);
                lp::constraint_index ci1, ci2, ci3, ci4;
                
                TRACE("arith",
                      bool hlb = has_lower_bound(vi2, ci3, bound); // has_lower_bound in turn trace "arith"
                      tout << "fixed: " << mk_pp(get_owner(v1), m) << " " << mk_pp(get_owner(v2), m) << " " << bound << " " << hlb << std::endl;);
                if (has_lower_bound(vi2, ci3, bound) && has_upper_bound(vi2, ci4, bound)) {
                    VERIFY (has_lower_bound(vi1, ci1, bound));
                    VERIFY (has_upper_bound(vi1, ci2, bound));
                    ++m_stats.m_fixed_eqs;
                    m_core.reset();
                    m_eqs.reset();
                    set_evidence(ci1);
                    set_evidence(ci2);
                    set_evidence(ci3);
                    set_evidence(ci4);
                    enode* x = get_enode(v1);
                    enode* y = get_enode(v2);
                    justification* js = 
                        ctx().mk_justification(
                            ext_theory_eq_propagation_justification(
                                get_id(), ctx().get_region(), m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), x, y, 0, nullptr));

                    TRACE("arith",
                          for (unsigned i = 0; i <  m_core.size(); ++i) {
                              ctx().display_detailed_literal(tout, m_core[i]);
                              tout << "\n";
                          } 
                          for (unsigned i = 0; i < m_eqs.size(); ++i) {
                              tout << mk_pp(m_eqs[i].first->get_owner(), m) << " = " << mk_pp(m_eqs[i].second->get_owner(), m) << "\n";
                          } 
                          tout << " ==> ";
                          tout << mk_pp(x->get_owner(), m) << " = " << mk_pp(y->get_owner(), m) << "\n";
                          );

                    // parameters are TBD.
                    //                    SASSERT(validate_eq(x, y));
                    ctx().assign_eq(x, y, eq_justification(js));
                }
            }
            else {
                // bounds on v2 were changed.
                m_fixed_var_table.insert(key, v1);
            }
        }
        else {
            m_fixed_var_table.insert(key, v1);
        }
    }

    lbool make_feasible() {
        TRACE("pcs",  tout << lp().constraints(););
        auto status = lp().find_feasible_solution();
        TRACE("arith_verbose", display(tout););
        switch (status) {
        case lp::lp_status::INFEASIBLE:
            return l_false;
        case lp::lp_status::FEASIBLE:
        case lp::lp_status::OPTIMAL:
            //            SASSERT(lp().all_constraints_hold());
            return l_true;
        case lp::lp_status::TIME_EXHAUSTED:
                
        default:
            TRACE("arith", tout << "status treated as inconclusive: " << status << "\n";);
            // TENTATIVE_UNBOUNDED, UNBOUNDED, TENTATIVE_DUAL_UNBOUNDED, DUAL_UNBOUNDED, 
            // FLOATING_POINT_ERROR, TIME_EXAUSTED, ITERATIONS_EXHAUSTED, EMPTY, UNSTABLE
            return l_undef;
        }
    }
 
    lp::explanation m_explanation;
    
    literal_vector      m_core;
    svector<enode_pair> m_eqs;
    vector<parameter>   m_params;

    // lp::constraint_index const null_constraint_index = UINT_MAX; // not sure what a correct fix is

    void set_evidence(lp::constraint_index idx) {
        if (idx == UINT_MAX) {
            return;
        }
        switch (m_constraint_sources[idx]) {
        case inequality_source: {
            literal lit = m_inequalities[idx];
            SASSERT(lit != null_literal);
            m_core.push_back(lit);
            break;
        }
        case equality_source: {
            SASSERT(m_equalities[idx].first  != nullptr);
            SASSERT(m_equalities[idx].second != nullptr);
            m_eqs.push_back(m_equalities[idx]);          
            break;
        }
        case definition_source: {
            // skip definitions (these are treated as hard constraints)
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }

    void get_infeasibility_explanation_and_set_conflict() {
        m_explanation.clear();
        lp().get_infeasibility_explanation(m_explanation);
        set_conflict();
    }

    void set_conflict() {
        literal_vector core;
        set_conflict_or_lemma(core, true);
    }

    void set_conflict_or_lemma(literal_vector const& core, bool is_conflict) {
        m_eqs.reset();
        m_core.reset();
        m_params.reset();
        for (literal lit : core) {
            m_core.push_back(lit);
        }
        // lp().shrink_explanation_to_minimum(m_explanation); // todo, enable when perf is fixed
        /*
          static unsigned cn = 0;
          static unsigned num_l = 0;
          num_l+=m_explanation.size();
          std::cout << num_l / (++cn) << "\n";
        */
        ++m_num_conflicts;
        ++m_stats.m_conflicts;
        TRACE("arith", tout << "scope: " << ctx().get_scope_level() << "\n"; display_evidence(tout, m_explanation); );
        TRACE("arith", display(tout););
        for (auto const& ev : m_explanation) {
            if (!ev.first.is_zero()) { 
                set_evidence(ev.second);
            }
        }
        // SASSERT(validate_conflict());
        dump_conflict();
        if (is_conflict) {
            ctx().set_conflict(
                ctx().mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx().get_region(), 
                        m_core.size(), m_core.c_ptr(), 
                        m_eqs.size(), m_eqs.c_ptr(), m_params.size(), m_params.c_ptr())));
        }
        else {
            for (auto const& eq : m_eqs) {
                m_core.push_back(th.mk_eq(eq.first->get_owner(), eq.second->get_owner(), false));
            }
            for (literal & c : m_core) {
                c.neg();
                ctx().mark_as_relevant(c);
            }

            // DEBUG_CODE(
            //     for (literal const& c : m_core) {
            //         if (ctx().get_assignment(c) == l_true) {
            //             TRACE("arith", ctx().display_literal_verbose(tout, c) << " is true\n";);
            //             SASSERT(false);
            //         }
            //     });   // TODO: this check seems to be too strict.
            // The lemmas can come in batches
            // and the same literal can appear in several lemmas in a batch: it becomes l_true
            // in earlier processing, but it was not so when the lemma was produced
            ctx().mk_th_axiom(get_id(), m_core.size(), m_core.c_ptr());
        }
    }

    justification * why_is_diseq(theory_var v1, theory_var v2) {
        return nullptr;
    }

    void reset_eh() {
        m_use_nra_model = false;
        m_arith_eq_adapter.reset_eh();
        m_solver = nullptr;
        m_internalize_head = 0;
        m_not_handled = nullptr;
        del_bounds(0);
        m_unassigned_bounds.reset();
        m_asserted_qhead  = 0;
        m_assume_eq_head = 0;
        m_scopes.reset();
        m_stats.reset();
        m_to_check.reset();
        reset_variable_values();
    }

    void init_model(model_generator & mg) {
        init_variable_values();
        m_factory = alloc(arith_factory, m);
        mg.register_factory(m_factory);
        TRACE("arith", display(tout););
    }

    nlsat::anum const& nl_value(theory_var v, scoped_anum& r) {
        SASSERT(m_nra);
        SASSERT(m_use_nra_model);
        lpvar vi = get_lpvar(v);
        if (lp().is_term(vi)) {

            m_todo_terms.push_back(std::make_pair(vi, rational::one()));

            TRACE("arith", tout << "v" << v << " := w" << vi << "\n";
                  lp().print_term(lp().get_term(vi), tout) << "\n";);

            m_nra->am().set(r, 0);
            while (!m_todo_terms.empty()) {
                rational wcoeff = m_todo_terms.back().second;
                vi = m_todo_terms.back().first;
                m_todo_terms.pop_back();
                lp::lar_term const& term = lp().get_term(vi);
                TRACE("arith", lp().print_term(term, tout) << "\n";);
                scoped_anum r1(m_nra->am());
                rational c1(0);
                m_nra->am().set(r1, c1.to_mpq());
                m_nra->am().add(r, r1, r);                
                for (auto const & arg : term) {
                    lpvar wi = arg.var();
                    c1 = arg.coeff() * wcoeff;
                    if (lp().is_term(wi)) {
                        m_todo_terms.push_back(std::make_pair(wi, c1));
                    }
                    else {
                        m_nra->am().set(r1, c1.to_mpq());
                        m_nra->am().mul(m_nra->value(wi), r1, r1);
                        m_nra->am().add(r1, r, r);
                    }
                }
            }
            return r;
        }
        else {
            return m_nra->value(vi);
        }
    }

    model_value_proc * mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        expr* o = n->get_owner();
        if (m_use_nra_model) {
            anum const& an = nl_value(v, *m_a1);
            if (a.is_int(o) && !m_nra->am().is_int(an)) {
                return alloc(expr_wrapper_proc, a.mk_numeral(rational::zero(), a.is_int(o)));
            }
            return alloc(expr_wrapper_proc, a.mk_numeral(nl_value(v, *m_a1), a.is_int(o)));
        }
        else {
            rational r = get_value(v);
            TRACE("arith", tout << "v" << v << " := " << r << "\n";);
            SASSERT("integer variables should have integer values: " && (!a.is_int(o) || r.is_int() || m.canceled()));
            if (a.is_int(o) && !r.is_int()) r = floor(r);
            return alloc(expr_wrapper_proc, m_factory->mk_value(r,  m.get_sort(o)));
        }
    }

    bool get_value(enode* n, rational& val) {
        theory_var v = n->get_th_var(get_id());            
        if (!can_get_bound(v)) return false;
        lpvar vi = get_lpvar(v);
        if (lp().has_value(vi, val)) {
            TRACE("arith", tout << expr_ref(n->get_owner(), m) << " := " << val << "\n";);
            if (is_int(n) && !val.is_int()) return false;
            return true;
        }
        else {
            return false;
        }
    }    

    bool get_value(enode* n, expr_ref& r) {
        rational val;
        if (get_value(n, val)) {
            r = a.mk_numeral(val, is_int(n));
            return true;
        }
        else {
            return false;
        }
    }    

    bool include_func_interp(func_decl* f) {
        return 
            a.is_div0(f) ||
            a.is_idiv0(f) ||
            a.is_power0(f) ||
            a.is_rem0(f) ||
            a.is_mod0(f);        
    }

    bool get_lower(enode* n, rational& val, bool& is_strict) {
        theory_var v = n->get_th_var(get_id());
        if (!can_get_bound(v)) {
            TRACE("arith", tout << "cannot get lower for " << v << "\n";);
            return false;
        }
        lpvar vi = get_lpvar(v);
        lp::constraint_index ci;
        return lp().has_lower_bound(vi, ci, val, is_strict);
    }

    bool get_lower(enode* n, expr_ref& r) {
        bool is_strict;
        rational val;
        if (get_lower(n, val, is_strict) && !is_strict) {
            r = a.mk_numeral(val, is_int(n));
            return true;
        }
        return false;
    }

    bool get_upper(enode* n, rational& val, bool& is_strict) {
        theory_var v = n->get_th_var(get_id());
        if (!can_get_bound(v))
            return false;
        lpvar vi = get_lpvar(v);
        lp::constraint_index ci;
        return lp().has_upper_bound(vi, ci, val, is_strict);

    }

    bool get_upper(enode* n, expr_ref& r) {
        bool is_strict;
        rational val;
        if (get_upper(n, val, is_strict) && !is_strict) {
            r = a.mk_numeral(val, is_int(n));
            return true;
        }
        return false;
    }

    // Auxiliary verification utilities.

    struct scoped_arith_mode {
        smt_params& p;
        scoped_arith_mode(smt_params& p) : p(p) {
            p.m_arith_mode = AS_OLD_ARITH;
        }
        ~scoped_arith_mode() {
            p.m_arith_mode = AS_NEW_ARITH;
        }
    };

    void dump_conflict() {
        if (dump_lemmas()) {
            unsigned id = ctx().display_lemma_as_smt_problem(m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), false_literal);
            (void)id;
        }
    }

    bool validate_conflict() {
        if (m_arith_params.m_arith_mode != AS_NEW_ARITH) return true;
        scoped_arith_mode _sa(ctx().get_fparams());
        context nctx(m, ctx().get_fparams(), ctx().get_params());
        add_background(nctx);
        cancel_eh<reslimit> eh(m.limit());
        scoped_timer timer(1000, &eh);
        bool result = l_true != nctx.check();
        CTRACE("arith", !result, ctx().display_lemma_as_smt_problem(tout, m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), false_literal););
        return result;
    }

    void dump_assign(literal lit) {
        if (dump_lemmas()) {                
            unsigned id = ctx().display_lemma_as_smt_problem(m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), lit);
            (void)id;
        }
    }

    bool validate_assign(literal lit) {
        if (m_arith_params.m_arith_mode != AS_NEW_ARITH) return true;
        scoped_arith_mode _sa(ctx().get_fparams());
        context nctx(m, ctx().get_fparams(), ctx().get_params());
        m_core.push_back(~lit);
        add_background(nctx);
        m_core.pop_back();
        cancel_eh<reslimit> eh(m.limit());
        scoped_timer timer(1000, &eh);
        bool result = l_true != nctx.check();
        CTRACE("arith", !result, ctx().display_lemma_as_smt_problem(tout, m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), lit);
               display(tout););   
        return result;
    }

    bool validate_eq(enode* x, enode* y) {
        if (m_arith_params.m_arith_mode == AS_NEW_ARITH) return true;
        context nctx(m, ctx().get_fparams(), ctx().get_params());
        add_background(nctx);
        nctx.assert_expr(m.mk_not(m.mk_eq(x->get_owner(), y->get_owner())));
        cancel_eh<reslimit> eh(m.limit());
        scoped_timer timer(1000, &eh);
        return l_true != nctx.check();
    }

    void add_background(context& nctx) {
        for (literal c : m_core) {
            expr_ref tmp(m);
            ctx().literal2expr(c, tmp);
            nctx.assert_expr(tmp);
        }
        for (auto const& eq : m_eqs) {
            nctx.assert_expr(m.mk_eq(eq.first->get_owner(), eq.second->get_owner()));
        }
    }        

    theory_lra::inf_eps value(theory_var v) {
        lp::impq ival = get_ivalue(v);
        return inf_eps(rational(0), inf_rational(ival.x, ival.y));
    }

    theory_lra::inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
        lp::impq term_max;
        lp::lp_status st;
        lpvar vi = 0;
        if (!can_get_bound(v)) {
            TRACE("arith", tout << "cannot get bound for v" << v << "\n";);
            st = lp::lp_status::UNBOUNDED;
        }
        else {
            vi = get_lpvar(v);
            st = lp().maximize_term(vi, term_max);
        }
        switch (st) {
        case lp::lp_status::OPTIMAL: {
            init_variable_values();
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            inf_rational val = get_value(v);
            // inf_rational val(term_max.x, term_max.y);
            blocker = mk_gt(v);
            return inf_eps(rational::zero(), val);
        }
        case lp::lp_status::FEASIBLE: {
            inf_rational val = get_value(v);
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            blocker = mk_gt(v);
            return inf_eps(rational::zero(), val);
        }
        default:
            SASSERT(st == lp::lp_status::UNBOUNDED);
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            has_shared = false;
            blocker = m.mk_false();
            return inf_eps(rational::one(), inf_rational());
        }
    }

    expr_ref mk_gt(theory_var v) {
        lp::impq val = get_ivalue(v);
        expr* obj = get_enode(v)->get_owner();
        rational r = val.x;
        expr_ref e(m);
        if (a.is_int(m.get_sort(obj))) {
            if (r.is_int()) {
                r += rational::one();
            }
            else {
                r = ceil(r);
            }
            e = a.mk_numeral(r, m.get_sort(obj));
            e = a.mk_ge(obj, e);
        }
        else {
            e = a.mk_numeral(r, m.get_sort(obj));
            if (val.y.is_neg()) {
                e = a.mk_ge(obj, e);
            }
            else {
                e = a.mk_gt(obj, e);
            }
        }
        TRACE("opt", tout << "v" << v << " " << val << " " << r << " " << e << "\n";);
        return e;
    }

    theory_var add_objective(app* term) {
        TRACE("opt", tout << expr_ref(term, m) << "\n";);
        return internalize_def(term);
    }

    void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs) {
        term2coeffs(term, coeffs, rational::one());
    }

    void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs, rational const& coeff) {
        for (const auto & ti : term) {
            theory_var w;
            if (lp().is_term(ti.var())) {
                //w = m_term_index2theory_var.get(lp().adjust_term_index(ti.m_key), null_theory_var);
                //if (w == null_theory_var) // if extracting expressions directly from nested term
                lp::lar_term const& term1 = lp().get_term(ti.var());
                rational coeff2 = coeff * ti.coeff();
                term2coeffs(term1, coeffs, coeff2);
                continue;
            }
            else {
                w = lp().local_to_external(ti.var());
            }
            rational c0(0);
            coeffs.find(w, c0);
            coeffs.insert(w, c0 + ti.coeff() * coeff);
        }
    }

    app_ref coeffs2app(u_map<rational> const& coeffs, rational const& offset, bool is_int) {
        expr_ref_vector args(m);
        for (auto const& kv : coeffs) {
            theory_var w = kv.m_key;
            expr* o = get_enode(w)->get_owner();
            if (kv.m_value.is_zero()) {
                // continue
            }
            else if (kv.m_value.is_one()) {
                args.push_back(o);
            }
            else {
                args.push_back(a.mk_mul(a.mk_numeral(kv.m_value, is_int), o));                
            }
        }
        if (!offset.is_zero()) {
            args.push_back(a.mk_numeral(offset, is_int));
        }
        switch (args.size()) {
        case 0:
            return app_ref(a.mk_numeral(rational::zero(), is_int), m);
        case 1:
            return app_ref(to_app(args[0].get()), m);
        default:
            return app_ref(a.mk_add(args.size(), args.c_ptr()), m);
        }
    }

    app_ref mk_term(lp::lar_term const& term, bool is_int) {     
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        return coeffs2app(coeffs, rational::zero(), is_int);
    }

    rational gcd_reduce(u_map<rational>& coeffs) {
        rational g(0);
        for (auto const& kv : coeffs) {
            g = gcd(g, kv.m_value);
        }
        if (g.is_zero())
            return rational::one();
        if (!g.is_one()) {
            for (auto& kv : coeffs) {
                kv.m_value /= g;
            }             
        }
        return g;
    }

    app_ref mk_obj(theory_var v) {
        lpvar vi = get_lpvar(v);
        bool is_int = a.is_int(get_enode(v)->get_owner());
        if (lp().is_term(vi)) {           
            return mk_term(lp().get_term(vi), is_int);
        }
        else {
            theory_var w = lp().external_to_local(vi);
            return app_ref(get_enode(w)->get_owner(), m);
        }
    }

    expr_ref mk_ge(generic_model_converter& fm, theory_var v, inf_rational const& val) {
        rational r = val.get_rational();
        bool is_strict =  val.get_infinitesimal().is_pos();
        app_ref b(m);
        bool is_int = a.is_int(get_enode(v)->get_owner());
        if (is_strict) {
            b = a.mk_le(mk_obj(v), a.mk_numeral(r, is_int));
        }
        else {
            b = a.mk_ge(mk_obj(v), a.mk_numeral(r, is_int));
        }
        if (!ctx().b_internalized(b)) {
            fm.hide(b->get_decl());
            bool_var bv =  ctx().mk_bool_var(b);
            ctx().set_var_theory(bv, get_id());
            // ctx().set_enode_flag(bv, true);
            lp_api::bound_kind bkind = lp_api::bound_kind::lower_t;
            if (is_strict) bkind = lp_api::bound_kind::upper_t;
            lp_api::bound* a = mk_var_bound(bv, v, bkind, r);
            mk_bound_axioms(*a);
            updt_unassigned_bounds(v, +1);
            m_bounds[v].push_back(a);
            m_bounds_trail.push_back(v);
            m_bool_var2bound.insert(bv, a);
            TRACE("arith", tout << mk_pp(b, m) << "\n";);
        }
        if (is_strict) {
            b = m.mk_not(b);
        }
        TRACE("arith", tout << b << "\n";);
        return expr_ref(b, m);
            
    }


    void display(std::ostream & out) {
        if (m_solver) {
            out << lp().constraints();
            lp().print_terms(out);
            // the tableau
            auto pp = lp ::core_solver_pretty_printer<lp::mpq, lp::impq>(
                 lp().m_mpq_lar_core_solver.m_r_solver, out);
            pp.print();
            for (unsigned j = 0; j < lp().number_of_vars(); j++) {
                lp().m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
            }
        }
        unsigned nv = th.get_num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (!ctx().is_relevant(get_enode(v))) out << "irr: ";
            out << "v" << v;
            if (can_get_value(v)) out << " = " << get_value(v); 
            if (is_int(v)) out << ", int";
            if (ctx().is_shared(get_enode(v))) out << ", shared";
            out << " := "; th.display_var_flat_def(out, v) << "\n";
        }
    }

    void display_evidence(std::ostream& out, lp::explanation const& evidence) {
        for (auto const& ev : evidence) {
            expr_ref e(m);
            SASSERT(!ev.first.is_zero()); 
            if (ev.first.is_zero()) { 
                continue;
            }
            unsigned idx = ev.second;
            switch (m_constraint_sources.get(idx, null_source)) {
            case inequality_source: {
                literal lit = m_inequalities[idx];
                ctx().literal2expr(lit, e);
                out << e << " " << ctx().get_assignment(lit) << "\n";
                break;
            }
            case equality_source: 
                out << mk_pp(m_equalities[idx].first->get_owner(), m) << " = " 
                    << mk_pp(m_equalities[idx].second->get_owner(), m) << "\n"; 
                break;
            case definition_source: {
                theory_var v = m_definitions[idx];
                if (v != null_theory_var) 
                    out << "def: v" << v << " := " << mk_pp(th.get_enode(v)->get_owner(), m) << "\n";
                break;
            }
            case null_source:                    
                out << idx << " null";
                break;
            default:
                UNREACHABLE();
                break; 
            }
        }
        for (auto const& ev : evidence) {
            lp().constraints().display(out << ev.first << ": ", ev.second); 
        }
    }

    void collect_statistics(::statistics & st) const {
        m_arith_eq_adapter.collect_statistics(st);
        st.update("arith-lower", m_stats.m_assert_lower);
        st.update("arith-upper", m_stats.m_assert_upper);
        st.update("arith-rows", m_stats.m_add_rows);
        st.update("arith-propagations", m_stats.m_bounds_propagations);
        st.update("arith-iterations", m_stats.m_num_iterations);
        st.update("arith-factorizations", lp().settings().stats().m_num_factorizations);
        st.update("arith-pivots", m_stats.m_need_to_solve_inf);
        st.update("arith-plateau-iterations", m_stats.m_num_iterations_with_no_progress);
        st.update("arith-fixed-eqs", m_stats.m_fixed_eqs);
        st.update("arith-conflicts", m_stats.m_conflicts);
        st.update("arith-bound-propagations-lp", m_stats.m_bound_propagations1);
        st.update("arith-bound-propagations-cheap", m_stats.m_bound_propagations2);
        st.update("arith-diseq", m_stats.m_assert_diseq);
        st.update("arith-make-feasible", lp().settings().stats().m_make_feasible);
        st.update("arith-max-columns", lp().settings().stats().m_max_cols);
        st.update("arith-max-rows", lp().settings().stats().m_max_rows);
        st.update("arith-gcd-calls", lp().settings().stats().m_gcd_calls);
        st.update("arith-gcd-conflict", lp().settings().stats().m_gcd_conflicts);
        st.update("arith-cube-calls", lp().settings().stats().m_cube_calls);
        st.update("arith-cube-success", lp().settings().stats().m_cube_success);
        st.update("arith-patches", lp().settings().stats().m_patches);
        st.update("arith-patches-success", lp().settings().stats().m_patches_success);
        st.update("arith-hnf-calls", lp().settings().stats().m_hnf_cutter_calls);
        st.update("arith-horner-calls", lp().settings().stats().m_horner_calls);
        st.update("arith-horner-conflicts", lp().settings().stats().m_horner_conflicts);
        st.update("arith-horner-cross-nested-forms", lp().settings().stats().m_cross_nested_forms);
        st.update("arith-grobner-calls", lp().settings().stats().m_grobner_calls);
        st.update("arith-grobner-conflicts", lp().settings().stats().m_grobner_conflicts);
        st.update("arith-nla-explanations", m_stats.m_nla_explanations);
        st.update("arith-nla-lemmas", m_stats.m_nla_lemmas);
        st.update("arith-gomory-cuts", m_stats.m_gomory_cuts);
        st.update("arith-assume-eqs", m_stats.m_assume_eqs);
        st.update("arith-branch", m_stats.m_branch);
    }        
};
    
theory_lra::theory_lra(ast_manager& m, theory_arith_params& ap):
    theory(m.get_family_id("arith")) {
    m_imp = alloc(imp, *this, m, ap);
}    
theory_lra::~theory_lra() {
    dealloc(m_imp);
}   
theory* theory_lra::mk_fresh(context* new_ctx) {
    return alloc(theory_lra, new_ctx->get_manager(), new_ctx->get_fparams());
}
void theory_lra::init(context * ctx) {
    theory::init(ctx);
    m_imp->init(ctx);
}
bool theory_lra::internalize_atom(app * atom, bool gate_ctx) {
    return m_imp->internalize_atom(atom, gate_ctx);
}
bool theory_lra::internalize_term(app * term) {
    return m_imp->internalize_term(term);
}
void theory_lra::internalize_eq_eh(app * atom, bool_var v) {
    m_imp->internalize_eq_eh(atom, v);
}
void theory_lra::assign_eh(bool_var v, bool is_true) {
    m_imp->assign_eh(v, is_true);
}
lbool theory_lra::get_phase(bool_var v) {
    return m_imp->get_phase(v);
}
void theory_lra::new_eq_eh(theory_var v1, theory_var v2) {
    m_imp->new_eq_eh(v1, v2);
}
bool theory_lra::use_diseqs() const {
    return m_imp->use_diseqs();
}
void theory_lra::new_diseq_eh(theory_var v1, theory_var v2) {
    m_imp->new_diseq_eh(v1, v2);
}
void theory_lra::apply_sort_cnstr(enode* n, sort* s) {
    m_imp->apply_sort_cnstr(n, s);
}
void theory_lra::push_scope_eh() {
    theory::push_scope_eh();
    m_imp->push_scope_eh();
}
void theory_lra::pop_scope_eh(unsigned num_scopes) {
    m_imp->pop_scope_eh(num_scopes);
    theory::pop_scope_eh(num_scopes);
}
void theory_lra::restart_eh() {
    m_imp->restart_eh();
}
void theory_lra::relevant_eh(app* e) {
    m_imp->relevant_eh(e);
}
void theory_lra::init_search_eh() {
    m_imp->init_search_eh();
}
final_check_status theory_lra::final_check_eh() {
    return m_imp->final_check_eh();
}
bool theory_lra::is_shared(theory_var v) const {
    return m_imp->is_shared(v);
}
bool theory_lra::can_propagate() {
    return m_imp->can_propagate();
}
void theory_lra::propagate() {
    m_imp->propagate();
}
justification * theory_lra::why_is_diseq(theory_var v1, theory_var v2) {
    return m_imp->why_is_diseq(v1, v2);
}
void theory_lra::reset_eh() {
    m_imp->reset_eh();
}
void theory_lra::init_model(model_generator & m) {
    m_imp->init_model(m);
}
model_value_proc * theory_lra::mk_value(enode * n, model_generator & mg) {
    return m_imp->mk_value(n, mg);
}
bool theory_lra::get_value(enode* n, rational& r) {
    return m_imp->get_value(n, r);
}
bool theory_lra::get_value(enode* n, expr_ref& r) {
    return m_imp->get_value(n, r);
}
bool theory_lra::include_func_interp(func_decl* f) {
    return m_imp->include_func_interp(f);
}
bool theory_lra::get_lower(enode* n, expr_ref& r) {
    return m_imp->get_lower(n, r);
}
bool theory_lra::get_upper(enode* n, expr_ref& r) {
    return m_imp->get_upper(n, r);
}
bool theory_lra::get_lower(enode* n, rational& r, bool& is_strict) {
    return m_imp->get_lower(n, r, is_strict);
}
bool theory_lra::get_upper(enode* n, rational& r, bool& is_strict) {
    return m_imp->get_upper(n, r, is_strict);
}
void theory_lra::display(std::ostream & out) const {
    m_imp->display(out);
}
void theory_lra::collect_statistics(::statistics & st) const {
    m_imp->collect_statistics(st);
}
theory_lra::inf_eps theory_lra::value(theory_var v) {
    return m_imp->value(v);
}
theory_lra::inf_eps theory_lra::maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
    return m_imp->maximize(v, blocker, has_shared);
}
theory_var theory_lra::add_objective(app* term) {
    return m_imp->add_objective(term);
}
expr_ref theory_lra::mk_ge(generic_model_converter& fm, theory_var v, inf_rational const& val) {
    return m_imp->mk_ge(fm, v, val);
}



}
