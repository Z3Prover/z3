/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  nla_core.h

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#pragma once
#include "math/lp/factorization.h"
#include "math/lp/lp_types.h"
#include "math/lp/var_eqs.h"
#include "math/lp/nla_tangent_lemmas.h"
#include "math/lp/nla_basics_lemmas.h"
#include "math/lp/nla_order_lemmas.h"
#include "math/lp/nla_monotone_lemmas.h"
#include "math/lp/nla_grobner.h"
#include "math/lp/nla_powers.h"
#include "math/lp/nla_divisions.h"
#include "math/lp/emonics.h"
#include "math/lp/nex.h"
#include "math/lp/horner.h"
#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_intervals.h"
#include "nlsat/nlsat_solver.h"
#include "smt/params/smt_params_helper.hpp"

namespace nra {
    class solver;
}

namespace nla {

template <typename A, typename B>
bool try_insert(const A& elem, B& collection) {
    auto it = collection.find(elem);
    if (it != collection.end())
        return false;
    collection.insert(elem);
    return true;
}

class core {
    friend struct common;
    friend class new_lemma;
    friend class grobner;
    friend class order;
    friend struct basics;
    friend struct tangents;
    friend class monotone;
    friend class powers;
    friend class intervals;
    friend class horner;
    friend class solver;
    friend class monomial_bounds;
    friend class nra::solver;
    friend class divisions;

    unsigned m_nlsat_delay = 0;
    unsigned m_nlsat_delay_bound = 0;

    bool should_run_bounded_nlsat();
    lbool bounded_nlsat();

    var_eqs<emonics>         m_evars;

    lp::lar_solver&          lra;
    reslimit&                m_reslim;
    smt_params_helper        m_params;
    std::function<bool(lpvar)> m_relevant;
    vector<lemma>            m_lemmas;
    vector<ineq>             m_literals;
    vector<lp::equality>       m_equalities;
    vector<lp::fixed_equality> m_fixed_equalities;
    indexed_uint_set         m_to_refine;
    indexed_uint_set         m_monics_with_changed_bounds;
    tangents                 m_tangents;
    basics                   m_basics;
    order                    m_order;
    monotone                 m_monotone;
    powers                   m_powers;
    divisions                m_divisions;
    intervals                m_intervals; 
    monomial_bounds          m_monomial_bounds;
    unsigned                 m_conflicts;
    bool                     m_check_feasible = false;
    horner                   m_horner;
    grobner                  m_grobner;
    emonics                  m_emons;
    svector<lpvar>           m_add_buffer;
    mutable indexed_uint_set m_active_var_set;

    reslimit                 m_nra_lim;

    bool                     m_use_nra_model = false;
    nra::solver              m_nra;
    bool                     m_cautious_patching = true;
    lpvar                    m_patched_var = 0;
    monic const*             m_patched_monic = nullptr; 



    void check_weighted(unsigned sz, std::pair<unsigned, std::function<void(void)>>* checks);
    void add_bounds();



public:    
    // constructor
    core(lp::lar_solver& s, params_ref const& p, reslimit&);
    const auto& monics_with_changed_bounds() const { return m_monics_with_changed_bounds; }
    void insert_to_refine(lpvar j);
    void erase_from_to_refine(lpvar j);
    
    const indexed_uint_set&  active_var_set () const { return m_active_var_set;}
    bool active_var_set_contains(unsigned j) const { return m_active_var_set.contains(j); }

    void insert_to_active_var_set(unsigned j) const { 
        m_active_var_set.insert(j); 
    }    

    void clear_active_var_set() const { m_active_var_set.reset(); }

    unsigned get_var_weight(lpvar) const;

    reslimit& reslim() { return m_reslim; }  
    emonics& emons() { return m_emons; }
    const emonics& emons() const { return m_emons; }
    monic& emon(unsigned i) { return m_emons[i]; }
    monic const& emon(unsigned i) const { return m_emons[i]; }

    bool has_relevant_monomial() const;

    bool compare_holds(const rational& ls, llc cmp, const rational& rs) const;
    
    rational value(const lp::lar_term& r) const;
    
    bool ineq_holds(const ineq& n) const;
    bool lemma_holds(const lemma& l) const;
    bool is_monic_var(lpvar j) const { return m_emons.is_monic_var(j); }
    const rational& val(lpvar j) const { return lra.get_column_value(j).x; }

    const rational& var_val(const monic& m) const { return lra.get_column_value(m.var()).x; }

    rational mul_val(const monic& m) const { 
        rational r(1);
        for (lpvar v : m.vars()) r *= lra.get_column_value(v).x;
        return r;
    }

    bool canonize_sign_is_correct(const monic& m) const;

    lpvar var(monic const& sv) const { return sv.var(); }

    rational val_rooted(const monic& m) const { return m.rsign()*val(m.var()); }

    rational val(const factor& f) const {  return f.rat_sign() * (f.is_var()? val(f.var()) : var_val(m_emons[f.var()])); }

    rational val(const factorization&) const;
    
    lpvar var(const factor& f) const { return f.var(); }

    smt_params_helper const & params() const { return m_params; }

    // returns true if the combination of the Horner's schema and Grobner Basis should be called
    bool need_run_horner() const { 
        return params().arith_nl_horner() && lp_settings().stats().m_nla_calls % params().arith_nl_horner_frequency() == 0; 
    }

    bool need_run_grobner() const {
        return params().arith_nl_grobner();         
    }

    void set_active_vars_weights(nex_creator&);
    std::unordered_set<lpvar> get_vars_of_expr_with_opening_terms(const nex* e);
    
    void incremental_linearization(bool);
    
    svector<lpvar> sorted_rvars(const factor& f) const;
    bool done() const;

    
    // the value of the factor is equal to the value of the variable multiplied
    // by the canonize_sign
    bool canonize_sign(const factor& f) const;
    bool canonize_sign(const factorization& f) const;

    bool canonize_sign(lpvar j) const;
    
    // the value of the rooted monomias is equal to the value of the m.var() variable multiplied
    // by the canonize_sign
    bool canonize_sign(const monic& m) const;
    

    void deregister_monic_from_monicomials (const monic & m, unsigned i);

    void deregister_monic_from_tables(const monic & m, unsigned i);

    void add_monic(lpvar v, unsigned sz, lpvar const* vs);   
    void add_idivision(lpvar q, lpvar x, lpvar y) { m_divisions.add_idivision(q, x, y); }
    void add_rdivision(lpvar q, lpvar x, lpvar y) { m_divisions.add_rdivision(q, x, y); }
    void add_bounded_division(lpvar q, lpvar x, lpvar y) { m_divisions.add_bounded_division(q, x, y); }

    void set_relevant(std::function<bool(lpvar)>& is_relevant) { m_relevant = is_relevant; }
    bool is_relevant(lpvar v) const { return !m_relevant || m_relevant(v); }

    void push();     
    void pop(unsigned n);

    trail_stack& trail() { return m_emons.get_trail_stack(); }

    rational mon_value_by_vars(unsigned i) const;
    rational product_value(const monic & m) const;
    
    // return true iff the monic value is equal to the product of the values of the factors
    bool check_monic(const monic& m) const;
   

    std::ostream & print_ineq(const ineq & in, std::ostream & out) const;
    std::ostream & print_var(lpvar j, std::ostream & out) const;
    std::ostream & print_monics(std::ostream & out) const;    
    std::ostream & print_ineqs(const lemma& l, std::ostream & out) const;    
    std::ostream & print_factorization(const factorization& f, std::ostream& out) const;
    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const;    
    template <typename T>
    std::string product_indices_str(const T & m) const;
    std::string var_str(lpvar) const;
    
    std::ostream & print_factor(const factor& f, std::ostream& out) const;
    std::ostream & print_factor_with_vars(const factor& f, std::ostream& out) const;
    std::ostream & print_factor_with_vars(lpvar j, std::ostream& out) const { return print_var(j, out); }
    std::ostream& print_monic(const monic& m, std::ostream& out) const;
    std::ostream& print_bfc(const factorization& m, std::ostream& out) const;
    std::ostream& print_monic_with_vars(unsigned i, std::ostream& out) const;
    template <typename T>
    std::ostream& print_product_with_vars(const T& m, std::ostream& out) const;
    std::ostream& print_monic_with_vars(const monic& m, std::ostream& out) const;
    std::ostream& print_explanation(const lp::explanation& exp, std::ostream& out) const;
    std::ostream& diagnose_pdd_miss(std::ostream& out);
    template <typename T>
    void trace_print_rms(const T& p, std::ostream& out);
    void trace_print_monic_and_factorization(const monic& rm, const factorization& f, std::ostream& out) const;
    void print_monic_stats(const monic& m, std::ostream& out);    
    void print_stats(std::ostream& out);
 
    pp_var pp(lpvar j) const { return pp_var(*this, j); }
    pp_fac pp(factor const& f) const { return pp_fac(*this, f); }
    pp_factorization pp(factorization const& f) const { return pp_factorization(*this, f); }
 
    std::ostream& print_lemma(const lemma& l, std::ostream& out) const;
    

    void trace_print_ol(const monic& ac,
                        const factor& a,
                        const factor& c,
                        const monic& bc,
                        const factor& b,
                        std::ostream& out);

        
    void mk_ineq_no_expl_check(new_lemma& lemma, lp::lar_term& t, llc cmp, const rational& rs);
    
    void maybe_add_a_factor(lpvar i,
                            const factor& c,
                            std::unordered_set<lpvar>& found_vars,
                            std::unordered_set<unsigned>& found_rm,
                            vector<factor> & r) const;

    llc apply_minus(llc cmp);
    
    void fill_explanation_and_lemma_sign(new_lemma& lemma, const monic& a, const monic & b, rational const& sign);

    svector<lpvar> reduce_monic_to_rooted(const svector<lpvar> & vars, rational & sign) const;

    monic_coeff canonize_monic(monic const& m) const;

    int vars_sign(const svector<lpvar>& v);
    bool has_upper_bound(lpvar j) const; 
    bool has_lower_bound(lpvar j) const;
    bool no_bounds(lpvar j) const {
        return !has_upper_bound(j) && !has_lower_bound(j);
    }
    const rational& get_upper_bound(unsigned j) const;
    const rational& get_lower_bound(unsigned j) const;    
    bool has_lower_bound(lp::lpvar var, u_dependency*& ci, lp::mpq& value, bool& is_strict) const { 
        return lra.has_lower_bound(var, ci, value, is_strict); 
    }
    bool has_upper_bound(lp::lpvar var, u_dependency*& ci, lp::mpq& value, bool& is_strict) const {
        return lra.has_upper_bound(var, ci, value, is_strict);
    }

    
    bool zero_is_an_inner_point_of_bounds(lpvar j) const;    
    bool var_is_int(lpvar j) const { return lra.column_is_int(j); }
    int rat_sign(const monic& m) const;
    inline int rat_sign(lpvar j) const { return nla::rat_sign(val(j)); }

    bool sign_contradiction(const monic& m) const;

    bool var_is_fixed_to_zero(lpvar j) const;
    bool var_is_fixed_to_val(lpvar j, const rational& v) const;

    bool var_is_fixed(lpvar j) const;
    bool var_is_free(lpvar j) const;
        
    bool find_canonical_monic_of_vars(const svector<lpvar>& vars, lpvar & i) const;
    bool is_canonical_monic(lpvar) const;
    bool elists_are_consistent(bool check_in_model) const;
    bool elist_is_consistent(const std::unordered_set<lpvar>&) const;
    bool var_has_positive_lower_bound(lpvar j) const;

    bool var_has_negative_upper_bound(lpvar j) const;
    
    bool var_is_separated_from_zero(lpvar j) const;

    bool vars_are_equiv(lpvar a, lpvar b) const;    
    bool explain_ineq(new_lemma& lemma, const lp::lar_term& t, llc cmp, const rational& rs);
    bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;
    bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;
    bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
    bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
    bool explain_by_equiv(const lp::lar_term& t, lp::explanation& e) const;
    bool has_zero_factor(const factorization& factorization) const;

    template <typename T>
    bool mon_has_zero(const T& product) const;
    lp::lp_settings& lp_settings();
    const lp::lp_settings& lp_settings() const;
    unsigned random();

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs();

    bool is_octagon_term(const lp::lar_term& t, bool & sign, lpvar& i, lpvar &j) const;
    
    void add_equivalence_maybe(const lp::lar_term* t, u_dependency* c0, u_dependency* c1);

    void init_vars_equivalence();

    bool vars_table_is_ok() const;

    bool rm_table_is_ok() const;
    
    bool tables_are_ok() const;
    
    bool var_is_a_root(lpvar j) const;

    template <typename T>
    bool vars_are_roots(const T& v) const;

    void register_monic_in_tables(unsigned i_mon);

    void register_monics_in_tables();

    void clear();
    
    void init_search();

    void init_to_refine();

    bool divide(const monic& bc, const factor& c, factor & b) const;
    
    std::unordered_set<lpvar> collect_vars(const lemma& l) const;

    bool rm_check(const monic&) const;
    std::unordered_map<unsigned, unsigned_vector> get_rm_by_arity();

    void negate_relation(new_lemma& lemma, unsigned j, const rational& a);
    void negate_factor_equality(new_lemma& lemma, const factor& c, const factor& d);    
    void negate_factor_relation(new_lemma& lemma, const rational& a_sign, const factor& a, const rational& b_sign, const factor& b);

    bool  find_bfc_to_refine_on_monic(const monic&, factorization & bf);
    
    bool  find_bfc_to_refine(const monic* & m, factorization& bf);

    bool  conflict_found() const;
    
    lbool check();
    lbool check_power(lpvar r, lpvar x, lpvar y);
    void check_bounded_divisions();

    bool  no_lemmas_hold() const;

    void propagate();

    void simplify();
    
    lbool  test_check();
    lpvar map_to_root(lpvar) const;
    std::ostream& print_terms(std::ostream&) const;
    std::ostream& print_term(const lp::lar_term&, std::ostream&) const;

    template <typename T>
    std::ostream& print_row(const T& row, std::ostream& out) const {
        vector<std::pair<rational, lpvar>> v;
        for (auto p : row) {
            v.push_back(std::make_pair(p.coeff(), p.var()));
        }
        return lp::print_linear_combination_customized(v, [this](lpvar j) { return var_str(j); }, out);
    }
    
    bool influences_nl_var(lpvar) const;
    bool is_nl_var(lpvar) const;
    
    bool is_used_in_monic(lpvar) const;
    void patch_monomials();
    void patch_monomials_on_to_refine();
    void patch_monomial(lpvar);
    bool var_breaks_correct_monic(lpvar) const;
    bool var_breaks_correct_monic_as_factor(lpvar, const monic&) const;
    void update_to_refine_of_var(lpvar j);
    bool try_to_patch(const rational&);
    bool to_refine_is_correct() const;
    bool is_patch_blocked(lpvar u, const lp::impq&) const;
    bool has_big_num(const monic&) const;
    bool var_is_big(lpvar) const;
    bool has_real(const factorization&) const;
    bool has_real(const monic& m) const;
    void set_use_nra_model(bool m);
    bool use_nra_model() const { return m_use_nra_model; }
    vector<nla::lemma> const& lemmas() const { return m_lemmas; }
    vector<nla::ineq> const& literals() const { return m_literals; }
    vector<lp::equality> const& equalities() const { return m_equalities; }
    vector<lp::fixed_equality> const& fixed_equalities() const { return m_fixed_equalities; }
    bool should_check_feasible() const { return m_check_feasible; }

    void add_fixed_equality(lp::lpvar v, rational const& k, lp::explanation const& e) { m_fixed_equalities.push_back({v, k, e}); }
    void add_equality(lp::lpvar i, lp::lpvar j, lp::explanation const& e) { m_equalities.push_back({i, j, e}); }

};  // end of core

struct pp_mon {
    core const& c;
    monic const& m;
    pp_mon(core const& c, monic const& m): c(c), m(m) {}
    pp_mon(core const& c, lpvar v): c(c), m(c.emons()[v]) {}
};
struct pp_mon_with_vars {
    core const& c;
    monic const& m;
    pp_mon_with_vars(core const& c, monic const& m): c(c), m(m) {}
    pp_mon_with_vars(core const& c, lpvar v): c(c), m(c.emons()[v]) {}
};

inline std::ostream& operator<<(std::ostream& out, pp_mon const& p) { return p.c.print_monic(p.m, out); }
inline std::ostream& operator<<(std::ostream& out, pp_mon_with_vars const& p) { return p.c.print_monic_with_vars(p.m, out); }
inline std::ostream& operator<<(std::ostream& out, pp_fac const& f) { return f.c.print_factor(f.f, out); }
inline std::ostream& operator<<(std::ostream& out, pp_factorization const& f) { return f.c.print_factorization(f.f, out); }
inline std::ostream& operator<<(std::ostream& out, pp_var const& v) { return v.c.print_var(v.v, out); }

} // end of namespace nla

