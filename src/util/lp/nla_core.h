/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include "util/lp/factorization.h"
#include "util/lp/lp_types.h"
#include "util/lp/var_eqs.h"
#include "util/lp/nla_tangent_lemmas.h"
#include "util/lp/nla_basics_lemmas.h"
#include "util/lp/nla_order_lemmas.h"
#include "util/lp/nla_monotone_lemmas.h"
#include "util/lp/emonomials.h"
namespace nla {

template <typename A, typename B>
bool try_insert(const A& elem, B& collection) {
    auto it = collection.find(elem);
    if (it != collection.end())
        return false;
    collection.insert(elem);
    return true;
}

typedef lp::constraint_index     lpci;
typedef lp::lconstraint_kind     llc;
typedef lp::constraint_index     lpci;
typedef lp::explanation          expl_set;
typedef lp::var_index            lpvar;

inline int rat_sign(const rational& r) { return r.is_pos()? 1 : ( r.is_neg()? -1 : 0); }
inline rational rrat_sign(const rational& r) { return rational(rat_sign(r)); }
inline bool is_set(unsigned j) {  return static_cast<int>(j) != -1; } 
inline bool is_even(unsigned k) { return (k >> 1) << 1 == k; }
struct ineq {
    lp::lconstraint_kind m_cmp;
    lp::lar_term         m_term;
    rational             m_rs;
    ineq(lp::lconstraint_kind cmp, const lp::lar_term& term, const rational& rs) : m_cmp(cmp), m_term(term), m_rs(rs) {}
    bool operator==(const ineq& a) const {
        return m_cmp == a.m_cmp && m_term == a.m_term && m_rs == a.m_rs;
    }
    const lp::lar_term& term() const { return m_term; };
    lp::lconstraint_kind cmp() const { return m_cmp;  };
    const rational& rs() const { return m_rs; };
};

class lemma {
    vector<ineq>     m_ineqs;
    lp::explanation  m_expl;
public:
    void push_back(const ineq& i) { m_ineqs.push_back(i);}
    size_t size() const { return m_ineqs.size() + m_expl.size(); }
    const vector<ineq>& ineqs() const { return m_ineqs; }
    vector<ineq>& ineqs() { return m_ineqs; }
    lp::explanation& expl() { return m_expl; }
    const lp::explanation& expl() const { return m_expl; }
    bool is_conflict() const { return m_ineqs.empty() && !m_expl.empty(); }
};


class core {
public:
    var_eqs                  m_evars;
    lp::lar_solver&          m_lar_solver;
    vector<lemma> *          m_lemma_vec;
    svector<lpvar>           m_to_refine;
    tangents                 m_tangents;
    basics                   m_basics;
    order                    m_order;
    monotone                 m_monotone;
    emonomials               m_emons;

    core(lp::lar_solver& s);

    bool compare_holds(const rational& ls, llc cmp, const rational& rs) const;
    
    rational value(const lp::lar_term& r) const;
    
    lp::lar_term subs_terms_to_columns(const lp::lar_term& t) const;
    bool ineq_holds(const ineq& n) const;
    bool lemma_holds(const lemma& l) const;
  
    rational vvr(lpvar j) const { return m_lar_solver.get_column_value_rational(j); }

    rational vvr(const monomial& m) const { return m_lar_solver.get_column_value_rational(m.var()); }

    lp::impq vv(lpvar j) const { return m_lar_solver.get_column_value(j); }
    
    lpvar var(signed_vars const& sv) const { return sv.var(); }

    rational vvr(const signed_vars& rm) const { return vvr(m_emons[rm.var()]); } // NB: removed multiplication with sign.

    rational vvr(const factor& f) const {  return f.is_var()? vvr(f.var()) : vvr(m_emons[f.var()]); }

    lpvar var(const factor& f) const { return f.var(); }

    svector<lpvar> sorted_vars(const factor& f) const;
    bool done() const;
    
    void add_empty_lemma();
    // the value of the factor is equal to the value of the variable multiplied
    // by the canonize_sign
    rational canonize_sign(const factor& f) const;

    rational canonize_sign_of_var(lpvar j) const;
    
    // the value of the rooted monomias is equal to the value of the variable multiplied
    // by the canonize_sign
    rational canonize_sign(const signed_vars& m) const;
    

    void deregister_monomial_from_signed_varsomials (const monomial & m, unsigned i);

    void deregister_monomial_from_tables(const monomial & m, unsigned i);

    // returns the monomial index
    void add(lpvar v, unsigned sz, lpvar const* vs);   
    void push();     
    void pop(unsigned n);

    rational mon_value_by_vars(unsigned i) const;
    template <typename T>
    rational product_value(const T & m) const;
    
    // return true iff the monomial value is equal to the product of the values of the factors
    bool check_monomial(const monomial& m) const;
    
    void explain(const monomial& m, lp::explanation& exp) const;
    void explain(const signed_vars& rm, lp::explanation& exp) const;
    void explain(const factor& f, lp::explanation& exp) const;
    void explain(lpvar j, lp::explanation& exp) const;
    void explain_existing_lower_bound(lpvar j);
    void explain_existing_upper_bound(lpvar j);    
    void explain_separation_from_zero(lpvar j);
    void explain_var_separated_from_zero(lpvar j);
    void explain_fixed_var(lpvar j);

    std::ostream & print_ineq(const ineq & in, std::ostream & out) const;
    std::ostream & print_var(lpvar j, std::ostream & out) const;
    std::ostream & print_monomials(std::ostream & out) const;    
    std::ostream & print_ineqs(const lemma& l, std::ostream & out) const;    
    std::ostream & print_factorization(const factorization& f, std::ostream& out) const;
    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const;
    std::ostream & print_factor(const factor& f, std::ostream& out) const;
    std::ostream & print_factor_with_vars(const factor& f, std::ostream& out) const;
    std::ostream& print_monomial(const monomial& m, std::ostream& out) const;
    std::ostream& print_bfc(const bfc& m, std::ostream& out) const;
    std::ostream& print_monomial_with_vars(unsigned i, std::ostream& out) const;
    template <typename T>
    std::ostream& print_product_with_vars(const T& m, std::ostream& out) const;
    std::ostream& print_monomial_with_vars(const monomial& m, std::ostream& out) const;
    std::ostream& print_explanation(const lp::explanation& exp, std::ostream& out) const;
    template <typename T>
    void trace_print_rms(const T& p, std::ostream& out);
    void trace_print_monomial_and_factorization(const signed_vars& rm, const factorization& f, std::ostream& out) const;
    void print_monomial_stats(const monomial& m, std::ostream& out);    
    void print_stats(std::ostream& out);
    std::ostream& print_lemma(std::ostream& out) const;

    void print_specific_lemma(const lemma& l, std::ostream& out) const;
    

    void trace_print_ol(const signed_vars& ac,
                        const factor& a,
                        const factor& c,
                        const signed_vars& bc,
                        const factor& b,
                        std::ostream& out);

        
    
    void mk_ineq(lp::lar_term& t, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp);
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp);
    void mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(lpvar j, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, llc cmp);
    void mk_ineq(lpvar j, lpvar k, llc cmp, lemma& l);
    void mk_ineq(lpvar j, llc cmp);
    
    
    void maybe_add_a_factor(lpvar i,
                            const factor& c,
                            std::unordered_set<lpvar>& found_vars,
                            std::unordered_set<unsigned>& found_rm,
                            vector<factor> & r) const;

    llc apply_minus(llc cmp);
    
    void fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign);

    svector<lpvar> reduce_monomial_to_rooted(const svector<lpvar> & vars, rational & sign) const;

    monomial_coeff canonize_monomial(monomial const& m) const;

    lemma& current_lemma();
    const lemma& current_lemma() const;
    vector<ineq>& current_ineqs();
    lp::explanation& current_expl();
    const lp::explanation& current_expl() const;

    int vars_sign(const svector<lpvar>& v);
    bool has_upper_bound(lpvar j) const; 
    bool has_lower_bound(lpvar j) const; 
    const rational& get_upper_bound(unsigned j) const;
    const rational& get_lower_bound(unsigned j) const;    
    
    bool zero_is_an_inner_point_of_bounds(lpvar j) const;
    
    int rat_sign(const monomial& m) const;
    inline int rat_sign(lpvar j) const { return nla::rat_sign(vvr(j)); }

    bool sign_contradiction(const monomial& m) const;

    bool var_is_fixed_to_zero(lpvar j) const;
    bool var_is_fixed_to_val(lpvar j, const rational& v) const;

    bool var_is_fixed(lpvar j) const;
        
    bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const;

    const monomial* find_monomial_of_vars(const svector<lpvar>& vars) const;


    int get_derived_sign(const signed_vars& rm, const factorization& f) const;


    bool var_has_positive_lower_bound(lpvar j) const;

    bool var_has_negative_upper_bound(lpvar j) const;
    
    bool var_is_separated_from_zero(lpvar j) const;
    

    bool vars_are_equiv(lpvar a, lpvar b) const;

    
    void explain_equiv_vars(lpvar a, lpvar b);
    void explain(const factorization& f, lp::explanation& exp);
    bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;

    bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;

    bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;

    bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
    
    bool explain_ineq(const lp::lar_term& t, llc cmp, const rational& rs);

    bool explain_by_equiv(const lp::lar_term& t, lp::explanation& e);

    bool has_zero_factor(const factorization& factorization) const;

    template <typename T>
    bool mon_has_zero(const T& product) const;
    lp::lp_settings& settings();
    unsigned random();
    void map_monomial_vars_to_monomial_indices(unsigned i);

    void map_vars_to_monomials();

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs();

    void collect_equivs_of_fixed_vars();

    bool is_octagon_term(const lp::lar_term& t, bool & sign, lpvar& i, lpvar &j) const;
    
    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1);

    void init_vars_equivalence();

    bool vars_table_is_ok() const;

    bool rm_table_is_ok() const;
    
    bool tables_are_ok() const;
    
    bool var_is_a_root(lpvar j) const;

    template <typename T>
    bool vars_are_roots(const T& v) const;

    void register_monomial_in_tables(unsigned i_mon);

    void register_monomials_in_tables();

    void clear();
    
    void init_search();

    void init_to_refine();

    bool divide(const signed_vars& bc, const factor& c, factor & b) const;

    void negate_factor_equality(const factor& c, const factor& d);
    
    void negate_factor_relation(const rational& a_sign, const factor& a, const rational& b_sign, const factor& b);

    std::unordered_set<lpvar> collect_vars(const lemma& l) const;

    bool rm_check(const signed_vars&) const;
    std::unordered_map<unsigned, unsigned_vector> get_rm_by_arity();

    void add_abs_bound(lpvar v, llc cmp);
    void add_abs_bound(lpvar v, llc cmp, rational const& bound);

    bool  find_bfc_to_refine_on_rmonomial(const signed_vars& rm, bfc & bf);
    
    bool  find_bfc_to_refine(bfc& bf, lpvar &j, rational& sign, const signed_vars*& rm_found);
    void generate_simple_sign_lemma(const rational& sign, const monomial& m);

    void negate_relation(unsigned j, const rational& a);
    bool  conflict_found() const;
    lbool  inner_check(bool derived);
    
    lbool  check(vector<lemma>& l_vec);

    bool  no_lemmas_hold() const;
    
    lbool  test_check(vector<lemma>& l);
};  // end of core

    struct pp_mon {
        core const& c;
        monomial const& m;
        pp_mon(core const& c, monomial const& m): c(c), m(m) {}
        pp_mon(core const& c, lpvar v): c(c), m(c.m_emons[v]) {}
    };

    inline std::ostream& operator<<(std::ostream& out, pp_mon const& p) { return p.c.print_monomial(p.m, out); }

} // end of namespace nla

