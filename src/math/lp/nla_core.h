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
#include "math/lp/factorization.h"
#include "math/lp/lp_types.h"
#include "math/lp/var_eqs.h"
#include "math/lp/nla_tangent_lemmas.h"
#include "math/lp/nla_basics_lemmas.h"
#include "math/lp/nla_order_lemmas.h"
#include "math/lp/nla_monotone_lemmas.h"
#include "math/lp/emonics.h"
#include "math/lp/nla_settings.h"
#include "math/lp/nex.h"
#include "math/lp/horner.h"
#include "math/lp/nla_intervals.h"
#include "math/grobner/pdd_solver.h"


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
const lpvar null_lpvar = UINT_MAX;

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
    var_eqs<emonics>         m_evars;
    lp::lar_solver&          m_lar_solver;
    vector<lemma> *          m_lemma_vec;
    lp::int_set              m_to_refine;
    tangents                 m_tangents;
    basics                   m_basics;
    order                    m_order;
    monotone                 m_monotone;
    intervals                m_intervals;                
    horner                   m_horner;
    nla_settings             m_nla_settings;    
    dd::pdd_manager          m_pdd_manager;
    dd::solver               m_pdd_grobner;
private:
    emonics                  m_emons;
    svector<lpvar>           m_add_buffer;
    mutable lp::int_set      m_active_var_set;
    lp::int_set              m_rows;
public:
    unsigned                 m_grobner_quota;
    reslimit                 m_reslim;

    
    const lp::int_set&  active_var_set () const { return m_active_var_set;}
    bool active_var_set_contains(unsigned j) const { return m_active_var_set.contains(j); }

    void insert_to_active_var_set(unsigned j) const { m_active_var_set.insert(j); }    

    void clear_active_var_set() const {
        m_active_var_set.clear();
    }

    void clear_and_resize_active_var_set() const {
        m_active_var_set.clear();
        m_active_var_set.resize(m_lar_solver.number_of_vars());
    }
    
    reslimit& reslim() { return m_reslim; }  
    emonics& emons() { return m_emons; }
    const emonics& emons() const { return m_emons; }
    // constructor
    core(lp::lar_solver& s, reslimit &);
   
    bool compare_holds(const rational& ls, llc cmp, const rational& rs) const;
    
    rational value(const lp::lar_term& r) const;
    
    lp::lar_term subs_terms_to_columns(const lp::lar_term& t) const;
    bool ineq_holds(const ineq& n) const;
    bool lemma_holds(const lemma& l) const;
    bool is_monic_var(lpvar j) const { return m_emons.is_monic_var(j); }
    rational val(lpvar j) const { return m_lar_solver.get_column_value_rational(j); }

    rational val(const monic& m) const { return m_lar_solver.get_column_value_rational(m.var()); }

    bool canonize_sign_is_correct(const monic& m) const;

    lpvar var(monic const& sv) const { return sv.var(); }

    rational val_rooted(const monic& m) const { return m.rsign()*val(m.var()); }

    rational val(const factor& f) const {  return f.rat_sign() * (f.is_var()? val(f.var()) : val(m_emons[f.var()])); }

    rational val(const factorization&) const;
    
    lpvar var(const factor& f) const { return f.var(); }

    // returns true if the combination of the Horner's schema and Grobner Basis should be called
    bool need_to_call_algebraic_methods() const { 
	return
            lp_settings().stats().m_nla_calls % m_nla_settings.horner_frequency() == 0; 
    }
    
    lbool incremental_linearization(bool);
    
    svector<lpvar> sorted_rvars(const factor& f) const;
    bool done() const;

    void add_empty_lemma();
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
    void push();     
    void pop(unsigned n);

    rational mon_value_by_vars(unsigned i) const;
    rational product_value(const unsigned_vector & m) const;
    
    // return true iff the monic value is equal to the product of the values of the factors
    bool check_monic(const monic& m) const;
    
    void explain(const monic& m, lp::explanation& exp) const;
    void explain(const factor& f, lp::explanation& exp) const;
    void explain(lpvar j, lp::explanation& exp) const;
    void explain_existing_lower_bound(lpvar j);
    void explain_existing_upper_bound(lpvar j);    
    void explain_separation_from_zero(lpvar j);
    void explain_var_separated_from_zero(lpvar j);
    void explain_fixed_var(lpvar j);

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
    std::ostream& print_lemma(std::ostream& out) const;
  
    void print_specific_lemma(const lemma& l, std::ostream& out) const;
    

    void trace_print_ol(const monic& ac,
                        const factor& a,
                        const factor& c,
                        const monic& bc,
                        const factor& b,
                        std::ostream& out);

        
    
    void mk_ineq(lp::lar_term& t, llc cmp, const rational& rs);
    void mk_ineq_no_expl_check(lp::lar_term& t, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(bool a, lpvar j, bool b, lpvar k, llc cmp, const rational& rs);
    void mk_ineq(bool a, lpvar j, bool b, lpvar k, llc cmp);
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
    
    void fill_explanation_and_lemma_sign(const monic& a, const monic & b, rational const& sign);

    svector<lpvar> reduce_monic_to_rooted(const svector<lpvar> & vars, rational & sign) const;

    monic_coeff canonize_monic(monic const& m) const;

    lemma& current_lemma();
    const lemma& current_lemma() const;
    vector<ineq>& current_ineqs();
    lp::explanation& current_expl();
    const lp::explanation& current_expl() const;

    int vars_sign(const svector<lpvar>& v);
    bool has_upper_bound(lpvar j) const; 
    bool has_lower_bound(lpvar j) const;
    bool no_bounds(lpvar j) const {
        return !has_upper_bound(j) && !has_lower_bound(j);
    }
    const rational& get_upper_bound(unsigned j) const;
    const rational& get_lower_bound(unsigned j) const;    
    
    bool zero_is_an_inner_point_of_bounds(lpvar j) const;
    
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
    void explain_equiv_vars(lpvar a, lpvar b);
    void explain(const factorization& f, lp::explanation& exp);
    bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;

    bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;

    bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;

    bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
    
    bool explain_ineq(const lp::lar_term& t, llc cmp, const rational& rs);

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
    
    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1);

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

    void negate_factor_equality(const factor& c, const factor& d);
    
    void negate_factor_relation(const rational& a_sign, const factor& a, const rational& b_sign, const factor& b);

    std::unordered_set<lpvar> collect_vars(const lemma& l) const;

    bool rm_check(const monic&) const;
    std::unordered_map<unsigned, unsigned_vector> get_rm_by_arity();

    void add_abs_bound(lpvar v, llc cmp);
    void add_abs_bound(lpvar v, llc cmp, rational const& bound);

    bool  find_bfc_to_refine_on_monic(const monic&, factorization & bf);
    
    bool  find_bfc_to_refine(const monic* & m, factorization& bf);

    void negate_relation(unsigned j, const rational& a);
    bool  conflict_found() const;
    lbool  inner_check(bool derived);
    
    lbool  check(vector<lemma>& l_vec);

    bool  no_lemmas_hold() const;
    
    lbool  test_check(vector<lemma>& l);
    lpvar map_to_root(lpvar) const;
    std::ostream& print_terms(std::ostream&) const;
    std::ostream& print_term(const lp::lar_term&, std::ostream&) const;
    template <typename T>
    std::ostream& print_row(const T & row , std::ostream& out) const {
        vector<std::pair<rational, lpvar>> v;
        for (auto p : row) {
            v.push_back(std::make_pair(p.coeff(), p.var()));
        }
        return lp::print_linear_combination_customized(v, [this](lpvar j) { return var_str(j); },
        out);        
    }
    void run_grobner();
    void find_nl_cluster();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  svector<lpvar>& q);
    std::unordered_set<lpvar> get_vars_of_expr_with_opening_terms(const nex* e);
    void display_matrix_of_m_rows(std::ostream & out) const;
    void set_active_vars_weights(nex_creator&);
    unsigned get_var_weight(lpvar) const;
    void add_row_to_grobner(const vector<lp::row_cell<rational>> & row);    
    bool check_pdd_eq(const dd::solver::equation*);
    const rational& val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep);
    dd::pdd pdd_expr(const rational& c, lpvar j, u_dependency*&);
    void set_level2var_for_grobner();
    void configure_grobner();
    bool influences_nl_var(lpvar) const;
    bool is_nl_var(lpvar) const;
    bool is_used_in_monic(lpvar) const;
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

struct pp_fac {
    core const& c;
    factor const& f;
    pp_fac(core const& c, factor const& f): c(c), f(f) {}
};

inline std::ostream& operator<<(std::ostream& out, pp_fac const& f) { return f.c.print_factor(f.f, out); }

struct pp_var {
    core const& c;
    lpvar v;
    pp_var(core const& c, lpvar v): c(c), v(v) {}
};

inline std::ostream& operator<<(std::ostream& out, pp_var const& v) { return v.c.print_var(v.v, out); }

} // end of namespace nla

