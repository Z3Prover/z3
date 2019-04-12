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
#include "util/lp/rooted_mons.h"
#include "util/lp/nla_tangent_lemmas.h"
#include "util/lp/nla_basics_lemmas.h"
namespace nla {

template <typename A, typename B>
bool try_insert(const A& elem, B& collection) {
    auto it = collection.find(elem);
    if (it != collection.end())
        return false;
    collection.insert(elem);
    return true;
}

typedef lp::constraint_index lpci;
typedef lp::lconstraint_kind llc;

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

struct point {
    rational x;
    rational y;
    point(const rational& a, const rational& b): x(a), y(b) {}
    point() {}
    point& operator*=(rational a) {
        x *= a;
        y *= a;
        return *this;
    } 
};

struct core {
    struct bfc {
        factor m_x, m_y;
        bfc() {}
        bfc(const factor& x, const factor& y): m_x(x), m_y(y) {};
    };

    //fields    
    var_eqs                                                          m_evars;
    vector<monomial>                                                 m_monomials;

    rooted_mon_table                                                 m_rm_table;
    // this field is used for the push/pop operations
    unsigned_vector                                                  m_monomials_counts;
    lp::lar_solver&                                                  m_lar_solver;
    std::unordered_map<lpvar, svector<lpvar>>                        m_monomials_containing_var;
    
    // m_var_to_its_monomial[m_monomials[i].var()] = i
    std::unordered_map<lpvar, unsigned>                              m_var_to_its_monomial;
    vector<lemma> *                                                  m_lemma_vec;
    unsigned_vector                                                  m_to_refine;
    std::unordered_map<unsigned_vector, unsigned, hash_svector>      m_mkeys; // the key is the sorted vars of a monomial 
    tangents                                                         m_tangents;
    basics                                                            m_basics;
    core(lp::lar_solver& s);
    
    bool compare_holds(const rational& ls, llc cmp, const rational& rs) const;
    
    rational value(const lp::lar_term& r) const;
    
    lp::lar_term subs_terms_to_columns(const lp::lar_term& t) const;
    bool ineq_holds(const ineq& n) const;
    bool lemma_holds(const lemma& l) const;
  
    rational vvr(lpvar j) const { return m_lar_solver.get_column_value_rational(j); }

    rational vvr(const monomial& m) const { return m_lar_solver.get_column_value_rational(m.var()); }

    lp::impq vv(lpvar j) const { return m_lar_solver.get_column_value(j); }
    
    lpvar var(const rooted_mon& rm) const {return m_monomials[rm.orig_index()].var(); }

    rational vvr(const rooted_mon& rm) const { return vvr(m_monomials[rm.orig_index()].var()) * rm.orig_sign(); }

    rational vvr(const factor& f) const {  return f.is_var()? vvr(f.index()) : vvr(m_rm_table.rms()[f.index()]); }

    lpvar var(const factor& f) const { return f.is_var()? f.index() : var(m_rm_table.rms()[f.index()]); }

    svector<lpvar> sorted_vars(const factor& f) const;
    bool done() const;
    
    void add_empty_lemma();
    // the value of the factor is equal to the value of the variable multiplied
    // by the canonize_sign
    rational canonize_sign(const factor& f) const;

    rational canonize_sign_of_var(lpvar j) const;
    
    // the value of the rooted monomias is equal to the value of the variable multiplied
    // by the canonize_sign
    rational canonize_sign(const rooted_mon& m) const;
    
    // returns the monomial index
    unsigned add(lpvar v, unsigned sz, lpvar const* vs);
    
    void push();

    void deregister_monomial_from_rooted_monomials (const monomial & m, unsigned i);

    void deregister_monomial_from_tables(const monomial & m, unsigned i);
     
    void pop(unsigned n);

    rational mon_value_by_vars(unsigned i) const;
    template <typename T>
    rational product_value(const T & m) const;
    
    // return true iff the monomial value is equal to the product of the values of the factors
    bool check_monomial(const monomial& m) const;
    
    void explain(const monomial& m, lp::explanation& exp) const;

    void explain(const rooted_mon& rm, lp::explanation& exp) const;

    void explain(const factor& f, lp::explanation& exp) const;

    void explain(lpvar j, lp::explanation& exp) const;

    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const;

    std::ostream & print_factor(const factor& f, std::ostream& out) const;

    std::ostream & print_factor_with_vars(const factor& f, std::ostream& out) const;

    std::ostream& print_monomial(const monomial& m, std::ostream& out) const;

    std::ostream& print_point(const point &a, std::ostream& out) const;
    
    std::ostream& print_tangent_domain(const point &a, const point &b, std::ostream& out) const;

    std::ostream& print_bfc(const bfc& m, std::ostream& out) const;

    std::ostream& print_monomial(unsigned i, std::ostream& out) const;

    std::ostream& print_monomial_with_vars(unsigned i, std::ostream& out) const;

    template <typename T>
    std::ostream& print_product_with_vars(const T& m, std::ostream& out) const;

    std::ostream& print_monomial_with_vars(const monomial& m, std::ostream& out) const;

    std::ostream& print_rooted_monomial(const rooted_mon& rm, std::ostream& out) const;

    std::ostream& print_rooted_monomial_with_vars(const rooted_mon& rm, std::ostream& out) const;

    std::ostream& print_explanation(const lp::explanation& exp, std::ostream& out) const;

    bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;
    bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;

    bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;

    bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
    
    // return true iff the negation of the ineq can be derived from the constraints
    bool explain_ineq(const lp::lar_term& t, llc cmp, const rational& rs);

    /**
     * \brief
     if t is an octagon term -+x -+ y try to explain why the term always
     equal zero
    */
    bool explain_by_equiv(const lp::lar_term& t, lp::explanation& e);
    
    void mk_ineq(lp::lar_term& t, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp);

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp);

    void mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, llc cmp, const rational& rs);

    void mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs);

    llc negate(llc cmp);
    
    llc apply_minus(llc cmp);
    
    void mk_ineq(const rational& a, lpvar j, llc cmp);

    void mk_ineq(lpvar j, lpvar k, llc cmp, lemma& l);

    void mk_ineq(lpvar j, llc cmp);
    
    // the monomials should be equal by modulo sign but this is not so in the model
    void fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign);

    // Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
    // Also sorts the result.
    // 
    svector<lpvar> reduce_monomial_to_rooted(const svector<lpvar> & vars, rational & sign) const;


    // Replaces definition m_v = v1* .. * vn by
    // m_v = coeff * w1 * ... * wn, where w1, .., wn are canonical
    // representatives, which are the roots of the equivalence tree, under current equations.
    // 
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

    // Returns true if the monomial sign is incorrect
    bool sign_contradiction(const monomial& m) const;

    /*
      unsigned_vector eq_vars(lpvar j) const;
    */
    // Monomials m and n vars have the same values, up to "sign"
    // Generate a lemma if values of m.var() and n.var() are not the same up to sign

    bool var_is_fixed_to_zero(lpvar j) const;
    bool var_is_fixed_to_val(lpvar j, const rational& v) const;

    bool var_is_fixed(lpvar j) const;
    
    std::ostream & print_ineq(const ineq & in, std::ostream & out) const;

    std::ostream & print_var(lpvar j, std::ostream & out) const;

    std::ostream & print_monomials(std::ostream & out) const;    

    std::ostream & print_ineqs(const lemma& l, std::ostream & out) const;
    
    std::ostream & print_factorization(const factorization& f, std::ostream& out) const;
    
    bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const;

    const monomial* find_monomial_of_vars(const svector<lpvar>& vars) const;

    void explain_existing_lower_bound(lpvar j);

    void explain_existing_upper_bound(lpvar j);
    
    void explain_separation_from_zero(lpvar j);

    int get_derived_sign(const rooted_mon& rm, const factorization& f) const;
    // here we use the fact xy = 0 -> x = 0 or y = 0
    void trace_print_monomial_and_factorization(const rooted_mon& rm, const factorization& f, std::ostream& out) const;

    void explain_var_separated_from_zero(lpvar j);

    void explain_fixed_var(lpvar j);
    // x = 0 or y = 0 -> xy = 0

    bool var_has_positive_lower_bound(lpvar j) const;

    bool var_has_negative_upper_bound(lpvar j) const;
    
    bool var_is_separated_from_zero(lpvar j) const;
    

    bool vars_are_equiv(lpvar a, lpvar b) const;

    
    void explain_equiv_vars(lpvar a, lpvar b);
    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    void explain(const factorization& f, lp::explanation& exp);

    bool has_zero_factor(const factorization& factorization) const;


    template <typename T>
    bool has_zero(const T& product) const;

    template <typename T>
    bool mon_has_zero(const T& product) const;
    void init_rm_to_refine();
    lp::lp_settings& settings();
    unsigned random();
    void map_monomial_vars_to_monomial_indices(unsigned i);

    void map_vars_to_monomials();

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs();

    void collect_equivs_of_fixed_vars();

    // returns true iff the term is in a form +-x-+y.
    // the sign is true iff the term is x+y, -x-y.
    bool is_octagon_term(const lp::lar_term& t, bool & sign, lpvar& i, lpvar &j) const;
    
    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1);

    // x is equivalent to y if x = +- y
    void init_vars_equivalence();

    bool vars_table_is_ok() const;

    bool rm_table_is_ok() const;
    
    bool tables_are_ok() const;
    
    bool var_is_a_root(lpvar j) const;

    template <typename T>
    bool vars_are_roots(const T& v) const;

    void register_monomial_in_tables(unsigned i_mon);

    template <typename T>
    void trace_print_rms(const T& p, std::ostream& out);

    void print_monomial_stats(const monomial& m, std::ostream& out);
    
    void print_stats(std::ostream& out);
        
    void register_monomials_in_tables();

    void clear();
    
    void init_search();

#if 0
    void init_to_refine();
#endif
    void init_to_refine();

    bool divide(const rooted_mon& bc, const factor& c, factor & b) const;

    void negate_factor_equality(const factor& c,
                                const factor& d);
    
    void negate_factor_relation(const rational& a_sign, const factor& a, const rational& b_sign, const factor& b);

    void negate_var_factor_relation(const rational& a_sign, lpvar a, const rational& b_sign, const factor& b);

    // |c_sign| = 1, and c*c_sign > 0
    // ac > bc => ac/|c| > bc/|c| => a*c_sign > b*c_sign
    void generate_ol(const rooted_mon& ac,                     
                     const factor& a,
                     int c_sign,
                     const factor& c,
                     const rooted_mon& bc,
                     const factor& b,
                     llc ab_cmp);

    void generate_mon_ol(const monomial& ac,                     
                         lpvar a,
                         const rational& c_sign,
                         lpvar c,
                         const rooted_mon& bd,
                         const factor& b,
                         const rational& d_sign,
                         lpvar d,
                         llc ab_cmp);

    std::unordered_set<lpvar> collect_vars(const lemma& l) const;

    void print_lemma(std::ostream& out);

    void print_specific_lemma(const lemma& l, std::ostream& out) const;
    

    void trace_print_ol(const rooted_mon& ac,
                        const factor& a,
                        const factor& c,
                        const rooted_mon& bc,
                        const factor& b,
                        std::ostream& out);
    
    bool order_lemma_on_ac_and_bc_and_factors(const rooted_mon& ac,
                                              const factor& a,
                                              const factor& c,
                                              const rooted_mon& bc,
                                              const factor& b);
    
    // a >< b && c > 0  => ac >< bc
    // a >< b && c < 0  => ac <> bc
    // ac[k] plays the role of c   
    bool order_lemma_on_ac_and_bc(const rooted_mon& rm_ac,
                                  const factorization& ac_f,
                                  unsigned k,
                                  const rooted_mon& rm_bd);
    void maybe_add_a_factor(lpvar i,
                            const factor& c,
                            std::unordered_set<lpvar>& found_vars,
                            std::unordered_set<unsigned>& found_rm,
                            vector<factor> & r) const;
    
    bool order_lemma_on_ac_explore(const rooted_mon& rm, const factorization& ac, unsigned k);

    void order_lemma_on_factorization(const rooted_mon& rm, const factorization& ab);
    
    /**
       \brief Add lemma: 
       a > 0 & b <= value(b) => sign*ab <= value(b)*a  if value(a) > 0
       a < 0 & b >= value(b) => sign*ab <= value(b)*a  if value(a) < 0
    */
    void order_lemma_on_ab_gt(const monomial& m, const rational& sign, lpvar a, lpvar b);
    // we need to deduce ab >= vvr(b)*a
    /**
       \brief Add lemma: 
       a > 0 & b >= value(b) => sign*ab >= value(b)*a if value(a) > 0
       a < 0 & b <= value(b) => sign*ab >= value(b)*a if value(a) < 0
    */
    void order_lemma_on_ab_lt(const monomial& m, const rational& sign, lpvar a, lpvar b);
    void order_lemma_on_ab(const monomial& m, const rational& sign, lpvar a, lpvar b, bool gt);
    bool rm_check(const rooted_mon&) const;
    void order_lemma_on_factor_binomial_explore(const monomial& m, unsigned k);
    void order_lemma_on_factor_binomial_rm(const monomial& ac, unsigned k, const rooted_mon& rm_bd);
    void order_lemma_on_binomial_ac_bd(const monomial& ac, unsigned k, const rooted_mon& bd, const factor& b, lpvar d);
    void order_lemma_on_binomial_k(const monomial& m, lpvar k, bool gt);
    void order_lemma_on_binomial_sign(const monomial& ac, lpvar x, lpvar y, int sign);
    void order_lemma_on_binomial(const monomial& ac);
    void order_lemma_on_rmonomial(const rooted_mon& rm);
    void order_lemma();
    void print_monotone_array(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted,
                              std::ostream& out) const;
    std::vector<rational> get_sorted_key(const rooted_mon& rm) const;
    std::unordered_map<unsigned, unsigned_vector> get_rm_by_arity();
    bool uniform_le(const std::vector<rational>& a,
                    const std::vector<rational>& b,
                    unsigned & strict_i) const;
    vector<std::pair<rational, lpvar>> get_sorted_key_with_vars(const rooted_mon& a) const;
    void negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict);

    void negate_abs_a_lt_abs_b(lpvar a, lpvar b);
    void assert_abs_val_a_le_abs_var_b(    const rooted_mon& a,    const rooted_mon& b,    bool strict);

    // strict version
    void generate_monl_strict(const rooted_mon& a,
                              const rooted_mon& b,
                              unsigned strict);

    // not a strict version
    void generate_monl(const rooted_mon& a,
                       const rooted_mon& b);
    
    bool monotonicity_lemma_on_lex_sorted_rm_upper(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm);

    bool monotonicity_lemma_on_lex_sorted_rm_lower(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm);

    bool monotonicity_lemma_on_lex_sorted_rm(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm);
    bool monotonicity_lemma_on_lex_sorted(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted);
    
    bool  monotonicity_lemma_on_rms_of_same_arity(const unsigned_vector& rms);
    
    void monotonicity_lemma();

#if 0
    void monotonicity_lemma();

#endif

    void monotonicity_lemma(unsigned i_mon);

    // add |j| <= |vvr(j)|  
    void var_abs_val_le(lpvar j);

    // assert that |j| >= |vvr(j)|
    void var_abs_val_ge(lpvar j);


    /**
       \brief Add |v| ~ |bound|
       where ~ is <, <=, >, >=, 
       and bound = vvr(v)

       |v| > |bound| 
       <=> 
       (v < 0 or v > |bound|) & (v > 0 or -v > |bound|)        
       => Let s be the sign of vvr(v)
       (s*v < 0 or s*v > |bound|)         

       |v| < |bound|
       <=>
       v < |bound| & -v < |bound| 
       => Let s be the sign of vvr(v)
       s*v < |bound|

    */

    void add_abs_bound(lpvar v, llc cmp);

    void add_abs_bound(lpvar v, llc cmp, rational const& bound);

    /** \brief enforce the inequality |m| <= product |m[i]| .
        by enforcing lemma:
        /\_i |m[i]| <= |vvr(m[i])| => |m| <= |product_i vvr(m[i])|
        <=>
        \/_i |m[i]| > |vvr(m[i])} or |m| <= |product_i vvr(m[i])|
    */

    void monotonicity_lemma_gt(const monomial& m, const rational& prod_val);
    
    /** \brief enforce the inequality |m| >= product |m[i]| .

        /\_i |m[i]| >= |vvr(m[i])| => |m| >= |product_i vvr(m[i])|
        <=>
        \/_i |m[i]| < |vvr(m[i])} or |m| >= |product_i vvr(m[i])|
    */
    void monotonicity_lemma_lt(const monomial& m, const rational& prod_val);
    
    bool  find_bfc_to_refine_on_rmonomial(const rooted_mon& rm, bfc & bf);
    
    bool  find_bfc_to_refine(bfc& bf, lpvar &j, rational& sign, const rooted_mon*& rm_found);
    void generate_simple_sign_lemma(const rational& sign, const monomial& m);

    void generate_simple_tangent_lemma(const rooted_mon* rm);
    
    void tangent_lemma();

    void generate_explanations_of_tang_lemma(const rooted_mon& rm, const bfc& bf, lp::explanation& exp);
    
    void tangent_lemma_bf(const bfc& bf, lpvar j, const rational& sign, const rooted_mon* rm);
    void generate_tang_plane(const rational & a, const rational& b, const factor& x, const factor& y, bool below, lpvar j, const rational& j_sign);  

    void negate_relation(unsigned j, const rational& a);
    
    void generate_two_tang_lines(const bfc & bf, const point& xy, const rational& sign, lpvar j);
    // Get two planes tangent to surface z = xy, one at point a,  and another at point b.
    // One can show that these planes still create a cut.
    void get_initial_tang_points(point &a, point &b, const point& xy,
                                 bool below) const;

    void push_tang_point(point &a, const point& xy, bool below, const rational& correct_val, const rational& val) const;
    
    void push_tang_points(point &a, point &b, const point& xy, bool below, const rational& correct_val, const rational& val) const;

    rational tang_plane(const point& a, const point& x) const;

    bool  plane_is_correct_cut(const point& plane,
                               const point& xy,
                               const rational & correct_val,                             
                               const rational & val,
                               bool below) const;

    // "below" means that the val is below the surface xy 
    void get_tang_points(point &a, point &b, bool below, const rational& val,
                         const point& xy) const;

    bool  conflict_found() const;
    lbool  inner_check(bool derived);
    
    lbool  check(vector<lemma>& l_vec);

    bool  no_lemmas_hold() const;
    
    void test_factorization(unsigned /*mon_index*/, unsigned /*number_of_factorizations*/);
    
    lbool  test_check(vector<lemma>& l);
};  // end of core
} // end of namespace nla
