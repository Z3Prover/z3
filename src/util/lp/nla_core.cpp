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
#include "util/lp/nla_core.h"
#include "util/lp/factorization_factory_imp.h"
namespace nla {

core::core(lp::lar_solver& s) :
    m_evars(),
    m_lar_solver(s),
    m_tangents(this),
    m_basics(this),
    m_order(this),
    m_monotone(this),
    m_emons(m_evars) {
}
    
bool core::compare_holds(const rational& ls, llc cmp, const rational& rs) const {
    switch(cmp) {
    case llc::LE: return ls <= rs;
    case llc::LT: return ls < rs;
    case llc::GE: return ls >= rs;
    case llc::GT: return ls > rs;
    case llc::EQ: return ls == rs;
    case llc::NE: return ls != rs;
    default: SASSERT(false);
    };
        
    return false;
}

rational core::value(const lp::lar_term& r) const {
    rational ret(0);
    for (const auto & t : r) {
        ret += t.coeff() * val(t.var());
    }
    return ret;
}

lp::lar_term core::subs_terms_to_columns(const lp::lar_term& t) const {
    lp::lar_term r;
    for (const auto& p : t) {
        lpvar j = p.var();
        if (m_lar_solver.is_term(j))
            j = m_lar_solver.map_term_index_to_column_index(j);
        r.add_coeff_var(p.coeff(), j);
    }
    return r;
} 
    
bool core::ineq_holds(const ineq& n) const {
    lp::lar_term t = subs_terms_to_columns(n.term());
    return compare_holds(value(t), n.cmp(), n.rs());
}

bool core::lemma_holds(const lemma& l) const {
    for(const ineq &i : l.ineqs()) {
        if (ineq_holds(i))
            return true;
    }
    return false;
}

lpvar core::map_to_root(lpvar j) const {
    return m_evars.find(j).var();
}
    
svector<lpvar> core::sorted_rvars(const factor& f) const {
    if (f.is_var()) {
        svector<lpvar> r; r.push_back(map_to_root(f.var()));
        return r;
    }
    TRACE("nla_solver", tout << "nv";);
    return m_emons[f.var()].rvars();
}

// the value of the factor is equal to the value of the variable multiplied
// by the canonize_sign
bool core::canonize_sign(const factor& f) const {
    return f.sign() ^ (f.is_var()? canonize_sign(f.var()) : canonize_sign(m_emons[f.var()]));
}

bool core::canonize_sign(lpvar j) const {
    return m_evars.find(j).sign();        
}

bool core::canonize_sign_is_correct(const monomial& m) const {
    bool r = false;
    for (lpvar j : m.vars()) {
        r ^= canonize_sign(j);
    }
    return r == m.rsign();
}

bool core::canonize_sign(const monomial& m) const {
    SASSERT(canonize_sign_is_correct(m));
    return m.rsign();
}

bool core::canonize_sign(const factorization& f) const {
    bool r = false;
    for (const factor & a : f) {
        r ^= canonize_sign(a);
    }
    return r;
}

void core::add(lpvar v, unsigned sz, lpvar const* vs) {
    m_emons.add(v, sz, vs);
}
    
void core::push() {
    TRACE("nla_solver",);
    m_emons.push();
}

     
void core::pop(unsigned n) {
    TRACE("nla_solver", tout << "n = " << n << "\n";);
    m_emons.pop(n);
    SASSERT(elists_are_consistent(false));
}

rational core::product_value(const unsigned_vector & m) const {
    rational r(1);
    for (auto j : m) {
        r *= m_lar_solver.get_column_value_rational(j);
    }
    return r;
}
    
// return true iff the monomial value is equal to the product of the values of the factors
bool core::check_monomial(const monomial& m) const {
    SASSERT(m_lar_solver.get_column_value(m.var()).is_int());        
    return product_value(m.vars()) == m_lar_solver.get_column_value_rational(m.var());
}
    
void core::explain(const monomial& m, lp::explanation& exp) const {       
    for (lpvar j : m.vars())
        explain(j, exp);
}

void core::explain(const factor& f, lp::explanation& exp) const {
    if (f.type() == factor_type::VAR) {
        explain(f.var(), exp);
    } else {
        explain(m_emons[f.var()], exp);
    }
}

void core::explain(lpvar j, lp::explanation& exp) const {
    m_evars.explain(j, exp);
}

template <typename T>
std::ostream& core::print_product(const T & m, std::ostream& out) const {
    bool first = true;
    for (lpvar v : m) {
        if (!first) out << "*"; else first = false;
        if (settings().m_print_external_var_name)
            out << "(" << m_lar_solver.get_variable_name(v) << "=" << val(v) << ")";
        else
            out << "(v" << v << " =" << val(v) << ")";
            
    }
    return out;
}

std::ostream & core::print_factor(const factor& f, std::ostream& out) const {
    if (f.sign())
        out << "- ";
    if (f.is_var()) {
        out << "VAR,  ";
        print_var(f.var(), out);
    } else {
        out << "MON, v" << m_emons[f.var()] << " = ";
        print_product(m_emons[f.var()].rvars(), out);
    }
    out << "\n";
    return out;
}

std::ostream & core::print_factor_with_vars(const factor& f, std::ostream& out) const {
    if (f.is_var()) {
        print_var(f.var(), out);
    } 
    else {
        out << " MON = " << pp_rmon(*this, m_emons[f.var()]);
    }
    return out;
}

std::ostream& core::print_monomial(const monomial& m, std::ostream& out) const {
    if (settings().m_print_external_var_name)
        out << "([" << m.var() << "] = " << m_lar_solver.get_variable_name(m.var()) << " = " << val(m.var()) << " = ";
    else 
        out << "(v" << m.var() << " = " << val(m.var()) << " = ";
    print_product(m.vars(), out) << ")\n";
    return out;
}

std::ostream& core::print_point(const point &a, std::ostream& out) const {
    out << "(" << a.x <<  ", " << a.y << ")";
    return out;
}
    
std::ostream& core::print_tangent_domain(const point &a, const point &b, std::ostream& out) const {
    out << "("; print_point(a, out);  out <<  ", "; print_point(b, out); out <<  ")";
    return out;
}

std::ostream& core::print_bfc(const factorization& m, std::ostream& out) const {
    SASSERT(m.size() == 2);
    out << "( x = ";
    print_factor(m[0], out);
    out <<  "* y = ";
    print_factor(m[1], out); out <<  ")";
    return out;
}

std::ostream& core::print_monomial_with_vars(lpvar v, std::ostream& out) const {
    return print_monomial_with_vars(m_emons[v], out);
}
template <typename T>
std::ostream& core::print_product_with_vars(const T& m, std::ostream& out) const {
    print_product(m, out) << "\n";
    for (unsigned k = 0; k < m.size(); k++) {
        print_var(m[k], out);
    }
    return out;
}

std::ostream& core::print_monomial_with_vars(const monomial& m, std::ostream& out) const {
    out << "["; print_var(m.var(), out) << "]\n";
    out << "vars:"; print_product_with_vars(m.vars(), out) << "\n";
    if (m.vars() == m.rvars())
        out << "same rvars, and m.rsign = " << m.rsign() << " of course\n";
    else {
        out << "rvars:"; print_product_with_vars(m.rvars(), out) << "\n";
        out << "rsign:" << m.rsign() << "\n";
    }
    return out;
}

std::ostream& core::print_explanation(const lp::explanation& exp, std::ostream& out) const {
    out << "expl: ";
    for (auto &p : exp) {
        out << "(" << p.second << ")";
        m_lar_solver.print_constraint(p.second, out);
        out << "      ";
    }
    out << "\n";
    return out;
}

bool core::explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
    rational b(0); // the bound
    for (const auto& p : t) {
        rational pb;
        if (explain_coeff_upper_bound(p, pb, e)) {
            b += pb;
        } else {
            e.clear();
            return false;
        }
    }
    if (b > rs ) {
        e.clear();
        return false;
    }
    return true;
}
bool core::explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
    rational b(0); // the bound
    for (const auto& p : t) {
        rational pb;
        if (explain_coeff_lower_bound(p, pb, e)) {
            b += pb;
        } else {
            e.clear();
            return false;
        }
    }
    if (b < rs ) {
        e.clear();
        return false;
    }
    return true;
}

bool core:: explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
    const rational& a = p.coeff();
    SASSERT(!a.is_zero());
    unsigned c; // the index for the lower or the upper bound
    if (a.is_pos()) {
        unsigned c = m_lar_solver.get_column_lower_bound_witness(p.var());
        if (c + 1 == 0)
            return false;
        bound = a * m_lar_solver.get_lower_bound(p.var()).x;
        e.add(c);
        return true;
    }
    // a.is_neg()
    c = m_lar_solver.get_column_upper_bound_witness(p.var());
    if (c + 1 == 0)
        return false;
    bound = a * m_lar_solver.get_upper_bound(p.var()).x;
    e.add(c);
    return true;
}

bool core:: explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
    const rational& a = p.coeff();
    SASSERT(!a.is_zero());
    unsigned c; // the index for the lower or the upper bound
    if (a.is_neg()) {
        unsigned c = m_lar_solver.get_column_lower_bound_witness(p.var());
        if (c + 1 == 0)
            return false;
        bound = a * m_lar_solver.get_lower_bound(p.var()).x;
        e.add(c);
        return true;
    }
    // a.is_pos()
    c = m_lar_solver.get_column_upper_bound_witness(p.var());
    if (c + 1 == 0)
        return false;
    bound = a * m_lar_solver.get_upper_bound(p.var()).x;
    e.add(c);
    return true;
}
    
// return true iff the negation of the ineq can be derived from the constraints
bool core:: explain_ineq(const lp::lar_term& t, llc cmp, const rational& rs) {
    // check that we have something like 0 < 0, which is always false and can be safely
    // removed from the lemma
        
    if (t.is_empty() && rs.is_zero() &&
        (cmp == llc::LT || cmp == llc::GT || cmp == llc::NE)) return true;
    lp::explanation exp;
    bool r;
    switch(negate(cmp)) {
    case llc::LE:
        r = explain_upper_bound(t, rs, exp);
        break;
    case llc::LT:
        r = explain_upper_bound(t, rs - rational(1), exp);
        break;
    case llc::GE: 
        r = explain_lower_bound(t, rs, exp);
        break;
    case llc::GT:
        r = explain_lower_bound(t, rs + rational(1), exp);
        break;

    case llc::EQ:
        r = (explain_lower_bound(t, rs, exp) && explain_upper_bound(t, rs, exp)) ||
            (rs.is_zero() && explain_by_equiv(t, exp));
        break;
    case llc::NE:
        // TBD - NB: does this work for Reals?
        r = explain_lower_bound(t, rs + rational(1), exp) || explain_upper_bound(t, rs - rational(1), exp);           
        break;
    default:
        UNREACHABLE();
        return false;
    }
    if (r) {
        current_expl().add(exp);
        return true;
    }
        
    return false;
}

/**
 * \brief
 if t is an octagon term -+x -+ y try to explain why the term always
 equal zero
*/
bool core:: explain_by_equiv(const lp::lar_term& t, lp::explanation& e) {
    lpvar i,j;
    bool sign;
    if (!is_octagon_term(t, sign, i, j))
        return false;
    if (m_evars.find(signed_var(i, false)) != m_evars.find(signed_var(j, sign)))
        return false;
            
    m_evars.explain(signed_var(i, false), signed_var(j, sign), e);
    TRACE("nla_solver", tout << "explained :"; m_lar_solver.print_term(t, tout););
    return true;
            
}
    
void core::mk_ineq(lp::lar_term& t, llc cmp, const rational& rs) {
    TRACE("nla_solver_details", m_lar_solver.print_term(t, tout << "t = "););
    if (!explain_ineq(t, cmp, rs)) {
        m_lar_solver.subs_term_columns(t);
        current_lemma().push_back(ineq(cmp, t, rs));
        CTRACE("nla_solver", ineq_holds(ineq(cmp, t, rs)), print_ineq(ineq(cmp, t, rs), tout) << "\n";);
        SASSERT(!ineq_holds(ineq(cmp, t, rs)));
    }
}

void core::mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs) {
    lp::lar_term t;
    t.add_coeff_var(a, j);
    t.add_coeff_var(b, k);
    mk_ineq(t, cmp, rs);
}

void core:: mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs) {
    mk_ineq(rational(1), j, b, k, cmp, rs);
}

void core:: mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp) {
    mk_ineq(j, b, k, cmp, rational::zero());
}

void core:: mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp) {
    mk_ineq(a, j, b, k, cmp, rational::zero());
}

void core:: mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs) {
    mk_ineq(a, j, rational(1), k, cmp, rs);
}

void core:: mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs) {
    mk_ineq(j, rational(1), k, cmp, rs);
}

void core:: mk_ineq(lpvar j, llc cmp, const rational& rs) {
    mk_ineq(rational(1), j, cmp, rs);
}

void core:: mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs) {
    lp::lar_term t;        
    t.add_coeff_var(a, j);
    mk_ineq(t, cmp, rs);
}

llc apply_minus(llc cmp) {
    switch(cmp) {
    case llc::LE: return llc::GE;
    case llc::LT: return llc::GT;
    case llc::GE: return llc::LE;
    case llc::GT: return llc::LT;
    default: break;
    }
    return cmp;
}
    
void core:: mk_ineq(const rational& a, lpvar j, llc cmp) {
    mk_ineq(a, j, cmp, rational::zero());
}

void core:: mk_ineq(lpvar j, lpvar k, llc cmp, lemma& l) {
    mk_ineq(rational(1), j, rational(1), k, cmp, rational::zero());
}

void core:: mk_ineq(lpvar j, llc cmp) {
    mk_ineq(j, cmp, rational::zero());
}
    
// the monomials should be equal by modulo sign but this is not so in the model
void core:: fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign) {
    SASSERT(sign == 1 || sign == -1);
    explain(a, current_expl());
    explain(b, current_expl());
    TRACE("nla_solver",
          tout << "used constraints: ";
          for (auto &p :  current_expl())
              m_lar_solver.print_constraint(p.second, tout); tout << "\n";
          );
    SASSERT(current_ineqs().size() == 0);
    mk_ineq(rational(1), a.var(), -sign, b.var(), llc::EQ, rational::zero());
    TRACE("nla_solver", print_lemma(tout););
}

// Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
// Also sorts the result.
// 
svector<lpvar> core::reduce_monomial_to_rooted(const svector<lpvar> & vars, rational & sign) const {
    svector<lpvar> ret;
    bool s = false;
    for (lpvar v : vars) {
        auto root = m_evars.find(v);
        s ^= root.sign();
        TRACE("nla_solver_eq",
              print_var(v,tout);
              tout << " mapped to ";
              print_var(root.var(), tout););
        ret.push_back(root.var());
    }
    sign = rational(s? -1: 1);
    std::sort(ret.begin(), ret.end());
    return ret;
}


// Replaces definition m_v = v1* .. * vn by
// m_v = coeff * w1 * ... * wn, where w1, .., wn are canonical
// representatives, which are the roots of the equivalence tree, under current equations.
// 
monomial_coeff core::canonize_monomial(monomial const& m) const {
    rational sign = rational(1);
    svector<lpvar> vars = reduce_monomial_to_rooted(m.vars(), sign);
    return monomial_coeff(vars, sign);
}

lemma& core::current_lemma() { return m_lemma_vec->back(); }
const lemma& core::current_lemma() const { return m_lemma_vec->back(); }
vector<ineq>& core::current_ineqs() { return current_lemma().ineqs(); }
lp::explanation& core::current_expl() { return current_lemma().expl(); }
const lp::explanation& core::current_expl() const { return current_lemma().expl(); }


int core::vars_sign(const svector<lpvar>& v) {
    int sign = 1;
    for (lpvar j : v) {
        sign *= nla::rat_sign(val(j));
        if (sign == 0) 
            return 0;
    }
    return sign;
}

void core:: negate_strict_sign(lpvar j) {
    TRACE("nla_solver_details", print_var(j, tout););
    if (!vvr(j).is_zero()) {
        int sign = nla::rat_sign(vvr(j));
        mk_ineq(j, (sign == 1? llc::LE : llc::GE));
    } else {   // vvr(j).is_zero()
        if (has_lower_bound(j) && get_lower_bound(j) >= rational(0)) {
            explain_existing_lower_bound(j);
            mk_ineq(j, llc::GT);
        } else {
            SASSERT(has_upper_bound(j) && get_upper_bound(j) <= rational(0));
            explain_existing_upper_bound(j);
            mk_ineq(j, llc::LT);
        }
    }
}
    
void core:: generate_strict_case_zero_lemma(const monomial& m, unsigned zero_j, int sign_of_zj) {
    TRACE("nla_solver_bl", tout << "sign_of_zj = " << sign_of_zj << "\n";);
    // we know all the signs
    add_empty_lemma();
    mk_ineq(zero_j, (sign_of_zj == 1? llc::GT : llc::LT));
    for (unsigned j : m){
        if (j != zero_j) {
            negate_strict_sign(j);
        }
    }
    negate_strict_sign(m.var());
    TRACE("nla_solver", print_lemma(tout););
}

bool core:: has_upper_bound(lpvar j) const {
    return m_lar_solver.column_has_upper_bound(j);
} 

bool core:: has_lower_bound(lpvar j) const {
    return m_lar_solver.column_has_lower_bound(j);
} 
const rational& core::get_upper_bound(unsigned j) const {
    return m_lar_solver.get_upper_bound(j).x;
}

const rational& core::get_lower_bound(unsigned j) const {
    return m_lar_solver.get_lower_bound(j).x;
}
    
    
bool core::zero_is_an_inner_point_of_bounds(lpvar j) const {
    if (has_upper_bound(j) && get_upper_bound(j) <= rational(0))            
        return false;
    if (has_lower_bound(j) && get_lower_bound(j) >= rational(0))            
        return false;
    return true;
}
    
int core::rat_sign(const monomial& m) const {
    int sign = 1;
    for (lpvar j : m.vars()) {
        auto v = val(j);
        if (v.is_neg()) {
            sign = - sign;
            continue;
        }
        if (v.is_pos()) {
            continue;
        }
        sign = 0;
        break;
    }
    return sign;
}

// Returns true if the monomial sign is incorrect
bool core::sign_contradiction(const monomial& m) const {
    return  nla::rat_sign(val(m)) != rat_sign(m);
}

/*
  unsigned_vector eq_vars(lpvar j) const {
  TRACE("nla_solver_eq", tout << "j = "; print_var(j, tout); tout << "eqs = ";
  for(auto jj : m_evars.eq_vars(j)) {
  print_var(jj, tout);
  });
  return m_evars.eq_vars(j);
  }
*/

// Monomials m and n vars have the same values, up to "sign"
// Generate a lemma if values of m.var() and n.var() are not the same up to sign
bool core:: basic_sign_lemma_on_two_monomials(const monomial& m, const monomial& n, const rational& sign) {
    if (vvr(m) == vvr(n) *sign)
        return false;
    TRACE("nla_solver", tout << "sign contradiction:\nm = "; print_monomial_with_vars(m, tout); tout << "n= "; print_monomial_with_vars(n, tout); tout << "sign: " << sign << "\n";);
    generate_sign_lemma(m, n, sign);
    return true;
}

void core:: basic_sign_lemma_model_based_one_mon(const monomial& m, int product_sign) {
    if (product_sign == 0) {
        TRACE("nla_solver_bl", tout << "zero product sign\n";);
        generate_zero_lemmas(m);
    } else {
        add_empty_lemma();
        for(lpvar j: m) {
            negate_strict_sign(j);
        }
        mk_ineq(m.var(), product_sign == 1? llc::GT : llc::LT);
        TRACE("nla_solver", print_lemma(tout); tout << "\n";);
    }
}
    
bool core:: basic_sign_lemma_model_based() {
    unsigned i = random() % m_to_refine.size();
    unsigned ii = i;
    do {
        const monomial& m = m_monomials[m_to_refine[i]];
        int mon_sign = nla::rat_sign(vvr(m));
        int product_sign = rat_sign(m);
        if (mon_sign != product_sign) {
            basic_sign_lemma_model_based_one_mon(m, product_sign);
            if (done())
                return true;
        }
        i++;
        if (i == m_to_refine.size())
            i = 0;
    } while (i != ii);
    return m_lemma_vec->size() > 0;
}

    
bool core:: basic_sign_lemma_on_mon(unsigned i, std::unordered_set<unsigned> & explored){
    const monomial& m = m_monomials[i];
    TRACE("nla_solver_details", tout << "i = " << i << ", mon = "; print_monomial_with_vars(m, tout););
    const index_with_sign&  rm_i_s = m_rm_table.get_rooted_mon(i);
    unsigned k = rm_i_s.index();
    if (!try_insert(k, explored))
        return false;

    const auto& mons_to_explore = m_rm_table.rms()[k].m_mons;
    TRACE("nla_solver", tout << "rm = "; print_rooted_monomial_with_vars(m_rm_table.rms()[k], tout) << "\n";);
        
    for (index_with_sign i_s : mons_to_explore) {
        TRACE("nla_solver", tout << "i_s = (" << i_s.index() << "," << i_s.sign() << ")\n";
              print_monomial_with_vars(m_monomials[i_s.index()], tout << "m = ") << "\n";
              {
                  for (lpvar j : m_monomials[i_s.index()] ) {
                      lpvar rj = m_evars.find(j).var();
                      if (j == rj)
                          tout << "rj = j ="  << j << "\n";
                      else {
                          lp::explanation e;
                          m_evars.explain(j, e);
                          tout << "j = " << j << ", e = "; print_explanation(e, tout) << "\n";
                      }
                  }
              }
              );
        unsigned n = i_s.index();
        if (n == i) continue;
        if (basic_sign_lemma_on_two_monomials(m, m_monomials[n], rm_i_s.sign()*i_s.sign()))
            if(done())
                return true;
    }
    TRACE("nla_solver_details", tout << "return false\n";);
    return false;
}

/**
 * \brief <generate lemma by using the fact that -ab = (-a)b) and
 -ab = a(-b)
*/
bool core:: basic_sign_lemma(bool derived) {
    if (!derived)
        return basic_sign_lemma_model_based();

    std::unordered_set<unsigned> explored;
    for (unsigned i : m_to_refine){
        if (basic_sign_lemma_on_mon(i, explored))
            return true;
    }
    return false;
}

bool core:: var_is_fixed_to_zero(lpvar j) const {
    return 
        m_lar_solver.column_has_upper_bound(j) &&
        m_lar_solver.column_has_lower_bound(j) &&
        m_lar_solver.get_upper_bound(j) == lp::zero_of_type<lp::impq>() &&
        m_lar_solver.get_lower_bound(j) == lp::zero_of_type<lp::impq>();
}
bool core:: var_is_fixed_to_val(lpvar j, const rational& v) const {
    return 
        m_lar_solver.column_has_upper_bound(j) &&
        m_lar_solver.column_has_lower_bound(j) &&
        m_lar_solver.get_upper_bound(j) == lp::impq(v) && m_lar_solver.get_lower_bound(j) == lp::impq(v);
}

bool core:: var_is_fixed(lpvar j) const {
    return 
        m_lar_solver.column_has_upper_bound(j) &&
        m_lar_solver.column_has_lower_bound(j) &&
        m_lar_solver.get_upper_bound(j) == m_lar_solver.get_lower_bound(j);
}
    
std::ostream & core::print_ineq(const ineq & in, std::ostream & out) const {
    m_lar_solver.print_term(in.m_term, out);
    out << " " << lconstraint_kind_string(in.m_cmp) << " " << in.m_rs;
    return out;
}

std::ostream & core::print_var(lpvar j, std::ostream & out) const {
    if (m_emons.is_monomial_var(j)) {
        print_monomial(m_emons[j], out);
    }
        
    m_lar_solver.print_column_info(j, out);
    signed_var jr = m_evars.find(j);
    out << "root=" << (jr.sign()? "-v":"v") << jr.var() << "\n";
    return out;
}

std::ostream & core::print_monomials(std::ostream & out) const {
    for (auto &m : m_emons) {
        print_monomial_with_vars(m, out);
    }
    return out;
}    

std::ostream & core::print_ineqs(const lemma& l, std::ostream & out) const {
    std::unordered_set<lpvar> vars;
    out << "ineqs: ";
    if (l.ineqs().size() == 0) {
        out << "conflict\n";
    } else {
        for (unsigned i = 0; i < l.ineqs().size(); i++) {
            auto & in = l.ineqs()[i]; 
            print_ineq(in, out);
            if (i + 1 < l.ineqs().size()) out << " or ";
            for (const auto & p: in.m_term)
                vars.insert(p.var());
        }
        out << std::endl;
        for (lpvar j : vars) {
            print_var(j, out);
        }
        out << "\n";
    }
    return out;
}
    
std::ostream & core::print_factorization(const factorization& f, std::ostream& out) const {
    if (f.is_mon()){
        out << "is_mon " << pp_mon(*this, f.mon());
    } 
    else {
        for (unsigned k = 0; k < f.size(); k++ ) {
            print_factor(f[k], out);
            if (k < f.size() - 1)
                out << "*";
        }
    }
    return out;
}
    
bool core::find_canonical_monomial_of_vars(const svector<lpvar>& vars, lpvar & i) const {
    monomial const* sv = m_emons.find_canonical(vars);
    return sv && (i = sv->var(), true);
}

bool core::is_canonical_monomial(lpvar j) const {
    return m_emons.is_canonical_monomial(j);
}


void core::explain_existing_lower_bound(lpvar j) {
    SASSERT(has_lower_bound(j));
    current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
}

void core::explain_existing_upper_bound(lpvar j) {
    SASSERT(has_upper_bound(j));
    current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
}
    
void core::explain_separation_from_zero(lpvar j) {
    SASSERT(!val(j).is_zero());
    if (val(j).is_pos())
        explain_existing_lower_bound(j);
    else
        explain_existing_upper_bound(j);
}

void core::trace_print_monomial_and_factorization(const monomial& rm, const factorization& f, std::ostream& out) const {
    out << "rooted vars: ";
    print_product(rm.rvars(), out);
    out << "\n";
        
    out << "mon:  " << pp_mon(*this, rm.var()) << "\n";
    out << "value: " << val(rm) << "\n";
    print_factorization(f, out << "fact: ") << "\n";
}

void core::explain_var_separated_from_zero(lpvar j) {
    SASSERT(var_is_separated_from_zero(j));
    if (m_lar_solver.column_has_upper_bound(j) && (m_lar_solver.get_upper_bound(j)< lp::zero_of_type<lp::impq>())) 
        current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
    else 
        current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
}

void core::explain_fixed_var(lpvar j) {
    SASSERT(var_is_fixed(j));
    current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
    current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
}

bool core:: var_has_positive_lower_bound(lpvar j) const {
    return m_lar_solver.column_has_lower_bound(j) && m_lar_solver.get_lower_bound(j) > lp::zero_of_type<lp::impq>();
}

bool core:: var_has_negative_upper_bound(lpvar j) const {
    return m_lar_solver.column_has_upper_bound(j) && m_lar_solver.get_upper_bound(j) < lp::zero_of_type<lp::impq>();
}
    
bool core:: var_is_separated_from_zero(lpvar j) const {
    return
        var_has_negative_upper_bound(j) ||
        var_has_positive_lower_bound(j);
}
    
// x = 0 or y = 0 -> xy = 0
bool core:: basic_lemma_for_mon_non_zero_derived(const rooted_mon& rm, const factorization& f) {
    TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););
    if (!var_is_separated_from_zero(var(rm)))
        return false; 
    int zero_j = -1;
    for (auto j : f) {
        if (var_is_fixed_to_zero(var(j))) {
            zero_j = var(j);
            break;
        }
    }

    if (zero_j == -1) {
        return false;
    } 
    add_empty_lemma();
    explain_fixed_var(zero_j);
    explain_var_separated_from_zero(var(rm));
    explain(rm, current_expl());
    TRACE("nla_solver", print_lemma(tout););
    return true;
}

// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
bool core:: basic_lemma_for_mon_neutral_monomial_to_factor_model_based(const rooted_mon& rm, const factorization& f) {
    TRACE("nla_solver_bl", trace_print_monomial_and_factorization(rm, f, tout););

    lpvar mon_var = m_monomials[rm.orig_index()].var();
    TRACE("nla_solver_bl", trace_print_monomial_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto & mv = vvr(mon_var);
    const auto  abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    lpvar jl = -1;
    for (auto j : f ) {
        if (abs(vvr(j)) == abs_mv) {
            jl = var(j);
            break;
        }
    }
    if (jl == static_cast<lpvar>(-1))
        return false;
    lpvar not_one_j = -1;
    for (auto j : f ) {
        if (var(j) == jl) {
            continue;
        }
        if (abs(vvr(j)) != rational(1)) {
            not_one_j = var(j);
            break;
        }
    }

bool core::vars_are_equiv(lpvar a, lpvar b) const {
    SASSERT(abs(val(a)) == abs(val(b)));
    return m_evars.vars_are_equiv(a, b);
}

    
void core::explain_equiv_vars(lpvar a, lpvar b) {
    SASSERT(abs(val(a)) == abs(val(b)));
    if (m_evars.vars_are_equiv(a, b)) {
        explain(a, current_expl());
        explain(b, current_expl());
    } else {
        explain_fixed_var(a);
        explain_fixed_var(b);
    }
}

// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
bool core:: basic_lemma_for_mon_neutral_monomial_to_factor_derived(const rooted_mon& rm, const factorization& f) {
    TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););

    lpvar mon_var = m_monomials[rm.orig_index()].var();
    TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto & mv = vvr(mon_var);
    const auto  abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    bool mon_var_is_sep_from_zero = var_is_separated_from_zero(mon_var);
    lpvar jl = -1;
    for (auto fc : f ) {
        lpvar j = var(fc);
        if (abs(vvr(j)) == abs_mv && vars_are_equiv(j, mon_var) &&
            (mon_var_is_sep_from_zero || var_is_separated_from_zero(j))) {
            jl = j;
            break;
        }
    }
    if (jl == static_cast<lpvar>(-1))
        return false;
        
    lpvar not_one_j = -1;
    for (auto j : f ) {
        if (var(j) == jl) {
            continue;
        }
        if (abs(vvr(j)) != rational(1)) {
            not_one_j = var(j);
            break;
        }
    }

    if (not_one_j == static_cast<lpvar>(-1)) {
        return false;
    } 

    add_empty_lemma();
    // mon_var = 0
    if (mon_var_is_sep_from_zero)
        explain_var_separated_from_zero(mon_var);
    else
        explain_var_separated_from_zero(jl);

    explain_equiv_vars(mon_var, jl);
        
    // not_one_j = 1
    mk_ineq(not_one_j, llc::EQ,  rational(1));   
        
    // not_one_j = -1
    mk_ineq(not_one_j, llc::EQ, -rational(1));
    explain(rm, current_expl());
    TRACE("nla_solver", print_lemma(tout); );
    return true;
}

// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool core:: basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(const rooted_mon& rm, const factorization& f) {
    rational sign = rm.orig_sign();
    TRACE("nla_solver_bl", tout << "f = "; print_factorization(f, tout); tout << ", sign = " << sign << '\n'; );
    lpvar not_one = -1;
    for (auto j : f){
        TRACE("nla_solver_bl", tout << "j = "; print_factor_with_vars(j, tout););
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }
            
        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 
            
        if (not_one == static_cast<lpvar>(-1)) {
            not_one = var(j);
            continue;
        }
            
        // if we are here then there are at least two factors with absolute values different from one : cannot create the lemma
        return false;
    }

    if (not_one + 1) {
        // we found the only not_one
        if (vvr(rm) == vvr(not_one) * sign) {
            TRACE("nla_solver", tout << "the whole equal to the factor" << std::endl;);
            return false;
        }
    } else {
        // we have +-ones only in the factorization
        if (vvr(rm) == sign) {
            return false;
        }
    }

    TRACE("nla_solver_bl", tout << "not_one = " << not_one << "\n";);
        
    add_empty_lemma();

    for (auto j : f){
        lpvar var_j = var(j);
        if (not_one == var_j) continue;
        mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) : canonize_sign(j) * vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        mk_ineq(m_monomials[rm.orig_index()].var(), llc::EQ, sign);
    } else {
        mk_ineq(m_monomials[rm.orig_index()].var(), -sign, not_one, llc::EQ);
    }
    explain(rm, current_expl());
    explain(f, current_expl());
    TRACE("nla_solver",
          print_lemma(tout);
          tout << "rm = "; print_rooted_monomial_with_vars(rm, tout);
          );
    return true;
}
// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool core:: basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based_fm(const monomial& m) {
    lpvar not_one = -1;
    rational sign(1);
    TRACE("nla_solver_bl", tout << "m = "; print_monomial(m, tout););
    for (auto j : m){
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }
        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 
        if (not_one == static_cast<lpvar>(-1)) {
            not_one = j;
            continue;
        }
        // if we are here then there are at least two factors with values different from one and minus one: cannot create the lemma
        return false;
    }

    if (not_one + 1) {  // we found the only not_one
        if (vvr(m) == vvr(not_one) * sign) {
            TRACE("nla_solver", tout << "the whole equal to the factor" << std::endl;);
            return false;
        }
    }
        
    add_empty_lemma();
    for (auto j : m){
        if (not_one == j) continue;
        mk_ineq(j, llc::NE, vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        mk_ineq(m.var(), llc::EQ, sign);
    } else {
        mk_ineq(m.var(), -sign, not_one, llc::EQ);
    }
    TRACE("nla_solver",  print_lemma(tout););
    return true;
}
// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool core:: basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(const rooted_mon& rm, const factorization& f) {
    return false;
    rational sign = rm.orig().m_sign;
    lpvar not_one = -1;

    TRACE("nla_solver", tout << "f = "; print_factorization(f, tout););
    for (auto j : f){
        TRACE("nla_solver", tout << "j = "; print_factor_with_vars(j, tout););
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }

        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 

        if (not_one == static_cast<lpvar>(-1)) {
            not_one = var(j);
            continue;
        }

        // if we are here then there are at least two factors with values different from one and minus one: cannot create the lemma
        return false;
    }

    add_empty_lemma();
    explain(rm, current_expl());

    for (auto j : f){
        lpvar var_j = var(j);
        if (not_one == var_j) continue;
        mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) : canonize_sign(j) * vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        mk_ineq(m_monomials[rm.orig_index()].var(), llc::EQ, sign);
    } else {
        mk_ineq(m_monomials[rm.orig_index()].var(), -sign, not_one, llc::EQ);
    }
    TRACE("nla_solver",
          tout << "rm = "; print_rooted_monomial_with_vars(rm, tout);
          print_lemma(tout););
    return true;
}
void core::basic_lemma_for_mon_neutral_model_based(const rooted_mon& rm, const factorization& f) {
    if (f.is_mon()) {
        basic_lemma_for_mon_neutral_monomial_to_factor_model_based_fm(*f.mon());
        basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based_fm(*f.mon());
    }
    else {
        basic_lemma_for_mon_neutral_monomial_to_factor_model_based(rm, f);
        basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(rm, f);
    }
}
    
bool core:: basic_lemma_for_mon_neutral_derived(const rooted_mon& rm, const factorization& factorization) {
    return
        basic_lemma_for_mon_neutral_monomial_to_factor_derived(rm, factorization) || 
        basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(rm, factorization);
    return false;
}

void core::explain(const factorization& f, lp::explanation& exp) {
    SASSERT(!f.is_mon());
    for (const auto& fc : f) {
        explain(fc, exp);
    }
}

bool core:: has_zero_factor(const factorization& factorization) const {
    for (factor f : factorization) {
        if (val(f).is_zero())
            return true;
    }
    return false;
}


template <typename T>
bool core:: mon_has_zero(const T& product) const {
    for (lpvar j: product) {
        if (val(j).is_zero())
            return true;
    }
    return false;
}

template bool core::mon_has_zero<unsigned_vector>(const unsigned_vector& product) const;


lp::lp_settings& core::settings() {
    return m_lar_solver.settings();
}
const lp::lp_settings& core::settings() const {
    return m_lar_solver.settings();
}
    
unsigned core::random() { return settings().random_next(); }
    

// we look for octagon constraints here, with a left part  +-x +- y 
void core::collect_equivs() {
    const lp::lar_solver& s = m_lar_solver;

    for (unsigned i = 0; i < s.terms().size(); i++) {
        unsigned ti = i + s.terms_start_index();
        if (!s.term_is_used_as_row(ti))
            continue;
        lpvar j = s.external_to_local(ti);
        if (var_is_fixed_to_zero(j)) {
            TRACE("nla_solver_eq", tout << "term = "; s.print_term(*s.terms()[i], tout););
            add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
        }
    }
}

void core::collect_equivs_of_fixed_vars() {
    std::unordered_map<rational, svector<lpvar> > abs_map;
    for (lpvar j = 0; j < m_lar_solver.number_of_vars(); j++) {
        if (!var_is_fixed(j))
            continue;
        rational v = abs(val(j));
        auto it = abs_map.find(v);
        if (it == abs_map.end()) {
            abs_map[v] = svector<lpvar>();
            abs_map[v].push_back(j);
        } else {
            it->second.push_back(j);
        }
    }
    for (auto p : abs_map) {
        svector<lpvar>& v = p.second;
        lpvar head = v[0];
        auto c0 = m_lar_solver.get_column_upper_bound_witness(head);
        auto c1 = m_lar_solver.get_column_lower_bound_witness(head);
        for (unsigned k = 1; k < v.size(); k++) {
            auto c2 = m_lar_solver.get_column_upper_bound_witness(v[k]);
            auto c3 = m_lar_solver.get_column_lower_bound_witness(v[k]);
            if (val(head) == val(v[k])) {
                m_evars.merge_plus(head, v[k], eq_justification({c0, c1, c2, c3}));
            } else {
                SASSERT(val(head) == -val(v[k]));
                m_evars.merge_minus(head, v[k], eq_justification({c0, c1, c2, c3}));
            }
        }
    }
}

// returns true iff the term is in a form +-x-+y.
// the sign is true iff the term is x+y, -x-y.
bool core:: is_octagon_term(const lp::lar_term& t, bool & sign, lpvar& i, lpvar &j) const {
    if (t.size() != 2)
        return false;
    bool seen_minus = false;
    bool seen_plus = false;
    i = -1;
    for(const auto & p : t) {
        const auto & c = p.coeff();
        if (c == 1) {
            seen_plus = true;
        } else if (c == - 1) {
            seen_minus = true;
        } else {
            return false;
        }
        if (i == static_cast<lpvar>(-1))
            i = p.var();
        else
            j = p.var();
    }
    SASSERT(j != static_cast<unsigned>(-1));
    sign = (seen_minus && seen_plus)? false : true;
    return true;
}
    
void core::add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1) {
    bool sign;
    lpvar i, j;
    if (!is_octagon_term(*t, sign, i, j))
        return;
    if (sign)
        m_evars.merge_minus(i, j, eq_justification({c0, c1}));
    else 
        m_evars.merge_plus(i, j, eq_justification({c0, c1}));
}

// x is equivalent to y if x = +- y
void core::init_vars_equivalence() {
    collect_equivs();
    //    SASSERT(tables_are_ok());
}
    
bool core:: tables_are_ok() const {
    return vars_table_is_ok() && rm_table_is_ok();
}
    
bool core:: var_is_a_root(lpvar j) const { return m_evars.is_root(j); }

template <typename T>
bool core:: vars_are_roots(const T& v) const {
    for (lpvar j: v) {
        if (!var_is_a_root(j))
            return false;
    }
    return true;
}



template <typename T>
void core::trace_print_rms(const T& p, std::ostream& out) {
    out << "p = {\n";
    for (auto j : p) {
        out << "j = " << j << ", rm = " << m_emons[j] << "\n";
    }
    out << "}";
}

void core::print_monomial_stats(const monomial& m, std::ostream& out) {
    if (m.size() == 2) return;
    monomial_coeff mc = canonize_monomial(m);
    for(unsigned i = 0; i < mc.vars().size(); i++){
        if (abs(val(mc.vars()[i])) == rational(1)) {
            auto vv = mc.vars();
            vv.erase(vv.begin()+i);
            monomial const* sv = m_emons.find_canonical(vv);
            if (!sv) {
                out << "nf length" << vv.size() << "\n"; ;
            }
        }
    }
}
    
void core::print_stats(std::ostream& out) {
}
        

void core::clear() {
    m_lemma_vec->clear();
}
    
void core::init_search() {
    clear();
    init_vars_equivalence();
    SASSERT(elists_are_consistent(false));
}

void core::init_to_refine() {
    TRACE("nla_solver", tout << "emons:" << pp_emons(*this, m_emons););
    m_to_refine.clear();
    for (auto const & m : m_emons) 
        if (!check_monomial(m)) 
            m_to_refine.push_back(m.var());
    
    TRACE("nla_solver", 
          tout << m_to_refine.size() << " mons to refine:\n";
          for (lpvar v : m_to_refine) tout << pp_mon(*this, m_emons[v]) << "\n";);
}
        
std::unordered_set<lpvar> core::collect_vars(const lemma& l) const {
    std::unordered_set<lpvar> vars;
    auto insert_j = [&](lpvar j) { 
        vars.insert(j);
        if (m_emons.is_monomial_var(j)) {
            for (lpvar k : m_emons[j].vars())
                vars.insert(k);
        }
    };
    
    for (const auto& i : current_lemma().ineqs()) {
        for (const auto& p : i.term()) {                
            insert_j(p.var());
        }
    }
    for (const auto& p : current_expl()) {
        const auto& c = m_lar_solver.get_constraint(p.second);
        for (const auto& r : c.coeffs()) {
            insert_j(r.second);
        }
    }
    return vars;
}

// divides bc by c, so bc = b*c
bool core::divide(const monomial& bc, const factor& c, factor & b) const {
    svector<lpvar> c_rvars = sorted_rvars(c);
    TRACE("nla_solver_div", tout << "c_rvars = "; print_product(c_rvars, tout); tout << "\nbc_rvars = "; print_product(bc.rvars(), tout););
    if (!lp::is_proper_factor(c_rvars, bc.rvars()))
        return false;
            
    auto b_rvars = lp::vector_div(bc.rvars(), c_rvars);
    TRACE("nla_solver_div", tout << "b_rvars = "; print_product(b_rvars, tout););
    SASSERT(b_rvars.size() > 0);
    if (b_rvars.size() == 1) {
        b = factor(b_rvars[0], factor_type::VAR);
    } else {
        monomial const* sv = m_emons.find_canonical(b_rvars);
        if (sv == nullptr) {
            TRACE("nla_solver_div", tout << "not in rooted";);
            return false;
        }
        b = factor(sv->var(), factor_type::MON);
    }
    SASSERT(!b.sign());
    // We have bc = canonize_sign(bc)*bc.rvars() = canonize_sign(b)*b.rvars()*canonize_sign(c)*c.rvars().
    // Dividing by bc.rvars() we get canonize_sign(bc) = canonize_sign(b)*canonize_sign(c)
    // Currently, canonize_sign(b) is 1, we might need to adjust it
    b.sign() = canonize_sign(b) ^ canonize_sign(c) ^ canonize_sign(bc); 
    TRACE("nla_solver", tout << "success div:"; print_factor(b, tout););
    return true;
}

void core::negate_factor_equality(const factor& c,
                                  const factor& d) {
    if (c == d)
        return;
    lpvar i = var(c);
    lpvar j = var(d);
    auto iv = val(i), jv = val(j);
    SASSERT(abs(iv) == abs(jv));
    if (iv == jv) {
        mk_ineq(i, -rational(1), j, llc::NE);
    } else { // iv == -jv
        mk_ineq(i, j, llc::NE, current_lemma());                
    }
}
    
void core::negate_factor_relation(const rational& a_sign, const factor& a, const rational& b_sign, const factor& b) {
    rational a_fs = sign_to_rat(canonize_sign(a));
    rational b_fs = sign_to_rat(canonize_sign(b));
    llc cmp = a_sign*val(a) < b_sign*val(b)? llc::GE : llc::LE;
    mk_ineq(a_fs*a_sign, var(a), - b_fs*b_sign, var(b), cmp);
}

std::ostream& core::print_lemma(std::ostream& out) const {
    print_specific_lemma(current_lemma(), out);
    return out;
}

void core::print_specific_lemma(const lemma& l, std::ostream& out) const {
    static int n = 0;
    out << "lemma:" << ++n << " ";
    print_ineqs(l, out);
    print_explanation(l.expl(), out);
    std::unordered_set<lpvar> vars = collect_vars(current_lemma());
        
    for (lpvar j : vars) {
        print_var(j, out);
    }
}
    

void core::trace_print_ol(const monomial& ac,
                          const factor& a,
                          const factor& c,
                          const monomial& bc,
                          const factor& b,
                          std::ostream& out) {
    out << "ac = " << pp_mon(*this, ac) << "\n";
    out << "bc = " << pp_mon(*this, bc) << "\n";
    out << "a = ";
    print_factor_with_vars(a, out);
    out << ", \nb = ";
    print_factor_with_vars(b, out);
    out << "\nc = ";
    print_factor_with_vars(c, out);
}
    
void core::maybe_add_a_factor(lpvar i,
                              const factor& c,
                              std::unordered_set<lpvar>& found_vars,
                              std::unordered_set<unsigned>& found_rm,
                              vector<factor> & r) const {
    SASSERT(abs(val(i)) == abs(val(c)));
    if (!m_emons.is_monomial_var(i)) {
        i = m_evars.find(i).var();
        if (try_insert(i, found_vars)) {
            r.push_back(factor(i, factor_type::VAR));
        }
    } else {
        if (try_insert(i, found_rm)) {
            r.push_back(factor(i, factor_type::MON));
            TRACE("nla_solver", tout << "inserting factor = "; print_factor_with_vars(factor(i, factor_type::MON), tout); );
        }
    }
}
    

// Returns rooted monomials by arity
std::unordered_map<unsigned, unsigned_vector> core::get_rm_by_arity() {
    std::unordered_map<unsigned, unsigned_vector> m;
    for (auto const& mon : m_emons) {
        unsigned arity = mon.vars().size();
        auto it = m.find(arity);
        if (it == m.end()) {
            it = m.insert(it, std::make_pair(arity, unsigned_vector()));
        }
        it->second.push_back(mon.var());
    }
    return m;
}

    

bool core::rm_check(const monomial& rm) const {
    return check_monomial(m_emons[rm.var()]);
}
    


/**
   \brief Add |v| ~ |bound|
   where ~ is <, <=, >, >=, 
   and bound = val(v)

   |v| > |bound| 
   <=> 
   (v < 0 or v > |bound|) & (v > 0 or -v > |bound|)        
   => Let s be the sign of val(v)
   (s*v < 0 or s*v > |bound|)         

   |v| < |bound|
   <=>
   v < |bound| & -v < |bound| 
   => Let s be the sign of val(v)
   s*v < |bound|

*/

void core::add_abs_bound(lpvar v, llc cmp) {
    add_abs_bound(v, cmp, val(v));
}

void core::add_abs_bound(lpvar v, llc cmp, rational const& bound) {
    SASSERT(!val(v).is_zero());
    lp::lar_term t;  // t = abs(v)
    t.add_coeff_var(rrat_sign(val(v)), v);

    switch (cmp) {
    case llc::GT:
    case llc::GE:  // negate abs(v) >= 0
        mk_ineq(t, llc::LT, rational(0));
        break;
    case llc::LT:
    case llc::LE:
        break;
    default:
        UNREACHABLE();
        break;
    }
    mk_ineq(t, cmp, abs(bound));
}

// NB - move this comment to monotonicity or appropriate.
/** \brief enforce the inequality |m| <= product |m[i]| .
    by enforcing lemma:
    /\_i |m[i]| <= |val(m[i])| => |m| <= |product_i val(m[i])|
    <=>
    \/_i |m[i]| > |val(m[i])} or |m| <= |product_i val(m[i])|
*/

    
bool core::find_bfc_to_refine_on_monomial(const monomial& m, factorization & bf) {
    for (auto f : factorization_factory_imp(m, *this)) {
        if (f.size() == 2) {
            auto a = f[0];
            auto b = f[1];
            if (val(m) != val(a) * val(b)) {
                bf = f;
                TRACE("nla_solver", tout << "found bf";
                      tout << ":m:" << pp_rmon(*this, m) << "\n";
                      tout << "bf:"; print_bfc(bf, tout););
                      
                return true;
            }
        }
    }
    return false;
}

// finds a monomial to refine with its binary factorization
bool core::find_bfc_to_refine(const monomial* & m, factorization & bf){
    m = nullptr;
    unsigned r = random(), sz = m_to_refine.size();
    for (unsigned k = 0; k < sz; k++) {
        lpvar i = m_to_refine[(k + r) % sz];
        m = &m_emons[i];
        SASSERT (!check_monomial(*m));
        if (m->size() == 2) {
            bf.set_mon(m);
            bf.push_back(factor(m->vars()[0], factor_type::VAR));
            bf.push_back(factor(m->vars()[1], factor_type::VAR));
            return true;
        }
                
        if (find_bfc_to_refine_on_monomial(*m, bf)) {
            TRACE("nla_solver",
                  tout << "bf = "; print_factorization(bf, tout);
                  tout << "\nval(*m) = " << val(*m) << ", should be = (val(bf[0])=" << val(bf[0]) << ")*(val(bf[1]) = " << val(bf[1]) << ") = " << val(bf[0])*val(bf[1]) << "\n";);
            return true;
        } 
    }
    return false;
}

rational core::val(const factorization& f) const {
    rational r(1);
    for (const factor &p : f) {
        r *= val(p);
    }
    return r;
}

void core::add_empty_lemma() {
    m_lemma_vec->push_back(lemma());
}
    
void core::generate_tang_plane(const rational & a, const rational& b, const factor& x, const factor& y, bool below, lpvar j, const rational& j_sign) {
    lpvar jx = var(x);
    lpvar jy = var(y);
    add_empty_lemma();
    negate_relation(jx, a);
    negate_relation(jy, b);
    bool sbelow = j_sign.is_pos()? below: !below;
#if Z3DEBUG
    int mult_sign = nla::rat_sign(a - vvr(jx))*nla::rat_sign(b - vvr(jy));
    SASSERT((mult_sign == 1) == sbelow);
    // If "mult_sign is 1"  then (a - x)(b-y) > 0 and ab - bx - ay + xy > 0
    // or -ab + bx + ay < xy or -ay - bx + xy > -ab
    // j_sign*vvr(j) stands for xy. So, finally we have  -ay - bx + j_sign*j > - ab
#endif

    lp::lar_term t;
    t.add_coeff_var(-a, jy);
    t.add_coeff_var(-b, jx);
    t.add_coeff_var( j_sign, j);
    mk_ineq(t, sbelow? llc::GT : llc::LT, - a*b);
}  

void core::negate_relation(unsigned j, const rational& a) {
    SASSERT(val(j) != a);
    if (val(j) < a) {
        mk_ineq(j, llc::GE, a);
    }
    else {
        mk_ineq(j, llc::LE, a);
    }
}
    
void core::generate_two_tang_lines(const bfc & bf, const point& xy, const rational& sign, lpvar j) {
    add_empty_lemma();
    mk_ineq(var(bf.m_x), llc::NE, xy.x);
    mk_ineq(sign, j, - xy.x, var(bf.m_y), llc::EQ);
        
    add_empty_lemma();
    mk_ineq(var(bf.m_y), llc::NE, xy.y);
    mk_ineq(sign, j, - xy.y, var(bf.m_x), llc::EQ);
        
}
// Get two planes tangent to surface z = xy, one at point a,  and another at point b.
// One can show that these planes still create a cut.
void core::get_initial_tang_points(point &a, point &b, const point& xy,
                                   bool below) const {
    const rational& x = xy.x;
    const rational& y = xy.y;
    if (!below){
        a = point(x - rational(1), y + rational(1));
        b = point(x + rational(1), y - rational(1));
    }
    else {
        a = point(x - rational(1), y - rational(1));
        b = point(x + rational(1), y + rational(1));
    }
}

void core::push_tang_point(point &a, const point& xy, bool below, const rational& correct_val, const rational& val) const {
    SASSERT(correct_val ==  xy.x * xy.y);
    int steps = 10;
    point del = a - xy;
    while (steps--) {
        del *= rational(2);
        point na = xy + del;
        TRACE("nla_solver", tout << "del = "; print_point(del, tout); tout << std::endl;);
        if (!plane_is_correct_cut(na, xy, correct_val, val, below)) {
            TRACE("nla_solver_tp", tout << "exit";tout << std::endl;);
            return;
        }
        a = na;
    }
}
    
void core::push_tang_points(point &a, point &b, const point& xy, bool below, const rational& correct_val, const rational& val) const {
    push_tang_point(a, xy, below, correct_val, val);
    push_tang_point(b, xy, below, correct_val, val);
}

rational core::tang_plane(const point& a, const point& x) const {
    return  a.x * x.y + a.y * x.x - a.x * a.y;
}

bool core:: plane_is_correct_cut(const point& plane,
                                 const point& xy,
                                 const rational & correct_val,                             
                                 const rational & val,
                                 bool below) const {
    SASSERT(correct_val ==  xy.x * xy.y);
    if (below && val > correct_val) return false;
    rational sign = below? rational(1) : rational(-1);
    rational px = tang_plane(plane, xy);
    return ((correct_val - px)*sign).is_pos() && !((px - val)*sign).is_neg();
        
}

// "below" means that the val is below the surface xy 
void core::get_tang_points(point &a, point &b, bool below, const rational& val,
                           const point& xy) const {
    get_initial_tang_points(a, b, xy, below);
    auto correct_val = xy.x * xy.y;
    TRACE("nla_solver", tout << "xy = "; print_point(xy, tout); tout << ", correct val = " << xy.x * xy.y;
          tout << "\ntang points:"; print_tangent_domain(a, b, tout);tout << std::endl;);
    TRACE("nla_solver", tout << "tang_plane(a, xy) = " << tang_plane(a, xy) << " , val = " << val;
          tout << "\ntang_plane(b, xy) = " << tang_plane(b, xy); tout << std::endl;);
    SASSERT(plane_is_correct_cut(a, xy, correct_val, val, below));
    SASSERT(plane_is_correct_cut(b, xy, correct_val, val, below));
    push_tang_points(a, b, xy, below, correct_val, val);
    TRACE("nla_solver", tout << "pushed a = "; print_point(a, tout); tout << "\npushed b = "; print_point(b, tout); tout << std::endl;);
}

bool core:: conflict_found() const {
    for (const auto & l : * m_lemma_vec) {
        if (l.is_conflict())
            return true;
    }
    return false;
}

bool core:: done() const {
    return m_lemma_vec->size() >= 10 || conflict_found();
}
        
lbool core:: inner_check(bool derived) {
    for (int search_level = 0; search_level < 3 && !done(); search_level++) {
        TRACE("nla_solver", tout << "derived = " << derived << ", search_level = " << search_level << "\n";);
        if (search_level == 0) {
            m_basics.basic_lemma(derived);
            if (!m_lemma_vec->empty())
                return l_false;
        }
        if (derived) continue;
        TRACE("nla_solver", tout << "passed derived and basic lemmas\n";);
        SASSERT(elists_are_consistent(true));
        if (search_level == 1) {
            m_order.order_lemma();
        } else { // search_level == 2
            m_monotone. monotonicity_lemma();
            m_tangents.tangent_lemma();
        }
    }
    return m_lemma_vec->empty()? l_undef : l_false;
}

bool core::elist_is_consistent(const std::unordered_set<lpvar> & list) const {
    bool first = true;
    bool p;
    for (lpvar j : list) {
        if (first) {
            p = check_monomial(m_emons[j]);
            first = false;
        } else 
            if (check_monomial(m_emons[j]) != p)
                return false;
    }
    return true;
}

bool core::elists_are_consistent(bool check_in_model) const {
    std::unordered_map<unsigned_vector, std::unordered_set<lpvar>, hash_svector> lists;
    if (!m_emons.elists_are_consistent(lists))
        return false;

    if (!check_in_model)
        return true;
    for (const auto & p : lists) {
        if (! elist_is_consistent(p.second))
            return false;
    }
    return true;
}

lbool core::check(vector<lemma>& l_vec) {
    settings().st().m_nla_calls++;
    TRACE("nla_solver", tout << "calls = " << settings().st().m_nla_calls << "\n";);
    m_lemma_vec =  &l_vec;
    if (!(m_lar_solver.get_status() == lp::lp_status::OPTIMAL || m_lar_solver.get_status() == lp::lp_status::FEASIBLE )) {
        TRACE("nla_solver", tout << "unknown because of the m_lar_solver.m_status = " << m_lar_solver.get_status() << "\n";);
        return l_undef;
    }

    init_to_refine();
    if (m_to_refine.empty()) {
        return l_true;
    }
    init_search();
    lbool ret = inner_check(true);
    if (ret == l_undef)
        ret = inner_check(false);

    TRACE("nla_solver", tout << "ret = " << ret << ", lemmas count = " << m_lemma_vec->size() << "\n";);
    IF_VERBOSE(2, if(ret == l_undef) {verbose_stream() << "Monomials\n"; print_monomials(verbose_stream());});
    CTRACE("nla_solver", ret == l_undef, tout << "Monomials\n"; print_monomials(tout););
    return ret;
}

bool core:: no_lemmas_hold() const {
    for (auto & l : * m_lemma_vec) {
        if (lemma_holds(l)) {
            TRACE("nla_solver", print_specific_lemma(l, tout););
            return false;
        }
    }
    return true;
}
    
lbool core::test_check(
    vector<lemma>& l) {
    m_lar_solver.set_status(lp::lp_status::OPTIMAL);
    return check(l);
}

} // end of nla


#if 0
rational core::mon_value_by_vars(unsigned i) const {
    return product_value(m_monomials[i]);
}
#endif
