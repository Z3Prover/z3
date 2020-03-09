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
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
#include "math/lp/nex.h"
#include "math/grobner/pdd_solver.h"
#include "math/dd/pdd_interval.h"
#include "math/dd/pdd_eval.h"
namespace nla {

core::core(lp::lar_solver& s, reslimit & lim) :
    m_evars(),
    m_lar_solver(s),
    m_tangents(this),
    m_basics(this),
    m_order(this),
    m_monotone(this),
    m_intervals(this, lim),
    m_horner(this, &m_intervals),
    m_pdd_manager(s.number_of_vars()),
    m_pdd_grobner(lim, m_pdd_manager),
    m_emons(m_evars),
    m_reslim(lim)
{}
    
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
        r.add_monomial(p.coeff(), j);
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

bool core::canonize_sign_is_correct(const monic& m) const {
    bool r = false;
    for (lpvar j : m.vars()) {
        r ^= canonize_sign(j);
    }
    return r == m.rsign();
}

bool core::canonize_sign(const monic& m) const {
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

void core::add_monic(lpvar v, unsigned sz, lpvar const* vs) {
    m_add_buffer.resize(sz);
    for (unsigned i = 0; i < sz; i++) {
        lpvar j = vs[i];
        if (m_lar_solver.is_term(j))
            j = m_lar_solver.adjust_term_index(j);        
        m_add_buffer[i] = j;
    }
        
    m_emons.add(v, m_add_buffer);
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
    
// return true iff the monic value is equal to the product of the values of the factors
bool core::check_monic(const monic& m) const {    
    SASSERT((!m_lar_solver.column_is_int(m.var())) || m_lar_solver.get_column_value(m.var()).is_int());
    bool ret = product_value(m.vars()) == m_lar_solver.get_column_value_rational(m.var()); 
    CTRACE("nla_solver", !ret, print_monic(m, tout) << '\n';);
    return ret;
}
    
void core::explain(const monic& m, lp::explanation& exp) const {       
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
        if (lp_settings().m_print_external_var_name)
            out << "(" << m_lar_solver.get_variable_name(v) << "=" << val(v) << ")";
        else
            out << "(v" << v << " =" << val(v) << ")";
            
    }
    return out;
}
template <typename T>
std::string core::product_indices_str(const T & m) const {
    std::stringstream out;
    bool first = true;
    for (lpvar v : m) {
        if (!first)
            out << "*";
        else
            first = false;
        out << "v" << v;;
    }
    return out.str();
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
        out << " MON = " << pp_mon_with_vars(*this, m_emons[f.var()]);
    }
    return out;
}

std::ostream& core::print_monic(const monic& m, std::ostream& out) const {
    if (lp_settings().m_print_external_var_name)
        out << "([" << m.var() << "] = " << m_lar_solver.get_variable_name(m.var()) << " = " << val(m.var()) << " = ";
    else 
        out << "(v" << m.var() << " = " << val(m.var()) << " = ";
    print_product(m.vars(), out) << ")\n";
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

std::ostream& core::print_monic_with_vars(lpvar v, std::ostream& out) const {
    return print_monic_with_vars(m_emons[v], out);
}
template <typename T>
std::ostream& core::print_product_with_vars(const T& m, std::ostream& out) const {
    print_product(m, out) << "\n";
    for (unsigned k = 0; k < m.size(); k++) {
        print_var(m[k], out);
    }
    return out;
}

std::ostream& core::print_monic_with_vars(const monic& m, std::ostream& out) const {
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
    unsigned i = 0;
    for (auto &p : exp) {
        out << "(" << p.second << ")";
        m_lar_solver.constraints().display(out, [this](lpvar j) { return var_str(j);}, p.second);
        if (++i < exp.size())
            out << "      ";
    }
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
 if t is an octagon term -+x -+ y try to explain why the term always is
 equal zero
*/
bool core:: explain_by_equiv(const lp::lar_term& t, lp::explanation& e) const {
    lpvar i,j;
    bool sign;
    if (!is_octagon_term(t, sign, i, j))
        return false;
    if (m_evars.find(signed_var(i, false)) != m_evars.find(signed_var(j, sign)))
        return false;
            
    m_evars.explain(signed_var(i, false), signed_var(j, sign), e);
    TRACE("nla_solver", tout << "explained :"; m_lar_solver.print_term_as_indices(t, tout););
    return true;
            
}
    
void core::mk_ineq(lp::lar_term& t, llc cmp, const rational& rs) {
    TRACE("nla_solver_details", m_lar_solver.print_term_as_indices(t, tout << "t = "););
    if (!explain_ineq(t, cmp, rs)) {
        m_lar_solver.subs_term_columns(t);
        current_lemma().push_back(ineq(cmp, t, rs));
        CTRACE("nla_solver", ineq_holds(ineq(cmp, t, rs)), print_ineq(ineq(cmp, t, rs), tout) << "\n";);
        SASSERT(!ineq_holds(ineq(cmp, t, rs)));
    }
}

void core::mk_ineq_no_expl_check(lp::lar_term& t, llc cmp, const rational& rs) {
    TRACE("nla_solver_details", m_lar_solver.print_term_as_indices(t, tout << "t = "););
    m_lar_solver.subs_term_columns(t);
    current_lemma().push_back(ineq(cmp, t, rs));
    CTRACE("nla_solver", ineq_holds(ineq(cmp, t, rs)), print_ineq(ineq(cmp, t, rs), tout) << "\n";);
    SASSERT(!ineq_holds(ineq(cmp, t, rs)));
}

void core::mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs) {
    lp::lar_term t;
    t.add_monomial(a, j);
    t.add_monomial(b, k);
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
    t.add_monomial(a, j);
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
    
// the monics should be equal by modulo sign but this is not so in the model
void core:: fill_explanation_and_lemma_sign(const monic& a, const monic & b, rational const& sign) {
    SASSERT(sign == 1 || sign == -1);
    explain(a, current_expl());
    explain(b, current_expl());
    TRACE("nla_solver",
          tout << "used constraints: ";
          for (auto &p :  current_expl())
              m_lar_solver.constraints().display(tout, p.second); tout << "\n";
                                                 );
    SASSERT(current_ineqs().size() == 0);
    mk_ineq(rational(1), a.var(), -sign, b.var(), llc::EQ, rational::zero());
    TRACE("nla_solver", print_lemma(tout););
}

// Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
// Also sorts the result.
// 
svector<lpvar> core::reduce_monic_to_rooted(const svector<lpvar> & vars, rational & sign) const {
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
monic_coeff core::canonize_monic(monic const& m) const {
    rational sign = rational(1);
    svector<lpvar> vars = reduce_monic_to_rooted(m.vars(), sign);
    return monic_coeff(vars, sign);
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
    
int core::rat_sign(const monic& m) const {
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

// Returns true if the monic sign is incorrect
bool core::sign_contradiction(const monic& m) const {
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

bool core:: var_is_fixed_to_zero(lpvar j) const {
    return 
        m_lar_solver.column_is_fixed(j) &&
        m_lar_solver.get_lower_bound(j) == lp::zero_of_type<lp::impq>();
}
bool core:: var_is_fixed_to_val(lpvar j, const rational& v) const {
    return 
        m_lar_solver.column_is_fixed(j) &&
        m_lar_solver.get_lower_bound(j) == lp::impq(v);
}

bool core:: var_is_fixed(lpvar j) const {
    return m_lar_solver.column_is_fixed(j);
}

bool core:: var_is_free(lpvar j) const {
    return m_lar_solver.column_is_free(j);
}
    
std::ostream & core::print_ineq(const ineq & in, std::ostream & out) const {
    m_lar_solver.print_term_as_indices(in.m_term, out);
    out << " " << lconstraint_kind_string(in.m_cmp) << " " << in.m_rs;
    return out;
}

std::ostream & core::print_var(lpvar j, std::ostream & out) const {
    if (m_emons.is_monic_var(j)) {
        print_monic(m_emons[j], out);
    }
        
    m_lar_solver.print_column_info(j, out);
    signed_var jr = m_evars.find(j);
    out << "root=";
    if (jr.sign()) {
        out << "-";
    }
        
    out << m_lar_solver.get_variable_name(jr.var()) << "\n";
    return out;
}

std::ostream & core::print_monics(std::ostream & out) const {
    for (auto &m : m_emons) {
        print_monic_with_vars(m, out);
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
    
bool core::find_canonical_monic_of_vars(const svector<lpvar>& vars, lpvar & i) const {
    monic const* sv = m_emons.find_canonical(vars);
    return sv && (i = sv->var(), true);
}

bool core::is_canonical_monic(lpvar j) const {
    return m_emons.is_canonical_monic(j);
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

void core::trace_print_monic_and_factorization(const monic& rm, const factorization& f, std::ostream& out) const {
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


lp::lp_settings& core::lp_settings() {
    return m_lar_solver.settings();
}
const lp::lp_settings& core::lp_settings() const {
    return m_lar_solver.settings();
}
    
unsigned core::random() { return lp_settings().random_next(); }
    

// we look for octagon constraints here, with a left part  +-x +- y 
void core::collect_equivs() {
    const lp::lar_solver& s = m_lar_solver;

    for (unsigned i = 0; i < s.terms().size(); i++) {
        unsigned ti = i + s.terms_start_index();
        if (!s.term_is_used_as_row(ti))
            continue;
        lpvar j = s.external_to_local(ti);
        if (var_is_fixed_to_zero(j)) {
            TRACE("nla_solver_eq", tout << "term = "; s.print_term_as_indices(*s.terms()[i], tout););
            add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
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

bool core::vars_table_is_ok() const {
    // return m_var_eqs.is_ok();
    return true;
}

bool core::rm_table_is_ok() const {
    // return m_emons.is_ok();
    return true;
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

void core::print_monic_stats(const monic& m, std::ostream& out) {
    if (m.size() == 2) return;
    monic_coeff mc = canonize_monic(m);
    for(unsigned i = 0; i < mc.vars().size(); i++){
        if (abs(val(mc.vars()[i])) == rational(1)) {
            auto vv = mc.vars();
            vv.erase(vv.begin()+i);
            monic const* sv = m_emons.find_canonical(vv);
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
    TRACE("nla_solver_details", tout << "emons:" << pp_emons(*this, m_emons););
    m_to_refine.clear();
    m_to_refine.resize(m_lar_solver.number_of_vars());
    unsigned r = random(), sz = m_emons.number_of_monics();
    for (unsigned k = 0; k < sz; k++) {
        auto const & m = *(m_emons.begin() + (k + r)% sz);
        if (!check_monic(m)) 
            m_to_refine.insert(m.var());
    }
    
    TRACE("nla_solver", 
          tout << m_to_refine.size() << " mons to refine:\n";
          for (lpvar v : m_to_refine) tout << pp_mon(*this, m_emons[v]) << "\n";);
}
        
std::unordered_set<lpvar> core::collect_vars(const lemma& l) const {
    std::unordered_set<lpvar> vars;
    auto insert_j = [&](lpvar j) { 
        vars.insert(j);
        if (m_emons.is_monic_var(j)) {
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
        const auto& c = m_lar_solver.constraints()[p.second];
        for (const auto& r : c.coeffs()) {
            insert_j(r.second);
        }
    }
    return vars;
}

// divides bc by c, so bc = b*c
bool core::divide(const monic& bc, const factor& c, factor & b) const {
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
        monic const* sv = m_emons.find_canonical(b_rvars);
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
    

void core::trace_print_ol(const monic& ac,
                          const factor& a,
                          const factor& c,
                          const monic& bc,
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
    if (!m_emons.is_monic_var(i)) {
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
    

// Returns rooted monics by arity
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

bool core::rm_check(const monic& rm) const {
    return check_monic(m_emons[rm.var()]);
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
    t.add_monomial(rrat_sign(val(v)), v);

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

    
bool core::find_bfc_to_refine_on_monic(const monic& m, factorization & bf) {
    for (auto f : factorization_factory_imp(m, *this)) {
        if (f.size() == 2) {
            auto a = f[0];
            auto b = f[1];
            if (val(m) != val(a) * val(b)) {
                bf = f;
                TRACE("nla_solver", tout << "found bf";
                      tout << ":m:" << pp_mon_with_vars(*this, m) << "\n";
                      tout << "bf:"; print_bfc(bf, tout););
                      
                return true;
            }
        }
    }
    return false;
}

// finds a monic to refine with its binary factorization
bool core::find_bfc_to_refine(const monic* & m, factorization & bf){
    m = nullptr;
    unsigned r = random(), sz = m_to_refine.size();
    for (unsigned k = 0; k < sz; k++) {
        lpvar i = m_to_refine[(k + r) % sz];
        m = &m_emons[i];
        SASSERT (!check_monic(*m));
        if (m->size() == 2) {
            bf.set_mon(m);
            bf.push_back(factor(m->vars()[0], factor_type::VAR));
            bf.push_back(factor(m->vars()[1], factor_type::VAR));
            return true;
        }
                
        if (find_bfc_to_refine_on_monic(*m, bf)) {
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
    
void core::negate_relation(unsigned j, const rational& a) {
    SASSERT(val(j) != a);
    if (val(j) < a) {
        mk_ineq(j, llc::GE, a);
    }
    else {
        mk_ineq(j, llc::LE, a);
    }
}

bool core::conflict_found() const {
    for (const auto & l : * m_lemma_vec) {
        if (l.is_conflict())
            return true;
    }
    return false;
}

bool core::done() const {
    return m_lemma_vec->size() >= 10 || conflict_found();
}

lbool core::incremental_linearization(bool constraint_derived) {
    TRACE("nla_solver_details", print_terms(tout); tout << m_lar_solver.constraints(););
    for (int search_level = 0; search_level < 3 && !done(); search_level++) {
        TRACE("nla_solver", tout << "constraint_derived = " << constraint_derived << ", search_level = " << search_level << "\n";);
        if (search_level == 0) {
            m_basics.basic_lemma(constraint_derived);
            if (!m_lemma_vec->empty())
                return l_false;
        }
        if (constraint_derived) continue;
        TRACE("nla_solver", tout << "passed constraint_derived and basic lemmas\n";);
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
// constraint_derived is set to true when we do not use the model values to
// obtain the lemmas
lbool core::inner_check(bool constraint_derived) {
    if (constraint_derived) {
        if (need_to_call_algebraic_methods())
            if (!m_horner.horner_lemmas()) {
                clear_and_resize_active_var_set();
                if (m_nla_settings.run_grobner()) {
                    find_nl_cluster();
                    run_grobner();
                }
            }
        if (done()) {
            return l_false;
        }
    }
    return incremental_linearization(constraint_derived);
}

bool core::elist_is_consistent(const std::unordered_set<lpvar> & list) const {
    bool first = true;
    bool p;
    for (lpvar j : list) {
        if (first) {
            p = check_monic(m_emons[j]);
            first = false;
        } else 
            if (check_monic(m_emons[j]) != p)
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
    lp_settings().stats().m_nla_calls++;
    TRACE("nla_solver", tout << "calls = " << lp_settings().stats().m_nla_calls << "\n";);
    m_lar_solver.get_rid_of_inf_eps();
    m_lemma_vec =  &l_vec;
    if (!(m_lar_solver.get_status() == lp::lp_status::OPTIMAL || m_lar_solver.get_status() == lp::lp_status::FEASIBLE )) {
        TRACE("nla_solver", tout << "unknown because of the m_lar_solver.m_status = " << m_lar_solver.get_status() << "\n";);
        return l_undef;
    }

    init_to_refine();
    if (m_to_refine.is_empty()) {
        return l_true;
    }
    init_search();
    lbool ret = inner_check(true);
    if (ret == l_undef)
        ret = inner_check(false);

    TRACE("nla_solver", tout << "ret = " << ret << ", lemmas count = " << m_lemma_vec->size() << "\n";);
    IF_VERBOSE(2, if(ret == l_undef) {verbose_stream() << "Monomials\n"; print_monics(verbose_stream());});
    CTRACE("nla_solver", ret == l_undef, tout << "Monomials\n"; print_monics(tout););
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

std::ostream& core::print_terms(std::ostream& out) const {
    for (unsigned i=0; i< m_lar_solver.m_terms.size(); i++) {
        unsigned ext = i + m_lar_solver.terms_start_index();
        if (!m_lar_solver.var_is_registered(ext)) {
            out << "term is not registered\n";
            continue;
        }
        
        const lp::lar_term & t = *m_lar_solver.m_terms[i];
        out << "term:"; print_term(t, out) << std::endl;        
        lpvar j = m_lar_solver.external_to_local(ext);
        print_var(j, out);
    }
    return out;
}

std::string core::var_str(lpvar j) const {
    return is_monic_var(j)?
        (product_indices_str(m_emons[j].vars()) + (check_monic(m_emons[j])? "": "_")) : (std::string("v") + lp::T_to_string(j));        
}

std::ostream& core::print_term( const lp::lar_term& t, std::ostream& out) const {
    return lp::print_linear_combination_customized(
        t.coeffs_as_vector(),
        [this](lpvar j) { return var_str(j); },
        out);
}


void core::run_grobner() {
    unsigned& quota = m_grobner_quota;
    if (quota == 1) {
        return;
    }
    lp_settings().stats().m_grobner_calls++;
    configure_grobner();
    m_pdd_grobner.saturate();
    bool conflict = false;
    unsigned n = m_pdd_grobner.number_of_conflicts_to_report();
    SASSERT(n > 0);
    for (auto eq : m_pdd_grobner.equations()) {
        if (check_pdd_eq(eq)) {
            conflict = true;
            if (--n == 0)
                break;
        }
    }
    if (conflict) {
        IF_VERBOSE(2, verbose_stream() << "grobner conflict\n");
    }
    else {
        if (quota > 1)
            quota--;
        IF_VERBOSE(2, verbose_stream() << "grobner miss, quota " << quota <<  "\n");
        IF_VERBOSE(4, diagnose_pdd_miss(verbose_stream()));
    }
}

void core::configure_grobner() {
    m_pdd_grobner.reset();
    try {
        set_level2var_for_grobner();
        for (unsigned i : m_rows) {
            add_row_to_grobner(m_lar_solver.A_r().m_rows[i]);
        }
    }
    catch (...) {
        IF_VERBOSE(2, verbose_stream() << "pdd throw\n");
        return;
    }
#if 0
    IF_VERBOSE(2, m_pdd_grobner.display(verbose_stream()));
    dd::pdd_eval eval(m_pdd_manager);
    eval.var2val() = [&](unsigned j){ return val(j); };
    for (auto* e : m_pdd_grobner.equations()) {
        dd::pdd p = e->poly();
        rational v = eval(p);
        if (p.is_linear() && !eval(p).is_zero()) {
            IF_VERBOSE(0, verbose_stream() << "violated linear constraint " << p << "\n");
        }
    }
#endif
   
    struct dd::solver::config cfg;
    cfg.m_max_steps = m_pdd_grobner.equations().size();
    cfg.m_max_simplified = m_nla_settings.grobner_max_simplified();
    cfg.m_eqs_growth = m_nla_settings.grobner_eqs_growth();
    cfg.m_expr_size_growth = m_nla_settings.grobner_expr_size_growth();
    cfg.m_expr_degree_growth = m_nla_settings.grobner_expr_degree_growth();
    cfg.m_number_of_conflicts_to_report = m_nla_settings.grobner_number_of_conflicts_to_report();
    m_pdd_grobner.set(cfg);
    m_pdd_grobner.adjust_cfg();
    m_pdd_manager.set_max_num_nodes(10000); // or something proportional to the number of initial nodes.
}

std::ostream& core::diagnose_pdd_miss(std::ostream& out) {

    // m_pdd_grobner.display(out);

    dd::pdd_eval eval;
    eval.var2val() = [&](unsigned j){ return val(j); };
    for (auto* e : m_pdd_grobner.equations()) {
        dd::pdd p = e->poly();
        rational v = eval(p);
        if (!v.is_zero()) {
            out << p << " := " << v << "\n";
        }
    }  
  
    for (unsigned j = 0; j < m_lar_solver.column_count(); ++j) {
        if (m_lar_solver.column_has_lower_bound(j) || m_lar_solver.column_has_upper_bound(j)) {
            out << j << ": [";
                if (m_lar_solver.column_has_lower_bound(j)) out << m_lar_solver.get_lower_bound(j);
                out << "..";
                if (m_lar_solver.column_has_upper_bound(j)) out << m_lar_solver.get_upper_bound(j);
                out << "]\n";
        }
    }              
    return out;
}

bool core::check_pdd_eq(const dd::solver::equation* e) {
    dd::pdd_interval eval(m_reslim);
    eval.var2interval() =
        [this](lpvar j, bool deps) {
            intervals::interval a;
            if (deps) m_intervals.set_var_interval<dd::w_dep::with_deps>(j, a);
            else m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
            return a;
        };
    auto i = eval.get_interval<dd::w_dep::without_deps>(e->poly());    
    dep_intervals di(m_reslim);
    if (!di.separated_from_zero(i))
        return false;
    auto i_wd = eval.get_interval<dd::w_dep::with_deps>(e->poly());  
    std::function<void (const lp::explanation&)> f = [this](const lp::explanation& e) {
                                                         add_empty_lemma();
                                                         current_expl().add(e);
                                                     };
    if (di.check_interval_for_conflict_on_zero(i_wd, e->dep(), f)) {
        lp_settings().stats().m_grobner_conflicts++;
        return true;
    }
    else {
        return false;
    }
}

void core::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, svector<lpvar> & q) {
    if (active_var_set_contains(j) || var_is_fixed(j)) return;
    TRACE("grobner", tout << "j = " << j << ", "; print_var(j, tout) << "\n";);
    const auto& matrix = m_lar_solver.A_r();
    insert_to_active_var_set(j);
    for (auto & s : matrix.m_columns[j]) {
        unsigned row = s.var();
        if (m_rows.contains(row)) continue;       
        if (matrix.m_rows[row].size() > m_nla_settings.grobner_row_length_limit()) {
            TRACE("grobner", tout << "ignore the row " << row << " with the size " << matrix.m_rows[row].size() << "\n";); 
            continue;
        }
        m_rows.insert(row);
        for (auto& rc : matrix.m_rows[row]) {
            add_var_and_its_factors_to_q_and_collect_new_rows(rc.var(), q);
        }
    }

    if (!is_monic_var(j))
        return;

    const monic& m = emons()[j];
    for (auto fcn : factorization_factory_imp(m, *this)) {
        for (const factor& fc: fcn) {
            q.push_back(var(fc));
        }
    }            
}

const rational& core::val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep) {
    unsigned lc, uc;
    m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
    dep = m_intervals.mk_join(dep, m_intervals.mk_leaf(lc));
    dep = m_intervals.mk_join(dep, m_intervals.mk_leaf(uc));
    return m_lar_solver.column_lower_bound(j).x;
}

dd::pdd core::pdd_expr(const rational& c, lpvar j, u_dependency*& dep) {
    if (m_nla_settings.grobner_subs_fixed() == 1 && var_is_fixed(j)) {
        return m_pdd_manager.mk_val(c * val_of_fixed_var_with_deps(j, dep));
    }

    if (m_nla_settings.grobner_subs_fixed() == 2 && var_is_fixed_to_zero(j)) {
        return m_pdd_manager.mk_val(val_of_fixed_var_with_deps(j, dep));
    }

    if (!is_monic_var(j))
        return c * m_pdd_manager.mk_var(j);

    u_dependency* zero_dep = dep;
    // j is a monic var
    dd::pdd r = m_pdd_manager.mk_val(c);
    const monic& m = emons()[j];
    for (lpvar k : m.vars()) {
        if (m_nla_settings.grobner_subs_fixed() && var_is_fixed(k)) {
            r *= m_pdd_manager.mk_val(val_of_fixed_var_with_deps(k, dep));
        } else if (m_nla_settings.grobner_subs_fixed() == 2 && var_is_fixed_to_zero(k)) {
            r = m_pdd_manager.mk_val(val_of_fixed_var_with_deps(k, zero_dep));
            dep = zero_dep;
            return r;
        } else {
            r *= m_pdd_manager.mk_var(k);
        }
    }
    return r;
}

void core::add_row_to_grobner(const vector<lp::row_cell<rational>> & row) {
    u_dependency *dep = nullptr;
    dd::pdd sum = m_pdd_manager.mk_val(rational(0));
    for (const auto &p : row) {
        sum  += pdd_expr(p.coeff(), p.var(), dep);
    }
    m_pdd_grobner.add(sum, dep);    
}


void core::find_nl_cluster() {
    prepare_rows_and_active_vars();
    svector<lpvar> q;
    for (lpvar j : m_to_refine) {        
        TRACE("grobner", print_monic(emons()[j], tout) << "\n";);
        q.push_back(j);
    }
    
    while (!q.empty()) {
        lpvar j = q.back();        
        q.pop_back();
        add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
    }
    TRACE("grobner", display_matrix_of_m_rows(tout););
}

void core::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(m_lar_solver.row_count());
    clear_and_resize_active_var_set();
}


std::unordered_set<lpvar> core::get_vars_of_expr_with_opening_terms(const nex *e ) {
    auto ret = get_vars_of_expr(e);
    auto & ls = m_lar_solver;
    svector<lpvar> added;
    for (auto j : ret) {
        added.push_back(j);
    }
    for (unsigned i = 0; i < added.size(); ++i) {
        lpvar j = added[i];
        if (ls.column_corresponds_to_term(j)) {
            const auto& t = m_lar_solver.get_term(ls.local_to_external(j));
            for (auto p : t) {
                if (ret.find(p.var()) == ret.end()) {
                    added.push_back(p.var());
                    ret.insert(p.var());
                }
            }
        }
    }
    return ret;
}

void core::display_matrix_of_m_rows(std::ostream & out) const {
    const auto& matrix = m_lar_solver.A_r();
    out << m_rows.size() << " rows" <<"\n";
    out << "the matrix\n";          
    for (const auto & r : matrix.m_rows) {
        print_row(r, out) << std::endl;
    }
}

void core::set_active_vars_weights(nex_creator& nc) {
    nc.set_number_of_vars(m_lar_solver.column_count());
    for (lpvar j : active_var_set()) {
        nc.set_var_weight(j, get_var_weight(j));
    }
}

void core::set_level2var_for_grobner() {
    unsigned n = m_lar_solver.column_count();
    unsigned_vector sorted_vars(n), weighted_vars(n);
    for (unsigned j = 0; j < n; j++) {
        sorted_vars[j] = j;
        weighted_vars[j] = get_var_weight(j);
    }
#if 1
    // potential update to weights
    for (unsigned j = 0; j < n; j++) {
        if (is_monic_var(j) && m_to_refine.contains(j)) {
            for (lpvar k : m_emons[j].vars()) {
                weighted_vars[k] += 6;
            }
        }
    }
#endif

    std::sort(sorted_vars.begin(), sorted_vars.end(), [&](unsigned a, unsigned b) {
                                                      unsigned wa = weighted_vars[a];
                                                      unsigned wb = weighted_vars[b];
                                                      return wa < wb || (wa == wb && a < b); });

    unsigned_vector l2v(n);
    for (unsigned j = 0; j < n; j++)
        l2v[j] = sorted_vars[j];

    m_pdd_manager.reset(l2v);
}

unsigned core::get_var_weight(lpvar j) const {
    unsigned k;
    switch (m_lar_solver.get_column_type(j)) {
        
    case lp::column_type::fixed:
        k = 0;
        break;
    case lp::column_type::boxed:
        k = 2;
        break;
    case lp::column_type::lower_bound:
    case lp::column_type::upper_bound:
        k = 4;
    case lp::column_type::free_column:
        k = 6;
        break;
    default:
        UNREACHABLE();
        break;
    }
    if (is_monic_var(j)) {
        k++;
        if (m_to_refine.contains(j)) {
            k++;
        }
    }
    return k;
}


bool core::is_nl_var(lpvar j) const {
    if (is_monic_var(j))
        return true;
    return m_emons.is_used_in_monic(j);
}



bool core::influences_nl_var(lpvar j) const {
    if (m_lar_solver.is_term(j))
        j = m_lar_solver.adjust_term_index(j);
    if (is_nl_var(j))
        return true;
    for (const auto & c : m_lar_solver.A_r().m_columns[j]) {
        lpvar basic_in_row = m_lar_solver.r_basis()[c.var()];
        if (is_nl_var(basic_in_row))
            return true;        
    }
    return false;
}

} // end of nla
