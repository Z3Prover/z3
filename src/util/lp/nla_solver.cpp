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
#include "util/lp/nla_solver.h"
#include <map>
#include "util/lp/monomial.h"
#include "util/lp/lp_utils.h"
#include "util/lp/vars_equivalence.h"
#include "util/lp/factorization.h"
#include "util/lp/rooted_mons.h"
namespace nla {

template <typename A, typename B>
bool try_insert(const A& elem, B& collection) {
    auto it = collection.find(elem);
    if (it != collection.end())
        return false;
    collection.insert(elem);
    return true;
}

typedef lp::lconstraint_kind llc;
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

point operator+(const point& a, const point& b) {
    return point(a.x + b.x, a.y + b.y);
} 

point operator-(const point& a, const point& b) {
    return point(a.x - b.x, a.y - b.y);
} 

void divide_by_common_factor(unsigned_vector& a, unsigned_vector& b) {
    SASSERT(lp::is_non_decreasing(a) && lp::is_non_decreasing(b));
    unsigned i = 0, j = 0;
    while (i < a.size() && j < b.size()){
        if (a[i] == b[j]) {
            a.erase(a.begin() + i);
            b.erase(b.begin() + j);
        } else if (a[i] < b[j]) {
            i++;
        } else {
            j++;
        }
    }
}

struct solver::imp {
    struct bfc {
        lpvar m_x, m_y;
        bfc() {}
        bfc(lpvar a, lpvar b) {
            if (a < b) {
                m_x = a; m_y = b;
            } else {
                m_x = b; m_y = a;
            }
        }
    };

    //fields    
    vars_equivalence                                                 m_vars_equivalence;
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
    
    unsigned find_monomial(const unsigned_vector& k) const {
        TRACE("nla_solver_find", tout << "k = "; print_product_with_vars(k, tout););
        auto it = m_mkeys.find(k);
        if (it == m_mkeys.end()) {
            TRACE("nla_solver", tout << "not found";);
            return -1;
        }
        TRACE("nla_solver", tout << "found " << it->second << ", mon = "; print_monomial_with_vars(m_monomials[it->second], tout););
        return it->second;
    }
    
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        :
        m_vars_equivalence([this](unsigned h){return vvr(h);}),
        m_lar_solver(s)
        // m_limit(lim),
        // m_params(p)
    {
    }
    
    bool compare_holds(const rational& ls, llc cmp, const rational& rs) const {
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

    rational value(const lp::lar_term& r) const {
        rational ret(0);
        for (const auto & t : r.coeffs()) {
            ret += t.second * vvr(t.first);
        }
        return ret;
    }

    lp::lar_term subs_terms_to_columns(const lp::lar_term& t) const {
        lp::lar_term r;
        for (const auto& p : t) {
            lpvar j = p.var();
            if (m_lar_solver.is_term(j))
                j = m_lar_solver.map_term_index_to_column_index(j);
            r.add_coeff_var(p.coeff(), j);
        }
        return r;
    } 
    
    bool ineq_holds(const ineq& n) const {
        lp::lar_term t = subs_terms_to_columns(n.term());
        return compare_holds(value(t), n.cmp(), n.rs());
    }

    bool an_ineq_holds(const lemma& l) const {
        for(const ineq &i : l.ineqs()) {
            if (!ineq_holds(i))
                return false;
        }
        return false;
    }
    
    rational vvr(lpvar j) const { return m_lar_solver.get_column_value_rational(j); }

    rational vvr(const monomial& m) const { return m_lar_solver.get_column_value_rational(m.var()); }

    lp::impq vv(lpvar j) const { return m_lar_solver.get_column_value(j); }
    
    lpvar var(const rooted_mon& rm) const {return m_monomials[rm.orig_index()].var(); }

    rational vvr(const rooted_mon& rm) const { return vvr(m_monomials[rm.orig_index()].var()) * rm.orig_sign(); }

    rational vvr(const factor& f) const { return vvr(var(f)); }

    lpvar var(const factor& f) const {
        return f.is_var()?
            f.index() : var(m_rm_table.vec()[f.index()]);
    }

    svector<lpvar> sorted_vars(const factor& f) const {
        if (f.is_var()) {
            svector<lpvar> r; r.push_back(f.index());
            return r;
        }
        TRACE("nla_solver", tout << "nv";);
        return m_rm_table.vec()[f.index()].vars();
    }

    // the value of the factor is equal to the value of the variable multiplied
    // by the flip_sign
    rational flip_sign(const factor& f) const {
        return f.is_var()?
            flip_sign_of_var(f.index()) : m_rm_table.vec()[f.index()].orig_sign();
    }

    rational flip_sign_of_var(lpvar j) const {
        rational sign(1);
        m_vars_equivalence.map_to_root(j, sign);
        return sign;
    }
    
    // the value of the rooted monomias is equal to the value of the variable multiplied
    // by the flip_sign
    rational flip_sign(const rooted_mon& m) const {
        return m.orig().sign();
    }
    
    // returns the monomial index
    unsigned add(lpvar v, unsigned sz, lpvar const* vs) {
        m_monomials.push_back(monomial(v, sz, vs));
        TRACE("nla_solver", print_monomial(m_monomials.back(), tout););
        const auto & m = m_monomials.back();
        SASSERT(m_mkeys.find(m.vars()) == m_mkeys.end());
        return m_mkeys[m.vars()] = m_monomials.size() - 1;
    }
    
    void push() {
        TRACE("nla_solver",);
        m_monomials_counts.push_back(m_monomials.size());
    }

    void deregister_monomial_from_rooted_monomials (const monomial & m, unsigned i){
        rational sign = rational(1);
        svector<lpvar> vars = reduce_monomial_to_rooted(m.vars(), sign);
        NOT_IMPLEMENTED_YET();
    }

    void deregister_monomial_from_tables(const monomial & m, unsigned i){
        TRACE("nla_solver", tout << "m = "; print_monomial(m, tout););
        m_mkeys.erase(m.vars());
        deregister_monomial_from_rooted_monomials(m, i);     
    }
     
    void pop(unsigned n) {
        TRACE("nla_solver", tout << "n = " << n <<
              " , m_monomials_counts.size() = " << m_monomials_counts.size() << ", m_monomials.size() = " << m_monomials.size() << "\n"; );
        if (n == 0) return;
        unsigned new_size = m_monomials_counts[m_monomials_counts.size() - n];
        TRACE("nla_solver", tout << "new_size = " << new_size << "\n"; );
        
        for (unsigned i = m_monomials.size(); i-- > new_size; ){
            deregister_monomial_from_tables(m_monomials[i], i);
        }
        m_monomials.shrink(new_size);
        m_monomials_counts.shrink(m_monomials_counts.size() - n);       
    }

    rational mon_value_by_vars(unsigned i) const {
        return product_value(m_monomials[i]);
    }
    template <typename T>
    rational product_value(const T & m) const {
        rational r(1);
        for (auto j : m) {
            r *= m_lar_solver.get_column_value_rational(j);
        }
        return r;
    }
    
    // return true iff the monomial value is equal to the product of the values of the factors
    bool check_monomial(const monomial& m) const {
        SASSERT(m_lar_solver.get_column_value(m.var()).is_int());        
        return product_value(m) == m_lar_solver.get_column_value_rational(m.var());
    }
    
    void explain(const monomial& m, lp::explanation& exp) const {
        m_vars_equivalence.explain(m, exp);
    }

    void explain(const rooted_mon& rm, lp::explanation& exp) const {
        auto & m = m_monomials[rm.orig_index()];
        explain(m, exp);
    }

    void explain(const factor& f, lp::explanation& exp) const {
        if (f.type() == factor_type::VAR) {
            m_vars_equivalence.explain(f.index(), exp);
        } else {
            m_vars_equivalence.explain(m_monomials[m_rm_table.vec()[f.index()].orig_index()], exp);
        }
    }

    void explain(lpvar j, lp::explanation& exp) const {
        m_vars_equivalence.explain(j, exp);
    }

    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const {
        for (unsigned k = 0; k < m.size(); k++) {
            out << "(" << m_lar_solver.get_variable_name(m[k]) << "=" << vvr(m[k]) << ")";
            if (k + 1 < m.size()) out << "*";
        }
        return out;
    }

    std::ostream & print_factor(const factor& f, std::ostream& out) const {
        if (f.is_var()) {
            out << "VAR,  ";
            print_var(f.index(), out);
        } else {
            out << "PROD, ";
            print_product(m_rm_table.vec()[f.index()].vars(), out);
        }
        out << "\n";
        return out;
    }

    std::ostream & print_factor_with_vars(const factor& f, std::ostream& out) const {
        if (f.is_var()) {
            print_var(f.index(), out);
        } else {
            out << " RM = "; print_rooted_monomial_with_vars(m_rm_table.vec()[f.index()], out);
            out << "\n orig mon = "; print_monomial_with_vars(m_monomials[m_rm_table.vec()[f.index()].orig_index()], out);
        }
        return out;
    }

    std::ostream& print_monomial(const monomial& m, std::ostream& out) const {
        out << "( [" << m.var() << "] = " << m_lar_solver.get_variable_name(m.var()) << " = " << vvr(m.var()) << " = ";
        print_product(m.vars(), out);
        out << ")\n";
        return out;
    }

    std::ostream& print_point(const point &a, std::ostream& out) const {
        out << "(" << a.x <<  ", " << a.y << ")";
        return out;
    }
    
    std::ostream& print_tangent_domain(const point &a, const point &b, std::ostream& out) const {
        out << "("; print_point(a, out);  out <<  ", "; print_point(b, out); out <<  ")";
        return out;
    }

    std::ostream& print_bfc(const bfc& m, std::ostream& out) const {
        out << "( x = "; print_var(m.m_x, out); out <<  ", y = "; print_var(m.m_y, out); out <<  ")";
        return out;
    }

    std::ostream& print_monomial(unsigned i, std::ostream& out) const {
        return print_monomial(m_monomials[i], out);
    }

    std::ostream& print_monomial_with_vars(unsigned i, std::ostream& out) const {
        return print_monomial_with_vars(m_monomials[i], out);
    }

    template <typename T>
    std::ostream& print_product_with_vars(const T& m, std::ostream& out) const {
        print_product(m, out);
        out << '\n';
        for (unsigned k = 0; k < m.size(); k++) {
            print_var(m[k], out);
        }
        return out;
    }

    std::ostream& print_monomial_with_vars(const monomial& m, std::ostream& out) const {
        out << "["; print_var(m.var(), out) << "]\n";
        print_product_with_vars(m.vars(), out);
        out << ")\n";
        return out;
    }

    std::ostream& print_rooted_monomial(const rooted_mon& rm, std::ostream& out) const {
        out << "vars = "; 
        print_product(rm.vars(), out);
        out << "\n orig = "; print_monomial(m_monomials[rm.orig_index()], out);
        out << ", orig sign = " << rm.orig_sign() << "\n";
        return out;
    }

    std::ostream& print_rooted_monomial_with_vars(const rooted_mon& rm, std::ostream& out) const {
        out << "vars = "; 
        print_product(rm.vars(), out);
        out << "\n orig = "; print_monomial_with_vars(m_monomials[rm.orig_index()], out);
        out << ", orig sign = " << rm.orig_sign() << "\n";
        out << ", vvr(rm) = " << vvr(rm) << "\n";
        
        return out;
    }

    std::ostream& print_explanation(lp::explanation& exp, std::ostream& out) const {
        out << "expl: ";
        for (auto &p : exp) {
            m_lar_solver.print_constraint(p.second, out);
            out << "      ";
        }
        out << "\n";
        return out;
    }

    bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
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
    bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
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

    bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
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

    bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
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
    bool explain_ineq(const lp::lar_term& t, llc cmp, const rational& rs) {
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
            r = explain_lower_bound(t, rs, exp) && explain_upper_bound(t, rs, exp);
            break;
        case llc::NE:
            r = explain_lower_bound(t, rs + rational(1), exp) || explain_upper_bound(t, rs - rational(1), exp);
            CTRACE("nla_solver", r, tout << "ineq:"; print_ineq(ineq(cmp, t, rs), tout); print_explanation(exp, tout << ", "););
            break;
        default:
            SASSERT(false);
            r = false;
        }
        if (r) {
            current_expl().add(exp);
            return true;
        }
        return false;
    }
    
    void mk_ineq(lp::lar_term& t, llc cmp, const rational& rs) {
       TRACE("nla_solver_details", m_lar_solver.print_term(t, tout << "t = "););
        if (explain_ineq(t, cmp, rs)) {
            return;
        }
        m_lar_solver.subs_term_columns(t);
        current_lemma().push_back(ineq(cmp, t, rs));
    }
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(a, j);
        t.add_coeff_var(b, k);
        mk_ineq(t, cmp, rs);
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs) {
        mk_ineq(rational(1), j, b, k, cmp, rs);
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp) {
        mk_ineq(j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp) {
        mk_ineq(a, j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs) {
        mk_ineq(a, j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs) {
        mk_ineq(j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, llc cmp, const rational& rs) {
        mk_ineq(rational(1), j, cmp, rs);
    }

    void mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs) {
        lp::lar_term t;        
        t.add_coeff_var(a, j);
        mk_ineq(t, cmp, rs);
    }

    llc negate(llc cmp) {
        switch(cmp) {
        case llc::LE: return llc::GT;
        case llc::LT: return llc::GE;
        case llc::GE: return llc::LT;
        case llc::GT: return llc::LE;
        case llc::EQ: return llc::NE;
        case llc::NE: return llc::EQ;
        default: SASSERT(false);
        };
        return cmp; // not reachable
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
    
    void mk_ineq(const rational& a, lpvar j, llc cmp) {
        mk_ineq(a, j, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, lpvar k, llc cmp, lemma& l) {
        mk_ineq(rational(1), j, rational(1), k, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, llc cmp) {
        mk_ineq(j, cmp, rational::zero());
    }
    
    // the monomials should be equal by modulo sign but this is not so in the model
    void fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign) {
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
    svector<lpvar> reduce_monomial_to_rooted(const svector<lpvar> & vars, rational & sign) const {
        svector<lpvar> ret;
        sign = 1;
        for (lpvar v : vars) {
            unsigned root = m_vars_equivalence.map_to_root(v, sign);
            SASSERT(m_vars_equivalence.is_root(root));
            TRACE("nla_solver_eq",
                  print_var(v,tout);
                  tout << " mapped to ";

                  print_var(root, tout););
            ret.push_back(root);
        }
        std::sort(ret.begin(), ret.end());
        return ret;
    }


    // Replaces definition m_v = v1* .. * vn by
    // m_v = coeff * w1 * ... * wn, where w1, .., wn are canonical
    // representatives, which are the roots of the equivalence tree, under current equations.
    // 
    monomial_coeff canonize_monomial(monomial const& m) const {
        rational sign = rational(1);
        svector<lpvar> vars = reduce_monomial_to_rooted(m.vars(), sign);
        return monomial_coeff(vars, sign);
    }

    // the value of the i-th monomial has to be equal to the value of the k-th monomial modulo sign
    // but it is not the case in the model
    void generate_sign_lemma(const monomial& m, const monomial& n, const rational& sign) {
        add_empty_lemma();
        TRACE("nla_solver",
              tout << "m = "; print_monomial_with_vars(m, tout);
              tout << "n = "; print_monomial_with_vars(n, tout);
              );
        mk_ineq(m.var(), -sign, n.var(), llc::EQ);
        explain(m, current_expl());
        explain(n, current_expl());        
        TRACE("nla_solver", print_lemma(tout););
    }
    lemma& current_lemma() { return m_lemma_vec->back(); }
    vector<ineq>& current_ineqs() { return current_lemma().ineqs(); }
    lp::explanation& current_expl() { return current_lemma().expl(); }

    static int rat_sign(const rational& r) {
        return r.is_pos()? 1 : ( r.is_neg()? -1 : 0);
    }

    int vars_sign(const svector<lpvar>& v) {
        int sign = 1;
        for (lpvar j : v) {
            sign *= rat_sign(vvr(j));
            if (sign == 0) 
                return 0;
        }
        return sign;
    }

    void negate_strict_sign(lpvar j) {
        TRACE("nla_solver", print_var(j, tout););
        if (!vvr(j).is_zero()) {
            int sign = rat_sign(vvr(j));
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
    
    void generate_strict_case_zero_lemma(const monomial& m, unsigned zero_j, int sign_of_zj) {
        TRACE("nla_solver", tout << "sign_of_zj = " << sign_of_zj << "\n";);
        // we know all the signs
        add_empty_lemma();
        mk_ineq(zero_j, (sign_of_zj == 1? llc::GT : llc::LT));
        for (unsigned j : m){
            if (j != zero_j) {
                negate_strict_sign(j);
            }
        }
        negate_strict_sign(m.var());
    }

    bool has_upper_bound(lpvar j) const {
        return m_lar_solver.column_has_upper_bound(j);
    } 

    bool has_lower_bound(lpvar j) const {
        return m_lar_solver.column_has_lower_bound(j);
    } 
    const rational& get_upper_bound(unsigned j) const {
        return m_lar_solver.get_upper_bound(j).x;
    }

    const rational& get_lower_bound(unsigned j) const {
        return m_lar_solver.get_lower_bound(j).x;
    }
    
    
    bool zero_is_an_inner_point_of_bounds(lpvar j) const {
        if (has_upper_bound(j) && get_upper_bound(j) <= rational(0))            
            return false;
        if (has_lower_bound(j) && get_lower_bound(j) >= rational(0))            
            return false;
        return true;
    }
    
    // try to find a variable j such that vvr(j) = 0
    // and the bounds on j contain 0 as an inner point
    lpvar find_best_zero(const monomial& m, unsigned_vector & fixed_zeros) const {
        lpvar zero_j = -1;
        for (unsigned j : m){
            if (vvr(j).is_zero()){
                if (var_is_fixed_to_zero(j))
                    fixed_zeros.push_back(j);
                
                if (!is_set(zero_j) || zero_is_an_inner_point_of_bounds(j))
                    zero_j = j;
            }
        }
        return zero_j;    
    }

    static bool is_set(unsigned j) {
        return static_cast<int>(j) != -1; 
    } 

    bool try_get_non_strict_sign_from_bounds(lpvar j, int& sign) const {
        SASSERT(sign);
        if (has_lower_bound(j) && get_lower_bound(j) >= rational(0))
            return true;
        if (has_upper_bound(j) && get_upper_bound(j) <= rational(0)) {
            sign = -sign;
            return true;
        }
        sign = 0;
        return false;
    }

    void get_non_strict_sign(lpvar j, int& sign) const {
            const rational & v = vvr(j);
            if (v.is_zero()) {
                try_get_non_strict_sign_from_bounds(j, sign);
            } else {
                sign *= rat_sign(v);
            }
    }

    static bool is_even(unsigned k) {
        return (k >> 1) << 1 == k;
    }
    
    void generate_zero_lemmas(const monomial& m) {
        SASSERT(!vvr(m).is_zero() && product_value(m).is_zero());
        int sign = rat_sign(vvr(m));
        unsigned_vector fixed_zeros;
        lpvar zero_j = find_best_zero(m, fixed_zeros);
        SASSERT(is_set(zero_j));
        unsigned zero_power = 0;
        for (unsigned j : m){
            if (j == zero_j) {
                zero_power++;
                continue;
            }
            get_non_strict_sign(j, sign);
            if(sign == 0)
                break;
        }
        if (sign && is_even(zero_power))
            sign = 0;
        TRACE("nla_solver", tout << "zero_j = " << zero_j << ", sign = " << sign << "\n";);
        if (sign == 0) {
            add_empty_lemma();
            mk_ineq(zero_j, llc::NE);
            mk_ineq(m.var(), llc::EQ);
        } else {
            generate_strict_case_zero_lemma(m, zero_j, sign);
        }
        TRACE("nla_solver", print_lemma(tout););
        for (lpvar j : fixed_zeros)
            add_fixed_zero_lemma(m, j);
    }

    void add_fixed_zero_lemma(const monomial& m, lpvar j) {
        add_empty_lemma();
        explain_fixed_var(j);
        mk_ineq(m.var(), llc::EQ);
        TRACE("nla_solver", print_lemma(tout););
    }
    
    int rat_sign(const monomial& m) const {
        int sign = 1;
        for (lpvar j : m) {
            auto v = vvr(j);
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
    bool sign_contradiction(const monomial& m) const {
        return  rat_sign(vvr(m)) != rat_sign(m);
    }

    unsigned_vector eq_vars(lpvar j) const {
        TRACE("nla_solver_eq", tout << "j = "; print_var(j, tout); tout << "eqs = ";
              for(auto jj : m_vars_equivalence.eq_vars(j)) {
                  print_var(jj, tout);
              });
        return m_vars_equivalence.eq_vars(j);
    }

    // Monomials m and n vars have the same values, up to "sign"
    // Generate a lemma if values of m.var() and n.var() are not the same up to sign
    bool basic_sign_lemma_on_two_monomials(const monomial& m, const monomial& n, const rational& sign) {
        if (vvr(m) == vvr(n) *sign)
            return false;
        TRACE("nla_solver", tout << "sign contradiction:\nm = "; print_monomial_with_vars(m, tout); tout << "n= "; print_monomial_with_vars(n, tout); tout << "sign: " << sign << "\n";);
        generate_sign_lemma(m, n, sign);
        return true;
    }

    void init_abs_val_table() {
        // register those vars that a factors in a monomial
        for (auto & p : m_monomials_containing_var) {
            m_vars_equivalence.register_var_with_abs_val(p.first, vvr(p.first));
        }
        // register monomial vars too
        for (auto & p : m_var_to_its_monomial) {
            m_vars_equivalence.register_var_with_abs_val(p.first, vvr(p.first));
        }
    }

    // replaces each var with its abs root and sorts the return vector
    template <typename T>
    unsigned_vector get_abs_key(const T& m) const {
        unsigned_vector r;
        for (unsigned j : m) {
            r.push_back(m_vars_equivalence.get_abs_root_for_var(abs(vvr(j))));
        }
        std::sort(r.begin(), r.end());
        return r;
    }

    // For each monomial m = m_monomials[i], where i is in m_to_refine,
    // try adding the pair (get_abs_key(m), i) to map
    std::unordered_map<unsigned_vector, unsigned, hash_svector> create_relevant_abs_keys() {
        std::unordered_map<unsigned_vector, unsigned, hash_svector> r;
        for (unsigned i : m_to_refine) {
            unsigned_vector key = get_abs_key(m_monomials[i]);
            if (contains(r, key))
                continue;
            r[key] = i;
        }
        return r;
    }

    void basic_sign_lemma_model_based_one_mon(const monomial& m, int product_sign) {
        if (product_sign == 0) {
            TRACE("nla_solver", tout << "zero product sign\n";);
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
    
    bool basic_sign_lemma_model_based() {
        init_abs_val_table();        
        std::unordered_map<unsigned_vector, unsigned, hash_svector> key_mons =
            create_relevant_abs_keys();
        unsigned i = random() % m_to_refine.size();
        unsigned ii = i;
        do {
            const monomial& m = m_monomials[m_to_refine[i]];
            int mon_sign = rat_sign(vvr(m));
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

    
    bool basic_sign_lemma_on_mon(unsigned i, std::unordered_set<unsigned> & explored){
        const monomial& m = m_monomials[i];
        TRACE("nla_solver_details", tout << "i = " << i << ", mon = "; print_monomial_with_vars(m, tout););
        const index_with_sign&  rm_i_s = m_rm_table.get_rooted_mon(i);
        unsigned k = rm_i_s.index();
        if (!try_insert(k, explored))
            return false;

        const auto& mons_to_explore = m_rm_table.vec()[k].m_mons;
        
        for (index_with_sign i_s : mons_to_explore) {
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
    bool basic_sign_lemma(bool derived) {
        if (!derived)
            return basic_sign_lemma_model_based();

        std::unordered_set<unsigned> explored;
        for (unsigned i : m_to_refine){
            if (basic_sign_lemma_on_mon(i, explored))
                return true;
        }
        return false;
    }

    bool var_is_fixed_to_zero(lpvar j) const {
        return 
            m_lar_solver.column_has_upper_bound(j) &&
            m_lar_solver.column_has_lower_bound(j) &&
            m_lar_solver.get_upper_bound(j) == lp::zero_of_type<lp::impq>() &&
            m_lar_solver.get_lower_bound(j) == lp::zero_of_type<lp::impq>();
    }
    bool var_is_fixed_to_val(lpvar j, const rational& v) const {
        return 
            m_lar_solver.column_has_upper_bound(j) &&
            m_lar_solver.column_has_lower_bound(j) &&
            m_lar_solver.get_upper_bound(j) == v && m_lar_solver.get_lower_bound(j) == v;
    }

    bool var_is_fixed(lpvar j) const {
        return 
            m_lar_solver.column_has_upper_bound(j) &&
            m_lar_solver.column_has_lower_bound(j) &&
            m_lar_solver.get_upper_bound(j) == m_lar_solver.get_lower_bound(j);
    }
    
    std::ostream & print_ineq(const ineq & in, std::ostream & out) const {
        m_lar_solver.print_term(in.m_term, out);
        out << " " << lconstraint_kind_string(in.m_cmp) << " " << in.m_rs;
        return out;
    }

    std::ostream & print_var(lpvar j, std::ostream & out) const {
        auto it = m_var_to_its_monomial.find(j);
        if (it != m_var_to_its_monomial.end()) {
            print_monomial(m_monomials[it->second], out);
            out << " = " << vvr(j);;
        }
        
        m_lar_solver.print_column_info(j, out) <<";";
        return out;
    }

    std::ostream & print_monomials(std::ostream & out) const {
        for (auto &m : m_monomials) {
            print_monomial_with_vars(m, out);
        }
        return out;
    }    

    std::ostream & print_ineqs(const lemma& l, std::ostream & out) const {
        std::unordered_set<lpvar> vars;
        out << "ineqs: ";
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
        return out;
    }
    
    std::ostream & print_factorization(const factorization& f, std::ostream& out) const {
        for (unsigned k = 0; k < f.size(); k++ ) {
            if (f[k].is_var())
                print_var(f[k].index(), out);
            else {
                out << "(";
                print_product(m_rm_table.vec()[f[k].index()].vars(), out);
                out << ")";
            }
            
            if (k < f.size() - 1)
                out << "*";
        }
        return out;
    }
    
    bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const {
        SASSERT(vars_are_roots(vars));
        auto it = m_rm_table.map().find(vars);
        if (it == m_rm_table.map().end()) {
            return false;
        }
        
        i = it->second;
        TRACE("nla_solver",);
        
        SASSERT(lp::vectors_are_equal_(vars, m_rm_table.vec()[i].vars()));
        return true;
    }

    struct factorization_factory_imp: factorization_factory {
        const imp&  m_imp;
        
        factorization_factory_imp(const svector<lpvar>& m_vars, const imp& s) :
            factorization_factory(m_vars),
            m_imp(s) { }
        
        bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const {
            return m_imp.find_rm_monomial_of_vars(vars, i);
        }
    };
    // here we use the fact
    // xy = 0 -> x = 0 or y = 0
    bool basic_lemma_for_mon_zero(const rooted_mon& rm, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););
        add_empty_lemma();
        explain_fixed_var(var(rm));
        std::unordered_set<lpvar> processed;
        for (auto j : f) {
            if (try_insert(var(j), processed))
                mk_ineq(var(j), llc::EQ);
        }
        explain(rm, current_expl());
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }

    void explain_existing_lower_bound(lpvar j) {
        SASSERT(has_lower_bound(j));
        current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
    }

    void explain_existing_upper_bound(lpvar j) {
        SASSERT(has_upper_bound(j));
        current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
    }
    
    void explain_separation_from_zero(lpvar j) {
        SASSERT(!vvr(j).is_zero());
        if (vvr(j).is_pos())
            explain_existing_lower_bound(j);
        else
            explain_existing_upper_bound(j);
    }

    int get_derived_sign(const rooted_mon& rm, const factorization& f) const {
        rational sign = rm.orig_sign(); // this is the flip sign of the variable var(rm)
        SASSERT(!sign.is_zero());
        for (const factor& fc: f) {
            lpvar j = var(fc);
            if (!(var_has_positive_lower_bound(j) || var_has_negative_upper_bound(j))) {
                return 0;
            }
            m_vars_equivalence.map_to_root(j, sign);
        }
        return rat_sign(sign);
    }
    // here we use the fact xy = 0 -> x = 0 or y = 0
    void basic_lemma_for_mon_zero_model_based(const rooted_mon& rm, const factorization& f) {        
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););
        SASSERT(vvr(rm).is_zero()&& !rm_check(rm));
        add_empty_lemma();
        int sign = get_derived_sign(rm, f);
        if (sign == 0) {
            mk_ineq(var(rm), llc::NE);        
            for (auto j : f) {
                mk_ineq(var(j), llc::EQ);
            }
        } else {
            mk_ineq(var(rm), llc::NE);        
            for (auto j : f) {
                explain_separation_from_zero(var(j));
            }            
        }
        explain(rm, current_expl());
        explain(f, current_expl());
        TRACE("nla_solver", print_lemma(tout););
    }

    void trace_print_monomial_and_factorization(const rooted_mon& rm, const factorization& f, std::ostream& out) const {
        out << "rooted vars: ";
        print_product(rm.m_vars, out);
        out << "\n";
        
        print_monomial(rm.orig_index(), out << "mon:  ") << "\n";
        out << "value: " << vvr(rm) << "\n";
        print_factorization(f, out << "fact: ") << "\n";
    }

    void explain_var_separated_from_zero(lpvar j) {
        SASSERT(var_is_separated_from_zero(j));
        if (m_lar_solver.column_has_upper_bound(j) && (m_lar_solver.get_upper_bound(j)< lp::zero_of_type<lp::impq>())) 
            current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
        else 
            current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
    }

    void explain_fixed_var(lpvar j) {
        SASSERT(var_is_fixed(j));
        current_expl().add(m_lar_solver.get_column_upper_bound_witness(j));
        current_expl().add(m_lar_solver.get_column_lower_bound_witness(j));
    }
    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_non_zero_model_based(const rooted_mon& rm, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););
        SASSERT (!vvr(rm).is_zero());
        int zero_j = -1;
        for (auto j : f) {
            if (vvr(j).is_zero()) {
                zero_j = var(j);
                break;
            }
        }

        if (zero_j == -1) {
            return false;
        } 
        add_empty_lemma();
        mk_ineq(zero_j, llc::NE);
        mk_ineq(var(rm), llc::EQ);

        explain(rm, current_expl());
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }

    bool var_has_positive_lower_bound(lpvar j) const {
        return m_lar_solver.column_has_lower_bound(j) && m_lar_solver.get_lower_bound(j) > lp::zero_of_type<lp::impq>();
    }

    bool var_has_negative_upper_bound(lpvar j) const {
        return m_lar_solver.column_has_upper_bound(j) && m_lar_solver.get_upper_bound(j) < lp::zero_of_type<lp::impq>();
    }
    
    bool var_is_separated_from_zero(lpvar j) const {
        return
            var_has_negative_upper_bound(j) ||
            var_has_positive_lower_bound(j);
    }
    
    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_non_zero_derived(const rooted_mon& rm, const factorization& f) {
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
    bool basic_lemma_for_mon_neutral_monomial_to_factor_model_based(const rooted_mon& rm, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););

        lpvar mon_var = m_monomials[rm.orig_index()].var();
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
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

        if (not_one_j == static_cast<lpvar>(-1)) {
            return false;
        } 

        add_empty_lemma();
        // mon_var = 0
        mk_ineq(mon_var, llc::EQ);
        
        // negate abs(jl) == abs()
        if (vvr(jl) == - vvr(mon_var))
            mk_ineq(jl, mon_var, llc::NE, current_lemma());   
        else  // jl == mon_var
            mk_ineq(jl, -rational(1), mon_var, llc::NE);   

        // not_one_j = 1
        mk_ineq(not_one_j, llc::EQ,  rational(1));   
        
        // not_one_j = -1
        mk_ineq(not_one_j, llc::EQ, -rational(1));
        explain(rm, current_expl());
        explain(f, current_expl());

        TRACE("nla_solver", print_lemma(tout); );
        return true;
    }

    bool vars_are_equiv(lpvar a, lpvar b) const {
        SASSERT(abs(vvr(a)) == abs(vvr(b)));
        return m_vars_equivalence.vars_are_equiv(a, b) ||
            (var_is_fixed(a) && var_is_fixed(b));
    }

    void explain_equiv_vars(lpvar a, lpvar b) {
        SASSERT(abs(vvr(a)) == abs(vvr(b)));
        if (m_vars_equivalence.vars_are_equiv(a, b)) {
            explain(a, current_expl());
            explain(b, current_expl());
        } else {
            explain_fixed_var(a);
            explain_fixed_var(b);
        }
    }
    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
    bool basic_lemma_for_mon_neutral_monomial_to_factor_derived(const rooted_mon& rm, const factorization& f) {
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
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(const rooted_mon& rm, const factorization& f) {
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

        if (not_one + 1) {
            // we found the only not_one
            if (vvr(rm) == vvr(not_one) * sign) {
                TRACE("nla_solver", tout << "the whole equal to the factor" << std::endl;);
                return false;
            }
        }
        
        add_empty_lemma();
        explain(rm, current_expl());

        for (auto j : f){
            lpvar var_j = var(j);
            if (not_one == var_j) continue;
            mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) : flip_sign(j) * vvr(j));   
        }

        if (not_one == static_cast<lpvar>(-1)) {
            mk_ineq(m_monomials[rm.orig_index()].var(), llc::EQ, sign);
        } else {
            mk_ineq(m_monomials[rm.orig_index()].var(), -sign, not_one, llc::EQ);
        }
        explain(f, current_expl());
        TRACE("nla_solver",
              tout << "rm = "; print_rooted_monomial_with_vars(rm, tout);
              print_lemma(tout););
        return true;
    }
    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(const rooted_mon& rm, const factorization& f) {
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
            mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) : flip_sign(j) * vvr(j));   
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
    
    void basic_lemma_for_mon_neutral_model_based(const rooted_mon& rm, const factorization& factorization) {
        basic_lemma_for_mon_neutral_monomial_to_factor_model_based(rm, factorization);
        basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(rm, factorization);
     }

    bool basic_lemma_for_mon_neutral_derived(const rooted_mon& rm, const factorization& factorization) {
        return
            basic_lemma_for_mon_neutral_monomial_to_factor_derived(rm, factorization) || 
            basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(rm, factorization);
        return false;
    }

    void explain(const factorization& f, lp::explanation& exp) {
        for (const auto& fc : f) {
            explain(fc, exp);
        }
    }

    bool has_zero_factor(const factorization& factorization) const {
        for (factor f : factorization) {
            if (vvr(f).is_zero())
                return true;
        }
        return false;
    }

    // none of the factors is zero -> |fc[factor_index]| <= |rm|
    void generate_pl(const rooted_mon& rm, const factorization& fc, int factor_index) {
        TRACE("nla_solver", tout << "factor_index = " << factor_index << ", rm = ";
              print_rooted_monomial_with_vars(rm, tout);
              tout << "fc = "; print_factorization(fc, tout);
              tout << "orig mon = "; print_monomial(m_monomials[rm.orig_index()], tout););
        add_empty_lemma();
        int fi = 0;
        rational rmv = vvr(rm);
        rational sm = rational(rat_sign(rmv));
        unsigned mon_var = var(rm);
        mk_ineq(sm, mon_var, llc::LT);
        for (factor f : fc) {
            if (fi++ != factor_index) {
                mk_ineq(var(f), llc::EQ);
            } else {
                lpvar j = var(f);
                rational jv = vvr(j);
                rational sj = rational(rat_sign(jv));
                SASSERT(sm*rmv < sj*jv);
                mk_ineq(sj, j, llc::LT);
                mk_ineq(sm, mon_var, -sj, j, llc::GE);
            }
        }
        explain(fc, current_expl());
        explain(rm, current_expl());
        TRACE("nla_solver", print_lemma(tout); );
    }   

    template <typename T>
    bool has_zero(const T& product) const {
        for (const rational & t : product) {
            if (t.is_zero())
                return true;
        }
        return false;
    }

        template <typename T>
    bool mon_has_zero(const T& product) const {
        for (lpvar j: product) {
            if (vvr(j).is_zero())
                return true;
        }
        return false;
    }

    // x != 0 or y = 0 => |xy| >= |y|
    bool proportion_lemma_model_based(const rooted_mon& rm, const factorization& factorization) {
        rational rmv = abs(vvr(rm));
        if (rmv.is_zero()) {
            SASSERT(has_zero_factor(factorization));
            return false;
        }
        int factor_index = 0;
        for (factor f : factorization) {
            if (abs(vvr(f)) > rmv) {
                generate_pl(rm, factorization, factor_index);
                return true;
            }
            factor_index++;
        }
        return false;
    }
    // x != 0 or y = 0 => |xy| >= |y|
    bool proportion_lemma_derived(const rooted_mon& rm, const factorization& factorization) {
        return false;
        rational rmv = abs(vvr(rm));
        if (rmv.is_zero()) {
            SASSERT(has_zero_factor(factorization));
            return false;
        }
        int factor_index = 0;
        for (factor f : factorization) {
            if (abs(vvr(f)) > rmv) {
                generate_pl(rm, factorization, factor_index);
                return true;
            }
            factor_index++;
        }
        return false;
    }

    void basic_lemma_for_mon_model_based(const rooted_mon& rm) {
        TRACE("nla_solver", tout << "rm = "; print_rooted_monomial(rm, tout););
        if (vvr(rm).is_zero()) {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                basic_lemma_for_mon_zero_model_based(rm, factorization);
                basic_lemma_for_mon_neutral_model_based(rm, factorization);
            }
        } else {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                basic_lemma_for_mon_non_zero_model_based(rm, factorization);
                basic_lemma_for_mon_neutral_model_based(rm, factorization);
                proportion_lemma_model_based(rm, factorization) ;
            }
        }
    }

    bool basic_lemma_for_mon_derived(const rooted_mon& rm) {
        if (var_is_fixed_to_zero(var(rm))) {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                if (basic_lemma_for_mon_zero(rm, factorization) ||
                    basic_lemma_for_mon_neutral_derived(rm, factorization)) {
                    explain(factorization, current_expl());
                    return true;
                }
            }
        } else {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                if (basic_lemma_for_mon_non_zero_derived(rm, factorization) ||
                    basic_lemma_for_mon_neutral_derived(rm, factorization) ||
                    proportion_lemma_derived(rm, factorization)) {
                    explain(factorization, current_expl());
                    return true;
                }
            }
        }
        return false;
    }
    
    // Use basic multiplication properties to create a lemma
    // for the given monomial.
    // "derived" means derived from constraints - the alternative is model based
    void basic_lemma_for_mon(const rooted_mon& rm, bool derived) {
        if (derived)
            basic_lemma_for_mon_derived(rm);
        else
            basic_lemma_for_mon_model_based(rm);
    }

    void init_rm_to_refine() {
        if (!m_rm_table.to_refine().empty())
            return;
        std::unordered_set<unsigned> ref;
        ref.insert(m_to_refine.begin(), m_to_refine.end());
        m_rm_table.init_to_refine(ref);
    }

    lp::lp_settings& settings() {
        return m_lar_solver.settings();
    }
    
    unsigned random() {return settings().random_next();}
    
    // use basic multiplication properties to create a lemma
    bool basic_lemma(bool derived) {
        if (basic_sign_lemma(derived))
            return true;
        if (derived)
            return false;
        init_rm_to_refine();
        const auto& rm_ref = m_rm_table.to_refine();
        TRACE("nla_solver", tout << "rm_ref = "; print_vector(rm_ref, tout););
        unsigned start = random() % rm_ref.size();
        unsigned i = start;
        do {
            const rooted_mon& r = m_rm_table.vec()[rm_ref[i]];
            SASSERT (!check_monomial(m_monomials[r.orig_index()]));
            basic_lemma_for_mon(r, derived);
            if (++i == rm_ref.size()) {
                i = 0;
            }
        } while(i != start && !done());
        
        return false;
    }

    void map_monomial_vars_to_monomial_indices(unsigned i) {
        const monomial& m = m_monomials[i];
        for (lpvar j : m.vars()) {
            auto it = m_monomials_containing_var.find(j);
            if (it == m_monomials_containing_var.end()) {
                unsigned_vector ms;
                ms.push_back(i);
                m_monomials_containing_var[j] = ms;
            }
            else {
                it->second.push_back(i);
            }
        }
    }

    void map_vars_to_monomials() {
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            const monomial& m = m_monomials[i];
            lpvar v = m.var();
            SASSERT(m_var_to_its_monomial.find(v) == m_var_to_its_monomial.end());
            m_var_to_its_monomial[v] = i;
            map_monomial_vars_to_monomial_indices(i);
        }
    }

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs() {
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

    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1) {
        if (t->size() != 2)
            return;
        bool seen_minus = false;
        bool seen_plus = false;
        lpvar i = -1, j = -1;
        for(const auto & p : *t) {
            const auto & c = p.coeff();
            if (c == 1) {
                seen_plus = true;
            } else if (c == - 1) {
                seen_minus = true;
            } else {
                return;
            }
            if (i == static_cast<lpvar>(-1))
                i = p.var();
            else
                j = p.var();
        }
        SASSERT(j != static_cast<unsigned>(-1));
        rational sign((seen_minus && seen_plus)? 1 : -1);
        m_vars_equivalence.add_equiv(i, j, sign, c0, c1);
    }

    // x is equivalent to y if x = +- y
    void init_vars_equivalence() {
        SASSERT(m_vars_equivalence.empty());
        collect_equivs();
        m_vars_equivalence.create_tree();
        TRACE("nla_solver", tout << "number of equivs = " << m_vars_equivalence.size(););
        
        SASSERT((settings().random_next() % 100) || tables_are_ok());
    }

    bool vars_table_is_ok() const {
        for (lpvar j = 0; j < m_lar_solver.number_of_vars(); j++) {
            auto it = m_var_to_its_monomial.find(j);
            if (it != m_var_to_its_monomial.end()
                && m_monomials[it->second].var() != j) {
                TRACE("nla_solver", tout << "j = ";
                      print_var(j, tout););
                return false;
            }
        }
        for (unsigned i = 0; i < m_monomials.size(); i++){
            const monomial& m = m_monomials[i];
            lpvar j = m.var();
            if (m_var_to_its_monomial.find(j) == m_var_to_its_monomial.end()){
                return false;
            }
        }
        return true;
    }

    bool rm_table_is_ok() const {
        for (const auto & rm : m_rm_table.vec()) {
            for (lpvar j : rm.vars()) {
                if (!m_vars_equivalence.is_root(j)){
                    TRACE("nla_solver", print_var(j, tout););
                    return false;
                }
            }
        }
        return true;
    }
    
    bool tables_are_ok() const {
        return vars_table_is_ok() && rm_table_is_ok();
    }
    
    bool var_is_a_root(lpvar j) const { return m_vars_equivalence.is_root(j); }

    template <typename T>
    bool vars_are_roots(const T& v) const {
        for (lpvar j: v) {
            if (!var_is_a_root(j))
                return false;
        }
        return true;
    }


    void register_monomial_in_tables(unsigned i_mon) {
        const monomial& m = m_monomials[i_mon];
        monomial_coeff mc = canonize_monomial(m);
        TRACE("nla_solver_rm", tout << "i_mon = " << i_mon << ", mon = ";
              print_monomial(m_monomials[i_mon], tout);
              tout << "\nmc = ";
              print_product(mc.vars(), tout);
              );
        m_rm_table.register_key_mono_in_rooted_monomials(mc, i_mon);        
    }

    template <typename T>
    void trace_print_rms(const T& p, std::ostream& out) {
        out << "p = {";
        for (auto j : p) {
            out << "\nj = " << j <<
                ", rm = ";
            print_rooted_monomial(m_rm_table.vec()[j], out);
        }
        out << "\n}";
    }

    void print_monomial_stats(const monomial& m, std::ostream& out) {
        if (m.size() == 2) return;
        monomial_coeff mc = canonize_monomial(m);
        for(unsigned i = 0; i < mc.vars().size(); i++){
            if (abs(vvr(mc.vars()[i])) == rational(1)) {
                auto vv = mc.vars();
                vv.erase(vv.begin()+i);
                auto it = m_rm_table.map().find(vv);
                if (it == m_rm_table.map().end()) {
                    out << "nf length" << vv.size() << "\n"; ;
                }
            }
        }
    }
    
    void print_stats(std::ostream& out) {
        // for (const auto& m : m_monomials) 
        //     print_monomial_stats(m, out);
        m_rm_table.print_stats(out);
    }
        
    void register_monomials_in_tables() {
        for (unsigned i = 0; i < m_monomials.size(); i++) 
            register_monomial_in_tables(i);

        m_rm_table.fill_rooted_monomials_containing_var();
        m_rm_table.fill_proper_factors();
        TRACE("nla_solver_rm", print_stats(tout););
    }

    void clear() {
        m_var_to_its_monomial.clear();
        m_vars_equivalence.clear();
        m_rm_table.clear();
        m_monomials_containing_var.clear();
        m_lemma_vec->clear();
    }
    
    void init_search() {
        clear();
        map_vars_to_monomials();
        init_vars_equivalence();
        register_monomials_in_tables();
    }

    void init_to_refine() {
        m_to_refine.clear();
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                m_to_refine.push_back(i);
        }
        TRACE("nla_solver",
              tout << m_to_refine.size() << " mons to refine: ";
              for (unsigned i: m_to_refine) {
                  print_monomial_with_vars(m_monomials[i], tout);
              }
              );
    }

    bool divide(const rooted_mon& bc, const factor& c, factor & b) const {
        svector<lpvar> c_vars = sorted_vars(c);
        TRACE("nla_solver_div",
              tout << "c_vars = ";
              print_product(c_vars, tout);
              tout << "\nbc_vars = ";
              print_product(bc.vars(), tout););
        if (!lp::is_proper_factor(c_vars, bc.vars()))
            return false;
            
        auto b_vars = lp::vector_div(bc.vars(), c_vars);
        TRACE("nla_solver_div", tout << "b_vars = "; print_product(b_vars, tout););
        SASSERT(b_vars.size() > 0);
        if (b_vars.size() == 1) {
            b = factor(b_vars[0]);
            return true;
        }
        auto it = m_rm_table.map().find(b_vars);
        if (it == m_rm_table.map().end()) {
            TRACE("nla_solver_div", tout << "not in rooted";);
            return false;
        }
        b = factor(it->second, factor_type::RM);
        TRACE("nla_solver_div", tout << "success div:"; print_factor(b, tout););
        return true;
    }

    void negate_factor_equality(const factor& c,
                                const factor& d) {
        if (c == d)
            return;
        lpvar i = var(c);
        lpvar j = var(d);
        auto iv = vvr(i), jv = vvr(j);
        SASSERT(abs(iv) == abs(jv));
        if (iv == jv) {
            mk_ineq(i, -rational(1), j, llc::NE);
        } else { // iv == -jv
            mk_ineq(i, j, llc::NE, current_lemma());                
        }
    }
    
    void negate_factor_relation(const rational& a_sign, const factor& a, const rational& b_sign, const factor& b) {
        rational a_fs = flip_sign(a);
        rational b_fs = flip_sign(b);
        llc cmp = a_sign*vvr(a) < b_sign*vvr(b)? llc::GE : llc::LE;
        mk_ineq(a_fs*a_sign, var(a), - b_fs*b_sign, var(b), cmp);
    }

    // |c_sign| = |d_sign| = 1, and c*c_sign = d*d_sign > 0
    // a*c_sign > b*d_sign => ac > bd.
    // The sign ">" above is replaced by ab_cmp
    void generate_ol(const rooted_mon& ac,                     
                     const factor& a,
                     int c_sign,
                     const factor& c,
                     const rooted_mon& bd,
                     const factor& b,
                     int d_sign,
                     const factor& d,
                     llc ab_cmp) {
        add_empty_lemma();
        mk_ineq(rational(c_sign) * flip_sign(c), var(c), llc::LE);
        negate_factor_equality(c, d);
        negate_factor_relation(rational(c_sign), a, rational(d_sign), b);
        mk_ineq(flip_sign(ac), var(ac), -flip_sign(bd), var(bd), ab_cmp);
        explain(ac, current_expl());
        explain(a, current_expl());
        explain(bd, current_expl());
        explain(b, current_expl());
        explain(c, current_expl());
        explain(d, current_expl());
        TRACE("nla_solver", print_lemma(tout););
    }

    std::unordered_set<lpvar> collect_vars(  const lemma& l) {
        std::unordered_set<lpvar> vars;
        for (const auto& i : current_lemma().ineqs()) {
            for (const auto& p : i.term()) {
                lpvar j = p.var();
                vars.insert(j);
                auto it = m_var_to_its_monomial.find(j);
                if (it != m_var_to_its_monomial.end()) {
                    for (lpvar k : m_monomials[it->second])
                        vars.insert(k);
                }
            }
        }
        for (const auto& p : current_expl()) {
            const auto& c = m_lar_solver.get_constraint(p.second);
            for (const auto& r : c.coeffs()) {
                lpvar j = r.second;
                vars.insert(j);
                auto it = m_var_to_its_monomial.find(j);
                if (it != m_var_to_its_monomial.end()) {
                    for (lpvar k : m_monomials[it->second])
                        vars.insert(k);
                }
            }
        }
        return vars;
    }

    void print_lemma(std::ostream& out) {
        static int n = 0;
        out << "lemma:" << ++n << " ";
        print_ineqs(current_lemma(), out);
        print_explanation(current_expl(), out);
        std::unordered_set<lpvar> vars = collect_vars(current_lemma());
        
        for (lpvar j : vars) {
            print_var(j, out);
        }
    }
    
    bool get_cd_signs_for_ol(const rational& c, const rational& d, int& c_sign, int & d_sign) const {
        if (c.is_zero() || d.is_zero())
            return false;
        if (c == d) {
            if (c.is_pos()) {
                c_sign = d_sign = 1;
            }
            else {
                c_sign = d_sign = -1;
            }
            return true;
        } else if (c == -d){
            if (c.is_pos()) {
                c_sign = 1;
                d_sign = -1;
            }
            else {
                c_sign = -1;
                d_sign = 1;
            }
            return true;
        }
        return false;
    }
    
    bool order_lemma_on_ac_and_bd_and_factors(const rooted_mon& ac,
                                              const factor& a,
                                              const factor& c,
                                              const rooted_mon& bd,
                                              const factor& b,
                                              const factor& d) {
        SASSERT(abs(vvr(c)) == abs(vvr(d)));
        auto cv = vvr(c); auto dv = vvr(d);
        int c_sign, d_sign;
        if (!get_cd_signs_for_ol(cv, dv, c_sign, d_sign))
            return false;
        SASSERT(cv*c_sign == dv*d_sign && (dv*d_sign).is_pos() && abs(c_sign) == 1 &&
                abs(d_sign) == 1);
        auto av = vvr(a)*rational(c_sign); auto bv = vvr(b)*rational(d_sign);
        auto acv = vvr(ac); auto bdv = vvr(bd);
        TRACE("nla_solver",
              tout << "ac = ";
              print_rooted_monomial_with_vars(ac, tout);
              tout << "\nbd = ";
              print_rooted_monomial_with_vars(bd, tout);
              tout << "\na = ";
              print_factor_with_vars(a, tout);
              tout << ", \nb = ";
              print_factor_with_vars(b, tout);
              tout << "\nc = ";
              print_factor_with_vars(c, tout);
              tout << ", \nd = ";
              print_factor_with_vars(d, tout);
              );
        
        if (av < bv){
            if(!(acv < bdv)) {
                generate_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::LT);
                return true;
            }
        } else if (av > bv){
            if(!(acv > bdv)) {
                generate_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::GT);
                return true;
            }
        }
        return false;
    }
    
    // a > b && c > 0 && d = c => ac > bd 
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c   
    bool order_lemma_on_ac_and_bd(const rooted_mon& rm_ac,
                                  const factorization& ac_f,
                                  unsigned k,
                                  const rooted_mon& rm_bd,
                                  const factor& d) {
        TRACE("nla_solver",   tout << "rm_ac = ";
              print_rooted_monomial(rm_ac, tout);
              tout << "\nrm_bd = ";
              print_rooted_monomial(rm_bd, tout);
              tout << "\nac_f[k] = ";
              print_factor_with_vars(ac_f[k], tout);
              tout << "\nd  = ";
              print_factor_with_vars(d, tout););
        SASSERT(abs(vvr(ac_f[k])) == abs(vvr(d)));
        factor b;
        if (!divide(rm_bd, d, b)){
            return false;
        }

        return order_lemma_on_ac_and_bd_and_factors(rm_ac, ac_f[(k + 1) % 2], ac_f[k], rm_bd, b, d);
    }
  void maybe_add_a_factor(lpvar i,
                            const factor& c,
                            std::unordered_set<lpvar>& found_vars,
                            std::unordered_set<unsigned>& found_rm,
                            vector<factor> & r) const {
        SASSERT(abs(vvr(i)) == abs(vvr(c)));
        auto it = m_var_to_its_monomial.find(i);
        if (it == m_var_to_its_monomial.end()) {
            i = m_vars_equivalence.map_to_root(i);
            if (try_insert(i, found_vars)) {
                r.push_back(factor(i, factor_type::VAR));
            }
        } else {
            SASSERT(m_monomials[it->second].var() == i && abs(vvr(m_monomials[it->second])) == abs(vvr(c)));
            const index_with_sign & i_s = m_rm_table.get_rooted_mon(it->second);
            unsigned rm_i = i_s.index();
            //                SASSERT(abs(vvr(m_rm_table.vec()[i])) == abs(vvr(c)));
            if (try_insert(rm_i, found_rm)) {
                r.push_back(factor(rm_i, factor_type::RM));
                TRACE("nla_solver", tout << "inserting factor = "; print_factor_with_vars(factor(rm_i, factor_type::RM), tout); );
            }
        }
    }
    
    vector<factor> factors_with_the_same_abs_val(const factor& c) const {
        vector<factor> r;
        std::unordered_set<lpvar> found_vars;
        std::unordered_set<unsigned> found_rm;
        TRACE("nla_solver", tout << "c = "; print_factor_with_vars(c, tout););
        for (lpvar i :  m_vars_equivalence.get_vars_with_the_same_abs_val(vvr(c))) {
            maybe_add_a_factor(i, c, found_vars, found_rm, r);
        }
        return r;
    }
    
    bool order_lemma_on_ad(const rooted_mon& rm, const factorization& ac, unsigned k, const factor & d) {
        TRACE("nla_solver", tout << "d = "; print_factor_with_vars(d, tout); );
        SASSERT(abs(vvr(d)) == abs(vvr(ac[k])));
        if (d.is_var()) {
            TRACE("nla_solver", tout << "var(d) = " << var(d););
            for (unsigned rm_bd : m_rm_table.var_map()[d.index()]) {
                TRACE("nla_solver", );
                if (order_lemma_on_ac_and_bd(rm ,ac, k, m_rm_table.vec()[rm_bd], d)) {
                    return true;
                }
            }
        } else {
            for (unsigned rm_b : m_rm_table.proper_factors()[d.index()]) {
                if (order_lemma_on_ac_and_bd(rm , ac, k, m_rm_table.vec()[rm_b], d)) {
                    return true;
                }
            }
        }
        return false;
    }

    
    // a > b && c > 0 => ac > bc
    // ac is a factorization of rm.vars()
    // ac[k] plays the role of c   
    bool order_lemma_on_factor_explore(const rooted_mon& rm, const factorization& ac, unsigned k) {
        auto c = ac[k];
        TRACE("nla_solver", tout << "k = " << k << ", c = "; print_factor_with_vars(c, tout); );

        for (const factor & d : factors_with_the_same_abs_val(c)) {
            if (order_lemma_on_ad(rm, ac, k, d))
                return true;
        }
        return false;
    }
    // ab is a factorization of rm.vars()
    // if, say, ab = -3, when a = -2, and b = 2
    // then we create a lemma
    // b <= 0 or a > -2 or ab <= -2b     
    void order_lemma_on_factorization(const rooted_mon& rm, const factorization& ab) {
        const monomial& m = m_monomials[rm.orig_index()];
        rational sign = rm.orig_sign();
        for(factor f: ab)
            sign *= flip_sign(f);
        const rational & fv = vvr(ab[0]) * vvr(ab[1]);
        const rational mv = sign * vvr(m);
        TRACE("nla_solver",
              tout << "ab.size()=" << ab.size() << "\n";
              tout << "we should have sign*vvr(m):" << mv << "=(" << sign << ")*(" << vvr(m) <<") to be equal to " << " vvr(ab[0])*vvr(ab[1]):" << fv << "\n";);
        if (mv == fv)
            return;
        bool gt = mv > fv;
        TRACE("nla_solver_f", tout << "m="; print_monomial_with_vars(m, tout); tout << "\nfactorization="; print_factorization(ab, tout););
        for (unsigned j = 0, k = 1; j < 2; j++, k--) {
            order_lemma_on_ab(m, sign, var(ab[k]), var(ab[j]), gt);
            explain(ab, current_expl()); explain(m, current_expl());
            order_lemma_on_factor_explore(rm, ab, j);
        }
        
    }
    
    // if gt is true we need to deduce ab <= vvr(b)*a
    void order_lemma_on_ab_gt(const monomial& m, const rational& sign, lpvar a, lpvar b) {
        SASSERT(sign * vvr(m) > vvr(a) * vvr(b));
        add_empty_lemma();
        if (vvr(a).is_pos()) {
            TRACE("nla_solver", tout << "a is pos\n";);
            //negate a > 0
            mk_ineq(a, llc::LE);
            // negate b <= vvr(b)
            mk_ineq(b, llc::GT, vvr(b));
            // ab <= vvr(b)a
            mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);
        } else {
            TRACE("nla_solver", tout << "a is neg\n";);
            SASSERT(vvr(a).is_neg());
            //negate a < 0
            mk_ineq(a, llc::GE);
            // negate b >= vvr(b)
            mk_ineq(b, llc::LT, vvr(b));
            // ab <= vvr(b)a
            mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);
        }
        TRACE("nla_solver", print_lemma(tout););
    }
    // we need to deduce ab >= vvr(b)*a
    void order_lemma_on_ab_lt(const monomial& m, const rational& sign, lpvar a, lpvar b) {
        SASSERT(sign * vvr(m) < vvr(a) * vvr(b));
        add_empty_lemma();
        if (vvr(a).is_pos()) {
            //negate a > 0
            mk_ineq(a, llc::LE);
            // negate b >= vvr(b)
            mk_ineq(b, llc::LT, vvr(b));
            // ab <= vvr(b)a
            mk_ineq(sign, m.var(), -vvr(b), a, llc::GE);
        } else {
            SASSERT(vvr(a).is_neg());
            //negate a < 0
            mk_ineq(a, llc::GE);
            // negate b <= vvr(b)
            mk_ineq(b, llc::GT, vvr(b));
            // ab >= vvr(b)a
            mk_ineq(sign, m.var(), -vvr(b), a, llc::GE);
        }
        TRACE("nla_solver", print_lemma(tout););
    }


    void order_lemma_on_ab(const monomial& m, const rational& sign, lpvar a, lpvar b, bool gt) {
        if (gt)
            order_lemma_on_ab_gt(m, sign, a, b);
        else 
            order_lemma_on_ab_lt(m, sign, a, b);
    }
 
    // void order_lemma_on_ab(const monomial& m, const rational& sign, lpvar a, lpvar b, bool gt) {
    //     add_empty_lemma();
    //     if (gt) {
    //         if (vvr(a).is_pos()) {
    //             //negate a > 0
    //             mk_ineq(a, llc::LE);
    //             // negate b >= vvr(b)
    //             mk_ineq(b, llc::LT, vvr(b));
    //             // ab <= vvr(b)a
    //             mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);
    //         } else {
    //             SASSERT(vvr(a).is_neg());
    //             //negate a < 0
    //             mk_ineq(a, llc::GE);
    //             // negate b <= vvr(b)
    //             mk_ineq(b, llc::GT, vvr(b));
    //             // ab < vvr(b)a
    //             mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);  }
    //     }
    // }
    
    // a > b && c > 0 => ac > bc
    void order_lemma_on_monomial(const rooted_mon& rm) {
        TRACE("nla_solver_details",
              tout << "rm = "; print_product(rm, tout);
              tout << ", orig = "; print_monomial(m_monomials[rm.orig_index()], tout);
              );
        for (auto ac : factorization_factory_imp(rm.vars(), *this)) {
            if (ac.size() != 2)
                continue;
            order_lemma_on_factorization(rm, ac);
            if (done())
                break;
        }
    }
    
    void order_lemma() {
        TRACE("nla_solver", );
        init_rm_to_refine();
        const auto& rm_ref = m_rm_table.to_refine();
        unsigned start = random() % rm_ref.size();
        unsigned i = start;
        do {
            const rooted_mon& rm = m_rm_table.vec()[rm_ref[i]];
            order_lemma_on_monomial(rm);
            if (++i == rm_ref.size()) {
                i = 0;
            }
        } while(i != start && !done());
    }

    std::vector<rational> get_sorted_key(const rooted_mon& rm) {
        std::vector<rational> r;
        for (unsigned j : rm.vars()) {
            r.push_back(abs(vvr(j)));
        }
        std::sort(r.begin(), r.end());
        return r;
    }

    void print_monotone_array(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted,
                              std::ostream& out) const {
        out << "Monotone array :\n";
        for (const auto & t : lex_sorted ){
            out << "(";
            print_vector(t.first, out);
            out << "), rm[" << t.second << "]" << std::endl;
        }
        out <<  "}";
    }
    
    // Returns rooted monomials by arity
    std::unordered_map<unsigned, unsigned_vector> get_rm_by_arity() {
        std::unordered_map<unsigned, unsigned_vector> m;
        for (unsigned i = 0; i < m_rm_table.vec().size(); i++ ) {
            unsigned arity = m_rm_table.vec()[i].vars().size();
            auto it = m.find(arity);
            if (it == m.end()) {
                it = m.insert(it, std::make_pair(arity, unsigned_vector()));
            }
            it->second.push_back(i);
        }
        return m;
    }

    
    bool uniform_le(const std::vector<rational>& a,
                    const std::vector<rational>& b,
                    unsigned & strict_i) const {
        SASSERT(a.size() == b.size());
        strict_i = -1;
        bool z_b = false;
        
        for (unsigned i = 0; i < a.size(); i++) {
            if (a[i] > b[i]){
                return false;
            }
            
            SASSERT(!a[i].is_neg());
            if (a[i] < b[i]){
                strict_i = i;
            } else if (b[i].is_zero()) {
                z_b = true;
            }
        }
        if (z_b) {strict_i = -1;}
        return true;
    }

    vector<std::pair<rational, lpvar>> get_sorted_key_with_vars(const rooted_mon& a) const {
        vector<std::pair<rational, lpvar>> r;
        for (lpvar j : a.vars()) {
            r.push_back(std::make_pair(abs(vvr(j)), j));
        }
        std::sort(r.begin(), r.end(), [](const std::pair<rational, lpvar>& a,
                                         const std::pair<rational, lpvar>& b) {
                      return
                          a.first < b.first ||
                                    (a.first == b.first &&
                                     a.second < b.second);
                  });
        return r;
    } 

    void negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict) {
        rational av = vvr(a);
        rational as = rational(rat_sign(av));
        rational bv = vvr(b);
        rational bs = rational(rat_sign(bv));
        TRACE("nla_solver", tout << "av = " << av << ", bv = " << bv << "\n";);
        SASSERT(as*av <= bs*bv);
        llc mod_s = strict? (llc::LE): (llc::LT);
        mk_ineq(as, a, mod_s); // |a| <= 0 || |a| < 0
        if (a != b) {
            mk_ineq(bs, b, mod_s); // |b| <= 0 || |b| < 0
            mk_ineq(as, a, -bs, b, llc::GT); // negate |aj| <= |bj|
        }
    }

    void negate_abs_a_lt_abs_b(lpvar a, lpvar b) {
        rational av = vvr(a);
        rational as = rational(rat_sign(av));
        rational bv = vvr(b);
        rational bs = rational(rat_sign(bv));
        TRACE("nla_solver", tout << "av = " << av << ", bv = " << bv << "\n";);
        SASSERT(as*av < bs*bv);
        mk_ineq(as, a, llc::LT); // |aj| < 0
        mk_ineq(bs, b, llc::LT); // |bj| < 0
        mk_ineq(as, a, -bs, b, llc::GE); // negate  |aj| < |bj|
    }

    void assert_abs_val_a_le_abs_var_b(
        const rooted_mon& a,
        const rooted_mon& b,
        bool strict) {
        lpvar aj = var(a);
        lpvar bj = var(b);
        rational av = vvr(aj);
        rational as = rational(rat_sign(av));
        rational bv = vvr(bj);
        rational bs = rational(rat_sign(bv));
        //        TRACE("nla_solver", tout << "rmv = " << rmv << ", jv = " << jv << "\n";);
        mk_ineq(as, aj, llc::LT); // |aj| < 0
        mk_ineq(bs, bj, llc::LT); // |bj| < 0
        mk_ineq(as, aj, -bs, bj, strict? llc::LT : llc::LE); // |aj| < |bj|
    }

    // strict version
    void generate_monl_strict(const rooted_mon& a,
                              const rooted_mon& b,
                              unsigned strict) {
        add_empty_lemma();
        auto akey = get_sorted_key_with_vars(a);
        auto bkey = get_sorted_key_with_vars(b);
        SASSERT(akey.size() == bkey.size());
        for (unsigned i = 0; i < akey.size(); i++) {
            if (i != strict) {
                negate_abs_a_le_abs_b(akey[i].second, bkey[i].second, true);
            } else {
                mk_ineq(b[i], llc::EQ);
                negate_abs_a_lt_abs_b(akey[i].second, bkey[i].second);
            }
        }
        assert_abs_val_a_le_abs_var_b(a, b, true);
        explain(a, current_expl());
        explain(b, current_expl());
        TRACE("nla_solver", print_lemma(tout););
    }

    // not a strict version
    void generate_monl(const rooted_mon& a,
                       const rooted_mon& b) {
        TRACE("nla_solver", tout <<
              "a = "; print_rooted_monomial_with_vars(a, tout) << "\n:";
              tout << "b = "; print_rooted_monomial_with_vars(a, tout) << "\n:";);
        add_empty_lemma();
        auto akey = get_sorted_key_with_vars(a);
        auto bkey = get_sorted_key_with_vars(b);
        SASSERT(akey.size() == bkey.size());
        for (unsigned i = 0; i < akey.size(); i++) {
            negate_abs_a_le_abs_b(akey[i].second, bkey[i].second, false);
        }
        assert_abs_val_a_le_abs_var_b(a, b, false);
        explain(a, current_expl());
        explain(b, current_expl());
        TRACE("nla_solver", print_lemma(tout););
    }
    
    bool monotonicity_lemma_on_lex_sorted_rm_upper(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm) {
        const rational v = abs(vvr(rm));
        const auto& key = lex_sorted[i].first;
        TRACE("nla_solver", tout << "rm = ";
              print_rooted_monomial_with_vars(rm, tout); tout << "i = " << i << std::endl;);
        for (unsigned k = i + 1; k < lex_sorted.size(); k++) {
            const auto& p = lex_sorted[k];
            const rooted_mon& rmk = m_rm_table.vec()[p.second];
            const rational vk = abs(vvr(rmk));
            TRACE("nla_solver", tout << "rmk = ";
                  print_rooted_monomial_with_vars(rmk, tout);
                  tout << "\n";
                  tout << "vk = " << vk << std::endl;);
            if (vk > v) continue;
            unsigned strict;
            if (uniform_le(key, p.first, strict)) {
                if (static_cast<int>(strict) != -1 && !has_zero(key)) {
                    generate_monl_strict(rm, rmk, strict);
                    return true;
                } else {
                    if (vk < v) {
                        generate_monl(rm, rmk);
                        return true;
                    }
                }
            }
            
        }
        return false;
    }

    bool monotonicity_lemma_on_lex_sorted_rm_lower(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm) {
        const rational v = abs(vvr(rm));
        const auto& key = lex_sorted[i].first;
        TRACE("nla_solver", tout << "rm = ";
              print_rooted_monomial_with_vars(rm, tout); tout << "i = " << i << std::endl;);
        
        for (unsigned k = i; k-- > 0;) {
            const auto& p = lex_sorted[k];
            const rooted_mon& rmk = m_rm_table.vec()[p.second];
            const rational vk = abs(vvr(rmk));
            TRACE("nla_solver", tout << "rmk = ";
                  print_rooted_monomial_with_vars(rmk, tout);
                  tout << "\n";
                  tout << "vk = " << vk << std::endl;);
            if (vk < v) continue;
            unsigned strict;
            if (uniform_le(p.first, key, strict)) {
                TRACE("nla_solver", tout << "strict = " << strict << std::endl;);
                if (static_cast<int>(strict) != -1) {
                    generate_monl_strict(rmk, rm, strict);
                    return true;
                } else {
                    SASSERT(key == p.first); 
                    if (vk < v) {
                        generate_monl(rmk, rm);
                        return true;
                    }
                }
            }
            
        }
        return false;
    }

    bool monotonicity_lemma_on_lex_sorted_rm(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted, unsigned i, const rooted_mon& rm) {
        return monotonicity_lemma_on_lex_sorted_rm_upper(lex_sorted, i, rm)
            || monotonicity_lemma_on_lex_sorted_rm_lower(lex_sorted, i, rm);
    }

    bool rm_check(const rooted_mon& rm) const {
        return check_monomial(m_monomials[rm.orig_index()]);
    }
    
    bool monotonicity_lemma_on_lex_sorted(const vector<std::pair<std::vector<rational>, unsigned>>& lex_sorted) {
        for (unsigned i = 0; i < lex_sorted.size(); i++) {
            unsigned rmi = lex_sorted[i].second;
            const rooted_mon& rm = m_rm_table.vec()[rmi];
            TRACE("nla_solver", print_rooted_monomial(rm, tout); tout << "\n, rm_check = " << rm_check(rm); tout << std::endl;); 
            if ((!rm_check(rm)) && monotonicity_lemma_on_lex_sorted_rm(lex_sorted, i, rm))
                return true;
        }
        return false;
    }
    
    bool monotonicity_lemma_on_rms_of_same_arity(const unsigned_vector& rms) { 
        vector<std::pair<std::vector<rational>, unsigned>> lex_sorted;
        for (unsigned i : rms) {
            lex_sorted.push_back(std::make_pair(get_sorted_key(m_rm_table.vec()[i]), i));
        }
        std::sort(lex_sorted.begin(), lex_sorted.end(),
                  [](const std::pair<std::vector<rational>, unsigned> &a,
                     const std::pair<std::vector<rational>, unsigned> &b) {
                      return a.first < b.first;
                  });
        TRACE("nla_solver", print_monotone_array(lex_sorted, tout););
        return monotonicity_lemma_on_lex_sorted(lex_sorted);
    }
    
    void monotonicity_lemma() {
        unsigned i = random()%m_rm_table.m_to_refine.size();
        unsigned ii = i;
        do {
            unsigned rm_i = m_rm_table.m_to_refine[i];
            monotonicity_lemma(m_rm_table.vec()[rm_i].orig_index());
            TRACE("nla_solver", print_lemma(tout); );
            if (done()) return;
            i++;
            if (i == m_rm_table.m_to_refine.size())
                i = 0;
        } while (i != ii);
    }

    void monotonicity_lemma(unsigned i_mon) {
        const monomial & m = m_monomials[i_mon];
        SASSERT(!check_monomial(m));
        if (mon_has_zero(m))
            return;
        const rational prod_val = abs(product_value(m));
        const rational m_val = abs(vvr(m));
        if (m_val < prod_val)
            monotonicity_lemma_lt(m, prod_val);
        else if (m_val > prod_val)
            monotonicity_lemma_gt(m, prod_val);
    }

    void monotonicity_lemma_gt(const monomial& m, const rational& prod_val) {
        // the abs of the monomial is too large
        SASSERT(prod_val.is_pos());
        add_empty_lemma();
        for (lpvar j : m) {
            auto s = rational(rat_sign(vvr(j)));
            mk_ineq(s, j, llc::LT);
            mk_ineq(s, j, llc::GT, abs(vvr(j)));
        }
        lpvar m_j = m.var();
        auto s = rational(rat_sign(vvr(m_j)));
        mk_ineq(s, m_j, llc::LT);
        mk_ineq(s, m_j, llc::LE, prod_val);
        TRACE("nla_solver", print_lemma(tout););
    }

    void monotonicity_lemma_lt(const monomial& m, const rational& prod_val) {
        // the abs of the monomial is too small
        SASSERT(prod_val.is_pos());
        add_empty_lemma();
        for (lpvar j : m) {
            auto s = rational(rat_sign(vvr(j)));
            mk_ineq(s, j, llc::LT);
            mk_ineq(s, j, llc::LT, abs(vvr(j)));
        }
        lpvar m_j = m.var();
        auto s = rational(rat_sign(vvr(m_j)));
        mk_ineq(s, m_j, llc::LT);
        mk_ineq(s, m_j, llc::GE, prod_val);
        TRACE("nla_solver", print_lemma(tout););
    }
    
    bool find_bfc_on_monomial(const rooted_mon& rm, bfc & bf) {
        for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
            if (factorization.size() == 2) {
                lpvar a = var(factorization[0]);
                lpvar b = var(factorization[1]);
                if (vvr(rm) != vvr(a) * vvr(b)) {
                    
                    bf = bfc(a, b);
                    return true;
                }
            }
        }
        return false;
    }
    
    bool find_bfc_to_refine(bfc& bf, lpvar &j, rational& sign, const rooted_mon*& rm_found){
        for (unsigned i: m_rm_table.to_refine()) {
            const auto& rm = m_rm_table.vec()[i]; 
            SASSERT (!check_monomial(m_monomials[rm.orig_index()]));
            rm_found = &rm;
            if (find_bfc_on_monomial(rm, bf)) {
                j = m_monomials[rm.orig_index()].var();
                sign = rm.orig_sign();
                TRACE("nla_solver", tout << "found bf";
                      tout << ":rm:"; print_rooted_monomial(rm, tout) << "\n";
                      print_bfc(bf, tout);
                      tout << ", product = " << vvr(rm) << ", but should be =" << vvr(bf.m_x)*vvr(bf.m_y);
                      tout << ", j == "; print_var(j, tout) << "\n";);
                return true;
            } 
        }
        return false;
    }

    void generate_simple_sign_lemma(const rational& sign, const monomial& m) {
        SASSERT(sign == rat_sign(product_value(m)));
        for (lpvar j : m) {
            if (vvr(j).is_pos()) {
                mk_ineq(j, llc::LE);
            } else {
                SASSERT(vvr(j).is_neg());
                mk_ineq(j, llc::GE);
            }
        }
        mk_ineq(m.var(), (sign.is_pos()? llc::GT : llc ::LT));
        TRACE("nla_solver", print_lemma(tout););
    }

    bool generate_simple_tangent_lemma(const rooted_mon* rm) {
        TRACE("nla_solver", tout << "rm:"; print_rooted_monomial_with_vars(*rm, tout) << std::endl; tout << "ls = " << m_lemma_vec->size(););
        add_empty_lemma();
        unsigned i_mon = rm->orig_index();
        const monomial & m = m_monomials[i_mon];
        const rational v = product_value(m);
        const rational& mv = vvr(m);
        SASSERT(mv != v);
        SASSERT(!mv.is_zero() && !v.is_zero());
        rational sign = rational(rat_sign(mv));
        if (sign != rat_sign(v)) {
            generate_simple_sign_lemma(-sign, m);
            return true;
        }
        bool gt = abs(mv) > abs(v);
        if (gt) {
            for (lpvar j : m) {
                const rational & jv = vvr(j);
                rational js = rational(rat_sign(jv));
                mk_ineq(js, j, llc::LT);
                mk_ineq(js, j, llc::GT, jv);
            }
            mk_ineq(sign, i_mon, llc::LT);
            mk_ineq(sign, i_mon, llc::LE, v);
        } else {
            for (lpvar j : m) {
                const rational & jv = vvr(j);
                rational js = rational(rat_sign(jv));
                mk_ineq(js, j, llc::LT);
                mk_ineq(js, j, llc::LT, jv);
            }
            mk_ineq(sign, m.var(), llc::LT);
            mk_ineq(sign, m.var(), llc::GE, v);
        }
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }
    
    bool tangent_lemma() {
        bfc bf;
        lpvar j;
        rational sign;
        const rooted_mon* rm = nullptr;
        
        if (!find_bfc_to_refine(bf, j, sign, rm)) {
            if (rm != nullptr)
                return generate_simple_tangent_lemma(rm);
            TRACE("nla_solver", tout << "cannot find a bfc to refine\n"; );
            return false;
        }
        tangent_lemma_bf(bf, j, sign, *rm);
        return true;
    }

    void generate_explanations_of_tang_lemma(const rooted_mon& rm, const bfc& bf, lp::explanation& exp) {
        // here we repeat the same explanation for each lemma
        explain(rm, exp);
        explain(bf.m_x, exp);
        explain(bf.m_y, exp);
    }
    
    void tangent_lemma_bf(const bfc& bf, lpvar j, const rational& sign, const rooted_mon& rm){
        point a, b;
        point xy (vvr(bf.m_x), vvr(bf.m_y));
        rational correct_mult_val =  xy.x * xy.y;
        rational val = vvr(j) * sign;
        bool below = val < correct_mult_val;
        TRACE("nla_solver", tout << "below = " << below << std::endl;);
        get_tang_points(a, b, below, val, xy);
        TRACE("nla_solver", tout << "sign = " << sign << ", tang domain = "; print_tangent_domain(a, b, tout); tout << std::endl;);
        lp::explanation expl;
        unsigned lemmas_start = m_lemma_vec->size();
        generate_explanations_of_tang_lemma(rm, bf, expl);
        generate_two_tang_lines(bf, xy, sign, j);
        generate_tang_plane(a.x, a.y, bf.m_x, bf.m_y, below, j, sign);
        generate_tang_plane(b.x, b.y, bf.m_x, bf.m_y, below, j, sign);
        for (unsigned i = lemmas_start; i < m_lemma_vec->size(); i++) {
            auto &l = (*m_lemma_vec)[i];
            l.expl().add(expl);
            TRACE("nla_solver",
                  print_ineqs(l, tout);
                  print_explanation(l.expl(), tout););
        }
    }

    void add_empty_lemma() {
        m_lemma_vec->push_back(lemma());
    }
    
    void generate_tang_plane(const rational & a, const rational& b, lpvar jx, lpvar jy, bool below, lpvar j, const rational& j_sign) {
        add_empty_lemma();
        negate_relation(jx, a);
        negate_relation(jy, b);
        // If "below" holds then ay + bx - ab < xy, otherwise ay + bx - ab > xy,
        // j_sign*vvr(j) stands for xy. So, finally we have ay + bx - j_sign*j < ab ( or > )
        lp::lar_term t;
        t.add_coeff_var(a, jy);
        t.add_coeff_var(b, jx);
        t.add_coeff_var( -j_sign, j);
        mk_ineq(t, below? llc::LT : llc::GT, a*b);
        TRACE("nla_solver", print_lemma(tout););
    }  

    void negate_relation(unsigned j, const rational& a) {
        SASSERT(vvr(j) != a);
        if (vvr(j) < a) {
            mk_ineq(j, llc::GE, a);
        }
        else {
            mk_ineq(j, llc::LE, a);
        }
    }
    
    void generate_two_tang_lines(const bfc & bf, const point& xy, const rational& sign, lpvar j) {
        add_empty_lemma();
        mk_ineq(bf.m_x, llc::NE, xy.x);
        mk_ineq(sign, j, - xy.x, bf.m_y, llc::EQ);
        TRACE("nla_solver", print_lemma(tout););
        
        add_empty_lemma();
        mk_ineq(bf.m_y, llc::NE, xy.y);
        mk_ineq(sign, j, - xy.y, bf.m_x, llc::EQ);
        TRACE("nla_solver", print_lemma(tout););
    }
    // Get two planes tangent to surface z = xy, one at point a,  and another at point b.
    // One can show that these planes still create a cut.
    void get_initial_tang_points(point &a, point &b, const point& xy,
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

    void push_tang_point(point &a, const point& xy, bool below, const rational& correct_val, const rational& val) const {
        SASSERT(correct_val ==  xy.x * xy.y);
        int steps = 10;
        point del = a - xy;
        while (steps--) {
            del *= rational(2);
            point na = xy + del;
            TRACE("nla_solver", tout << "del = "; print_point(del, tout); tout << std::endl;);
            if (!plane_is_correct_cut(na, xy, correct_val, val, below)) {
                TRACE("nla_solver", tout << "exit";tout << std::endl;);
                return;
            }
            a = na;
        }
    }
    
    void push_tang_points(point &a, point &b, const point& xy, bool below, const rational& correct_val, const rational& val) const {
        push_tang_point(a, xy, below, correct_val, val);
        push_tang_point(b, xy, below, correct_val, val);
    }

    rational tang_plane(const point& a, const point& x) const {
        return  a.x * x.y + a.y * x.x - a.x * a.y;
    }

    bool plane_is_correct_cut(const point& plane,
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
    void get_tang_points(point &a, point &b, bool below, const rational& val,
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

    bool conflict_found() const {
        for (const auto & l : * m_lemma_vec) {
            if (l.is_conflict())
                return true;
        }
        return false;
    }

    bool done() const {
        return m_lemma_vec->size() >= 10 || conflict_found();
    }
        
    lbool inner_check(bool derived) {
        for (int search_level = 0; search_level < 3 && !done(); search_level++) {
            TRACE("nla_solver", tout << "derived = " << derived << ", search_level = " << search_level << "\n";);
            if (search_level == 0) {
                basic_lemma(derived);
                if (!m_lemma_vec->empty())
                    return l_false;
            }
            if (derived) continue;
            if (search_level == 1) {
                order_lemma();
            } else { // search_level == 2
                monotonicity_lemma();
                tangent_lemma();
            }
        }
        return m_lemma_vec->empty()? l_undef : l_false;
    }
    
    lbool check(vector<lemma>& l_vec) {
        settings().st().m_nla_calls++;
        TRACE("nla_solver", tout << "calls = " << settings().st().m_nla_calls << "\n";);
        m_lemma_vec =  &l_vec;
        if (!(m_lar_solver.get_status() == lp::lp_status::OPTIMAL || m_lar_solver.get_status() == lp::lp_status::FEASIBLE )) {
            TRACE("nla_solver", tout << "unknown because of the m_lar_solver.m_status = " << lp_status_to_string(m_lar_solver.get_status()) << "\n";);
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
        SASSERT(ret != l_false || no_lemmas_hold());
        return ret;
    }

    bool no_lemmas_hold() const {
        for (auto & l : * m_lemma_vec) {
            if (an_ineq_holds(l))
                return false;
        }
        return true;
    }
    
    void test_factorization(unsigned mon_index, unsigned number_of_factorizations) {
        vector<ineq> lemma;

        unsigned_vector vars = m_monomials[mon_index].vars();
        
        factorization_factory_imp fc(vars, // 0 is the index of "abcde"
                                     *this);
     
        std::cout << "factorizations = of "; print_monomial(m_monomials[mon_index], std::cout) << "\n";
        unsigned found_factorizations = 0;
        for (auto f : fc) {
            if (f.is_empty()) continue;
            found_factorizations ++;
            print_factorization(f, std::cout);
            std::cout << std::endl;
        }
        SASSERT(found_factorizations == number_of_factorizations);
    }
    
    lbool test_check(
        vector<lemma>& l)
    {
        m_lar_solver.set_status(lp::lp_status::OPTIMAL);
        return check(l);
    }
}; // end of imp

// returns the monomial index
unsigned solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    return m_imp->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(vector<lemma>& l) {
    return m_imp->check(l);
}

void solver::push(){
    m_imp->push();
}

void solver::pop(unsigned n) {
    m_imp->pop(n);
}
        
solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p);
}

solver::~solver() {
    dealloc(m_imp);
}

void create_abcde(solver & nla,
                  unsigned lp_a,
                  unsigned lp_b,
                  unsigned lp_c,
                  unsigned lp_d,
                  unsigned lp_e,
                  unsigned lp_abcde,
                  unsigned lp_ac,
                  unsigned lp_bde,
                  unsigned lp_acd,
                  unsigned lp_be) {
    // create monomial abcde
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monomial(lp_abcde, vec.size(), vec.begin());

    // create monomial ac
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    nla.add_monomial(lp_ac, vec.size(), vec.begin());

    // create monomial bde
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);
    nla.add_monomial(lp_bde, vec.size(), vec.begin());

    // create monomial acd
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_acd, vec.size(), vec.begin());

    // create monomial be
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_e);
    nla.add_monomial(lp_be, vec.size(), vec.begin());
}

void solver::test_factorization() {
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    lpvar lp_be = s.add_named_var(be, true, "be");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    nla.m_imp->register_monomials_in_tables();
    nla.m_imp->print_monomials(std::cout);
    nla.m_imp->test_factorization(1, // 0 is the index of monomial abcde
                                  1); // 3 is the number of expected factorizations
    nla.m_imp->test_factorization(0, // 0 is the index of monomial abcde
                                  3); // 3 is the number of expected factorizations

    
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial() {
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0\n";
    enable_trace("nla_solver");
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_bde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_b);v.push_back(lp_c);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_abcde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_c);
    nla.add_monomial(lp_ac, v.size(), v.begin());
     
    vector<lemma> lv;

    // set abcde = ac * bde
    // ac = 1 then abcde = bde, but we have abcde < bde
    s.set_column_value(lp_a, rational(4));
    s.set_column_value(lp_b, rational(4));
    s.set_column_value(lp_c, rational(4));
    s.set_column_value(lp_d, rational(4));
    s.set_column_value(lp_e, rational(4));
    s.set_column_value(lp_abcde, rational(15));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(16));

    
    SASSERT(nla.m_imp->test_check(lv) == l_false);
    
    nla.m_imp->print_lemma(std::cout);

    ineq i0(llc::NE, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_ac);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_bde);
    i1.m_term.add_coeff_var(-rational(1), lp_abcde);
    ineq i2(llc::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_var(lp_abcde);
    i2.m_term.add_coeff_var(-rational(1), lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    for (const auto& k : lv[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } 
    }

    SASSERT(found0 && (found1 || found2));

    
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1\n";
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_bde = s.add_var(bde, true);
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monomial(lp_bde, v.size(), v.begin());

    vector<lemma> lemma;

    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_bde, rational(3));

    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    SASSERT(lemma[0].size() == 4);
    nla.m_imp->print_lemma(std::cout);

    ineq i0(llc::NE, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_b);
    ineq i1(llc::NE, lp::lar_term(), rational(1));
    i1.m_term.add_var(lp_d);
    ineq i2(llc::NE, lp::lar_term(), rational(1));
    i2.m_term.add_var(lp_e);
    ineq i3(llc::EQ, lp::lar_term(), rational(1));
    i3.m_term.add_var(lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    bool found3 = false;
    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } else if (k == i3) {
            found3 = true;
        }

    }

    SASSERT(found0 && found1 && found2 && found3);

}

void solver::test_basic_lemma_for_mon_zero_from_factors_to_monomial() {
    std::cout << "test_basic_lemma_for_mon_zero_from_factors_to_monomial\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    lpvar lp_be = s.add_named_var(be, true, "be");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<lemma> lemma;

    // set vars
    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(0));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_abcde, rational(0));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(0));
    s.set_column_value(lp_acd, rational(1));
    s.set_column_value(lp_be, rational(1));

    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    nla.m_imp->print_lemma(std::cout);
    SASSERT(lemma.size() == 1 && lemma[0].size() == 2);
    ineq i0(llc::NE, lp::lar_term(), rational(0));
    i0.m_term.add_var(lp_b);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_be);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void solver::test_basic_lemma_for_mon_zero_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_zero_from_monomial_to_factors\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, c = 2, d = 3, acd = 8;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);

    // create monomial acd
    unsigned_vector vec;
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_acd, vec.size(), vec.begin());
    
    vector<lemma> lemma;
    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_acd, rational(0));

    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    
    nla.m_imp->print_lemma(std::cout);

    ineq i0(llc::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_var(lp_a);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_c);
    ineq i2(llc::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_var(lp_d);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2){
            found2 = true;
        }
    }

    SASSERT(found0 && found1 && found2);
    
}

void solver::test_basic_lemma_for_mon_neutral_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_monomial_to_factors\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    lpvar lp_be = s.add_named_var(be, true, "be");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<lemma> lemma;

    // set all vars to 1
    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_abcde, rational(1));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(1));
    s.set_column_value(lp_acd, rational(1));
    s.set_column_value(lp_be, rational(1));

    // set bde to 2, b to minus 2
    s.set_column_value(lp_bde, rational(2));
    s.set_column_value(lp_b, - rational(2));
    // we have bde = -b, therefore d = +-1 and e = +-1
    s.set_column_value(lp_d,  rational(3));
    SASSERT(nla.m_imp->test_check(lemma) == l_false);

    
    nla.m_imp->print_lemma(std::cout);
    ineq i0(llc::EQ, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_d);
    ineq i1(llc::EQ, lp::lar_term(), -rational(1));
    i1.m_term.add_var(lp_d);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void solver::test_basic_sign_lemma() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7, acd = 8;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial bde
    vector<unsigned> vec;

    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monomial(lp_bde, vec.size(), vec.begin());
    vec.clear();

    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);

    nla.add_monomial(lp_acd, vec.size(), vec.begin());

    // set the values of the factors so it should be bde = -acd according to the model
    
    // b = -a
    s.set_column_value(lp_a, rational(7));
    s.set_column_value(lp_b, rational(-7));
    
    // e - c = 0
    s.set_column_value(lp_e, rational(4));
    s.set_column_value(lp_c, rational(4));

    s.set_column_value(lp_d, rational(6));

    //    make bde != -acd according to the model
    s.set_column_value(lp_bde, lp::impq(rational(5)));
    s.set_column_value(lp_acd, lp::impq(rational(3)));
   
    vector<lemma> lemma;
    SASSERT(nla.m_imp->test_check(lemma) == l_false);

    lp::lar_term t;
    t.add_var(lp_bde);
    t.add_var(lp_acd);
    ineq q(llc::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout);
    SASSERT(q == lemma[0].ineqs().back());
    ineq i0(llc::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_var(lp_bde);
    i0.m_term.add_var(lp_acd);
    bool found = false;
    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found = true;
        } 
    }

    SASSERT(found);
}

void solver::test_order_lemma_params(bool var_equiv, int sign) {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, abef = 13, cdij = 16, ij = 17,
        k = 18;
    
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_f = s.add_named_var(f, true, "f");
    lpvar lp_i = s.add_named_var(i, true, "i");
    lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_k = s.add_named_var(k, true, "k");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_cd = s.add_named_var(cd, true, "cd");
    lpvar lp_ef = s.add_named_var(ef, true, "ef");
    lpvar lp_ij = s.add_named_var(ij, true, "ij");
    lpvar lp_abef = s.add_named_var(abef, true, "abef");
    lpvar lp_cdij = s.add_named_var(cdij, true, "cdij");

    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s.set_column_value(j, rational(j + 2));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monomial(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    int mon_cd = nla.add_monomial(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    int mon_ef = nla.add_monomial(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    if (var_equiv)
        vec.push_back(lp_k);
    else
        vec.push_back(lp_j);
    int mon_ij = nla.add_monomial(lp_ij, vec.size(), vec.begin());

    if (var_equiv) { // make k equivalent to j
        lp::lar_term t;
        t.add_var(lp_k);
        t.add_coeff_var(-rational(1), lp_j);
        lpvar kj = s.add_term(t.coeffs_as_vector(), -1);
        s.add_var_bound(kj, llc::LE, rational(0));
        s.add_var_bound(kj, llc::GE, rational(0));
    }
    
    //create monomial (ab)(ef) 
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_f);
    nla.add_monomial(lp_abef, vec.size(), vec.begin());

    //create monomial (cd)(ij)
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    auto mon_cdij = nla.add_monomial(lp_cdij, vec.size(), vec.begin());

    // set i == e
    s.set_column_value(lp_e, s.get_column_value(lp_i));
    // set f == sign*j
    s.set_column_value(lp_f, rational(sign) * s.get_column_value(lp_j));
    if (var_equiv) {
        s.set_column_value(lp_k, s.get_column_value(lp_j));
    }
    // set the values of ab, ef, cd, and ij correctly
    s.set_column_value(lp_ab, nla.m_imp->mon_value_by_vars(mon_ab));
    s.set_column_value(lp_ef, nla.m_imp->mon_value_by_vars(mon_ef));
    s.set_column_value(lp_cd, nla.m_imp->mon_value_by_vars(mon_cd));
    s.set_column_value(lp_ij, nla.m_imp->mon_value_by_vars(mon_ij));
   
    // set abef = cdij, while it has to be abef < cdij
    if (sign > 0) {
        SASSERT(s.get_column_value(lp_ab) < s.get_column_value(lp_cd));
        // we have ab < cd

        // we need to have ab*ef < cd*ij, so let us make ab*ef > cd*ij
        s.set_column_value(lp_cdij, nla.m_imp->mon_value_by_vars(mon_cdij));
        s.set_column_value(lp_abef, nla.m_imp->mon_value_by_vars(mon_cdij)
                           + rational(1));
        
    }
    else {
        SASSERT(-s.get_column_value(lp_ab) < s.get_column_value(lp_cd));
        // we need to have abef < cdij, so let us make abef < cdij
        s.set_column_value(lp_cdij, nla.m_imp->mon_value_by_vars(mon_cdij));
        s.set_column_value(lp_abef, nla.m_imp->mon_value_by_vars(mon_cdij)
                           + rational(1));
    }
    vector<lemma> lemma;

    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    // lp::lar_term t;
    // t.add_coeff_var(lp_bde);
    // t.add_coeff_var(lp_acd);
    // ineq q(llc::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout);
    // SASSERT(q == lemma.back());
    // ineq i0(llc::EQ, lp::lar_term(), rational(0));
    // i0.m_term.add_coeff_var(lp_bde);
    // i0.m_term.add_coeff_var(rational(1), lp_acd);
    // bool found = false;
    // for (const auto& k : lemma){
    //     if (k == i0) {
    //         found = true;
    //     } 
    // }

    // SASSERT(found);
}

void solver::test_monotone_lemma() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, ij = 17;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_f = s.add_named_var(f, true, "f");
    lpvar lp_i = s.add_named_var(i, true, "i");
    lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_cd = s.add_named_var(cd, true, "cd");
    lpvar lp_ef = s.add_named_var(ef, true, "ef");
    lpvar lp_ij = s.add_named_var(ij, true, "ij");
    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s.set_column_value(j, rational((j + 2)*(j + 2)));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monomial(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    int mon_cd = nla.add_monomial(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    nla.add_monomial(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    int mon_ij = nla.add_monomial(lp_ij, vec.size(), vec.begin());

    // set e == i + 1
    s.set_column_value(lp_e, s.get_column_value(lp_i) + rational(1));
    // set f == j + 1
    s.set_column_value(lp_f, s.get_column_value(lp_j) + rational(1));
    // set the values of ab, ef, cd, and ij correctly
    
    s.set_column_value(lp_ab, nla.m_imp->mon_value_by_vars(mon_ab));
    s.set_column_value(lp_cd, nla.m_imp->mon_value_by_vars(mon_cd));
    s.set_column_value(lp_ij, nla.m_imp->mon_value_by_vars(mon_ij));
   
    // set ef = ij while it has to be ef > ij
    s.set_column_value(lp_ef, s.get_column_value(lp_ij));

    vector<lemma> lemma;
    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    nla.m_imp->print_lemma(std::cout);
}

void solver::test_tangent_lemma_reg() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, ab = 10;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    //    lpvar lp_c = s.add_named_var(c, true, "c");
    //    lpvar lp_d = s.add_named_var(d, true, "d");
    // lpvar lp_e = s.add_named_var(e, true, "e");
    // lpvar lp_f = s.add_named_var(f, true, "f");
    // lpvar lp_i = s.add_named_var(i, true, "i");
    // lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    int sign = 1;
    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        sign *= -1;
        s.set_column_value(j, sign * rational((j + 2) * (j + 2)));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monomial(lp_ab, vec.size(), vec.begin());
    
    s.set_column_value(lp_ab, nla.m_imp->mon_value_by_vars(mon_ab) + rational(10)); // greater by ten than the correct value
    vector<lemma> lemma;
    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    nla.m_imp->print_lemma(std::cout);
}

void solver::test_tangent_lemma_equiv() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, k = 2, ab = 10;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_k = s.add_named_var(k, true, "k");
    lpvar lp_b = s.add_named_var(b, true, "b");
    //    lpvar lp_c = s.add_named_var(c, true, "c");
    //    lpvar lp_d = s.add_named_var(d, true, "d");
    // lpvar lp_e = s.add_named_var(e, true, "e");
    // lpvar lp_f = s.add_named_var(f, true, "f");
    // lpvar lp_i = s.add_named_var(i, true, "i");
    // lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    int sign = 1;
    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        sign *= -1;
        s.set_column_value(j, sign * rational((j + 2) * (j + 2)));
    }

    // make k == -a
    lp::lar_term t;
    t.add_var(lp_k);
    t.add_var(lp_a);
    lpvar kj = s.add_term(t.coeffs_as_vector(), -1);
    s.add_var_bound(kj, llc::LE, rational(0)); 
    s.add_var_bound(kj, llc::GE, rational(0));
    s.set_column_value(lp_a, - s.get_column_value(lp_k));
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monomial(lp_ab, vec.size(), vec.begin());
    
    s.set_column_value(lp_ab, nla.m_imp->mon_value_by_vars(mon_ab) + rational(10)); // greater by ten than the correct value
    vector<lemma> lemma;

    SASSERT(nla.m_imp->test_check(lemma) == l_false);
    nla.m_imp->print_lemma(std::cout);
}


void solver::test_tangent_lemma() {
    test_tangent_lemma_reg();
    test_tangent_lemma_equiv();    
}

void solver::test_order_lemma() {
    test_order_lemma_params(false,  1);
    test_order_lemma_params(false, -1);
    test_order_lemma_params(true,   1);
    test_order_lemma_params(true,  -1);
}
}
