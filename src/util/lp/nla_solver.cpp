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
#include "util/map.h"
#include "util/lp/monomial.h"
#include "util/lp/lp_utils.h"
#include "util/lp/vars_equivalence.h"
#include "util/lp/factorization.h"

namespace nla {

// returns true if a factor of b
template <typename T>
bool is_factor(const T & a, const T & b) {
    SASSERT(lp::is_non_decreasing(a) && lp::is_non_decreasing(b));
    auto i = a.begin();
    auto j = b.begin();
    
    while (true) {
        if (i == a.end()) {
            return true;
        }
        if (j == b.end()) {
            return false;
        }

        if (*i == *j) {
            i++;j++;
            continue;
        } 

        i++;
    }
}

    // b / a, where a is a factor of b and both vectors are sorted
template <typename T>
svector<unsigned> vector_div(const T & b, const T & a) {
    SASSERT(lp::is_non_decreasing(a));
    SASSERT(lp::is_non_decreasing(b));
    SASSERT(is_factor(a, b));
    svector<unsigned> r;
    auto i = a.begin();
    auto j = b.begin();
    
    while (true) {
        if (j == b.end()) {
            break;
        }
        if (i == a.end()) {
            r.push_back(*j);
            j++;
            continue;
        }

        if (*i == *j) {
            i++;j++;
            continue;
        } 

        r.push_back(*j);
        j++;
    }
    return r;
}

struct solver::imp {

    struct rooted_mon {
        svector<lpvar>   m_vars;
        index_with_sign  m_orig;
        rooted_mon(const svector<lpvar>& vars, unsigned i, const rational& sign): m_vars(vars), m_orig(i, sign) {
            SASSERT(lp::is_non_decreasing(vars));
        }
        lpvar operator[](unsigned k) const { return m_vars[k];}
        unsigned size() const { return m_vars.size(); }
        unsigned orig_index() const { return m_orig.m_i; }
        const rational& orig_sign() const { return m_orig.m_sign; }
        const svector<lpvar> & vars() const {return m_vars;}
    };

    struct rooted_mon_info {
        unsigned                 m_i; // index to m_vector_of_rooted_monomials
        vector<index_with_sign>  m_mons; // canonize_monomial(m_mons[j]) gives m_vector_of_rooted_monomials[m_i]
        rooted_mon_info(unsigned i, const index_with_sign& ind_s) : m_i(i) {
            m_mons.push_back(ind_s);
        }

        void push_back(const index_with_sign& ind_s) {
            m_mons.push_back(ind_s);
        }
    };
    
    typedef lp::lar_base_constraint lpcon;
    
   

    //fields    
    vars_equivalence                                                 m_vars_equivalence;
    vector<monomial>                                                 m_monomials;
    // maps the vector of the rooted monomial vars to the list of the indices of monomials having the same rooted monomial
    std::unordered_map<svector<lpvar>,
                       rooted_mon_info,
                       hash_svector>                                 m_rooted_monomials_map;
    vector<rooted_mon>                                               m_vector_of_rooted_monomials;

    // this field is used for the push/pop operations
    unsigned_vector                                                  m_monomials_counts;
    lp::lar_solver&                                                  m_lar_solver;
    std::unordered_map<lpvar, svector<lpvar>>                        m_monomials_containing_var;
    // for every k 
    // for each i in m_rooted_monomials_containing_var[k]
    // m_vector_of_rooted_monomials[i] contains k
    std::unordered_map<lpvar, std::unordered_set<unsigned>>          m_rooted_monomials_containing_var;

    // A map from m_vector_of_rooted_monomials to a set
    // of sets of m_vector_of_rooted_monomials,
    // such that for every i and every h in m_vector_of_rooted_monomials[i]
    // m_vector_of_rooted_monomials[i] is a proper factor of m_vector_of_rooted_monomials[h]
    std::unordered_map<unsigned, std::unordered_set<unsigned>>       m_rooted_factor_to_product;
    
    // u_map[m_monomials[i].var()] = i
    std::unordered_map<lpvar, unsigned>                              m_var_to_its_monomial;
    lp::explanation *                                                m_expl;
    lemma *                                                          m_lemma;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        :
        m_vars_equivalence([this](unsigned h){return vvr(h);}),
        m_lar_solver(s)
        // m_limit(lim),
        // m_params(p)
    {
    }


    rational vvr(lpvar j) const { return m_lar_solver.get_column_value_rational(j); }

    lp::impq vv(lpvar j) const { return m_lar_solver.get_column_value(j); }
    
    lpvar var(const rooted_mon& rm) const {return m_monomials[rm.m_orig.m_i].var(); }

    rational vvr(const rooted_mon& rm) const { return vvr(m_monomials[rm.m_orig.m_i].var()) * rm.m_orig.m_sign; }

    rational vvr(const factor& f) const { return f.is_var()? vvr(f.index()) : vvr(m_vector_of_rooted_monomials[f.index()]); }

    lpvar var(const factor& f) const {
        return f.is_var()?
            f.index() : var(m_vector_of_rooted_monomials[f.index()]);
    }

    svector<lpvar> sorted_vars(const factor& f) const {
        if (f.is_var()) {
            svector<lpvar> r; r.push_back(f.index());
            return r;
        }
        TRACE("nla_solver", tout << "nv";);
        return m_vector_of_rooted_monomials[f.index()].vars();
    }

    // the value of the factor is equal to the value of the variable multiplied
    // by the flip_sign
    rational flip_sign(const factor& f) const {
        return f.is_var()?
            rational(1) : m_vector_of_rooted_monomials[f.index()].m_orig.sign();
    }

    // the value of the rooted monomias is equal to the value of the variable multiplied
    // by the flip_sign
    rational flip_sign(const rooted_mon& m) const {
        return m.m_orig.sign();
    }

    void add(lpvar v, unsigned sz, lpvar const* vs) {
        m_var_to_its_monomial[v] = m_monomials.size();
        m_monomials.push_back(monomial(v, sz, vs));
        TRACE("nla_solver", print_monomial(m_monomials.back(), tout););
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
        m_vars_equivalence.deregister_monomial_from_abs_vals(m, i);  
        deregister_monomial_from_rooted_monomials(m, i);     
    }
     
    void pop(unsigned n) {
        TRACE("nla_solver",);
        if (n == 0) return;
        unsigned new_size = m_monomials_counts[m_monomials_counts.size() - n];
        for (unsigned i = m_monomials.size(); i-- > new_size; ){
            deregister_monomial_from_tables(m_monomials[i], i);
        }
        m_monomials.shrink(new_size);
        m_monomials_counts.shrink(m_monomials_counts.size() - n);       
    }

    // return true if the monomial value is equal to the product of the values of the factors
    bool check_monomial(const monomial& m) {
        SASSERT(m_lar_solver.get_column_value(m.var()).is_int());
        const rational & model_val = m_lar_solver.get_column_value_rational(m.var());
        rational r(1);
        for (auto j : m) {
            r *= m_lar_solver.get_column_value_rational(j);
        }
        return r == model_val;
    }
    
    /**
     * \brief <here we have two monomials, i_mon and other_m, examined for "sign" equivalence>
     */

    bool values_are_different(lpvar j, rational const& sign, lpvar k) const {
        SASSERT(sign == 1 || sign == -1);
        return sign * m_lar_solver.get_column_value(j) != m_lar_solver.get_column_value(k);
    }

    void explain(const rooted_mon& rm) {
        expl_set e;
        add_explanation_of_reducing_to_rooted_monomial_and_set_expl(rm, e);
    }
    
    void add_explanation_of_reducing_to_rooted_monomial(const monomial& m, expl_set & exp) const {
        m_vars_equivalence.add_explanation_of_reducing_to_rooted_monomial(m, exp);
    }

    void add_explanation_of_reducing_to_rooted_monomial(lpvar j, expl_set & exp) const {
        auto it = m_var_to_its_monomial.find(j);
        if (it == m_var_to_its_monomial.end())
            return; // j is not a var of a monomial
        add_explanation_of_reducing_to_rooted_monomial(it->second, exp);
    }

    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const {
        for (unsigned k = 0; k < m.size(); k++) {
            out << m_lar_solver.get_variable_name(m[k]);
            if (k + 1 < m.size()) out << "*";
        }
        return out;
    }

    std::ostream & print_factor(const factor& f, std::ostream& out) const {
        if (f.is_var()) {
            print_var(f.index(), out);
        } else {
            print_product(m_vector_of_rooted_monomials[f.index()].vars(), out);
        }
        return out;
    }

    std::ostream & print_factor_with_vars(const factor& f, std::ostream& out) const {
        if (f.is_var()) {
            print_var(f.index(), out);
        } else {
            print_product_with_vars(m_vector_of_rooted_monomials[f.index()].vars(), out);
        }
        return out;
    }

    std::ostream& print_monomial(const monomial& m, std::ostream& out) const {
        out << m_lar_solver.get_variable_name(m.var()) << " = ";
        return print_product(m.vars(), out);
    }

    std::ostream& print_monomial(unsigned i, std::ostream& out) const {
        return print_monomial(m_monomials[i], out);
    }

    std::ostream& print_monomial_with_vars(unsigned i, std::ostream& out) const {
        return print_monomial_with_vars(m_monomials[i], tout);
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
        out << m_lar_solver.get_variable_name(m.var()) << " = ";
        return print_product_with_vars(m, out);
    }

    std::ostream& print_rooted_monomial(const rooted_mon& rm, std::ostream& out) const {
        out << "vars = "; 
        print_product(rm.vars(), out);
        out << "\n orig = "; print_monomial(m_monomials[rm.orig_index()], out);
        out << ", orig sign = " << rm.orig_sign() << "\n";
        return out;
    }
    
    std::ostream& print_explanation(std::ostream& out) const {
        for (auto &p : *m_expl) {
            m_lar_solver.print_constraint(p.second, out);
        }
        return out;
    }

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(a, j);
        t.add_coeff_var(b, k);
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(rational(1), j, b, k, cmp, rs);
    }

    void mk_ineq(lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(a, j, b, k, cmp, rational::zero());
    }

    void mk_ineq(const rational& a ,lpvar j, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(a, j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, lpvar k, lp::lconstraint_kind cmp, const rational& rs) {
        mk_ineq(j, rational(1), k, cmp, rs);
    }

    void mk_ineq(lpvar j, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(j);  
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(const rational& a, lpvar j, lp::lconstraint_kind cmp, const rational& rs) {
        lp::lar_term t;
        t.add_coeff_var(a, j);  
        m_lemma->push_back(ineq(cmp, t, rs));
    }

    void mk_ineq(const rational& a, lpvar j, lp::lconstraint_kind cmp) {
        mk_ineq(a, j, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, lpvar k, lp::lconstraint_kind cmp) {
        mk_ineq(rational(1), j, rational(1), k, cmp, rational::zero());
    }

    void mk_ineq(lpvar j, lp::lconstraint_kind cmp) {
        mk_ineq(j, cmp, rational::zero());
    }
    
    // the monomials should be equal by modulo sign but this is not so the model
    void fill_explanation_and_lemma_sign(const monomial& a, const monomial & b, rational const& sign) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_explanation_of_reducing_to_rooted_monomial(a, expl);
        add_explanation_of_reducing_to_rooted_monomial(b, expl);
        m_expl->clear();
        m_expl->add(expl);
        TRACE("nla_solver",
              tout << "used constraints: ";
              for (auto &p : *m_expl)
                  m_lar_solver.print_constraint(p.second, tout); tout << "\n";
              );
        SASSERT(m_lemma->size() == 0);
        mk_ineq(rational(1), a.var(), -sign, b.var(), lp::lconstraint_kind::EQ, rational::zero());
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
    void generate_sign_lemma(const vector<rational>& abs_vals, unsigned i, unsigned k, const rational& sign) {
        SASSERT(sign == rational(1) || sign == rational(-1));
        SASSERT(m_lemma->empty());
        TRACE("nla_solver",
              tout << "mon i=" << i << " = "; print_monomial_with_vars(m_monomials[i],tout);
              tout << '\n';
              tout << "mon k=" << k << " = "; print_monomial_with_vars(m_monomials[k],tout);
              tout << '\n';
              tout << "abs_vals="; print_vector(abs_vals, tout);
              );
        std::unordered_map<rational, vector<index_with_sign>> map;
        for (const rational& v : abs_vals) {
            map[v] = vector<index_with_sign>();
        }
  
        for (unsigned j : m_monomials[i]) {
            rational v = vvr(j);
            int s;
            if (v.is_pos()) {
                s = 1;
            } else {
                s = -1;
                v = -v; 
            };
            // v = abs(vvr(j))
            auto it = map.find(v);
            SASSERT(it != map.end());
            it->second.push_back(index_with_sign(j, rational(s)));
        } 

        for (unsigned j : m_monomials[k]) {
            rational v = vvr(j);
            rational s;
            if (v.is_pos()) {
                s = rational(1);
            } else {
                s = -rational(1);
                v = -v;
            };
            // v = abs(vvr(j))
            auto it = map.find(v);
            SASSERT(it != map.end());
            index_with_sign & ins = it->second.back();
            if (j != ins.m_i) {
                s *= ins.m_sign;
                mk_ineq(j, -s, ins.m_i, lp::lconstraint_kind::NE);
            }
            it->second.pop_back();
        } 

        mk_ineq(m_monomials[i].var(), -sign, m_monomials[k].var(), lp::lconstraint_kind::EQ);        
        TRACE("nla_solver", print_lemma(tout););
    }


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
    
    bool basic_sign_lemma_on_a_bucket_of_abs_vals(const vector<rational>& abs_vals, const unsigned_vector& list){
        rational val =  vvr(m_monomials[list[0]].var());
        int sign = vars_sign(m_monomials[list[0]].vars());
        if (sign == 0) {
            return false;
        }
        
        for (unsigned i = 1; i < list.size(); i++) {
            rational rsign = rational(vars_sign(m_monomials[list[i]].vars()) * sign);
            SASSERT(!rsign.is_zero());
            rational other_val =  vvr(m_monomials[list[i]].var());
            if (val * rsign != other_val) {
                generate_sign_lemma(abs_vals, list[0], list[i], rsign);
                return true;
            }
        }
        return false;
    }
    
    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool basic_sign_lemma() {
        for (const auto & p : m_vars_equivalence.monomials_by_abs_values()){
            if (basic_sign_lemma_on_a_bucket_of_abs_vals(p.first, p.second))
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
    
    std::ostream & print_ineq(const ineq & in, std::ostream & out) const {
        m_lar_solver.print_term(in.m_term, out);
        out << " " << lp::lconstraint_kind_string(in.m_cmp) << " " << in.m_rs;
        return out;
    }

    std::ostream & print_var(lpvar j, std::ostream & out) const {
        bool is_monomial = false;
        for (const monomial & m : m_monomials) {
            if (j == m.var()) {
                is_monomial = true;
                print_monomial(m, out);
                out << " = " << vvr(j);;
                break;
            }
        }
        if (!is_monomial)
            out << m_lar_solver.get_variable_name(j) << " = " << vvr(j);
        out <<";";
        return out;
    }    

    std::ostream & print_lemma(std::ostream & out) const {
        auto &l = *m_lemma;
        out << "lemma: ";
        for (unsigned i = 0; i < l.size(); i++) {
            print_ineq(l[i], out);
            if (i + 1 < l.size()) out << " or ";
        }
        out << std::endl;
        std::unordered_set<lpvar> vars;
        for (auto & in: l) {
            for (const auto & p: in.m_term)
                vars.insert(p.var());
        }
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
                print_product(m_vector_of_rooted_monomials[f[k].index()].vars(), out);
            }
            if (k < f.size() - 1)
                out << "*";
        }
        return out;
    }
    
    struct factorization_factory_imp: factorization_factory {
        const imp&         m_imp;
        
        factorization_factory_imp(const svector<lpvar>& m_vars, const imp& s) :
            factorization_factory(m_vars),
            m_imp(s) { }
        
        bool find_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const {
            SASSERT(m_imp.vars_are_roots(vars));
            auto it = m_imp.m_rooted_monomials_map.find(vars);
            if (it == m_imp.m_rooted_monomials_map.end()) {
                return false;
            }

            i = it->second.m_mons.begin()->m_i;
            return true;
        }
    };

    
    
    // here we use the fact
    // xy = 0 -> x = 0 or y = 0
    bool basic_lemma_for_mon_zero(const rooted_mon& rm, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););
        SASSERT(vvr(rm).is_zero());
        for (auto j : f) {
            if (vvr(j).is_zero()) {
                return false;
            }
        }
        
        SASSERT(m_lemma->empty());
        
        mk_ineq(var(rm), lp::lconstraint_kind::NE);
        for (auto j : f) {
            mk_ineq(var(j), lp::lconstraint_kind::EQ);
        }

        explain(rm);
        TRACE("nla_solver", print_lemma(tout););

        return true;
    }

    void add_explanation_of_reducing_to_rooted_monomial_and_set_expl(const rooted_mon& rm, expl_set& ex) {
        add_explanation_of_reducing_to_rooted_monomial(m_monomials[rm.orig_index()], ex);
        set_expl(ex);
    }
    
    void set_expl(const expl_set & e) {
        m_expl->clear();
        for (lpci ci : e)
            m_expl->push_justification(ci);
    }

    void trace_print_monomial_and_factorization(const rooted_mon& rm, const factorization& f, std::ostream& out) const {
        out << "rooted vars: ";
        print_product(rm.m_vars, out);
        out << "\n";
        
        print_monomial(rm.orig_index(), out << "mon:  ") << "\n";
        out << "value: " << vvr(rm) << "\n";
        print_factorization(f, out << "fact: ") << "\n";
    }

    // x = 0 or y = 0 -> xy = 0
    bool basic_lemma_for_mon_non_zero(const rooted_mon& rm, const factorization& f) {
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

        mk_ineq(zero_j, lp::lconstraint_kind::NE);
        mk_ineq(var(rm), lp::lconstraint_kind::EQ);

        explain(rm);
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }

    // use the fact that
    // |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1
    bool basic_lemma_for_mon_neutral_monomial_to_factor(const rooted_mon& rm, const factorization& f) {
        TRACE("nla_solver", trace_print_monomial_and_factorization(rm, f, tout););

        lpvar mon_var = m_monomials[rm.orig_index()].var();
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
        
        SASSERT(m_lemma->empty());
        // jl + mon_var != 0
        mk_ineq(jl, mon_var, lp::lconstraint_kind::NE);   
        
        // jl - mon_var != 0
        mk_ineq(jl, -rational(1), mon_var, lp::lconstraint_kind::NE);   

        // not_one_j = 1
        mk_ineq(not_one_j, lp::lconstraint_kind::EQ,  rational(1));   
        
        // not_one_j = -1
        mk_ineq(not_one_j, lp::lconstraint_kind::EQ, -rational(1));
        explain(rm);
        TRACE("nla_solver", print_lemma(tout); );
        return true;
    }

    // use the fact
    // 1 * 1 ... * 1 * x * 1 ... * 1 = x
    bool basic_lemma_for_mon_neutral_from_factors_to_monomial(const rooted_mon& rm, const factorization& f) {
        rational sign = rm.m_orig.m_sign;
        lpvar not_one = -1;
        for (auto j : f){
            if (vvr(j) == rational(1)) {
                continue;
            }

            if (vvr(j) == -rational(1)) { 
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
       
        explain(rm);

        for (auto j : f){
            lpvar var_j = var(j);
            if (not_one == var_j) continue;
            mk_ineq(var_j, lp::lconstraint_kind::NE, j.is_var()? vvr(j) : flip_sign(j) * vvr(j) );   
        }

        if (not_one == static_cast<lpvar>(-1)) {
            mk_ineq(m_monomials[rm.orig_index()].var(), lp::lconstraint_kind::EQ, sign);
        } else {
            mk_ineq(m_monomials[rm.orig_index()].var(), -sign, not_one, lp::lconstraint_kind::EQ);
        }
        TRACE("nla_solver", print_lemma(tout););
        return true;
    }
    
    bool basic_lemma_for_mon_neutral(const rooted_mon& rm, const factorization& factorization) {
        return
            basic_lemma_for_mon_neutral_monomial_to_factor(rm, factorization) || 
            basic_lemma_for_mon_neutral_from_factors_to_monomial(rm, factorization);
        return false;
    }

    
    // use basic multiplication properties to create a lemma
    // for the given monomial
    bool basic_lemma_for_mon(const rooted_mon& rm) {
        if (vvr(rm).is_zero()) {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                if (basic_lemma_for_mon_zero(rm, factorization) ||
                    basic_lemma_for_mon_neutral(rm, factorization))
                    return true;
            }
        } else {
            for (auto factorization : factorization_factory_imp(rm.m_vars, *this)) {
                if (factorization.is_empty())
                    continue;
                if (basic_lemma_for_mon_non_zero(rm, factorization) ||
                    basic_lemma_for_mon_neutral(rm, factorization))
                    return true;
            
            }
        }
        return false;
    }

    // use basic multiplication properties to create a lemma
    bool basic_lemma() {
        if (basic_sign_lemma())
            return true;

        for (const rooted_mon& r : m_vector_of_rooted_monomials) {
            if (check_monomial(m_monomials[r.orig_index()]))
                continue;
            if (basic_lemma_for_mon(r)) {
                return true;
            }
        }
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
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monomial_vars_to_monomial_indices(i);
    }

    // we look for octagon constraints here, with a left part  +-x +- y 
    void collect_equivs() {
        const lp::lar_solver& s = m_lar_solver;

        for (unsigned i = 0; i < s.terms().size(); i++) {
            unsigned ti = i + s.terms_start_index();
            if (!s.term_is_used_as_row(ti))
                continue;
            lpvar j = s.external2local(ti);
            if (var_is_fixed_to_zero(j)) {
                TRACE("nla_solver", tout << "term = "; s.print_term(*s.terms()[i], tout););
                add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
            }
        }
    }

    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1) {
        if (t->size() != 2)
            return;
        bool seen_minus = false;
        bool seen_plus = false;
        lpvar i = -1, j;
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
        TRACE("nla_solver", tout << "adding equiv";);
        rational sign((seen_minus && seen_plus)? 1 : -1);
        m_vars_equivalence.add_equiv(i, j, sign, c0, c1);
    }

    // x is equivalent to y if x = +- y
    void init_vars_equivalence() {
        m_vars_equivalence.clear();
        collect_equivs();
        m_vars_equivalence.create_tree();
        for (lpvar j = 0; j < m_lar_solver.number_of_vars(); j++) {
            m_vars_equivalence.register_var(j, vvr(j));
        }
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

    void register_key_mono_in_rooted_monomials(monomial_coeff const& mc, unsigned i) {
        SASSERT(vars_are_roots(mc.vars()));
        SASSERT(lp::is_non_decreasing(mc.vars()));
        index_with_sign ms(i, mc.coeff());
        auto it = m_rooted_monomials_map.find(mc.vars());
        if (it == m_rooted_monomials_map.end()) {
            rooted_mon_info rmi(m_vector_of_rooted_monomials.size(), ms);
            m_rooted_monomials_map.emplace(mc.vars(), rmi);
            m_vector_of_rooted_monomials.push_back(rooted_mon(mc.vars(), i, mc.coeff()));
        } 
        else {
            it->second.push_back(ms);
        }
    }

    void register_monomial_in_tables(unsigned i) {
        m_vars_equivalence.register_monomial_in_abs_vals(i, m_monomials[i]);
        monomial_coeff mc = canonize_monomial(m_monomials[i]);
        register_key_mono_in_rooted_monomials(mc, i);        
    }

    void intersect_set(std::unordered_set<unsigned>& p, const std::unordered_set<unsigned>& w) {
        for (auto it = p.begin(); it != p.end(); ) {
            auto iit = it;
            iit ++;
            if (w.find(*it) == w.end())
                p.erase(it);
            it = iit;
        }
    }

    void reduce_set_by_checking_actual_containment(std::unordered_set<unsigned>& p,
                                                   const rooted_mon & rm ) {
        for (auto it = p.begin(); it != p.end();) {
            if (is_factor(rm.m_vars, m_vector_of_rooted_monomials[*it].m_vars)) {
                it++;
                continue;
            }
            auto iit = it;
            iit ++;
            p.erase(it);
            it = iit;
        }
    }
    
    // here i is the index of a monomial in m_vector_of_rooted_monomials
    void find_containing_rooted_monomials(unsigned i) {
        const auto & rm = m_vector_of_rooted_monomials[i];
        TRACE("nla_solver", tout << "i = " << i << ", rm = "; print_rooted_monomial(rm, tout););
       
        std::unordered_set<unsigned> p = m_rooted_monomials_containing_var[rm[0]];
        for (unsigned k = 1; k < rm.size(); k++) {
            intersect_set(p, m_rooted_monomials_containing_var[rm[k]]);
        }
        reduce_set_by_checking_actual_containment(p, rm);
        TRACE("nla_solver",
              tout << "p = " << p.size();
              for (auto j : p)
                  TRACE("nla_solver", tout << "j = " << j << ", rm = "; print_rooted_monomial(m_vector_of_rooted_monomials[j], tout););
              );

        m_rooted_factor_to_product[i] = p;
    }
    
    void fill_rooted_factor_to_product() {
        for (unsigned i = 0; i < m_vector_of_rooted_monomials.size(); i++) {
            find_containing_rooted_monomials(i);
        }
    }

    void register_monomial_containing_vars(unsigned i) {
        for (lpvar j : m_vector_of_rooted_monomials[i].vars()) {
            auto it = m_rooted_monomials_containing_var.find(j);
            if (it == m_rooted_monomials_containing_var.end()) {
                std::unordered_set<unsigned> s;
                s.insert(i);
                m_rooted_monomials_containing_var[i] = s;
            } else {
                it->second.insert(i);
            }
        }
    }
    
    void fill_rooted_monomials_containing_var() {
        for (unsigned i = 0; i < m_vector_of_rooted_monomials.size(); i++) {
            register_monomial_containing_vars(i);
        }
      
    }
    
    void register_monomials_in_tables() {
        m_vars_equivalence.clear_monomials_by_abs_vals();
        for (unsigned i = 0; i < m_monomials.size(); i++) 
            register_monomial_in_tables(i);

        fill_rooted_monomials_containing_var();
        fill_rooted_factor_to_product();
    }
    
    void init_search() {
        map_vars_to_monomials();
        init_vars_equivalence();
        register_monomials_in_tables();
        m_expl->clear();
        m_lemma->clear();
    }


    bool divide(const rooted_mon& bc, const factor& c, factor & b) const {
        svector<lpvar> c_vars = sorted_vars(c);
        TRACE("nla_solver",
              tout << "c_vars = ";
              print_product(c_vars, tout);
              tout << "\nbc_vars = ";
              print_product(bc.vars(), tout););
        if (!is_factor(c_vars, bc.vars()))
            return false;
            
        auto b_vars = vector_div(bc.vars(), c_vars);
        TRACE("nla_solver", tout << "b_vars = "; print_product(b_vars, tout););
        SASSERT(b_vars.size() > 0);
        if (b_vars.size() == 1) {
            b = factor(b_vars[0]);
            return true;
        }
        auto it = m_rooted_monomials_map.find(b_vars);
        if (it == m_rooted_monomials_map.end()) {
            return false;
        }
        b = factor(it->second.m_i, factor_type::RM);
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
            mk_ineq(i, -rational(1), j, lp::lconstraint_kind::NE);
        } else { // iv == -jv
            mk_ineq(i, j, lp::lconstraint_kind::NE);                
        }
    }
    
    void negate_factor_relation(const factor& a, const factor& b) {
        rational a_fs = flip_sign(a);
        rational b_fs = flip_sign(b);
        lp::lconstraint_kind cmp = vvr(a) < vvr(b)? lp::lconstraint_kind::GE : lp::lconstraint_kind::LE;
        mk_ineq(a_fs, var(a), - b_fs, var(b), cmp);
    }
    
    void generate_ol(const rooted_mon& ac,
                     const factor& a,
                     const factor& c,
                     const rooted_mon& bd,
                     const factor& b,
                     const factor& d,
                     lp::lconstraint_kind cmp) {
        negate_factor_equality(c, d);
        negate_factor_relation(a, b);
        mk_ineq(flip_sign(ac), var(ac), -flip_sign(bd), var(bd), cmp);
    }

    bool order_lemma_on_ac_and_bd_and_factors(const rooted_mon& ac,
                                              const factor& a,
                                              const factor& c,
                                              const rooted_mon& bd,
                                              const factor& b,
                                              const factor& d) {
        
        auto ac_m = vvr(a) * vvr(c);
        auto bd_m = vvr(b) * vvr(d);

        auto ac_v = vvr(ac);
        auto bd_v = vvr(bd);

        if (ac_m < bd_m && !(ac_v < bd_v)) {
            generate_ol(ac, a, c, bd, b, d, lp::lconstraint_kind::LT);
            return true;
        }
        else if (ac_m > bd_m && !(ac_v > bd_v)) {
            generate_ol(ac, a, c, bd, b, d, lp::lconstraint_kind::GT);
            return true;
        }

        return false;
    }
    
    // a > b && c > 0 && d = |c => ac > bd 
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
              tout << ", d  = "; print_factor(d, tout););
        SASSERT(abs(vvr(ac_f[k])) == abs(vvr(d)));
        factor b;
        if (!divide(rm_bd, d, b))
            return false;

        TRACE("nla_solver", tout << "factor b = ";
              print_factor(b, tout););

        TRACE("nla_solver", tout << "vvr(b) = " << vvr(b););

        
        return order_lemma_on_ac_and_bd_and_factors(rm_ac, ac_f[(k + 1) % 2], ac_f[k], rm_bd, b, d);
    }

    // collect all vars and rooted monomials with the same absolute
    //value as c and return them as factors 
    vector<factor> primitive_factors_with_the_same_abs_val(const factor& c) const {
        vector<factor> r;
        std::unordered_set<lpvar> found_vars;
        std::unordered_set<unsigned> found_rm;
        TRACE("nla_solver", tout << "c = "; print_factor_with_vars(c, tout););
        for (lpvar i : m_vars_equivalence.get_vars_with_the_same_abs_val(vvr(c))) {
            auto it = m_var_to_its_monomial.find(i);
            if (it == m_var_to_its_monomial.end()) {
                i = m_vars_equivalence.map_to_root(i);
                if (!contains(found_vars, i)) {
                    found_vars.insert(i);
                    r.push_back(factor(i, factor_type::VAR));
                }
            } else {
                const monomial& m = m_monomials[it->second];
                monomial_coeff mc = canonize_monomial(m);
                auto it = m_rooted_monomials_map.find(mc.vars());
                SASSERT(it != m_rooted_monomials_map.end());
                i = it->second.m_i;
                if (!contains(found_rm, i)) {
                    found_rm.insert(i);
                    r.push_back(factor(i, factor_type::RM));
                    TRACE("nla_solver", tout << "ins "; print_factor(factor(i, factor_type::RM), tout); );
                }
                
            }
        }
        return r;
    }
    
    // a > b && c > 0 => ac > bc
    // ac is a factorization of m_monomials[i_mon]
    // ac[k] plays the role of c   
    bool order_lemma_on_factor(const rooted_mon& rm, const factorization& ac, unsigned k) {
        auto c = ac[k];
        TRACE("nla_solver", tout << "k = " << k << ", c = "; print_factor(c, tout); );

        for (const factor & d : primitive_factors_with_the_same_abs_val(c)) {
            TRACE("nla_solver", tout << "d = "; print_factor(d, tout); );
            if (d.is_var()) {
                TRACE("nla_solver", tout << "var(d) = " << var(d););
                for (unsigned rm_bd : m_rooted_monomials_containing_var[d.index()]) {
                    TRACE("nla_solver", );
                    if (order_lemma_on_ac_and_bd(rm , ac, k, m_vector_of_rooted_monomials[rm_bd], d)) {
                        return true;
                    }
                }
            } else {
                TRACE("nla_solver", tout << "size = " << m_rooted_factor_to_product[d.index()].size() ;);
                for (unsigned rm_bd : m_rooted_factor_to_product[d.index()]) {
                    TRACE("nla_solver", );
                    if (order_lemma_on_ac_and_bd(rm , ac, k, m_vector_of_rooted_monomials[rm_bd], d)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    // a > b && c == d => ac > bd
    // ac is a factorization of m_monomials[i_mon]
    bool order_lemma_on_factorization(const rooted_mon& rm, const factorization& ac) {
        SASSERT(ac.size() == 2);
        TRACE("nla_solver", tout << "factorization = "; print_factorization(ac, tout););
        for (unsigned k = 0; k < ac.size(); k++) {
            const rational & v = vvr(ac[k]);
            if (v.is_zero())
                continue;

            if (order_lemma_on_factor(rm, ac, k)) { 
                return true;
            }
        }
        return false;
    }

    // a > b && c > 0 => ac > bc
    bool order_lemma_on_monomial(const rooted_mon& rm) {
        TRACE("nla_solver",
              tout << "rm = "; print_product(rm, tout);
              tout << ", orig = "; print_monomial(m_monomials[rm.orig_index()], tout);
              );
        for (auto ac : factorization_factory_imp(rm.vars(), *this)) {
            if (ac.size() != 2)
                continue;
            if (order_lemma_on_factorization(rm, ac))
                return true;
        }
        return false;
    }
    
    bool order_lemma() {
        for (const auto& rm : m_vector_of_rooted_monomials) {
            if (check_monomial(m_monomials[rm.orig_index()]))
                continue;
            if (order_lemma_on_monomial(rm)) {
                return true;
            } 
        }
        return false;
    }

    bool monotonicity_lemma_on_factorization(unsigned i_mon, const factorization& factorization) {
        return false;
    }
    
    bool monotonicity_lemma_on_monomial() {
        /*
          for (auto factorization : factorization_factory_imp(i_mon, *this)) {
          if (factorization.is_empty())
          continue;
          if (monotonicity_lemma_on_factorization(i_mon, factorization))
          return true;
          }*/
        return false;
    }
    
    bool monotonicity_lemma() {
        
        // for (unsigned i_mon : to_refine) {
        //     if (monotonicity_lemma_on_monomial(i_mon)) {
        //         return true;
        //     } 
        // }
        
        return false;
    }

    bool tangent_lemma() {
        return false;
    }
    
    lbool check(lp::explanation & exp, lemma& l) {
        TRACE("nla_solver", tout << "check of nla";);
        m_expl =   &exp;
        m_lemma =  &l;
       
        if (!(m_lar_solver.get_status() == lp::lp_status::OPTIMAL || m_lar_solver.get_status() == lp::lp_status::FEASIBLE )) {
            TRACE("nla_solver", tout << "unknown because of the m_lar_solver.m_status = " << lp_status_to_string(m_lar_solver.get_status()) << "\n";);
            return l_undef;
        }

        bool to_refine = false;
        for (unsigned i = 0; i < m_monomials.size() && !to_refine; i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine = true;
        }

        if (!to_refine) {
            return l_true;
        }

        init_search();
        for (int search_level = 0; search_level < 3; search_level++) {
            if (search_level == 0) {
                if (basic_lemma()) {
                    return l_false;
                }
            } else if (search_level == 1) {
                if (order_lemma()) {
                    return l_false;
                }
            } else { // search_level == 3
                if (monotonicity_lemma()) {
                    return l_false;
                }
                                
                if (tangent_lemma()) {
                    return l_false;
                }
            }
        }
    
        return l_undef;
    }
    
    void test_factorization(unsigned mon_index, unsigned number_of_factorizations) {
        vector<ineq> lemma;
        m_lemma = & lemma;
        lp::explanation exp;
        m_expl = & exp;
        init_search();

        factorization_factory_imp fc(m_monomials[mon_index].vars(), // 0 is the index of "abcde"
                                     *this);
     
        std::cout << "factorizations = of "; print_var(m_monomials[0].var(), std::cout) << "\n";
        unsigned found_factorizations = 0;
        for (auto f : fc) {
            if (f.is_empty()) continue;
            found_factorizations ++;
            for (auto j : f) {
                std::cout << "j = "; print_factor(j, std::cout);
            }
            std::cout << std::endl;
        }
        SASSERT(found_factorizations == number_of_factorizations);
    }
    
    lbool test_check(
        vector<ineq>& lemma,
        lp::explanation& exp )
    {
        m_lar_solver.set_status(lp::lp_status::OPTIMAL);
        m_lemma = & lemma;
        m_expl = & exp;

        return check(exp, lemma);
    }
}; // end of imp



void solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    m_imp->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(lp::explanation & ex, lemma& l) {
    return m_imp->check(ex, l);
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
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
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

    nla.m_imp->test_factorization(0, // 0 is the index of monomial abcde
                                  3); // 3 is the number of expected factorizations

    
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial() {
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
}

void solver::test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0\n";
    // enable_trace("nla_solver");
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    
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
     
    vector<ineq> lemma;
    lp::explanation exp;

    // set abcde = ac * bde
    // ac = 1, bde = 3 -> abcde = bde, but we have abcde set to 2
    s.set_column_value(lp_a, rational(4));
    s.set_column_value(lp_b, rational(4));
    s.set_column_value(lp_c, rational(4));
    s.set_column_value(lp_d, rational(4));
    s.set_column_value(lp_e, rational(4));
    s.set_column_value(lp_abcde, rational(2));
    s.set_column_value(lp_ac, rational(1));
    s.set_column_value(lp_bde, rational(3));

    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_ac);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_bde);
    i1.m_term.add_coeff_var(-rational(1), lp_abcde);
    ineq i2(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_coeff_var(lp_abcde);
    i2.m_term.add_coeff_var(-rational(1), lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    for (const auto& k : lemma){
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

    vector<ineq> lemma;
    lp::explanation exp;

    s.set_column_value(lp_a, rational(1));
    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_c, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));
    s.set_column_value(lp_bde, rational(3));

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    SASSERT(lemma.size() == 4);
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i1.m_term.add_coeff_var(lp_d);
    ineq i2(lp::lconstraint_kind::NE, lp::lar_term(), rational(1));
    i2.m_term.add_coeff_var(lp_e);
    ineq i3(lp::lconstraint_kind::EQ, lp::lar_term(), rational(1));
    i3.m_term.add_coeff_var(lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    bool found3 = false;
    for (const auto& k : lemma){
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
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
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
    vector<ineq> lemma;
    lp::explanation exp;


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

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    SASSERT(lemma.size() == 2);
    ineq i0(lp::lconstraint_kind::NE, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_be);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma){
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
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
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
    vector<ineq> lemma;
    lp::explanation exp;


    s.set_column_value(lp_b, rational(1));
    s.set_column_value(lp_d, rational(1));
    s.set_column_value(lp_e, rational(1));

    // set bde to zero
    s.set_column_value(lp_bde, rational(0));

    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");

    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_coeff_var(lp_d);
    ineq i2(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_coeff_var(lp_e);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;

    for (const auto& k : lemma){
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
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_abcde = s.add_var(abcde, true);
    lpvar lp_ac = s.add_var(ac, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    lpvar lp_be = s.add_var(be, true);
    
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
    vector<ineq> lemma;
    lp::explanation exp;

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
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);
    
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(1));
    i0.m_term.add_coeff_var(lp_b);
    ineq i1(lp::lconstraint_kind::EQ, lp::lar_term(), -rational(1));
    i1.m_term.add_coeff_var(lp_b);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void solver::test_basic_sign_lemma() {
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7, acd = 8;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_bde = s.add_var(bde, true);
    lpvar lp_acd = s.add_var(acd, true);
    
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
   
    vector<ineq> lemma;
    lp::explanation exp;
    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);

    lp::lar_term t;
    t.add_coeff_var(lp_bde);
    t.add_coeff_var(lp_acd);
    ineq q(lp::lconstraint_kind::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout << "expl & lemma: ");
    SASSERT(q == lemma.back());
    ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_coeff_var(lp_bde);
    i0.m_term.add_coeff_var(rational(1), lp_acd);
    bool found = false;
    for (const auto& k : lemma){
        if (k == i0) {
            found = true;
        } 
    }

    SASSERT(found);
}

void solver::test_order_lemma() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, abef = 13, cdij = 16, ij = 17;
    
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
    lpvar lp_abef = s.add_named_var(abef, true, "abef");
    lpvar lp_cdij = s.add_named_var(cdij, true, "cdij");

    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s.set_column_value(j, rational(3));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s, l, p);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    nla.add_monomial(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    nla.add_monomial(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    nla.add_monomial(lp_ij, vec.size(), vec.begin());
    
    // make ab < cd it the model
    s.set_column_value(lp_ab, rational(7));
    s.set_column_value(lp_cd, rational(8));

    s.set_column_value(lp_a,  rational(4));
    s.set_column_value(lp_b,  rational(4));
    s.set_column_value(lp_c,  rational(2));
    s.set_column_value(lp_d,  rational(3));
    //create monomial abef 
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_f);
    nla.add_monomial(lp_abef, vec.size(), vec.begin());

    s.set_column_value(lp_e,  rational(9));
    s.set_column_value(lp_f,  rational(11));

    //create monomial cdij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monomial(lp_cdij, vec.size(), vec.begin());

    // set ij == ef in the model
    s.set_column_value(lp_ij, rational(17));
    s.set_column_value(lp_ef, rational(17));

    // set abef = cdij, while it has to be abef < cdij
    s.set_column_value(lp_abef, rational(18));
    s.set_column_value(lp_cdij, rational(18));
   
    vector<ineq> lemma;
    lp::explanation exp;
    
    SASSERT(nla.m_imp->test_check(lemma, exp) == l_false);

    // lp::lar_term t;
    // t.add_coeff_var(lp_bde);
    // t.add_coeff_var(lp_acd);
    // ineq q(lp::lconstraint_kind::EQ, t, rational(0));
   
    nla.m_imp->print_lemma(std::cout << "lemma: ");
    // SASSERT(q == lemma.back());
    // ineq i0(lp::lconstraint_kind::EQ, lp::lar_term(), rational(0));
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
}
