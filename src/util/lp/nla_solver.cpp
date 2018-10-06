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
namespace nla {
typedef lp::constraint_index     lpci;
typedef std::unordered_set<lpci> expl_set;
typedef lp::var_index            lpvar;

struct hash_svector {
    size_t operator()(const unsigned_vector & v) const {
        return svector_hash<unsigned_hash>()(v);
    }
};

struct vars_equivalence {
    
    struct equiv {
        lpvar                m_i;
        lpvar                m_j;
        rational             m_sign;
        lpci                 m_c0;
        lpci                 m_c1;

        equiv(lpvar i, lpvar j, rational const& sign, lpci c0, lpci c1) :
            m_i(i),
            m_j(j),
            m_sign(sign),
            m_c0(c0),
            m_c1(c1) {
            SASSERT(m_i != m_j);
        }
    };

    // The map from the variables to m_equivs indices
    // m_tree is a spanning tree of the graph of equivs represented by m_equivs
    std::unordered_map<unsigned, unsigned> m_tree;  
    // If m_tree[v] == -1 then the variable is a root.
    // if m_tree[v] is not equal to -1 then m_equivs[m_tree[v]] = (k, v) or (v, k), that k is the parent of v
    vector<equiv>                     m_equivs;         // all equivalences extracted from constraints
    void clear() {
        m_equivs.clear();
        m_tree.clear();
    }

    unsigned size() const { return static_cast<unsigned>(m_tree.size()); }

    // we create a spanning tree on all variables participating in an equivalence
    void create_tree() {
        for (unsigned k = 0; k < m_equivs.size(); k++)
            connect_equiv_to_tree(k);
    }

    void add_equiv(lpvar i, lpvar j, rational const& sign, lpci c0, lpci c1) {
        m_equivs.push_back(equiv(i, j, sign, c0, c1));
    }
    
    void connect_equiv_to_tree(unsigned k) {
        // m_tree is a spanning tree of the graph of m_equivs
        const equiv &e = m_equivs[k];
        TRACE("nla_solver", tout << "m_i = " << e.m_i << ", " << "m_j = " << e.m_j ;);
        bool i_is_in = m_tree.find(e.m_i) != m_tree.end();
        bool j_is_in = m_tree.find(e.m_j) != m_tree.end();
        
        if (!(i_is_in || j_is_in)) {
            // none of the edge vertices is in the tree
            // let m_i be the parent, and m_j be the child
            TRACE("nla_solver", tout << "create nodes for " << e.m_i << " and " << e.m_j; );
            m_tree.emplace(e.m_i, -1);
            m_tree.emplace(e.m_j, k);
        } else if (i_is_in && (!j_is_in)) {
            // create a node for m_j, with m_i is the parent
            TRACE("nla_solver", tout << "create a node for " << e.m_j; );
            m_tree.emplace(e.m_j, k);
            // if m_i is a root here we can set its parent m_j
        } else if ((!i_is_in) && j_is_in) {
            TRACE("nla_solver", tout << "create a node for " << e.m_i; );
            m_tree.emplace(e.m_i, k);
            // if m_j is a root here we can set its parent to m_i
        } else {
            TRACE("nla_solver", tout << "both vertices are in the tree";);
        }
    }
    
    bool empty() const {
        return m_tree.empty();
    }

    bool is_root(unsigned j) const {
        auto it = m_tree.find(j);
        if (it == m_tree.end())
            return true;

        return it->second == static_cast<unsigned>(-1);
    }

    static unsigned get_parent_node(unsigned j, const equiv& e) {
        SASSERT(e.m_i == j || e.m_j == j);
        return e.m_i == j? e.m_j : e.m_i;
    }
    
    // Finds the root var which is equivalent to j.
    // The sign is flipped if needed
    lpvar map_to_root(lpvar j, rational& sign) const {
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return j;
            if (it->second == static_cast<unsigned>(-1))
                return j;
            const equiv & e = m_equivs[it->second];
            sign *= e.m_sign;
            j = get_parent_node(j, e);
        }
    }

    void add_equiv_exp(unsigned j, expl_set& exp) const {
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return;
            if (it->second == static_cast<unsigned>(-1))
                return;
            const equiv & e = m_equivs[it->second];
            exp.insert(e.m_c0);
            exp.insert(e.m_c1);
            j = get_parent_node(j, e);
        }
    }
    
    template <typename T>
    void add_explanation_of_reducing_to_rooted_monomial(const T & m, expl_set & exp) const {
        for (auto j : m)
            add_equiv_exp(j, exp);
    }

}; // end of vars_equivalence

struct solver::imp {

    typedef lp::lar_base_constraint lpcon;
    
    struct mono_index_with_sign {
        unsigned m_i; // the monomial index
        rational m_sign; // the monomial sign: -1 or 1
        mono_index_with_sign(unsigned i, rational sign) : m_i(i), m_sign(sign) {}
        mono_index_with_sign() {}
    };
    
    vars_equivalence                                       m_vars_equivalence;
    vector<monomial>                                         m_monomials;
    // maps the vector of the rooted monomial vars to the list of the indices of monomials having the same rooted monomial
    std::unordered_map<svector<lpvar>, vector<mono_index_with_sign>, hash_svector>
    m_rooted_monomials;
    unsigned_vector                                        m_monomials_lim;
    lp::lar_solver&                                        m_lar_solver;
    std::unordered_map<lpvar, unsigned_vector>             m_var_to_mon_indices;

    // monomial.var()  -> monomial index
    u_map<unsigned>                                        m_var_to_its_monomial;
    lp::explanation *                                      m_expl;
    lemma *                                                m_lemma;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        : m_lar_solver(s)
          // m_limit(lim),
          // m_params(p)
    {
    }


    rational vvr(unsigned j) const { return m_lar_solver.get_column_value_rational(j); }
    lp::impq vv(unsigned j) const { return m_lar_solver.get_column_value(j); }
    
    void add(lpvar v, unsigned sz, lpvar const* vs) {
        m_monomials.push_back(monomial(v, sz, vs));
        m_var_to_its_monomial.insert(v, m_monomials.size() - 1);
    }
    
    void push() {
        m_monomials_lim.push_back(m_monomials.size());
    }
    
    void pop(unsigned n) {
        if (n == 0) return;
        m_monomials.shrink(m_monomials_lim[m_monomials_lim.size() - n]);
        m_monomials_lim.shrink(m_monomials_lim.size() - n);       
    }

    // make sure that the monomial value is the product of the values of the factors
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

    void add_explanation_of_reducing_to_rooted_monomial(const monomial& m, expl_set & exp) const {
        m_vars_equivalence.add_explanation_of_reducing_to_rooted_monomial(m, exp);
    }

    void add_explanation_of_reducing_to_rooted_monomial(lpvar j, expl_set & exp) const {
        unsigned index = 0;
        if (!m_var_to_its_monomial.find(j, index))
            return; // j is not a var of a monomial
        add_explanation_of_reducing_to_rooted_monomial(m_monomials[index], exp);
    }

    std::ostream& print_monomial(const monomial& m, std::ostream& out) const {
        out << m_lar_solver.get_variable_name(m.var()) << " = ";
        for (unsigned k = 0; k < m.size(); k++) {
            out << m_lar_solver.get_variable_name(m.vars()[k]);
            if (k + 1 < m.size()) out << "*";
        }
        return out;
    }

    std::ostream& print_explanation(std::ostream& out) const {
        for (auto &p : *m_expl) {
            m_lar_solver.print_constraint(p.second, out);
        }
        return out;
    }

    
    // the monomials should be equal by modulo sign, but they are not equal in the model by modulo sign
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
        lp::lar_term t;
        t.add_coeff_var(rational(1), a.var());
        t.add_coeff_var(-sign, b.var());
        ineq in(lp::lconstraint_kind::EQ, t, rational::zero());
        m_lemma->push_back(in);
        TRACE("nla_solver", print_explanation_and_lemma(tout););
    }

    // Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
    // 
    svector<lpvar> reduce_monomial_to_canonical(const svector<lpvar> & vars, rational & sign) const {
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
    // representative under current equations.
    // 
    monomial_coeff canonize_monomial(monomial const& m) const {
        rational sign = rational(1);
        svector<lpvar> vars = reduce_monomial_to_canonical(m.vars(), sign);
        return monomial_coeff(m.var(), vars, sign);
    }

    bool list_contains_one_to_refine(const std::unordered_set<unsigned> & to_refine_set,
                                     const vector<mono_index_with_sign>& list_of_mon_indices) {
        for (const auto& p : list_of_mon_indices) {
            if (to_refine_set.find(p.m_i) != to_refine_set.end())
                return true;
        }
        return false;
    }
    
    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool basic_sign_lemma(const unsigned_vector& to_refine) {
        if (m_vars_equivalence.empty()) {
            return false;
        }
        std::unordered_set<unsigned> to_refine_set;
        for (unsigned i : to_refine)
            to_refine_set.insert(i);
        for (auto it : m_rooted_monomials) {
            const auto & list = it.second;
            if (!list_contains_one_to_refine(to_refine_set, list))
                continue;
            const auto & m0 = list[0];
           
            rational val = vvr(m_monomials[m0.m_i].var()) * m0.m_sign;
            // every other monomial in the list has to have the same value up to the sign
            for (unsigned i = 1; i < list.size(); i++) {
                const auto & mi = list[i];
                rational other_val = vvr(m_monomials[mi.m_i].var()) * mi.m_sign;
                if (val != other_val) {
                    fill_explanation_and_lemma_sign(m_monomials[m0.m_i],
                                                    m_monomials[mi.m_i],
                                                    m0.m_sign * mi.m_sign);
                    return true;
                }
            }
        }
        
        return false;
    }

    bool is_set(unsigned j) const {
        return static_cast<unsigned>(-1) != j;
    }

    
    // Return 0 if the var has to to have a zero value,
    // -1 if the monomial has to be negative
    // 1 if positive.
    // If strict is true on the entrance then it can be set to false,
    // otherwise it remains false
    // Returns 2 if the sign is not defined.
    int get_mon_sign_zero_var(unsigned j, bool & strict) {
        if (m_var_to_mon_indices.find(j) == m_var_to_mon_indices.end())
            return 2;
        lpci lci = -1;
        lpci uci = -1;
        rational lb, ub;
        bool lower_is_strict;
        bool upper_is_strict;
        m_lar_solver.has_lower_bound(j, lci, lb, lower_is_strict);
        m_lar_solver.has_upper_bound(j, uci, ub, upper_is_strict);
            
        if (is_set(uci) && is_set(lci) && ub == lb) {
            if (ub.is_zero()){
                m_expl->clear();
                m_expl->push_justification(uci);
                m_expl->push_justification(lci);
                return 0;
            }
            m_expl->push_justification(uci);
            m_expl->push_justification(lci);
            return ub.is_pos() ? 1 : -1;
        }
        
        if (is_set(uci)) {
            if (ub.is_neg()) {
                m_expl->push_justification(uci);
                return -1;
            }
            if (ub.is_zero()) {
                strict = false;
                m_expl->push_justification(uci);
                return -1;
            }
        }
        
        if (is_set(lci)) {
            if (lb.is_pos()) {
                m_expl->push_justification(lci);
                return 1;
            }
            if (lb.is_zero()) {
                strict = false;
                m_expl->push_justification(lci);
                return 1;
            }
        }
        
        return 2; // the sign of the variable is not defined
    }
    

    // Return 0 if the monomial has to to have a zero value,
    // -1 if the monomial has to be negative or zero 
    // 1 if positive or zero
    // otherwise return 2 (2 is not a sign!)
    // if strict is true then 0 is excluded
    int get_mon_sign_zero(unsigned i_mon, bool & strict) {
        int sign = 1;
        strict = true;
        const monomial m = m_monomials[i_mon];
        for (lpvar j : m) {
            int s = get_mon_sign_zero_var(j, strict);
            if (s == 2)
                return 2;
            if (s == 0)
                return 0;
            sign *= s;
        }
        return sign;
    }

    /*
      Here we use the following theorems
      a) v1 = 0 or v2 = 0 iff v1*v2 = 0
      b) (v1 > 0 and v2 > 0) or (v1 < 0 and v2 < 0) iff
      v1 * v2 > 0
      c) (v1 < 0 and v2 > 0) or (v1 > 0 and v2 < 0) iff
      v1 * v2 < 0
    */
    bool basic_lemma_for_mon_zero(unsigned i_mon) {
        m_expl->clear();
        const auto mon = m_monomials[i_mon];
        const rational & mon_val = m_lar_solver.get_column_value_rational(mon.var());
        bool strict;
        int sign = get_mon_sign_zero(i_mon, strict);
        lp::lconstraint_kind kind;
        rational rs(0);
        switch(sign) {
        case 0:
            SASSERT(!mon_val.is_zero());
            kind = lp::lconstraint_kind::EQ;
            break;
        case 1:
            if (strict)
                rs = rational(1);
            if (mon_val >= rs)
                return false;
            kind = lp::lconstraint_kind::GE;
            break;
        case -1:
            if (strict)
                rs = rational(-1);
            if (mon_val <= rs)
                return false;
            kind = lp::lconstraint_kind::LE;
            break;
        default:
            if (mon_val.is_zero() && var_is_fixed_to_zero(mon.var())) {
                create_lemma_one_of_the_factors_is_zero(mon);
                TRACE("nla_solver", print_explanation_and_lemma(tout););
                return true;
            }
            return false;
        }
        lp::lar_term t;
        t.add_coeff_var(rational(1), m_monomials[i_mon].var());
        ineq in(kind, t, rs);
        m_lemma->push_back(in);
        TRACE("nla_solver", print_explanation_and_lemma(tout););
        return true;
    }

    void create_lemma_one_of_the_factors_is_zero(const monomial& m) {
        lpci lci, uci;
        rational b;
        bool is_strict;
        m_lar_solver.has_lower_bound(m.var(), lci, b, is_strict);
        SASSERT(b.is_zero() && !is_strict);
        m_lar_solver.has_upper_bound(m.var(), uci, b, is_strict);
        SASSERT(b.is_zero() && !is_strict);
        m_expl->clear();
        m_expl->push_justification(lci);
        m_expl->push_justification(uci);
        m_lemma->clear();
        for (auto j : m) {
            m_lemma->push_back(ineq_j_is_equal_to_zero(j));
        }
    }

    ineq ineq_j_is_equal_to_zero(lpvar j) const {
        lp::lar_term t;
        t.add_coeff_var(rational(1), j);
        ineq i(lp::lconstraint_kind::EQ, t, rational::zero());
        return i;
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
        out << " " << lp::lconstraint_kind_string(in.m_cmp) << " 0";
        return out;
    }

    std::ostream & print_var(lpvar j, std::ostream & out) const {
        bool is_monomial = false;
        for (const monomial & m : m_monomials) {
            if (j == m.var()) {
                is_monomial = true;
                print_monomial(m, out);
                out << " = " << m_lar_solver.get_column_value(j);;
                break;
            }
        }
        if (!is_monomial)
            out << m_lar_solver.get_variable_name(j) << " = " << m_lar_solver.get_column_value(j);
        out <<";";
        return out;
    }    

    
    std::ostream & print_lemma(lemma& l, std::ostream & out) const {
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
        return out;
    }

    std::ostream & print_explanation_and_lemma(std::ostream & out) const {
        out << "explanation:\n";
        print_explanation(out) << "lemma: ";
        print_lemma(*m_lemma, out);
        out << "\n";
        return out;
    }
    /**
     * \brief <return true if j is fixed to 1 or -1, and put the value into "sign">
     */
    bool get_one_of_var(lpvar j, rational & sign) {
        lpci lci;
        lpci uci;
        rational lb, ub;
        bool is_strict;
        if (!m_lar_solver.has_lower_bound(j, lci, lb, is_strict))
            return false;
        SASSERT(!is_strict);
        if (!m_lar_solver.has_upper_bound(j, uci, ub, is_strict))
            return false;
        SASSERT(!is_strict);

        if (ub == lb) {
            if (ub == rational(1)) {
                sign = rational(1);
            }
            else if (ub == -rational(1)) {
                sign = rational(-1);
            }
            else 
                return false;
            return true;
        }
        return false;
    }

    vector<mono_index_with_sign> get_ones_of_monomimal(const svector<lpvar> & vars) {
        TRACE("nla_solver", tout << "get_ones_of_monomimal";);
        vector<mono_index_with_sign> ret;
        for (unsigned i = 0; i < vars.size(); i++) {
            mono_index_with_sign mi;
            if (get_one_of_var(vars[i], mi.m_sign)) {
                mi.m_i = i;
                ret.push_back(mi);
            }
        }
        return ret;
    }

    
    void get_large_and_small_indices_of_monomimal(const monomial& m,
                                                  unsigned_vector & large,
                                                  unsigned_vector & _small) {

        for (unsigned i = 0; i < m.size(); ++i) {
            unsigned j = m.vars()[i];
            lp::constraint_index lci = -1, uci = -1;
            rational             lb, ub;
            bool                 is_strict;
            if (m_lar_solver.has_lower_bound(j, lci, lb, is_strict)) {
                SASSERT(!is_strict);
                if (lb >= rational(1)) {
                    large.push_back(i);
                }
            }
            if (m_lar_solver.has_upper_bound(j, uci, ub, is_strict)) {
                SASSERT(!is_strict);
                if (ub <= -rational(1)) {
                    large.push_back(i);
                }
            }
            
            if (is_set(lci) && is_set(uci) && -rational(1) <= lb && ub <= rational(1)) {
                _small.push_back(i);
            }
        }
    }

    /**
     * \brief generate lemma by using the fact that 1*x = x or x*1 = x
     * v is the value of monomial, 
     * vars is the array of reduced to minimum variables of the monomial
     */
    bool basic_neutral_for_reduced_monomial(const monomial & m, const rational & v, const svector<lpvar> & vars) {
        vector<mono_index_with_sign> ones_of_mon = get_ones_of_monomimal(vars);
        
        // if abs(m.vars()[j]) is 1, then ones_of_mon[j] = sign, where sign is 1 in case of m.vars()[j] = 1, or -1 otherwise.
        if (ones_of_mon.empty()) {
            return false;
        }
        
        return process_ones_of_mon(m, ones_of_mon, vars, v);
    }
    /**
     * \brief <generate lemma by using the fact that 1*x = x or x*1 = x>
     */    
    bool basic_lemma_for_mon_neutral(unsigned i_mon) {
        const monomial & m = m_monomials[i_mon];
        rational sign;
        svector<lpvar> reduced_vars = reduce_monomial_to_canonical(m.vars(), sign);
        rational v = m_lar_solver.get_column_value_rational(m.var());
        if (sign == -1)
            v = -v;
        return basic_neutral_for_reduced_monomial(m, v, reduced_vars);
    }

    // returns the variable m_i, of a monomial if found and sets the sign,
    bool find_monomial_of_vars(const svector<lpvar>& vars, monomial& m, rational & sign) const {
        auto it = m_rooted_monomials.find(vars);
        if (it == m_rooted_monomials.end()) {
            return false;
        }

        const mono_index_with_sign & mi = *(it->second.begin());
        sign = mi.m_sign;
        m = m_monomials[mi.m_i];
        return true;
    }

    bool find_complimenting_monomial(const svector<lpvar> & vars, lpvar & j) {
        monomial m;
        rational other_sign;
        if (!find_monomial_of_vars(vars, m, other_sign)) {
            return false;
        }
        j = m.var();
        return true;
    }
    
    bool find_lpvar_and_sign_with_wrong_val(
        const monomial& m,
        svector<lpvar> & vars,
        const rational& v,
        rational sign,
        lpvar& j) {
        rational other_sign;
        monomial mn;
        if (!find_monomial_of_vars(vars, mn, other_sign)) {
            return false;
        }
        sign *= other_sign;
        j = mn.var();
        rational other_val = m_lar_solver.get_column_value_rational(j);
        return sign * other_val != v;                
    }

    void add_explanation_of_one(const mono_index_with_sign & mi) {
        NOT_IMPLEMENTED_YET();
    }

    // m: v = v1*v2...*vn
    // mask: indices of variables that were processed
    // ones_of_monomial signed monomial indices
    // sign ?
    // j ?
    // 
    void equality_for_neutral_case(const monomial & m,
                                   const svector<bool> & mask,
                                   const vector<mono_index_with_sign>& ones_of_monomial, lpvar j, rational const& sign) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_explanation_of_reducing_to_rooted_monomial(m, expl);
        m_expl->clear();
        m_expl->add(expl);
        for (unsigned k : mask) {
            add_explanation_of_one(ones_of_monomial[k]);
        }
        lp::lar_term t;
        t.add_coeff_var(rational(1), m.var());
        t.add_coeff_var(rational(- sign), j);
        ineq in(lp::lconstraint_kind::EQ, t, rational::zero());
        m_lemma->push_back(in);
        TRACE("nla_solver", print_explanation_and_lemma(tout););
    }
    
    // vars here are root vars for m.vs
    bool process_ones_of_mon(const monomial& m,
                             const vector<mono_index_with_sign>& ones_of_monomial, const svector<lpvar> &min_vars,
                             const rational& v) {
        svector<bool> mask(ones_of_monomial.size(), false);
        auto vars = min_vars;
        rational sign(1);
        // We cross out the ones representing the mask from vars
        do {
            for (unsigned k = 0; k < mask.size(); k++) {
                if (!mask[k]) {
                    mask[k] = true;
                    sign *= ones_of_monomial[k].m_sign;
                    TRACE("nla_solver", tout << "index m_i = " << ones_of_monomial[k].m_i;);
                    vars.erase(vars.begin() + ones_of_monomial[k].m_i);
                    std::sort(vars.begin(), vars.end());
                    // now the value of vars has to be v*sign
                    lpvar j;
                    if (!find_lpvar_and_sign_with_wrong_val(m, vars, v, sign, j))
                        return false;
                    equality_for_neutral_case(m, mask, ones_of_monomial, j, sign);
                    return true;
                } else {
                    SASSERT(mask[k]);
                    sign *= ones_of_monomial[k].m_sign;
                    mask[k] = false;
                    vars.push_back(min_vars[ones_of_monomial[k].m_i]); // vars becomes unsorted
                }
            }
        } while(true);
        return false; // we exhausted the mask and did not find a compliment monomial
    }

    void add_explanation_of_large_value(lpvar j, expl_set & expl) {
        lpci ci;
        rational b;
        bool strict;
        if (m_lar_solver.has_lower_bound(j, ci, b, strict) && rational(1) <= b) {
            expl.insert(ci);
        } else if (m_lar_solver.has_upper_bound(j, ci, b, strict)) {
            SASSERT(b <= rational(-1));
            expl.insert(ci);
        } else {
            UNREACHABLE();
        }
    }

    void add_explanation_of_small_value(lpvar j, expl_set & expl) {
        lpci ci;
        rational b;
        bool strict;
        m_lar_solver.has_lower_bound(j, ci, b, strict);
        SASSERT(b >= -rational(1));
        expl.insert(ci);
        m_lar_solver.has_upper_bound(j, ci, b, strict);
        SASSERT(b <= rational(1));
        expl.insert(ci);
    }

    void large_lemma_for_proportion_case_on_known_signs(const monomial& m,
                                                        unsigned j,
                                                        int mon_sign,
                                                        int j_sign) {
        // Imagine that the signs are all positive and flip them afterwards.
        // For this case we would have x[j] < 0 || x[m.var()] < 0 || x[m.var] >= x[j]
        // But for the general case we have
        // j_sign * x[j] < 0 || mon_sign * x[m.var()] < 0 || mon_sign * x[m.var()] >= j_sign * x[j]
        // the first literal
        lp::lar_term t; 
        t.add_coeff_var(rational(j_sign), j);
        m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, rational::zero()));

        t.clear();
        // the second literal
        t.add_coeff_var(rational(mon_sign), m.var());
        m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, rational::zero()));

        t.clear();
        // the third literal
        t.add_coeff_var(rational(mon_sign), m.var());
        t.add_coeff_var(- rational(j_sign), j);
        m_lemma->push_back(ineq(lp::lconstraint_kind::GE, t, rational::zero()));
    }
    
    bool large_lemma_for_proportion_case(const monomial& m, const svector<bool> & mask,
                                         const unsigned_vector & large, unsigned j) {
        TRACE("nla_solver", );
        const rational j_val = m_lar_solver.get_column_value_rational(j);
        const rational m_val = m_lar_solver.get_column_value_rational(m.var());
        const rational m_abs_val = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // since the abs of masked factor is greater than or equal to one
        // j_val has to be less than or equal to m_abs_val
        int j_sign = j_val < - m_abs_val? -1: (j_val > m_abs_val)? 1: 0;
        if (j_sign == 0) // abs(j_val) <= abs(m_val) which is not a conflict
            return false;
        expl_set expl;
        add_explanation_of_reducing_to_rooted_monomial(m, expl);
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k] == 1)
                add_explanation_of_large_value(m.vars()[large[k]], expl);
        }
        m_expl->clear();
        m_expl->add(expl);
        int mon_sign = m_val < rational(0) ? -1 : 1;
        large_lemma_for_proportion_case_on_known_signs(m, j, mon_sign, j_sign);
        return true;
    }

    bool small_lemma_for_proportion_case(const monomial& m, const svector<bool> & mask,
                                         const unsigned_vector & _small, unsigned j) {
        TRACE("nla_solver", );
        const rational j_val = m_lar_solver.get_column_value_rational(j);
        const rational m_val = m_lar_solver.get_column_value_rational(m.var());
        const rational m_abs_val = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // since the abs of the masked factor is less than or equal to one
        // j_val has to be greater than or equal to m_abs_val
        if (j_val <= - m_abs_val || j_val > m_abs_val)
            return false;

        expl_set expl;
        add_explanation_of_reducing_to_rooted_monomial(m, expl);
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k] == 1)
                add_explanation_of_small_value(m.vars()[_small[k]], expl);
        }
        m_expl->clear();
        m_expl->add(expl);
        int mon_sign = m_val < rational(0) ? -1 : 1;
        int j_sign = j_val >= rational(0)? 1: -1;
        small_lemma_for_proportion_case_on_known_signs(m, j, mon_sign, j_sign);
        return true;
    }

    // It is the case where |x[j]| >= |x[m.var()]| should hold in the model, but it does not.
    void small_lemma_for_proportion_case_on_known_signs(const monomial& m, unsigned j, int mon_sign, int j_sign) {
        // Imagine that the signs are all positive.
        // For this case we would have x[j] < 0 || x[m.var()] < 0 || x[j] >= x[m.var()]
        // But for the general case we have
        // j_sign * x[j] < 0 || mon_sign * x[m.var()] < 0 || j_sign * x[j] >= mon_sign * x[m.var]
  
        lp::lar_term t;
        // the first literal
        t.add_coeff_var(rational(j_sign), j);
        m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, rational::zero()));
        //the second literal
        t.clear();
        t.add_coeff_var(rational(mon_sign), m.var());
        m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, rational::zero()));
        // the third literal
        t.clear();
        t.add_coeff_var(rational(j_sign), j);
        t.add_coeff_var(- rational(mon_sign), m.var());
        m_lemma->push_back(ineq(lp::lconstraint_kind::GE, t, rational::zero()));
    }
    
    bool large_basic_lemma_for_mon_proportionality(unsigned i_mon, const unsigned_vector& large) {
        svector<bool> mask(large.size(), false);  // init mask by false
        const auto & m = m_monomials[i_mon];
        rational sign;
        auto vars = reduce_monomial_to_canonical(m.vars(), sign);
        auto vars_copy = vars;
        auto v = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // We cross out from vars the "large" variables represented by the mask
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k]) {
                mask[k] = true;
                TRACE("nla_solver", tout << "large[" << k << "] = " << large[k];);
                SASSERT(std::find(vars.begin(), vars.end(), vars_copy[large[k]]) != vars.end());
                vars.erase(vars_copy[large[k]]);
                std::sort(vars.begin(), vars.end());
                // now the value of vars has to be v*sign
                lpvar j;
                if (find_complimenting_monomial(vars, j) &&
                    large_lemma_for_proportion_case(m, mask, large, j)) {
                    TRACE("nla_solver", print_explanation_and_lemma(tout););
                    return true;
                }
            } else {
                SASSERT(mask[k]);
                mask[k] = false;
                vars.push_back(vars_copy[large[k]]); // vars might become unsorted
            }
        }
        return false; // we exhausted the mask and did not find the compliment monomial
    }

    bool small_basic_lemma_for_mon_proportionality(unsigned i_mon, const unsigned_vector& _small) {
        svector<bool> mask(_small.size(), false); // init mask by false
        const auto & m = m_monomials[i_mon];
        rational sign;
        auto vars = reduce_monomial_to_canonical(m.vars(), sign);
        auto vars_copy = vars;
        auto v = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // We cross out from vars the "large" variables represented by the mask
        for (unsigned k = 0; k < mask.size(); k++) {
            if (!mask[k]) {
                mask[k] = true;
                TRACE("nla_solver", tout << "_small[" << k << "] = " << _small[k];);
                SASSERT(std::find(vars.begin(), vars.end(), vars_copy[_small[k]]) != vars.end());
                vars.erase(vars_copy[_small[k]]);
                std::sort(vars.begin(), vars.end());
                // now the value of vars has to be v*sign
                lpvar j;
                if (find_complimenting_monomial(vars, j) &&
                    small_lemma_for_proportion_case(m, mask, _small, j)) {
                    TRACE("nla_solver", print_explanation_and_lemma(tout););
                    return true;
                }
            } else {
                SASSERT(mask[k]);
                mask[k] = false;
                vars.push_back(vars_copy[_small[k]]); // vars might become unsorted
            }
        }

        return false; // we exhausted the mask and did not find the compliment monomial
    }

    // we derive a lemma from |x| >= 1 => |xy| >= |y| or |x| <= 1 => |xy| <= |y|  
    bool basic_lemma_for_mon_proportionality_from_factors_to_product(unsigned i_mon) {
        const monomial & m = m_monomials[i_mon];
        unsigned_vector large;
        unsigned_vector _small;
        get_large_and_small_indices_of_monomimal(m, large, _small);
        TRACE("nla_solver", tout << "large size = " << large.size() << ", _small size = " << _small.size(););
        if (large.empty() && _small.empty())
            return false;
        
        return 
           large_basic_lemma_for_mon_proportionality(i_mon, large)
		   ||
           small_basic_lemma_for_mon_proportionality(i_mon, _small);
    }

    // Using the following theorems
    // |ab| >= |b| iff |a| >= 1 or b = 0
    // |ab| <= |b| iff |a| <= 1 or b = 0
    // and their commutative variants
    bool basic_lemma_for_mon_proportionality(unsigned i_mon) {
        TRACE("nla_solver", tout << "basic_lemma_for_mon_proportionality";);
        return 
            basic_lemma_for_mon_proportionality_from_factors_to_product(i_mon) ||
            basic_lemma_for_mon_proportionality_from_product_to_factors(i_mon);
    }

    class signed_factorization {
        svector<lpvar>         m_vars;  // the m_vars[j] corresponds to a monomial var or just to a var 
        rational               m_sign;
        std::function<void (expl_set&)> m_explain;
    public:
        void explain(expl_set& s) const { m_explain(s); }
        bool is_empty() const { return m_vars.empty(); }
        svector<lpvar> & vars() { return m_vars; }
        const svector<lpvar> & vars() const { return m_vars; }
        rational const& sign() const { return m_sign; }
        rational& sign() { return m_sign; } // the setter
        unsigned operator[](unsigned k) const { return m_vars[k]; }
        size_t size() const { return m_vars.size(); }
        const lpvar* begin() const { return m_vars.begin(); }
        const lpvar* end() const { return m_vars.end(); }
        signed_factorization(std::function<void (expl_set&)> explain) : m_explain(explain) {}
    };

    std::ostream & print_factorization(const signed_factorization& f, std::ostream& out) const {
        for (unsigned k = 0; k < f.size(); k++ ) {
            print_var(f[k], out);
            if (k < f.size() - 1)
                out << "*";
        }
        return out << ", sign = " << f.sign();
    }
    
    struct binary_factorizations_of_monomial {
        unsigned         m_i_mon;
        const imp&       m_imp;
        const monomial&    m_mon;
        monomial_coeff m_cmon;

        binary_factorizations_of_monomial(unsigned i_mon, const imp& s) :
            m_i_mon(i_mon),
            m_imp(s),
            m_mon(m_imp.m_monomials[i_mon]),
            m_cmon(m_imp.canonize_monomial(m_mon)) {
        }

        
        
        struct const_iterator {
            // fields
            svector<bool>                              m_mask;
            const binary_factorizations_of_monomial&   m_binary_factorizations;
            bool m_full_factorization_returned;

            //typedefs
            typedef const_iterator self_type;
            typedef signed_factorization value_type;
            typedef const signed_factorization reference;
            typedef int difference_type;
            typedef std::forward_iterator_tag iterator_category;

            void init_vars_by_the_mask(unsigned_vector & k_vars, unsigned_vector & j_vars) const {
                // the last element for m_binary_factorizations.m_rooted_vars goes to k_vars
                SASSERT(m_mask.size() + 1  == m_binary_factorizations.m_cmon.vars().size());
                k_vars.push_back(m_binary_factorizations.m_cmon.vars().back()); 
                for (unsigned j = 0; j < m_mask.size(); j++) {
                    if (m_mask[j]) {
                        k_vars.push_back(m_binary_factorizations.m_cmon[j]);
                    } else {
                        j_vars.push_back(m_binary_factorizations.m_cmon[j]);
                    }
                }
            }
            
            bool get_factors(unsigned& k, unsigned& j, rational& sign) const {
                unsigned_vector k_vars;
                unsigned_vector j_vars;
                init_vars_by_the_mask(k_vars, j_vars);
                SASSERT(!k_vars.empty() && !j_vars.empty());
                std::sort(k_vars.begin(), k_vars.end());
                std::sort(j_vars.begin(), j_vars.end());

                rational k_sign, j_sign;
                monomial m;
                if (k_vars.size() == 1) {
                    k = k_vars[0];
                    k_sign = 1;
                } else {
                    if (!m_binary_factorizations.m_imp.find_monomial_of_vars(k_vars, m, k_sign)) {
                        return false;
                    }
                    k = m.var();
                }
                if (j_vars.size() == 1) {
                    j = j_vars[0];
                    j_sign = 1;
                } else {
                    if (!m_binary_factorizations.m_imp.find_monomial_of_vars(j_vars, m, j_sign)) {
                        return false;
                    }
                    j = m.var();
                }
                sign = j_sign * k_sign;
                return true;
            }

            reference operator*() const {
                if (m_full_factorization_returned == false)  {
                    return create_full_factorization();
                }
                unsigned j, k; rational sign;
                if (!get_factors(j, k, sign))
                    return signed_factorization([](expl_set&){});
                return create_binary_signed_factorization(j, k, m_binary_factorizations.m_cmon.coeff() * sign);
            }
            
            void advance_mask() {
                if (!m_full_factorization_returned) {
                    m_full_factorization_returned = true;
                    return;
                }
                for (bool& m : m_mask) {
                    if (m) {
                        m = false;
                    }
                    else {
                        m = true;
                        break;
                    }
                }
            }

            
            self_type operator++() {  self_type i = *this; operator++(1); return i;  }
            self_type operator++(int) { advance_mask(); return *this; }

            const_iterator(const svector<bool>& mask, const binary_factorizations_of_monomial & f) : 
                m_mask(mask),
                m_binary_factorizations(f) ,
                m_full_factorization_returned(false)
            {}
            
            bool operator==(const self_type &other) const {
                return
                    m_full_factorization_returned == other.m_full_factorization_returned &&
                    m_mask == other.m_mask;
            }
            bool operator!=(const self_type &other) const { return !(*this == other); }
            
            signed_factorization create_binary_signed_factorization(lpvar j, lpvar k, rational const& sign) const {
                std::function<void (expl_set&)> explain = [&](expl_set& exp){
                    const imp & impl = m_binary_factorizations.m_imp;
                    unsigned mon_index = 0;
                    if (impl.m_var_to_its_monomial.find(k, mon_index)) {
                        impl.add_explanation_of_reducing_to_rooted_monomial(impl.m_monomials[mon_index], exp);
                    }
                    if (impl.m_var_to_its_monomial.find(j, mon_index)) {
                        impl.add_explanation_of_reducing_to_rooted_monomial(impl.m_monomials[mon_index], exp);
                    }
                    if (m_full_factorization_returned) {                        
                        impl.add_explanation_of_reducing_to_rooted_monomial(m_binary_factorizations.m_mon, exp);
                    }
                };
                signed_factorization f(explain);
                f.vars().push_back(j);
                f.vars().push_back(k);
                f.sign() = sign;
                return f;
            }

            signed_factorization create_full_factorization() const {
                signed_factorization f([](expl_set&){});
                f.vars() = m_binary_factorizations.m_cmon.vars();
                f.sign() = m_binary_factorizations.m_cmon.coeff();
                return f;
            }
        };

        
        const_iterator begin() const {
            // we keep the last element always in the first factor to avoid
            // repeating a pair twice
            svector<bool> mask(m_mon.vars().size() - 1, false);
            return const_iterator(mask, *this);
        }
        
        const_iterator end() const {
            svector<bool> mask(m_mon.vars().size() - 1, true);
            auto it = const_iterator(mask, *this);
            it.m_full_factorization_returned = true;
            return it;
        }
    };

    void restrict_signs_of_xy_and_y_on_lemma(lpvar y, lpvar xy, const rational& _y, const rational& _xy, int& y_sign, int &xy_sign) {
        lp::lar_term t;
        t.add_coeff_var(rational(1), y);
        if (_y.is_pos()) {
            y_sign = 1;
            m_lemma->push_back(ineq(lp::lconstraint_kind::LE, t, rational::zero()));
        } else {
            y_sign = -1;
            m_lemma->push_back(ineq(lp::lconstraint_kind::GT, t, rational::zero()));
        }

        t.clear();
        t.add_coeff_var(rational(1), xy);
        if (_y.is_pos()) {
            xy_sign = 1;
            m_lemma->push_back(ineq(lp::lconstraint_kind::LE, t, rational::zero()));
        } else {
            xy_sign = -1;
            m_lemma->push_back(ineq(lp::lconstraint_kind::GT, t, rational::zero()));
        }
    }
    
    // We derive a lemma from |x| >= 1 || y = 0 => |xy| >= |y|
    // Here f is a factorization of monomial xy ( it can have more factors than 2)
    // f[k] plays the role of y, the rest of the factors play the role of x
    bool lemma_for_proportional_factors_on_vars_ge(lpvar xy, unsigned k, const signed_factorization& f) {
        TRACE("nla_solver",
              print_factorization(f, tout << "f=");
              print_var(f[k], tout << "y="););
        NOT_IMPLEMENTED_YET();
        /*
        const rational & _x = vvr(x);
        const rational & _y = vvr(y);

        if (!(abs(_x) >= rational(1) || _y.is_zero()))
            return false;
        // the precondition holds
        const rational & _xy = vvr(xy);
        if (abs(_xy) >= abs(_y))
            return false;
        // Here we just create the lemma.
        lp::lar_term t;
        if (abs(_x) >= rational(1)) {
            // add to lemma x < -1 || x > 1
            t.add_coeff_var(rational(1), x);
            if (_x >= rational(1))
                m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, rational(1)));
            else {
                lp_assert(_x <= -rational(1));
                m_lemma->push_back(ineq(lp::lconstraint_kind::GT, t, -rational(1)));
            }
        } else {
            lp_assert(_y.is_zero() && t.is_empty());
            // add to lemma y != 0
            t.add_coeff_var(rational(1), y);
            m_lemma->push_back(ineq(lp::lconstraint_kind::NE, t, rational::zero()));
        }

        int xy_sign, y_sign;
        restrict_signs_of_xy_and_y_on_lemma(y, xy, _y, _xy, y_sign, xy_sign);
        
        t.clear(); // abs(xy) - abs(y) <= 0
        t.add_coeff_var(rational(xy_sign), xy);
        t.add_coeff_var(rational(-y_sign), y);
        m_lemma->push_back(ineq(lp::lconstraint_kind::GE, t, rational::zero()));
        TRACE("nla_solver", tout<< "lemma: ";print_lemma(*m_lemma, tout););
        return true;
        */
        return false;
    }

    // we derive a lemma from |x| <= 1 || y = 0 => |xy| <= |y|
    bool lemma_for_proportional_factors_on_vars_le(lpvar xy, unsigned k, const signed_factorization & f) {
        NOT_IMPLEMENTED_YET();
        /*
        TRACE("nla_solver",
              print_var(xy, tout << "xy=");
              print_var(x, tout << "x=");
              print_var(y, tout << "y="););
        const rational & _x = vvr(x);
        const rational & _y = vvr(y);

        if (!(abs(_x) <= rational(1) || _y.is_zero()))
            return false;
        // the precondition holds
        const rational & _xy = vvr(xy);
        if (abs(_xy) <= abs(_y))
            return false;
        // Here we just create the lemma.
        lp::lar_term t;
        if (abs(_x) <= rational(1)) {
            // add to lemma x < -1 || x > 1
            t.add_coeff_var(rational(1), x);
            m_lemma->push_back(ineq(lp::lconstraint_kind::LT, t, -rational(1)));
            m_lemma->push_back(ineq(lp::lconstraint_kind::GT, t,  rational(1)));
        } else {
            lp_assert(_y.is_zero() && t.is_empty());
            // add to lemma y != 0
            t.add_coeff_var(rational(1), y);
            m_lemma->push_back(ineq(lp::lconstraint_kind::NE, t, rational::zero()));
        }
        
        int y_sign, xy_sign;
        restrict_signs_of_xy_and_y_on_lemma(y, xy, _y, _xy, y_sign, xy_sign);
        
        t.clear(); // abs(xy) - abs(y) <= 0
        t.add_coeff_var(rational(xy_sign), xy);
        t.add_coeff_var(rational(-y_sign), y);
        m_lemma->push_back(ineq(lp::lconstraint_kind::LE, t, rational::zero()));
        TRACE("nla_solver", tout<< "lemma: ";print_lemma(*m_lemma, tout););
        return true;
        */
        return false;
    }

    // we derive a lemma from |x| >= 1 || |y| = 0 => |xy| >= |y|, or the similar of <= 
    bool lemma_for_proportional_factors(unsigned i_mon, const signed_factorization& f) {
        lpvar var_of_mon = m_monomials[i_mon].var();
        TRACE("nla_solver", print_var(var_of_mon, tout); tout << " is factorized as "; print_factorization(f, tout););
        for (unsigned k = 0; k < f.size(); k++) {
            if (lemma_for_proportional_factors_on_vars_ge(var_of_mon, k, f) ||
                lemma_for_proportional_factors_on_vars_le(var_of_mon, k, f))
                return true;
        }
        return false;
    }
    // we derive a lemma from |xy| >= |y| => |x| >= 1 || |y| = 0
    bool basic_lemma_for_mon_proportionality_from_product_to_factors(unsigned i_mon) {
        for (auto factorization : binary_factorizations_of_monomial(i_mon, *this)) {
            if (factorization.is_empty()) {
                TRACE("nla_solver", tout << "empty factorization";);
                continue;
            }
            if (lemma_for_proportional_factors(i_mon, factorization)) {
                expl_set exp;
                add_explanation_of_reducing_to_rooted_monomial(m_monomials[i_mon], exp);
                for (lpvar j : factorization)
                    add_explanation_of_reducing_to_rooted_monomial(j, exp);
                m_expl->clear();
                m_expl->add(exp);
                return true;
            }
        }
        return false;
    }
    // here we use the fact
    // xy = 0 -> x = 0 or y = 0
    bool basic_lemma_for_mon_zero_from_monomial_to_factor(lpvar i_mon, const signed_factorization& factorization) {
        if (!vvr(i_mon).is_zero() )
            return false;
        for (lpvar j : factorization) {
            if (vvr(j).is_zero())
                return false;
        }
        lp::lar_term t;
        t.add_coeff_var(rational::one(), i_mon);
        SASSERT(m_lemma->empty());
        m_lemma->push_back(ineq(lp::lconstraint_kind::NE, t, rational::zero()));
        for (lpvar j : factorization) {
            t.clear();
            t.add_coeff_var(rational::one(), j);
            m_lemma->push_back(ineq(lp::lconstraint_kind::EQ, t, rational::zero()));            
        }
        expl_set e;
        factorization.explain(e);
        set_expl(e);
        return true;
    }

    void set_expl(const expl_set & e) {
        m_expl->clear();
        for (lpci ci : e)
            m_expl->push_justification(ci);
    }
    
    bool basic_lemma_for_mon_zero_from_factors_to_monomial(lpvar i_mon, const signed_factorization& factorization) {
        NOT_IMPLEMENTED_YET();
        return false;
    }

    
    bool basic_lemma_for_mon_zero(lpvar i_mon, const signed_factorization& factorization) {
        return 
            basic_lemma_for_mon_zero_from_monomial_to_factor(i_mon, factorization) || 
            basic_lemma_for_mon_zero_from_factors_to_monomial(i_mon, factorization);
    }
            
    bool basic_lemma_for_mon_neutral(const signed_factorization& factorization) {
        NOT_IMPLEMENTED_YET();
        return false;
    }
            
    bool basic_lemma_for_mon_proportionality(const signed_factorization& factorization) {
        NOT_IMPLEMENTED_YET();
        return false;
    }
    
    // use basic multiplication properties to create a lemma
    // for the given monomial
    bool basic_lemma_for_mon(unsigned i_mon) {
        for (auto factorization : binary_factorizations_of_monomial(i_mon, *this)) {
            if (basic_lemma_for_mon_zero(i_mon, factorization) ||
                basic_lemma_for_mon_neutral(factorization) ||
                basic_lemma_for_mon_proportionality(factorization))
                return true;
            
        }
        return false;
    }

    // use basic multiplication properties to create a lemma
    bool basic_lemma(unsigned_vector & to_refine) {
        if (basic_sign_lemma(to_refine))
            return true;

        for (unsigned i : to_refine) {
            if (basic_lemma_for_mon(i)) {
                return true;
            }
        }
        return false;
    }

    void map_monomial_vars_to_monomial_indices(unsigned i) {
        const monomial& m = m_monomials[i];
        for (lpvar j : m.vars()) {
            auto it = m_var_to_mon_indices.find(j);
            if (it == m_var_to_mon_indices.end()) {
                unsigned_vector v;
                v.push_back(i);
                m_var_to_mon_indices[j] = v;
            }
            else {
                it->second.push_back(i);
            }
        }
    }

    void map_vars_to_monomials_and_constraints() {
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
        TRACE("nla_solver", tout << "term size = 2";);
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
    }

    void register_key_mono_in_min_monomials(monomial_coeff const& mc, unsigned i) {

        mono_index_with_sign ms(i, mc.coeff());
        auto it = m_rooted_monomials.find(mc.vars());
        if (it == m_rooted_monomials.end()) {
            vector<mono_index_with_sign> v;
            v.push_back(ms);
            // v is a vector containing a single mono_index_with_sign
            m_rooted_monomials.emplace(mc.vars(), v);
        } 
        else {
            it->second.push_back(ms);
        }
    }
    
    void register_monomial_in_min_map(unsigned i) {
        monomial_coeff mc = canonize_monomial(m_monomials[i]);
        register_key_mono_in_min_monomials(mc, i);        
    }

    void create_rooted_monomials_map() {
        for (unsigned i = 0; i < m_monomials.size(); i++) 
            register_monomial_in_min_map(i);
    }
    
    void init_search() {
        map_vars_to_monomials_and_constraints();
        init_vars_equivalence();
        create_rooted_monomials_map();
        m_expl->clear();
        m_lemma->clear();
    }
    
    lbool check(lp::explanation & exp, lemma& l) {
        TRACE("nla_solver", tout << "check of nla";);
        m_expl =   &exp;
        m_lemma =  &l;
        lp_assert(m_lar_solver.get_status() == lp::lp_status::OPTIMAL);
        unsigned_vector to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }

        if (to_refine.empty())
            return l_true;

        TRACE("nla_solver", tout << "to_refine.size() = " << to_refine.size() << std::endl;);
        
        init_search();
        
        if (basic_lemma(to_refine))
            return l_false;
        
        return l_undef;
    }
    
    void test_factorization(unsigned mon_index, unsigned number_of_factorizations) {
        vector<ineq> lemma;
        m_lemma = & lemma;
        lp::explanation exp;
        m_expl = & exp;
        init_search();

        binary_factorizations_of_monomial fc(mon_index, // 0 is the index of "abcde"
                                             *this);
     
        std::cout << "factorizations = of "; print_var(m_monomials[0].var(), std::cout) << "\n";
        unsigned found_factorizations = 0;
        for (auto f : fc) {
            if (f.is_empty()) continue;
            found_factorizations ++;
            for (lpvar j : f) {
                std::cout << "j = "; print_var(j, std::cout);
            }
            std::cout << "sign = " << f.sign() << std::endl;
        }
        SASSERT(found_factorizations == number_of_factorizations);
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

void solver::test() {
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

    nla.m_imp->test_factorization(0, // 0 is the index of monomial abcde
                                  3); // 3 is the number of expected factorizations

    
}

}
