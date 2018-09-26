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
#include "util/lp/mon_eq.h"
#include "util/lp/lp_utils.h"
namespace nla {
typedef lp::constraint_index     lpci;
typedef std::unordered_set<lpci> expl_set;
typedef nra::mon_eq              mon_eq;
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
        int                  m_sign;
        lpci                 m_c0;
        lpci                 m_c1;

        equiv(lpvar i, lpvar j, int sign, lpci c0, lpci c1) :
            m_i(i),
            m_j(j),
            m_sign(sign),
            m_c0(c0),
            m_c1(c1) {
            SASSERT(m_i != m_j);
        }
    };

    // The map from the variables to m_equivs indices
    // If m_tree[v] == -1 then the variable is a root.
    // Otherwize m_equivs[m_tree[v]].m_i == v or m_equivs[m_tree[v]].m_i == v.
    // m_tree is a spanning tree of the graph of equivs represented by m_equivs
    std::unordered_map<unsigned, unsigned> m_tree;  
    
    // if m_tree[v] is not equal to -1 then m_equivs[v] = (k, v), that is m_equivs[v].m_j = v
    vector<equiv>                     m_equivs;         // all equivalences extracted from constraints
    void clear() {
        m_equivs.clear();
        m_tree.clear();
    }

    unsigned size() const { return m_tree.size(); }

    // we create a spanning tree on all variables participating in an equivalence
    void create_tree() {
        for (unsigned k = 0; k < m_equivs.size(); k++)
            connect_equiv_to_tree(k);
    }

    void add_equiv(lpvar i, lpvar j, int sign, lpci c0, lpci c1) {
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
    lpvar map_to_root(lpvar j, int& sign) const {
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
        int      m_sign; // the monomial sign: -1 or 1
        mono_index_with_sign(unsigned i, int sign) : m_i(i), m_sign(sign) {}
        mono_index_with_sign() {}
    };
    
    vars_equivalence                                       m_vars_equivalence;
    vector<mon_eq>                                         m_monomials;
    // maps the vector of the rooted monomial vars to the list of the indices of monomials having the same rooted monomial
    std::unordered_map<svector<lpvar>, vector<mono_index_with_sign>, hash_svector>
    m_rooted_monomials;
    unsigned_vector                                        m_monomials_lim;
    lp::lar_solver&                                        m_lar_solver;
    std::unordered_map<lpvar, unsigned_vector>             m_var_to_mon_indices;

    // mon_eq.var()  -> monomial index
    std::unordered_map<lpvar, unsigned>                    m_var_to_its_monomial;
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
        m_monomials.push_back(mon_eq(v, sz, vs));
        m_var_to_its_monomial[v] = m_monomials.size() - 1;
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
    bool check_monomial(const mon_eq& m) {
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
    // If we see that monomials are the same up to the sign,
    // but the values are not equal up to the sign, we generate a lemman and a conflict explanation
    bool generate_basic_lemma_for_mon_sign_var_other_mon(
        unsigned i_mon,
        unsigned j_var,
        const unsigned_vector & mon_vars,
        const mon_eq& other_m, int sign) {
        if (mon_vars.size() != other_m.size())
            return false;

        auto other_vars_copy = other_m.vars();
        int other_sign = 1;
        reduce_monomial_to_canonical(other_vars_copy, other_sign);
        if (mon_vars == other_vars_copy &&
            values_are_different(m_monomials[i_mon].var(), sign * other_sign, other_m.var())) {
            fill_explanation_and_lemma_sign(m_monomials[i_mon],
                                            other_m,
                                            sign * other_sign);
            TRACE("nla_solver", tout << "lemma generated\n";);
            return true;
        }
            
        return false;
    }

    bool values_are_different(lpvar j, int sign, lpvar k) const {
        SASSERT(sign == 1 || sign == -1);
        return ! ( sign * m_lar_solver.get_column_value(j) == m_lar_solver.get_column_value(k));
    }

    void add_explanation_of_reducing_to_rooted_monomial(const mon_eq& m, expl_set & exp) const {
        m_vars_equivalence.add_explanation_of_reducing_to_rooted_monomial(m, exp);
    }

    void add_explanation_of_reducing_to_rooted_monomial(lpvar j, expl_set & exp) const {
        auto it = m_var_to_its_monomial.find(j);
        if (it == m_var_to_its_monomial.end())
            return; // j is not a var of a monomial
        add_explanation_of_reducing_to_rooted_monomial(m_monomials[it->second], exp);
    }

    

    
    std::ostream& print_monomial(const mon_eq& m, std::ostream& out) const {
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
    void fill_explanation_and_lemma_sign(const mon_eq& a, const mon_eq & b, int sign) {
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
        lp::lar_term t;
        t.add_coeff_var(rational(1), a.var());
        t.add_coeff_var(rational(- sign), b.var());
        TRACE("nla_solver", print_explanation_and_lemma(tout););
        ineq in(lp::lconstraint_kind::NE, t, rational::zero());
        m_lemma->push_back(in);
    }
    
    /**
     * \brief <go over monomials containing j_var and generate the sign lemma
     */
    bool generate_basic_lemma_for_mon_sign_var(unsigned i_mon,
                                               unsigned j_var, const svector<lpvar>& mon_vars, int sign) {
        auto it = m_var_lists.find(j_var);
        for (auto other_i_mon : it->second) {
            if (other_i_mon == i_mon) continue;
            if (generate_basic_lemma_for_mon_sign_var_other_mon(
                    i_mon,
                    j_var,
                    mon_vars,
                    m_monomials[other_i_mon],
                    sign))
                return true;
        }
        return false;
    }

    // Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
    // 
    svector<lpvar> reduce_monomial_to_canonical(const svector<lpvar> & vars, int & sign) const {
        svector<lpvar> ret;
        sign = 1;
        for (unsigned i = 0; i < vars.size(); i++) {
            unsigned root = m_vars_equivalence.map_to_root(vars[i], sign);
            SASSERT(m_vars_equivalence.is_root(root));
            ret.push_back(m_vars_equivalence.map_to_root(vars[i], sign));
        }
        std::sort(ret.begin(), ret.end());
        return ret;
    }

    /**
     * \brief <generate lemma by using the fact that -ab = (-a)b) and
     -ab = a(-b)
    */
    bool generate_basic_lemma_for_mon_sign(unsigned i_mon) {
        if (m_vars_equivalence.empty()) {
            return false;
        }
        const mon_eq& m_of_i = m_monomials[i_mon];
        int sign = 1;
        
        auto mon_vars =  m_of_i.vars();
        reduce_monomial_to_canonical(mon_vars, sign);
        for (unsigned j_var : mon_vars)
            if (generate_basic_lemma_for_mon_sign_var(i_mon, j_var, mon_vars, sign))
                return true;
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
        auto it = m_var_lists.find(j);
        if (it == m_var_lists.end())
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
        const mon_eq m = m_monomials[i_mon];
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
    bool generate_basic_lemma_for_mon_zero(unsigned i_mon) {
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

    void create_lemma_one_of_the_factors_is_zero(const mon_eq& m) {
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
        if (!m_lar_solver.column_has_upper_bound(j) ||
            !m_lar_solver.column_has_lower_bound(j))
            return false;
        if (m_lar_solver.get_upper_bound(j) != lp::zero_of_type<lp::impq>() ||
            m_lar_solver.get_lower_bound(j) != lp::zero_of_type<lp::impq>())
            return false;
        return true;
    }
    
    std::ostream & print_ineq(const ineq & in, std::ostream & out) const {
        m_lar_solver.print_term(in.m_term, out);
        out << " " << lp::lconstraint_kind_string(in.m_cmp) << " 0";
        return out;
    }

    std::ostream & print_var(lpvar j, std::ostream & out) const {
        bool monomial = false;
        for (const mon_eq & m : m_monomials) {
            if (j == m.var()) {
                monomial = true;
                print_monomial(m, out);
                out << " = " << m_lar_solver.get_column_value(j);;
                break;
            }
        }
        if (!monomial)
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
    bool get_one_of_var(lpvar j, int & sign) {
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
                sign = 1;
            }
            else if (ub == -rational(1)) {
                sign = -1;
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

    
    void get_large_and_small_indices_of_monomimal(const mon_eq& m,
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
     * \brief <generate lemma by using the fact that 1*x = x or x*1 = x>
     * v is the value of monomial, vars is the array of reduced to minimum variables of the monomial
     */
    bool generate_basic_neutral_for_reduced_monomial(const mon_eq & m, const rational & v, const svector<lpvar> & vars) {
        vector<mono_index_with_sign> ones_of_mon = get_ones_of_monomimal(vars);
        
        // if abs(m.vars()[j]) is 1, then ones_of_mon[j] = sign, where sign is 1 in case of m.vars()[j] = 1, or -1 otherwise.
        if (ones_of_mon.empty()) {
            return false;
        }
        if (m_rooted_monomials.empty() && m.size() > 2)
            create_min_mon_map();
        
        return process_ones_of_mon(m, ones_of_mon, vars, v);
    }
    /**
     * \brief <generate lemma by using the fact that 1*x = x or x*1 = x>
     */    
    bool generate_basic_lemma_for_mon_neutral(unsigned i_mon) {
        const mon_eq & m = m_monomials[i_mon];
        int sign;
        svector<lpvar> reduced_vars = reduce_monomial_to_canonical(m.vars(), sign);
        rational v = m_lar_solver.get_column_value_rational(m.var());
        if (sign == -1)
            v = -v;
        return generate_basic_neutral_for_reduced_monomial(m, v, reduced_vars);
    }

    // returns the variable m_i, of a monomial if found and sets the sign,
    bool find_monomial_of_vars(const svector<lpvar>& vars, unsigned &j, int & sign) const {
        if (vars.size() == 1) {
            j = vars[0];
            sign = 1;
            return true;
        }
        auto it = m_rooted_monomials.find(vars);
        if (it == m_rooted_monomials.end()) {
            return false;
        }

        const mono_index_with_sign & mi = *(it->second.begin());
        sign = mi.m_sign;
        j = mi.m_i;
        return true;
    }

    bool find_compimenting_monomial(const svector<lpvar> & vars, lpvar & j) {
        int other_sign;
        if (!find_monomial_of_vars(vars, j, other_sign)) {
            return false;
        }
        return true;
    }
    
    bool find_lpvar_and_sign_with_wrong_val(
        const mon_eq& m,
        svector<lpvar> & vars,
        const rational& v,
        int sign,
        lpvar& j) {
        int other_sign;
        if (!find_monomial_of_vars(vars, j, other_sign)) {
            return false;
        }
        sign *= other_sign;
        rational other_val = m_lar_solver.get_column_value_rational(j);
        return sign * other_val != v;                
    }

    void add_explanation_of_one(const mono_index_with_sign & mi) {
        SASSERT(false);
    }

    void generate_equality_for_neutral_case(const mon_eq & m,
                                            const unsigned_vector & mask,
                                            const vector<mono_index_with_sign>& ones_of_monomial, int sign, lpvar j) {
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
    bool process_ones_of_mon(const mon_eq& m,
                             const vector<mono_index_with_sign>& ones_of_monomial, const svector<lpvar> &min_vars,
                             const rational& v) {
        unsigned_vector mask(ones_of_monomial.size(), (unsigned) 0);
        auto vars = min_vars;
        int sign = 1;
        // We cross out the ones representing the mask from vars
        do {
            for (unsigned k = 0; k < mask.size(); k++) {
                if (mask[k] == 0) {
                    mask[k] = 1;
                    sign *= ones_of_monomial[k].m_sign;
                    TRACE("nla_solver", tout << "index m_i = " << ones_of_monomial[k].m_i;);
                    vars.erase(vars.begin() + ones_of_monomial[k].m_i);
                    std::sort(vars.begin(), vars.end());
                    // now the value of vars has to be v*sign
                    lpvar j;
                    if (!find_lpvar_and_sign_with_wrong_val(m, vars, v, sign, j))
                        return false;
                    generate_equality_for_neutral_case(m, mask, ones_of_monomial, j, sign);
                    return true;
                } else {
                    SASSERT(mask[k] == 1);
                    sign *= ones_of_monomial[k].m_sign;
                    mask[k] = 0;
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
            SASSERT(false);
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

    void large_lemma_for_proportion_case_on_known_signs(const mon_eq& m,
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
    
    bool large_lemma_for_proportion_case(const mon_eq& m, const unsigned_vector & mask,
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

    bool small_lemma_for_proportion_case(const mon_eq& m, const unsigned_vector & mask,
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
    void small_lemma_for_proportion_case_on_known_signs(const mon_eq& m, unsigned j, int mon_sign, int j_sign) {
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
        unsigned_vector mask(large.size(), (unsigned) 0); // init mask by zeroes
        const auto & m = m_monomials[i_mon];
        int sign;
        auto vars = reduce_monomial_to_canonical(m.vars(), sign);
        auto vars_copy = vars;
        auto v = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // We cross out from vars the "large" variables represented by the mask
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k] == 0) {
                mask[k] = 1;
                TRACE("nla_solver", tout << "large[" << k << "] = " << large[k];);
                SASSERT(std::find(vars.begin(), vars.end(), vars_copy[large[k]]) != vars.end());
                vars.erase(vars_copy[large[k]]);
                std::sort(vars.begin(), vars.end());
                // now the value of vars has to be v*sign
                lpvar j;
                if (find_compimenting_monomial(vars, j) &&
                    large_lemma_for_proportion_case(m, mask, large, j)) {
                    TRACE("nla_solver", print_explanation_and_lemma(tout););
                    return true;
                }
            } else {
                SASSERT(mask[k] == 1);
                mask[k] = 0;
                vars.push_back(vars_copy[large[k]]); // vars might become unsorted
            }
        }
        return false; // we exhausted the mask and did not find the compliment monomial
    }

    bool small_basic_lemma_for_mon_proportionality(unsigned i_mon, const unsigned_vector& _small) {
        unsigned_vector mask(_small.size(), (unsigned) 0); // init mask by zeroes
        const auto & m = m_monomials[i_mon];
        int sign;
        auto vars = reduce_monomial_to_canonical(m.vars(), sign);
        auto vars_copy = vars;
        auto v = lp::abs(m_lar_solver.get_column_value_rational(m.var()));
        // We cross out from vars the "large" variables represented by the mask
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k] == 0) {
                mask[k] = 1;
                TRACE("nla_solver", tout << "_small[" << k << "] = " << _small[k];);
                SASSERT(std::find(vars.begin(), vars.end(), vars_copy[_small[k]]) != vars.end());
                vars.erase(vars_copy[_small[k]]);
                std::sort(vars.begin(), vars.end());
                // now the value of vars has to be v*sign
                lpvar j;
                if (find_compimenting_monomial(vars, j) &&
                    small_lemma_for_proportion_case(m, mask, _small, j)) {
                    TRACE("nla_solver", print_explanation_and_lemma(tout););
                    return true;
                }
            } else {
                SASSERT(mask[k] == 1);
                mask[k] = 0;
                vars.push_back(vars_copy[_small[k]]); // vars might become unsorted
            }
        }

        return false; // we exhausted the mask and did not find the compliment monomial
    }

    // we derive a lemma from |x| >= 1 => |xy| >= |y| or |x| <= 1 => |xy| <= |y|  
    bool basic_lemma_for_mon_proportionality_from_factors_to_product(unsigned i_mon) {
        const mon_eq & m = m_monomials[i_mon];
        unsigned_vector large;
        unsigned_vector _small;
        get_large_and_small_indices_of_monomimal(m, large, _small);
        TRACE("nla_solver", tout << "large size = " << large.size() << ", _small size = " << _small.size(););
        if (large.empty() && _small.empty())
            return false;
        
        if (m_rooted_monomials.empty())
            create_min_mon_map();

        if (!large.empty() && large_basic_lemma_for_mon_proportionality(i_mon, large))
            return true;

        if (!_small.empty() && small_basic_lemma_for_mon_proportionality(i_mon, _small))
            return true;

        return false;
    }

    // Using the following theorems
    // |ab| >= |b| iff |a| >= 1 or b = 0
    // |ab| <= |b| iff |a| <= 1 or b = 0
    // and their commutative variants
    bool generate_basic_lemma_for_mon_proportionality(unsigned i_mon) {
        TRACE("nla_solver", tout << "generate_basic_lemma_for_mon_proportionality";);
        if (basic_lemma_for_mon_proportionality_from_factors_to_product(i_mon))
            return true;

        return basic_lemma_for_mon_proportionality_from_product_to_factors(i_mon);
    }

    struct signed_binary_factorization {
        unsigned m_j; // var index : the var can correspond to a monomial var or just to a var 
        unsigned m_k; // var index : the var can correspond to a monomial var or just to a var
        int      m_sign;
        // the default constructor
        signed_binary_factorization() :m_j(-1) {}
        signed_binary_factorization(unsigned j, unsigned k, int sign) :
            m_j(j),
            m_k(k),
            m_sign(sign) {}

    };
    
    struct binary_factorizations_of_monomial {
        unsigned         m_i_mon;
        const imp&       m_imp;
        const mon_eq&    m_mon;
        unsigned_vector  m_rooted_vars;
        int              m_sign; // the sign appears after reducing the monomial "mm_mon" to the rooted one
        
        binary_factorizations_of_monomial(unsigned i_mon, const imp& s) :
            m_i_mon(i_mon),
            m_imp(s),
            m_mon(m_imp.m_monomials[i_mon]) {
            m_rooted_vars = m_imp.reduce_monomial_to_canonical(
                m_imp.m_monomials[m_i_mon].vars(), m_sign);
        }

        
        
        struct const_iterator {
            // fields
            unsigned_vector        m_mask;
            const binary_factorizations_of_monomial&   m_binary_factorizations;

            //typedefs
            typedef const_iterator self_type;
            typedef signed_binary_factorization value_type;
            typedef const signed_binary_factorization reference;
            typedef int difference_type;
            typedef std::forward_iterator_tag iterator_category;

            void init_vars_by_the_mask(unsigned_vector & k_vars, unsigned_vector & j_vars) const {
                for (unsigned j = 0; j < m_mask.size(); j++) {
                    if (m_mask[j] == 1) {
                        k_vars.push_back(m_binary_factorizations.m_rooted_vars[j]);
                    } else {
                        j_vars.push_back(m_binary_factorizations.m_rooted_vars[j]);
                    }
                }
            }
            
            bool get_factors(unsigned& k, unsigned& j, unsigned & k_mon, unsigned & j_mon, int& sign) const {
                unsigned_vector k_vars;
                unsigned_vector j_vars;
                init_vars_by_the_mask(k_vars, j_vars);
                SASSERT(!k_vars.empty() && !j_vars.empty());
                std::sort(k_vars.begin(), k_vars.end());
                std::sort(j_vars.begin(), j_vars.end());

                int k_sign, j_sign;
                if (k_vars.size() == 1) {
                    k = k_vars[0];
                    k_sign = 1;
                    k_mon = -1;
                } else if (!m_binary_factorizations.m_imp.find_monomial_of_vars(k_vars, k, k_sign)) {
                    return false;
                }
                if (j_vars.size() == 1) {
                    j = j_vars[0];
                    j_sign = 1;
                } else if (!m_binary_factorizations.m_imp.find_monomial_of_vars(j_vars, j, j_sign)) {
                    return false;
                }
                sign = j_sign * k_sign;
                return true;
            }

            reference operator*() const {
                unsigned j, k; int sign;
                unsigned j_mon, k_mon;
                if (!get_factors(j, k, j_mon, k_mon, sign))
                    return signed_binary_factorization();
                return signed_binary_factorization(j, k, m_binary_factorizations.m_sign * sign);
            }
            
            void advance_mask() {
                for (unsigned k = 0; k < m_mask.size(); k++) {
                    if (m_mask[k] == 0){
                        m_mask[k] = 1;
                        break;
                    } else {
                        m_mask[k] = 0;
                    }
                }
            }

            
            self_type operator++() {  self_type i = *this; operator++(1); return i;  }
            self_type operator++(int) { advance_mask(); return *this; }

            const_iterator(const unsigned_vector& mask, const binary_factorizations_of_monomial & f) : m_mask(mask), m_binary_factorizations(f) {}
            
            bool operator==(const self_type &other) const {
                return m_mask == other.m_mask;
            }
            bool operator!=(const self_type &other) const { return !(*this == other); }
        };

        const_iterator begin() const {
            unsigned_vector mask(m_mon.vars().size(), static_cast<lpvar>(0));
            mask[0] = 1; 
            return const_iterator(mask, *this);
        }
        
        const_iterator end() const {
            unsigned_vector mask(m_mon.vars().size(), 1);
            return const_iterator(mask, *this);
        }
    };

    // we derive a lemma from |x| >= 1 || |y| = 0 => |xy| >= |y|
    bool lemma_for_proportional_factors_on_vars_ge(lpvar i, lpvar j, lpvar k) {
        if (!(abs(vvr(j)) >= rational(1) || vvr(k).is_zero()))
            return false;
        // the precondition holds
        if (! (abs(vvr(i)) >= abs(vvr(k)))) {
            SASSERT(false); // create here
            return true;
        }
        return false;
    }

    // we derive a lemma from |x| <= 1 || |y| = 0 => |xy| <= |y|
    bool lemma_for_proportional_factors_on_vars_le(lpvar i, lpvar j, lpvar k) {
        TRACE("nla_solver",
              tout << "i=";
              print_var(i, tout);
              tout << "j=";
              print_var(j, tout);
              tout << "k=";
              print_var(k, tout););
              
        if (!(abs(vvr(j)) <= rational(1) || vvr(k).is_zero()))
            return false;
        // the precondition holds
        if (! (abs(vvr(i)) <= abs(vvr(k)))) {
            SASSERT(false); // create here
            return true;
        }
        return false;
    }

    
    // we derive a lemma from |x| >= 1 || |y| = 0 => |xy| >= |y|, or the similar of <= 
    bool lemma_for_proportional_factors(unsigned i_mon, const signed_binary_factorization& f) {
        lpvar var_of_mon = m_monomials[i_mon].var();
        TRACE("nla_solver",
              m_lar_solver.print_constraints(tout);
              tout << "\n";
              print_var(var_of_mon, tout);
              tout << " is factorized as ";
              if (f.m_sign == -1) { tout << "-";}
              print_var(f.m_j, tout);
              tout << "*";
              print_var(f.m_k, tout);
              );
        if (lemma_for_proportional_factors_on_vars_ge(var_of_mon, f.m_j, f.m_k)
            || lemma_for_proportional_factors_on_vars_ge(var_of_mon, f.m_k, f.m_j))
            return true;
        if (lemma_for_proportional_factors_on_vars_le(var_of_mon, f.m_j, f.m_k)
            || lemma_for_proportional_factors_on_vars_le(var_of_mon, f.m_k, f.m_j))
            return true;
        return false;
    }
    // we derive a lemma from |xy| >= |y| => |x| >= 1 || |y| = 0
    bool basic_lemma_for_mon_proportionality_from_product_to_factors(unsigned i_mon) {
        for (auto factorization : binary_factorizations_of_monomial(i_mon, *this)) {
            if (lemma_for_proportional_factors(i_mon, factorization)) {
                expl_set exp;
                add_explanation_of_reducing_to_rooted_monomial(m_monomials[i_mon], exp);
                add_explanation_of_reducing_to_rooted_monomial(factorization.m_j, exp);
                add_explanation_of_reducing_to_rooted_monomial(factorization.m_k, exp);
                m_expl->clear();
                m_expl->add(exp);
                return true;
            }
        }
        //  return true;
        SASSERT(false);
        return false;
    }

    // use basic multiplication properties to create a lemma
    // for the given monomial
    bool generate_basic_lemma_for_mon(unsigned i_mon) {
        return generate_basic_lemma_for_mon_sign(i_mon)
            || generate_basic_lemma_for_mon_zero(i_mon)
            || generate_basic_lemma_for_mon_neutral(i_mon)
            || generate_basic_lemma_for_mon_proportionality(i_mon);
    }

    // use basic multiplication properties to create a lemma
    bool generate_basic_lemma(unsigned_vector & to_refine) {
        for (unsigned i : to_refine) {
            if (generate_basic_lemma_for_mon(i)) {
                return true;
            }
        }
        return false;
    }

    void map_monomial_vars_to_monomial_indices(unsigned i) {
        const mon_eq& m = m_monomials[i];
        for (lpvar j : m.vars()) {
            auto it = m_var_to_mon_indices.find(j);
            if (it == m_var_to_mon_indices.end()) {
                unsigned_vector v;
                v.push_back(i);
                m_var_lists[j] = v;
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
            if (!s.column_has_upper_bound(j) ||
                !s.column_has_lower_bound(j))
                continue;
            if (s.get_upper_bound(j) != lp::zero_of_type<lp::impq>() ||
                s.get_lower_bound(j) != lp::zero_of_type<lp::impq>())
                continue;
            TRACE("nla_solver", tout << "term = "; s.print_term(*s.terms()[i], tout););
            add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
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
        int sign = (seen_minus && seen_plus)? 1 : -1;
        m_vars_equivalence.add_equiv(i, j, sign, c0, c1);
    }

    
    // x is equivalent to y if x = +- y
    void init_vars_equivalence() {
        m_vars_equivalence.clear();
        collect_equivs();
        m_vars_equivalence.create_tree();
    }

    void register_key_mono_in_min_monomials(const svector<lpvar>& key, unsigned i, int sign) {
        mono_index_with_sign ms(i, sign);
        auto it = m_rooted_monomials.find(key);
        if (it == m_rooted_monomials.end()) {
            vector<mono_index_with_sign> v;
            v.push_back(ms);
            // v is a vector containing a single mono_index_with_sign
            m_rooted_monomials.emplace(key, v);
        } else {
            it->second.push_back(ms);
        }
    }
    
    void register_monomial_in_min_map(unsigned i) {
        const mon_eq& m = m_monomials[i];
        int sign;
        svector<lpvar> key = reduce_monomial_to_canonical(m.vars(), sign);
        register_key_mono_in_min_monomials(key, i, sign);
    }
    
    void create_min_mon_map() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            register_monomial_in_min_map(i);
    }
    
    void init_search() {
        map_vars_to_monomials_and_constraints();
        init_vars_equivalence();
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
        
        if (generate_basic_lemma(to_refine))
            return l_false;
        
        return l_undef;
    }
    void test() {
        std::cout << "test called\n";
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
    reslimit l;
    params_ref p;
    imp i(s, l, p);
    i.test();
}

}
