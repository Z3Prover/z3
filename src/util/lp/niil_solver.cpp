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
#include "util/lp/niil_solver.h"
#include "util/map.h"
#include "util/lp/mon_eq.h"
#include "util/lp/lp_utils.h"
namespace niil {
typedef lp::constraint_index     lpci;
typedef std::unordered_set<lpci> expl_set;
typedef nra::mon_eq              mon_eq;
typedef lp::var_index            lpvar;

struct hash_svector {
    size_t operator()(const svector<unsigned> & v) const {
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
            m_c1(c1)
        {
            SASSERT(i > j);
        }
    };

    struct eq_var {
        lpvar m_var;
        int   m_sign;
        expl_set m_explanation;
        eq_var(const equiv& e) :
            m_var(e.m_j),
            m_sign(e.m_sign) {
            m_explanation.insert(e.m_c0); m_explanation.insert(e.m_c1);
        }
        void improve(const equiv & e) {
            SASSERT(e.m_j > m_var);
            m_var = e.m_j;
            m_sign *= e.m_sign;
            m_explanation.insert(e.m_c0); m_explanation.insert(e.m_c1);
        }
    };
    std::unordered_map<lpvar, eq_var> m_map;         // the resulting mapping
    vector<equiv>                     m_equivs;         // all equivalences extracted from constraints
    void clear() {
        m_equivs.clear();
        m_map.clear();
    }

    unsigned size() const { return m_map.size(); }

    void add_equivalence_maybe(const lp::lar_term *t, lpci c0, lpci c1) {
        if (t->size() != 2 || ! t->m_v.is_zero())
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
        SASSERT(i != j && i != static_cast<lpvar>(-1));
        if (i < j) { // swap 
            lpvar tmp = i;
            i = j;
            j = tmp;
        }
        int sign = (seen_minus && seen_plus)? 1 : -1;
        m_equivs.push_back(equiv(i, j, sign, c0, c1));
    }

    void collect_equivs(const lp::lar_solver& s) {
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
            add_equivalence_maybe(s.terms()[i], s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
        }
    }

    void create_map() {
        bool progress;
        do {
            progress = false;
            for (const auto & e : m_equivs) {
                unsigned i = e.m_i;
                auto it = m_map.find(i);
                if (it == m_map.end()) {
                    m_map.emplace(i, eq_var(e));
                    progress = true;
                } else {
                    if (it->second.m_var > e.m_j) {
                        it->second.improve(e);
                        progress = true;
                    }
                }
            }
        } while(progress);
    }
        
    void init(const lp::lar_solver& s) {
        clear();
        collect_equivs(s);
        create_map();
    }

    bool empty() const {
        return m_map.empty();
    }

    // the sign is flipped if needed
    lpvar map_to_min(lpvar j, int& sign) const {
        auto it = m_map.find(j);
        if (it == m_map.end())
            return j;

        if (it->second.m_sign == -1) {
            sign = -sign;
        }
        return it->second.m_var;
    }

    template <typename T>
    void add_explanation_of_reducing_to_mininal_monomial(const T & m, expl_set & exp) const {
        for (auto j : m)
            add_equiv_exp(j, exp);
    }
        
    void add_equiv_exp(lpvar j, expl_set & exp) const {
        auto it = m_map.find(j);
        if (it == m_map.end())
            return;
        for (auto k : it->second.m_explanation)
            exp.insert(k);
    }
}; // end of vars_equivalence

struct solver::imp {

    typedef lp::lar_base_constraint lpcon;
    
    struct var_lists {
        svector<unsigned>                 m_monomials; // of the var
        const svector<unsigned>& mons() const { return m_monomials;}
        svector<unsigned>& mons() { return m_monomials;}
        void add_monomial(unsigned i) { mons().push_back(i); }
    };

    struct mono_index_with_sign {
        unsigned m_i; // the monomial index
        int      m_sign; // the monomial sign: -1 or 1
        mono_index_with_sign(unsigned i, int sign) : m_i(i), m_sign(sign) {}
        mono_index_with_sign() {}
    };
    
    vars_equivalence                                       m_vars_equivalence;
    vector<mon_eq>                                         m_monomials;
    // maps the vector of the minimized monomial vars to the list of monomial indices having the same vector
    std::unordered_map<svector<lpvar>, vector<mono_index_with_sign>, hash_svector>
                                                           m_minimal_monomials;
    unsigned_vector                                        m_monomials_lim;
    lp::lar_solver&                                        m_lar_solver;
    std::unordered_map<lpvar, var_lists>                   m_var_lists;
    lp::explanation *                                      m_expl;
    lemma *                                                m_lemma;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        : m_lar_solver(s)
          // m_limit(lim),
          // m_params(p)
    {
    }

    void add(lpvar v, unsigned sz, lpvar const* vs) {
        m_monomials.push_back(mon_eq(v, sz, vs));
    }
    
    void push() {
        m_monomials_lim.push_back(m_monomials.size());
    }
    
    void pop(unsigned n) {
        if (n == 0) return;
        m_monomials.shrink(m_monomials_lim[m_monomials_lim.size() - n]);
        m_monomials_lim.shrink(m_monomials_lim.size() - n);       
    }

    bool check_monomial(const mon_eq& m) {
        SASSERT(m_lar_solver.get_column_value(m.var()).is_int());
        const rational & model_val = m_lar_solver.get_column_value_rational(m.var());
        rational r(1);
        for (auto j : m.m_vs) {
            r *= m_lar_solver.get_column_value_rational(j);
        }
        return r == model_val;
    }
    
    /**
     * \brief <here we have two monomials, i_mon and other_m, examined for "sign" equivalence>
     */
    bool generate_basic_lemma_for_mon_sign_var_other_mon(
        unsigned i_mon,
        unsigned j_var,
        const svector<unsigned> & mon_vars,
        const mon_eq& other_m, int sign) {
        if (mon_vars.size() != other_m.size())
            return false;

        auto other_vars_copy = other_m.m_vs;
        int other_sign = 1;
        reduce_monomial_to_minimal(other_vars_copy, other_sign);
        if (mon_vars == other_vars_copy &&
            values_are_different(m_monomials[i_mon].var(), sign * other_sign, other_m.var())) {
            fill_explanation_and_lemma_sign(m_monomials[i_mon],
                                       other_m,
                                       sign * other_sign);
            TRACE("niil_solver", tout << "lemma generated\n";);
            return true;
        }
            
        return false;
    }

    bool values_are_different(lpvar j, int sign, lpvar k) const {
        SASSERT(sign == 1 || sign == -1);
        return ! ( sign * m_lar_solver.get_column_value(j) == m_lar_solver.get_column_value(k));
    }

    void add_explanation_of_reducing_to_mininal_monomial(const mon_eq& m, expl_set & eset) const {
        m_vars_equivalence.add_explanation_of_reducing_to_mininal_monomial(m, eset);
    }

    std::ostream& print_monomial(const mon_eq& m, std::ostream& out) {
        out << m_lar_solver.get_column_name(m.var()) << " = ";
        for (unsigned k = 0; k < m.size(); k++) {
            out << m_lar_solver.get_column_name(m.m_vs[k]);
            if (k + 1 < m.m_vs.size()) out << "*";
        }
        return out;
    }

    std::ostream& print_explanation(std::ostream& out) const {
        for (auto &p : *m_expl) {
            m_lar_solver.print_constraint(p.second, out) << "\n";
        }
        return out;
    }

    // the monomials should be equal by modulo sign, but they are not equal in the model module sign
    void fill_explanation_and_lemma_sign(const mon_eq& a, const mon_eq & b, int sign) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_explanation_of_reducing_to_mininal_monomial(a, expl);
        add_explanation_of_reducing_to_mininal_monomial(b, expl);
        m_expl->clear();
        m_expl->add(expl);
        TRACE("niil_solver",
              tout << "used constraints: ";
              for (auto &p : *m_expl)
                  m_lar_solver.print_constraint(p.second, tout); tout << "\n";
              );
        lp::lar_term t;
        t.add_monomial(rational(1), a.var());
        t.add_monomial(rational(- sign), b.var());
        TRACE("niil_solver", print_explanation_and_lemma(tout););
        ineq in(lp::lconstraint_kind::NE, t);
        m_lemma->push_back(in);
    }
    
    /**
     * \brief <go over monomials containing j_var>
     */
    bool generate_basic_lemma_for_mon_sign_var(unsigned i_mon,
                                               unsigned j_var, const svector<lpvar>& mon_vars, int sign) {
        auto it = m_var_lists.find(j_var);
        for (auto other_i_mon : it->second.mons()) {
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

    // replaces each variable by a smaller one and flips the sing if the var comes with a minus
    svector<lpvar> reduce_monomial_to_minimal(const svector<lpvar> & vars, int & sign)  {
        svector<lpvar> ret;
        sign = 1;
        for (unsigned i = 0; i < vars.size(); i++) {
            ret.push_back(m_vars_equivalence.map_to_min(vars[i], sign));
        }
        std::sort(ret.begin(), ret.end());
        return ret;
    }

    /**
     * \brief <generate lemma by using the fact that (-(ab) = (-a)b)>
     */
    bool generate_basic_lemma_for_mon_sign(unsigned i_mon) {
        if (m_vars_equivalence.empty()) {
            return false;
        }
        const mon_eq& m_of_i = m_monomials[i_mon];
        int sign = 1;
        
        auto mon_vars =  m_of_i.m_vs;
        reduce_monomial_to_minimal(mon_vars, sign);
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
        for (lpvar j : m.m_vs) {
            int s = get_mon_sign_zero_var(j, strict);
            if (s == 2)
                return 2;
            if (s == 0)
                return 0;
            sign *= s;
        }
        return sign;
    }
    
    bool generate_basic_lemma_for_mon_zero(unsigned i_mon) {
        m_expl->clear();
        const rational & mon_val = m_lar_solver.get_column_value(m_monomials[i_mon].var()).x;
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
            return false;
        }
        lp::lar_term t;
        t.add_monomial(rational(1), m_monomials[i_mon].var());
        t.m_v = -rs;
        ineq in(kind, t);
        m_lemma->push_back(in);
        TRACE("niil_solver", print_explanation_and_lemma(tout););
        return true;
    }

    
    std::ostream & print_ineq(ineq & in, std::ostream & out) const {
        m_lar_solver.print_term(in.m_term, out);
        out << " " << lp::lconstraint_kind_string(in.m_cmp) << " 0";
        return out;
    }

    std::ostream & print_lemma(lemma& l, std::ostream & out) const {
        for (auto & in: l) {
            out << "("; print_ineq(in, out) << ")";
        }
        return out;
    }

    std::ostream & print_explanation_and_lemma(std::ostream & out) const {
        out << "explanation:\n"; print_explanation(out) << "\nlemma\n:" ; print_lemma(*m_lemma, out) << "\n";
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
        TRACE("niil_solver", tout << "get_ones_of_monomimal";);
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
                                                  svector<unsigned> & large,
                                                  svector<unsigned> & _small) {

        for (unsigned i = 0; i < m.m_vs.size(); ++i) {
            unsigned j = m.m_vs[i];
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
        
        // if abs(m.m_vs[j]) is 1, then ones_of_mon[j] = sign, where sign is 1 in case of m.m_vs[j] = 1, or -1 otherwise.
        if (ones_of_mon.empty()) {
            return false;
        }
        if (m_minimal_monomials.empty() && m.size() > 2)
            create_min_map();
        
        return process_ones_of_mon(m, ones_of_mon, vars, v);
    }
    /**
     * \brief <generate lemma by using the fact that 1*x = x or x*1 = x>
     */    
    bool generate_basic_lemma_for_mon_neutral(unsigned i_mon) {
        const mon_eq & m = m_monomials[i_mon];
        int sign;
        svector<lpvar> reduced_vars = reduce_monomial_to_minimal(m.m_vs, sign);
        rational v = m_lar_solver.get_column_value_rational(m.m_v);
        if (sign == -1)
            v = -v;
        return generate_basic_neutral_for_reduced_monomial(m, v, reduced_vars);
    }

    // returns the variable m_i, of a monomial if found and sets the sign,
    // if the 
    bool find_monomial_of_vars(const svector<lpvar>& vars, unsigned &j, int & sign) {
        if (vars.size() == 1) {
            j = vars[0];
            sign = 1;
            return true;
        }
        auto it = m_minimal_monomials.find(vars);
        if (it == m_minimal_monomials.end()) {
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
                                            const svector<unsigned> & mask,
                                            const vector<mono_index_with_sign>& ones_of_monomial, int sign, lpvar j) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_explanation_of_reducing_to_mininal_monomial(m, expl);
        m_expl->clear();
        m_expl->add(expl);
        for (unsigned k : mask) {
            add_explanation_of_one(ones_of_monomial[k]);
        }
        lp::lar_term t;
        t.add_monomial(rational(1), m.var());
        t.add_monomial(rational(- sign), j);
        ineq in(lp::lconstraint_kind::EQ, t);
        m_lemma->push_back(in);
        TRACE("niil_solver", print_explanation_and_lemma(tout););
    }
    
    // vars here are minimal vars for m.vs
    bool process_ones_of_mon(const mon_eq& m,
                             const vector<mono_index_with_sign>& ones_of_monomial, const svector<lpvar> &min_vars,
                             const rational& v) {
        svector<unsigned> mask(ones_of_monomial.size(), (unsigned) 0);
        auto vars = min_vars;
        int sign = 1;
        // We cross out the ones representing the mask from vars
        do {
            for (unsigned k = 0; k < mask.size(); k++) {
                if (mask[k] == 0) {
                    mask[k] = 1;
                    sign *= ones_of_monomial[k].m_sign;
                    TRACE("niil_solver", tout << "index m_i = " << ones_of_monomial[k].m_i;);
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
    bool large_lemma_for_proportion_case(const mon_eq& m, const svector<unsigned> & mask,
                                         const svector<unsigned> & large, unsigned j) {
        TRACE("niil_solver", );
        const rational j_val = m_lar_solver.get_column_value_rational(j);
        const rational m_val = lp::abs(m_lar_solver.get_column_value_rational(m.m_v));
        // since the masked factor is greater than or equal to one
        // j_val has to be less than or equal to m_val
        int sign = j_val < - m_val? -1: (j_val > m_val)? 1: 0;
        if (sign == 0) // abs(j_val) <= m_val which is not a conflict
            return false;
        expl_set expl;
        add_explanation_of_reducing_to_mininal_monomial(m, expl);
        for (unsigned k = 0; k < mask.size(); k++) {
            if (mask[k] == 1)
                add_explanation_of_large_value(m.m_vs[large[k]], expl);
        }
        m_expl->clear();
        m_expl->add(expl);

        if (sign == -1) {
            lp::lar_term t;  // j >= -m_val or j + m.m_v >= 0
            t.add_monomial(rational(1), j);
            t.add_monomial(rational(1), m.m_v);
            t.m_v = rational(0);
            ineq in(lp::lconstraint_kind::GE, t);
            m_lemma->push_back(in);
            return true;
        }
        SASSERT(sign == 1);
        lp::lar_term t;  // j <= m_val or j - m.m_v <= 0
        t.add_monomial(rational(1), j);
        t.add_monomial(rational(-1), m.m_v);
        t.m_v = rational(0);
        ineq in(lp::lconstraint_kind::LE, t);
        m_lemma->push_back(in);
        return true;
    }
    bool large_basic_lemma_for_mon_proportionality(unsigned i_mon, const svector<unsigned>& large) {
        svector<unsigned> mask(large.size(), (unsigned) 0); // init mask by zeroes
        const auto & m = m_monomials[i_mon];
        int sign;
        auto vars = reduce_monomial_to_minimal(m.m_vs, sign);
        
        auto v = lp::abs(m_lar_solver.get_column_value_rational(m.m_v));
        // We cross out from vars the "large" variables represented by the mask
        do {
            for (unsigned k = 0; k < mask.size(); k++) {
                if (mask[k] == 0) {
                    mask[k] = 1;
                    TRACE("niil_solver", tout << "large[" << k << "] = " << large[k];);
                    vars.erase(vars.begin() + large[k]);
                    std::sort(vars.begin(), vars.end());
                    // now the value of vars has to be v*sign
                    lpvar j;
                    if (find_compimenting_monomial(vars, j) &&
                        large_lemma_for_proportion_case(m, mask, large, j)) {
                        TRACE("niil_solver", print_explanation_and_lemma(tout););
                        return true;
                    }
                } else {
                    SASSERT(mask[k] == 1);
                    mask[k] = 0;
                    vars.push_back(vars[large[k]]); // vars becomes unsorted
                }
            }
        } while(true);
        TRACE("niil_solver", tout << "return false";);
        return false; // we exhausted the mask and did not find the compliment monomial
    }

    bool small_basic_lemma_for_mon_proportionality(unsigned i_mon, const svector<unsigned>& _small) {
        svector<unsigned> mask(_small.size(), (unsigned) 0);

        return false;
    }

    bool generate_basic_lemma_for_mon_proportionality(unsigned i_mon) {
        TRACE("niil_solver", tout << "generate_basic_lemma_for_mon_proportionality";);
        const mon_eq & m = m_monomials[i_mon];
        svector<unsigned> large;
        svector<unsigned> _small;
        get_large_and_small_indices_of_monomimal(m, large, _small);
        TRACE("niil_solver", tout << "large size = " << large.size() << ", _small size = " << _small.size(););
        if (large.empty() && _small.empty())
            return false;
        
        if (m_minimal_monomials.empty())
            create_min_map();

        if (!large.empty() && large_basic_lemma_for_mon_proportionality(i_mon, large))
            return true;

        if (!_small.empty() && small_basic_lemma_for_mon_proportionality(i_mon, _small))
            return true;

        return false;

    }

    bool generate_basic_lemma_for_mon(unsigned i_mon) {
        return generate_basic_lemma_for_mon_sign(i_mon)
            || generate_basic_lemma_for_mon_zero(i_mon)
            || generate_basic_lemma_for_mon_neutral(i_mon)
            || generate_basic_lemma_for_mon_proportionality(i_mon);
    }

    bool generate_basic_lemma(svector<unsigned> & to_refine) {
        for (unsigned i : to_refine)
            if (generate_basic_lemma_for_mon(i)) {
                TRACE("niil_solver", tout << "a lemma generated for monomial " << i << std::endl;
                      tout << "lemma.size() = " << m_lemma->size() << "\n";
                      print_explanation_and_lemma(tout); );
                return true;
            }
        return false;
    }

    void map_monominals_vars(unsigned i) {
        const mon_eq& m = m_monomials[i];
        for (lpvar j : m.m_vs) {
            auto it = m_var_lists.find(j);
            if (it == m_var_lists.end()) {
                var_lists v;
                v.add_monomial(i);
                m_var_lists[j] = v;
            }
            else {
                it->second.add_monomial(i);
            }
        }
    }

    void map_vars_to_monomials_and_constraints() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monominals_vars(i);
    }

    void init_vars_equivalence() {
        m_vars_equivalence.init(m_lar_solver);
    }

    void add_pair_to_min_monomials(const svector<lpvar>& key, unsigned i, int sign) {
        mono_index_with_sign ms(i, sign);
        auto it = m_minimal_monomials.find(key);
        if (it == m_minimal_monomials.end()) {
            vector<mono_index_with_sign> v;
            v.push_back(ms);
            m_minimal_monomials.emplace(key, v);
        } else {
            it->second.push_back(ms);
        }
    }
    
    void add_monomial_to_min_map(unsigned i) {
        const mon_eq& m = m_monomials[i];
        int sign;
        svector<lpvar> key = reduce_monomial_to_minimal(m.m_vs, sign);
        add_pair_to_min_monomials(key, i, sign);
    }
    
    void create_min_map() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            add_monomial_to_min_map(i);
    }
    
    void init_search() {
        map_vars_to_monomials_and_constraints();
        init_vars_equivalence();
        m_expl->clear();
        m_lemma->clear();
    }
    
    lbool check(lp::explanation & exp, lemma& l) {
        TRACE("niil_solver", tout << "check of niil";);
        m_expl =   &exp;
        m_lemma =  &l;
        lp_assert(m_lar_solver.get_status() == lp::lp_status::OPTIMAL);
        svector<unsigned> to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }

        if (to_refine.empty())
            return l_true;

        TRACE("niil_solver", tout << "to_refine.size() = " << to_refine.size() << std::endl;);
        
        init_search();
        
        if (generate_basic_lemma(to_refine))
            return l_false;
        
        return l_undef;
    }
}; // end of imp

void solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    m_imp->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(lp::explanation & ex, lemma& l) {
    return m_imp->check(ex, l);
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

}
