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
        size_t seed = 0;
        for (unsigned t : v)
            hash_combine(seed, t);
        return seed;
    }

};

bool operator==(const svector<unsigned> & a, const svector<unsigned> & b) {
    if (a.size() != b.size())
        return false;
    for (unsigned i = 0; i < a.size(); i++)
        if (a[i] != b[i])
            return false;
    return true;
}

struct solver::imp {
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
        void add_expl_from_monomial(const T & m, expl_set & exp) const {
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

    typedef lp::lar_base_constraint lpcon;
    
    struct var_lists {
        svector<unsigned>                 m_monomials; // of the var
        svector<lpci> m_constraints; // of the var
        const svector<unsigned>& mons() const { return m_monomials;}
        svector<unsigned>& mons() { return m_monomials;}
        const svector<lpci>& constraints() const { return m_constraints;}
        void add_monomial(unsigned i) { mons().push_back(i); }
        void add_constraint(lpci i) { m_constraints.push_back(i); };
    };

    struct mono_index_with_sign {
        unsigned m_i; // the monomial index
        int      m_sign; // the monomial sign: -1 or 1
        mono_index_with_sign(unsigned i, int sign) : m_i(i), m_sign(sign) {}
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
            return true;
        }
            
        return false;
    }

    bool values_are_different(lpvar j, int sign, lpvar k) const {
        SASSERT(sign == 1 || sign == -1);
        return ! ( sign * m_lar_solver.get_column_value(j) == m_lar_solver.get_column_value(k));
    }

    void add_expl_from_monomial(const mon_eq& m, expl_set & eset) const {
        m_vars_equivalence.add_expl_from_monomial(m, eset);
    }

    void print_monomial(const mon_eq& m, std::ostream& out) {
        out << m_lar_solver.get_column_name(m.var()) << " = ";
        for (unsigned j : m) {
            out << m_lar_solver.get_column_name(j) << "*";
        }
    }
    // the monomials should be equal by modulo sign, but they are not equal in the model
    void fill_explanation_and_lemma_sign(const mon_eq& a, const mon_eq & b, int sign) {
        expl_set expl;
        SASSERT(sign == 1 || sign == -1);
        add_expl_from_monomial(a, expl);
        add_expl_from_monomial(b, expl);
        m_expl->clear();
        m_expl->add(expl);
        TRACE("niil_solver",
              for (auto &p : *m_expl)
                  m_lar_solver.print_constraint(p.second, tout); tout << "\n";
              );
        lp::lar_term t;
        t.add_monomial(rational(1), a.var());
        t.add_monomial(rational(- sign), b.var());
        TRACE("niil_solver", 
              m_lar_solver.print_term(t, tout);
              tout << "\n";
              print_monomial(a, tout);
              tout << "\n";
              print_monomial(b, tout);
              );

        ineq in(lp::lconstraint_kind::NE, t);
        m_lemma->push_back(in);
    }
    
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
    svector<lpvar> reduce_monomial_to_minimal(const svector<lpvar> & vars, int & sign) {
        svector<lpvar> ret;
        sign = 1;
        for (unsigned i = 0; i < vars.size(); i++) {
            ret.push_back(m_vars_equivalence.map_to_min(vars[i], sign));
        }
        std::sort(ret.begin(), ret.end());
        return ret;
    }
    
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
    bool get_mon_sign_zero_var_loop_body(lpvar j, lpci ci, lpci & lci, lpci & uci,
                                         rational& lb, rational &ub) const {
        const auto * c = m_lar_solver.constraints()[ci];
        if (c->size() != 1)
            return false;
        const auto coeffs = c->get_left_side_coefficients();
        SASSERT(coeffs[0].second == j);
        auto kind = c->m_kind;
        const rational& a = coeffs[0].first;
        if (a.is_neg())
            kind = lp::flip_kind(kind);
            
        rational rs = c->m_right_side / a ;
        SASSERT(rs.is_int());
        switch(kind) {
        le_case:
        case lp::LE:
            if (!is_set(uci)) {
                uci = ci;
                ub = rs;
            } else {
                if (ub > rs) {
                    ub = rs;
                    uci = ci;
                }
            }
            break;

        case lp::LT:
            rs -= 1;
            goto le_case;

        ge_case:
        case lp::GE:
            if (!is_set(lci)) {
                lci = ci;
                lb = rs;
            } else {
                if (lb < rs) {
                    lb = rs;
                    lci = ci;
                }
            }
            break;

        case lp::GT:
            rs += 1;
            goto ge_case;
        case lp::EQ:
            uci = lci = ci;
            ub = lb = rs;
            break;
        default:
            return false; 
        }
        return true;
    }
    
    // Return 0 if the monomial has to to have a zero value,
    // -1 if the monomial has to be negative
    // 1 if positive.
    // If strict is true on the entrance then it can be set to false,
    // otherwise it remains false
    // Returns true if the sign is not defined.
    int get_mon_sign_zero_var(unsigned j, bool & strict) {
        auto it = m_var_lists.find(j);
        if (it == m_var_lists.end())
            return 2;
        lpci lci = -1;
        lpci uci = -1;
        rational lb, ub;
        for (lpci ci : it->second.m_constraints) {
            if (get_mon_sign_zero_var_loop_body(j, ci, lci, uci, lb, ub) == false)
                continue;
            
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
                return 2;;
            if (s == 0)
                return 0;
            sign *= s;
        }
        return sign;
    }
    
    bool generate_basic_lemma_for_mon_zero(unsigned i_mon) {
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
        TRACE("niil_solver",
              for (auto &p : *m_expl)
                  m_lar_solver.print_constraint(p.second, tout); tout << "\n";
              m_lar_solver.print_term(t, tout);
              tout << " " << lp::lconstraint_kind_string(kind) << " 0\n";
              print_monomial(m_monomials[i_mon], tout); tout << "\n";
              lpvar mon_var = m_monomials[i_mon].var();
              
              tout << m_lar_solver.get_column_name(mon_var) << " = " << m_lar_solver.get_column_value(mon_var);
              );
        

        return true;
    }

    bool generate_basic_lemma_for_mon_neutral(unsigned i_mon) {
        return false;
    }

    bool generate_basic_lemma_for_mon_proportionality(unsigned i_mon) {
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
            if (generate_basic_lemma_for_mon(i))
                return true;
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

    void bind_var_and_constraint(lpvar j, lpci ci) {
        auto it = m_var_lists.find(j);
        if (it == m_var_lists.end()) {
            var_lists v;
            v.add_constraint(ci);
            m_var_lists.insert(std::pair<lpvar, var_lists>(j, v));
        } else {
            it->second.add_constraint(ci);
        }
    }
    
    void process_constraint_vars(lpci ci) {
        for (const auto p : m_lar_solver.constraints()[ci]->get_left_side_coefficients())
            bind_var_and_constraint(p.second, ci);
    }
    
    void map_vars_to_monomials_and_constraints() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monominals_vars(i);
        for (lpci ci = 0; ci < m_lar_solver.constraints().size(); ci++) {
            process_constraint_vars(ci);
        }
    }

    void init_vars_equivalence() {
        m_vars_equivalence.init(m_lar_solver);
    }

    void add_pair_to_min_monomials(const svector<lpvar>& key, unsigned i, int sign) {
        mono_index_with_sign ms(i, sign);
        auto it = m_minimal_monomials.find(i);
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
        /*
            svector<lpvar> sorted_vs;
            for (unsigned i = 0; i < sz; i++)
                sorted_vs.push_back(vs[i]);
            std::sort(sorted_vs.begin(), sorted_vs.end());
            std::cout << "sorted_vs = ";
            print_vector(sorted_vs, std::cout);
            m_monomials.push_back(mon_eq(v, sorted_vs));
        }
        auto it = m_hashed_monomials.find(m_monomials.back().m_vs);
        if (it == m_hashed_monomials.end()) {
            svector<unsigned> t; t.push_back(m_monomials.size() - 1); // the index of the last monomial
            m_hashed_monomials.insert(std::pair(m_monomials.back().m_vs, t));
        } else {
            it->second.push_back(m_monomials.size() - 1); // we have at least two monomials that are identical in their vars
            }*/
    }
    
    void init_search() {
        map_vars_to_monomials_and_constraints();
        init_vars_equivalence();
        create_min_map();
    }
    
    lbool check(lp::explanation & exp, lemma& l) {
        m_expl =   &exp;
        m_lemma =  &l;
        lp_assert(m_lar_solver.get_status() == lp::lp_status::OPTIMAL);
        svector<unsigned> to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }

        if (to_refine.size() == 0)
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


void solver::push(){
    m_imp->push();
}
void solver::pop(unsigned n) {
    m_imp->pop(n);
}


solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p);
}


}
