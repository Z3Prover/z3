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

typedef nra::mon_eq mon_eq;
typedef lp::var_index lpvar;
struct solver::imp {
    struct vars_equivalence {
        struct signed_var {
            lpvar m_var;
            int   m_sign;
            signed_var(lpvar j, int sign) : m_var(j), m_sign(sign) {}
        };
        struct equiv {
            lpvar             m_i;
            signed_var        m_signed_var;
            equiv(lpvar i, lpvar j, int sign) :m_i(i), m_signed_var(j, sign) {
                SASSERT(i > j);
            }
        };

        // the resulting mapping
        std::unordered_map<lpvar, signed_var> m_map;
        // all equivalences extracted from constraints
        vector<equiv>                         m_equivs;
        unsigned size() const { return m_map.size(); }
        void add_equivalence_maybe(const lp::lar_term *t) {
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
            m_equivs.push_back(equiv(i, j, sign));
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
                add_equivalence_maybe(s.terms()[i]);
            }
        }

        void create_map() {
            bool progress = true;
            while (progress) {
                progress = false;
                for (const auto & e : m_equivs) {
                    unsigned i = e.m_i;
                    auto it = m_map.find(i);
                    if (it == m_map.end()) {
                        m_map.insert(std::pair<lpvar, signed_var>(i, e.m_signed_var));
                        progress = true;
                    } else {
                        if (it->second.m_var > e.m_signed_var.m_var) {
                            it->second = signed_var(
                                e.m_signed_var.m_var,
                                e.m_signed_var.m_sign * it->second.m_sign);
                            progress = true;
                        }
                    }
                }
            }
        }
        
        void init(const lp::lar_solver& s) {
            collect_equivs(s);
            create_map();
        }
        lpvar get_equivalent_var(lpvar j, bool & sign) {
            SASSERT(false);
            return false;
        }
        bool empty() const {
            return m_map.empty();
        }

        // the sign is flipped if needed
        lpvar map_to_min(lpvar j, int sign) const {
            auto it = m_map.find(j);
            if (it == m_map.end())
                return j;

            if (it->second.m_sign == -1) {
                sign = -sign;
            }
            return it->second.m_var;
        }
        
    };
    vars_equivalence                                       m_vars_equivalence;
    vector<mon_eq>                                         m_monomials;
    unsigned_vector                                        m_monomials_lim;
    lp::lar_solver&                                        m_lar_solver;
    std::unordered_map<lpvar, svector<unsigned>>   m_var_to_monomials;
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
        unsigned j_var,
        const svector<unsigned> & mon_vars,
        const mon_eq& other_m, bool sign, lemma& l) {
        if (mon_vars.size() != other_m.size())
            return false;
        
        return false;
    }
    
    bool generate_basic_lemma_for_mon_sign_var(unsigned i_mon,
                                               unsigned j_var, const svector<lpvar>& mon_vars, lemma& l, bool sign) {
        auto it = m_var_to_monomials.find(j_var);
        for (auto other_i_mon : it->second) {
            if (other_i_mon == i_mon) continue;
            if (generate_basic_lemma_for_mon_sign_var_other_mon(j_var, mon_vars,
                                                                m_monomials[other_i_mon], sign, l))
                return true;
        }
        return false;
    }

    // replaces each variable by a smaller one and flips the sing if the var comes with a minus
    void reduce_monomial_to_minimal(svector<lpvar> & vars, int & sign) {
        for (unsigned i = 0; i < vars.size(); i++) {
            vars[i] = m_vars_equivalence.map_to_min(vars[i], sign);
        }
    }
    
    bool generate_basic_lemma_for_mon_sign(unsigned i_mon, lemma& l) {
        if (m_vars_equivalence.empty()) {
            std::cout << "empty m_vars_equivalence\n";
            return false;
        } else {
            std::cout << "m_vars_equivalence size = " << m_vars_equivalence.size() << std::endl;
        }
        const mon_eq& m_of_i = m_monomials[i_mon];
        int sign = 1;
        
        auto mon_vars =  m_of_i.m_vs;
        reduce_monomial_to_minimal(mon_vars, sign);
        for (unsigned j_var : mon_vars)
            if (generate_basic_lemma_for_mon_sign_var(i_mon, j_var, mon_vars, l, sign))
                return true;
        return false;
    }

    bool generate_basic_lemma_for_mon_zero(unsigned i_mon, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon_neutral(unsigned i_mon, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon_proportionality(unsigned i_mon, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon(unsigned i_mon, lemma & l) {
        return generate_basic_lemma_for_mon_sign(i_mon, l)
            || generate_basic_lemma_for_mon_zero(i_mon, l)
            || generate_basic_lemma_for_mon_neutral(i_mon, l)
            || generate_basic_lemma_for_mon_proportionality(i_mon, l);
    }

    bool generate_basic_lemma(lemma & l, svector<unsigned> & to_refine) {
        for (unsigned i : to_refine)
            if (generate_basic_lemma_for_mon(i, l))
                return true;
        return false;
    }

    void map_monominals_vars(unsigned i) {
        const mon_eq& m = m_monomials[i];
        for (lpvar j : m.m_vs) {
            auto it = m_var_to_monomials.find(j);
            if (it == m_var_to_monomials.end()) {
                auto vect = svector<unsigned>();
                vect.push_back(i);
                m_var_to_monomials[j] = vect;
            }
            else {
                it->second.push_back(i);
            }
        }
    }
    
    void map_var_to_monomials() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monominals_vars(i);
    }

    void init_vars_equivalence() {
        m_vars_equivalence.init(m_lar_solver);
    }
    
    void init_search() {
        map_var_to_monomials();
        init_vars_equivalence();
    }
    
    lbool check(lemma& l) {
        lp_assert(m_lar_solver.get_status() == lp::lp_status::OPTIMAL);
        svector<unsigned> to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }
        std::cout << "to_refine size = " << to_refine.size() << std::endl;
        if (to_refine.size() == 0)
            return l_true;

        init_search();
        
        if (generate_basic_lemma(l, to_refine))
            return l_true;
        
        return l_undef;
    }

};


void solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    m_imp->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(lemma& l) {
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


}
