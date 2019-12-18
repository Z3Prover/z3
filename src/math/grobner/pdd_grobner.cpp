/*++
  Copyright (c) 2019 Microsoft Corporation

  Abstract:

    Grobner core based on pdd representation of polynomials

  Author:
     Nikolaj Bjorner (nbjorner)
     Lev Nachmanson (levnach)

  --*/

#include "math/grobner/pdd_grobner.h"

namespace dd {

    /***
        The main algorithm maintains two sets (S, A), 
        where S is m_processed, and A is m_to_simplify.
        Initially S is empty and A contains the initial equations.
        
        Each step proceeds as follows:
        - pick a in A, and remove a from A
        - simplify a using S
        - simplify S using a
        - for s in S:
             b = superpose(a, s)
             add b to A
        - add a to S
        - simplify A using a
    */

    grobner::grobner(reslimit& lim, pdd_manager& m) : 
        m(m),
        m_limit(lim), 
        m_conflict(false)
    {}


    grobner::~grobner() {
        del_equations(0);
    }

    void grobner::compute_basis() {
        try {
            while (!done() && compute_basis_step()) {
                TRACE("grobner", display(tout););
                DEBUG_CODE(invariant(););
            }
        }
        catch (pdd_manager::mem_out) {
            // don't reduce further
        }
    }

    bool grobner::compute_basis_step() {
        m_stats.m_compute_steps++;
        equation* e = pick_next();
        if (!e) return false;
        equation& eq = *e;
        SASSERT(!eq.is_processed());
        if (!simplify_using(eq, m_processed)) return false;
        if (eliminate(eq)) return true;
        if (check_conflict(eq)) return false;
        if (!simplify_using(m_processed, eq)) return false;
        TRACE("grobner", tout << "eq = "; display_equation(tout, eq););
        superpose(eq);
        toggle_processed(eq);
        return simplify_using(m_to_simplify, eq);
    }
    
    grobner::equation* grobner::pick_next() {
        equation* eq = nullptr;
        ptr_buffer<equation> to_delete;
        for (auto* curr : m_to_simplify) {
            if (!eq|| is_simpler(*curr, *eq)) {
                eq = curr;
            }
        }
        for (auto* e : to_delete)
            del_equation(e);
        if (eq) 
            m_to_simplify.erase(eq);
        return eq;
    }

    void grobner::superpose(equation const & eq) {
        for (equation * target : m_processed) {
            superpose(eq, *target);
        }
    }

    /*
      Use a set of equations to simplify eq
    */
    bool grobner::simplify_using(equation& eq, equation_set const& eqs) {
        bool simplified, changed_leading_term;
        TRACE("grobner", tout << "simplifying: "; display_equation(tout, eq); tout << "using equalities of size " << eqs.size() << "\n";);
        do {
            simplified = false;
            for (equation* p : eqs) {
                if (simplify_source_target(*p, eq, changed_leading_term)) {
                    simplified = true;
                }
                if (canceled() || eq.poly().is_val()) {
                    break;
                }
            }
        }
        while (simplified && !eq.poly().is_val());

        TRACE("grobner", tout << "simplification result: ";  display_equation(tout, eq););

        check_conflict(eq);
        return !done();
    }

    /*
      Use the given equation to simplify equations in set
    */
    bool grobner::simplify_using(equation_set& set, equation const& eq) {
        TRACE("grobner", tout << "poly " << eq.poly() <<  "\n";);
        ptr_buffer<equation> to_delete;
        ptr_buffer<equation> to_move;
        bool changed_leading_term = false;
        for (equation* target : set) {
            if (canceled())
                return false;
            if (simplify_source_target(eq, *target, changed_leading_term)) {
                if (is_trivial(*target))
                    to_delete.push_back(target);
                else if (check_conflict(*target))
                    return false;
                else if (changed_leading_term && target->is_processed()) {
                    to_move.push_back(target);
                }
            }            
        }
        for (equation* eq : to_delete)
            del_equation(eq);
        for (equation* eq : to_move) 
            toggle_processed(*eq);
        return true;
    }    

    /*
      simplify target using source.
      return true if the target was simplified. 
      set changed_leading_term if the target is in the m_processed set and the leading term changed.
     */
    bool grobner::simplify_source_target(equation const& source, equation& target, bool& changed_leading_term) {
        TRACE("grobner", tout << "simplifying: " << target.poly() << "\nusing: " << source.poly() << "\n";);
        m_stats.m_simplified++;
        pdd r = source.poly().reduce(target.poly());
        if (r == source.poly()) {
            return false;
        }
        changed_leading_term = target.is_processed() && m.different_leading_term(r, source.poly());
        target = r;
        target = m_dep_manager.mk_join(target.dep(), source.dep());
        update_stats_max_degree_and_size(target);

        TRACE("grobner", tout << "simplified " << target.poly() << "\n";);
        return true;
    }

    /*
       let eq1: ab+q=0, and eq2: ac+e=0, then qc - eb = 0
    */
    void grobner::superpose(equation const& eq1, equation const& eq2) {
        TRACE("grobner_d", tout << "eq1="; display_equation(tout, eq1) << "eq2="; display_equation(tout, eq2););
        pdd r(m);
        if (!m.try_spoly(eq1.poly(), eq2.poly(), r)) return;
        m_stats.m_superposed++;
        if (r.is_zero()) return;
        unsigned idx = m_equations.size();
        equation* eq = alloc(equation, r, m_dep_manager.mk_join(eq1.dep(), eq2.dep()), idx);
        update_stats_max_degree_and_size(*eq);
        if (r.is_val()) set_conflict();
        m_to_simplify.insert(eq);
    }

    void grobner::toggle_processed(equation& eq) {
        if (eq.is_processed()) {
            m_to_simplify.insert(&eq);
            m_processed.erase(&eq);
        }
        else {
            m_processed.insert(&eq);
            m_to_simplify.erase(&eq);            
        }
        eq.set_processed(!eq.is_processed());        
    }

    grobner::equation_set const& grobner::equations() {
        m_all_eqs.reset();
        for (equation* eq : m_equations) if (eq) m_all_eqs.insert(eq);
        return m_all_eqs;
    }

    void grobner::reset() {
        del_equations(0);
        SASSERT(m_equations.empty());    
        m_processed.reset();
        m_to_simplify.reset();
        m_stats.reset();
        m_conflict = false;
    }

    void grobner::add(pdd const& p, u_dependency * dep) {
        if (p.is_zero()) return;
        if (p.is_val()) set_conflict();
        equation * eq = alloc(equation, p, dep, m_equations.size());
        m_equations.push_back(eq);
        m_to_simplify.insert(eq);
    }   

    void grobner::del_equations(unsigned old_size) {
        for (unsigned i = m_equations.size(); i-- > old_size; ) {
            del_equation(m_equations[i]);
        }
        m_equations.shrink(old_size);    
    }

    void grobner::del_equation(equation* eq) {
        if (!eq) return;
        unsigned idx = eq->idx();
        m_processed.erase(eq);
        m_to_simplify.erase(eq);
        dealloc(m_equations[idx]);
        m_equations[idx] = nullptr;
    }
    
    bool grobner::canceled() {
        return m_limit.get_cancel_flag();
    }
    
    bool grobner::done() {
        return m_to_simplify.size() + m_processed.size() >= m_config.m_eqs_threshold || canceled() || m_conflict;
    }
    
    void grobner::update_stats_max_degree_and_size(const equation& e) {
        m_stats.m_max_expr_size = std::max(m_stats.m_max_expr_size, e.poly().tree_size());
        m_stats.m_max_expr_degree = std::max(m_stats.m_max_expr_degree, e.poly().degree());
    }
    
    void grobner::collect_statistics(statistics& st) const {
        st.update("steps", m_stats.m_compute_steps);
        st.update("simplified", m_stats.m_simplified);
        st.update("superposed", m_stats.m_superposed);
        st.update("degree", m_stats.m_max_expr_degree);
        st.update("size", m_stats.m_max_expr_size);
    }
            
    std::ostream& grobner::display_equation(std::ostream & out, const equation & eq) const {
        out << "expr = " << eq.poly() << "\n";
        m_print_dep(eq.dep(), out);
        return out;
    }

    std::ostream& grobner::display(std::ostream& out) const {
        out << "processed\n"; for (auto e : m_processed) display_equation(out, *e);
        out << "to_simplify\n"; for (auto e : m_to_simplify) display_equation(out, *e);
        statistics st;
        collect_statistics(st);
        st.display(out);
        return out;
    }

    void grobner::invariant() const {
        for (auto* e : m_processed) {
            SASSERT(e->is_processed());            
        }
        for (auto* e : m_to_simplify) {
            SASSERT(!e->is_processed());            
        }
        for (auto* e : m_equations) {
            if (e) {
                SASSERT(!e->is_processed() || m_processed.contains(e));
                SASSERT(e->is_processed() || m_to_simplify.contains(e));
                SASSERT(!is_trivial(*e));
            }
        }
    }


}

