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
        A simple algorithm maintains two sets (S, A), 
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

        Alternate:

        - Fix a variable ordering x1 > x2 > x3 > ....
        In each step:
          - pick a in A with *highest* variable x_i in leading term of *lowest* degree.
          - simplify a using S
          - simplify S using a
          - if a does not contains x_i, put it back into A and pick again (determine whether possible)
          - for s in S:
               b = superpose(a, s)
               if superposition is invertible, then remove s
               add b to A
          - add a to S
          - simplify A using a


        Apply a watch list to filter out relevant elements of S
        Index leading_term_watch: Var -> Equation*
        Only need to simplify equations that contain eliminated variable.
        The watch list can be used to index into equations that are useful to simplify.
        A Bloom filter on leading term could further speed up test whether reduction applies.

        For p in A:
            populate watch list by maxvar(p) |-> p
        For p in S:
            populate watch list by vars(p) |-> p

        - the variable ordering should be chosen from a candidate model M, 
          in a way that is compatible with weights that draw on the number of occurrences
          in polynomials with violated evaluations and with the maximal slack (degree of freedom).
         
          weight(x) := < count { p in P | x in p, M(p) != 0 }, min_{p in P | x in p} slack(p,x) >

          slack is computed from interval assignments to variables, and is an interval in which x can possibly move
          (an over-approximation).

        The alternative version maintains the following invariant:
        - polynomials not in the watch list cannot be simplified using a
          Justification:
          - elements in S have all variables watched
          - elements in A are always reduced modulo all variables above the current x_i.

        Invertible rules:
          when p, q are linear in x, e.g., is of the form p = k*x + a, q = l*x + b 
          where k, l are constant and x is maximal, then 
          from l*a - k*b and k*x + a we have the equality lkx+al+kb-al, which is lx+b
          So we can throw away q after superposition without losing solutions.
          - this corresponds to triangulating a matrix during Gauss.

    */

    grobner::grobner(reslimit& lim, pdd_manager& m) : 
        m(m),
        m_limit(lim), 
        m_conflict(nullptr)
    {}

    grobner::~grobner() {
        reset();
    }

    void grobner::saturate() {
        try {
            while (!done() && step()) {
                TRACE("grobner", display(tout););
                DEBUG_CODE(invariant(););
            }
        }
        catch (pdd_manager::mem_out) {
            // don't reduce further
        }
    }

    bool grobner::step() {
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
        eq.set_processed(true);
        m_processed.push_back(e);
        return simplify_using(m_to_simplify, eq);
    }
    
    grobner::equation* grobner::pick_next() {
        equation* eq = nullptr;
        for (auto* curr : m_to_simplify) {
            if (!eq || is_simpler(*curr, *eq)) {
                eq = curr;
            }
        }
        if (eq) pop_equation(eq->idx(), m_to_simplify);
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
    bool grobner::simplify_using(equation& eq, equation_vector const& eqs) {
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
    bool grobner::simplify_using(equation_vector& set, equation const& eq) {
        TRACE("grobner", tout << "poly " << eq.poly() <<  "\n";);
        unsigned j = 0, sz = set.size();
        for (unsigned i = 0; i < sz; ++i) {
            equation& target = *set[i];
            bool changed_leading_term = false;
            bool simplified = !done() && simplify_source_target(eq, target, changed_leading_term); 
            if (simplified && (is_trivial(target) || is_too_complex(target))) {
                retire(&target);
            }
            else if (simplified && !check_conflict(target) && changed_leading_term && target.is_processed()) {
                target.set_index(m_to_simplify.size());
                target.set_processed(false);
                m_to_simplify.push_back(&target);                    
            }
            else {
                set[j] = &target;
                target.set_index(j);
                ++j;
            } 
        }
        set.shrink(j);
        return !done();
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
        if (is_too_complex(r)) return;
        add(r, m_dep_manager.mk_join(eq1.dep(), eq2.dep()));
    }

    grobner::equation_vector const& grobner::equations() {
        m_all_eqs.reset();
        for (equation* eq : m_to_simplify) m_all_eqs.push_back(eq);
        for (equation* eq : m_processed) m_all_eqs.push_back(eq);
        return m_all_eqs;
    }

    void grobner::reset() {
        for (equation* e : m_to_simplify) dealloc(e);
        for (equation* e : m_processed) dealloc(e);
        m_processed.reset();
        m_to_simplify.reset();
        m_stats.reset();
        m_conflict = nullptr;
    }

    void grobner::add(pdd const& p, u_dependency * dep) {
        if (p.is_zero()) return;
        equation * eq = alloc(equation, p, dep, m_to_simplify.size());
        m_to_simplify.push_back(eq);
        check_conflict(*eq);
        update_stats_max_degree_and_size(*eq);
    }   
    
    bool grobner::canceled() {
        return m_limit.get_cancel_flag();
    }
    
    bool grobner::done() {
        return m_to_simplify.size() + m_processed.size() >= m_config.m_eqs_threshold || canceled() || m_conflict != nullptr;
    }

    void grobner::del_equation(equation& eq) {
        pop_equation(eq.idx(), eq.is_processed() ? m_processed : m_to_simplify);
        retire(&eq);
    }

    void grobner::pop_equation(unsigned idx, equation_vector& v) {
        equation* eq2 = v.back();
        eq2->set_index(idx);
        v[idx] = eq2;
        v.pop_back();            
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
        unsigned i = 0;
        for (auto* e : m_processed) {
            SASSERT(e->is_processed());            
            SASSERT(e->idx() == i);
            ++i;
        }
        i = 0;
        for (auto* e : m_to_simplify) {
            SASSERT(!e->is_processed());            
            SASSERT(e->idx() == i);
            ++i;
        }
    }
}

