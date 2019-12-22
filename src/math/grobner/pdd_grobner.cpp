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
            do not occur in watch list

        - the variable ordering should be chosen from a candidate model M, 
          in a way that is compatible with weights that draw on the number of occurrences
          in polynomials with violated evaluations and with the maximal slack (degree of freedom).
         
          weight(x) := < count { p in P | x in p, M(p) != 0 }, min_{p in P | x in p} slack(p,x) >

          slack is computed from interval assignments to variables, and is an interval in which x can possibly move
          (an over-approximation).

        The alternative version maintains the following invariant:
        - polynomials not in the watch list cannot be simplified using a
          Justification:
          - elements in S have no variables watched
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
        if (is_tuned()) tuned_init();
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
        return is_tuned() ? tuned_step() : basic_step();
    }

    bool grobner::basic_step() {
        equation* e = pick_next();
        if (!e) return false;
        scoped_detach sd(*this, e);
        equation& eq = *e;
        TRACE("grobner", display(tout << "eq = ", eq); display(tout););
        SASSERT(!eq.is_processed());
        if (!simplify_using(eq, m_processed)) return false;
        if (is_trivial(eq)) { sd.e = nullptr; retire(e); return true; }
        if (check_conflict(eq)) return false;
        if (!simplify_using(m_processed, eq)) return false;
        superpose(eq);
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
        unsigned j = 0;
        for (equation* target : m_processed) {
            if (superpose(eq, *target)) {
                retire(target); 
            }
            else {
                target->set_index(j);
                m_processed[j++] = target;
            }
        }
        m_processed.shrink(j);
    }

    /*
      Use a set of equations to simplify eq
    */
    bool grobner::simplify_using(equation& eq, equation_vector const& eqs) {
        bool simplified, changed_leading_term;
        TRACE("grobner", display(tout << "simplifying: ", eq); tout << "using equalities of size " << eqs.size() << "\n";);
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

        TRACE("grobner", display(tout << "simplification result: ", eq););

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
            if (simplified && is_trivial(target)) {
                retire(&target);
            }
            else if (simplified && !check_conflict(target) && changed_leading_term) {
                SASSERT(target.is_processed());
                target.set_processed(false);
                if (is_tuned()) {
                    m_levelp1 = std::max(m_var2level[target.poly().var()]+1, m_levelp1);
                }
                push_equation(target, m_to_simplify);               
            }
            else {
                set[j] = set[i];
                target.set_index(j++);                
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
        pdd t = source.poly();
        pdd r = target.poly().reduce(t);
        if (r == target.poly() || is_too_complex(r)) {
            return false;
        }
        changed_leading_term = target.is_processed() && m.different_leading_term(r, target.poly());
        target = r;
        target = m_dep_manager.mk_join(target.dep(), source.dep());
        update_stats_max_degree_and_size(target);
        TRACE("grobner", tout << "simplified " << target.poly() << "\n";);
        return true;
    }

    /*
       let eq1: ab+q=0, and eq2: ac+e=0, then qc - eb = 0
    */
    bool grobner::superpose(equation const& eq1, equation const& eq2) {
        TRACE("grobner_d", tout << "eq1="; display(tout, eq1) << "eq2="; display(tout, eq2););
        pdd r(m);
        if (!m.try_spoly(eq1.poly(), eq2.poly(), r)) return false;
        m_stats.m_superposed++;
        if (r.is_zero() || is_too_complex(r)) return false;
        add(r, m_dep_manager.mk_join(eq1.dep(), eq2.dep()));
        return is_tuned() && m.spoly_is_invertible(eq1.poly(), eq2.poly());
    }

    bool grobner::tuned_step() {
        equation* e = tuned_pick_next();
        if (!e) return false;
        scoped_detach sd(*this, e);
        equation& eq = *e;
        SASSERT(!m_watch[eq.poly().var()].contains(e));
        SASSERT(!eq.is_processed());
        if (!simplify_using(eq, m_processed)) return false;
        if (is_trivial(eq)) { sd.e = nullptr; retire(e); return true; }
        if (check_conflict(eq)) return false;
        if (!simplify_using(m_processed, eq)) return false;
        TRACE("grobner", tout << "eq = "; display(tout, eq););
        superpose(eq);
        return simplify_to_simplify(eq);
    }

    void grobner::tuned_init() {
        unsigned_vector const& l2v = m.get_level2var();
        m_level2var.resize(l2v.size());
        m_var2level.resize(l2v.size());
        for (unsigned i = 0; i < l2v.size(); ++i) {
            m_level2var[i] = l2v[i];
            m_var2level[l2v[i]] = i;
        }
        m_watch.reserve(m_level2var.size());
        m_levelp1 = m_level2var.size();
        for (equation* eq : m_to_simplify) add_to_watch(*eq);
        SASSERT(m_processed.empty());
    }

    void grobner::add_to_watch(equation& eq) {
        SASSERT(!eq.is_processed());
        pdd const& p = eq.poly();
        if (is_tuned() && !p.is_val()) {
            m_watch[p.var()].push_back(&eq);
        }
    }

    bool grobner::simplify_to_simplify(equation const& eq) {
        unsigned v = eq.poly().var();
        auto& watch = m_watch[v];
        unsigned j = 0;
        for (equation* _target : watch) {
            equation& target = *_target;
            SASSERT(!target.is_processed());
            SASSERT(target.poly().var() == v);
            bool changed_leading_term = false;
            if (!done()) simplify_source_target(eq, target, changed_leading_term);
            if (is_trivial(target)) {
                retire(&target);
            }
            else if (check_conflict(target)) {
                // remove from watch
            } else if (target.poly().var() != v) {
                // move to other watch list
                m_watch[target.poly().var()].push_back(_target);
            }
            else {
                // keep watching same variable
                watch[++j] = _target;
            }
        }
        watch.shrink(j);        
        return false;
    }

    grobner::equation* grobner::tuned_pick_next() {
        while (m_levelp1 > 0) {
            unsigned v = m_level2var[m_levelp1-1];
            equation_vector const& watch = m_watch[v];
            equation* eq = nullptr;
            for (equation* curr : watch) {
                pdd const& p = curr->poly();
                if (!curr->is_processed() && !p.is_val() && p.var() == v) {
                    if (!eq || is_simpler(*curr, *eq))
                        eq = curr;
                }
            }
            if (eq) {
                pop_equation(eq->idx(), m_to_simplify);
                m_watch[eq->poly().var()].erase(eq);
                return eq;
            }
            --m_levelp1;
        }
        return nullptr;
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
        if (!check_conflict(*eq) && is_tuned()) {
            m_levelp1 = std::max(m_var2level[p.var()]+1, m_levelp1);
        }
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
        if (idx != v.size() - 1) {
            equation* eq2 = v.back();
            eq2->set_index(idx);
            v[idx] = eq2;
        }
        v.pop_back();            
    }

    void grobner::push_equation(equation& eq, equation_vector& v) {
        eq.set_index(v.size());
        v.push_back(&eq);
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
            
    std::ostream& grobner::display(std::ostream & out, const equation & eq) const {
        out << eq.poly() << "\n";
        if (m_print_dep) m_print_dep(eq.dep(), out);
        return out;
    }

    std::ostream& grobner::display(std::ostream& out) const {
        out << "processed\n"; for (auto e : m_processed) display(out, *e);
        out << "to_simplify\n"; for (auto e : m_to_simplify) display(out, *e);
        statistics st;
        collect_statistics(st);
        st.display(out);
        return out;
    }

    void grobner::invariant() const {
        // equations in processed have correct indices
        // they are labled as processed
        unsigned i = 0;
        for (auto* e : m_processed) {
            VERIFY(e->is_processed());            
            VERIFY(e->idx() == i);
            ++i;
        }
        // equations in to_simplify have correct indices
        // they are labeled as non-processed
        // their top-most variable is watched
        i = 0;
        for (auto* e : m_to_simplify) {
            VERIFY(!e->is_processed());            
            VERIFY(e->idx() == i);
            if (is_tuned()) {
                pdd const& p = e->poly();
                VERIFY(p.is_val() || m_watch[p.var()].contains(e));
            }
            ++i;
        }
        // the watch list consists of equations in to_simplify
        // they watch the top most variable in poly
        i = 0;
        for (auto const& w : m_watch) {
            for (equation* e : w) {
                VERIFY(!e->poly().is_val());
                VERIFY(e->poly().var() == i);
                VERIFY(!e->is_processed());
                VERIFY(m_to_simplify.contains(e));
            }
            ++i;
        }
    }
}

