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


        TBD: 

        Linear Elimination:
        - comprises of a simplification pass that puts linear equations in to_processed
        - so before simplifying with respect to the variable ordering, eliminate linear equalities.

        Extended Linear Simplification (as exploited in Bosphorus AAAI 2019):
        - multiply each polynomial by one variable from their orbits.
        - The orbit of a varible are the variables that occur in the same monomial as it in some polynomial.
        - The extended set of polynomials is fed to a linear Gauss Jordan Eliminator that extracts
          additional linear equalities.
        - Bosphorus uses M4RI to perform efficient GJE to scale on large bit-matrices.

        Long distance vanishing polynomials (used by PolyCleaner ICCAD 2019):
        - identify polynomials p, q, such that p*q = 0
        - main case is half-adders and full adders (p := x + y, q := x * y) over GF2
          because (x+y)*x*y = 0 over GF2
          To work beyond GF2 we would need to rely on simplification with respect to asserted equalities.
          The method seems rather specific to hardware multipliers so not clear it is useful to 
          generalize.
        - find monomials that contain pairs of vanishing polynomials, transitively 
          withtout actually inlining.
          Then color polynomial variables w by p, resp, q if they occur in polynomial equalities
          w - r = 0, such that all paths in r contain a node colored by p, resp q. 
          polynomial variables that get colored by both p and q can be set to 0.
          When some variable gets colored, other variables can be colored.
        - We can walk pdd nodes by level to perform coloring in a linear sweep.
          PDD nodes that are equal to 0 using some equality are marked as definitions.
          First walk definitions to search for vanishing polynomial pairs. 
          Given two definition polynomials d1, d2, it must be the case that 
          level(lo(d1)) = level(lo(d1)) for the polynomial lo(d1)*lo(d2) to be vanishing.        
          Then starting from the lowest level examine pdd nodes. 
          Let the current node be called p, check if the pdd node p is used in an equation
          w - r = 0. In which case, w inherits the labels from r.
          Otherwise, label the node by the intersection of vanishing polynomials from lo(p) and hi(p).

       Eliminating multiplier variables, but not adders [Kaufmann et al FMCAD 2019 for GF2];
       - Only apply GB saturation with respect to variables that are part of multipliers.
       - Perhaps this amounts to figuring out whether a variable is used in an xor or more
       
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
        return basic_step(pick_next());
    }

    bool grobner::basic_step(equation* e) {
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
        if (eq) pop_equation(eq, m_to_simplify);
        return eq;
    }

    grobner::equation* grobner::pick_linear() {
        equation* eq = nullptr;
        for (auto* curr : m_to_simplify) {
            if (!eq || curr->poly().is_linear() && is_simpler(*curr, *eq)) {
                eq = curr;
            }
        }
        if (eq) pop_equation(eq, m_to_simplify);
        return eq;
    }

    void grobner::simplify_linear() {
        try {
            while (simplify_linear_step()) {
                DEBUG_CODE(invariant(););
            }
        }
        catch (pdd_manager::mem_out) {
            // done reduce
        }
    }

    struct grobner::compare_top_var {
        bool operator()(equation* a, equation* b) const {
            return a->poly().var() < b->poly().var();
        }
    };

    bool grobner::simplify_linear_step() {
        equation_vector linear;
        for (equation* e : m_to_simplify) {
            if (e->poly().is_linear()) {
                linear.push_back(e);
            }
        }
        if (linear.empty()) return false;
        vector<equation_vector> use_list;
        for (equation * e : m_to_simplify) {
            add_to_use(e, use_list);
        }
        for (equation * e : m_processed) {
            add_to_use(e, use_list);
        }
        compare_top_var ctv;
        std::stable_sort(linear.begin(), linear.end(), ctv);
        for (equation* src : linear) {
            equation_vector const& uses = use_list[src->poly().var()];
            bool changed_leading_term;
            for (equation* dst : uses) {
                if (src == dst || !simplify_source_target(*src, *dst, changed_leading_term)) {
                    continue;                    
                }
                if (dst->is_processed() && changed_leading_term) {
                    dst->set_processed(false);
                    pop_equation(dst, m_processed);
                    push_equation(dst, m_to_simplify);
                }
            }            
        } 
        for (equation* src : linear) {
            pop_equation(src, m_to_simplify);
            push_equation(src, m_processed);
            src->set_processed(true);
        }
        return true;
    }

    void grobner::add_to_use(equation* e, vector<equation_vector>& use_list) {
        unsigned_vector const& fv = m.free_vars(e->poly());
        for (unsigned v : fv) {
            use_list.reserve(v + 1);
            use_list[v].push_back(e);
        }
    }

    void grobner::superpose(equation const & eq) {
        for (equation* target : m_processed) {
            superpose(eq, *target);
        }
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
    void grobner::superpose(equation const& eq1, equation const& eq2) {
        TRACE("grobner_d", display(tout << "eq1=", eq1); display(tout << "eq2=", eq2););
        pdd r(m);
        if (m.try_spoly(eq1.poly(), eq2.poly(), r) && 
            !r.is_zero() && !is_too_complex(r)) {
            m_stats.m_superposed++;
            add(r, m_dep_manager.mk_join(eq1.dep(), eq2.dep()));
        }
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
        TRACE("grobner", display(tout << "eq = ", eq););
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
        SASSERT(is_tuned());
        pdd const& p = eq.poly();
        if (!p.is_val()) {
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
                pop_equation(eq, m_to_simplify);
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
        return 
            m_to_simplify.size() + m_processed.size() >= m_config.m_eqs_threshold || 
            canceled() || 
            m_conflict != nullptr;
    }

    void grobner::del_equation(equation& eq) {
        pop_equation(eq, eq.is_processed() ? m_processed : m_to_simplify);
        retire(&eq);
    }

    void grobner::pop_equation(equation& eq, equation_vector& v) {
        unsigned idx = eq.idx();
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

