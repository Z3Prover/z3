/*++
  Copyright (c) 2019 Microsoft Corporation

  Abstract:

    Grobner core based on pdd representation of polynomials

  Author:
     Nikolaj Bjorner (nbjorner)
     Lev Nachmanson (levnach)

  --*/

#include "math/grobner/pdd_grobner.h"
#include "util/uint_set.h"

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
        simplify();
        if (is_tuned()) tuned_init();
        TRACE("grobner", display(tout););
        try {
            while (!done() && step()) {
                TRACE("grobner", display(tout););
                DEBUG_CODE(invariant(););
            }
            DEBUG_CODE(invariant(););
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

    grobner::scoped_process::~scoped_process() {
        if (e) {
            pdd p = e->poly();
            SASSERT(!p.is_val());
            if (p.hi().is_val()) {
                g.push_equation(solved, e);
            }
            else {
                g.push_equation(processed, e);
            }
        }
    }

    bool grobner::basic_step(equation* e) {
        if (!e) return false;
        scoped_process sd(*this, e);
        equation& eq = *e;
        TRACE("grobner", display(tout << "eq = ", eq); display(tout););
        SASSERT(eq.state() == to_simplify);
        if (!simplify_using(eq, m_processed)) return false;
        if (is_trivial(eq)) { sd.e = nullptr; retire(e); return true; }
        if (check_conflict(eq)) { sd.e = nullptr; return false; }
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
        if (eq) pop_equation(eq);
        return eq;
    }

    void grobner::simplify() {
        try {
            while (!done() &&
                   (simplify_linear_step(true) || 
                    simplify_elim_pure_step() ||
                    simplify_cc_step() || 
                    simplify_leaf_step() ||
                    simplify_linear_step(false) || 
                    /*simplify_elim_dual_step() ||*/
                    false)) {
                DEBUG_CODE(invariant(););
                TRACE("grobner", display(tout););
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

    bool grobner::simplify_linear_step(bool binary) {
        TRACE("grobner", tout << "binary " << binary << "\n";);
        equation_vector linear;
        for (equation* e : m_to_simplify) {
            pdd p = e->poly();
            if (binary) {
                if (p.is_binary()) linear.push_back(e);
            }
            else if (p.is_linear()) {
                linear.push_back(e);
            }
        }
        return simplify_linear_step(linear);
    }

    /**
       \brief simplify linear equations by using top variable as solution.
       The linear equation is moved to set of solved equations.
    */
    bool grobner::simplify_linear_step(equation_vector& linear) {
        if (linear.empty()) return false;
        use_list_t use_list = get_use_list();
        compare_top_var ctv;
        std::stable_sort(linear.begin(), linear.end(), ctv);
        equation_vector trivial;
        unsigned j = 0;
        for (equation* src : linear) {
            unsigned v = src->poly().var();
            equation_vector const& uses = use_list[v];
            TRACE("grobner", 
                  display(tout << "uses of: ", *src) << "\n";
                  for (equation* e : uses) {
                      display(tout, *e) << "\n";
                  });
            bool changed_leading_term;
            bool all_reduced = true;
            for (equation* dst : uses) {
                if (src == dst || is_trivial(*dst)) {
                    continue;                    
                }
                pdd q = dst->poly();
                if (!src->poly().is_binary() && !q.is_linear()) {
                    all_reduced = false;
                    continue;
                }
                remove_from_use(dst, use_list, v);
                simplify_using(*dst, *src, changed_leading_term);
                if (is_trivial(*dst)) {
                    trivial.push_back(dst);
                }
                else if (is_conflict(dst)) {
                    pop_equation(dst);
                    set_conflict(dst);
                    return true;
                }
                else if (changed_leading_term) {
                    pop_equation(dst);
                    push_equation(to_simplify, dst);
                }
                // v has been eliminated.
                SASSERT(!m.free_vars(dst->poly()).contains(v));
                add_to_use(dst, use_list);                
            }          
            if (all_reduced) {
                linear[j++] = src;              
            }
        }
        linear.shrink(j);      
        for (equation* src : linear) {
            pop_equation(src);
            push_equation(solved, src);
        }
        for (equation* e : trivial) {
            del_equation(e);
        }
        DEBUG_CODE(invariant(););
        return j > 0;
    }

    /**
       \brief simplify using congruences
       replace pair px + q and ry + q by
       px + q, px - ry
       since px = ry
     */
    bool grobner::simplify_cc_step() {
        TRACE("grobner", tout << "cc\n";);
        u_map<equation*> los;
        bool reduced = false;
        unsigned j = 0;
        for (equation* eq1 : m_to_simplify) {
            SASSERT(eq1->state() == to_simplify);
            pdd p = eq1->poly();
            auto* e = los.insert_if_not_there2(p.lo().index(), eq1);
            equation* eq2 = e->get_data().m_value;
            pdd q = eq2->poly();
            if (eq2 != eq1 && (p.hi().is_val() || q.hi().is_val()) && !p.lo().is_val()) {
                *eq1 = p - eq2->poly();
                *eq1 = m_dep_manager.mk_join(eq1->dep(), eq2->dep());
                reduced = true;
                if (is_trivial(*eq1)) {
                    retire(eq1);
                    continue;
                }
                else if (check_conflict(*eq1)) {
                    continue;
                }
            }
            m_to_simplify[j] = eq1;
            eq1->set_index(j++);
        }
        m_to_simplify.shrink(j);
        return reduced;
    }

    /**
       \brief remove ax+b from p if x occurs as a leaf in p and a is a constant.
    */
    bool grobner::simplify_leaf_step() {
        TRACE("grobner", tout << "leaf\n";);
        use_list_t use_list = get_use_list();
        equation_vector leaves;
        for (unsigned i = 0; i < m_to_simplify.size(); ++i) {
            equation* e = m_to_simplify[i];
            pdd p = e->poly();
            if (!p.hi().is_val()) {
                continue;
            }
            leaves.reset();
            for (equation* e2 : use_list[p.var()]) {
                if (e != e2 && e2->poly().var_is_leaf(p.var())) {
                    leaves.push_back(e2);
                }
            }
            for (equation* e2 : leaves) {
                bool changed_leading_term;
                remove_from_use(e2, use_list);
                simplify_using(*e2, *e, changed_leading_term);
                add_to_use(e2, use_list);
                if (is_trivial(*e2)) {
                    pop_equation(e2);
                    retire(e2);
                }
                else if (e2->poly().is_val()) {
                    pop_equation(e2);
                    set_conflict(*e2);
                    return true;
                }
                else if (changed_leading_term) {
                    pop_equation(e2);
                    push_equation(to_simplify, e2);
                }
            }
        }
        return false;
    }

    /**
       \brief treat equations as processed if top variable occurs only once.
    */
    bool grobner::simplify_elim_pure_step() {
        TRACE("grobner", tout << "pure\n";);
        use_list_t use_list = get_use_list();        
        unsigned j = 0;
        for (equation* e : m_to_simplify) {
            pdd p = e->poly();
            if (!p.is_val() && p.hi().is_val() && use_list[p.var()].size() == 1) {
                push_equation(solved, e);
            }
            else {
                m_to_simplify[j] = e;
                e->set_index(j++);
            }
        }
        if (j != m_to_simplify.size()) {
            m_to_simplify.shrink(j);
            return true;
        }
        return false;
    }

    /**
       \brief 
       reduce equations where top variable occurs only twice and linear in one of the occurrences.       
     */
    bool grobner::simplify_elim_dual_step() {
        use_list_t use_list = get_use_list();        
        unsigned j = 0;
        bool reduced = false;
        for (unsigned i = 0; i < m_to_simplify.size(); ++i) {
            equation* e = m_to_simplify[i];            
            pdd p = e->poly();
            // check that e is linear in top variable.
            if (e->state() != to_simplify) {
                reduced = true;
            }
            else if (!done() && !is_trivial(*e) && p.hi().is_val() && use_list[p.var()].size() == 2) {
                for (equation* e2 : use_list[p.var()]) {
                    if (e2 == e) continue;
                    bool changed_leading_term;

                    remove_from_use(e2, use_list);
                    simplify_using(*e2, *e, changed_leading_term);
                    if (is_conflict(e2)) {
                        pop_equation(e2);
                        set_conflict(e2);
                    }
                    // when e2 is trivial, leading term is changed
                    SASSERT(!is_trivial(*e2) || changed_leading_term);
                    if (changed_leading_term) {
                        pop_equation(e2);
                        push_equation(to_simplify, e2);
                    }
                    add_to_use(e2, use_list);
                    break;
                }
                reduced = true;
                push_equation(solved, e);
            }
            else {
                m_to_simplify[j] = e;
                e->set_index(j++);
            }
        }
        if (reduced) {
            // clean up elements in m_to_simplify 
            // they may have moved.
            m_to_simplify.shrink(j);
            j = 0;
            for (equation* e : m_to_simplify) {
                if (is_trivial(*e)) {
                    retire(e);
                }
                else if (e->state() == to_simplify) {
                    m_to_simplify[j] = e;
                    e->set_index(j++);
                }
            }
            m_to_simplify.shrink(j);
            return true;
        }
        else {
            return false;
        }
    }

    void grobner::add_to_use(equation* e, use_list_t& use_list) {
        unsigned_vector const& fv = m.free_vars(e->poly());
        for (unsigned v : fv) {
            use_list.reserve(v + 1);
            use_list[v].push_back(e);
        }
    }

    void grobner::remove_from_use(equation* e, use_list_t& use_list) {
        unsigned_vector const& fv = m.free_vars(e->poly());
        for (unsigned v : fv) {
            use_list.reserve(v + 1);
            use_list[v].erase(e);
        }
    }

    void grobner::remove_from_use(equation* e, use_list_t& use_list, unsigned except_v) {
        unsigned_vector const& fv = m.free_vars(e->poly());
        for (unsigned v : fv) {
            if (v != except_v) {
                use_list.reserve(v + 1);
                use_list[v].erase(e);
            }
        }
    }

    grobner::use_list_t grobner::get_use_list() {
        use_list_t use_list;
        for (equation * e : m_to_simplify) {
            add_to_use(e, use_list);
        }
        for (equation * e : m_processed) {
            add_to_use(e, use_list);
        }
        return use_list;
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
        do {
            simplified = false;
            for (equation* p : eqs) {
                if (try_simplify_using(eq, *p, changed_leading_term)) {
                    simplified = true;
                }
                if (canceled() || eq.poly().is_val()) {
                    break;
                }
            }
        }
        while (simplified && !eq.poly().is_val());

        TRACE("grobner", display(tout << "simplification result: ", eq););

        return !done();
    }

    /*
      Use the given equation to simplify equations in set
    */
    bool grobner::simplify_using(equation_vector& set, equation const& eq) {
        unsigned j = 0, sz = set.size();
        for (unsigned i = 0; i < sz; ++i) {
            equation& target = *set[i];
            bool changed_leading_term = false;
            bool simplified = !done() && try_simplify_using(target, eq, changed_leading_term); 
            if (simplified && is_trivial(target)) {
                retire(&target);
            }
            else if (simplified && check_conflict(target)) {
                // pushed to solved
            }
            else if (simplified && changed_leading_term) {
                SASSERT(target.state() == processed);
                push_equation(to_simplify, target);
                if (!m_watch.empty()) {
                    m_levelp1 = std::max(m_var2level[target.poly().var()]+1, m_levelp1);
                    add_to_watch(target);
                }
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
    bool grobner::try_simplify_using(equation& dst, equation const& src, bool& changed_leading_term) {
        if (&src == &dst) {
            return false;
        }
        m_stats.m_simplified++;
        pdd t = src.poly();
        pdd r = dst.poly().reduce(t);
        if (r == dst.poly() || is_too_complex(r)) {
            return false;
        }
        TRACE("grobner", 
              tout << "reduce: " << dst.poly() << "\n";
              tout << "using:  " << t << "\n";
              tout << "to:     " << r << "\n";);
        changed_leading_term = dst.state() == processed && m.different_leading_term(r, dst.poly());
        dst = r;
        dst = m_dep_manager.mk_join(dst.dep(), src.dep());
        update_stats_max_degree_and_size(dst);
        return true;
    }

    void grobner::simplify_using(equation & dst, equation const& src, bool& changed_leading_term) {
        if (&src == &dst) return;        
        m_stats.m_simplified++;
        pdd t = src.poly();
        pdd r = dst.poly().reduce(t);
        changed_leading_term = dst.state() == processed && m.different_leading_term(r, dst.poly());
        TRACE("grobner", 
              tout << "reduce: " << dst.poly() << "\n";
              tout << "using:  " << t << "\n";
              tout << "to:     " << r << "\n";);

        if (r == dst.poly()) return;
        dst = r;
        dst = m_dep_manager.mk_join(dst.dep(), src.dep());
        update_stats_max_degree_and_size(dst);
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
        scoped_process sd(*this, e);
        equation& eq = *e;
        SASSERT(!m_watch[eq.poly().var()].contains(e));
        SASSERT(eq.state() == to_simplify);
        if (!simplify_using(eq, m_processed)) return false;
        if (is_trivial(eq)) { sd.e = nullptr; retire(e); return true; }
        if (check_conflict(eq)) { sd.e = nullptr; return false; }
        if (!simplify_using(m_processed, eq)) return false;
        TRACE("grobner", display(tout << "eq = ", eq););
        superpose(eq);
        simplify_watch(eq);
        return true;
    }

    void grobner::tuned_init() {
        unsigned_vector const& l2v = m.get_level2var();
        m_level2var.resize(l2v.size());
        m_var2level.resize(l2v.size());
        for (unsigned i = 0; i < l2v.size(); ++i) {
            m_level2var[i] = l2v[i];
            m_var2level[l2v[i]] = i;
        }
        m_watch.reset();
        m_watch.reserve(m_level2var.size());
        m_levelp1 = m_level2var.size();
        for (equation* eq : m_to_simplify) add_to_watch(*eq);
    }

    void grobner::add_to_watch(equation& eq) {
        SASSERT(eq.state() == to_simplify);
        SASSERT(is_tuned());
        pdd const& p = eq.poly();
        if (!p.is_val()) {
            m_watch[p.var()].push_back(&eq);
        }
    }

    void grobner::simplify_watch(equation const& eq) {
        unsigned v = eq.poly().var();
        auto& watch = m_watch[v];
        unsigned j = 0;
        for (equation* _target : watch) {
            equation& target = *_target;
            SASSERT(target.state() == to_simplify);
            SASSERT(target.poly().var() == v);
            bool changed_leading_term = false;
            if (!done()) {
                try_simplify_using(target, eq, changed_leading_term);
            }
            if (is_trivial(target)) {
                pop_equation(target);
                retire(&target);
            }
            else if (is_conflict(target)) {
                pop_equation(target);
                set_conflict(target);
            }
            else if (target.poly().var() != v) {
                // move to other watch list
                m_watch[target.poly().var()].push_back(_target);
            }
            else {
                // keep watching same variable
                watch[j++] = _target;
            }
        }
        watch.shrink(j);        
    }

    grobner::equation* grobner::tuned_pick_next() {
        while (m_levelp1 > 0) {
            unsigned v = m_level2var[m_levelp1-1];
            equation_vector const& watch = m_watch[v];
            equation* eq = nullptr;
            for (equation* curr : watch) {
                pdd const& p = curr->poly();
                if (curr->state() == to_simplify && p.var() == v) {
                    if (!eq || is_simpler(*curr, *eq))
                        eq = curr;
                }
            }
            if (eq) {
                pop_equation(eq);
                m_watch[eq->poly().var()].erase(eq);
                return eq;
            }
            --m_levelp1;
        }
        return nullptr;
    }

    grobner::equation_vector const& grobner::equations() {
        m_all_eqs.reset();
        for (equation* eq : m_solved) m_all_eqs.push_back(eq);
        for (equation* eq : m_to_simplify) m_all_eqs.push_back(eq);
        for (equation* eq : m_processed) m_all_eqs.push_back(eq);
        return m_all_eqs;
    }

    void grobner::reset() {
        for (equation* e : m_solved) dealloc(e);
        for (equation* e : m_to_simplify) dealloc(e);
        for (equation* e : m_processed) dealloc(e);
        m_solved.reset();
        m_processed.reset();
        m_to_simplify.reset();
        m_stats.reset();
        m_watch.reset();
        m_level2var.reset();
        m_var2level.reset();
        m_conflict = nullptr;
    }

    void grobner::add(pdd const& p, u_dependency * dep) {
        if (p.is_zero()) return;
        equation * eq = alloc(equation, p, dep);
        if (check_conflict(*eq)) {
            return;
        }
        push_equation(to_simplify, eq);
        
        if (!m_watch.empty()) {
            m_levelp1 = std::max(m_var2level[p.var()]+1, m_levelp1);
            add_to_watch(*eq);
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

    grobner::equation_vector& grobner::get_queue(equation const& eq) {
        switch (eq.state()) {
        case processed: return m_processed;
        case to_simplify: return m_to_simplify;
        case solved: return m_solved;
        }
        UNREACHABLE();
        return m_to_simplify;
    }

    void grobner::del_equation(equation* eq) {
        pop_equation(eq);
        retire(eq);
    }

    void grobner::pop_equation(equation& eq) {
        equation_vector& v = get_queue(eq);
        unsigned idx = eq.idx();
        if (idx != v.size() - 1) {
            equation* eq2 = v.back();
            eq2->set_index(idx);
            v[idx] = eq2;
        }
        v.pop_back();            
    }

    void grobner::push_equation(eq_state st, equation& eq) {
        eq.set_state(st);
        equation_vector& v = get_queue(eq);
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
        out << "solved\n"; for (auto e : m_solved) display(out, *e);
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
            VERIFY(e->state() == processed);
            VERIFY(e->idx() == i);
            VERIFY(!e->poly().is_val());
            ++i;
        }

        i = 0;
        uint_set head_vars;
        for (auto* e : m_solved) {
            VERIFY(e->state() == solved);
            VERIFY(e->idx() == i);
            ++i;
            pdd p = e->poly();
            if (!p.is_val() && p.hi().is_val()) {
                unsigned v = p.var();
                SASSERT(!head_vars.contains(v));
                head_vars.insert(v);
            }
        }

        if (!head_vars.empty()) {
            for (auto * e : m_to_simplify) {
                for (auto v : m.free_vars(e->poly())) VERIFY(!head_vars.contains(v));
            }
            for (auto * e : m_processed) {
                for (auto v : m.free_vars(e->poly())) VERIFY(!head_vars.contains(v));
            }
        }

        // equations in to_simplify have correct indices
        // they are labeled as non-processed
        // their top-most variable is watched
        i = 0;
        for (auto* e : m_to_simplify) {
            VERIFY(e->idx() == i);
            VERIFY(e->state() == to_simplify);
            pdd const& p = e->poly();
            VERIFY(!p.is_val());
            CTRACE("grobner", !m_watch.empty() && !m_watch[p.var()].contains(e), 
                   display(tout << "not watched: ", *e) << "\n";);
            VERIFY(m_watch.empty() || m_watch[p.var()].contains(e));            
            ++i;
        }
        // the watch list consists of equations in to_simplify
        // they watch the top most variable in poly
        i = 0;
        for (auto const& w : m_watch) {            
            for (equation* e : w) {
                VERIFY(!e->poly().is_val());
                VERIFY(e->poly().var() == i);
                VERIFY(e->state() == to_simplify);
                VERIFY(m_to_simplify.contains(e));
            }
            ++i;
        }
    }
}

