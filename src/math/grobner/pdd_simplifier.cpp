/*++
  Copyright (c) 2020 Microsoft Corporation


  Abstract:

    simplification routines for pdd polys

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

  Notes:


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

  --*/

#include "math/grobner/pdd_simplifier.h"
#include "math/simplex/bit_matrix.h"

namespace dd {


    void simplifier::operator()() {
        try {
            while (!s.done() &&
                   (simplify_linear_step(true) || 
                    simplify_elim_pure_step() ||
                    simplify_cc_step() || 
                    simplify_leaf_step() ||
                    simplify_linear_step(false) || 
                    /*simplify_elim_dual_step() ||*/
                    simplify_exlin() ||
                    false)) {
                DEBUG_CODE(s.invariant(););
                TRACE("dd.solver", s.display(tout););
            }
        }
        catch (pdd_manager::mem_out) {
            IF_VERBOSE(2, verbose_stream() << "simplifier memout\n");
            // done reduce
            DEBUG_CODE(s.invariant(););
        }
    }

    struct simplifier::compare_top_var {
        bool operator()(equation* a, equation* b) const {
            return a->poly().var() < b->poly().var();
        }
    };

    bool simplifier::simplify_linear_step(bool binary) {
        TRACE("dd.solver", tout << "binary " << binary << "\n";);
        IF_VERBOSE(2, verbose_stream() << "binary " << binary << "\n");
        equation_vector linear;
        for (equation* e : s.m_to_simplify) {
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
    bool simplifier::simplify_linear_step(equation_vector& linear) {
        if (linear.empty()) return false;
        use_list_t use_list = get_use_list();
        compare_top_var ctv;
        std::stable_sort(linear.begin(), linear.end(), ctv);
        equation_vector trivial;
        unsigned j = 0;
        bool has_conflict = false;
        for (equation* src : linear) {
            if (has_conflict) {
                break;
            }
            unsigned v = src->poly().var();
            equation_vector const& uses = use_list[v];
            TRACE("dd.solver", 
                  s.display(tout << "uses of: ", *src) << "\n";
                  for (equation* e : uses) {
                      s.display(tout, *e) << "\n";
                  });
            bool changed_leading_term;
            bool all_reduced = true;
            for (equation* dst : uses) {
                if (src == dst || s.is_trivial(*dst)) {
                    continue;                    
                }
                pdd q = dst->poly();
                if (!src->poly().is_binary() && !q.is_linear()) {
                    all_reduced = false;
                    continue;
                }
                remove_from_use(dst, use_list, v);
                s.simplify_using(*dst, *src, changed_leading_term);
                if (s.is_trivial(*dst)) {
                    trivial.push_back(dst);
                }
                else if (s.is_conflict(dst)) {
                    s.pop_equation(dst);
                    s.set_conflict(dst);
                    has_conflict = true;
                }
                else if (changed_leading_term) {
                    s.pop_equation(dst);
                    s.push_equation(solver::to_simplify, dst);
                }
                // v has been eliminated.
                //                SASSERT(!dst->poly().free_vars().contains(v));
                add_to_use(dst, use_list);                
            }          
            if (all_reduced) {
                linear[j++] = src;              
            }
        }
        if (!has_conflict) {
            linear.shrink(j);      
            for (equation* src : linear) {
                s.pop_equation(src);
                s.push_equation(solver::solved, src);
            }
        }
        for (equation* e : trivial) {
            s.del_equation(e);
        }
        DEBUG_CODE(s.invariant(););
        return j > 0 || has_conflict;
    }

    /**
       \brief simplify using congruences
       replace pair px + q and ry + q by
       px + q, px - ry
       since px = ry
     */
    bool simplifier::simplify_cc_step() {
        TRACE("dd.solver", tout << "cc\n";);
        IF_VERBOSE(2, verbose_stream() << "cc\n");
        u_map<equation*> los;
        bool reduced = false;
        unsigned j = 0;
        for (equation* eq1 : s.m_to_simplify) {
            SASSERT(eq1->state() == solver::to_simplify);
            pdd p = eq1->poly();
            auto* e = los.insert_if_not_there2(p.lo().index(), eq1);
            equation* eq2 = e->get_data().m_value;
            pdd q = eq2->poly();
            if (eq2 != eq1 && (p.hi().is_val() || q.hi().is_val()) && !p.lo().is_val()) {
                *eq1 = p - eq2->poly();
                *eq1 = s.m_dep_manager.mk_join(eq1->dep(), eq2->dep());
                reduced = true;
                if (s.is_trivial(*eq1)) {
                    s.retire(eq1);
                    continue;
                }
                else if (s.check_conflict(*eq1)) {
                    continue;
                }
            }
            s.m_to_simplify[j] = eq1;
            eq1->set_index(j++);
        }
        s.m_to_simplify.shrink(j);
        return reduced;
    }

    /**
       \brief remove ax+b from p if x occurs as a leaf in p and a is a constant.
    */
    bool simplifier::simplify_leaf_step() {
        TRACE("dd.solver", tout << "leaf\n";);
        IF_VERBOSE(2, verbose_stream() << "leaf\n");
        use_list_t use_list = get_use_list();
        equation_vector leaves;
        for (unsigned i = 0; i < s.m_to_simplify.size(); ++i) {
            equation* e = s.m_to_simplify[i];
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
                s.simplify_using(*e2, *e, changed_leading_term);
                add_to_use(e2, use_list);
                if (s.is_trivial(*e2)) {
                    s.pop_equation(e2);
                    s.retire(e2);
                }
                else if (e2->poly().is_val()) {
                    s.pop_equation(e2);
                    s.set_conflict(*e2);
                    return true;
                }
                else if (changed_leading_term) {
                    s.pop_equation(e2);
                    s.push_equation(solver::to_simplify, e2);
                }
            }
        }
        return false;
    }

    /**
       \brief treat equations as processed if top variable occurs only once.
    */
    bool simplifier::simplify_elim_pure_step() {
        TRACE("dd.solver", tout << "pure\n";);
        IF_VERBOSE(2, verbose_stream() << "pure\n");
        use_list_t use_list = get_use_list();        
        unsigned j = 0;
        for (equation* e : s.m_to_simplify) {
            pdd p = e->poly();
            if (!p.is_val() && p.hi().is_val() && use_list[p.var()].size() == 1) {
                s.push_equation(solver::solved, e);
            }
            else {
                s.m_to_simplify[j] = e;
                e->set_index(j++);
            }
        }
        if (j != s.m_to_simplify.size()) {
            s.m_to_simplify.shrink(j);
            return true;
        }
        return false;
    }

    /**
       \brief 
       reduce equations where top variable occurs only twice and linear in one of the occurrences.       
     */
    bool simplifier::simplify_elim_dual_step() {
        use_list_t use_list = get_use_list();        
        unsigned j = 0;
        bool reduced = false;
        for (unsigned i = 0; i < s.m_to_simplify.size(); ++i) {
            equation* e = s.m_to_simplify[i];            
            pdd p = e->poly();
            // check that e is linear in top variable.
            if (e->state() != solver::to_simplify) {
                reduced = true;
            }
            else if (!s.done() && !s.is_trivial(*e) && p.hi().is_val() && use_list[p.var()].size() == 2) {
                for (equation* e2 : use_list[p.var()]) {
                    if (e2 == e) continue;
                    bool changed_leading_term;

                    remove_from_use(e2, use_list);
                    s.simplify_using(*e2, *e, changed_leading_term);
                    if (s.is_conflict(e2)) {
                        s.pop_equation(e2);
                        s.set_conflict(e2);
                    }
                    // when e2 is trivial, leading term is changed
                    SASSERT(!s.is_trivial(*e2) || changed_leading_term);
                    if (changed_leading_term) {
                        s.pop_equation(e2);
                        s.push_equation(solver::to_simplify, e2);
                    }
                    add_to_use(e2, use_list);
                    break;
                }
                reduced = true;
                s.push_equation(solver::solved, e);
            }
            else {
                s.m_to_simplify[j] = e;
                e->set_index(j++);
            }
        }
        if (reduced) {
            // clean up elements in s.m_to_simplify 
            // they may have moved.
            s.m_to_simplify.shrink(j);
            j = 0;
            for (equation* e : s.m_to_simplify) {
                if (s.is_trivial(*e)) {
                    s.retire(e);
                }
                else if (e->state() == solver::to_simplify) {
                    s.m_to_simplify[j] = e;
                    e->set_index(j++);
                }
            }
            s.m_to_simplify.shrink(j);
            return true;
        }
        else {
            return false;
        }
    }

    void simplifier::add_to_use(equation* e, use_list_t& use_list) {
        unsigned_vector const& fv = e->poly().free_vars();
        for (unsigned v : fv) {
            use_list.reserve(v + 1);
            use_list[v].push_back(e);
        }
    }

    void simplifier::remove_from_use(equation* e, use_list_t& use_list) {
        unsigned_vector const& fv = e->poly().free_vars();
        for (unsigned v : fv) {
            use_list.reserve(v + 1);
            use_list[v].erase(e);
        }
    }

    void simplifier::remove_from_use(equation* e, use_list_t& use_list, unsigned except_v) {
        unsigned_vector const& fv = e->poly().free_vars();
        for (unsigned v : fv) {
            if (v != except_v) {
                use_list.reserve(v + 1);
                use_list[v].erase(e);
            }
        }
    }

    simplifier::use_list_t simplifier::get_use_list() {
        use_list_t use_list;
        for (equation * e : s.m_to_simplify) {
            add_to_use(e, use_list);
        }
        for (equation * e : s.m_processed) {
            add_to_use(e, use_list);
        }
        return use_list;
    }


    /**
       \brief use Gauss elimination to extract linear equalities.
       So far just for GF(2) semantics.
     */

    bool simplifier::simplify_exlin() {
        if (s.m.get_semantics() != pdd_manager::mod2_e ||
            !s.m_config.m_enable_exlin) {
            return false;
        }
        vector<pdd> eqs, simp_eqs;
        for (auto* e : s.m_to_simplify) if (!e->dep()) eqs.push_back(e->poly());
        for (auto* e : s.m_processed) if (!e->dep()) eqs.push_back(e->poly());
        vector<uint_set> orbits(s.m.num_vars());
        init_orbits(eqs, orbits);
        exlin_augment(orbits, eqs);        
        simplify_exlin(orbits, eqs, simp_eqs);
        for (pdd const& p : simp_eqs) {
            s.add(p);
        }        
        IF_VERBOSE(10, verbose_stream() << "simp_linear " << simp_eqs.size() << "\n";);
        return !simp_eqs.empty() && simplify_linear_step(false);
    }

    void simplifier::init_orbits(vector<pdd> const& eqs, vector<uint_set>& orbits) {
        for (pdd const& p : eqs) {
            auto const& fv = p.free_vars();
            for (unsigned i = fv.size(); i-- > 0; ) {
                orbits[fv[i]].insert(fv[i]); // if v is used, it is in its own orbit.
                for (unsigned j = i; j-- > 0; ) {
                    orbits[fv[i]].insert(fv[j]);
                    orbits[fv[j]].insert(fv[i]);
                }
            }
        }
    }


    /**
       augment set of equations by multiplying with selected variables.
       Uses orbits to prune which variables are multiplied.
       TBD: could also prune added polynomials based on a maximal degree.
       TBD: for large systems, extract cluster of polynomials based on sampling orbits       
     */

    void simplifier::exlin_augment(vector<uint_set> const& orbits, vector<pdd>& eqs) {
        IF_VERBOSE(10, verbose_stream() << "pdd-exlin augment\n";);
        unsigned nv = s.m.num_vars();
        random_gen rand(s.m_config.m_random_seed);
        unsigned modest_num_eqs = std::max(eqs.size(), 500u);
        unsigned max_xlin_eqs = modest_num_eqs;
        unsigned max_degree = 5;
        TRACE("dd.solver", tout << "augment " << nv << "\n";
              for (auto const& o : orbits) tout << o.num_elems() << "\n";);
        vector<pdd> n_eqs;
        unsigned start = rand();
        for (unsigned _v = 0; _v < nv; ++_v) {
            unsigned v = (_v + start) % nv;
            auto const& orbitv = orbits[v];
            if (orbitv.empty()) continue;
            pdd pv = s.m.mk_var(v);
            for (pdd p : eqs) {
                if (p.degree() > max_degree) continue;
                for (unsigned w : p.free_vars()) {
                    if (v != w && orbitv.contains(w)) {
                        n_eqs.push_back(pv * p);
                        if (n_eqs.size() > max_xlin_eqs) {
                            goto end_of_new_eqs;
                        }
                        break;
                    }
                }
            }
        }

        start = rand();
        for (unsigned _v = 0; _v < nv; ++_v) {
            unsigned v = (_v + start) % nv;
            auto const& orbitv = orbits[v];
            if (orbitv.empty()) continue;
            pdd pv = s.m.mk_var(v);
            for (unsigned w : orbitv) {
                if (v >= w) continue;
                pdd pw = s.m.mk_var(w);
                for (pdd p : eqs) {
                    if (p.degree() + 1 > max_degree) continue;
                    for (unsigned u : p.free_vars()) {
                        if (orbits[w].contains(u) || orbits[v].contains(u)) {
                            n_eqs.push_back(pw * pv * p);
                            if (n_eqs.size() > max_xlin_eqs) {
                                goto end_of_new_eqs;
                            }
                            break;
                        }
                    }
                }
            }
        }
    end_of_new_eqs:
        s.m_config.m_random_seed = rand();
        eqs.append(n_eqs);
        TRACE("dd.solver", for (pdd const& p : eqs) tout << p << "\n";);
    }

    void simplifier::simplify_exlin(vector<uint_set> const& orbits, vector<pdd> const& eqs, vector<pdd>& simp_eqs) {
        IF_VERBOSE(10, verbose_stream() << "pdd simplify-exlin\n";);
        // index monomials
        unsigned_vector vars;
        struct mon {
            unsigned sz;
            unsigned offset;
            unsigned index;
            mon(unsigned sz, unsigned offset): sz(sz), offset(offset), index(UINT_MAX) {}
            mon(): sz(0), offset(0), index(UINT_MAX) {}
            bool is_valid() const { return index != UINT_MAX; }
            struct hash { 
                unsigned_vector& vars;
                hash(unsigned_vector& vars):vars(vars) {}
                bool operator()(mon const& m) const {
                    return unsigned_ptr_hash(vars.c_ptr() + m.offset, m.sz, 1);
                };
            };
            struct eq {
                unsigned_vector& vars;
                eq(unsigned_vector& vars):vars(vars) {}
                bool operator()(mon const& a, mon const& b) const {
                    if (a.sz != b.sz) return false;
                    for (unsigned i = 0; i < a.sz; ++i) 
                        if (vars[a.offset+i] != vars[b.offset+i]) 
                            return false;
                    return true;
                }
            };
        };
        mon::hash mon_hash(vars);
        mon::eq mon_eq(vars);
        hashtable<mon, mon::hash, mon::eq> mon2idx(DEFAULT_HASHTABLE_INITIAL_CAPACITY, mon_hash, mon_eq);
        svector<mon> idx2mon;

        auto insert_mon = [&](unsigned n, unsigned const* vs) {
            mon mm(n, vars.size());
            vars.append(n, vs);
            auto* e = mon2idx.insert_if_not_there2(mm);
            if (!e->get_data().is_valid()) {
                e->get_data().index = idx2mon.size();
                idx2mon.push_back(e->get_data());
            }
            else {
                vars.shrink(vars.size() - n);
            }
        };
        
        // insert monomials of degree > 1
        for (pdd const& p : eqs) {
            for (auto const& m : p) {
                if (m.vars.size() <= 1) continue;
                insert_mon(m.vars.size(), m.vars.c_ptr());
            }
        }
        
        // insert variables last.
        unsigned nv = s.m.num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            if (!orbits[v].empty()) { // not all variables are used.
                insert_mon(1, &v);
            }                           
        }

        IF_VERBOSE(10, verbose_stream() << "extracted monomials: " << idx2mon.size() << "\n";);


        bit_matrix bm;
        unsigned const_idx = idx2mon.size();
        bm.reset(const_idx + 1);

        // populate rows 
        for (pdd const& p : eqs) {
            if (p.is_zero()) {
                continue;
            }
            auto row = bm.add_row();
            for (auto const& m : p) {
                SASSERT(m.coeff.is_one());
                if (m.vars.empty()) {
                    row.set(const_idx);
                    continue;
                }
                unsigned n = m.vars.size();
                mon mm(n, vars.size());
                vars.append(n, m.vars.c_ptr());
                VERIFY(mon2idx.find(mm, mm));
                vars.shrink(vars.size() - n);
                row.set(mm.index);
            }
        }

        TRACE("dd.solver", tout << bm << "\n";);
        IF_VERBOSE(10, verbose_stream() << "bit-matrix solving\n");

        bm.solve();

        TRACE("dd.solver", tout << bm << "\n";);
        IF_VERBOSE(10, verbose_stream() << "bit-matrix solved\n");

        for (auto const& r : bm) {
            bool is_linear = true;
            for (unsigned c : r) {
                SASSERT(r[c]);
                if (c == const_idx) {
                    break;
                }
                if (idx2mon[c].sz != 1) {
                    is_linear = false;
                    break;
                }
            }

            if (is_linear) {
                pdd p = s.m.zero();
                for (unsigned c : r) {
                    if (c == const_idx) {
                        p += s.m.one();
                    }
                    else {
                        mon const& mm = idx2mon[c];
                        p += s.m.mk_var(vars[mm.offset]);
                    }
                }
                if (!p.is_zero()) {
                    TRACE("dd.solver", tout << "new linear: " << p << "\n";);
                    simp_eqs.push_back(p);
                }
            }

            // could also consider singleton monomials as Bosphorus does
            // Singleton monomials are of the form v*w*u*v == 0            
            // Generally want to deal with negations too
            // v*(w+1)*u will have shared pdd under w, 
            // e.g, test every variable in p whether it has hi() == lo().
            // maybe easier to read out of a pdd than the expanded form.
        }
    }

}
