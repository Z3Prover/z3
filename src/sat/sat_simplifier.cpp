/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_simplifier.cpp

Abstract:

    SAT simplification procedures that use a "full" occurrence list:
    Subsumption, Blocked Clause Removal, Variable Elimination, ...


Author:

    Leonardo de Moura (leonardo) 2011-05-24.

Revision History:

--*/
#include "sat/sat_simplifier.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_solver.h"
#include "sat/sat_elim_vars.h"
#include "sat/sat_integrity_checker.h"
#include "util/stopwatch.h"
#include "util/trace.h"

namespace sat {

    void use_list::init(unsigned num_vars) {
        m_use_list.reset();
        unsigned num_lits = 2 * num_vars;
        m_use_list.resize(num_lits);
    }

    void use_list::insert(clause & c) {
        for (literal l : c) 
            m_use_list[l.index()].insert(c);
    }

    void use_list::erase(clause & c) {
        for (literal l : c) 
            m_use_list[l.index()].erase(c);
    }

    void use_list::erase(clause & c, literal l) {
        for (literal l2 : c) 
            if (l2 != l)
                m_use_list[l2.index()].erase(c);
    }

    void use_list::block(clause& c) {
        for (literal l : c) 
            m_use_list[l.index()].block(c);
    }

    void use_list::unblock(clause& c) {
        for (literal l : c) 
            m_use_list[l.index()].unblock(c);
    }

    simplifier::simplifier(solver & _s, params_ref const & p):
        s(_s),
        m_num_calls(0) {
        updt_params(p);
        reset_statistics();
    }

    simplifier::~simplifier() {
        finalize();
    }

    watch_list & simplifier::get_wlist(literal l) { return s.get_wlist(l); }

    watch_list const & simplifier::get_wlist(literal l) const { return s.get_wlist(l); }

    bool simplifier::is_external(bool_var v) const { 
        return 
            s.is_assumption(v) ||
            (s.is_external(v) && s.is_incremental()) ||
            (s.is_external(v) && s.m_ext &&
             (!m_ext_use_list.get(literal(v, false)).empty() ||
              !m_ext_use_list.get(literal(v, true)).empty()));
    }

    inline bool simplifier::was_eliminated(bool_var v) const { return s.was_eliminated(v); }

    lbool simplifier::value(bool_var v) const { return s.value(v); }

    lbool simplifier::value(literal l) const { return s.value(l); }

    inline void simplifier::checkpoint() { s.checkpoint(); }

    bool simplifier::single_threaded() const { return s.m_config.m_num_threads == 1; }

    bool simplifier::bce_enabled_base() const {
        return 
            !m_incremental_mode && !s.tracking_assumptions() && 
            !m_learned_in_use_lists && m_num_calls >= m_bce_delay && single_threaded();
    }

    bool simplifier::ate_enabled()  const { return m_num_calls >= m_bce_delay && m_ate; }
    bool simplifier::bce_enabled()  const { return bce_enabled_base() && (m_bce || m_bce_at == m_num_calls || m_acce || m_abce || m_cce); }
    bool simplifier::acce_enabled() const { return bce_enabled_base() && m_acce; }
    bool simplifier::cce_enabled()  const { return bce_enabled_base() && (m_cce || m_acce); }
    bool simplifier::abce_enabled() const { return bce_enabled_base() && m_abce; }
    bool simplifier::bca_enabled()  const { return bce_enabled_base() && m_bca; }
    bool simplifier::elim_vars_bdd_enabled() const { 
        return !m_incremental_mode && !s.tracking_assumptions() && m_elim_vars_bdd && m_num_calls >= m_elim_vars_bdd_delay && single_threaded(); 
    }
    bool simplifier::elim_vars_enabled() const { 
        return !m_incremental_mode && !s.tracking_assumptions() && m_elim_vars && single_threaded(); 
    }    

    void simplifier::register_clauses(clause_vector & cs) {
        std::stable_sort(cs.begin(), cs.end(), size_lt());
        for (clause* c : cs) {
            if (!c->frozen()) {
                m_use_list.insert(*c);
                if (c->strengthened())
                    m_sub_todo.insert(*c);
            }
        }
    }

    inline void simplifier::remove_clause_core(clause & c) {
        for (literal l : c) 
            insert_elim_todo(l.var());
        m_sub_todo.erase(c);
        c.set_removed(true);
        TRACE("resolution_bug", tout << "del_clause: " << c << "\n";);
        m_need_cleanup = true;
    }

    inline void simplifier::remove_clause(clause & c) {
        remove_clause_core(c);
        m_use_list.erase(c);
    }

    inline void simplifier::remove_clause(clause & c, literal l) {
        remove_clause_core(c);
        m_use_list.erase(c, l);
    }

    inline void simplifier::set_learned(clause & c) {
        m_need_cleanup = true;
        s.set_learned(c, true);
        m_use_list.block(c);
    }

    inline void simplifier::set_learned(literal l1, literal l2) {
        m_sub_bin_todo.erase(bin_clause(l1, l2, false));
        m_sub_bin_todo.erase(bin_clause(l2, l1, false));
        m_sub_bin_todo.push_back(bin_clause(l1, l2, true));
        m_sub_bin_todo.push_back(bin_clause(l2, l1, true));
    }

    void simplifier::init_visited() {
        m_visited.reset();
        m_visited.resize(2*s.num_vars(), false);
    }

    void simplifier::finalize() {
        m_use_list.finalize();
        m_sub_todo.finalize();
        m_sub_bin_todo.finalize();
        m_elim_todo.finalize();
        m_visited.finalize();
        m_bs_cs.finalize();
        m_bs_ls.finalize();
        m_ext_use_list.finalize();
    }

    void simplifier::initialize() {
        m_need_cleanup = false;
        s.m_cleaner(true);
        m_last_sub_trail_sz = s.m_trail.size();
        m_use_list.init(s.num_vars());
        if (s.m_ext) s.m_ext->init_use_list(m_ext_use_list);
        m_sub_todo.reset();
        m_sub_bin_todo.reset();
        m_elim_todo.reset();
        init_visited();
        TRACE("after_cleanup", s.display(tout););
        CASSERT("sat_solver", s.check_invariant());
    }

    void simplifier::operator()(bool learned) {

        if (s.inconsistent())
            return;
        if (!m_subsumption && !bce_enabled() && !bca_enabled() && !elim_vars_enabled())
            return;
        
        initialize();

        CASSERT("sat_solver", s.check_invariant());
        TRACE("sat_simplifier", s.display(tout););

        s.m_cleaner(true);
        TRACE("after_cleanup", s.display(tout););
        CASSERT("sat_solver", s.check_invariant());
        m_need_cleanup = false;
        m_use_list.init(s.num_vars());
        m_learned_in_use_lists = learned;
        if (learned) {
            register_clauses(s.m_learned);
        }
        register_clauses(s.m_clauses);

        if (!learned && (bce_enabled() || bca_enabled() || ate_enabled())) {
            elim_blocked_clauses();
        }

        if (!learned) {
            m_num_calls++;
        }

        m_sub_counter  = m_subsumption_limit;
        m_elim_counter = m_res_limit;
        m_old_num_elim_vars = m_num_elim_vars;

        for (bool_var v = 0; v < s.num_vars(); ++v) {
            if (!s.m_eliminated[v] && !is_external(v)) {
                insert_elim_todo(v);
            }
        }

        do {
            if (m_subsumption)
                subsume();
            if (s.inconsistent())
                return;
            if (!learned && elim_vars_enabled())
                elim_vars();            
            if (s.inconsistent())
                return;
            if (!m_subsumption || m_sub_counter < 0)
                break;
        }
        while (!m_sub_todo.empty());
        bool vars_eliminated = m_num_elim_vars > m_old_num_elim_vars;

        if (m_need_cleanup || vars_eliminated) {
            TRACE("after_simplifier", tout << "cleanning watches...\n";);
            cleanup_watches();
            move_clauses(s.m_learned, true);
            move_clauses(s.m_clauses, false);
            cleanup_clauses(s.m_learned, true, vars_eliminated,  m_learned_in_use_lists);
            cleanup_clauses(s.m_clauses, false, vars_eliminated, true);
        }

        CASSERT("sat_solver", s.check_invariant());
        TRACE("sat_simplifier", s.display(tout); tout << "model_converter:\n"; s.m_mc.display(tout););

        finalize();
    }

    /**
       \brief Eliminate all ternary and clause watches.
    */
    void simplifier::cleanup_watches() {
        for (watch_list& wlist : s.m_watches) {
            watch_list::iterator it2    = wlist.begin();
            watch_list::iterator itprev = it2;
            watch_list::iterator end2   = wlist.end();
            for (; it2 != end2; ++it2) {
                switch (it2->get_kind()) {
                case watched::TERNARY:
                case watched::CLAUSE:
                    // consume
                    break;
                default:
                    *itprev = *it2;
                    itprev++;
                    break;
                }
            }
            wlist.set_end(itprev);            
        }
    }

    void simplifier::move_clauses(clause_vector& cs, bool learned) {
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        unsigned nm = 0;
        for (; it != end; ++it) {
            clause & c = *(*it);
            if (learned && !c.is_learned()) {
                s.m_clauses.push_back(&c);
                ++nm;
            }
            else if (!learned && c.is_learned()) {
                s.m_learned.push_back(&c);
                ++nm;
            }
            else {
                *it2 = *it;
                ++it2;
            }
        }
        cs.set_end(it2);
    }

    void simplifier::cleanup_clauses(clause_vector & cs, bool learned, bool vars_eliminated, bool in_use_lists) {
        TRACE("sat", tout << "cleanup_clauses\n";);
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            VERIFY(learned == c.is_learned());
            if (c.was_removed()) {
                s.del_clause(c);
                continue;
            }

            if (learned && vars_eliminated) {
                unsigned sz = c.size();
                unsigned i;
                for (i = 0; i < sz; i++) {
                    if (was_eliminated(c[i].var()))
                        break;
                }
                if (i < sz) {
                    s.del_clause(c);
                    continue;
                }
            }

            if (cleanup_clause(c, in_use_lists)) {
                s.del_clause(c);
                continue;
            }
            unsigned sz = c.size();
            if (sz == 0) {
                s.set_conflict(justification());
                for (; it != end; ++it, ++it2) {
                    *it2 = *it;
                    ++it2;
                }
                break;
            }
            if (sz == 1) {
                s.assign(c[0], justification());
                s.del_clause(c);
                continue;
            }
            if (sz == 2) {
                s.mk_bin_clause(c[0], c[1], c.is_learned());
                s.del_clause(c);
                continue;
            }
            *it2 = *it;
            it2++;
            if (!c.frozen()) {
                s.attach_clause(c);
                if (s.m_config.m_drat) {
                    s.m_drat.add(c, true);
                }
            }
        }
        cs.set_end(it2);
    }

    void simplifier::mark_all_but(clause const & c, literal l1) {
        for (literal l2 : c) 
            if (l2 != l1)
                mark_visited(l2);
    }

    void simplifier::unmark_all(clause const & c) {
        for (literal l : c)
            unmark_visited(l);
    }

    /**
       \brief Return the variable in c with the minimal number positive+negative occurrences.
    */
    bool_var simplifier::get_min_occ_var(clause const & c) const {
        literal l_best = null_literal;
        unsigned best = UINT_MAX;
        for (literal l : c) {
            unsigned num = m_use_list.get(l).size() + m_use_list.get(~l).size();
            if (num < best) {
                l_best = l;
                best   = num;
            }
        }
        return l_best.var();
    }

    /**
       If c1 subsumes c2, return true
       If c2 can self subsumed by c1, return true and store the literal that can be removed from c2 in l.
       Otherwise return false
    */
    bool simplifier::subsumes1(clause const & c1, clause const & c2, literal & l) {
        for (literal lit : c2) 
            mark_visited(lit);

        bool r = true;
        l = null_literal;
        for (literal lit : c1) {
            if (!is_marked(lit)) {
                if (l == null_literal && is_marked(~lit)) {
                    l = ~lit;
                }
                else {
                    l = null_literal;
                    r = false;
                    break;
                }
            }
        }

        for (literal lit : c2) 
            unmark_visited(lit);
        return r;
    }

    /**
       \brief Return the clauses subsumed by c1 and the clauses that can be subsumed resolved using c1.
       The collections is populated using the use list of target.
    */
    void simplifier::collect_subsumed1_core(clause const & c1, clause_vector & out, literal_vector & out_lits,
                                            literal target) {
        clause_use_list const & cs = m_use_list.get(target);
        for (auto it = cs.mk_iterator(); !it.at_end(); it.next()) {
            clause & c2 = it.curr();
            CTRACE("resolution_bug", c2.was_removed(), tout << "clause has been removed:\n" << c2 << "\n";);
            SASSERT(!c2.was_removed());
            if (&c2 != &c1 &&
                c1.size() <= c2.size() &&
                approx_subset(c1.approx(), c2.approx())) {
                m_sub_counter -= c1.size() + c2.size();
                literal l;
                if (subsumes1(c1, c2, l)) {
                    out.push_back(&c2);
                    out_lits.push_back(l);
                }
            }
        }
    }

    /**
       \brief Return the clauses subsumed by c1 and the clauses that can be subsumed resolved using c1.
    */
    void simplifier::collect_subsumed1(clause const & c1, clause_vector & out, literal_vector & out_lits) {
        bool_var v = get_min_occ_var(c1);
        collect_subsumed1_core(c1, out, out_lits, literal(v, false));
        collect_subsumed1_core(c1, out, out_lits, literal(v, true));
    }

    /**
       \brief Perform backward subsumption and self-subsumption resolution using c1.
    */
    void simplifier::back_subsumption1(clause & c1) {
        m_bs_cs.reset();
        m_bs_ls.reset();
        collect_subsumed1(c1, m_bs_cs, m_bs_ls);
        SASSERT(m_bs_cs.size() == m_bs_ls.size());
        clause_vector::iterator it    = m_bs_cs.begin();
        clause_vector::iterator end   = m_bs_cs.end();
        literal_vector::iterator l_it = m_bs_ls.begin();
        for (; it != end; ++it, ++l_it) {
            clause & c2 = *(*it);
            if (!c2.was_removed() && *l_it == null_literal) {
                // c2 was subsumed
                if (c1.is_learned() && !c2.is_learned())
                    s.set_learned(c1, false);
                TRACE("subsumption", tout << c1 << " subsumed " << c2 << "\n";);
                remove_clause(c2);
                m_num_subsumed++;
            }
            else if (!c2.was_removed()) {
                // subsumption resolution
                TRACE("subsumption_resolution", tout << c1 << " sub-ref(" << *l_it << ") " << c2 << "\n";);
                elim_lit(c2, *l_it);
                m_num_sub_res++;
                TRACE("subsumption_resolution", tout << "result: " << c2 << "\n";);
            }
            if (s.inconsistent())
                break;
        }
    }

    void simplifier::back_subsumption1(literal l1, literal l2, bool learned) {
        m_dummy.set(l1, l2, learned);
        clause & c = *(m_dummy.get());
        back_subsumption1(c);
    }

    /**
       \brief Return the literal in c with the minimal number of occurrences.
    */
    literal simplifier::get_min_occ_var0(clause const & c) const {
        literal l_best = null_literal;
        unsigned best = UINT_MAX;
        for (literal l : c) {
            unsigned num = m_use_list.get(l).size();
            if (num < best) {
                l_best = l;
                best   = num;
            }
        }
        return l_best;
    }

    /**
       If c1 subsumes c2, return true
       Otherwise return false
    */
    bool simplifier::subsumes0(clause const & c1, clause const & c2) {
        for (literal l : c2) 
            mark_visited(l);

        bool r = true;
        for (literal l : c1) {
            if (!is_marked(l)) {
                r = false;
                break;
            }
        }

        for (literal l : c2)
            unmark_visited(l);

        return r;
    }

    /**
       \brief Collect the clauses subsumed by c1 (using the occurrence list of target).
    */
    void simplifier::collect_subsumed0_core(clause const & c1, clause_vector & out, literal target) {
        clause_use_list const & cs = m_use_list.get(target);
        clause_use_list::iterator it = cs.mk_iterator();
        for (; !it.at_end(); it.next()) {
            clause & c2 = it.curr();
            SASSERT(!c2.was_removed());
            if (&c2 != &c1 &&
                c1.size() <= c2.size() &&
                approx_subset(c1.approx(), c2.approx())) {
                m_sub_counter -= c1.size() + c2.size();
                if (subsumes0(c1, c2)) {
                    out.push_back(&c2);
                }
            }
        }
    }

    /**
       \brief Collect the clauses subsumed by c1
    */
    void simplifier::collect_subsumed0(clause const & c1, clause_vector & out) {
        literal l = get_min_occ_var0(c1);
        collect_subsumed0_core(c1, out, l);
    }


    /**
       \brief Perform backward subsumption using c1.
    */
    void simplifier::back_subsumption0(clause & c1) {
        m_bs_cs.reset();
        collect_subsumed0(c1, m_bs_cs);
        for (clause* cp : m_bs_cs) {
            clause & c2 = *cp;
            // c2 was subsumed
            if (c1.is_learned() && !c2.is_learned())
                s.set_learned(c1, false);
            TRACE("subsumption", tout << c1 << " subsumed " << c2 << "\n";);
            remove_clause(c2);
            m_num_subsumed++;
        }
    }

    /**
       \brief Eliminate false literals from c, and update occurrence lists

       Return true if the clause is satisfied
    */
    bool simplifier::cleanup_clause(clause & c, bool in_use_list) {
        bool r = false;
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; i++) {
            literal l = c[i];
            switch (value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            case l_false:
                m_need_cleanup = true;
                if (in_use_list && !c.frozen()) {
                    // Remark: if in_use_list is false, then the given clause was not added to the use lists.
                    // Remark: frozen clauses are not added to the use lists.
                    m_use_list.get(l).erase_not_removed(c);
                }
                break;
            case l_true:
                r = true;
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            }
        }
        if (j < sz) {
            if (s.m_config.m_drat) s.m_drat.del(c);
            c.shrink(j);
            if (s.m_config.m_drat) s.m_drat.add(c, true);
        }
        return r;
    }

    /**
       \brief Eliminate false literals from c.

       Return true if the clause is satisfied
    */
    bool simplifier::cleanup_clause(literal_vector & c) {
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; i++) {
            literal l = c[i];
            switch (value(l)) {
            case l_undef:
                if (i != j) {
                    std::swap(c[j], c[i]);
                }
                j++;
                break;
            case l_false:
                break;
            case l_true:
                return true;
            }
        }
        c.shrink(j);            
        return false;
    }

    inline void simplifier::propagate_unit(literal l) {
        unsigned old_trail_sz = s.m_trail.size();
        s.assign(l, justification());
        s.propagate_core(false); // must not use propagate(), since s.m_clauses is not in a consistent state.
        if (s.inconsistent())
            return;
        unsigned new_trail_sz = s.m_trail.size();
        for (unsigned i = old_trail_sz; i < new_trail_sz; i++) {
            literal l = s.m_trail[i];
            // put clauses with literals assigned to false back into todo-list
            for (auto it = m_use_list.get(~l).mk_iterator(); !it.at_end(); it.next()) {
                m_sub_todo.insert(it.curr());
            }
            clause_use_list& cs = m_use_list.get(l);
            for (auto it = cs.mk_iterator(); !it.at_end(); ) {
                clause & c = it.curr();
                it.next();
                remove_clause(c, l);
            }
            cs.reset();            
        }
    }

    void simplifier::elim_lit(clause & c, literal l) {
        TRACE("elim_lit", tout << "processing: " << l << " @ " << c << "\n";);
        m_need_cleanup = true;
        m_num_elim_lits++;
        insert_elim_todo(l.var());
        c.elim(l);
        if (s.m_config.m_drat) s.m_drat.add(c, true); 
        // if (s.m_config.m_drat) s.m_drat.del(c0); // can delete previous version 
        clause_use_list & occurs = m_use_list.get(l);
        occurs.erase_not_removed(c);
        m_sub_counter -= occurs.size()/2;
        if (cleanup_clause(c, true /* clause is in the use lists */)) {
            // clause was satisfied
            TRACE("elim_lit", tout << "clause was satisfied\n";);
            remove_clause(c);
            return;
        }
        switch (c.size()) {
        case 0:
            TRACE("elim_lit", tout << "clause is empty\n";);
            s.set_conflict(justification());
            return;
        case 1:
            TRACE("elim_lit", tout << "clause became unit: " << c[0] << "\n";);
            propagate_unit(c[0]);
            // propagate_unit will delete c.
            // remove_clause(c);
            return;
        case 2:
            TRACE("elim_lit", tout << "clause became binary: " << c[0] << " " << c[1] << "\n";);
            s.mk_bin_clause(c[0], c[1], c.is_learned());
            m_sub_bin_todo.push_back(bin_clause(c[0], c[1], c.is_learned()));
            remove_clause(c);
            return;
        default:
            TRACE("elim_lit", tout << "result: " << c << "\n";);
            m_sub_todo.insert(c);
            return;
        }
    }

    bool simplifier::subsume_with_binaries() {
        unsigned init = s.m_rand(); // start in a random place, since subsumption can be aborted
        unsigned num_lits = s.m_watches.size();
        for (unsigned i = 0; i < num_lits; i++) {
            unsigned l_idx = (i + init) % num_lits;
            watch_list & wlist = get_wlist(to_literal(l_idx));
            literal l = ~to_literal(l_idx);
            // should not traverse wlist using iterators, since back_subsumption1 may add new binary clauses there
            for (unsigned j = 0; j < wlist.size(); j++) {
                watched w  = wlist[j];
                if (w.is_binary_non_learned_clause()) {
                    literal l2 = w.get_literal();
                    if (l.index() < l2.index()) {
                        m_dummy.set(l, l2, w.is_learned());
                        clause & c = *(m_dummy.get());
                        back_subsumption1(c);
                        if (w.is_learned() && !c.is_learned()) {
                            SASSERT(wlist[j] == w);
                            TRACE("set_not_learned_bug",
                                  tout << "marking as not learned: " << l2 << " " << wlist[j].is_learned() << "\n";);
                            wlist[j].set_learned(false);
                            mark_as_not_learned_core(get_wlist(~l2), l);
                        }
                        if (s.inconsistent())
                            return false;
                    }
                }
            }
            if (m_sub_counter < 0)
                break;
        }
        return true;
    }

    void simplifier::mark_as_not_learned_core(watch_list & wlist, literal l2) {
        for (watched & w : wlist) {
            if (w.is_binary_clause() && w.get_literal() == l2 && w.is_learned()) {
                w.set_learned(false);
                return;
            }
        }
    }

    void simplifier::mark_as_not_learned(literal l1, literal l2) {
        mark_as_not_learned_core(get_wlist(~l1), l2);
        mark_as_not_learned_core(get_wlist(~l2), l1);
    }

    struct bin_lt {
        bool operator()(watched const & w1, watched const & w2) const {
            if (!w1.is_binary_clause()) return false;
            if (!w2.is_binary_clause()) return true;
            unsigned l1_idx = w1.get_literal().index();
            unsigned l2_idx = w2.get_literal().index();
            if (l1_idx < l2_idx) return true;
            if (l1_idx == l2_idx && !w1.is_learned() && w2.is_learned()) return true;
            return false;
        }
    };

    /**
       \brief Eliminate duplicated binary clauses.
    */
    void simplifier::elim_dup_bins() {
#ifdef _TRACE
        unsigned l_idx = 0;
#endif
        unsigned elim = 0;
        for (watch_list & wlist : s.m_watches) {
            checkpoint();
            std::stable_sort(wlist.begin(), wlist.end(), bin_lt());
            literal last_lit   = null_literal;
            watch_list::iterator it    = wlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end   = wlist.end();
            for (; it != end; ++it) {
                if (!it->is_binary_clause()) {
                    *itprev = *it;
                    itprev++;
                    continue;
                }
                if (it->get_literal() == last_lit) {
                    TRACE("subsumption", tout << "eliminating: " << ~to_literal(l_idx)
                          << " " << it->get_literal() << "\n";);
                    elim++;
                }
                else {
                    last_lit = it->get_literal();
                    *itprev = *it;
                    itprev++;
                }
            }
            wlist.set_end(itprev);
            TRACE_CODE(l_idx++;);
        }
        m_num_subsumed += elim/2; // each binary clause is "eliminated" twice.
    }

    struct simplifier::subsumption_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_subsumed;
        unsigned     m_num_sub_res;
        subsumption_report(simplifier & s):
            m_simplifier(s),
            m_num_subsumed(s.m_num_subsumed),
            m_num_sub_res(s.m_num_sub_res) {
            m_watch.start();
        }

        ~subsumption_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-subsumer :subsumed "
                       << (m_simplifier.m_num_subsumed - m_num_subsumed)
                       << " :subsumption-resolution " << (m_simplifier.m_num_sub_res - m_num_sub_res)
                       << " :threshold " << m_simplifier.m_sub_counter
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    void simplifier::subsume() {
        subsumption_report rpt(*this);
        elim_dup_bins();
        subsume_with_binaries();
        TRACE("subsumption_bug", s.display(tout););
        while (true) {
            TRACE("subsumption", tout << "sub_todo size: " << m_sub_todo.size() << "\n";);

            m_sub_counter -= m_sub_bin_todo.size();
            while (!m_sub_bin_todo.empty()) {
                checkpoint();
                m_dummy.set(m_sub_bin_todo.back());
                m_sub_bin_todo.pop_back();
                clause & c = *(m_dummy.get());
                bool was_learned = c.is_learned();
                back_subsumption1(c);
                if (was_learned && !c.is_learned()) {
                    mark_as_not_learned(c[0], c[1]);
                }
            }

            checkpoint();

            TRACE("subsumption_bug", s.display(tout););

            if (m_sub_todo.empty()) {
                m_last_sub_trail_sz = s.m_trail.size();
                break;
            }

            if (m_sub_counter < 0)
                break;

            clause & c = m_sub_todo.erase();

            c.unmark_strengthened();
            m_sub_counter--;
            TRACE("subsumption", tout << "next: " << c << "\n";);
            if (s.m_trail.size() > m_last_sub_trail_sz) {
                if (cleanup_clause(c, true /* clause is in the use_lists */)) {
                    remove_clause(c);
                    continue;
                }
                unsigned sz = c.size();
                if (sz == 0) {
                    s.set_conflict(justification());
                    return;
                }
                if (sz == 1) {
                    propagate_unit(c[0]);
                    // propagate_unit will delete c.
                    // remove_clause(c);
                    continue;
                }
                if (sz == 2) {
                    TRACE("subsumption", tout << "clause became binary: " << c << "\n";);
                    s.mk_bin_clause(c[0], c[1], c.is_learned());
                    m_sub_bin_todo.push_back(bin_clause(c[0], c[1], c.is_learned()));
                    remove_clause(c);
                    continue;
                }
            }
            TRACE("subsumption", tout << "using: " << c << "\n";);
            back_subsumption1(c);
        }
    }

    struct simplifier::blocked_clause_elim {
        class literal_lt {
            use_list const &   m_use_list;
            vector<watch_list> const & m_watches;
        public:
            literal_lt(use_list const & l, vector<watch_list> const & ws):m_use_list(l), m_watches(ws) {}

            unsigned weight(unsigned l_idx) const {
                return 2*m_use_list.get(~to_literal(l_idx)).size() + m_watches[l_idx].size();
            }

            bool operator()(unsigned l_idx1, unsigned l_idx2) const {
                return weight(l_idx1) < weight(l_idx2);
            }
        };

        class clause_ante {
            bool    m_from_ri;
            literal m_lit1;
            literal m_lit2;
            clause* m_clause;
        public:
            clause_ante():
                m_from_ri(false), m_lit1(null_literal), m_lit2(null_literal), m_clause(nullptr) {}
            clause_ante(literal l1, bool from_ri):
                m_from_ri(from_ri), m_lit1(l1), m_lit2(null_literal), m_clause(nullptr) {}
            clause_ante(literal l1, literal l2):
                m_from_ri(false), m_lit1(l1), m_lit2(l2), m_clause(nullptr) {}
            clause_ante(clause& c):
                m_from_ri(false), m_lit1(null_literal), m_lit2(null_literal), m_clause(&c) {}            
            literal lit1() const { return m_lit1; }
            literal lit2() const { return m_lit2; }
            clause* cls() const { return m_clause; }
            bool from_ri() const { return m_from_ri; }
            bool operator==(clause_ante const& a) const {
                return a.m_lit1 == m_lit1 && a.m_lit2 == m_lit2 && a.m_clause == m_clause;
            }
            std::ostream& display(std::ostream& out, literal lit) const {
                if (cls()) {
                    out << *cls() << " ";
                }
                else {
                    out << "(" << ~lit;
                }
                if (lit1() != null_literal) {
                    out << " " << lit1();
                }
                if (lit2() != null_literal) {
                    out << " " << lit2();
                }
                if (!cls()) out << ")";
                if (from_ri()) out << "ri";
                out << "\n";
                return out;
            }
        };

        class queue {
            heap<literal_lt> m_queue;
        public:
            queue(use_list const & l, vector<watch_list> const & ws):m_queue(128, literal_lt(l, ws)) {}
            void insert(literal l) {
                unsigned idx = l.index();
                m_queue.reserve(idx + 1);
                SASSERT(!m_queue.contains(idx));
                m_queue.insert(idx);
            }
            void decreased(literal l) {
                unsigned idx = l.index();
                if (m_queue.contains(idx))
                    m_queue.decreased(idx);
                else 
                    m_queue.insert(idx);
            }
            literal next() { SASSERT(!empty()); return to_literal(m_queue.erase_min()); }
            bool empty() const { return m_queue.empty(); }
            void reset() { m_queue.reset(); }
        };

        simplifier &      s;
        int               m_counter;
        model_converter & m_mc;
        queue             m_queue;

        literal_vector m_covered_clause;              // covered clause
        svector<clause_ante> m_covered_antecedent;    // explainations for literals in covered clause
        literal_vector m_intersection;                // current resolution intersection
        literal_vector m_tautology;                   // literals that are used in blocking tautology
        literal_vector m_new_intersection;
        svector<bool>  m_in_intersection;
        unsigned       m_ala_qhead;
        clause_wrapper m_clause;

        blocked_clause_elim(simplifier & _s, unsigned limit, model_converter & _mc, use_list & l,
                            vector<watch_list> & wlist):
            s(_s),
            m_counter(limit),
            m_mc(_mc),
            m_queue(l, wlist),
            m_clause(null_literal, null_literal) {
            m_in_intersection.resize(s.s.num_vars() * 2, false);
        }

        void insert(literal l) {
            VERIFY(process_var(l.var()));
            m_queue.insert(l);
        }

        bool process_var(bool_var v) {
            return !s.s.is_assumption(v) && !s.was_eliminated(v) && !s.is_external(v) && s.value(v) == l_undef;
        }

        enum elim_type {
            bce_t,
            cce_t,
            acce_t,
            abce_t,
            ate_t,
            no_t
        };

        void operator()() {
            if (s.acce_enabled()) {
                cce<acce_t>();
            }
            if (s.ate_enabled() && !s.abce_enabled() && !s.acce_enabled()) {
                cce<ate_t>();
            }
            if (s.cce_enabled() && !s.acce_enabled()) {
                cce<cce_t>();
            }
            if (s.abce_enabled() && !s.acce_enabled()) {
                cce<abce_t>();
            }
            if (s.bce_enabled() && !s.cce_enabled() && !s.abce_enabled()) {
                cce<bce_t>();
            }
            if (s.bca_enabled()) {
                bca();
            }
        }

        void insert_queue() {
            unsigned num_vars = s.s.num_vars();
            for (bool_var v = 0; v < num_vars; v++) {
                if (process_var(v)) {
                    insert(literal(v, false));
                    insert(literal(v, true));
                }
            }
        }

        void reset_intersection() {
            for (literal l : m_intersection) m_in_intersection[l.index()] = false;
            m_intersection.reset();
        }

        void add_intersection(literal lit) {
            m_intersection.push_back(lit);
            m_in_intersection[lit.index()] = true;
        }        
        
        //
        // Resolve intersection
        // Find literals that are in the intersection of all resolvents with l.
        //
        bool resolution_intersection(literal l, bool adding) {
            unsigned tsz = m_tautology.size();
            reset_intersection();
            if (!process_var(l.var())) return false;
            bool first = true;
            VERIFY(s.value(l) == l_undef);
            for (watched & w : s.get_wlist(l)) {
                // when adding a blocked clause, then all non-learned clauses have to be considered for the
                // resolution intersection.
                bool process_bin = adding ? w.is_binary_clause() : w.is_binary_non_learned_clause();
                if (process_bin) {
                    literal lit = w.get_literal();
                    if (s.is_marked(~lit) && lit != ~l) {
                        m_tautology.push_back(~lit);
                        continue; // tautology
                    }
                    if (!first || s.is_marked(lit)) {
                        reset_intersection();
                        m_tautology.shrink(tsz);
                        return false; // intersection is empty or does not add anything new.
                    }
                    first = false;
                    SASSERT(m_intersection.empty());
                    add_intersection(lit);
                }
            }
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                bool tautology = false;
                clause & c = it.curr();
                if (c.is_learned() && !adding) continue;
                if (c.was_removed()) continue;
                for (literal lit : c) {
                    if (s.is_marked(~lit) && lit != ~l) {
                        m_tautology.push_back(~lit);
                        tautology = true;
                        break;
                    }
                }
                if (!tautology) {
                    if (first) {
                        for (literal lit : c) 
                            if (lit != ~l && !s.is_marked(lit)) 
                                add_intersection(lit);
                        first = false;
                    }
                    else {
                        m_new_intersection.reset();
                        for (literal lit : c) 
                            if (m_in_intersection[lit.index()]) 
                                m_new_intersection.push_back(lit);
                        reset_intersection();
                        for (literal lit : m_new_intersection) 
                            add_intersection(lit);
                    }
                    if (m_intersection.empty()) {
                        m_tautology.shrink(tsz);
                        return false;
                    }
                }
            }
            // remove tautology literals if literal has no resolution intersection
            if (m_intersection.empty() && !first) {
                m_tautology.shrink(tsz);
            }
            // if (first) IF_VERBOSE(0, verbose_stream() << "taut: " << m_tautology << "\n";);
            return first;
        }

        bool check_abce_tautology(literal l) {
            unsigned tsz = m_tautology.size();
            if (!process_var(l.var())) return false;
            for (watched & w : s.get_wlist(l)) {
                if (w.is_binary_non_learned_clause()) {
                    literal lit = w.get_literal();
                    VERIFY(lit != ~l);
                    if (!s.is_marked(~lit)) {
                        m_tautology.shrink(tsz);
                        return false;
                    }
                    m_tautology.push_back(~lit);
                }
            }
            clause_use_list & neg_occs = s.m_use_list.get(~l);
            for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned() || c.was_removed()) continue;
                bool tautology = false;
                for (literal lit : c) {
                    if (s.is_marked(~lit) && lit != ~l) {
                        tautology = true;
                        m_tautology.push_back(~lit);
                        break;
                    }
                }
                if (!tautology) {
                    m_tautology.shrink(tsz);
                    return false;
                }
            }
            return true;
        }

        bool revisit_binary(literal l1, literal l2) const {
            return m_clause.is_binary() && 
                ((m_clause[0] == l1 && m_clause[1] == l2) ||
                 (m_clause[0] == l2 && m_clause[1] == l1));
        }

        bool revisit_clause(clause const& c) const {
            return !m_clause.is_binary() && (m_clause.get_clause() == &c);
        }

        /**
           \brief idx is the index of the blocked literal.
           m_tautology contains literals that were used to establish that the current members of m_covered_clause is blocked.
           This routine removes literals that were not relevant to establishing it was blocked.

           It has a bug: literals that are used to prune tautologies during resolution intersection should be included
           in the dependencies. They may get used in some RI prunings and then they have to be included to avoid flipping
           RI literals.
         */
        void minimize_covered_clause(unsigned idx) {
            // IF_VERBOSE(0, verbose_stream() << "minimize: " << m_covered_clause 
            // << " @ " << idx << "\n" << "tautology: " << m_tautology << "\n";);
            literal _blocked = m_covered_clause[idx];
            for (literal l : m_tautology) VERIFY(s.is_marked(l));
            for (literal l : m_covered_clause) s.unmark_visited(l);
            for (literal l : m_tautology) s.mark_visited(l);
            s.mark_visited(m_covered_clause[idx]);
            for (unsigned i = 0; i < m_covered_clause.size(); ++i) {
                literal lit = m_covered_clause[i];
                if (m_covered_antecedent[i] == clause_ante()) s.mark_visited(lit);
                if (s.is_marked(lit)) idx = i; 
            }
            if (false && _blocked.var() == 8074) {
                IF_VERBOSE(0, verbose_stream() << "covered: " << m_covered_clause << "\n";
                           verbose_stream() << "tautology: " << m_tautology << "\n";
                           verbose_stream() << "index: " << idx << "\n";
                           for (unsigned i = idx; i > 0; --i) {
                               m_covered_antecedent[i].display(verbose_stream(), m_covered_clause[i]);
                           });
            }
            for (unsigned i = idx; i > 0; --i) {
                literal lit = m_covered_clause[i];
                //s.mark_visited(lit);
                //continue;
                if (!s.is_marked(lit)) continue;
                clause_ante const& ante = m_covered_antecedent[i];
                if (ante.cls()) {
                    for (literal l : *ante.cls()) {
                        if (l != ~lit) s.mark_visited(l);
                    }
                }
                if (ante.lit1() != null_literal) {
                    s.mark_visited(ante.lit1());
                }
                if (ante.lit2() != null_literal) {
                    s.mark_visited(ante.lit2());
                }
            }
            unsigned j = 0;
            literal blocked = null_literal;
            for (unsigned i = 0; i <= idx; ++i) {
                literal lit = m_covered_clause[i];
                if (s.is_marked(lit)) {
                    // 
                    // Record that the resolving literal for 
                    // resolution intersection can be flipped.
                    // 
                    clause_ante const& ante = m_covered_antecedent[i];
                    if (ante.from_ri() && blocked != ante.lit1()) {
                        blocked = ante.lit1();
                        VERIFY(s.value(blocked) == l_undef);
                        m_mc.stackv().push_back(std::make_pair(j, blocked));
                    }
                    m_covered_clause[j++] = lit;
                    s.unmark_visited(lit);
                }
            }
            for (literal l : m_covered_clause) VERIFY(!s.is_marked(l)); 
            for (bool_var v = 0; v < s.s.num_vars(); ++v) VERIFY(!s.is_marked(literal(v, true)) && !s.is_marked(literal(v, false)));

            // unsigned sz0 = m_covered_clause.size();
            m_covered_clause.resize(j);
            VERIFY(j >= m_clause.size());
            if (false && _blocked.var() == 16774) {
                IF_VERBOSE(0, verbose_stream() << "covered: " << m_covered_clause << "\n");
            }
            // IF_VERBOSE(0, verbose_stream() << "reduced from size " << sz0 << " to " << m_covered_clause << "\n" << m_clause << "\n";);
        }

        /*
         * C \/ l     l \/ lit
         * -------------------
         *    C \/ l \/ ~lit
         *
         * C \/ lit \/ l   l \/ lit
         * ------------------------
         *        l \/ lit              C \/ lit \/ l can be removed
         *
         * C \/ l1 \/ ... \/ lk     l1 \/ ... \/ lk \/ lit
         * -----------------------------------------------
         *      C \/ l1 \/ ... \/ lk \/ ~lit
         * unless C contains lit, and it is a tautology.
         */
        bool add_ala() {
            for (; m_ala_qhead < m_covered_clause.size(); ++m_ala_qhead) {
                literal l = m_covered_clause[m_ala_qhead];                
                for (watched & w : s.get_wlist(~l)) {
                    if (w.is_binary_non_learned_clause()) {
                        literal lit = w.get_literal();
                        if (revisit_binary(l, lit)) continue;
                        if (s.is_marked(lit)) {
                            return true;
                        }
                        if (!s.is_marked(~lit)) {
                            // if (m_covered_clause[0].var() == 10219) IF_VERBOSE(0, verbose_stream() << "ala: " << l << " " << lit << "\n");
                            m_covered_clause.push_back(~lit);
                            m_covered_antecedent.push_back(clause_ante(l, false));
                            s.mark_visited(~lit);
                        }
                    }
                }
                clause_use_list & pos_occs = s.m_use_list.get(l);
                clause_use_list::iterator it = pos_occs.mk_iterator();
                for (; !it.at_end(); it.next()) {
                    clause & c = it.curr();
                    if (c.is_learned() || c.was_removed()) continue;
                    if (revisit_clause(c)) continue;
                    literal lit1 = null_literal;
                    bool ok = true;
                    for (literal lit : c) {
                        if (lit == l) continue;
                        if (s.is_marked(lit)) continue;
                        if (!s.is_marked(~lit) && lit1 == null_literal) {
                            lit1 = lit;
                        }
                        else {
                            ok = false;
                            break;
                        }
                    }
                    if (!ok) continue;
                    if (lit1 == null_literal) {
                        return true;
                    }
                    // if (m_covered_clause[0].var() == 10219) IF_VERBOSE(0, verbose_stream() << "ala: " << c << " " << lit1 << "\n");
                    m_covered_clause.push_back(~lit1);
                    m_covered_antecedent.push_back(clause_ante(c));
                    s.mark_visited(~lit1);
                }
            }
            return false;
        }


        /*
         *  C \/ l    ~l \/ lit \/ D_i   for i = 1...N all the clauses that have ~l
         *  -------------------------
         *      C \/ l \/ lit
         *
         *
         */
        bool add_cla(literal& blocked) {
            for (unsigned i = 0; i < m_covered_clause.size(); ++i) {
                literal lit = m_covered_clause[i];
                if (resolution_intersection(lit, false)) {
                    blocked = m_covered_clause[i];                    
                    minimize_covered_clause(i);
                    return true;
                }
                for (literal l : m_intersection) {
                    if (!s.is_marked(l)) {
                        s.mark_visited(l);
                        m_covered_clause.push_back(l);
                        m_covered_antecedent.push_back(clause_ante(lit, true));
                    }
                }
            }
            return false;
        }

        bool above_threshold(unsigned sz0) const {
            // if (sz0 * 400 < m_covered_clause.size()) IF_VERBOSE(0, verbose_stream() << "above threshold " << sz0 << " " << m_covered_clause.size() << "\n";);
            return sz0 * 400 < m_covered_clause.size();
        }

        void reset_mark() {
            for (literal l : m_covered_clause) s.unmark_visited(l);
        }

        template<elim_type et>
        elim_type cce(literal& blocked, model_converter::kind& k) {
            bool first = true;
            unsigned sz = 0, sz0 = m_covered_clause.size();     
            for (literal l : m_covered_clause) s.mark_visited(l);
            shuffle<literal>(m_covered_clause.size(), m_covered_clause.c_ptr(), s.s.m_rand);
            m_tautology.reset();
            m_mc.stackv().reset();
            m_ala_qhead = 0;

            switch (et) {
            case cce_t:
                k = model_converter::CCE;
                break;
            case acce_t:
                k = model_converter::ACCE;
                break;
            default:
                k = model_converter::BCE;
                break;
            }

            /*
             * For blocked clause elimination with asymmetric literal addition (ABCE) 
             * it suffices to check if one of the original
             * literals in the clause is blocked modulo the additional literals added to the clause.
             * So we record sz0, the original set of literals in the clause, mark additional literals, 
             * and then check if any of the first sz0 literals are blocked.
             */

            if (et == ate_t) {
                bool ala = add_ala();
                reset_mark();
                m_covered_clause.shrink(sz0);
                return ala ? ate_t : no_t;
            }

            while (m_covered_clause.size() > sz && !above_threshold(sz0)) {

                if ((et == abce_t || et == acce_t) && add_ala()) {
                    reset_mark();
                    if (first) {
                        m_covered_clause.shrink(sz0);
                    }
                    else {
                        /*
                         * tautology depends on resolution intersection. 
                         * literals used for resolution intersection may have to be flipped.
                         */
                        for (literal l : m_covered_clause) {
                            m_tautology.push_back(l);
                            s.mark_visited(l);
                        }
                        minimize_covered_clause(m_covered_clause.size()-1);
                    }
                    return ate_t;                               
                }

                if (first) {
                    for (unsigned i = 0; i < sz0; ++i) {
                        if (check_abce_tautology(m_covered_clause[i])) {
                            blocked = m_covered_clause[i];
                            reset_mark();
#if 0
                            if (sz0 == 3 && blocked.var() == 10219) {
                                IF_VERBOSE(0, verbose_stream() << "abce: " << m_covered_clause << "\n";
                                           for (literal l : m_covered_clause) verbose_stream() << s.value(l) << "\n";
                                           );
                                literal l = blocked;
                                clause_use_list & neg_occs = s.m_use_list.get(~l);
                                for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
                                    clause & c = it.curr();
                                    IF_VERBOSE(0, verbose_stream() << c << "\n");
                                }
                            }
#endif
                            m_covered_clause.shrink(sz0);
                            if (et == bce_t) return bce_t;
                            k = model_converter::ABCE;
                            return abce_t;
                        }
                    }
                }
                first = false;
                
                if (et == abce_t || et == bce_t) {
                    break;
                }
                
                /*
                 * Add resolution intersection while checking if the clause becomes a tautology.
                 */
                sz = m_covered_clause.size();
                if ((et == cce_t || et == acce_t) && add_cla(blocked)) {
                    reset_mark();
                    return et;
                }
            }
            reset_mark();
            return no_t;
        }

        // perform covered clause elimination.
        // first extract the covered literal addition (CLA).
        // then check whether the CLA is blocked.
        template<elim_type et>
        elim_type cce(clause& c, literal& blocked, model_converter::kind& k) {
            m_clause = clause_wrapper(c);
            m_covered_clause.reset();
            m_covered_antecedent.reset();
            for (literal l : c) { 
                m_covered_clause.push_back(l);
                m_covered_antecedent.push_back(clause_ante());
            }
            return cce<et>(blocked, k);
        }

        template<elim_type et>
        elim_type cce(literal l1, literal l2, literal& blocked, model_converter::kind& k) {
            m_clause = clause_wrapper(l1, l2);
            m_covered_clause.reset();
            m_covered_antecedent.reset();
            m_covered_clause.push_back(l1);
            m_covered_clause.push_back(l2);
            m_covered_antecedent.push_back(clause_ante());
            m_covered_antecedent.push_back(clause_ante());
            return cce<et>(blocked, k);            
        }
        
        template<elim_type et>
        void cce() {
            insert_queue();
            cce_clauses<et>();
            cce_binary<et>();
        }

        template<elim_type et>
        void cce_binary() {
            while (!m_queue.empty() && m_counter >= 0) {
                s.checkpoint();
                process_cce_binary<et>(m_queue.next());
            }
        }

        template<elim_type et>
        void process_cce_binary(literal l) {
            literal blocked = null_literal;
            watch_list & wlist = s.get_wlist(~l);
            m_counter -= wlist.size();
            model_converter::kind k;
            for (watched & w : wlist) {
                if (!w.is_binary_non_learned_clause()) continue;
                if (!select_clause<et>(2)) continue;
                literal l2 = w.get_literal();
                elim_type r = cce<et>(l, l2, blocked, k); 
                inc_bc(r);
                switch (r) {
                case ate_t:
                    w.set_learned(true);
                    s.s.set_learned1(l2, l, true);
                    m_mc.add_ate(m_covered_clause);
                    break;
                case no_t:
                    break;
                default:
                    w.set_learned(true);
                    s.s.set_learned1(l2, l, true);
                    block_covered_binary(w, l, blocked, k);
                    break;
                }
            }
        }

        template<elim_type et>
        void cce_clauses() {
            literal blocked;
            model_converter::kind k;
            for (clause* cp : s.s.m_clauses) {
                clause& c = *cp;
                if (c.was_removed() || c.is_learned()) continue;
                if (!select_clause<et>(c.size())) continue;
                elim_type r = cce<et>(c, blocked, k);
                inc_bc(r);
                switch (r) {
                case ate_t:
                    m_mc.add_ate(m_covered_clause);
                    s.set_learned(c);                    
                    break;
                case no_t:
                    break;
                default:
                    block_covered_clause(c, blocked, k);
                    s.set_learned(c);
                    break;
                }
            }
        }

        void inc_bc(elim_type et) {
            switch (et) {
            case cce_t: s.m_num_cce++; break;
            case acce_t: s.m_num_acce++; break;
            case abce_t: s.m_num_abce++; break;
            case ate_t: s.m_num_ate++; break;
            case bce_t: s.m_num_bce++; break;
            default: break;
            }
        }

        // select 25% of clauses size 2, 3
        // always try to remove larger clauses.
        template<elim_type et>
        bool select_clause(unsigned sz) {
            return (sz > 3) || s.s.m_rand(4) == 0;
        }

        void block_covered_clause(clause& c, literal l, model_converter::kind k) {
            if (false) {
                IF_VERBOSE(0, verbose_stream() << "blocked: " << l << " @ " << c << " :covered " << m_covered_clause << "\n";
                           s.m_use_list.display(verbose_stream() << "use  " << l << ":", l);
                           s.m_use_list.display(verbose_stream() << "use  " << ~l << ":", ~l);
                           s.s.display_watch_list(verbose_stream() <<  ~l << ": ", s.get_wlist(l)) << "\n";
                           s.s.display_watch_list(verbose_stream() <<   l << ": ", s.get_wlist(~l)) << "\n";
                           );
                
            }
            TRACE("blocked_clause", tout << "new blocked clause: " << c << "\n";);
            SASSERT(!s.is_external(l));
            model_converter::entry& new_entry = m_mc.mk(k, l.var());
            for (literal lit : c) {
                if (lit != l && process_var(lit.var())) {
                    m_queue.decreased(~lit);
                }
            }
            m_mc.insert(new_entry, m_covered_clause);
        }
        
        void block_covered_binary(watched const& w, literal l1, literal blocked, model_converter::kind k) {
            SASSERT(!s.is_external(blocked));
            model_converter::entry& new_entry = m_mc.mk(k, blocked.var());
            literal l2 = w.get_literal();
            TRACE("blocked_clause", tout << "new blocked clause: " << l2 << " " << l1 << "\n";);
            s.set_learned(l1, l2);
            m_mc.insert(new_entry, m_covered_clause);
            m_queue.decreased(~l2);
        }

        void bca() {
            m_queue.reset();
            insert_queue();
            while (!m_queue.empty() && m_counter >= 0) {
                s.checkpoint();
                bca(m_queue.next());
            }
        }

        /*
          \brief blocked binary clause addition for literal l
          Let RI be the resolution intersection with l, e.g, RI are the literals
          that are in all clauses of the form ~l \/ C.
          If RI is non-empty, then let l' be a literal in RI.
          Then the following binary clause is blocked: l \/ ~l'
         */
        void bca(literal l) {
            m_tautology.reset();
            if (resolution_intersection(l, true)) {
                // this literal is pure. 
                return;
            }
            for (literal l2 : m_intersection) {
                watched* w = find_binary_watch(s.get_wlist(~l), ~l2);
                if (!w) {
                    s.s.mk_bin_clause(l, ~l2, true);
                    ++s.m_num_bca;
                }
            }
        }

        bool all_tautology(literal l) {
            watch_list & wlist = s.get_wlist(l);
            m_counter -= wlist.size();
            for (auto const& w : wlist) {
                if (w.is_binary_non_learned_clause() && 
                    !s.is_marked(~w.get_literal()))
                    return false;
            }

            clause_use_list & neg_occs = s.m_use_list.get(~l);
            clause_use_list::iterator it = neg_occs.mk_iterator();
            for (; !it.at_end(); it.next()) {
                clause & c = it.curr();
                if (c.is_learned()) continue;
                if (c.was_removed()) continue;
                m_counter -= c.size();
                unsigned sz = c.size();
                unsigned i;
                for (i = 0; i < sz; i++) {
                    if (s.is_marked(~c[i]))
                        break;
                }
                if (i == sz)
                    return false;
            }

            if (s.s.m_ext) {
                ext_constraint_list const& ext_list = s.m_ext_use_list.get(~l);
                for (ext_constraint_idx idx : ext_list) {
                    if (!s.s.m_ext->is_blocked(l, idx)) {
                        return false;
                    }
                }
            }
            return true;
        }
    };

    struct simplifier::blocked_cls_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_bce;
        unsigned     m_num_cce;
        unsigned     m_num_acce;
        unsigned     m_num_abce;
        unsigned     m_num_ate;
        unsigned     m_num_bca;
        blocked_cls_report(simplifier & s):
            m_simplifier(s),
            m_num_bce(s.m_num_bce),
            m_num_cce(s.m_num_cce),
            m_num_acce(s.m_num_acce),
            m_num_abce(s.m_num_abce),
            m_num_ate(s.m_num_ate),
            m_num_bca(s.m_num_bca) {
            m_watch.start();
        }

        ~blocked_cls_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-blocked-clauses";
                       report(m_simplifier.m_num_ate,  m_num_ate,  " :ate ");
                       report(m_simplifier.m_num_bce,  m_num_bce,  " :bce ");
                       report(m_simplifier.m_num_abce, m_num_abce, " :abce ");
                       report(m_simplifier.m_num_cce,  m_num_cce,  " :cce ");
                       report(m_simplifier.m_num_bca,  m_num_bca,  " :bca ");
                       report(m_simplifier.m_num_acce, m_num_acce, " :acce ");
                       verbose_stream() << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }

        void report(unsigned n, unsigned m, char const* s) {
            if (n > m) verbose_stream() << s << (n - m);
        }
    };

    void simplifier::elim_blocked_clauses() {
        TRACE("blocked_clause_bug", tout << "trail: " << s.m_trail.size() << "\n"; s.display_watches(tout); s.display(tout););
        blocked_cls_report rpt(*this);
        blocked_clause_elim elim(*this, m_blocked_clause_limit, s.m_mc, m_use_list, s.m_watches);
        elim();
    }

    unsigned simplifier::num_nonlearned_bin(literal l) const {
        unsigned r = 0;
        watch_list const & wlist = get_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_non_learned_clause())
                r++;
        }
        return r;
    }

    unsigned simplifier::get_to_elim_cost(bool_var v) const {
        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned num_pos = m_use_list.get(pos_l).size();
        unsigned num_neg = m_use_list.get(neg_l).size();
        unsigned num_bin_pos = num_nonlearned_bin(pos_l);
        unsigned num_bin_neg = num_nonlearned_bin(neg_l);
        unsigned cost = 2 * num_pos * num_neg + num_pos * num_bin_neg + num_neg * num_bin_pos;
        CTRACE("elim_vars_detail", cost == 0, tout << v << " num_pos: " << num_pos << " num_neg: " << num_neg << " num_bin_pos: " << num_bin_pos
               << " num_bin_neg: " << num_bin_neg << " cost: " << cost << "\n";);
        return cost;
    }

    typedef std::pair<bool_var, unsigned> bool_var_and_cost;

    struct bool_var_and_cost_lt {
        bool operator()(bool_var_and_cost const & p1, bool_var_and_cost const & p2) const { return p1.second < p2.second; }
    };

    void simplifier::order_vars_for_elim(bool_var_vector & r) {
        svector<bool_var_and_cost> tmp;
        for (bool_var v : m_elim_todo) {
            if (is_external(v))
                continue;
            if (was_eliminated(v))
                continue;
            if (value(v) != l_undef)
                continue;
            unsigned c = get_to_elim_cost(v);
            tmp.push_back(bool_var_and_cost(v, c));
        }
        m_elim_todo.reset();
        std::stable_sort(tmp.begin(), tmp.end(), bool_var_and_cost_lt());
        TRACE("elim_vars",
              for (auto& p : tmp) tout << "(" << p.first << ", " << p.second << ") ";
              tout << "\n";);
        for (auto& p : tmp) 
            r.push_back(p.first);
    }

    /**
       \brief Collect clauses and binary clauses containing l.
    */
    void simplifier::collect_clauses(literal l, clause_wrapper_vector & r) {
        clause_use_list const & cs = m_use_list.get(l);
        for (auto it = cs.mk_iterator(); !it.at_end(); it.next()) {
            clause& c = it.curr();
            if (!c.is_learned() && !c.was_removed()) {
                r.push_back(clause_wrapper(c));
                SASSERT(r.back().size() == c.size());
            }
        }

        watch_list & wlist = get_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_non_learned_clause()) {
                r.push_back(clause_wrapper(l, w.get_literal()));
                SASSERT(r.back().size() == 2);
            }
        }
    }

    /**
       \brief Resolve clauses c1 and c2.
       c1 must contain l.
       c2 must contain ~l.
       Store result in r.
       Return false if the result is a tautology
    */
    bool simplifier::resolve(clause_wrapper const & c1, clause_wrapper const & c2, literal l, literal_vector & r) {
        CTRACE("resolve_bug", !c1.contains(l), tout << c1 << "\n" << c2 << "\nl: " << l << "\n";);
        SASSERT(c1.contains(l));
        SASSERT(c2.contains(~l));
        bool res = true;
        m_elim_counter -= c1.size() + c2.size();
        unsigned sz1 = c1.size();
        for (unsigned i = 0; i < sz1; ++i) {
            literal l1 = c1[i];
            if (l == l1)
                continue;
            m_visited[l1.index()] = true;
            r.push_back(l1);
        }

        literal not_l = ~l;
        unsigned sz2 = c2.size();
        for (unsigned i = 0; i < sz2; ++i) {
            literal l2 = c2[i];
            if (not_l == l2)
                continue;
            if (m_visited[(~l2).index()]) {
                res = false;
                break;
            }
            if (!m_visited[l2.index()])
                r.push_back(l2);
        }

        for (unsigned i = 0; i < sz1; ++i) {
            literal l1 = c1[i];
            m_visited[l1.index()] = false;
        }
        return res;
    }

    void simplifier::save_clauses(model_converter::entry & mc_entry, clause_wrapper_vector const & cs) {
        for (auto & e : cs) {
            s.m_mc.insert(mc_entry, e);
        }
    }

    void simplifier::add_non_learned_binary_clause(literal l1, literal l2) {
#if 0
        if ((l1.var() == 2039 || l2.var() == 2039) &&
            (l1.var() == 27042 || l2.var() == 27042)) { 
            IF_VERBOSE(1, verbose_stream() << "add_bin: " << l1 << " " << l2 << "\n");
        }
#endif
#if 0
        watched* w;
        watch_list & wlist1 = get_wlist(~l1);
        watch_list & wlist2 = get_wlist(~l2);
        w = find_binary_watch(wlist1, l2);
        if (w) {
            if (w->is_learned())
                w->set_learned(false);
        }
        else {
            wlist1.push_back(watched(l2, false));
        }

        w = find_binary_watch(wlist2, l1);
        if (w) {
            if (w->is_learned())
                w->set_learned(false);
        }
        else {
            wlist2.push_back(watched(l1, false));
        }
#else
        s.mk_bin_clause(l1, l2, false);
#endif
    }

    /**
       \brief Eliminate the binary clauses watched by l, when l.var() is being eliminated
    */
    void simplifier::remove_bin_clauses(literal l) {
        watch_list & wlist = get_wlist(~l);
        for (auto & w : wlist) {
            if (w.is_binary_clause()) {
                literal l2 = w.get_literal();
                watch_list & wlist2 = get_wlist(~l2);
                watch_list::iterator it2  = wlist2.begin();
                watch_list::iterator itprev = it2;
                watch_list::iterator end2 = wlist2.end();
                for (; it2 != end2; ++it2) {
                    if (it2->is_binary_clause() && it2->get_literal() == l) {
                        if ((l.var() == 2039 || l2.var() == 2039) &&
                            (l.var() == 27042 || l2.var() == 27042)) { 
                            IF_VERBOSE(1, verbose_stream() << "remove_bin: " << l << " " << l2 << "\n");
                        }

                        TRACE("bin_clause_bug", tout << "removing: " << l << " " << it2->get_literal() << "\n";);
                        m_sub_bin_todo.erase(bin_clause(l2, l, it2->is_learned()));
                        continue;
                    }
                    *itprev = *it2;
                    itprev++;
                }
                wlist2.set_end(itprev);
                m_sub_bin_todo.erase(bin_clause(l, l2, w.is_learned()));
            }
        }
        TRACE("bin_clause_bug", tout << "collapsing watch_list of: " << l << "\n";);
        wlist.finalize();
    }

    /**
       \brief Eliminate the clauses where the variable being eliminated occur.
    */
    void simplifier::remove_clauses(clause_use_list const & cs, literal l) {
        for (auto it = cs.mk_iterator(); !it.at_end(); ) {
            clause & c = it.curr();
            it.next();
            SASSERT(c.contains(l));
            c.set_removed(true);
            m_use_list.erase(c, l);
            m_sub_todo.erase(c);
            TRACE("resolution_bug", tout << "del_clause (elim_var): " << c << "\n";);
            m_need_cleanup = true;
        }
    }

    bool simplifier::try_eliminate(bool_var v) {
        TRACE("resolution_bug", tout << "processing: " << v << "\n";);
        if (value(v) != l_undef)
            return false;

        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned num_bin_pos = num_nonlearned_bin(pos_l);
        unsigned num_bin_neg = num_nonlearned_bin(neg_l);
        clause_use_list & pos_occs = m_use_list.get(pos_l);
        clause_use_list & neg_occs = m_use_list.get(neg_l);
        unsigned num_pos = pos_occs.num_irredundant() + num_bin_pos;
        unsigned num_neg = neg_occs.num_irredundant() + num_bin_neg;

        TRACE("resolution", tout << v << " num_pos: " << num_pos << " neg_pos: " << num_neg << "\n";);

        if (num_pos >= m_res_occ_cutoff && num_neg >= m_res_occ_cutoff)
            return false;

        unsigned before_lits = num_bin_pos*2 + num_bin_neg*2;

        for (auto it = pos_occs.mk_iterator(); !it.at_end(); it.next()) {
            if (!it.curr().is_learned())
                before_lits += it.curr().size();
        }

        for (auto it = neg_occs.mk_iterator(); !it.at_end(); it.next()) {
            if (!it.curr().is_learned())
                before_lits += it.curr().size();
        }

        TRACE("resolution", tout << v << " num_pos: " << num_pos << " neg_pos: " << num_neg << " before_lits: " << before_lits << "\n";);

        if (num_pos >= m_res_occ_cutoff3 && num_neg >= m_res_occ_cutoff3 && before_lits > m_res_lit_cutoff3 && s.m_clauses.size() > m_res_cls_cutoff2)
            return false;
        if (num_pos >= m_res_occ_cutoff2 && num_neg >= m_res_occ_cutoff2 && before_lits > m_res_lit_cutoff2 &&
            s.m_clauses.size() > m_res_cls_cutoff1 && s.m_clauses.size() <= m_res_cls_cutoff2)
            return false;
        if (num_pos >= m_res_occ_cutoff1 && num_neg >= m_res_occ_cutoff1 && before_lits > m_res_lit_cutoff1 &&
            s.m_clauses.size() <= m_res_cls_cutoff1)
            return false;

        m_pos_cls.reset();
        m_neg_cls.reset();
        collect_clauses(pos_l, m_pos_cls);
        collect_clauses(neg_l, m_neg_cls);

        TRACE("resolution_detail", tout << "collecting number of after_clauses\n";);
        unsigned before_clauses = num_pos + num_neg;
        unsigned after_clauses  = 0;
        for (clause_wrapper& c1 : m_pos_cls) {
            for (clause_wrapper& c2 : m_neg_cls) {
                m_new_cls.reset();
                if (resolve(c1, c2, pos_l, m_new_cls)) {
                    TRACE("resolution_detail", tout << c1 << "\n" << c2 << "\n-->\n";
                          for (literal l : m_new_cls) tout << l << " "; tout << "\n";);
                    after_clauses++;
                    if (after_clauses > before_clauses) {
                        TRACE("resolution", tout << "too many after clauses: " << after_clauses << "\n";);
                        return false;
                    }
                }
            }
        }
        TRACE("resolution", tout << "found var to eliminate, before: " << before_clauses << " after: " << after_clauses << "\n";);
        m_elim_counter -= num_pos * num_neg + before_lits;

        m_elim_counter -= num_pos * num_neg + before_lits;

        if (false) {
            literal l(v, false);
            IF_VERBOSE(0, 
                       verbose_stream() << "elim: " << l << "\n";
                       s.display_watch_list(verbose_stream() <<  ~l << ": ", get_wlist(l)) << "\n";
                       s.display_watch_list(verbose_stream() <<   l << ": ", get_wlist(~l)) << "\n";);
        }
        // eliminate variable
        ++s.m_stats.m_elim_var_res;
        VERIFY(!is_external(v));
        model_converter::entry & mc_entry = s.m_mc.mk(model_converter::ELIM_VAR, v);
        save_clauses(mc_entry, m_pos_cls);
        save_clauses(mc_entry, m_neg_cls);
        s.m_eliminated[v] = true;
        remove_bin_clauses(pos_l);
        remove_bin_clauses(neg_l);
        remove_clauses(pos_occs, pos_l);
        remove_clauses(neg_occs, neg_l);
        pos_occs.reset();
        neg_occs.reset();

        m_elim_counter -= num_pos * num_neg + before_lits;

        for (auto & c1 : m_pos_cls) {
            for (auto & c2 : m_neg_cls) {
                m_new_cls.reset();
                if (!resolve(c1, c2, pos_l, m_new_cls))
                    continue;
                if (false && v == 767) IF_VERBOSE(0, verbose_stream() << "elim: " << c1 << " +  " << c2 << " -> " << m_new_cls << "\n");
                TRACE("resolution_new_cls", tout << c1 << "\n" << c2 << "\n-->\n" << m_new_cls << "\n";);
                if (cleanup_clause(m_new_cls))
                    continue; // clause is already satisfied.
                switch (m_new_cls.size()) {
                case 0:
                    s.set_conflict(justification());
                    break;
                case 1:
                    propagate_unit(m_new_cls[0]);
                    break;
                case 2:
                    s.m_stats.m_mk_bin_clause++;
                    add_non_learned_binary_clause(m_new_cls[0], m_new_cls[1]);
                    back_subsumption1(m_new_cls[0], m_new_cls[1], false);
                    break;
                default:
                    if (m_new_cls.size() == 3)
                        s.m_stats.m_mk_ter_clause++;
                    else
                        s.m_stats.m_mk_clause++;
                    clause * new_c = s.alloc_clause(m_new_cls.size(), m_new_cls.c_ptr(), false);

                    if (s.m_config.m_drat) s.m_drat.add(*new_c, true);
                    s.m_clauses.push_back(new_c);

                    m_use_list.insert(*new_c);
                    if (m_sub_counter > 0)
                        back_subsumption1(*new_c);
                    else
                        back_subsumption0(*new_c);
                    break;
                }
                if (s.inconsistent())
                    return true;
            }
        }
        return true;
    }

    struct simplifier::elim_var_report {
        simplifier & m_simplifier;
        stopwatch    m_watch;
        unsigned     m_num_elim_vars;
        elim_var_report(simplifier & s):
            m_simplifier(s),
            m_num_elim_vars(s.m_num_elim_vars) {
            m_watch.start();
        }

        ~elim_var_report() {
            m_watch.stop();
            IF_VERBOSE(SAT_VB_LVL,
                       verbose_stream() << " (sat-resolution :elim-vars "
                       << (m_simplifier.m_num_elim_vars - m_num_elim_vars)
                       << " :threshold " << m_simplifier.m_elim_counter
                       << mem_stat()
                       << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() << ")\n";);
        }
    };

    void simplifier::elim_vars() {
        if (!elim_vars_enabled()) return;
        elim_var_report rpt(*this);
        bool_var_vector vars;
        order_vars_for_elim(vars);
        sat::elim_vars elim_bdd(*this);
        for (bool_var v : vars) {
            checkpoint();
            if (m_elim_counter < 0) 
                break;
            if (is_external(v)) {
                // skip
            }
            else if (try_eliminate(v)) {
                m_num_elim_vars++;
            }
            else if (elim_vars_bdd_enabled() && elim_bdd(v)) { 
                m_num_elim_vars++;
            }
        }

        m_pos_cls.finalize();
        m_neg_cls.finalize();
        m_new_cls.finalize();
    }

    void simplifier::updt_params(params_ref const & _p) {
        sat_simplifier_params p(_p);
        m_cce                     = p.cce();
        m_acce                    = p.acce();
        m_bca                     = false && p.bca(); // disabled
        m_abce                    = p.abce();
        m_ate                     = p.ate();
        m_bce_delay               = p.bce_delay();
        m_bce                     = p.bce();
        m_bce_at                  = p.bce_at();
        m_retain_blocked_clauses  = p.retain_blocked_clauses();
        m_blocked_clause_limit    = p.blocked_clause_limit();
        m_res_limit               = p.resolution_limit();
        m_res_occ_cutoff          = p.resolution_occ_cutoff();
        m_res_occ_cutoff1         = p.resolution_occ_cutoff_range1();
        m_res_occ_cutoff2         = p.resolution_occ_cutoff_range2();
        m_res_occ_cutoff3         = p.resolution_occ_cutoff_range3();
        m_res_lit_cutoff1         = p.resolution_lit_cutoff_range1();
        m_res_lit_cutoff2         = p.resolution_lit_cutoff_range2();
        m_res_lit_cutoff3         = p.resolution_lit_cutoff_range3();
        m_res_cls_cutoff1         = p.resolution_cls_cutoff1();
        m_res_cls_cutoff2         = p.resolution_cls_cutoff2();
        m_subsumption             = p.subsumption();
        m_subsumption_limit       = p.subsumption_limit();
        m_elim_vars               = p.elim_vars();
        m_elim_vars_bdd           = false && p.elim_vars_bdd(); // buggy?
        m_elim_vars_bdd_delay     = p.elim_vars_bdd_delay();
        m_incremental_mode        = s.get_config().m_incremental && !p.override_incremental();
    }

    void simplifier::collect_param_descrs(param_descrs & r) {
        sat_simplifier_params::collect_param_descrs(r);
    }

    void simplifier::collect_statistics(statistics & st) const {
        st.update("subsumed", m_num_subsumed);
        st.update("subsumption resolution", m_num_sub_res);
        st.update("elim literals", m_num_elim_lits);
        st.update("bce",  m_num_bce);
        st.update("cce",  m_num_cce);
        st.update("acce", m_num_acce);
        st.update("abce", m_num_abce);
        st.update("bca",  m_num_bca);
        st.update("ate",  m_num_ate);
    }

    void simplifier::reset_statistics() {
        m_num_bce = 0;
        m_num_cce = 0;
        m_num_acce = 0;
        m_num_abce = 0;
        m_num_subsumed = 0;
        m_num_sub_res = 0;
        m_num_elim_lits = 0;
        m_num_elim_vars = 0;
        m_num_bca = 0;
        m_num_ate = 0;
    }
};
