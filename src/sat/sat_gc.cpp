/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver.cpp

Abstract:

    SAT solver main class.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/


#include "sat/sat_solver.h"

#define ENABLE_TERNARY true

namespace sat {

    // -----------------------
    //
    // GC
    //
    // -----------------------

    bool solver::should_gc() const {
        return 
            m_conflicts_since_gc > m_gc_threshold &&
            (m_config.m_gc_strategy != GC_DYN_PSM || at_base_lvl());
    }

    void solver::do_gc() {
        if (!should_gc()) return;
        TRACE("sat", tout << m_conflicts_since_gc << " " << m_gc_threshold << "\n";);
        unsigned gc = m_stats.m_gc_clause;
        m_conflicts_since_gc = 0;
        m_gc_threshold += m_config.m_gc_increment;
        IF_VERBOSE(10, verbose_stream() << "(sat.gc)\n";);
        CASSERT("sat_gc_bug", check_invariant());
        switch (m_config.m_gc_strategy) {
        case GC_GLUE:
            gc_glue();
            break;
        case GC_PSM:
            gc_psm();
            break;
        case GC_GLUE_PSM:
            gc_glue_psm();
            break;
        case GC_PSM_GLUE:
            gc_psm_glue();
            break;
        case GC_DYN_PSM:
            if (!m_assumptions.empty()) {
                gc_glue_psm();
                break;
            }
            if (!at_base_lvl()) 
                return;
            gc_dyn_psm();
            break;
        default:
            UNREACHABLE();
            break;
        }
        if (m_ext) m_ext->gc();
        if (gc > 0 && should_defrag()) {
            defrag_clauses();
        }
        CASSERT("sat_gc_bug", check_invariant());
    }

    /**
       \brief Lex on (glue, size)
    */
    struct glue_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->glue() < c2->glue()) return true;
            return c1->glue() == c2->glue() && c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (psm, size)
    */
    struct psm_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->psm() < c2->psm()) return true;
            return c1->psm() == c2->psm() && c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (glue, psm, size)
    */
    struct glue_psm_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->glue() < c2->glue()) return true;
            if (c1->glue() > c2->glue()) return false;
            if (c1->psm() < c2->psm()) return true;
            if (c1->psm() > c2->psm()) return false;
            return c1->size() < c2->size();
        }
    };

    /**
       \brief Lex on (psm, glue, size)
    */
    struct psm_glue_lt {
        bool operator()(clause const * c1, clause const * c2) const {
            if (c1->psm() < c2->psm()) return true;
            if (c1->psm() > c2->psm()) return false;
            if (c1->glue() < c2->glue()) return true;
            if (c1->glue() > c2->glue()) return false;
            return c1->size() < c2->size();
        }
    };

    void solver::gc_glue() {
        std::stable_sort(m_learned.begin(), m_learned.end(), glue_lt());
        gc_half("glue");
    }

    void solver::gc_psm() {
        save_psm();
        std::stable_sort(m_learned.begin(), m_learned.end(), psm_lt());
        gc_half("psm");
    }

    void solver::gc_glue_psm() {
        save_psm();
        std::stable_sort(m_learned.begin(), m_learned.end(), glue_psm_lt());
        gc_half("glue-psm");
    }

    void solver::gc_psm_glue() {
        save_psm();
        std::stable_sort(m_learned.begin(), m_learned.end(), psm_glue_lt());
        gc_half("psm-glue");
    }

    /**
       \brief Compute the psm of all learned clauses.
    */
    void solver::save_psm() {
        for (clause* cp : m_learned) {
            cp->set_psm(psm(*cp));
        }
    }

    /**
       \brief GC (the second) half of the clauses in the database.
    */
    void solver::gc_half(char const * st_name) {
        TRACE("sat", tout << "gc\n";);
        unsigned sz     = m_learned.size();
        unsigned new_sz = sz/2; // std::min(sz/2, m_clauses.size()*2);
        unsigned j      = new_sz;
        for (unsigned i = new_sz; i < sz; i++) {
            clause & c = *(m_learned[i]);
            if (can_delete(c)) {
                detach_clause(c);
                del_clause(c);
            }
            else {
                m_learned[j] = &c;
                j++;
            }
        }
        new_sz = j;
        m_stats.m_gc_clause += sz - new_sz;
        m_learned.shrink(new_sz);
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :strategy " << st_name << " :deleted " << (sz - new_sz) << ")\n";);
    }

    bool solver::can_delete3(literal l1, literal l2, literal l3) const {                                                           
        if (value(l1) == l_true && 
            value(l2) == l_false && 
            value(l3) == l_false) {
            justification const& j = m_justification[l1.var()];
            if (j.is_ternary_clause()) {
                watched w1(l2, l3);
                watched w2(j.get_literal1(), j.get_literal2());
                return w1 != w2;
            }
        }
        return true;
    }

    bool solver::can_delete(clause const & c) const {
        if (c.on_reinit_stack())
            return false;
        if (ENABLE_TERNARY && c.size() == 3) {
            return
                can_delete3(c[0],c[1],c[2]) &&
                can_delete3(c[1],c[0],c[2]) &&
                can_delete3(c[2],c[0],c[1]);
        }
        literal l0 = c[0];
        if (value(l0) != l_true)
            return true;
        justification const & jst = m_justification[l0.var()];
        return !jst.is_clause() || cls_allocator().get_clause(jst.get_clause_offset()) != &c;
    }

    /**
       \brief Use gc based on dynamic psm. Clauses are initially frozen.
    */
    void solver::gc_dyn_psm() {
        TRACE("sat", tout << "gc\n";);
        // To do gc at scope_lvl() > 0, I will need to use the reinitialization stack, or live with the fact
        // that I may miss some propagations for reactivated clauses.
        SASSERT(at_base_lvl());
        // compute
        // d_tk
        unsigned h = 0;
        unsigned V_tk = 0;
        for (bool_var v = 0; v < num_vars(); v++) {
            if (m_assigned_since_gc[v]) {
                V_tk++;
                m_assigned_since_gc[v] = false;
            }
            if (m_phase[v] != m_prev_phase[v]) {
                h++;
                m_prev_phase[v] = m_phase[v];
            }
        }
        double d_tk = V_tk == 0 ? static_cast<double>(num_vars() + 1) : static_cast<double>(h)/static_cast<double>(V_tk);
        if (d_tk < m_min_d_tk)
            m_min_d_tk = d_tk;
        TRACE("sat_frozen", tout << "m_min_d_tk: " << m_min_d_tk << "\n";);
        unsigned frozen    = 0;
        unsigned deleted   = 0;
        unsigned activated = 0;
        clause_vector::iterator it  = m_learned.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = m_learned.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            if (!c.frozen()) {
                // Active clause
                if (c.glue() > m_config.m_gc_small_lbd) {
                    // I never delete clauses with small lbd
                    if (c.was_used()) {
                        c.reset_inact_rounds();
                    }
                    else {
                        c.inc_inact_rounds();
                        if (c.inact_rounds() > m_config.m_gc_k) {
                            detach_clause(c);
                            del_clause(c);
                            m_stats.m_gc_clause++;
                            deleted++;
                            continue;
                        }
                    }
                    c.unmark_used();
                    if (psm(c) > static_cast<unsigned>(c.size() * m_min_d_tk)) {
                        // move to frozen;
                        TRACE("sat_frozen", tout << "freezing size: " << c.size() << " psm: " << psm(c) << " " << c << "\n";);
                        detach_clause(c);
                        c.reset_inact_rounds();
                        c.freeze();
                        m_num_frozen++;
                        frozen++;
                    }
                }
            }
            else {
                // frozen clause
                clause & c = *(*it);
                if (psm(c) <= static_cast<unsigned>(c.size() * m_min_d_tk)) {
                    c.unfreeze();
                    m_num_frozen--;
                    activated++;
                    if (!activate_frozen_clause(c)) {
                        // clause was satisfied, reduced to a conflict, unit or binary clause.
                        del_clause(c);
                        continue;
                    }
                }
                else {
                    c.inc_inact_rounds();
                    if (c.inact_rounds() > m_config.m_gc_k) {
                        del_clause(c);
                        m_stats.m_gc_clause++;
                        deleted++;
                        continue;
                    }
                }
            }
            *it2 = *it;
            ++it2;
        }
        m_learned.set_end(it2);
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :d_tk " << d_tk << " :min-d_tk " << m_min_d_tk <<
                   " :frozen " << frozen << " :activated " << activated << " :deleted " << deleted << ")\n";);
    }

    // return true if should keep the clause, and false if we should delete it.
    bool solver::activate_frozen_clause(clause & c) {
        TRACE("sat_gc", tout << "reactivating:\n" << c << "\n";);
        SASSERT(at_base_lvl());
        // do some cleanup
        unsigned sz = c.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; i++) {
            literal l = c[i];
            switch (value(l)) {
            case l_true:
                return false;
            case l_false:
                break;
            case l_undef:
                if (i != j) {
                    std::swap(c[i], c[j]);
                }
                j++;
                break;
            }
        }
        TRACE("sat", tout << "after cleanup:\n" << mk_lits_pp(j, c.begin()) << "\n";);
        unsigned new_sz = j;
        switch (new_sz) {
        case 0:
            if (m_config.m_drat) m_drat.add();
            set_conflict();
            return false;
        case 1:
            assign_unit(c[0]);
            return false;
        case 2:
            mk_bin_clause(c[0], c[1], true);
            return false;
        default:
            shrink(c, sz, new_sz);
            attach_clause(c);
            return true;
        }
    }

    /**
       \brief Compute phase saving measure for the given clause.
    */
    unsigned solver::psm(clause const & c) const {
        unsigned r  = 0;
        for (literal l : c) {
            if (l.sign() ^ m_phase[l.var()]) {
                r++;
            }
        }
        return r;
    }

    /**
     * Control the size of the reinit-stack.
     * by agressively garbage collecting lemmas that are not asserting.
     */

    void solver::gc_reinit_stack(unsigned num_scopes) {
        return;
        SASSERT (!at_base_lvl());
        unsigned new_lvl = scope_lvl() - num_scopes;
        ptr_vector<clause> to_gc;
        unsigned j = m_scopes[new_lvl].m_clauses_to_reinit_lim;
        unsigned sz = m_clauses_to_reinit.size();
        if (sz - j <= 2000)
            return;
        for (unsigned i = j; i < sz; ++i) {
            auto cw = m_clauses_to_reinit[i];
            if (cw.is_binary() || is_asserting(new_lvl, cw)) 
                m_clauses_to_reinit[j++] = cw;
            else 
                to_gc.push_back(cw.get_clause());
        }
        m_clauses_to_reinit.shrink(j);
        if (to_gc.empty())
            return;
        for (clause* c : to_gc) {
            SASSERT(c->on_reinit_stack());
            c->set_removed(true);
            c->set_reinit_stack(false);
        }
        j = 0;
        for (unsigned i = 0; i < m_learned.size(); ++i) {
            clause & c = *(m_learned[i]);
            if (c.was_removed()) {
                detach_clause(c);
                del_clause(c);
            }
            else 
                m_learned[j++] = &c;            
        }
        std::cout << "gc: " << to_gc.size() << " " << m_learned.size() << " -> " << j << "\n";
        SASSERT(m_learned.size() - j == to_gc.size());
        m_learned.shrink(j);
    }

    bool solver::is_asserting(unsigned new_lvl, clause_wrapper const& cw) const {
        if (!cw.is_learned())
            return true;
        bool seen_true = false;
        for (literal lit : cw) {
            switch (value(lit)) {
            case l_true:
                if (lvl(lit) > new_lvl || seen_true)
                    return false;
                seen_true = true;
                continue;
            case l_false:
                continue;
            case l_undef:
                return false;
            }
        }
        return true;
    }

    void solver::gc_vars(bool_var max_var) {
        init_visited();
        m_aux_literals.reset();
        auto gc_watch = [&](literal lit) {
            auto& wl1 = get_wlist(lit);
            for (auto w : get_wlist(lit)) {
                if (w.is_binary_clause() && w.get_literal().var() < max_var && !is_visited(w.get_literal())) {
                    m_aux_literals.push_back(w.get_literal());
                    mark_visited(w.get_literal());
                }
            }
            wl1.reset();
        };
        for (unsigned v = max_var; v < num_vars(); ++v) {
            gc_watch(literal(v, false));
            gc_watch(literal(v, true));
        }

        for (literal lit : m_aux_literals) {
            auto& wl2 = get_wlist(~lit);
            unsigned j = 0;
            for (auto w2 : wl2) 
                if (!w2.is_binary_clause() || w2.get_literal().var() < max_var)
                    wl2[j++] = w2;
            wl2.shrink(j);                        
        }
        m_aux_literals.reset();

        auto gc_clauses = [&](ptr_vector<clause>& clauses) {
            unsigned j = 0;
            for (clause* c : clauses) {
                bool should_remove = false;
                for (auto lit : *c) 
                    should_remove |= lit.var() >= max_var;
                if (should_remove) {
                    SASSERT(!c->on_reinit_stack());
                    detach_clause(*c);
                    del_clause(*c);
                }
                else {
                    clauses[j++] = c;
                }
            }
            clauses.shrink(j);
        };
        gc_clauses(m_learned);
        gc_clauses(m_clauses);

        if (m_ext)
            m_ext->gc_vars(max_var);
        
        unsigned j = 0;
        for (literal lit : m_trail) {
            SASSERT(lvl(lit) == 0);
            if (lit.var() < max_var)
                m_trail[j++] = lit;
        }
        m_trail.shrink(j);
        shrink_vars(max_var);
    }

#if 0
    void solver::gc_reinit_stack(unsigned num_scopes) {
        SASSERT (!at_base_lvl());
        collect_clauses_to_gc(num_scopes);
        for (literal lit : m_watch_literals_to_gc) {
            mark_members_of_watch_list(lit);
            shrink_watch_list(lit);
        }
        unsigned j = 0;
        for (clause* c : m_learned) 
            if (!c->was_removed())
                m_learned[j++] = c;
        m_learned.shrink(j);
        for (clause* c : m_clauses_to_gc) 
            del_clause(*c);
        m_clauses_to_gc.reset();
    }

    void solver::add_to_gc(literal lit, clause_wrapper const& cw) {        
        m_literal2gc_clause.reserve(lit.index()+1);
        m_literal2gc_clause[lit.index()].push_back(cw);
        if (!is_visited(lit)) {
            mark_visited(lit);
            m_watch_literals_to_gc.push_back(lit);
        }
    }

    void solver::add_to_gc(clause_wrapper const& cw) {
        std::cout << "add-to-gc " << cw << "\n";
        if (cw.is_binary()) {
            add_to_gc(cw[0], cw);
            add_to_gc(cw[1], clause_wrapper(cw[1], cw[0]));
        }
        else if (ENABLE_TERNARY && cw.is_ternary()) {
            SASSERT(cw.is_learned());
            add_to_gc(cw[0], cw);
            add_to_gc(cw[1], cw);
            add_to_gc(cw[2], cw);
            cw.get_clause()->set_removed(true);
        }
        else {
            SASSERT(cw.is_learned());
            add_to_gc(cw[0], cw);
            add_to_gc(cw[1], cw); 
            cw.get_clause()->set_removed(true);
        }
    }

    void solver::insert_ternary_to_delete(literal lit, clause_wrapper const& cw) {
        SASSERT(cw.is_ternary());
        SASSERT(lit == cw[0] || lit == cw[1] || lit == cw[2]);
        literal lit1, lit2;
        if (cw[0] == lit) 
            lit1 = cw[1], lit2 = cw[2];
        else if (cw[1] == lit) 
            lit1 = cw[0], lit2 = cw[2];
        else 
            lit1 = cw[0], lit2 = cw[1];
        insert_ternary_to_delete(lit1, lit2, true);
    }

    void solver::insert_ternary_to_delete(literal lit1, literal lit2, bool should_delete) {
        if (lit1.index() > lit2.index())
            std::swap(lit1, lit2);        
        m_ternary_to_delete.push_back(std::tuple(lit1, lit2, should_delete));
    }

    bool solver::in_ternary_to_delete(literal lit1, literal lit2) {
        if (lit1.index() > lit2.index())
            std::swap(lit1, lit2);
        bool found = m_ternary_to_delete.contains(std::make_pair(lit1, lit2));
        if (found) std::cout << lit1 << " " << lit2 << "\n"; 
        return found;
    }


    void solver::collect_clauses_to_gc(unsigned num_scopes) {
        unsigned new_lvl = scope_lvl() - num_scopes;
        init_visited();
        m_watch_literals_to_gc.reset();
        unsigned j = m_scopes[new_lvl].m_clauses_to_reinit_lim;
        for (unsigned i = j, sz = m_clauses_to_reinit.size(); i < sz; ++i) {
            auto cw = m_clauses_to_reinit[i];
            if (is_asserting(new_lvl, cw)) 
                m_clauses_to_reinit[j++] = cw;
            else 
                add_to_gc(cw);
        }
        m_clauses_to_reinit.shrink(j);
        SASSERT(m_clauses_to_reinit.size() >= j);
    }

    void solver::mark_members_of_watch_list(literal lit) {
        init_visited();
        m_ternary_to_delete.reset();
        for (auto const& cw : m_literal2gc_clause[lit.index()]) {
            SASSERT(!cw.is_binary() || lit == cw[0]);
            SASSERT(cw.is_binary() || cw.was_removed());
            if (cw.is_binary()) 
                mark_visited(cw[1]);       
            else if (ENABLE_TERNARY && cw.is_ternary())
                insert_ternary_to_delete(lit, cw);
        }        
    }

    void solver::shrink_watch_list(literal lit) {
        auto& wl = get_wlist((~lit).index());
        unsigned j = 0, sz = wl.size(), end = sz;
        for (unsigned i = 0; i < end; ++i) {
            auto w = wl[i];
            if (w.is_binary_clause() && !is_visited(w.get_literal()))
                wl[j++] = w;
            else if (ENABLE_TERNARY && w.is_ternary_clause()) 
                insert_ternary_to_delete(w.literal1(), w.literal2(), false);
            else if (w.is_clause() && !get_clause(w).was_removed())
                wl[j++] = w;
            else if (w.is_ext_constraint())
                wl[j++] = w;
        }
#if 0
        std::sort(m_ternary_to_delete.begin(), m_ternary_to_delete.end());
        int prev = -1;
        unsigned k = 0;
        std::tuple<literal, literal, bool> p = tuple(null_literal, null_literal, false);
        for (unsigned i = 0; i < m_ternary_to_delete.size(); ++i) {
            auto const& t = m_ternary_to_delete[i];
        }
#endif
        std::cout << "gc-watch-list " << lit << " " << wl.size() << " -> " << j << "\n";
        wl.shrink(j);
        m_literal2gc_clause[lit.index()].reset();
    }


#endif

}
