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


#include <cmath>
#ifndef SINGLE_THREAD
#include <thread>
#endif
#include "util/luby.h"
#include "util/trace.h"
#include "util/max_cliques.h"
#include "util/gparams.h"
#include "sat/sat_solver.h"
#include "sat/sat_integrity_checker.h"
#include "sat/sat_lookahead.h"
#include "sat/sat_ddfw.h"
#include "sat/sat_prob.h"
#include "sat/sat_anf_simplifier.h"
#include "sat/sat_cut_simplifier.h"
#if defined(_MSC_VER) && !defined(_M_ARM) && !defined(_M_ARM64)
# include <xmmintrin.h>
#endif

#define ENABLE_TERNARY true

namespace sat {


    solver::solver(params_ref const & p, reslimit& l):
        solver_core(l),
        m_checkpoint_enabled(true),
        m_config(p),
        m_par(nullptr),
        m_drat(*this),
        m_cls_allocator_idx(false),
        m_cleaner(*this),
        m_simplifier(*this, p),
        m_scc(*this, p),
        m_asymm_branch(*this, p),
        m_probing(*this, p),
        m_mus(*this),
        m_binspr(*this),
        m_inconsistent(false),
        m_searching(false),
        m_conflict(justification(0)),
        m_num_frozen(0),
        m_activity_inc(128),
        m_case_split_queue(m_activity),
        m_qhead(0),
        m_scope_lvl(0),
        m_search_lvl(0),
        m_fast_glue_avg(),
        m_slow_glue_avg(),
        m_fast_glue_backup(),
        m_slow_glue_backup(),
        m_trail_avg(),
        m_params(p),
        m_par_id(0),
        m_par_syncing_clauses(false) {
        init_reason_unknown();
        updt_params(p);
        m_best_phase_size         = 0;
        m_conflicts_since_gc      = 0;
        m_conflicts_since_init    = 0;
        m_next_simplify           = 0;
        m_num_checkpoints         = 0;
        m_simplifications         = 0;
        m_touch_index             = 0;
        m_ext                     = nullptr;
        m_cuber                   = nullptr;
        m_local_search            = nullptr;
        m_mc.set_solver(this);
        mk_var(false, false);
    }

    solver::~solver() {
        m_ext = nullptr;
        SASSERT(m_config.m_num_threads > 1 || check_invariant());
        CTRACE("sat", !m_clauses.empty(), tout << "Delete clauses\n";);
        del_clauses(m_clauses);
        CTRACE("sat", !m_learned.empty(), tout << "Delete learned\n";);
        del_clauses(m_learned);
        dealloc(m_cuber);
        m_cuber = nullptr;
    }

    void solver::del_clauses(clause_vector& clauses) {
        for (clause * cp : clauses) 
            dealloc_clause(cp);
        clauses.reset();
        ++m_stats.m_non_learned_generation;
    }

    void solver::set_extension(extension* ext) {
        m_ext = ext;
        if (ext) {
            ext->set_solver(this);
            for (unsigned i = num_user_scopes(); i-- > 0;)
                ext->user_push();
            for (unsigned i = num_scopes(); i-- > 0;)
                ext->push();
        }
    }

    void solver::copy(solver const & src, bool copy_learned) {
        pop_to_base_level();
        del_clauses(m_clauses);
        del_clauses(m_learned);
        m_watches.reset();
        m_assignment.reset();
        m_justification.reset();
        m_decision.reset();
        m_eliminated.reset();
        m_external.reset();
        m_var_scope.reset();
        m_activity.reset();
        m_mark.reset();
        m_lit_mark.reset();
        m_best_phase.reset();
        m_phase.reset();
        m_prev_phase.reset();
        m_assigned_since_gc.reset();
        m_last_conflict.reset();
        m_last_propagation.reset();
        m_participated.reset();
        m_canceled.reset();
        m_reasoned.reset();
        m_case_split_queue.reset();
        m_simplifier.reset_todos();
        m_qhead = 0;
        m_trail.reset();
        m_scopes.reset();
        mk_var(false, false);

        if (src.inconsistent()) {
            set_conflict();
            return;
        }
        
        // create new vars
        for (bool_var v = num_vars(); v < src.num_vars(); v++) {
            bool ext  = src.m_external[v];
            bool dvar = src.m_decision[v];
            VERIFY(v == mk_var(ext, dvar));
            if (src.was_eliminated(v)) {
                set_eliminated(v, true);
            }
            m_phase[v] = src.m_phase[v];
            m_best_phase[v] = src.m_best_phase[v];
            m_prev_phase[v] = src.m_prev_phase[v];

            // inherit activity:
            m_activity[v] = src.m_activity[v];
            m_case_split_queue.activity_changed_eh(v, false);
        }

        //
        // register the extension before performing assignments.
        // the assignments may call back into the extension.
        //
        if (src.get_extension()) {
            m_ext = src.get_extension()->copy(this);
        }

        unsigned trail_sz = src.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            assign_unit(src.m_trail[i]);
        }

        // copy binary clauses 
        {
            unsigned sz = src.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l = ~to_literal(l_idx);
                if (src.was_eliminated(l.var())) continue;
                watch_list const & wlist = src.m_watches[l_idx];
                for (auto & wi : wlist) {
                    if (!wi.is_binary_clause())
                        continue;
                    literal l2 = wi.get_literal();
                    if (l.index() > l2.index() ||
                        src.was_eliminated(l2.var()))
                        continue;
                                        
                    watched w1(l2, wi.is_learned());
                    watched w2(l, wi.is_learned());
                    m_watches[(~l).index()].push_back(w1);
                    m_watches[(~l2).index()].push_back(w2);
                }
            }
        }

        {
            literal_vector buffer;
            // copy clauses
            for (clause* c : src.m_clauses) {
                buffer.reset();
                for (literal l : *c) buffer.push_back(l);
                mk_clause_core(buffer);
            }

            // copy high quality lemmas
            unsigned num_learned = 0;
            for (clause* c : src.m_learned) {
                if (c->glue() <= 2 || (c->size() <= 40 && c->glue() <= 8) || copy_learned) {
                    buffer.reset();
                    for (literal l : *c) buffer.push_back(l);
                    clause* c1 = mk_clause_core(buffer.size(), buffer.data(), sat::status::redundant());
                    if (c1) {
                        ++num_learned;
                        c1->set_glue(c->glue());
                        c1->set_psm(c->psm());
                    }
                }
            }
            IF_VERBOSE(2, verbose_stream() << "(sat.copy :learned " << num_learned << ")\n";);
        }
        m_best_phase_size = src.m_best_phase_size;
        if (m_best_phase_size > 0) {
            for (bool_var v = 0; v < num_vars(); ++v) {
                m_best_phase[v] = src.m_best_phase[v];
            }
        }

        m_user_scope_literals.reset();
        m_user_scope_literals.append(src.m_user_scope_literals);

        m_mc = src.m_mc;
        m_stats.m_units = init_trail_size();
    }

    // -----------------------
    //
    // Variable & Clause creation
    //
    // -----------------------

    void solver::reset_var(bool_var v, bool ext, bool dvar) {
        m_watches[2*v].reset();
        m_watches[2*v+1].reset();
        m_assignment[2*v] = l_undef;
        m_assignment[2*v+1] = l_undef;
        m_justification[v] = justification(UINT_MAX);
        m_decision[v] = dvar;
        m_eliminated[v] = false;
        m_external[v] = ext;
        m_var_scope[v] = scope_lvl();
        m_touched[v] = 0;
        m_activity[v] = 0;
        m_mark[v] = false;
        m_lit_mark[2*v] = false;
        m_lit_mark[2*v+1] = false;
        m_phase[v] = false;
        m_best_phase[v] = false;
        m_prev_phase[v] = false;
        m_assigned_since_gc[v] = false;
        m_last_conflict[v] = 0;        
        m_last_propagation[v] = 0;
        m_participated[v] = 0;
        m_canceled[v] = 0;
        m_reasoned[v] = 0;
        m_case_split_queue.mk_var_eh(v);
        m_simplifier.insert_elim_todo(v);
    }

    bool_var solver::mk_var(bool ext, bool dvar) {
        m_model_is_current = false;
        m_stats.m_mk_var++;
        bool_var v = m_justification.size();
        if (!m_free_vars.empty()) {
            v = m_free_vars.back();
            m_free_vars.pop_back();
            m_active_vars.push_back(v);
            reset_var(v, ext, dvar);
            return v;
        }
        m_active_vars.push_back(v);
        m_watches.push_back(watch_list());
        m_watches.push_back(watch_list());
        m_assignment.push_back(l_undef);
        m_assignment.push_back(l_undef);
        m_justification.push_back(justification(UINT_MAX));
        m_decision.push_back(dvar);
        m_eliminated.push_back(false);
        m_external.push_back(ext);
        m_var_scope.push_back(scope_lvl());
        m_touched.push_back(0);
        m_activity.push_back(0);
        m_mark.push_back(false);
        m_lit_mark.push_back(false);
        m_lit_mark.push_back(false);
        m_phase.push_back(false);
        m_best_phase.push_back(false);
        m_prev_phase.push_back(false);
        m_assigned_since_gc.push_back(false);
        m_last_conflict.push_back(0);
        m_last_propagation.push_back(0);
        m_participated.push_back(0);
        m_canceled.push_back(0);
        m_reasoned.push_back(0);
        m_case_split_queue.mk_var_eh(v);
        m_simplifier.insert_elim_todo(v);
        SASSERT(!was_eliminated(v));
        return v;
    }

    void solver::set_non_external(bool_var v) {
        m_external[v] = false;
    }

    void solver::set_external(bool_var v) {
        m_external[v] = true;
    }

    void solver::set_eliminated(bool_var v, bool f) { 
        if (m_eliminated[v] == f)
            return;
        if (!f) 
            reset_var(v, m_external[v], m_decision[v]);
        else if (f && m_ext)
            m_ext->set_eliminated(v);
        m_eliminated[v] = f; 
    }


    clause* solver::mk_clause(unsigned num_lits, literal * lits, sat::status st) {
        m_model_is_current = false;
            
        for (unsigned i = 0; i < num_lits; i++) 
            VERIFY(!was_eliminated(lits[i]));
        
        DEBUG_CODE({
                for (unsigned i = 0; i < num_lits; i++) {
                    CTRACE("sat", was_eliminated(lits[i]), tout << lits[i] << " was eliminated\n";);
                    SASSERT(!was_eliminated(lits[i]));
                }
        });

        if (m_user_scope_literals.empty()) {
            return mk_clause_core(num_lits, lits, st);
        }
        else {
            m_aux_literals.reset();
            m_aux_literals.append(num_lits, lits);
            m_aux_literals.append(m_user_scope_literals);
            return mk_clause_core(m_aux_literals.size(), m_aux_literals.data(), st);
        }
    }

    clause* solver::mk_clause(literal l1, literal l2, sat::status st) {
        literal ls[2] = { l1, l2 };
        return mk_clause(2, ls, st);
    }

    clause* solver::mk_clause(literal l1, literal l2, literal l3, sat::status st) {
        literal ls[3] = { l1, l2, l3 };
        return mk_clause(3, ls, st);
    }

    void solver::del_clause(clause& c) {
        if (!c.is_learned()) {
            m_stats.m_non_learned_generation++;
        } 
        if (c.frozen()) {
            --m_num_frozen;
        }
        if (!c.was_removed() && m_config.m_drat && !m_drat.is_cleaned(c)) {
            m_drat.del(c);
        }
        dealloc_clause(&c);        
        if (m_searching) 
            m_stats.m_del_clause++;
    }

    void solver::drat_explain_conflict() {
        if (m_config.m_drat && m_ext) {
            extension::scoped_drating _sd(*m_ext);
            bool unique_max;
            m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);        
            resolve_conflict_for_unsat_core();                
        }
    }

    void solver::drat_log_unit(literal lit, justification j) {
        if (!m_ext)
            return;
        extension::scoped_drating _sd(*m_ext.get());
        if (j.get_kind() == justification::EXT_JUSTIFICATION) 
            fill_ext_antecedents(lit, j, false);
        m_drat.add(lit, m_searching);
    }

    void solver::drat_log_clause(unsigned num_lits, literal const* lits, sat::status st) {
        m_drat.add(num_lits, lits, st);
    }

    clause * solver::mk_clause_core(unsigned num_lits, literal * lits, sat::status st) {
        bool redundant = st.is_redundant();
        TRACE("sat", tout << "mk_clause: "  << mk_lits_pp(num_lits, lits) << (redundant?" learned":" aux") << "\n";);
        if (!redundant || !st.is_sat()) {
            unsigned old_sz = num_lits;
            bool keep = simplify_clause(num_lits, lits);
            TRACE("sat_mk_clause", tout << "mk_clause (after simp), keep: " << keep << "\n" << mk_lits_pp(num_lits, lits) << "\n";);
            if (!keep) {
                return nullptr; // clause is equivalent to true.
            }
            // if an input clause is simplified, then log the simplified version as learned
            if (m_config.m_drat && old_sz > num_lits)
                drat_log_clause(num_lits, lits, st);

            ++m_stats.m_non_learned_generation;
            if (!m_searching) {
                m_mc.add_clause(num_lits, lits);
            }
        }       


        switch (num_lits) {
        case 0:
            set_conflict();
            return nullptr;
        case 1:
            if (m_config.m_drat && (!st.is_sat() || st.is_input()))
                drat_log_clause(num_lits, lits, st);
            assign_unit(lits[0]);
            return nullptr;
        case 2:
            mk_bin_clause(lits[0], lits[1], st);
            if (redundant && m_par) 
                m_par->share_clause(*this, lits[0], lits[1]);
            return nullptr;
        case 3:
            if (ENABLE_TERNARY) 
                return mk_ter_clause(lits, st);
            Z3_fallthrough;
        default:
            return mk_nary_clause(num_lits, lits, st);
        }
    }

    void solver::mk_bin_clause(literal l1, literal l2, sat::status st) {
        bool redundant = st.is_redundant();
        m_touched[l1.var()] = m_touch_index;
        m_touched[l2.var()] = m_touch_index;
        
        if (redundant && find_binary_watch(get_wlist(~l1), ~l2) && value(l1) == l_undef) {
            assign_unit(l1);
            return;
        }
        if (redundant && find_binary_watch(get_wlist(~l2), ~l1) && value(l2) == l_undef) {
            assign_unit(l2);
            return;
        }
        watched* w0 = redundant ? find_binary_watch(get_wlist(~l1), l2) : nullptr;
        if (w0) {
            TRACE("sat", tout << "found binary " << l1 << " " << l2 << "\n";);
            if (w0->is_learned() && !redundant) {
                w0->set_learned(false);
                w0 = find_binary_watch(get_wlist(~l2), l1);            
                VERIFY(w0);
                w0->set_learned(false);                        
            }
            if (propagate_bin_clause(l1, l2) && !at_base_lvl() && !redundant)
                push_reinit_stack(l1, l2);
            else if (has_variables_to_reinit(l1, l2))
                push_reinit_stack(l1, l2);
            return;
        }
        if (m_config.m_drat) 
            m_drat.add(l1, l2, st);
        if (propagate_bin_clause(l1, l2)) {
            if (at_base_lvl())
                return;
            push_reinit_stack(l1, l2);
        }
        else if (has_variables_to_reinit(l1, l2))
            push_reinit_stack(l1, l2);
        m_stats.m_mk_bin_clause++;
        get_wlist(~l1).push_back(watched(l2, redundant));
        get_wlist(~l2).push_back(watched(l1, redundant));
    }

    bool solver::has_variables_to_reinit(clause const& c) const {
        for (auto lit : c)
            if (m_var_scope[lit.var()] > 0)
                return true;
        return false;
    }

    bool solver::has_variables_to_reinit(literal l1, literal l2) const {
        if (at_base_lvl())
            return false;
        if (m_var_scope[l1.var()] > 0)
            return true;
        if (m_var_scope[l2.var()] > 0)
            return true;
        return false;
    }

    bool solver::propagate_bin_clause(literal l1, literal l2) {
        if (value(l2) == l_false) {
            m_stats.m_bin_propagate++;
            assign(l1, justification(lvl(l2), l2));            
            return true;
        }
        if (value(l1) == l_false) {
            m_stats.m_bin_propagate++;
            assign(l2, justification(lvl(l1), l1));
            return true;
        }
        return false;
    }

    void solver::push_reinit_stack(clause & c) {
        SASSERT(!at_base_lvl());
        TRACE("sat_reinit", tout << "adding to reinit stack: " << c << "\n";);
        m_clauses_to_reinit.push_back(clause_wrapper(c));
        c.set_reinit_stack(true);
    }

    void solver::push_reinit_stack(literal l1, literal l2) {
        TRACE("sat_reinit", tout << "adding to reinit stack: " << l1 << " " << l2 << "\n";);
        m_clauses_to_reinit.push_back(clause_wrapper(l1, l2));
    }

    clause * solver::mk_ter_clause(literal * lits, sat::status st) {
        VERIFY(ENABLE_TERNARY);
        m_stats.m_mk_ter_clause++;
        clause * r = alloc_clause(3, lits, st.is_redundant());
        bool reinit = attach_ter_clause(*r, st);
        if (reinit || has_variables_to_reinit(*r)) push_reinit_stack(*r);
        if (st.is_redundant())
            m_learned.push_back(r);
        else
            m_clauses.push_back(r);
        for (literal l : *r) {
            m_touched[l.var()] = m_touch_index;
        }
        return r;
    }

    bool solver::attach_ter_clause(clause & c, sat::status st) {
        VERIFY(ENABLE_TERNARY);
        bool reinit = false;
        if (m_config.m_drat) m_drat.add(c, st);
        TRACE("sat_verbose", tout << c << "\n";);
        SASSERT(!c.was_removed());
        m_watches[(~c[0]).index()].push_back(watched(c[1], c[2]));
        m_watches[(~c[1]).index()].push_back(watched(c[0], c[2]));
        m_watches[(~c[2]).index()].push_back(watched(c[0], c[1]));
        if (!at_base_lvl()) 
            reinit = propagate_ter_clause(c);        
        return reinit;
    }

    bool solver::propagate_ter_clause(clause& c) {
        bool reinit = false;
        if (value(c[1]) == l_false && value(c[2]) == l_false) {
            m_stats.m_ter_propagate++;
            assign(c[0], justification(std::max(lvl(c[1]), lvl(c[2])), c[1], c[2]));
            reinit = !c.is_learned();
        }
        else if (value(c[0]) == l_false && value(c[2]) == l_false) {
            m_stats.m_ter_propagate++;
            assign(c[1], justification(std::max(lvl(c[0]), lvl(c[2])), c[0], c[2]));
            reinit = !c.is_learned();
        }
        else if (value(c[0]) == l_false && value(c[1]) == l_false) {
            m_stats.m_ter_propagate++;
            assign(c[2], justification(std::max(lvl(c[0]), lvl(c[1])), c[0], c[1]));
            reinit = !c.is_learned();
        }
        return reinit;
    }

    clause * solver::mk_nary_clause(unsigned num_lits, literal * lits, sat::status st) {
        m_stats.m_mk_clause++;
        clause * r = alloc_clause(num_lits, lits, st.is_redundant());
        SASSERT(!st.is_redundant() || r->is_learned());
        bool reinit = attach_nary_clause(*r, st.is_sat() && st.is_redundant());
        if (reinit || has_variables_to_reinit(*r)) push_reinit_stack(*r);
        if (st.is_redundant()) {
            m_learned.push_back(r);
        }
        else {
            m_clauses.push_back(r);
        }
        if (m_config.m_drat) {
            m_drat.add(*r, st);
        }
        for (literal l : *r) {
            m_touched[l.var()] = m_touch_index;
        }
        return r;
    }

    bool solver::attach_nary_clause(clause & c, bool is_asserting) {
        bool reinit = false;
        clause_offset cls_off = cls_allocator().get_offset(&c);
        if (!at_base_lvl()) {
            if (is_asserting) {
                unsigned w2_idx = select_learned_watch_lit(c);
                std::swap(c[1], c[w2_idx]);
            }
            else {
                unsigned w1_idx = select_watch_lit(c, 0);
                std::swap(c[0], c[w1_idx]);
                unsigned w2_idx = select_watch_lit(c, 1);
                std::swap(c[1], c[w2_idx]);
            }

            if (value(c[0]) == l_false) {
                m_stats.m_propagate++; 
                unsigned level = lvl(c[0]);
                for (unsigned i = c.size(); i-- > 2; ) {
                    level = std::max(level, lvl(c[i]));
                }
                assign(c[1], justification(level, cls_off));
                reinit |= !c.is_learned();
            }
            else if (value(c[1]) == l_false) {
                m_stats.m_propagate++;
                unsigned level = lvl(c[1]);
                for (unsigned i = c.size(); i-- > 2; ) {
                    level = std::max(level, lvl(c[i]));
                }
                assign(c[0], justification(level, cls_off));
                reinit |= !c.is_learned();
            }
        }
        unsigned some_idx = c.size() >> 1;
        literal block_lit = c[some_idx];
        VERIFY(!c.frozen());
        DEBUG_CODE(for (auto const& w : m_watches[(~c[0]).index()]) SASSERT(!w.is_clause() || w.get_clause_offset() != cls_off););
        DEBUG_CODE(for (auto const& w : m_watches[(~c[1]).index()]) SASSERT(!w.is_clause() || w.get_clause_offset() != cls_off););
        SASSERT(c[0] != c[1]);
        m_watches[(~c[0]).index()].push_back(watched(block_lit, cls_off));
        m_watches[(~c[1]).index()].push_back(watched(block_lit, cls_off));
        return reinit;
    }

    void solver::attach_clause(clause & c, bool & reinit) {
        SASSERT(c.size() > 2);
        reinit = false;
        if (ENABLE_TERNARY && c.size() == 3)
            reinit = attach_ter_clause(c, c.is_learned() ? sat::status::redundant() : sat::status::asserted());
        else
            reinit = attach_nary_clause(c, c.is_learned() && !c.on_reinit_stack());
    }

    void solver::set_learned(clause& c, bool redundant) {
        if (c.is_learned() != redundant) 
            c.set_learned(redundant);
    }

    void solver::set_learned1(literal l1, literal l2, bool redundant) {
        for (watched& w : get_wlist(~l1)) {
            if (w.is_binary_clause() && l2 == w.get_literal() && !w.is_learned()) {
                w.set_learned(redundant);
                break;
            }
        }
    }

    void solver::shrink(clause& c, unsigned old_sz, unsigned new_sz) {
        SASSERT(new_sz > 2);
        SASSERT(old_sz >= new_sz);
        if (old_sz != new_sz) {
            c.shrink(new_sz);
            for (literal l : c) {
                m_touched[l.var()] = m_touch_index;
            }
            if (m_config.m_drat) {
                m_drat.add(c, status::redundant());
                c.restore(old_sz);
                m_drat.del(c);
                c.shrink(new_sz);
            }
        }
    }

    bool solver::memory_pressure() {
        return 3*cls_allocator().get_allocation_size()/2 + memory::get_allocation_size() > memory::get_max_memory_size();
    }

    struct solver::cmp_activity {
        solver& s;
        cmp_activity(solver& s):s(s) {}
        bool operator()(bool_var v1, bool_var v2) const {
            return s.m_activity[v1] > s.m_activity[v2];
        }
    };

    bool solver::should_defrag() {
        if (m_defrag_threshold > 0) --m_defrag_threshold;
        return m_defrag_threshold == 0 && m_config.m_gc_defrag;
    }

    void solver::defrag_clauses() {
        m_defrag_threshold = 2;
        if (memory_pressure()) return;
        pop(scope_lvl());
        IF_VERBOSE(2, verbose_stream() << "(sat-defrag)\n");
        clause_allocator& alloc = m_cls_allocator[!m_cls_allocator_idx];
        ptr_vector<clause> new_clauses, new_learned;
        for (clause* c : m_clauses) c->unmark_used();
        for (clause* c : m_learned) c->unmark_used();

        svector<bool_var> vars;
        for (unsigned i = 0; i < num_vars(); ++i) vars.push_back(i);
        std::stable_sort(vars.begin(), vars.end(), cmp_activity(*this));
        literal_vector lits;
        for (bool_var v : vars) lits.push_back(literal(v, false)), lits.push_back(literal(v, true));
        // walk clauses, reallocate them in an order that defragments memory and creates locality.
        for (literal lit : lits) {
            watch_list& wlist = m_watches[lit.index()];
            for (watched& w : wlist) {
                if (w.is_clause()) {
                    clause& c1 = get_clause(w);
                    clause_offset offset;
                    if (c1.was_used()) {
                        offset = c1.get_new_offset();
                    }
                    else {
                        clause* c2 = alloc.copy_clause(c1); 
                        c1.mark_used();
                        if (c1.is_learned()) {
                            new_learned.push_back(c2);
                        }
                        else {
                            new_clauses.push_back(c2);
                        }
                        offset = get_offset(*c2);
                        c1.set_new_offset(offset);
                    }
                    w = watched(w.get_blocked_literal(), offset);
                }
            }
        }

        // reallocate ternary clauses.
        for (clause* c : m_clauses) {
            if (!c->was_used()) {
                SASSERT(c->size() == 3);
                new_clauses.push_back(alloc.copy_clause(*c));
            }
            dealloc_clause(c);
        }

        for (clause* c : m_learned) {
            if (!c->was_used()) {
                SASSERT(c->size() == 3);
                new_learned.push_back(alloc.copy_clause(*c));
            }
            dealloc_clause(c);
        }
        m_clauses.swap(new_clauses);
        m_learned.swap(new_learned);

        cls_allocator().finalize();
        m_cls_allocator_idx = !m_cls_allocator_idx;

        reinit_assumptions();
    }


    void solver::set_learned(literal l1, literal l2, bool redundant) {
        set_learned1(l1, l2, redundant);
        set_learned1(l2, l1, redundant);
    }

    /**
       \brief Select a watch literal starting the search at the given position.
       This method is only used for clauses created during the search.

       I use the following rules to select a watch literal.

       1- select a literal l in idx >= starting_at such that value(l) = l_true,
       and for all l' in idx' >= starting_at . value(l') = l_true implies lvl(l) <= lvl(l')

       The purpose of this rule is to make the clause inactive for as long as possible. A clause
       is inactive when it contains a literal assigned to true.

       2- if there isn't a literal assigned to true, then select an unassigned literal l in idx >= starting_at

       3- if there isn't a literal l in idx >= starting_at such that value(l) = l_true or
       value(l) = l_undef (that is, all literals at positions >= starting_at are assigned
       to false), then peek the literal l such that for all l' starting at starting_at
       lvl(l) >= lvl(l')

       Without rule 3, boolean propagation is incomplete, that is, it may miss possible propagations.

       \remark The method select_lemma_watch_lit is used to select the watch literal for regular learned clauses.
    */
    unsigned solver::select_watch_lit(clause const & cls, unsigned starting_at) const {
        SASSERT(cls.size() >= 2);
        unsigned min_true_idx  = UINT_MAX;
        unsigned max_false_idx = UINT_MAX;
        unsigned unknown_idx   = UINT_MAX;
        unsigned n = cls.size();
        for (unsigned i = starting_at; i < n; i++) {
            literal l   = cls[i];
            switch(value(l)) {
            case l_false:
                if (max_false_idx == UINT_MAX || lvl(l) > lvl(cls[max_false_idx]))
                    max_false_idx = i;
                break;
            case l_undef:
                unknown_idx = i;
                break;
            case l_true:
                if (min_true_idx == UINT_MAX || lvl(l) < lvl(cls[min_true_idx]))
                    min_true_idx = i;
                break;
            }
        }
        if (min_true_idx != UINT_MAX)
            return min_true_idx;
        if (unknown_idx != UINT_MAX)
            return unknown_idx;
        SASSERT(max_false_idx != UINT_MAX);
        return max_false_idx;
    }

    /**
       \brief The learned clauses (lemmas) produced by the SAT solver
       have the property that the first literal will be implied by it
       after backtracking. All other literals are assigned to (or
       implied to be) false when the learned clause is created. The
       first watch literal will always be the first literal.  The
       second watch literal is computed by this method. It should be
       the literal with the highest decision level.

       // TODO: do we really need this? strength the conflict resolution
    */
    unsigned solver::select_learned_watch_lit(clause const & cls) const {
        SASSERT(cls.size() >= 2);
        unsigned max_false_idx = UINT_MAX;
        unsigned num_lits = cls.size();
        for (unsigned i = 1; i < num_lits; i++) {
            literal l    = cls[i];
            CTRACE("sat", value(l) != l_false, tout << l << ":=" << value(l););
            SASSERT(value(l) == l_false);
            if (max_false_idx == UINT_MAX || lvl(l) > lvl(cls[max_false_idx]))
                max_false_idx = i;
        }
        return max_false_idx;
    }

    template<bool lvl0>
    bool solver::simplify_clause_core(unsigned & num_lits, literal * lits) const {
        std::sort(lits, lits+num_lits);
        literal prev = null_literal;
        unsigned i = 0;
        unsigned j = 0;
        for (; i < num_lits; i++) {
            literal curr = lits[i];
            lbool val = value(curr);
            if (!lvl0 && lvl(curr) > 0)
                val = l_undef;
            switch (val) {
            case l_false:
                break; // ignore literal
            case l_undef:
                if (curr == ~prev)
                    return false; // clause is equivalent to true
                if (curr != prev) {
                    prev = curr;
                    if (i != j)
                        std::swap(lits[j], lits[i]);
                    j++;
                }
                break;
            case l_true:
                return false; // clause is equivalent to true
            }
        }
        num_lits = j;
        return true;
    }

    bool solver::simplify_clause(unsigned & num_lits, literal * lits) const {
        if (at_base_lvl()) 
            return simplify_clause_core<true>(num_lits, lits);
        else
            return simplify_clause_core<false>(num_lits, lits);
    }

    void solver::detach_bin_clause(literal l1, literal l2, bool redundant) {
        get_wlist(~l1).erase(watched(l2, redundant));
        get_wlist(~l2).erase(watched(l1, redundant));
        if (m_config.m_drat) m_drat.del(l1, l2);       
    }

    void solver::detach_clause(clause & c) {
        if (ENABLE_TERNARY && c.size() == 3)
            detach_ter_clause(c);
        else
            detach_nary_clause(c);
    }

    void solver::detach_nary_clause(clause & c) {
        clause_offset cls_off = get_offset(c);
        erase_clause_watch(get_wlist(~c[0]), cls_off);
        erase_clause_watch(get_wlist(~c[1]), cls_off);
    }

    void solver::detach_ter_clause(clause & c) {
        erase_ternary_watch(get_wlist(~c[0]), c[1], c[2]);
        erase_ternary_watch(get_wlist(~c[1]), c[0], c[2]);
        erase_ternary_watch(get_wlist(~c[2]), c[0], c[1]);
    }

    // -----------------------
    //
    // Basic
    //
    // -----------------------

    void solver::set_conflict(justification c, literal not_l) {
        if (m_inconsistent)
            return;
        m_inconsistent = true;
        m_conflict = c;
        m_not_l    = not_l;
    }

    void solver::assign_core(literal l, justification j) {
        SASSERT(value(l) == l_undef);
        TRACE("sat_assign_core", tout << l << " " << j << "\n";);
        if (j.level() == 0) {
            if (m_config.m_drat) 
                drat_log_unit(l, j);
            
            j = justification(0); // erase justification for level 0
        }
        else {
            VERIFY(!at_base_lvl());
        }
        m_assignment[l.index()]    = l_true;
        m_assignment[(~l).index()] = l_false;
        bool_var v = l.var();
        m_justification[v]         = j;
        m_phase[v]                 = !l.sign();
        m_assigned_since_gc[v]     = true;
        m_trail.push_back(l);
        
        switch (m_config.m_branching_heuristic) {
        case BH_VSIDS: 
            break;
        case BH_CHB:
            m_last_propagation[v] = m_stats.m_conflict;
            break;
        }

        if (m_config.m_anti_exploration) {
            uint64_t age = m_stats.m_conflict - m_canceled[v];
            if (age > 0) {
                double decay = pow(0.95, static_cast<double>(age));
                set_activity(v, static_cast<unsigned>(m_activity[v] * decay));
                // NB. MapleSAT does not update canceled.
                m_canceled[v] = m_stats.m_conflict;
            }
        }
        
        if (m_config.m_propagate_prefetch) {
#if defined(__GNUC__) || defined(__clang__)
            __builtin_prefetch((const char*)((m_watches[l.index()].data())));
#else
    #if !defined(_M_ARM) && !defined(_M_ARM64)
            _mm_prefetch((const char*)((m_watches[l.index()].data())), _MM_HINT_T1);
    #endif
#endif
        }

        SASSERT(!l.sign() || !m_phase[v]);
        SASSERT(l.sign()  || m_phase[v]);
        SASSERT(!l.sign() || value(v) == l_false);
        SASSERT(l.sign()  || value(v) == l_true);
        SASSERT(value(l) == l_true);
        SASSERT(value(~l) == l_false);
    }

    lbool solver::status(clause const & c) const {
        bool found_undef = false;
        for (literal lit : c) {
            switch (value(lit)) {
            case l_true:
                return l_true;
            case l_undef:
                found_undef = true;
                break;
            default:
                break;
            }
        }
        return found_undef ? l_undef : l_false;
    }

    // -----------------------
    //
    // Propagation
    //
    // -----------------------

    bool solver::propagate_core(bool update) {
        while (m_qhead < m_trail.size() && !m_inconsistent) {
            do {
                checkpoint();
                m_cleaner.dec();
                literal l = m_trail[m_qhead];
                m_qhead++;
                if (!propagate_literal(l, update))
                    return false;
            } while (m_qhead < m_trail.size());

            if (m_ext && (!is_probing() || at_base_lvl())) 
                m_ext->unit_propagate();            
        }
        if (m_inconsistent)
            return false;

        SASSERT(m_qhead == m_trail.size());
        SASSERT(!m_inconsistent);
        return true;
    }

    bool solver::propagate(bool update) {
        unsigned qhead = m_qhead;
        bool r = propagate_core(update);
        if (m_config.m_branching_heuristic == BH_CHB) {
            update_chb_activity(r, qhead);
        }
        CASSERT("sat_propagate", check_invariant());
        CASSERT("sat_missed_prop", check_missed_propagation());
        return r;
    }

    bool solver::propagate_literal(literal l, bool update) {
        literal l1, l2;
        lbool val1, val2;
        bool keep;
        unsigned curr_level = lvl(l);
        TRACE("sat_propagate", tout << "propagating: " << l << "@" << curr_level << " " << m_justification[l.var()] << "\n"; );

        literal not_l = ~l;
        SASSERT(value(l) == l_true);
        SASSERT(value(not_l) == l_false);
        watch_list& wlist = m_watches[l.index()];
        m_asymm_branch.dec(wlist.size());
        m_probing.dec(wlist.size());
        watch_list::iterator it = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
#define CONFLICT_CLEANUP() {                    \
                for (; it != end; ++it, ++it2)  \
                    *it2 = *it;                 \
                wlist.set_end(it2);             \
            }
        for (; it != end; ++it) {
            switch (it->get_kind()) {
            case watched::BINARY:
                l1 = it->get_literal();
                switch (value(l1)) {
                case l_false:
                    CONFLICT_CLEANUP();
                    set_conflict(justification(curr_level, not_l), ~l1);
                    return false;
                case l_undef:
                    m_stats.m_bin_propagate++;
                    assign_core(l1, justification(curr_level, not_l));
                    break;
                case l_true:
                    break; // skip
                }
                *it2 = *it;
                it2++;
                break;
            case watched::TERNARY:
                l1 = it->get_literal1();
                l2 = it->get_literal2();
                val1 = value(l1);
                val2 = value(l2);
                if (val1 == l_false && val2 == l_undef) {
                    m_stats.m_ter_propagate++;
                    assign_core(l2, justification(std::max(curr_level, lvl(l1)), l1, not_l));
                }
                else if (val1 == l_undef && val2 == l_false) {
                    m_stats.m_ter_propagate++;
                    assign_core(l1, justification(std::max(curr_level, lvl(l2)), l2, not_l));
                }
                else if (val1 == l_false && val2 == l_false) {
                    CONFLICT_CLEANUP();
                    set_conflict(justification(std::max(curr_level, lvl(l1)), l1, not_l), ~l2);
                    return false;
                }
                *it2 = *it;
                it2++;
                break;
            case watched::CLAUSE: {
                if (value(it->get_blocked_literal()) == l_true) {
                    TRACE("propagate_clause_bug", tout << "blocked literal " << it->get_blocked_literal() << "\n";
                    tout << get_clause(it) << "\n";);
                    *it2 = *it;
                    it2++;
                    break;
                }
                clause_offset cls_off = it->get_clause_offset();
                clause& c = get_clause(cls_off);
                TRACE("propagate_clause_bug", tout << "processing... " << c << "\nwas_removed: " << c.was_removed() << "\n";);
                if (c[0] == not_l)
                    std::swap(c[0], c[1]);
                CTRACE("propagate_bug", c[1] != not_l, tout << "l: " << l << " " << c << "\n";);
                if (c.was_removed() || c.size() == 1 || c[1] != not_l) {
                    // Remark: this method may be invoked when the watch lists are not in a consistent state,
                    // and may contain dead/removed clauses, or clauses with removed literals.
                    // See: method propagate_unit at sat_simplifier.cpp
                    // So, we must check whether the clause was marked for deletion, or
                    // c[1] != not_l
                    *it2 = *it;
                    it2++;
                    break;
                }
                if (value(c[0]) == l_true) {
                    it2->set_clause(c[0], cls_off);
                    it2++;
                    break;
                }
                VERIFY(c[1] == not_l);
                literal* l_it = c.begin() + 2;
                literal* l_end = c.end();
                unsigned assign_level = curr_level;
                unsigned max_index = 1;
                for (; l_it != l_end; ++l_it) {
                    if (value(*l_it) != l_false) {
                        c[1] = *l_it;
                        *l_it = not_l;
                        DEBUG_CODE(for (auto const& w : m_watches[(~c[1]).index()]) VERIFY(!w.is_clause() || w.get_clause_offset() != cls_off););
                        m_watches[(~c[1]).index()].push_back(watched(c[0], cls_off));
                        goto end_clause_case;
                    }
                }
                SASSERT(value(c[0]) == l_false || value(c[0]) == l_undef);
                if (assign_level != scope_lvl()) {
                    for (unsigned i = 2; i < c.size(); ++i) {
                        unsigned level = lvl(c[i]);
                        if (level > assign_level) {
                            assign_level = level;
                            max_index = i;
                        }
                    }
                    IF_VERBOSE(20, verbose_stream() << "lower assignment level " << assign_level << " scope: " << scope_lvl() << "\n");
                }

                if (value(c[0]) == l_false) {
                    assign_level = std::max(assign_level, lvl(c[0]));
                    c.mark_used();
                    CONFLICT_CLEANUP();
                    set_conflict(justification(assign_level, cls_off));
                    return false;
                }
                else {
                    if (max_index != 1) {
                        IF_VERBOSE(20, verbose_stream() << "swap watch for: " << c[1] << " " << c[max_index] << "\n");
                        std::swap(c[1], c[max_index]);
                        m_watches[(~c[1]).index()].push_back(watched(c[0], cls_off));
                    }
                    else {
                        *it2 = *it;
                        it2++;
                    }
                    m_stats.m_propagate++;
                    c.mark_used();
                    assign_core(c[0], justification(assign_level, cls_off));
                    if (update && c.is_learned() && c.glue() > 2) {
                        unsigned glue;
                        if (num_diff_levels_below(c.size(), c.begin(), c.glue() - 1, glue)) {
                            c.set_glue(glue);
                        }
                    }
                }
            end_clause_case:
                break;
            }
            case watched::EXT_CONSTRAINT:
                SASSERT(m_ext);
                keep = m_ext->propagated(l, it->get_ext_constraint_idx());
                if (m_inconsistent) {
                    if (!keep) {
                        ++it;
                    }
                    CONFLICT_CLEANUP();
                    return false;
                }
                if (keep) {
                    *it2 = *it;
                    it2++;
                }
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        wlist.set_end(it2);
        if (m_ext && m_external[l.var()] && (!is_probing() || at_base_lvl()))
            m_ext->asserted(l);

        return true;
    }

    void solver::display_lookahead_scores(std::ostream& out) {
        lookahead lh(*this);
        lh.display_lookahead_scores(out);
    }

    lbool solver::cube(bool_var_vector& vars, literal_vector& lits, unsigned backtrack_level) {
        bool is_first = !m_cuber;
        if (is_first) {
            m_cuber = alloc(lookahead, *this);
        }
        lbool result = m_cuber->cube(vars, lits, backtrack_level);
        m_cuber->update_cube_statistics(m_aux_stats);
        switch (result) {
        case l_false:
            dealloc(m_cuber);
            m_cuber = nullptr;
            if (is_first) {
                pop_to_base_level();
                set_conflict();
            }
            break;
        case l_true: {
            lits.reset();
            pop_to_base_level();
            model const& mdl = m_cuber->get_model();
            for (bool_var v = 0; v < mdl.size(); ++v) {
                if (value(v) != l_undef) {
                    continue;
                }
                literal l(v, false);
                if (mdl[v] != l_true) l.neg();
                if (inconsistent())
                    return l_undef;
                push();
                assign_core(l, justification(scope_lvl()));
                propagate(false);
            }
            mk_model();
            break;
        }
        default:
            break;
        }
        return result;
    }


    // -----------------------
    //
    // Search
    //
    // -----------------------
    lbool solver::check(unsigned num_lits, literal const* lits) {
        init_reason_unknown();
        pop_to_base_level();
        m_stats.m_units = init_trail_size();
        IF_VERBOSE(2, verbose_stream() << "(sat.solver)\n";);
        SASSERT(at_base_lvl());

        if (m_config.m_ddfw_search) {
            m_cleaner(true);
            return do_ddfw_search(num_lits, lits);
        }
        if (m_config.m_prob_search) {
            m_cleaner(true);
            return do_prob_search(num_lits, lits);
        }
        if (m_config.m_local_search) {
            m_cleaner(true);
            return do_local_search(num_lits, lits);
        }
        if ((m_config.m_num_threads > 1 || m_config.m_local_search_threads > 0 || 
             m_config.m_ddfw_threads > 0) && !m_par && !m_ext) {
            SASSERT(scope_lvl() == 0);
            return check_par(num_lits, lits);
        }
        flet<bool> _searching(m_searching, true);
        m_clone = nullptr;
        if (m_mc.empty() && gparams::get_ref().get_bool("model_validate", false)) {
            m_clone = alloc(solver, m_params, m_rlimit);
            m_clone->copy(*this);
            m_clone->set_extension(nullptr);
        }
        try {
            init_search();
            if (check_inconsistent()) return l_false;
            propagate(false);
            if (check_inconsistent()) return l_false;
            init_assumptions(num_lits, lits);
            propagate(false);
            if (check_inconsistent()) return l_false;
            if (m_config.m_force_cleanup) do_cleanup(true);
            TRACE("sat", display(tout););

            if (m_config.m_gc_burst) {
                // force gc
                m_conflicts_since_gc = m_gc_threshold + 1;
                do_gc();
            }

            if (m_config.m_enable_pre_simplify) {
                do_simplify();
                if (check_inconsistent()) return l_false;
            }

            if (m_config.m_max_conflicts == 0) {
                IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-conflicts = 0\")\n";);
                TRACE("sat", display(tout); m_mc.display(tout););
                return l_undef;
            }

            log_stats();
            if (m_config.m_max_conflicts > 0 && m_config.m_burst_search > 0) {               
                m_restart_threshold = m_config.m_burst_search;
                lbool r = bounded_search();
                log_stats();
                if (r != l_undef) 
                    return r;
                
                pop_reinit(scope_lvl());
                m_conflicts_since_restart = 0;
                m_restart_threshold = m_config.m_restart_initial;
            }

            lbool is_sat = search();
            log_stats();
            return is_sat;
        }
        catch (const abort_solver &) {
            m_reason_unknown = "sat.giveup";
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort giveup\")\n";);
            return l_undef;
        }
    }

    bool solver::should_cancel() {
        if (limit_reached() || memory_exceeded()) {
            return true;
        }
        if (m_config.m_restart_max <= m_restarts) {
            m_reason_unknown = "sat.max.restarts";
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-restarts\")\n";);
            return true;
        }
        if (m_config.m_inprocess_max <= m_simplifications) {
            m_reason_unknown = "sat.max.inprocess";
            IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-inprocess\")\n";);
            return true;
        }
        if (reached_max_conflicts()) {
            return true;
        }
        return false;
    }

    enum par_exception_kind {
        DEFAULT_EX,
        ERROR_EX
    };

    lbool solver::invoke_local_search(unsigned num_lits, literal const* lits) {
        literal_vector _lits(num_lits, lits);
        for (literal lit : m_user_scope_literals) _lits.push_back(~lit);
        struct scoped_ls {
            solver& s;
            scoped_ls(solver& s): s(s) {}
            ~scoped_ls() { 
                dealloc(s.m_local_search); 
                s.m_local_search = nullptr; 
            }
        };
        scoped_ls _ls(*this);
        if (inconsistent()) 
            return l_false;
        scoped_limits scoped_rl(rlimit());
        SASSERT(m_local_search);
        m_local_search->add(*this);
        m_local_search->updt_params(m_params);
        scoped_rl.push_child(&(m_local_search->rlimit()));
        lbool r = m_local_search->check(_lits.size(), _lits.data(), nullptr);
        if (r == l_true) {
            m_model = m_local_search->get_model();
            m_model_is_current = true;
        }
        return r;
    }

    lbool solver::do_local_search(unsigned num_lits, literal const* lits) {
        SASSERT(!m_local_search);
        m_local_search = alloc(local_search);
        return invoke_local_search(num_lits, lits);
    }

    lbool solver::do_ddfw_search(unsigned num_lits, literal const* lits) {
        if (m_ext) return l_undef;
        SASSERT(!m_local_search);
        m_local_search = alloc(ddfw);
        return invoke_local_search(num_lits, lits);
    }

    lbool solver::do_prob_search(unsigned num_lits, literal const* lits) {
        if (m_ext) return l_undef;
        if (num_lits > 0 || !m_user_scope_literals.empty()) return l_undef;
        SASSERT(!m_local_search);
        m_local_search = alloc(prob);
        return invoke_local_search(num_lits, lits);
    }

#ifdef SINGLE_THREAD
    lbool solver::check_par(unsigned num_lits, literal const* lits) {
        return l_undef;
    }
#else
    lbool solver::check_par(unsigned num_lits, literal const* lits) {
        if (!rlimit().inc()) {
            return l_undef;
        }
        if (m_ext)
            return l_undef;

        scoped_ptr_vector<i_local_search> ls;
        scoped_ptr_vector<solver> uw;
        int num_extra_solvers = m_config.m_num_threads - 1;
        int num_local_search  = static_cast<int>(m_config.m_local_search_threads);
        int num_ddfw      = m_ext ? 0 : static_cast<int>(m_config.m_ddfw_threads);
        int num_threads = num_extra_solvers + 1 + num_local_search + num_ddfw;        
        for (int i = 0; i < num_local_search; ++i) {
            local_search* l = alloc(local_search);
            l->updt_params(m_params);
            l->add(*this);
            l->set_seed(m_config.m_random_seed + i);
            ls.push_back(l);
        }

        vector<reslimit> lims(num_ddfw);            
        // set up ddfw search
        for (int i = 0; i < num_ddfw; ++i) {
            ddfw* d = alloc(ddfw);
            d->updt_params(m_params);
            d->set_seed(m_config.m_random_seed + i);
            d->add(*this);
            ls.push_back(d);
        }
        int local_search_offset = num_extra_solvers;
        int main_solver_offset = num_extra_solvers + num_local_search + num_ddfw;

#define IS_AUX_SOLVER(i)   (0 <= i && i < num_extra_solvers)
#define IS_LOCAL_SEARCH(i) (local_search_offset <= i && i < main_solver_offset)
#define IS_MAIN_SOLVER(i)  (i == main_solver_offset)

        sat::parallel par(*this);
        par.reserve(num_threads, 1 << 12);
        par.init_solvers(*this, num_extra_solvers);
        for (unsigned i = 0; i < ls.size(); ++i) {
            par.push_child(ls[i]->rlimit());
        }
        for (reslimit& rl : lims) {
            par.push_child(rl);
        }
        for (unsigned i = 0; i < uw.size(); ++i) {
            uw[i]->set_par(&par, 0);
        }
        int finished_id = -1;
        std::string        ex_msg;
        par_exception_kind ex_kind = DEFAULT_EX;
        unsigned error_code = 0;
        lbool result = l_undef;
        bool canceled = false;
        std::mutex mux;

        auto worker_thread = [&](int i) {
            try {
                lbool r = l_undef;
                if (IS_AUX_SOLVER(i)) {
                    r = par.get_solver(i).check(num_lits, lits);
                }
                else if (IS_LOCAL_SEARCH(i)) {
                    r = ls[i-local_search_offset]->check(num_lits, lits, &par);
                }
                else {
                    r = check(num_lits, lits);
                }
                bool first = false;
                {
                    std::lock_guard<std::mutex> lock(mux);
                    if (finished_id == -1) {
                        finished_id = i;
                        first = true;
                        result = r;
                    }
                }
                if (first) {
                    for (unsigned j = 0; j < ls.size(); ++j) {
                        ls[j]->rlimit().cancel();
                    }
                    for (auto& rl : lims) {
                        rl.cancel();
                    }
                    for (int j = 0; j < num_extra_solvers; ++j) {
                        if (i != j) {
                            par.cancel_solver(j);
                        }
                    }
                    if (!IS_MAIN_SOLVER(i)) {
                        canceled = !rlimit().inc();
                        if (!canceled) {
                            rlimit().cancel();
                        }
                    }
                }
            }
            catch (z3_error & err) {
                error_code = err.error_code();
                ex_kind = ERROR_EX;                
            }
            catch (z3_exception & ex) {
                ex_msg = ex.msg();
                ex_kind = DEFAULT_EX;    
            }
        };

        if (!rlimit().inc()) {
            set_par(nullptr, 0);
            return l_undef;
        }

        vector<std::thread> threads(num_threads);
        for (int i = 0; i < num_threads; ++i) {
            threads[i] = std::thread([&, i]() { worker_thread(i); });
        }
        for (auto & th : threads) {
            th.join();
        }
        
        if (IS_AUX_SOLVER(finished_id)) {
            m_stats = par.get_solver(finished_id).m_stats;
        }
        if (result == l_true && IS_AUX_SOLVER(finished_id)) {
            set_model(par.get_solver(finished_id).get_model(), true);
        }
        else if (result == l_false && IS_AUX_SOLVER(finished_id)) {
            m_core.reset();
            m_core.append(par.get_solver(finished_id).get_core());
        }
        if (result == l_true && IS_LOCAL_SEARCH(finished_id)) {
            set_model(ls[finished_id - local_search_offset]->get_model(), true);
        }
        if (!canceled) {
            rlimit().reset_cancel();
        }
        set_par(nullptr, 0);
        ls.reset();
        uw.reset();
        if (finished_id == -1) {
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            default: throw default_exception(std::move(ex_msg));
            }
        }
        return result;

    }
#endif

    /*
      \brief import lemmas/units from parallel sat solvers.
     */
    void solver::exchange_par() {
        if (m_par && at_base_lvl() && m_config.m_num_threads > 1) m_par->get_clauses(*this);
        if (m_par && at_base_lvl() && m_config.m_num_threads > 1) {
            // SASSERT(scope_lvl() == search_lvl());
            // TBD: import also dependencies of assumptions.
            unsigned sz = init_trail_size();
            unsigned num_in = 0, num_out = 0;
            literal_vector in, out;
            for (unsigned i = m_par_limit_out; i < sz; ++i) {
                literal lit = m_trail[i];
                if (lit.var() < m_par_num_vars) {
                    ++num_out;
                    out.push_back(lit);
                }
            }
            m_par_limit_out = sz;
            m_par->exchange(*this, out, m_par_limit_in, in);
            for (unsigned i = 0; !inconsistent() && i < in.size(); ++i) {
                literal lit = in[i];
                SASSERT(lit.var() < m_par_num_vars);
                if (lvl(lit.var()) != 0 || value(lit) != l_true) {
                    ++num_in;
                    assign_unit(lit);
                }
            }
            if (num_in > 0 || num_out > 0) {
                IF_VERBOSE(2, verbose_stream() << "(sat-sync out: " << num_out << " in: " << num_in << ")\n";);
            }
        }
    }

    void solver::set_par(parallel* p, unsigned id) {
        m_par = p;
        m_par_num_vars = num_vars();
        m_par_limit_in = 0;
        m_par_limit_out = 0;
        m_par_id = id; 
        m_par_syncing_clauses = false;
    }

    bool_var solver::next_var() {
        bool_var next;

        if (m_rand() < static_cast<int>(m_config.m_random_freq * random_gen::max_value())) {
            if (num_vars() == 0)
                return null_bool_var;
            next = m_rand() % num_vars();
            TRACE("random_split", tout << "next: " << next << " value(next): " << value(next) << "\n";);
            if (value(next) == l_undef && !was_eliminated(next))
                return next;
        }

        while (!m_case_split_queue.empty()) {
            if (m_config.m_anti_exploration) {
                next = m_case_split_queue.min_var();
                auto age = m_stats.m_conflict - m_canceled[next];
                while (age > 0) {
                    set_activity(next, static_cast<unsigned>(m_activity[next] * pow(0.95, static_cast<double>(age))));
                    m_canceled[next] = m_stats.m_conflict;
                    next = m_case_split_queue.min_var();
                    age = m_stats.m_conflict - m_canceled[next];                    
                }
            }
            next = m_case_split_queue.next_var();
            if (value(next) == l_undef && !was_eliminated(next))
                return next;
        }

        return null_bool_var;
    }

    bool solver::decide() {
        bool_var next = next_var();
        if (next == null_bool_var)
            return false;
        push();
        m_stats.m_decision++;
        lbool lphase = m_ext ? m_ext->get_phase(next) : l_undef;
        bool phase = lphase == l_true;

        if (lphase == l_undef) {
            switch (m_config.m_phase) {
            case PS_ALWAYS_TRUE:
                phase = true;
                break;
            case PS_ALWAYS_FALSE:
                phase = false;
                break;
            case PS_BASIC_CACHING:
                phase = m_phase[next];
                break;
            case PS_FROZEN:
                phase = m_best_phase[next];
                break;
            case PS_SAT_CACHING:
                if (m_search_state == s_unsat) {
                    phase = m_phase[next];
                }
                else {
                    phase = m_best_phase[next];
                }
                break;
            case PS_RANDOM:
                phase = (m_rand() % 2) == 0;
                break;
            default:
                UNREACHABLE();
                phase = false;
                break;
            }
        }

        literal next_lit(next, !phase);
        TRACE("sat_decide", tout << scope_lvl() << ": next-case-split: " << next_lit << "\n";);
        assign_scoped(next_lit);
        return true;
    }

    lbool solver::bounded_search() {
        flet<bool> _disable_simplify(m_simplify_enabled, false);
        flet<bool> _restart_enabled(m_restart_enabled, false);
        return search();
    }

    lbool solver::basic_search() {
        lbool is_sat = l_undef;
        while (is_sat == l_undef && !should_cancel()) {
            if (inconsistent()) is_sat = resolve_conflict_core();
            else if (should_propagate()) propagate(true);
            else if (do_cleanup(false)) continue;
            else if (should_gc()) do_gc();
            else if (should_rephase()) do_rephase();
            else if (should_restart()) { if (!m_restart_enabled) return l_undef; do_restart(!m_config.m_restart_fast); }
            else if (should_simplify()) do_simplify();
            else if (!decide()) is_sat = final_check();
        }
        return is_sat;
    }

    lbool solver::search() {
        if (!m_ext || !m_ext->tracking_assumptions())
            return basic_search();
        while (true) {
            pop_to_base_level();
            reinit_assumptions();
            lbool r = basic_search();
            if (r != l_false) 
                return r;
            if (!m_ext->should_research(m_core))
                return r;
        }
    }

    bool solver::should_propagate() const {        
        return !inconsistent() && m_qhead < m_trail.size();
    }

    lbool solver::final_check() {
        if (m_ext) {
            switch (m_ext->check()) {
            case check_result::CR_DONE:
                mk_model();
                return l_true;
            case check_result::CR_CONTINUE:
                break;
            case check_result::CR_GIVEUP:
                throw abort_solver();
            }
            return l_undef;
        }
        else {
            mk_model();
            return l_true;
        }
    }


    bool solver::check_inconsistent() {
        if (inconsistent()) {
            if (tracking_assumptions() && at_search_lvl())
                resolve_conflict();
            else if (m_config.m_drat && at_base_lvl())
                resolve_conflict();
            return true;
        }
        else {
            return false;
        }
    }    


    void solver::init_assumptions(unsigned num_lits, literal const* lits) {
        if (num_lits == 0 && m_user_scope_literals.empty()) {
            return;
        }

        SASSERT(at_base_lvl());
        reset_assumptions();
        push();

        propagate(false);
        if (inconsistent()) {
            return;
        }

        TRACE("sat",
              tout << literal_vector(num_lits, lits) << "\n";
              if (!m_user_scope_literals.empty()) {
                  tout << "user literals: " << m_user_scope_literals << "\n";
              }
              m_mc.display(tout);
              );

        for (unsigned i = 0; !inconsistent() && i < m_user_scope_literals.size(); ++i) {
            literal nlit = ~m_user_scope_literals[i];
            assign_scoped(nlit);
        }

        for (unsigned i = 0; !inconsistent() && i < num_lits; ++i) {
            literal lit = lits[i];
            set_external(lit.var());
            SASSERT(is_external(lit.var()));
            add_assumption(lit);
            assign_scoped(lit);
        }

        m_search_lvl = scope_lvl(); 
        SASSERT(m_search_lvl == 1);
    }

    void solver::update_min_core() {
        if (!m_min_core_valid || m_core.size() < m_min_core.size()) {
            m_min_core.reset();
            m_min_core.append(m_core);
            m_min_core_valid = true;
        }
    }

    void solver::reset_assumptions() {
        m_assumptions.reset();
        m_assumption_set.reset();
        m_ext_assumption_set.reset();
    }

    void solver::add_assumption(literal lit) {
        m_assumption_set.insert(lit);
        m_assumptions.push_back(lit);
        set_external(lit.var());
    }

    void solver::reassert_min_core() {
        SASSERT(m_min_core_valid);
        pop_to_base_level();
        push();
        reset_assumptions();
        TRACE("sat", tout << "reassert: " << m_min_core << "\n";);
        for (literal lit : m_min_core) {
            SASSERT(is_external(lit.var()));
            add_assumption(lit);
            assign_scoped(lit);
        }
        propagate(false);
        SASSERT(inconsistent());
    }

    void solver::reinit_assumptions() {
        if (tracking_assumptions() && at_base_lvl() && !inconsistent()) {
            TRACE("sat", tout << "assumptions: " << m_assumptions << " user scopes: " << m_user_scope_literals << "\n";);
            if (!propagate(false)) return;
            push();
            for (literal lit : m_user_scope_literals) {
                if (inconsistent()) break;
                assign_scoped(~lit);
            }
            for (literal lit : m_assumptions) {
                if (inconsistent()) break;
                assign_scoped(lit);
            }
            init_ext_assumptions();

            if (!inconsistent()) 
                propagate(false);
            TRACE("sat",
                  tout << "consistent: " << !inconsistent() << "\n";
                  for (literal a : m_assumptions) {
                      index_set s;
                      if (m_antecedents.find(a.var(), s)) {
                          tout << a << ": "; display_index_set(tout, s) << "\n";
                      }
                  }
                  for (literal lit : m_user_scope_literals) {
                      tout << "user " << lit << "\n"; 
                  }
                  );
        }
    }

    void solver::init_ext_assumptions() {
        if (m_ext && m_ext->tracking_assumptions()) {
            m_ext_assumption_set.reset();
            unsigned trail_size = m_trail.size();
            if (!inconsistent())
                m_ext->add_assumptions();
            for (unsigned i = trail_size; i < m_trail.size(); ++i)
                m_ext_assumption_set.insert(m_trail[i]);
        }
    }

    bool solver::tracking_assumptions() const {
        return !m_assumptions.empty() || !m_user_scope_literals.empty() || (m_ext && m_ext->tracking_assumptions());
    }

    bool solver::is_assumption(literal l) const {
        return tracking_assumptions() && (m_assumption_set.contains(l) || m_ext_assumption_set.contains(l));
    }

    void solver::set_activity(bool_var v, unsigned new_act) {
        unsigned old_act = m_activity[v];
        m_activity[v] = new_act; 
        if (!was_eliminated(v) && value(v) == l_undef && new_act != old_act) {
            m_case_split_queue.activity_changed_eh(v, new_act > old_act);
        }
    }

    bool solver::is_assumption(bool_var v) const {
        return is_assumption(literal(v, false)) || is_assumption(literal(v, true));
    }

    void solver::init_search() {
        m_model_is_current        = false;
        m_phase_counter           = 0;
        m_search_state            = s_unsat;
        m_search_unsat_conflicts  = m_config.m_search_unsat_conflicts;
        m_search_sat_conflicts    = m_config.m_search_sat_conflicts;
        m_search_next_toggle      = m_search_unsat_conflicts;
        m_best_phase_size         = 0;
        m_rephase_lim             = 0;
        m_rephase_inc             = 0;
        m_reorder_lim             = m_config.m_reorder_base;
        m_reorder_inc             = 0;
        m_conflicts_since_restart = 0;
        m_force_conflict_analysis = false;
        m_restart_threshold       = m_config.m_restart_initial;
        m_luby_idx                = 1;
        m_gc_threshold            = m_config.m_gc_initial;
        m_defrag_threshold        = 2;
        m_restarts                = 0;
        m_last_position_log       = 0;
        m_restart_logs            = 0;
        m_simplifications         = 0;
        m_conflicts_since_init    = 0;
        m_next_simplify           = m_config.m_simplify_delay;
        m_min_d_tk                = 1.0;
        m_search_lvl              = 0;
        if (m_learned.size() <= 2*m_clauses.size())
            m_conflicts_since_gc      = 0;
        m_restart_next_out        = 0;
        m_asymm_branch.init_search();
        m_stopwatch.reset();
        m_stopwatch.start();
        m_core.reset();
        m_min_core_valid = false;
        m_min_core.reset();
        m_simplifier.init_search();
        m_mc.init_search(*this);
        if (m_ext)
            m_ext->init_search();
        TRACE("sat", display(tout););
    }

    bool solver::should_simplify() const {
        return m_conflicts_since_init >= m_next_simplify && m_simplify_enabled;
    }
    /**
       \brief Apply all simplifications.
    */
    void solver::do_simplify() {
        if (!should_simplify()) {
            return;
        }
        log_stats();
        m_simplifications++;

        TRACE("sat", tout << "simplify\n";);

        pop(scope_lvl());
        struct report {
            solver&   s;
            stopwatch m_watch;
            report(solver& s):s(s) { 
                m_watch.start(); 
                s.log_stats();
                IF_VERBOSE(2, verbose_stream() << "(sat.simplify :simplifications " << s.m_simplifications << ")\n";);
            }
            ~report() { 
                m_watch.stop(); 
                s.log_stats();
            }
        };
        report _rprt(*this);
        SASSERT(at_base_lvl());

        m_cleaner(m_config.m_force_cleanup);
        CASSERT("sat_simplify_bug", check_invariant());

        m_scc();
        CASSERT("sat_simplify_bug", check_invariant());

        if (m_ext) {
            m_ext->pre_simplify();
        }
      
        m_simplifier(false);

        CASSERT("sat_simplify_bug", check_invariant());
        CASSERT("sat_missed_prop", check_missed_propagation());
        if (!m_learned.empty()) {
            m_simplifier(true);
            CASSERT("sat_missed_prop", check_missed_propagation());
            CASSERT("sat_simplify_bug", check_invariant());
        }
        sort_watch_lits();
        CASSERT("sat_simplify_bug", check_invariant());

        m_probing();
        CASSERT("sat_missed_prop", check_missed_propagation());
        CASSERT("sat_simplify_bug", check_invariant());
        m_asymm_branch(false);

        CASSERT("sat_missed_prop", check_missed_propagation());
        CASSERT("sat_simplify_bug", check_invariant());
        if (m_ext) {
            m_ext->clauses_modifed();
            m_ext->simplify();
        }
        if (m_config.m_lookahead_simplify && !m_ext) {
            lookahead lh(*this);
            lh.simplify(true);
            lh.collect_statistics(m_aux_stats);
        }

        reinit_assumptions();
        if (inconsistent()) return;

        if (m_next_simplify == 0) {
            m_next_simplify = m_config.m_next_simplify1;
        }
        else {
            m_next_simplify = static_cast<unsigned>(m_conflicts_since_init * m_config.m_simplify_mult2);
            if (m_next_simplify > m_conflicts_since_init + m_config.m_simplify_max)
                m_next_simplify = m_conflicts_since_init + m_config.m_simplify_max;
        }

        if (m_par) {
            m_par->from_solver(*this);
            if (m_par->to_solver(*this)) {
                m_activity_inc = 128;
            }
        }

        if (m_config.m_binspr && !inconsistent()) {
            m_binspr();
        }

        if (m_config.m_anf_simplify && m_simplifications > m_config.m_anf_delay && !inconsistent()) {
            anf_simplifier anf(*this);
            anf_simplifier::config cfg;
            cfg.m_enable_exlin = m_config.m_anf_exlin;
            anf();
            anf.collect_statistics(m_aux_stats);
            // TBD: throttle anf_delay based on yield
        }
        
        if (m_cut_simplifier && m_simplifications > m_config.m_cut_delay && !inconsistent()) {
            (*m_cut_simplifier)();
        }

        if (m_config.m_inprocess_out.is_non_empty_string()) {
            std::ofstream fout(m_config.m_inprocess_out.str());
            if (fout) {
                display_dimacs(fout);
            }
            throw solver_exception("output generated");
        }
    }

    bool solver::set_root(literal l, literal r) {
        return !m_ext || m_ext->set_root(l, r);
    }

    void solver::flush_roots() {
        if (m_ext) m_ext->flush_roots();
    }

    void solver::sort_watch_lits() {
        for (watch_list & wlist : m_watches) {
            std::stable_sort(wlist.begin(), wlist.end(), watched_lt());
        }
    }

    void solver::set_model(model const& mdl, bool is_current) {
        m_model.reset();
        m_model.append(mdl);
        m_model_is_current = is_current;
    }

    void solver::mk_model() {
        m_model.reset();
        m_model_is_current = true;
        unsigned num = num_vars();
        m_model.resize(num, l_undef);
        for (bool_var v = 0; v < num; v++) {
            if (!was_eliminated(v)) {
                m_model[v] = value(v);
                m_phase[v] = value(v) == l_true;
                m_best_phase[v] = value(v) == l_true;
            }
        }
        TRACE("sat_mc_bug", m_mc.display(tout););

#if 0
        IF_VERBOSE(2, for (bool_var v = 0; v < num; v++) verbose_stream() << v << ": " << m_model[v] << "\n";);
        for (auto p : big::s_del_bin) {
            if (value(p.first) != l_true && value(p.second) != l_true) {
                IF_VERBOSE(2, verbose_stream() << "binary violation: " << p.first << " " << p.second << "\n");
            }
        }
#endif

        if (m_clone) {
            IF_VERBOSE(10, verbose_stream() << "\"checking model\"\n";);
            if (!check_clauses(m_model)) {
                throw solver_exception("check model failed");
            }
        }
        
        if (m_config.m_drat) {
            m_drat.check_model(m_model);
        }

        m_mc(m_model);

        if (m_clone && !check_clauses(m_model)) {
            IF_VERBOSE(1, verbose_stream() << "failure checking clauses on transformed model\n";);
            IF_VERBOSE(10, m_mc.display(verbose_stream()));
            IF_VERBOSE(1, for (bool_var v = 0; v < num; v++) verbose_stream() << v << ": " << m_model[v] << "\n";);

            throw solver_exception("check model failed");
        }

        TRACE("sat", for (bool_var v = 0; v < num; v++) tout << v << ": " << m_model[v] << "\n";);

        if (m_clone) {
            IF_VERBOSE(1, verbose_stream() << "\"checking model (on original set of clauses)\"\n";);
            if (!m_clone->check_model(m_model)) {
                IF_VERBOSE(1, m_mc.display(verbose_stream()));
                IF_VERBOSE(1, display_units(verbose_stream()));
                throw solver_exception("check model failed (for cloned solver)");
            }
        }
    }

    bool solver::check_clauses(model const& m) const {
        bool ok = true;
        for (clause const* cp : m_clauses) {
            clause const & c = *cp;
            if (!c.satisfied_by(m)) {
                IF_VERBOSE(1, verbose_stream() << "failed clause " << c.id() << ": " << c << "\n";);
                TRACE("sat", tout << "failed: " << c << "\n";
                      tout << "assumptions: " << m_assumptions << "\n";
                      tout << "trail: " << m_trail << "\n";
                      tout << "model: " << m << "\n";
                      m_mc.display(tout);
                      );
                for (literal l : c) {
                    if (was_eliminated(l.var())) IF_VERBOSE(1, verbose_stream() << "eliminated: " << l << "\n";);
                }
                ok = false;
            }
        }
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_watches) {
            literal l = ~to_literal(l_idx);
            if (value_at(l, m) != l_true) {
                for (watched const& w : wlist) {
                    if (!w.is_binary_non_learned_clause())
                        continue;
                    literal l2 = w.get_literal();
                    if (l.index() > l2.index()) 
                        continue;
                    if (value_at(l2, m) != l_true) {
                        IF_VERBOSE(1, verbose_stream() << "failed binary: " << l << " := " << value_at(l, m) << " " << l2 <<  " := " << value_at(l2, m) << "\n");
                        IF_VERBOSE(1, verbose_stream() << "elim l1: " << was_eliminated(l.var()) << " elim l2: " << was_eliminated(l2) << "\n");
                        TRACE("sat", m_mc.display(tout << "failed binary: " << l << " " << l2 << "\n"););
                        ok = false;
                    }
                }
            }
            ++l_idx;
        }
        for (literal l : m_assumptions) {
            if (value_at(l, m) != l_true) {
                VERIFY(is_external(l.var()));
                IF_VERBOSE(1, verbose_stream() << "assumption: " << l << " does not model check " << value_at(l, m) << "\n";);
                TRACE("sat",
                      tout << l << " does not model check\n";
                      tout << "trail: " << m_trail << "\n";
                      tout << "model: " << m << "\n";
                      m_mc.display(tout);
                      );
                ok = false;
            }
        }
        if (m_ext && !m_ext->check_model(m)) {
            ok = false;
        }
        return ok;
    }

    bool solver::check_model(model const & m) const {
        bool ok = check_clauses(m);
        if (ok && !m_mc.check_model(m)) {
            ok = false;
            TRACE("sat", tout << "model: " << m << "\n"; m_mc.display(tout););
            IF_VERBOSE(0, verbose_stream() << "model check failed\n");
        }
        return ok;
    }

    bool solver::should_restart() const {
        if (m_conflicts_since_restart <= m_restart_threshold) return false;
        if (scope_lvl() < 2 + search_lvl()) return false;
        if (m_config.m_restart != RS_EMA) return true;
        return 
            m_fast_glue_avg + search_lvl() <= scope_lvl() && 
            m_config.m_restart_margin * m_slow_glue_avg <= m_fast_glue_avg;
    }

    void solver::log_stats() {
        m_restart_logs++;
        
        std::stringstream strm;
        strm << "(sat.stats " << std::setw(6) << m_stats.m_conflict << " " 
             << std::setw(6) << m_stats.m_decision << " "
             << std::setw(4) << m_stats.m_restart 
             << mk_stat(*this)
             << " " << std::setw(6) << std::setprecision(2) << m_stopwatch.get_current_seconds() << ")\n";
        std::string str(strm.str());
        svector<size_t> nums;
        for (size_t i = 0; i < str.size(); ++i) {
            while (i < str.size() && str[i] != ' ') ++i;
            while (i < str.size() && str[i] == ' ') ++i;
            // position of first character after space
            if (i < str.size()) {
                nums.push_back(i);
            }
        }   
        bool same = m_last_positions.size() == nums.size();
        size_t diff = 0;
        for (unsigned i = 0; i < nums.size() && same; ++i) {
            if (m_last_positions[i] > nums[i]) diff += m_last_positions[i] - nums[i];
            if (m_last_positions[i] < nums[i]) diff += nums[i] - m_last_positions[i];
        }
        if (m_last_positions.empty() || 
            m_restart_logs >= 20 + m_last_position_log || 
            (m_restart_logs >= 6 + m_last_position_log && (!same || diff > 3))) {
            m_last_position_log = m_restart_logs;
            //           conflicts          restarts          learned            gc               time
            //                     decisions         clauses            units          memory
            int adjust[9] = { -3,      -3,      -3,      -1,      -3,      -2,   -1,     -2,       -1 };
            char const* tag[9]  = { ":conflicts ", ":decisions ", ":restarts ", ":clauses/bin ", ":learned/bin ", ":units ", ":gc ", ":memory ", ":time" };
            std::stringstream l1, l2;
            l1 << "(sat.stats ";
            l2 << "(sat.stats ";
            size_t p1 = 11, p2 = 11;
            SASSERT(nums.size() == 9);
            for (unsigned i = 0; i < 9 && i < nums.size(); ++i) {
                size_t p = nums[i];
                if (i & 0x1) {
                    // odd positions
                    for (; p2 < p + adjust[i]; ++p2) l2 << " ";
                    p2 += strlen(tag[i]);
                    l2 << tag[i];
                }
                else {
                    // even positions
                    for (; p1 < p + adjust[i]; ++p1) l1 << " ";
                    p1 += strlen(tag[i]);
                    l1 << tag[i];
                }                               
            }
            for (; p1 + 2 < str.size(); ++p1) l1 << " ";            
            for (; p2 + 2 < str.size(); ++p2) l2 << " ";            
            l1 << ")\n";
            l2 << ")\n";
            IF_VERBOSE(1, verbose_stream() << l1.str() << l2.str());
            m_last_positions.reset();
            m_last_positions.append(nums);
        }
        IF_VERBOSE(1, verbose_stream() << str);            
    }

    void solver::do_restart(bool to_base) {        
        m_stats.m_restart++;
        m_restarts++;
        if (m_conflicts_since_init >= m_restart_next_out && get_verbosity_level() >= 1) {
            if (0 == m_restart_next_out) {
                m_restart_next_out = 1;
            }
            else {
                m_restart_next_out = std::min(m_conflicts_since_init + 50000, (3*m_restart_next_out)/2 + 1); 
            }
            log_stats();
        }
        TRACE("sat", tout << "restart " << restart_level(to_base) << "\n";);
        IF_VERBOSE(30, display_status(verbose_stream()););
        TRACE("sat", tout << "restart " << restart_level(to_base) << "\n";);
        pop_reinit(restart_level(to_base));
        set_next_restart();        
    }

    unsigned solver::restart_level(bool to_base) {
        if (to_base || scope_lvl() == search_lvl()) {
            return scope_lvl() - search_lvl();
        }
        else {
            bool_var next = m_case_split_queue.min_var();

            // Implementations of Marijn's idea of reusing the 
            // trail when the next decision literal has lower precedence.
            // pop trail from top
#if 0
            unsigned n = 0;
            do {
                bool_var prev = scope_literal(scope_lvl() - n - 1).var();
                if (m_case_split_queue.more_active(prev, next)) break;                
                ++n;
            }
            while (n < scope_lvl() - search_lvl());
            return n;
#endif
            // pop trail from bottom
            unsigned n = search_lvl();
            for (; n < scope_lvl() && m_case_split_queue.more_active(scope_literal(n).var(), next); ++n) {
            }
            return n - search_lvl();
        }
    }

    void solver::update_activity(bool_var v, double p) {
        unsigned new_act = (unsigned) (num_vars() * m_config.m_activity_scale *  p);
        set_activity(v, new_act);
    }

    void solver::set_next_restart() {
        m_conflicts_since_restart = 0;
        switch (m_config.m_restart) {
        case RS_GEOMETRIC:
            m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_config.m_restart_factor);
            break;
        case RS_LUBY:
            m_luby_idx++;
            m_restart_threshold = m_config.m_restart_initial * get_luby(m_luby_idx);
            break;
        case RS_EMA:
            m_restart_threshold = m_config.m_restart_initial;
            break;
        case RS_STATIC:
            break;
        default:
            UNREACHABLE();
            break;
        }
        CASSERT("sat_restart", check_invariant());
    }


    // -----------------------
    //
    // Conflict resolution
    //
    // -----------------------

    bool solver::resolve_conflict() {
        while (true) {
            lbool r = resolve_conflict_core();
            CASSERT("sat_check_marks", check_marks());
            // after pop, clauses are reinitialized, this may trigger another conflict.
            if (r == l_false)
                return false;
            if (!inconsistent())
                return true;
        }
    }


    lbool solver::resolve_conflict_core() {
        m_conflicts_since_init++;
        m_conflicts_since_restart++;
        m_conflicts_since_gc++;
        m_stats.m_conflict++;
        if (m_step_size > m_config.m_step_size_min) {
            m_step_size -= m_config.m_step_size_dec;
        }

        bool unique_max;
        m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);        
        justification js = m_conflict;

        if (m_conflict_lvl <= 1 && tracking_assumptions()) {
            TRACE("sat", tout << "unsat core\n";);
            resolve_conflict_for_unsat_core();
            return l_false;
        }

        if (m_conflict_lvl == 0) {
            drat_explain_conflict();
            if (m_config.m_drat)
                drat_log_clause(0, nullptr, sat::status::redundant());
            TRACE("sat", tout << "conflict level is 0\n";);
            return l_false;
        }

        // force_conflict_analysis is used instead of relying on normal propagation to assign m_not_l 
        // at the backtracking level. This is the case where the external theories miss propagations
        // that only get triggered after decisions.
        
        if (allow_backtracking() && unique_max && !m_force_conflict_analysis) {
            TRACE("sat", tout << "unique max " << js << " " << m_not_l << "\n";);
            pop_reinit(m_scope_lvl - m_conflict_lvl + 1);
            m_force_conflict_analysis = true;
            ++m_stats.m_backtracks;
            return l_undef;
        }
        m_force_conflict_analysis = false;

        updt_phase_of_vars();

        if (m_ext) {
            switch (m_ext->resolve_conflict()) {
            case l_true:                
                learn_lemma_and_backjump();
                return l_undef;
            case l_undef:
                break;
            case l_false:
                // backjumping was taken care of internally.
                return l_undef;
            }
        }

        m_lemma.reset();

        unsigned idx = skip_literals_above_conflict_level();

        // save space for first uip
        m_lemma.push_back(null_literal);

        TRACE("sat_conflict_detail", 
              tout << "resolve: " << m_not_l << " " 
              << " js: " << js 
              << " idx: " << idx 
              << " trail: " << m_trail.size() 
              << " @" << m_conflict_lvl << "\n";);

        unsigned num_marks = 0;
        literal consequent = null_literal;
        if (m_not_l != null_literal) {
            TRACE("sat_conflict_detail", tout << "not_l: " << m_not_l << "\n";);
            process_antecedent(m_not_l, num_marks);
            consequent = ~m_not_l;
        }

        do {
            TRACE("sat_conflict_detail", tout << "processing consequent: " << consequent << " @" << (consequent==null_literal?m_conflict_lvl:lvl(consequent)) << "\n";
                  tout << "num_marks: " << num_marks << "\n";
                  display_justification(tout, js) << "\n";);

            switch (js.get_kind()) {
            case justification::NONE:
                break;
            case justification::BINARY:
                process_antecedent(~(js.get_literal()), num_marks);
                break;
            case justification::TERNARY:
                process_antecedent(~(js.get_literal1()), num_marks);
                process_antecedent(~(js.get_literal2()), num_marks);
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                unsigned i = 0;
                if (consequent != null_literal) {
                    SASSERT(c[0] == consequent || c[1] == consequent);
                    if (c[0] == consequent) {
                        i = 1;
                    }
                    else {
                        process_antecedent(~c[0], num_marks);
                        i = 2;
                    }
                }
                unsigned sz = c.size();
                for (; i < sz; i++)
                    process_antecedent(~c[i], num_marks);
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                fill_ext_antecedents(consequent, js, false);
                TRACE("sat", tout << "ext antecedents: " << m_ext_antecedents << "\n";);
                for (literal l : m_ext_antecedents) 
                    process_antecedent(l, num_marks);
                
#if 0
                if (m_ext_antecedents.size() <= 1) {
                    for (literal& l : m_ext_antecedents) 
                        l.neg();
                    m_ext_antecedents.push_back(consequent);
                    mk_clause(m_ext_antecedents.size(), m_ext_antecedents.c_ptr(), sat::status::redundant());
                }
#endif
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            
            bool_var c_var;
            while (true) {
                consequent = m_trail[idx];
                c_var = consequent.var();
                if (is_marked(c_var)) {
                    if (lvl(c_var) == m_conflict_lvl) {
                        break;
                    }
                    SASSERT(lvl(c_var) < m_conflict_lvl);
                }
                CTRACE("sat", idx == 0, 
                       for (literal lit : m_trail)
                           if (is_marked(lit.var()))
                               tout << "missed " << lit << "@" << lvl(lit) << "\n";);
                CTRACE("sat", idx == 0, display(tout););
                if (idx == 0)
                    IF_VERBOSE(0, verbose_stream() << "num-conflicts: " << m_stats.m_conflict << "\n");
                VERIFY(idx > 0);
                idx--;
            }
            SASSERT(lvl(consequent) == m_conflict_lvl);
            js             = m_justification[c_var];
            idx--;
            num_marks--;
            reset_mark(c_var);

            TRACE("sat", display_justification(tout << consequent << " ", js) << "\n";);            
        }
        while (num_marks > 0);

        m_lemma[0] = ~consequent;
        learn_lemma_and_backjump();

        return l_undef;
    }

    void solver::learn_lemma_and_backjump() {
        TRACE("sat_lemma", tout << "new lemma size: " << m_lemma.size() << "\n" << m_lemma << "\n";);
        
        if (m_lemma.empty()) {
            pop_reinit(m_scope_lvl);
            mk_clause_core(0, nullptr, sat::status::redundant());
            return;
        }
        
        if (m_config.m_minimize_lemmas) {
            minimize_lemma();
            reset_lemma_var_marks();
            if (m_config.m_dyn_sub_res)
                dyn_sub_res();
            TRACE("sat_lemma", tout << "new lemma (after minimization) size: " << m_lemma.size() << "\n" << m_lemma << "\n";);
        }
        else {
            reset_lemma_var_marks();
        }
        
        unsigned backtrack_lvl = lvl(m_lemma[0]);
        unsigned backjump_lvl  = 0;
        for (unsigned i = m_lemma.size(); i-- > 1;) {
            unsigned level = lvl(m_lemma[i]);
            backjump_lvl = std::max(level, backjump_lvl);
        }    
        // with scope tracking and chronological backtracking, 
        // consequent may not be at highest decision level.
        if (backtrack_lvl < backjump_lvl) {
            backtrack_lvl = backjump_lvl;
            for (unsigned i = m_lemma.size(); i-- > 1;) {
                if (lvl(m_lemma[i]) == backjump_lvl) {
                    TRACE("sat", tout << "swap " << m_lemma[0] << "@" << lvl(m_lemma[0]) << m_lemma[1] << "@" << backjump_lvl << "\n";);
                    std::swap(m_lemma[i], m_lemma[0]);
                    break;
                }
            }
        }
        
        unsigned glue = num_diff_levels(m_lemma.size(), m_lemma.data());        
        m_fast_glue_avg.update(glue);
        m_slow_glue_avg.update(glue);
    
        // compute whether to use backtracking or backjumping
        unsigned num_scopes = m_scope_lvl - backjump_lvl;
        
        if (use_backjumping(num_scopes)) {
            ++m_stats.m_backjumps;
            pop_reinit(num_scopes);
        }
        else {
            TRACE("sat", tout << "backtrack " << (m_scope_lvl - backtrack_lvl + 1) << " scopes\n";);
            ++m_stats.m_backtracks;
            pop_reinit(m_scope_lvl - backtrack_lvl + 1);
        }
        clause * lemma = mk_clause_core(m_lemma.size(), m_lemma.data(), sat::status::redundant());
        if (lemma) {
            lemma->set_glue(glue);
        }
        if (m_par && lemma) {
            m_par->share_clause(*this, *lemma);
        }
        m_lemma.reset();
        TRACE("sat_conflict_detail", tout << "consistent " << (!m_inconsistent) << " scopes: " << scope_lvl() << " backtrack: " << backtrack_lvl << " backjump: " << backjump_lvl << "\n";);
        decay_activity();
        updt_phase_counters();
    }

    bool solver::use_backjumping(unsigned num_scopes) const {
        return 
            num_scopes > 0 && 
            (num_scopes <= m_config.m_backtrack_scopes || !allow_backtracking());
    }

    bool solver::allow_backtracking() const {
        return m_conflicts_since_init > m_config.m_backtrack_init_conflicts;
    }

    void solver::process_antecedent_for_unsat_core(literal antecedent) {
        bool_var var     = antecedent.var();
        SASSERT(var < num_vars());
        TRACE("sat", tout << antecedent << " " << (is_marked(var)?"+":"-") << "\n";);
        if (!is_marked(var)) {
            mark(var);
            m_unmark.push_back(var);
            if (is_assumption(antecedent)) {
                m_core.push_back(antecedent);
            }
        }
    }

    void solver::process_consequent_for_unsat_core(literal consequent, justification const& js) {
        TRACE("sat", tout << "processing consequent: ";
              if (consequent == null_literal) tout << "null\n";
              else tout << consequent << "\n";
              display_justification(tout << "js kind: ", js) << "\n";);
        switch (js.get_kind()) {
        case justification::NONE:
            break;
        case justification::BINARY:
            SASSERT(consequent != null_literal);
            process_antecedent_for_unsat_core(~(js.get_literal()));
            break;
        case justification::TERNARY:
            SASSERT(consequent != null_literal);
            process_antecedent_for_unsat_core(~(js.get_literal1()));
            process_antecedent_for_unsat_core(~(js.get_literal2()));
            break;
        case justification::CLAUSE: {
            clause & c = get_clause(js);
            unsigned i = 0;
            if (consequent != null_literal) {
                SASSERT(c[0] == consequent || c[1] == consequent);
                if (c[0] == consequent) {
                    i = 1;
                }
                else {
                    process_antecedent_for_unsat_core(~c[0]);
                    i = 2;
                }
            }
            unsigned sz = c.size();
            for (; i < sz; i++)
                process_antecedent_for_unsat_core(~c[i]);
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            fill_ext_antecedents(consequent, js, false);
            for (literal l : m_ext_antecedents) {
                process_antecedent_for_unsat_core(l);
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }

    void solver::resolve_conflict_for_unsat_core() {
        TRACE("sat_verbose", display(tout);
              unsigned level = 0;
              for (literal l : m_trail) {
                  if (level != lvl(l)) {
                      level = lvl(l);
                      tout << level << ": ";
                  }
                  tout << l;
                  if (m_mark[l.var()]) {
                      tout << "*";
                  }
                  tout << " ";
              }
              tout << "\n";
              tout << "conflict level: " << m_conflict_lvl << "\n";
              );

        m_core.reset();
        if (!m_config.m_drat && m_conflict_lvl == 0) {
            return;
        }
        SASSERT(m_unmark.empty());
        DEBUG_CODE({
                for (literal lit : m_trail) {
                    SASSERT(!is_marked(lit.var()));
                }});

        unsigned old_size = m_unmark.size();
        int idx = skip_literals_above_conflict_level();

        literal consequent = m_not_l;
        if (m_not_l != null_literal) {
            justification js = m_justification[m_not_l.var()];
            TRACE("sat", tout << "not_l: " << m_not_l << "\n";
                  display_justification(tout, js) << "\n";);

            process_antecedent_for_unsat_core(m_not_l);
            if (is_assumption(~m_not_l)) {
                m_core.push_back(~m_not_l);
            }
            else {
                process_consequent_for_unsat_core(m_not_l, js);
            }
            consequent = ~m_not_l;
        }

        justification js = m_conflict;

        int init_sz = init_trail_size();
        while (true) {
            process_consequent_for_unsat_core(consequent, js);
            while (idx >= init_sz) {
                consequent = m_trail[idx];
                if (is_marked(consequent.var()) && lvl(consequent) == m_conflict_lvl)
                    break;
                idx--;
            }
            if (idx < init_sz) {
                break;
            }
            SASSERT(lvl(consequent) == m_conflict_lvl);
            js = m_justification[consequent.var()];
            idx--;
        }
        reset_unmark(old_size);
        if (m_core.size() > 1) {
            unsigned j = 0;
            for (unsigned i = 0; i < m_core.size(); ++i) {
                if (lvl(m_core[i]) > 0) m_core[j++] = m_core[i];            
            }
            m_core.shrink(j);
        }

        if (m_config.m_core_minimize) {
            if (m_min_core_valid && m_min_core.size() < m_core.size()) {
                IF_VERBOSE(2, verbose_stream() << "(sat.updating core " << m_min_core.size() << " " << m_core.size() << ")\n";);
                m_core.reset();
                m_core.append(m_min_core);
            }
            // TBD:
            // apply optional clause minimization by detecting subsumed literals.
            // initial experiment suggests it has no effect.
            m_mus(); // ignore return value on cancelation.
            set_model(m_mus.get_model(), !m_mus.get_model().empty());
            IF_VERBOSE(2, verbose_stream() << "(sat.core: " << m_core << ")\n";);
        }
    }


    unsigned solver::get_max_lvl(literal not_l, justification js, bool& unique_max) {
        unique_max = true;
        unsigned level = 0;

        if (not_l != null_literal) {
            level = lvl(not_l);            
        }      

        switch (js.get_kind()) {
        case justification::NONE:
            level = std::max(level, js.level());
            return level;
        case justification::BINARY:
            level = update_max_level(js.get_literal(), level, unique_max);
            return level;
        case justification::TERNARY:
            level = update_max_level(js.get_literal1(), level, unique_max);
            level = update_max_level(js.get_literal2(), level, unique_max);
            return level;
        case justification::CLAUSE: 
            for (literal l : get_clause(js)) 
                level = update_max_level(l, level, unique_max);
            return level;
        case justification::EXT_JUSTIFICATION:
            if (not_l != null_literal) 
                not_l.neg();
            fill_ext_antecedents(not_l, js, true);
            for (literal l : m_ext_antecedents) 
                level = update_max_level(l, level, unique_max);
            return level;
        default:
            UNREACHABLE();
            return 0;
        }
    }

    /**
       \brief Skip literals from levels above m_conflict_lvl.
       It returns an index idx such that lvl(m_trail[idx]) <= m_conflict_lvl, and
       for all idx' > idx, lvl(m_trail[idx']) > m_conflict_lvl
    */
    unsigned solver::skip_literals_above_conflict_level() {
        unsigned idx = m_trail.size();
        if (idx == 0) {
            return idx;
        }
        idx--;
        // skip literals from levels above the conflict level
        while (lvl(m_trail[idx]) > m_conflict_lvl) {
            SASSERT(idx > 0);
            idx--;
        }
        return idx;
    }

    void solver::process_antecedent(literal antecedent, unsigned & num_marks) {
        bool_var var     = antecedent.var();
        unsigned var_lvl = lvl(var);
        SASSERT(var < num_vars());
        TRACE("sat_verbose", tout << "process " << var << "@" << var_lvl << " marked " << is_marked(var) << " conflict " << m_conflict_lvl << "\n";);
        if (!is_marked(var) && var_lvl > 0) {
            mark(var);
            switch (m_config.m_branching_heuristic) {
            case BH_VSIDS:
                inc_activity(var);
                break;
            case BH_CHB:
                m_last_conflict[var] = m_stats.m_conflict;
                break;
            default:
                break;
            }
            if (var_lvl == m_conflict_lvl)
                num_marks++;
            else
                m_lemma.push_back(~antecedent);
        }
    }


    /**
       \brief js is an external justification. Collect its antecedents and store at m_ext_antecedents.
    */
    void solver::fill_ext_antecedents(literal consequent, justification js, bool probing) {
        SASSERT(js.is_ext_justification());
        SASSERT(m_ext);
        auto idx = js.get_ext_justification_idx();
        m_ext_antecedents.reset();
        m_ext->get_antecedents(consequent, idx, m_ext_antecedents, probing);
    }

    bool solver::is_two_phase() const {
        return m_config.m_phase == PS_SAT_CACHING;
    }

    bool solver::is_sat_phase() const {
        return is_two_phase() && m_search_state == s_sat;
    }

    void solver::updt_phase_of_vars() {
        if (m_config.m_phase == PS_FROZEN)
            return;
        unsigned from_lvl = m_conflict_lvl;
        unsigned head = from_lvl == 0 ? 0 : m_scopes[from_lvl - 1].m_trail_lim;
        unsigned sz   = m_trail.size();
        for (unsigned i = head; i < sz; i++) {
            bool_var v = m_trail[i].var();
            TRACE("forget_phase", tout << "forgetting phase of v" << v << "\n";);
            m_phase[v] = m_rand() % 2 == 0;
        }
        if (is_sat_phase() && head >= m_best_phase_size) {
            m_best_phase_size = head;
            IF_VERBOSE(12, verbose_stream() << "sticky trail: " << head << "\n");
            for (unsigned i = 0; i < head; ++i) {
                bool_var v = m_trail[i].var();
                m_best_phase[v] = m_phase[v];
            }
        }
    }

    bool solver::should_toggle_search_state() {
        if (m_search_state == s_unsat) {
            m_trail_avg.update(m_trail.size());
        }
        return 
            (m_phase_counter >= m_search_next_toggle) &&
            (m_search_state == s_sat || m_trail.size() > 0.50*m_trail_avg);  
    }

    void solver::do_toggle_search_state() {

        if (is_two_phase()) {
            m_best_phase_size = 0;
            std::swap(m_fast_glue_backup, m_fast_glue_avg);
            std::swap(m_slow_glue_backup, m_slow_glue_avg);
            if (m_search_state == s_sat) {
                m_search_unsat_conflicts += m_config.m_search_unsat_conflicts;   
            }
            else {
                m_search_sat_conflicts += m_config.m_search_sat_conflicts;
            }
        }

        if (m_search_state == s_unsat) {
            m_search_state = s_sat;
            m_search_next_toggle = m_search_sat_conflicts;
        }
        else {
            m_search_state = s_unsat;
            m_search_next_toggle = m_search_unsat_conflicts;
        }

        m_phase_counter = 0;
    }

    bool solver::should_rephase() {
        return m_conflicts_since_init > m_rephase_lim;
    }

    void solver::do_rephase() {
        switch (m_config.m_phase) {
        case PS_ALWAYS_TRUE:
            for (auto& p : m_phase) p = true;
            break;
        case PS_ALWAYS_FALSE:
            for (auto& p : m_phase) p = false;
            break;
        case PS_FROZEN:
            break;
        case PS_BASIC_CACHING:
            switch (m_rephase_lim % 4) {
            case 0:
                for (auto& p : m_phase) p = (m_rand() % 2) == 0;
                break;
            case 1:
                for (auto& p : m_phase) p = false;
                break;
            case 2:
                for (auto& p : m_phase) p = !p;
                break;
            default:
                break;
            }
            break;
        case PS_SAT_CACHING:
            if (m_search_state == s_sat) {
                for (unsigned i = 0; i < m_phase.size(); ++i) {
                    m_phase[i] = m_best_phase[i];
                }
            }
            break;
        case PS_RANDOM:
            for (auto& p : m_phase) p = (m_rand() % 2) == 0;
            break;
        default:
            UNREACHABLE();
            break;
        }
        m_rephase_inc += m_config.m_rephase_base;
        m_rephase_lim += m_rephase_inc;
    }

    bool solver::should_reorder() {
        return m_conflicts_since_init > m_reorder_lim;
    }

    void solver::do_reorder() {
        IF_VERBOSE(1, verbose_stream() << "(reorder)\n");
        m_activity_inc = 128;
        svector<bool_var> vars;
        for (bool_var v = num_vars(); v-- > 0; ) {
            if (!was_eliminated(v) && value(v) == l_undef) {            
                vars.push_back(v);
            }
        }
#if 1
        // 
        //   exp(logits[i]) / sum(exp(logits)) 
        // = 
        //   exp(log(exp(logits[i]) / sum(exp(logits)))) 
        // = 
        //   exp(log(exp(logits[i])) - log(sum(exp(logits)))) 
        // =
        //   exp(logits[i] - lse)
        svector<double> logits(vars.size(), 0.0);
        double itau = m_config.m_reorder_itau;
        double lse = 0;
        double mid = m_rand.max_value()/2;
        double max = 0;
        for (double& f : logits) {
            f = itau * (m_rand() - mid)/mid;
            if (f > max) max = f;
        }
        for (double f : logits) {
            lse += log(f - max);
        }
        lse = max + exp(lse);

        for (unsigned i = 0; i < vars.size(); ++i) {
            update_activity(vars[i], exp(logits[i] - lse));
        }
#else
        shuffle(vars.size(), vars.c_ptr(), m_rand);
        for (bool_var v : vars) {
            update_activity(v, m_rand(10)/10.0);
        }
#endif
        m_reorder_inc += m_config.m_reorder_base;
        m_reorder_lim += m_reorder_inc;
    }

    void solver::updt_phase_counters() {
        m_phase_counter++;
        if (should_toggle_search_state()) {
            do_toggle_search_state();
        }
    }

    /**
       \brief Return the number of different levels in lits.
       All literals in lits must be assigned.
    */
    unsigned solver::num_diff_levels(unsigned num, literal const * lits) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        unsigned r = 0;
        for (unsigned i = 0; i < num; i++) {
            SASSERT(value(lits[i]) != l_undef);
            unsigned lit_lvl = lvl(lits[i]);
            if (!m_diff_levels[lit_lvl]) {
                m_diff_levels[lit_lvl] = true;
                r++;
            }
        }
        // reset m_diff_levels.
        for (unsigned i = 0; i < num; i++)
            m_diff_levels[lvl(lits[i])] = false;
        return r;
    }

    bool solver::num_diff_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        glue = 0;
        unsigned i = 0;
        for (; i < num && glue < max_glue; i++) {
            SASSERT(value(lits[i]) != l_undef);
            unsigned lit_lvl = lvl(lits[i]);
            if (!m_diff_levels[lit_lvl]) {
                m_diff_levels[lit_lvl] = true;
                glue++;
            }
        }       
        // reset m_diff_levels.
        for (; i-- > 0; )
            m_diff_levels[lvl(lits[i])] = false;
        return glue < max_glue;        
    }

    bool solver::num_diff_false_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue) {
        m_diff_levels.reserve(scope_lvl() + 1, false);
        glue = 0;
        unsigned i = 0;
        for (; i < num && glue < max_glue; i++) {
            if (value(lits[i]) == l_false) {
                unsigned lit_lvl = lvl(lits[i]);
                if (!m_diff_levels[lit_lvl]) {
                    m_diff_levels[lit_lvl] = true;
                    glue++;
                }
            }
        }
        // reset m_diff_levels.
        for (; i-- > 0;) {
            literal lit = lits[i];
            if (value(lit) == l_false) {
                VERIFY(lvl(lit) < m_diff_levels.size());
                m_diff_levels[lvl(lit)] = false;
            }
        }
        return glue < max_glue;        
    }


    /**
       \brief Process an antecedent for lemma minimization.
    */
    bool solver::process_antecedent_for_minimization(literal antecedent) {
        bool_var var = antecedent.var();
        unsigned var_lvl = lvl(var);
        if (!is_marked(var) && var_lvl > 0) {
            if (m_lvl_set.may_contain(var_lvl)) {
                mark(var);
                m_unmark.push_back(var);
                m_lemma_min_stack.push_back(antecedent);
            }
            else {
                return false;
            }
        }
        return true;
    }

    /**
       \brief Return true if lit is implied by other marked literals
       and/or literals assigned at the base level.
       The set lvl_set is used as an optimization.
       The idea is to stop the recursive search with a failure
       as soon as we find a literal assigned in a level that is not in lvl_set.
    */
    bool solver::implied_by_marked(literal lit) {
        m_lemma_min_stack.reset();  // avoid recursive function
        m_lemma_min_stack.push_back(lit);
        unsigned old_size = m_unmark.size();

        while (!m_lemma_min_stack.empty()) {
            lit = m_lemma_min_stack.back();
            bool_var var = lit.var();
            m_lemma_min_stack.pop_back();
            justification const& js   = m_justification[var];
            switch(js.get_kind()) {
            case justification::NONE:
                // it is a decision variable from a previous scope level
                if (lvl(var) > 0) {
                    reset_unmark(old_size);
                    return false;
                }
                break;
            case justification::BINARY:
                if (!process_antecedent_for_minimization(~(js.get_literal()))) {
                    reset_unmark(old_size);
                    return false;
                }
                break;
            case justification::TERNARY:
                if (!process_antecedent_for_minimization(~(js.get_literal1())) ||
                    !process_antecedent_for_minimization(~(js.get_literal2()))) {
                    reset_unmark(old_size);
                    return false;
                }
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                unsigned i   = 0;
                if (c[0].var() == var) {
                    i = 1;
                }
                else {
                    SASSERT(c[1].var() == var);
                    if (!process_antecedent_for_minimization(~c[0])) {
                        reset_unmark(old_size);
                        return false;
                    }
                    i = 2;
                }
                unsigned sz = c.size();
                for (; i < sz; i++) {
                    if (!process_antecedent_for_minimization(~c[i])) {
                        reset_unmark(old_size);
                        return false;
                    }
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                literal consequent(var, value(var) == l_false);
                fill_ext_antecedents(consequent, js, false);
                for (literal l : m_ext_antecedents) {
                    if (!process_antecedent_for_minimization(l)) {
                        reset_unmark(old_size);
                        return false;
                    }
                }
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            TRACE("sat_conflict", 
                  display_justification(tout << var << " ",js) << "\n";);
        }
        return true;
    }

    /**
       \brief Restore the size of m_unmark to old_size, and
       unmark variables at positions [old_size, m_unmark.size()).
    */
    void solver::reset_unmark(unsigned old_size) {
        unsigned curr_size = m_unmark.size();
        for(unsigned i = old_size; i < curr_size; i++)
            reset_mark(m_unmark[i]);
        m_unmark.shrink(old_size);
    }

    /**
       \brief Store the levels of the literals at m_lemma in the
       approximated set m_lvl_set.
    */
    void solver::updt_lemma_lvl_set() {
        m_lvl_set.reset();
        for (literal l : m_lemma) 
            m_lvl_set.insert(lvl(l));
    }

    /**
       \brief Minimize lemma using binary resolution
    */
    bool solver::minimize_lemma_binres() {
        SASSERT(!m_lemma.empty());
        SASSERT(m_unmark.empty());
        unsigned sz   = m_lemma.size();
        unsigned num_reduced = 0;
        for (unsigned i = 1; i < sz; ++i) {
            mark_lit(m_lemma[i]);            
        }
        watch_list const& wlist = get_wlist(m_lemma[0]);
        for (watched const& w : wlist) {
            if (w.is_binary_clause() && is_marked_lit(w.get_literal())) {
                unmark_lit(~w.get_literal());
                num_reduced++;
            }
        }
        if (num_reduced > 0) {
            unsigned j = 1;
            for (unsigned i = 1; i < sz; ++i) {
                if (is_marked_lit(m_lemma[i])) {
                    m_lemma[j++] = m_lemma[i];
                    unmark_lit(m_lemma[i]);
                }
            }
            m_lemma.shrink(j);
        }

        return num_reduced > 0;
    }

    /**
       \brief Minimize the number of literals in m_lemma. The main idea is to remove
       literals that are implied by other literals in m_lemma and/or literals
       assigned at level 0.
    */
    bool solver::minimize_lemma() {
        SASSERT(!m_lemma.empty());
        SASSERT(m_unmark.empty());
        updt_lemma_lvl_set();

        unsigned sz   = m_lemma.size();
        unsigned i    = 1; // the first literal is the FUIP
        unsigned j    = 1;
        for (; i < sz; i++) {
            literal l = m_lemma[i];
            if (implied_by_marked(l)) {
                m_unmark.push_back(l.var());
            }
            else {
                m_lemma[j++] = m_lemma[i];
            }
        }

        reset_unmark(0);
        m_lemma.shrink(j);
        m_stats.m_minimized_lits += sz - j;
        return j < sz;
    }

    /**
       \brief Reset the mark of the variables in the current lemma.
    */
    void solver::reset_lemma_var_marks() {
        if (m_config.m_branching_heuristic == BH_VSIDS) {
            update_lrb_reasoned();
        }        
        literal_vector::iterator it  = m_lemma.begin();
        literal_vector::iterator end = m_lemma.end();
        SASSERT(!is_marked((*it).var()));
        ++it;
        for(; it != end; ++it) {
            bool_var var = (*it).var();
            reset_mark(var);
        }
    }

    void solver::update_lrb_reasoned() {
        unsigned sz = m_lemma.size();
        SASSERT(!is_marked(m_lemma[0].var()));
        mark(m_lemma[0].var());
        for (unsigned i = m_lemma.size(); i-- > 0; ) {
            justification js = m_justification[m_lemma[i].var()];
            switch (js.get_kind()) {
            case justification::NONE:
                break;                    
            case justification::BINARY:
                update_lrb_reasoned(js.get_literal());
                break;
            case justification::TERNARY:
                update_lrb_reasoned(js.get_literal1());
                update_lrb_reasoned(js.get_literal2());
                break;
            case justification::CLAUSE: {
                clause & c = get_clause(js);
                for (literal l : c) {
                    update_lrb_reasoned(l);
                }
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                fill_ext_antecedents(~m_lemma[i], js, true);
                for (literal l : m_ext_antecedents) {
                    update_lrb_reasoned(l);
                }
                break;
            }
            }
        }
        reset_mark(m_lemma[0].var());
        for (unsigned i = m_lemma.size(); i-- > sz; ) {
            reset_mark(m_lemma[i].var());
        }
        m_lemma.shrink(sz);
    }

    void solver::update_lrb_reasoned(literal lit) {
        bool_var v = lit.var();
        if (!is_marked(v)) {
            mark(v);
            m_reasoned[v]++;
            inc_activity(v);
            m_lemma.push_back(lit);
        }
    }

    /**
       \brief Apply dynamic subsumption resolution to new lemma.
       Only binary and ternary clauses are used.
    */
    bool solver::dyn_sub_res() {
        unsigned sz = m_lemma.size();
        for (unsigned i = 0; i < sz; i++) {
            mark_lit(m_lemma[i]);
        }

        literal l0 = m_lemma[0];
        // l0 is the FUIP, and we never remove the FUIP.
        //
        // In the following loop, we use unmark_lit(l) to remove a
        // literal from m_lemma.

        for (unsigned i = 0; i < sz; i++) {
            literal l = m_lemma[i];
            if (!is_marked_lit(l))
                continue; // literal was eliminated
            // first use watch lists
            watch_list const & wlist = get_wlist(~l);
            for (watched const& w : wlist) {
                // In this for-loop, the conditions l0 != ~l2 and l0 != ~l3
                // are not really needed if the solver does not miss unit propagations.
                // However, we add them anyway because we don't want to rely on this
                // property of the propagator.
                // For example, if this property is relaxed in the future, then the code
                // without the conditions l0 != ~l2 and l0 != ~l3 may remove the FUIP
                if (w.is_binary_clause()) {
                    literal l2 = w.get_literal();
                    if (is_marked_lit(~l2) && l0 != ~l2) {
                        // eliminate ~l2 from lemma because we have the clause l \/ l2
                        unmark_lit(~l2);
                    }
                }
                else if (w.is_ternary_clause()) {
                    literal l2 = w.get_literal1();
                    literal l3 = w.get_literal2();
                    if (is_marked_lit(l2) && is_marked_lit(~l3) && l0 != ~l3) {
                        // eliminate ~l3 from lemma because we have the clause l \/ l2 \/ l3
                        unmark_lit(~l3);
                    }
                    else if (is_marked_lit(~l2) && is_marked_lit(l3) && l0 != ~l2) {
                        // eliminate ~l2 from lemma because we have the clause l \/ l2 \/ l3
                        unmark_lit(~l2);
                    }
                }
                else {
                    // May miss some binary/ternary clauses, but that is ok.
                    // I sort the watch lists at every simplification round.
                    break;
                }
            }
            // try to use cached implication if available
            literal_vector * implied_lits = m_probing.cached_implied_lits(~l);
            if (implied_lits) {
                for (literal l2 : *implied_lits) {
                    // Here, we must check l0 != ~l2.
                    // l \/ l2 is an implied binary clause.
                    // However, it may have been deduced using a lemma that has been deleted.
                    // For example, consider the following sequence of events:
                    //
                    // 1. Initial clause database:
                    //
                    //    l  \/ ~p1
                    //    p1 \/ ~p2
                    //    p2 \/ ~p3
                    //    p3 \/ ~p4
                    //    q1  \/ q2  \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    q1  \/ ~q2 \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ~q1 \/ q2  \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ~q1 \/ ~q2 \/ p1 \/ p2 \/ p3 \/ p4 \/ l2
                    //    ...
                    //
                    // 2. Now suppose we learned the lemma
                    //
                    //    p1 \/ p2 \/ p3 \/ p4 \/ l2   (*)
                    //
                    // 3. Probing is executed and we notice hat (~l => l2) when we assign l to false.
                    //    That is, l \/ l2 is an implied clause. Note that probing does not add
                    //    this clause to the clause database (there are too many).
                    //
                    // 4. Lemma (*) is deleted (garbage collected).
                    //
                    // 5. l is decided to be false, p1, p2, p3 and p4 are propagated using BCP,
                    //    but l2 is not since the lemma (*) was deleted.
                    //
                    //    Probing module still "knows" that l \/ l2 is valid binary clause
                    //
                    // 6. A new lemma is created where ~l2 is the FUIP and the lemma also contains l.
                    //    If we remove l0 != ~l2 may try to delete the FUIP.
                    if (is_marked_lit(~l2) && l0 != ~l2) {
                        // eliminate ~l2 from lemma because we have the clause l \/ l2
                        unmark_lit(~l2);
                    }
                }
            }
        }

        // can't eliminat FUIP
        SASSERT(is_marked_lit(m_lemma[0]));

        unsigned j = 0;
        for (unsigned i = 0; i < sz; i++) {
            literal l = m_lemma[i];
            if (is_marked_lit(l)) {
                unmark_lit(l);
                m_lemma[j] = l;
                j++;
            }
        }

        m_stats.m_dyn_sub_res += sz - j;

        SASSERT(j >= 1);
        m_lemma.shrink(j);
        return j < sz;
    }


    // -----------------------
    //
    // Backtracking
    //
    // -----------------------
    void solver::push() {
        SASSERT(!inconsistent());
        TRACE("sat_verbose", tout << "q:" << m_qhead << " trail: " << m_trail.size() << "\n";);
        SASSERT(m_qhead == m_trail.size());
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        m_scope_lvl++;
        s.m_trail_lim = m_trail.size();
        s.m_clauses_to_reinit_lim = m_clauses_to_reinit.size();
        s.m_inconsistent = m_inconsistent;
        if (m_ext) {
            m_vars_lim.push(m_active_vars.size());
            m_ext->push();
        }
    }

    void solver::pop_reinit(unsigned num_scopes) {
        pop(num_scopes);
        exchange_par();
        reinit_assumptions();
        m_stats.m_units = init_trail_size();
    }

    void solver::pop_vars(unsigned num_scopes) {
        //integrity_checker check(*this);
        //check.check_reinit_stack();
        m_vars_to_reinit.reset();
        unsigned old_num_vars = m_vars_lim.pop(num_scopes);
        if (old_num_vars == m_active_vars.size())
            return;
        unsigned free_vars_head = m_free_vars.size();
        unsigned sz = m_active_vars.size(), j = old_num_vars;
        unsigned new_lvl = m_scopes.size() - num_scopes;

        gc_reinit_stack(num_scopes);        

        // check.check_reinit_stack();
        init_visited();
        unsigned old_sz = m_scopes[new_lvl].m_clauses_to_reinit_lim;
        for (unsigned i = m_clauses_to_reinit.size(); i-- > old_sz; ) {
            clause_wrapper const& cw = m_clauses_to_reinit[i];
            for (unsigned j = cw.size(); j-- > 0; )
                mark_visited(cw[j].var());
        }
        for (literal lit : m_lemma)
            mark_visited(lit.var());

        auto is_active = [&](bool_var v) {
            return value(v) != l_undef && lvl(v) <= new_lvl;
        };

        for (unsigned i = old_num_vars; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            if (is_visited(v) || is_active(v)) {
                m_vars_to_reinit.push_back(v);
                m_active_vars[j++] = v;
                m_var_scope[v] = new_lvl;
            }
            else {
                set_eliminated(v, true);
                if (!is_external(v) || true) {
                    m_free_vars.push_back(v);                   
                }
            }
        }
        m_active_vars.shrink(j);

        auto cleanup_watch = [&](literal lit) {
            for (auto const& w : get_wlist(lit)) {
                IF_VERBOSE(0, verbose_stream() << "cleanup: " << lit << " " << w.is_binary_clause() << "\n");
            }
        };
        for (unsigned i = m_free_vars.size(); i-- > free_vars_head; ) {
            bool_var v = m_free_vars[i];
            cleanup_watch(literal(v, false));
            cleanup_watch(literal(v, true));
            
        }
        TRACE("sat",
            tout << "clauses to reinit: " << (m_clauses_to_reinit.size() - old_sz) << "\n";
            tout << "new level:         " << new_lvl << "\n";
            tout << "vars to reinit:    " << m_vars_to_reinit << "\n";
            tout << "free vars:         " << bool_var_vector(m_free_vars.size() - free_vars_head, m_free_vars.data() + free_vars_head) << "\n";
            for (unsigned i = m_clauses_to_reinit.size(); i-- > old_sz; )
                tout << "reinit:           " << m_clauses_to_reinit[i] << "\n";
            display(tout););        
    }

    void solver::shrink_vars(unsigned v) {
        unsigned j = 0; 
        for (bool_var w : m_free_vars) 
            if (w < v)
                m_free_vars[j++] = w;
        m_free_vars.shrink(j);

        for (bool_var w = m_justification.size(); w-- > v;) {
            m_case_split_queue.del_var_eh(w);
            m_probing.reset_cache(literal(w, true));
            m_probing.reset_cache(literal(w, false));
        }
        m_watches.shrink(2*v);
        m_assignment.shrink(2*v);
        m_justification.shrink(v);
        m_decision.shrink(v);
        m_eliminated.shrink(v);
        m_external.shrink(v);
        m_var_scope.shrink(v);
        m_touched.shrink(v);
        m_activity.shrink(v);
        m_mark.shrink(v);
        m_lit_mark.shrink(2*v);
        m_phase.shrink(v);
        m_best_phase.shrink(v);
        m_prev_phase.shrink(v);
        m_assigned_since_gc.shrink(v);
        m_simplifier.reset_todos();
    }

    void solver::pop(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        unsigned free_vars_head = m_free_vars.size();
        if (m_ext) {
            pop_vars(num_scopes);
            m_ext->pop(num_scopes);
        }
        SASSERT(num_scopes <= scope_lvl());
        unsigned new_lvl = scope_lvl() - num_scopes;
        scope & s        = m_scopes[new_lvl];
        m_inconsistent   = false; // TBD: use model seems to make this redundant: s.m_inconsistent;
        unassign_vars(s.m_trail_lim, new_lvl);
        for (unsigned i = m_free_vars.size(); i-- > free_vars_head; )
            m_case_split_queue.del_var_eh(m_free_vars[i]);
        m_scope_lvl -= num_scopes;
        reinit_clauses(s.m_clauses_to_reinit_lim);
        m_scopes.shrink(new_lvl);
        if (m_ext) 
            m_ext->pop_reinit();
    }

    void solver::unassign_vars(unsigned old_sz, unsigned new_lvl) {
        SASSERT(old_sz <= m_trail.size());
        SASSERT(m_replay_assign.empty());
        for (unsigned i = m_trail.size(); i-- > old_sz; ) {
            literal l  = m_trail[i];
            bool_var v = l.var();
            if (lvl(v) <= new_lvl) {
                m_replay_assign.push_back(l);
                continue;
            }
            m_assignment[l.index()]    = l_undef;
            m_assignment[(~l).index()] = l_undef;
            SASSERT(value(v) == l_undef);
            m_case_split_queue.unassign_var_eh(v);
            if (m_config.m_anti_exploration) {
                m_canceled[v] = m_stats.m_conflict;
            }
        }
        m_trail.shrink(old_sz);        
        m_qhead = m_trail.size();
        if (!m_replay_assign.empty()) IF_VERBOSE(20, verbose_stream() << "replay assign: " << m_replay_assign.size() << "\n");
        CTRACE("sat", !m_replay_assign.empty(), tout << "replay-assign: " << m_replay_assign << "\n";);
        for (unsigned i = m_replay_assign.size(); i-- > 0; ) {
            literal lit = m_replay_assign[i];
            m_trail.push_back(lit);            
        }
        
        m_replay_assign.reset();
    }

    void solver::reinit_clauses(unsigned old_sz) {
        unsigned sz = m_clauses_to_reinit.size();
        SASSERT(old_sz <= sz);
        unsigned j = old_sz;
        for (unsigned i = old_sz; i < sz; i++) {
            clause_wrapper cw = m_clauses_to_reinit[i];
            bool reinit = false;
            if (cw.is_binary()) {
                if (propagate_bin_clause(cw[0], cw[1]) && !at_base_lvl()) 
                    m_clauses_to_reinit[j++] = cw;
                else if (has_variables_to_reinit(cw[0], cw[1]))
                    m_clauses_to_reinit[j++] = cw;
            }
            else {
                clause & c = *(cw.get_clause());
                if (ENABLE_TERNARY && c.size() == 3) {
                    if (!at_base_lvl() && propagate_ter_clause(c))
                        m_clauses_to_reinit[j++] = cw;                
                    else if (has_variables_to_reinit(c))
                        m_clauses_to_reinit[j++] = cw;
                    else 
                        c.set_reinit_stack(false);
                    continue;
                }
                detach_clause(c);
                attach_clause(c, reinit);
                if (!at_base_lvl() && reinit) 
                    // clause propagated literal, must keep it in the reinit stack.
                    m_clauses_to_reinit[j++] = cw;                
                else if (has_variables_to_reinit(c))
                    m_clauses_to_reinit[j++] = cw;
                else 
                    c.set_reinit_stack(false);                
            }
        }
        m_clauses_to_reinit.shrink(j);
    }

    //
    // All new clauses that are added to the solver
    // are relative to the user-scope literals.
    //

    void solver::user_push() {
        pop_to_base_level();
        m_free_var_freeze.push_back(m_free_vars);
        m_free_vars.reset(); // resetting free_vars forces new variables to be assigned above new_v
        bool_var new_v = mk_var(true, false);
        literal lit = literal(new_v, false);
        m_user_scope_literals.push_back(lit);
        m_cut_simplifier = nullptr; // for simplicity, wipe it out
        if (m_ext)
            m_ext->user_push();
        TRACE("sat", tout << "user_push: " << lit << "\n";);
    }

    void solver::user_pop(unsigned num_scopes) {
        unsigned old_sz = m_user_scope_literals.size() - num_scopes;
        bool_var max_var = m_user_scope_literals[old_sz].var();
        m_user_scope_literals.shrink(old_sz);

        pop_to_base_level();
        if (m_ext)
            m_ext->user_pop(num_scopes);

        gc_vars(max_var);
        TRACE("sat", display(tout););

        m_qhead = 0;
        unsigned j = 0;
        for (bool_var v : m_free_vars) 
            if (v < max_var)
                m_free_vars[j++] = v;
        m_free_vars.shrink(j);
        m_free_vars.append(m_free_var_freeze[old_sz]); 
        m_free_var_freeze.shrink(old_sz);
        scoped_suspend_rlimit _sp(m_rlimit);
        propagate(false);
    }

    void solver::pop_to_base_level() {
        reset_assumptions();
        pop(scope_lvl());
    }

    // -----------------------
    //
    // Misc
    //
    // -----------------------

    void solver::updt_params(params_ref const & p) {
        m_params.append(p);
        m_config.updt_params(p);
        m_simplifier.updt_params(p);
        m_asymm_branch.updt_params(p);
        m_probing.updt_params(p);
        m_scc.updt_params(p);
        m_rand.set_seed(m_config.m_random_seed);
        m_step_size = m_config.m_step_size_init;
        m_drat.updt_config();
        m_fast_glue_avg.set_alpha(m_config.m_fast_glue_avg);
        m_slow_glue_avg.set_alpha(m_config.m_slow_glue_avg);
        m_fast_glue_backup.set_alpha(m_config.m_fast_glue_avg);
        m_slow_glue_backup.set_alpha(m_config.m_slow_glue_avg);
        m_trail_avg.set_alpha(m_config.m_slow_glue_avg);

        if (m_config.m_cut_simplify && !m_cut_simplifier && m_user_scope_literals.empty()) {
            m_cut_simplifier = alloc(cut_simplifier, *this);
        }
    }

    void solver::collect_param_descrs(param_descrs & d) {
        config::collect_param_descrs(d);
        simplifier::collect_param_descrs(d);
        asymm_branch::collect_param_descrs(d);
        probing::collect_param_descrs(d);
        scc::collect_param_descrs(d);
    }

    void solver::collect_statistics(statistics & st) const {
        m_stats.collect_statistics(st);
        m_cleaner.collect_statistics(st);
        m_simplifier.collect_statistics(st);
        m_scc.collect_statistics(st);
        m_asymm_branch.collect_statistics(st);
        m_probing.collect_statistics(st);
        if (m_ext) m_ext->collect_statistics(st);
        if (m_local_search) m_local_search->collect_statistics(st);
        if (m_cut_simplifier) m_cut_simplifier->collect_statistics(st);
        st.copy(m_aux_stats);
    }

    void solver::reset_statistics() {
        m_stats.reset();
        m_cleaner.reset_statistics();
        m_simplifier.reset_statistics();
        m_asymm_branch.reset_statistics();
        m_probing.reset_statistics();
        m_aux_stats.reset();
    }

    // -----------------------
    //
    // Activity related stuff
    //
    // -----------------------

    void solver::rescale_activity() {
        SASSERT(m_config.m_branching_heuristic == BH_VSIDS);
        for (unsigned& act : m_activity) {
            act >>= 14;
        }
        m_activity_inc >>= 14;
    }

    void solver::update_chb_activity(bool is_sat, unsigned qhead) {
        SASSERT(m_config.m_branching_heuristic == BH_CHB);
        double multiplier = m_config.m_reward_offset * (is_sat ? m_config.m_reward_multiplier : 1.0);
        for (unsigned i = qhead; i < m_trail.size(); ++i) {
            auto v = m_trail[i].var();
            auto d = m_stats.m_conflict - m_last_conflict[v] + 1;
            if (d == 0) d = 1;
            auto reward = multiplier / d;            
            auto activity = m_activity[v];
            set_activity(v, static_cast<unsigned>(m_step_size * reward + ((1.0 - m_step_size) * activity)));
        }
    }

    void solver::move_to_front(bool_var b) {
        if (b >= num_vars())
            return;
        bool_var next = m_case_split_queue.min_var();
        auto next_act = m_activity[next];
        set_activity(b, next_act + 1);
    }

    // -----------------------
    //
    // Iterators
    //
    // -----------------------
    void solver::collect_bin_clauses(svector<bin_clause> & r, bool redundant, bool learned_only) const {
        SASSERT(redundant || !learned_only);  
        unsigned sz = m_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; l_idx++) {
            literal l = to_literal(l_idx);
            l.neg();
            for (watched const& w : m_watches[l_idx]) {
                if (!w.is_binary_clause())
                    continue;
                if (!redundant && w.is_learned())
                    continue;
                else if (redundant && learned_only && !w.is_learned()) 
                    continue;
                literal l2 = w.get_literal();
                if (l.index() > l2.index())
                    continue;
                TRACE("cleanup_bug", tout << "collected: " << l << " " << l2 << "\n";);
                r.push_back(bin_clause(l, l2));
            }
        }
    }

    // -----------------------
    //
    // Debugging
    //
    // -----------------------
    bool solver::check_invariant() const {
        if (!m_rlimit.inc()) return true;
        integrity_checker checker(*this);
        VERIFY(checker());
        VERIFY(!m_ext || m_ext->validate());
        return true;
    }

    bool solver::check_marks() const {
        for (bool_var v = 0; v < num_vars(); v++) {
            SASSERT(!is_marked(v));
        }
        return true;
    }

    std::ostream& solver::display_model(std::ostream& out) const {
        unsigned num = num_vars();
        for (bool_var v = 0; v < num; v++) {
            out << v << ": " << m_model[v] << "\n";
        }
        return out;
}

    void solver::display_binary(std::ostream & out) const {
        unsigned sz = m_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; l_idx++) {
            literal l = to_literal(l_idx);
            l.neg();
            for (watched const& w : m_watches[l_idx]) {
                if (!w.is_binary_clause())
                    continue;
                literal l2 = w.get_literal();
                if (l.index() > l2.index())
                    continue;
                out << "(" << l << " " << l2 << ")";
                if (w.is_learned()) out << "*";
                out << "\n";
            }
        }
    }

    void solver::display_units(std::ostream & out) const {
        unsigned level = 0;
        for (literal lit : m_trail) {            
            if (lvl(lit) > level) {
                level = lvl(lit);
                out << level << ": ";
            }
            else {
                out << "    ";
            }
            out << lit << " ";
            if (lvl(lit) < level) {
                out << "@" << lvl(lit) << " ";
            }
            display_justification(out, m_justification[lit.var()]) << "\n";
        }
    }

    void solver::display(std::ostream & out) const {
        out << "(sat\n";
        display_units(out);
        display_binary(out);
        out << m_clauses << m_learned;
        if (m_ext) {
            m_ext->display(out);
        }
        out << ")\n";
    }

    std::ostream& solver::display_justification(std::ostream & out, justification const& js) const {
        switch (js.get_kind()) {
        case justification::NONE:
            out << "none @" << js.level();
            break;
        case justification::BINARY:
            out << "binary " << js.get_literal() << "@" << lvl(js.get_literal());
            break;
        case justification::TERNARY:
            out << "ternary " << js.get_literal1() << "@" << lvl(js.get_literal1()) << " ";
            out << js.get_literal2() << "@" << lvl(js.get_literal2());
            break;
        case justification::CLAUSE: {
            out << "(";
            bool first = true;
            for (literal l : get_clause(js)) {
                if (first) first = false; else out << " ";
                out << l << "@" << lvl(l);
            }
            out << ")";
            break;
        }
        case justification::EXT_JUSTIFICATION:
            if (m_ext) 
                m_ext->display_justification(out << "ext ", js.get_ext_justification_idx());            
            break;
        default:
            break;
        }
        return out;
    }


    unsigned solver::num_clauses() const {
        unsigned num_cls = m_trail.size(); // units;
        unsigned l_idx = 0;
        for (auto const& wl : m_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wl) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index())
                    num_cls++;
            }
        }
        return num_cls + m_clauses.size() + m_learned.size();
    }

    void solver::num_binary(unsigned& given, unsigned& redundant) const {
        given = redundant = 0;
        unsigned l_idx = 0;
        for (auto const& wl : m_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wl) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index()) {
                    if (w.is_learned()) ++redundant; else ++given;
                }
            }
        }
    }

    void solver::display_dimacs(std::ostream & out) const {
        out << "p cnf " << num_vars() << " " << num_clauses() << "\n";
        for (literal lit : m_trail) {
            out << dimacs_lit(lit) << " 0\n";
        }
        unsigned l_idx = 0;
        for (auto const& wlist : m_watches) {
            literal l = ~to_literal(l_idx++);
            for (auto const& w : wlist) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index())
                    out << dimacs_lit(l) << " " << dimacs_lit(w.get_literal()) << " 0\n";
            }
        }
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; i++) {
            clause_vector const & cs = *(vs[i]);
            for (auto cp : cs) {
                for (literal l : *cp) {
                    out << dimacs_lit(l) << " ";
                }
                out << "0\n";
            }
        }
    }

    void solver::display_wcnf(std::ostream & out, unsigned sz, literal const* lits, unsigned const* weights) const {
        unsigned max_weight = 0;
        for (unsigned i = 0; i < sz; ++i) 
            max_weight += weights[i];
        ++max_weight;

        if (m_ext)
            throw default_exception("wcnf is only supported for pure CNF problems");

        out << "p wcnf " << num_vars() << " " << num_clauses() + sz << " " << max_weight << "\n";
        out << "c soft " << sz << "\n";

        for (literal lit : m_trail) 
            out << max_weight << " " << dimacs_lit(lit) << " 0\n";
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_watches) {
            literal l = ~to_literal(l_idx);
            for (watched const& w : wlist) {
                if (w.is_binary_clause() && l.index() < w.get_literal().index())
                    out << max_weight << " " << dimacs_lit(l) << " " << dimacs_lit(w.get_literal()) << " 0\n";
            }
            ++l_idx;
        }
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; i++) {
            clause_vector const & cs = *(vs[i]);
            for (clause const* cp : cs) {
                clause const & c = *cp;
                out << max_weight << " ";
                for (literal l : c)
                    out << dimacs_lit(l) << " ";
                out << "0\n";
            }
        }
        for (unsigned i = 0; i < sz; ++i) {
            out << weights[i] << " " << lits[i] << " 0\n";
        }
        out.flush();
    }

    void solver::display_watches(std::ostream & out, literal lit) const {
        display_watch_list(out << lit << ": ", get_wlist(lit)) << "\n";
    }

    void solver::display_watches(std::ostream & out) const {
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_watches) {
            literal l = to_literal(l_idx++);
            if (!wlist.empty()) 
                display_watch_list(out << l << ": ", wlist) << "\n";
        }
    }

    std::ostream& solver::display_watch_list(std::ostream& out, watch_list const& wl) const {
        return sat::display_watch_list(out, cls_allocator(), wl, m_ext.get());
    }

    void solver::display_assignment(std::ostream & out) const {
        out << m_trail << "\n";
    }

    /**
       \brief Return true, if c is a clause containing one unassigned literal.
    */
    bool solver::is_unit(clause const & c) const {
        bool found_undef = false;
        for (literal l : c) {
            switch (value(l)) {
            case l_undef:
                if (found_undef)
                    return false;
                found_undef = true;
                break;
            case l_true:
                return false;
            case l_false:
                break;
            }
        }
        return found_undef;
    }

    /**
       \brief Return true, if all literals in c are assigned to false.
    */
    bool solver::is_empty(clause const & c) const {
        for (literal lit : c) 
            if (value(lit) != l_false)
                return false;
        return true;
    }

    bool solver::check_missed_propagation(clause_vector const & cs) const {
        for (clause* cp : cs) {
            clause const & c = *cp;
            if (c.frozen())
                continue;
            if (is_empty(c) || is_unit(c)) {
                TRACE("sat_missed_prop", tout << "missed_propagation: " << c << "\n";
                      for (literal l : c) tout << l << ": " << value(l) << "\n";);
                UNREACHABLE();
            }
            SASSERT(!is_empty(c));
            SASSERT(!is_unit(c));
        }
        return true;
    }

    bool solver::check_missed_propagation() const {
        if (inconsistent())
            return true;
        return check_missed_propagation(m_clauses) && check_missed_propagation(m_learned);
    }

    // -----------------------
    //
    // Simplification
    //
    // -----------------------
    bool solver::do_cleanup(bool force) {
        if (m_conflicts_since_init == 0 && !force)
            return false;
        if (at_base_lvl() && !inconsistent() && m_cleaner(force)) {
            if (m_ext)
                m_ext->clauses_modifed();
            return true;
        }
        return false;
    }

    void solver::simplify(bool redundant) {
        if (!at_base_lvl() || inconsistent())
            return;
        m_simplifier(redundant);
        m_simplifier.finalize();
        if (m_ext)
            m_ext->clauses_modifed();
    }

    unsigned solver::scc_bin() {
        if (!at_base_lvl() || inconsistent())
            return 0;
        unsigned r = m_scc();
        if (r > 0 && m_ext)
            m_ext->clauses_modifed();
        return r;
    }

    // -----------------------
    //
    // Extraction of mutexes
    //
    // -----------------------

    struct neg_literal {
        unsigned negate(unsigned idx) {
            return (~to_literal(idx)).index();
        }
    };

    lbool solver::find_mutexes(literal_vector const& lits, vector<literal_vector> & mutexes) {
        max_cliques<neg_literal> mc;
        m_user_bin_clauses.reset();
        m_binary_clause_graph.reset();
        collect_bin_clauses(m_user_bin_clauses, true, false);
        hashtable<literal_pair, pair_hash<literal_hash, literal_hash>, default_eq<literal_pair> > seen_bc;
        for (auto const& b : m_user_bin_clauses) {
            literal l1 = b.first;
            literal l2 = b.second;
            literal_pair p(l1, l2);
            if (!seen_bc.contains(p)) {
                seen_bc.insert(p);
                mc.add_edge(l1.index(), l2.index());
            }
        }
        vector<unsigned_vector> _mutexes;
        literal_vector _lits(lits);
        if (m_ext) {
            // m_ext->find_mutexes(_lits, mutexes);
        }
        unsigned_vector ps;
        for (literal lit : _lits) {
            ps.push_back(lit.index());
        }
        mc.cliques(ps, _mutexes);
        for (auto const& mux : _mutexes) {
            literal_vector clique;
            for (auto const& idx : mux) {
                clique.push_back(to_literal(idx));
            }
            mutexes.push_back(clique);
        }
        return l_true;
    }

    // -----------------------
    //
    // Consequence generation.
    //
    // -----------------------

    static void prune_unfixed(sat::literal_vector& lambda, sat::model const& m) {
        for (unsigned i = 0; i < lambda.size(); ++i) {
            if ((m[lambda[i].var()] == l_false) != lambda[i].sign()) {
                lambda[i] = lambda.back();
                lambda.pop_back();
                --i;
            }
        }
    }

    // Algorithm 7: Corebased Algorithm with Chunking

    static void back_remove(sat::literal_vector& lits, sat::literal l) {
        for (unsigned i = lits.size(); i > 0; ) {
            --i;
            if (lits[i] == l) {
                lits[i] = lits.back();
                lits.pop_back();
                return;
            }
        }
        UNREACHABLE();
    }

    static void brute_force_consequences(sat::solver& s, sat::literal_vector const& asms, sat::literal_vector const& gamma, vector<sat::literal_vector>& conseq) {
        for (literal lit : gamma) {
            sat::literal_vector asms1(asms);
            asms1.push_back(~lit);
            lbool r = s.check(asms1.size(), asms1.data());
            if (r == l_false) {
                conseq.push_back(s.get_core());
            }
        }
    }

    static lbool core_chunking(sat::solver& s, model const& m, sat::bool_var_vector const& vars, sat::literal_vector const& asms, vector<sat::literal_vector>& conseq, unsigned K) {
        sat::literal_vector lambda;
        for (bool_var v : vars) {
            lambda.push_back(sat::literal(v, m[v] == l_false));
        }
        while (!lambda.empty()) {
            IF_VERBOSE(1, verbose_stream() << "(sat-backbone-core " << lambda.size() << " " << conseq.size() << ")\n";);
            unsigned k = std::min(K, lambda.size());
            sat::literal_vector gamma, omegaN;
            for (unsigned i = 0; i < k; ++i) {
                sat::literal l = lambda[lambda.size() - i - 1];
                gamma.push_back(l);
                omegaN.push_back(~l);
            }
            while (true) {
                sat::literal_vector asms1(asms);
                asms1.append(omegaN);
                lbool r = s.check(asms1.size(), asms1.data());
                if (r == l_true) {
                    IF_VERBOSE(1, verbose_stream() << "(sat) " << omegaN << "\n";);
                    prune_unfixed(lambda, s.get_model());
                    break;
                }
                sat::literal_vector const& core = s.get_core();
                sat::literal_vector occurs;
                IF_VERBOSE(1, verbose_stream() << "(core " << core.size() << ")\n";);
                for (unsigned i = 0; i < omegaN.size(); ++i) {
                    if (core.contains(omegaN[i])) {
                        occurs.push_back(omegaN[i]);
                    }
                }
                if (occurs.size() == 1) {
                    sat::literal lit = occurs.back();
                    sat::literal nlit = ~lit;
                    conseq.push_back(core);
                    back_remove(lambda, ~lit);
                    back_remove(gamma, ~lit);
                    s.mk_clause(1, &nlit);
                }
                for (unsigned i = 0; i < omegaN.size(); ++i) {
                    if (occurs.contains(omegaN[i])) {
                        omegaN[i] = omegaN.back();
                        omegaN.pop_back();
                        --i;
                    }
                }
                if (omegaN.empty() && occurs.size() > 1) {
                    brute_force_consequences(s, asms, gamma, conseq);
                    for (unsigned i = 0; i < gamma.size(); ++i) {
                        back_remove(lambda, gamma[i]);
                    }
                    break;
                }
            }
        }
        return l_true;
    }


    lbool solver::get_consequences(literal_vector const& asms, bool_var_vector const& vars, vector<literal_vector>& conseq) {
        literal_vector lits;
        lbool is_sat = l_true;

        if (m_config.m_restart_max != UINT_MAX && !m_model_is_current) {
            return get_bounded_consequences(asms, vars, conseq);
        }
        if (!m_model_is_current) {
            is_sat = check(asms.size(), asms.data());
        }
        if (is_sat != l_true) {
            return is_sat;
        }
        model mdl = get_model();
        for (unsigned i = 0; i < vars.size(); ++i) {
            bool_var v = vars[i];
            switch (get_model()[v]) {
            case l_true: lits.push_back(literal(v, false)); break;
            case l_false: lits.push_back(literal(v, true)); break;
            default: break;
            }
        }

        if (false && asms.empty()) {
            is_sat = core_chunking(*this, mdl, vars, asms, conseq, 100);
        }
        else {
            is_sat = get_consequences(asms, lits, conseq);
        }
        set_model(mdl, !mdl.empty());
        return is_sat;
    }

    void solver::fixup_consequence_core() {
        index_set s;
        TRACE("sat", tout << m_core << "\n";);
        for (unsigned i = 0; i < m_core.size(); ++i) {
            TRACE("sat", tout << m_core[i] << ": "; display_index_set(tout, m_antecedents.find(m_core[i].var())) << "\n";);
            s |= m_antecedents.find(m_core[i].var());
        }
        m_core.reset();
        for (unsigned idx : s) {
            m_core.push_back(to_literal(idx));
        }
        TRACE("sat", tout << m_core << "\n";);
    }

    bool solver::reached_max_conflicts() {
        if (m_config.m_max_conflicts == 0 || m_conflicts_since_init > m_config.m_max_conflicts) {
            if (m_reason_unknown != "sat.max.conflicts") {
                m_reason_unknown = "sat.max.conflicts";
                IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-conflicts = " << m_conflicts_since_init << "\")\n";);
            }
            return !inconsistent();
        }
        return false;
    }


    lbool solver::get_bounded_consequences(literal_vector const& asms, bool_var_vector const& vars, vector<literal_vector>& conseq) {
        bool_var_set unfixed_vars;
        unsigned num_units = 0, num_iterations = 0;
        for (bool_var v : vars) {
            unfixed_vars.insert(v);
        }
        TRACE("sat", tout << asms << "\n";);
        m_antecedents.reset();
        pop_to_base_level();
        if (inconsistent()) return l_false;
        flet<bool> _searching(m_searching, true);
        init_search();
        propagate(false);
        if (inconsistent()) return l_false;
        if (asms.empty()) {
            bool_var v = mk_var(true, false);
            literal lit(v, false);
            init_assumptions(1, &lit);
        }
        else {
            init_assumptions(asms.size(), asms.data());
        }
        propagate(false);
        if (check_inconsistent()) return l_false;

        extract_fixed_consequences(num_units, asms, unfixed_vars, conseq);

        do_simplify();
        if (check_inconsistent()) {
            fixup_consequence_core();
            return l_false;
        }

        while (true) {
            ++num_iterations;
            SASSERT(!inconsistent());

            lbool r = bounded_search();
            if (r != l_undef) {
                fixup_consequence_core();
                return r;
            }

            extract_fixed_consequences(num_units, asms, unfixed_vars, conseq);

            do_restart(true);
            do_simplify();
            if (check_inconsistent()) {
                fixup_consequence_core();
                return l_false;
            }
            do_gc();

            if (should_cancel()) {
                return l_undef;
            }
        }
    }

    lbool solver::get_consequences(literal_vector const& asms, literal_vector const& lits, vector<literal_vector>& conseq) {
        TRACE("sat", tout << asms << "\n";);
        m_antecedents.reset();
        literal_set unfixed_lits(lits), assumptions(asms);
        bool_var_set unfixed_vars;
        for (literal lit : lits) {
            unfixed_vars.insert(lit.var());
        }

        pop_to_base_level();
        if (inconsistent()) return l_false;
        init_search();
        propagate(false);
        if (inconsistent()) return l_false;
        if (asms.empty()) {
            bool_var v = mk_var(true, false);
            literal lit(v, false);
            init_assumptions(1, &lit);
        }
        else {
            init_assumptions(asms.size(), asms.data());
        }
        propagate(false);
        if (check_inconsistent()) return l_false;
        SASSERT(search_lvl() == 1);

        unsigned num_iterations = 0;
        extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);
        update_unfixed_literals(unfixed_lits, unfixed_vars);
        while (!unfixed_lits.empty()) {
            if (scope_lvl() > search_lvl()) {
                pop(scope_lvl() - search_lvl());
            }
            propagate(false);
            ++num_iterations;
            checkpoint();
            unsigned num_resolves = 0;
            unsigned num_fixed = 0;
            unsigned num_assigned = 0;
            lbool is_sat = l_true;
            for (literal lit : unfixed_lits) {
                if (value(lit) != l_undef) {
                    ++num_fixed;
                    if (lvl(lit) <= 1 && value(lit) == l_true) {
                        extract_fixed_consequences(lit, assumptions, unfixed_vars, conseq);
                    }
                    continue;
                }
                push();
                ++num_assigned;
                assign_scoped(~lit);
                propagate(false);
                while (inconsistent()) {
                    if (!resolve_conflict()) {
                        TRACE("sat", display(tout << "inconsistent\n"););
                        m_inconsistent = false;
                        is_sat = l_undef;
                        break;
                    }
                    propagate(false);
                    ++num_resolves;
                }
            }

            extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);

            if (is_sat == l_true) {
                if (scope_lvl() == search_lvl() && num_resolves > 0) {
                    IF_VERBOSE(1, verbose_stream() << "(sat.get-consequences backjump)\n";);
                    is_sat = l_undef;
                }
                else {
                    is_sat = bounded_search();
                    if (is_sat == l_undef) {
                        do_restart(true);                        
                        propagate(false);
                    }
                    extract_fixed_consequences(unfixed_lits, assumptions, unfixed_vars, conseq);
                }
            }
            if (is_sat == l_false) {
                TRACE("sat", tout << "unsat\n";);
                m_inconsistent = false;
            }
            if (is_sat == l_true) {
                delete_unfixed(unfixed_lits, unfixed_vars);
            }
            update_unfixed_literals(unfixed_lits, unfixed_vars);
            IF_VERBOSE(1, verbose_stream() << "(sat.get-consequences"
                       << " iterations: " << num_iterations
                       << " variables: " << unfixed_lits.size()
                       << " fixed: " << conseq.size()
                       << " status: " << is_sat
                       << " pre-assigned: " << num_fixed
                       << " unfixed: " << lits.size() - conseq.size() - unfixed_lits.size()
                       << ")\n";);

            if (!unfixed_lits.empty() && m_config.m_restart_max <= num_iterations) {
                return l_undef;
            }
        }
        return l_true;
    }

    void solver::delete_unfixed(literal_set& unfixed_lits, bool_var_set& unfixed_vars) {
        literal_set to_keep;
        for (literal lit : unfixed_lits) {
            if (value(lit) == l_true) {
                to_keep.insert(lit);
            }
            else {
                unfixed_vars.remove(lit.var());
            }
        }
        unfixed_lits = to_keep;
    }

    void solver::update_unfixed_literals(literal_set& unfixed_lits, bool_var_set& unfixed_vars) {
        literal_vector to_delete;
        for (literal lit : unfixed_lits) {
            if (!unfixed_vars.contains(lit.var())) {
                to_delete.push_back(lit);
            }
        }
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            unfixed_lits.remove(to_delete[i]);
        }
    }


    void solver::extract_fixed_consequences(unsigned& start, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        SASSERT(!inconsistent());
        unsigned sz = m_trail.size();
        for (unsigned i = start; i < sz && lvl(m_trail[i]) <= 1; ++i) {
            extract_fixed_consequences(m_trail[i], assumptions, unfixed, conseq);
        }
        start = sz;
    }

    void solver::extract_fixed_consequences(literal_set const& unfixed_lits, literal_set const& assumptions, bool_var_set& unfixed_vars, vector<literal_vector>& conseq) {
        for (literal lit: unfixed_lits) {
            TRACE("sat", tout << "extract: " << lit << " " << value(lit) << " " << lvl(lit) << "\n";);

            if (lvl(lit) <= 1 && value(lit) == l_true) {
                extract_fixed_consequences(lit, assumptions, unfixed_vars, conseq);
            }
        }
    }

    bool solver::check_domain(literal lit, literal lit2) {
        if (!m_antecedents.contains(lit2.var())) {
            SASSERT(value(lit2) == l_true);
            SASSERT(m_todo_antecedents.empty() || m_todo_antecedents.back() != lit2);
            m_todo_antecedents.push_back(lit2);
            return false;
        }
        else {
            return true;
        }
    }

    bool solver::extract_assumptions(literal lit, index_set& s) {
        justification js = m_justification[lit.var()];
        TRACE("sat", tout << lit << " " << js << "\n";);
        bool all_found = true;
        switch (js.get_kind()) {
        case justification::NONE:
            break;
        case justification::BINARY:
            if (!check_domain(lit, ~js.get_literal())) return false;
            s |= m_antecedents.find(js.get_literal().var());
            break;
        case justification::TERNARY:
            if (!check_domain(lit, ~js.get_literal1()) ||
                !check_domain(lit, ~js.get_literal2())) return false;
            s |= m_antecedents.find(js.get_literal1().var());
            s |= m_antecedents.find(js.get_literal2().var());
            break;
        case justification::CLAUSE: {
            clause & c = get_clause(js);
            for (literal l : c) {
                if (l != lit) {
                    if (check_domain(lit, ~l) && all_found) {
                        s |= m_antecedents.find(l.var());
                    }
                    else {
                        all_found = false;
                    }
                }
            }
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            fill_ext_antecedents(lit, js, true);
            for (literal l : m_ext_antecedents) {
                if (check_domain(lit, l) && all_found) {
                    s |= m_antecedents.find(l.var());
                }
                else {
                    all_found = false;
                }
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        TRACE("sat", display_index_set(tout << lit << ": " , s) << "\n";);
        return all_found;
    }

    std::ostream& solver::display_index_set(std::ostream& out, index_set const& s) const {
        for (unsigned idx : s) {
            out << to_literal(idx) << " ";
        }
        return out;
    }


    bool solver::extract_fixed_consequences1(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        index_set s;
        if (m_antecedents.contains(lit.var())) {
            return true;
        }
        if (assumptions.contains(lit)) {
            s.insert(lit.index());
        }
        else {
            if (!extract_assumptions(lit, s)) {
                SASSERT(!m_todo_antecedents.empty());
                return false;
            }
            add_assumption(lit);
        }
        m_antecedents.insert(lit.var(), s);
        if (unfixed.contains(lit.var())) {
            literal_vector cons;
            cons.push_back(lit);
            for (unsigned idx : s) {
                cons.push_back(to_literal(idx));
            }
            unfixed.remove(lit.var());
            conseq.push_back(cons);
        }
        return true;
    }

    void solver::extract_fixed_consequences(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq) {
        SASSERT(m_todo_antecedents.empty());
        m_todo_antecedents.push_back(lit);
        while (!m_todo_antecedents.empty()) {
            if (extract_fixed_consequences1(m_todo_antecedents.back(), assumptions, unfixed, conseq)) {
                m_todo_antecedents.pop_back();
            }
        }
    }

    // -----------------------
    //
    // Statistics
    //
    // -----------------------

    void solver::display_status(std::ostream & out) const {
        unsigned num_bin = 0;
        unsigned num_ext = 0;
        unsigned num_lits = 0;
        unsigned l_idx = 0;
        for (watch_list const& wlist : m_watches) {
            literal l = ~to_literal(l_idx++);
            for (watched const& w : wlist) {
                switch (w.get_kind()) {
                case watched::BINARY:
                    if (l.index() < w.get_literal().index()) {
                        num_lits += 2;
                        num_bin++;
                    }
                    break;
                case watched::EXT_CONSTRAINT:
                    num_ext++;
                    break;
                default:
                    break;
                }
            }
        }
        unsigned num_elim = 0;
        for (bool_var v = 0; v < num_vars(); v++) {
            if (m_eliminated[v])
                num_elim++;
        }
        unsigned num_ter  = 0;
        unsigned num_cls  = 0;
        clause_vector const * vs[2] = { &m_clauses, &m_learned };
        for (unsigned i = 0; i < 2; i++) {
            clause_vector const & cs = *(vs[i]);
            for (clause* cp : cs) {
                clause & c = *cp;
                if (ENABLE_TERNARY && c.size() == 3)
                    num_ter++;
                else
                    num_cls++;
                num_lits += c.size();
            }
        }
        unsigned total_cls = num_cls + num_ter + num_bin;
        double mem = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        out << "(sat-status\n";
        out << "  :inconsistent    " << (m_inconsistent ? "true" : "false") << "\n";
        out << "  :vars            " << num_vars() << "\n";
        out << "  :elim-vars       " << num_elim << "\n";
        out << "  :lits            " << num_lits << "\n";
        out << "  :assigned        " << m_trail.size() << "\n";
        out << "  :binary-clauses  " << num_bin << "\n";
        out << "  :ternary-clauses " << num_ter << "\n";
        out << "  :clauses         " << num_cls << "\n";
        out << "  :del-clause      " << m_stats.m_del_clause << "\n";
        out << "  :avg-clause-size " << (total_cls == 0 ? 0.0 : static_cast<double>(num_lits) / static_cast<double>(total_cls)) << "\n";
        out << "  :memory          " << std::fixed << std::setprecision(2) << mem << ")" << std::endl;
    }

    void stats::collect_statistics(statistics & st) const {
        st.update("sat mk clause 2ary", m_mk_bin_clause);
        st.update("sat mk clause 3ary", m_mk_ter_clause);
        st.update("sat mk clause nary", m_mk_clause);
        st.update("sat mk var", m_mk_var);
        st.update("sat gc clause", m_gc_clause);
        st.update("sat del clause", m_del_clause);
        st.update("sat conflicts", m_conflict);
        st.update("sat decisions", m_decision);
        st.update("sat propagations 2ary", m_bin_propagate);
        st.update("sat propagations 3ary", m_ter_propagate);
        st.update("sat propagations nary", m_propagate);
        st.update("sat restarts", m_restart);
        st.update("sat minimized lits", m_minimized_lits);
        st.update("sat subs resolution dyn", m_dyn_sub_res);
        st.update("sat blocked correction sets", m_blocked_corr_sets);
        st.update("sat units", m_units);
        st.update("sat elim bool vars res", m_elim_var_res);
        st.update("sat elim bool vars bdd", m_elim_var_bdd);
        st.update("sat backjumps", m_backjumps);
        st.update("sat backtracks", m_backtracks);
    }

    void stats::reset() {
        memset(this, 0, sizeof(*this));
    }

    void mk_stat::display(std::ostream & out) const {
        unsigned given, redundant;
        m_solver.num_binary(given, redundant);
        out << " " << std::setw(5) << m_solver.m_clauses.size() + given << "/" << given;
        out << " " << std::setw(5) << (m_solver.m_learned.size() + redundant - m_solver.m_num_frozen) << "/" << redundant;
        out << " " << std::setw(3)  << m_solver.init_trail_size();
        out << " " << std::setw(7)  << m_solver.m_stats.m_gc_clause << " ";
        out << " " << std::setw(7)  << mem_stat();
    }

    std::ostream & operator<<(std::ostream & out, mk_stat const & stat) {
        stat.display(out);
        return out;
    }

    bool solver::all_distinct(literal_vector const& lits) {
        init_visited();
        for (literal l : lits) {
            if (is_visited(l.var())) {
                return false;
            }
            mark_visited(l.var());
        }
        return true;
    }

    bool solver::all_distinct(clause const& c) {
        init_visited();
        for (literal l : c) {
            if (is_visited(l.var())) {
                return false;
            }
            mark_visited(l.var());
        }
        return true;
    }

    void solver::init_visited() {
        if (m_visited.empty()) {
            m_visited_ts = 0;
        }
        m_visited_ts++;
        if (m_visited_ts == 0) {
            m_visited_ts = 1;
            m_visited.reset();
        }
        while (m_visited.size() < 2*num_vars()) {
            m_visited.push_back(0);
        }
    }



};
