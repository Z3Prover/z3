/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_integrity_checker.cpp

Abstract:

    Checker whether the SAT solver internal datastructures 
    are consistent or not.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#include"sat_integrity_checker.h"
#include"sat_solver.h"
#include"trace.h"

namespace sat {
    
    integrity_checker::integrity_checker(solver const & _s):
        s(_s) {
    }

    // for ternary clauses 
    static bool contains_watched(watch_list const & wlist, literal l1, literal l2) {
        return wlist.contains(watched(l1, l2));
    }
    
    // for nary clauses
    static bool contains_watched(watch_list const & wlist, clause const & c, clause_offset cls_off) {
        watch_list::const_iterator it  = wlist.begin();
        watch_list::const_iterator end = wlist.end();
        for (; it != end; ++it) {
            if (it->is_clause()) {
                if (it->get_clause_offset() == cls_off) {
                    // the blocked literal must be in the clause.
                    SASSERT(c.contains(it->get_blocked_literal()));
                    return true;
                }
            }
        }
        UNREACHABLE();
        return false;
    }

    bool integrity_checker::check_clause(clause const & c) const {
        SASSERT(!c.was_removed());
        for (unsigned i = 0; i < c.size(); i++) {
            SASSERT(c[i].var() <= s.num_vars());
            CTRACE("sat_bug", s.was_eliminated(c[i].var()),
                   tout << "l: " << c[i].var() << "\n";
                   tout << "c: " << c << "\n";
                   s.display(tout););
            SASSERT(!s.was_eliminated(c[i].var()));
        }

        SASSERT(c.check_approx());
        
        if (c.frozen())
            return true;

        if (c.size() == 3) {
            CTRACE("sat_ter_watch_bug", !contains_watched(s.get_wlist(~c[0]), c[1], c[2]), tout << c << "\n";
                   tout << "watch_list:\n";
                   sat::display(tout, s.m_cls_allocator, s.get_wlist(~c[0]));
                   tout << "\n";);
            VERIFY(contains_watched(s.get_wlist(~c[0]), c[1], c[2]));
            VERIFY(contains_watched(s.get_wlist(~c[1]), c[0], c[2]));
            VERIFY(contains_watched(s.get_wlist(~c[2]), c[0], c[1]));
        }
        else {
            if (s.value(c[0]) == l_false || s.value(c[1]) == l_false) {
                bool on_prop_stack = false;
                for (unsigned i = s.m_qhead; i < s.m_trail.size(); i++) {
                    if (s.m_trail[i].var() == c[0].var() ||
                        s.m_trail[i].var() == c[1].var()) {
                        on_prop_stack = true;
                        break;
                    }
                }
                // the clause has been satisfied or all other literals are assigned to false.
                if (!on_prop_stack && s.status(c) != l_true) {
                    for (unsigned i = 2; i < c.size(); i++) {
                        CTRACE("sat_bug", s.value(c[i]) != l_false,
                               tout << c << " status: " << s.status(c) << "\n";
                               for (unsigned i = 0; i < c.size(); i++) tout << "val(" << i << "): " << s.value(c[i]) << "\n";);
                        SASSERT(s.value(c[i]) == l_false);
                    }
                }
            }
            
            // the first two literals must be watched.
            SASSERT(contains_watched(s.get_wlist(~c[0]), c, s.get_offset(c)));
            SASSERT(contains_watched(s.get_wlist(~c[1]), c, s.get_offset(c)));
        }
        return true;
    }

    bool integrity_checker::check_clauses(clause * const * begin, clause * const * end) const {
        for (clause * const * it = begin; it != end; ++it) {
            SASSERT(check_clause(*(*it)));
        }
        return true;
    }

    bool integrity_checker::check_clauses() const {
        return check_clauses(s.begin_clauses(), s.end_clauses());
    }

    bool integrity_checker::check_learned_clauses() const {
        unsigned num_frozen = 0;
        clause * const * end = s.end_clauses();
        for (clause * const * it = s.begin_clauses(); it != end; ++it) {
            clause & c = *(*it);
            if (c.frozen())
                num_frozen++;
        }
        SASSERT(num_frozen == s.m_num_frozen);
        return check_clauses(s.begin_learned(), s.end_learned());
    }

    bool integrity_checker::check_assignment() const {
        return true;
    }

    bool integrity_checker::check_bool_vars() const {
        SASSERT(s.m_watches.size() == s.num_vars() * 2);
        SASSERT(s.m_assignment.size() == s.num_vars() * 2);
        SASSERT(s.m_lit_mark.size() == s.num_vars() * 2);
        SASSERT(s.m_justification.size() == s.num_vars());
        SASSERT(s.m_decision.size() == s.num_vars());
        SASSERT(s.m_eliminated.size() == s.num_vars());
        SASSERT(s.m_external.size() == s.num_vars());
        SASSERT(s.m_level.size() == s.num_vars());
        SASSERT(s.m_mark.size() == s.num_vars());
        SASSERT(s.m_activity.size() == s.num_vars());
        SASSERT(s.m_phase.size() == s.num_vars());
        SASSERT(s.m_prev_phase.size() == s.num_vars());
        SASSERT(s.m_assigned_since_gc.size() == s.num_vars());
        for (bool_var v = 0; v < s.num_vars(); v++) {
            if (s.was_eliminated(v)) {
                SASSERT(s.get_wlist(literal(v, false)).empty());
                SASSERT(s.get_wlist(literal(v, true)).empty());
            }
        }
        return true;
    }

    bool integrity_checker::check_watches() const {
        DEBUG_CODE(
        vector<watch_list>::const_iterator it  = s.m_watches.begin();
        vector<watch_list>::const_iterator end = s.m_watches.end();
        for (unsigned l_idx = 0; it != end; ++it, ++l_idx) {
            literal l = ~to_literal(l_idx);            
            watch_list const & wlist = *it;
            CTRACE("sat_bug", 
                   s.was_eliminated(l.var()) && !wlist.empty(),
                   tout << "l: " << l << "\n";
                   s.display_watches(tout);
                   s.display(tout););
            SASSERT(!s.was_eliminated(l.var()) || wlist.empty());
            watch_list::const_iterator it2  = wlist.begin();
            watch_list::const_iterator end2 = wlist.end();
            for (; it2 != end2; ++it2) {
                switch (it2->get_kind()) {
                case watched::BINARY:
                    SASSERT(!s.was_eliminated(it2->get_literal().var()));
                    CTRACE("sat_watched_bug", !s.get_wlist(~(it2->get_literal())).contains(watched(l, it2->is_learned())),
                           tout << "l: " << l << " l2: " << it2->get_literal() << "\n"; 
                           tout << "was_eliminated1: " << s.was_eliminated(l.var());
                           tout << " was_eliminated2: " << s.was_eliminated(it2->get_literal().var());
                           tout << " learned: " << it2->is_learned() << "\n";
                           sat::display(tout, s.m_cls_allocator, wlist);
                           tout << "\n";
                           sat::display(tout, s.m_cls_allocator, s.get_wlist(~(it2->get_literal())));
                           tout << "\n";);
                        SASSERT(s.get_wlist(~(it2->get_literal())).contains(watched(l, it2->is_learned())));
                    break;
                case watched::TERNARY:
                    SASSERT(!s.was_eliminated(it2->get_literal1().var()));
                    SASSERT(!s.was_eliminated(it2->get_literal2().var()));
                    SASSERT(it2->get_literal1().index() < it2->get_literal2().index());
                    break;
                case watched::CLAUSE:
                    SASSERT(!s.m_cls_allocator.get_clause(it2->get_clause_offset())->was_removed());
                    break;
                default:
                    break;
                }
            }
        });
        return true;
    }

    bool integrity_checker::check_reinit_stack() const {
        clause_wrapper_vector::const_iterator it  = s.m_clauses_to_reinit.begin();
        clause_wrapper_vector::const_iterator end = s.m_clauses_to_reinit.end();
        for (; it != end; ++it) {
            if (it->is_binary())
                continue;
            SASSERT(it->get_clause()->on_reinit_stack());
        }
        return true;
    }

    bool integrity_checker::check_disjoint_clauses() const {
        uint_set ids;
        clause_vector::const_iterator it  = s.m_clauses.begin();
        clause_vector::const_iterator end = s.m_clauses.end();
        for (; it != end; ++it) {
            ids.insert((*it)->id());
        }
        it = s.m_learned.begin();
        end = s.m_learned.end();
        for (; it != end; ++it) {
            if (ids.contains((*it)->id())) {
                TRACE("sat", tout << "Repeated clause: " << (*it)->id() << "\n";);
                return false;
            }
        }
        return true;
    }
    
    bool integrity_checker::operator()() const {
        if (s.inconsistent())
            return true;
        SASSERT(check_clauses());
        SASSERT(check_learned_clauses());
        SASSERT(check_watches());
        SASSERT(check_bool_vars());
        SASSERT(check_reinit_stack());
        SASSERT(check_disjoint_clauses());
        return true;
    }
};
