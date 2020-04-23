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
#include "sat/sat_integrity_checker.h"
#include "sat/sat_solver.h"
#include "util/trace.h"

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
        for (watched const& w : wlist) {
            if (w.is_clause()) {
                if (w.get_clause_offset() == cls_off) {
                    // the blocked literal must be in the clause.
                    VERIFY(c.contains(w.get_blocked_literal()));
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
            VERIFY(c[i].var() <= s.num_vars());
            CTRACE("sat_bug", s.was_eliminated(c[i].var()),
                   tout << "l: " << c[i].var() << "\n";
                   tout << "c: " << c << "\n";
                   s.display(tout););
            VERIFY(!s.was_eliminated(c[i].var()));
        }

        SASSERT(c.check_approx());
        
        if (c.frozen())
            return true;

        if (c.size() == 3) {
            CTRACE("sat_ter_watch_bug", !contains_watched(s.get_wlist(~c[0]), c[1], c[2]), tout << c << "\n";
                   tout << "watch_list:\n";
                   s.display_watch_list(tout, s.get_wlist(~c[0]));
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
                        VERIFY(s.value(c[i]) == l_false);
                    }
                }
            }
            
            // the first two literals must be watched.
            VERIFY(contains_watched(s.get_wlist(~c[0]), c, s.get_offset(c)));
            VERIFY(contains_watched(s.get_wlist(~c[1]), c, s.get_offset(c)));
        }
        return true;
    }

    bool integrity_checker::check_clauses(clause * const * begin, clause * const * end) const {        
        for (clause * const * it = begin; it != end; ++it) {
            VERIFY(check_clause(*(*it)));
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
        VERIFY(s.m_watches.size() == s.num_vars() * 2);
        VERIFY(s.m_assignment.size() == s.num_vars() * 2);
        VERIFY(s.m_lit_mark.size() == s.num_vars() * 2);
        VERIFY(s.m_justification.size() == s.num_vars());
        VERIFY(s.m_decision.size() == s.num_vars());
        VERIFY(s.m_eliminated.size() == s.num_vars());
        VERIFY(s.m_external.size() == s.num_vars());
        VERIFY(s.m_mark.size() == s.num_vars());
        VERIFY(s.m_activity.size() == s.num_vars());
        VERIFY(s.m_phase.size() == s.num_vars());
        VERIFY(s.m_prev_phase.size() == s.num_vars());
        VERIFY(s.m_assigned_since_gc.size() == s.num_vars());
        for (bool_var v = 0; v < s.num_vars(); v++) {
            if (s.was_eliminated(v)) {
                VERIFY(s.get_wlist(literal(v, false)).empty());
                VERIFY(s.get_wlist(literal(v, true)).empty());
            }
        }
        return true;
    }

    bool integrity_checker::check_watches(literal l) const {
        return check_watches(l, s.get_wlist(~l));
    }

    bool integrity_checker::check_watches(literal l, watch_list const& wlist) const {
        for (watched const& w : wlist) {
            switch (w.get_kind()) {
            case watched::BINARY:
                VERIFY(!s.was_eliminated(w.get_literal().var()));
                CTRACE("sat_watched_bug", !s.get_wlist(~(w.get_literal())).contains(watched(l, w.is_learned())),
                       tout << "l: " << l << " l2: " << w.get_literal() << "\n"; 
                       tout << "was_eliminated1: " << s.was_eliminated(l.var());
                       tout << " was_eliminated2: " << s.was_eliminated(w.get_literal().var());
                       tout << " learned: " << w.is_learned() << "\n";
                       s.display_watch_list(tout, wlist);
                       tout << "\n";
                       s.display_watch_list(tout, s.get_wlist(~(w.get_literal())));
                       tout << "\n";);
                VERIFY(find_binary_watch(s.get_wlist(~(w.get_literal())), l));
                break;
            case watched::TERNARY:
                VERIFY(!s.was_eliminated(w.get_literal1().var()));
                VERIFY(!s.was_eliminated(w.get_literal2().var()));
                VERIFY(w.get_literal1().index() < w.get_literal2().index());
                break;
            case watched::CLAUSE:
                VERIFY(!s.get_clause(w.get_clause_offset()).was_removed());
                break;
            default:
                break;
            }
        }
        return true;
    }

    bool integrity_checker::check_watches() const {
        unsigned l_idx = 0;
        for (watch_list const& wlist : s.m_watches) {
            literal l = ~to_literal(l_idx++);            
            CTRACE("sat_bug", 
                   s.was_eliminated(l.var()) && !wlist.empty(),
                   tout << "l: " << l << "\n";
                   s.display_watches(tout);
                   s.display(tout););
            VERIFY(!s.was_eliminated(l.var()) || wlist.empty());
            if (!check_watches(l, wlist)) 
                return false;
        }        
        return true;
    }

    bool integrity_checker::check_reinit_stack() const {
        for (auto const& c : s.m_clauses_to_reinit) {
            VERIFY(c.is_binary() || c.get_clause()->on_reinit_stack());
        }
        return true;
    }

    bool integrity_checker::check_disjoint_clauses() const {
        uint_set ids;
        for (clause* cp : s.m_clauses) {
            ids.insert(cp->id());
        }
        for (clause* cp : s.m_learned) {
            if (ids.contains(cp->id())) {
                TRACE("sat", tout << "Repeated clause: " << cp->id() << "\n";);
                return false;
            }
        }
        return true;
    }
    
    bool integrity_checker::operator()() const {
        if (s.inconsistent())
            return true;
        VERIFY(check_clauses());
        VERIFY(check_learned_clauses());
        VERIFY(check_watches());
        VERIFY(check_bool_vars());
        VERIFY(check_reinit_stack());
        VERIFY(check_disjoint_clauses());
        return true;
    }
};
