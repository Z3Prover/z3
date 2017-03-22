/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_elim_eqs.cpp

Abstract:

    Helper class for eliminating eqs.

Author:

    Leonardo de Moura (leonardo) 2011-05-27.

Revision History:

--*/
#include"sat_elim_eqs.h"
#include"sat_solver.h"
#include"trace.h"

namespace sat {
    
    elim_eqs::elim_eqs(solver & s):
        m_solver(s) {
    }

    inline literal norm(literal_vector const & roots, literal l) {
        if (l.sign()) 
            return ~roots[l.var()];
        else
            return roots[l.var()];
    }

    void elim_eqs::cleanup_bin_watches(literal_vector const & roots) {
        vector<watch_list>::iterator it  = m_solver.m_watches.begin();
        vector<watch_list>::iterator end = m_solver.m_watches.end();
        for (unsigned l_idx = 0; it != end; ++it, ++l_idx) {
            watch_list & wlist = *it;
            literal l1 = ~to_literal(l_idx);
            literal r1 = norm(roots, l1);
            watch_list::iterator it2    = wlist.begin();
            watch_list::iterator itprev = it2;
            watch_list::iterator end2   = wlist.end();
            for (; it2 != end2; ++it2) {
                if (it2->is_binary_clause()) {
                    literal l2 = it2->get_literal();
                    literal r2 = norm(roots, l2);
                    if (r1 == r2) {
                        m_solver.assign(r1, justification());
                        if (m_solver.inconsistent())
                            return;
                        // consume unit
                        continue;
                    }
                    if (r1 == ~r2) {
                        // consume tautology
                        continue;
                    }
                    if (l1 != r1) {
                        // add half r1 => r2, the other half ~r2 => ~r1 is added when traversing l2 
                        m_solver.m_watches[(~r1).index()].push_back(watched(r2, it2->is_learned()));
                        continue;
                    }
                    it2->set_literal(r2); // keep it
                }
                *itprev = *it2;
                itprev++;
            }
            wlist.set_end(itprev);
        }
    }

    void elim_eqs::cleanup_clauses(literal_vector const & roots, clause_vector & cs) {
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c     = *(*it);
            TRACE("elim_eqs", tout << "processing: " << c << "\n";);
            unsigned sz    = c.size();
            unsigned i;
            for (i = 0; i < sz; i++) {
                literal l = c[i];
                literal r = norm(roots, l);
                if (l != r)
                    break;
            }
            if (i == sz) {
                // clause was not affected
                *it2 = *it;
                it2++;
                continue;
            }
            if (!c.frozen())
                m_solver.detach_clause(c);
            // apply substitution
            for (i = 0; i < sz; i++) {
                SASSERT(!m_solver.was_eliminated(c[i].var()));
                c[i] = norm(roots, c[i]);
            }
            std::sort(c.begin(), c.end());
            TRACE("elim_eqs", tout << "after normalization/sorting: " << c << "\n";);
            // remove duplicates, and check if it is a tautology
            literal l_prev = null_literal;
            unsigned j = 0;
            for (i = 0; i < sz; i++) {
                literal l = c[i];
                if (l == l_prev)
                    continue;
                if (l == ~l_prev)
                    break;
                l_prev = l;
                lbool val = m_solver.value(l);
                if (val == l_true)
                    break; // clause was satisfied
                if (val == l_false)
                    continue; // skip
                c[j] = l;
                j++;
            }
            if (i < sz) {
                // clause is a tautology or was simplified
                m_solver.del_clause(c);
                continue; 
            }
            if (j == 0) {
                // empty clause
                m_solver.set_conflict(justification());
                for (; it != end; ++it) {
                    *it2 = *it;
                    it2++;
                }
                cs.set_end(it2);
                return;
            }
            TRACE("elim_eqs", tout << "after removing duplicates: " << c << " j: " << j << "\n";);
            if (j < sz)
                c.shrink(j);
            else
                c.update_approx();
            SASSERT(c.size() == j);
            DEBUG_CODE({
                for (unsigned i = 0; i < c.size(); i++) {
                    SASSERT(c[i] == norm(roots, c[i]));
                }
            });
            SASSERT(j >= 1);
            switch (j) {
            case 1:
                m_solver.assign(c[0], justification());
                m_solver.del_clause(c);
                break;
            case 2:
                m_solver.mk_bin_clause(c[0], c[1], c.is_learned());
                m_solver.del_clause(c);
                break;
            default:
                SASSERT(*it == &c);
                *it2 = *it;
                it2++;
                if (!c.frozen())
                    m_solver.attach_clause(c);
                break;
            }
        }
        cs.set_end(it2);
    }

    void elim_eqs::save_elim(literal_vector const & roots, bool_var_vector const & to_elim) {
        model_converter & mc = m_solver.m_mc;
        bool_var_vector::const_iterator it  = to_elim.begin();
        bool_var_vector::const_iterator end = to_elim.end();
        for (; it != end; ++it) {
            bool_var v = *it;
            literal  l(v, false);
            literal r  = roots[v];
            SASSERT(v != r.var());
            if (m_solver.is_external(v)) {
                // cannot really eliminate v, since we have to notify extension of future assignments
                m_solver.mk_bin_clause(~l, r, false);
                m_solver.mk_bin_clause(l, ~r, false);
            }
            else {
                model_converter::entry & e = mc.mk(model_converter::ELIM_VAR, v);
                TRACE("save_elim", tout << "marking as deleted: " << v << " l: " << l << " r: " << r << "\n";);
                m_solver.m_eliminated[v] = true;
                mc.insert(e, ~l, r);
                mc.insert(e,  l, ~r);
            }
        }
    }

    bool elim_eqs::check_clauses(literal_vector const & roots) const {
        clause_vector * vs[2] = { &m_solver.m_clauses, &m_solver.m_learned };
        for (unsigned i = 0; i < 2; i++) {
            clause_vector & cs  = *(vs[i]);
            clause_vector::iterator it  = cs.begin();
            clause_vector::iterator end = cs.end();
            for (; it != end; ++it) {
                clause & c  = *(*it);
                unsigned sz = c.size();
                for (unsigned i = 0; i < sz; i++) {
                    CTRACE("elim_eqs_bug", m_solver.was_eliminated(c[i].var()), tout << "lit: " << c[i] << " " << norm(roots, c[i]) << "\n";
                           tout << c << "\n";);
                    SASSERT(!m_solver.was_eliminated(c[i].var()));
                }
            }
        }
        return true;
    }

    void elim_eqs::operator()(literal_vector const & roots, bool_var_vector const & to_elim) {
        cleanup_bin_watches(roots);
        TRACE("elim_eqs", tout << "after bin cleanup\n"; m_solver.display(tout););
        cleanup_clauses(roots, m_solver.m_clauses);
        if (m_solver.inconsistent()) return;
        cleanup_clauses(roots, m_solver.m_learned);
        if (m_solver.inconsistent()) return;
        save_elim(roots, to_elim);
        m_solver.propagate(false);
        SASSERT(check_clauses(roots));
    }
};
