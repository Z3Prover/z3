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
#include "sat/sat_elim_eqs.h"
#include "sat/sat_solver.h"
#include "util/trace.h"

namespace sat {
    
    elim_eqs::elim_eqs(solver & s):
        m_solver(s),
        m_to_delete(nullptr) {
    }

    elim_eqs::~elim_eqs() {
        dealloc(m_to_delete);
    }


    inline literal norm(literal_vector const & roots, literal l) {
        if (l.sign()) 
            return ~roots[l.var()];
        else
            return roots[l.var()];
    }

    void elim_eqs::cleanup_bin_watches(literal_vector const & roots) {        
        unsigned l_idx = 0;
        m_new_bin.reset();
        for (watch_list & wlist : m_solver.m_watches) {
            literal l1 = ~to_literal(l_idx++);
            literal r1 = norm(roots, l1);
            watch_list::iterator it     = wlist.begin();
            watch_list::iterator itprev = it;
            watch_list::iterator end    = wlist.end();
            for (; it != end; ++it) {
                if (it->is_binary_clause()) {
                    literal l2 = it->get_literal();
                    literal r2 = norm(roots, l2);
                    if (r1 == r2) {
                        m_solver.assign_unit(r1);
                        if (m_solver.inconsistent())
                            return;
                        // consume unit
                        continue;
                    }
                    if (r1 == ~r2) {
                        // consume tautology
                        continue;
                    }
#if 0
                    if (l1 != r1) {
                        // add half r1 => r2, the other half ~r2 => ~r1 is added when traversing l2 
                        m_solver.m_watches[(~r1).index()].push_back(watched(r2, it->is_learned()));
                        continue;
                    }
                    it->set_literal(r2); // keep it.
#else
                    if (l1 != r1 || l2 != r2) {
                        if (r1.index() < r2.index()) {
                            m_new_bin.push_back(bin(r1, r2, it->is_learned()));
                        }
                        continue;
                    }
                    // keep it
#endif
                }
                *itprev = *it;
                itprev++;
            }
            wlist.set_end(itprev);
        }

        for (auto const& b : m_new_bin) {
            m_solver.mk_bin_clause(b.l1, b.l2, b.learned);
        }
        m_new_bin.reset();
    }

    void elim_eqs::drat_delete_clause() {
        if (m_solver.m_config.m_drat) {
            m_solver.m_drat.del(*m_to_delete->get());             
        }
    }

    void elim_eqs::cleanup_clauses(literal_vector const & roots, clause_vector & cs) {
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c     = *(*it);
            TRACE("sats", tout << "processing: " << c << "\n";);
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
            if (!c.frozen()) {
                m_solver.detach_clause(c);
            }
            
            // save clause to be deleted for drat
            if (m_solver.m_config.m_drat) {
                if (!m_to_delete) m_to_delete = alloc(tmp_clause);
                m_to_delete->set(sz, c.begin(), c.is_learned());
            }

            // apply substitution
            for (i = 0; i < sz; i++) {   
                literal lit = c[i];
                c[i] = norm(roots, lit);
                VERIFY(c[i] == norm(roots, c[i]));
                VERIFY(!m_solver.was_eliminated(c[i].var()) || lit == c[i]);
            }
            std::sort(c.begin(), c.end());
            for (literal l : c) VERIFY(l == norm(roots, l));
            TRACE("sats", tout << "after normalization/sorting: " << c << "\n"; tout.flush(););
            DEBUG_CODE({
                    for (literal l : c) {
                        CTRACE("sat", l != norm(roots, l), tout << l << " " << norm(roots, l) << "\n"; tout.flush(););
                        SASSERT(l == norm(roots, l));
                    } });

            // remove duplicates, and check if it is a tautology
            unsigned j = 0;
            literal l_prev = null_literal;
            for (i = 0; i < sz; i++) {
                literal l = c[i];
                if (l == ~l_prev) {
                    break;
                }
                if (l == l_prev) {
                    continue;
                }
                SASSERT(l != ~l_prev);
                l_prev = l;
                lbool val = m_solver.value(l);
                if (val == l_true) {
                    break;
                }
                if (val == l_false) {
                    continue; // skip
                }
                c[j] = l;                
                j++;
            }
            TRACE("elim_eqs", tout << "after removing duplicates: " << c << " j: " << j << "\n";);

            if (i < sz) {
                drat_delete_clause();
                c.set_removed(true);
                m_solver.del_clause(c);
                continue; 
            }

            switch (j) {
            case 0:
                m_solver.set_conflict();
                for (; it != end; ++it) {
                    *it2 = *it;
                    it2++;
                }
                cs.set_end(it2);
                return;                
            case 1:
                m_solver.assign_unit(c[0]);
                drat_delete_clause();
                c.set_removed(true);
                m_solver.del_clause(c);
                break;
            case 2:
                m_solver.mk_bin_clause(c[0], c[1], c.is_learned());
                drat_delete_clause();
                c.set_removed(true);
                m_solver.del_clause(c);
                break;
            default:
                SASSERT(*it == &c);
                if (j < sz) {
                    c.shrink(j);
                }
                else {
                    c.update_approx();
                }
                if (m_solver.m_config.m_drat) {
                    m_solver.m_drat.add(c, true);
                    drat_delete_clause();
                }

                DEBUG_CODE(for (literal l : c) VERIFY(l == norm(roots, l)););
                
                *it2 = *it;
                it2++;
                if (!c.frozen()) {
                    m_solver.attach_clause(c);
                }
                break;
            }
        }
        cs.set_end(it2);
    }

    void elim_eqs::save_elim(literal_vector const & roots, bool_var_vector const & to_elim) {
        model_converter & mc = m_solver.m_mc;
        for (bool_var v : to_elim) {
            literal  l(v, false);
            literal r  = roots[v];
            SASSERT(v != r.var());
            if (m_solver.m_cut_simplifier) m_solver.m_cut_simplifier->set_root(v, r);
            bool set_root = m_solver.set_root(l, r);
            bool root_ok = !m_solver.is_external(v) || set_root;
            if (m_solver.is_assumption(v) || (m_solver.is_external(v) && (m_solver.is_incremental() || !root_ok))) {
                // cannot really eliminate v, since we have to notify extension of future assignments
                if (m_solver.m_config.m_drat && m_solver.m_config.m_drat_file.is_null()) {
                    std::cout << "DRAT\n";
                    m_solver.m_drat.add(~l, r, true);
                    m_solver.m_drat.add(l, ~r, true);
                }
                m_solver.mk_bin_clause(~l, r, false);
                m_solver.mk_bin_clause(l, ~r, false);
            }
            else {
                model_converter::entry & e = mc.mk(model_converter::ELIM_VAR, v);
                TRACE("save_elim", tout << "marking as deleted: " << v << " l: " << l << " r: " << r << "\n";);
                m_solver.set_eliminated(v, true);
                mc.insert(e, ~l, r);
                mc.insert(e,  l, ~r);
            }
        }
        m_solver.flush_roots();
    }

    bool elim_eqs::check_clause(clause const& c, literal_vector const& roots) const {
        for (literal l : c) {
            CTRACE("elim_eqs_bug", m_solver.was_eliminated(l.var()), tout << "lit: " << l << " " << norm(roots, l) << "\n";
                   tout << c << "\n";);
            if (m_solver.was_eliminated(l.var())) {
                IF_VERBOSE(0, verbose_stream() << c << " contains eliminated literal " << l << " " << norm(roots, l) << "\n";);
                UNREACHABLE();
            }
        }
        return true;
    }


    bool elim_eqs::check_clauses(literal_vector const & roots) const {
        for (clause * cp : m_solver.m_clauses)
            if (!check_clause(*cp, roots)) 
                return false;
        for (clause * cp : m_solver.m_learned)
            if (!check_clause(*cp, roots)) 
                return false;
        return true;
    }

    void elim_eqs::operator()(literal_vector const & roots, bool_var_vector const & to_elim) {
        TRACE("elim_eqs", tout << "before bin cleanup\n"; m_solver.display(tout););
        cleanup_bin_watches(roots);
        TRACE("elim_eqs", tout << "after bin cleanup\n"; m_solver.display(tout););
        cleanup_clauses(roots, m_solver.m_clauses);
        if (m_solver.inconsistent()) return;
        cleanup_clauses(roots, m_solver.m_learned);
        if (m_solver.inconsistent()) return;
        save_elim(roots, to_elim);
        m_solver.propagate(false);
        SASSERT(check_clauses(roots));
        TRACE("elim_eqs", tout << "after full cleanup\n"; m_solver.display(tout););
    }

    void elim_eqs::operator()(union_find<>& uf) {
        literal_vector roots(m_solver.num_vars(), null_literal);
        bool_var_vector to_elim;
        for (unsigned i = m_solver.num_vars(); i-- > 0; ) {
            literal l1(i, false);
            unsigned idx = uf.find(l1.index());
            if (idx != l1.index()) {
                roots[i] = to_literal(idx);
                to_elim.push_back(i);
            }
            else {
                roots[i] = l1;
            }
        }
        (*this)(roots, to_elim);
    }
};
