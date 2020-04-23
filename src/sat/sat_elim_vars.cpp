/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_elim_vars.cpp

Abstract:

    Helper class for eliminating variables

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-14

Revision History:

--*/

#include "sat/sat_simplifier.h"
#include "sat/sat_elim_vars.h"
#include "sat/sat_solver.h"

namespace sat{

    elim_vars::elim_vars(simplifier& s) : simp(s), s(s.s), m(20) {
        m_mark_lim = 0;
        m_max_literals = 11; 
        m_miss = 0;
        m_hit1 = 0;
        m_hit2 = 0;
    }

    bool elim_vars::operator()(bool_var v) {
        if (s.value(v) != l_undef)
            return false;

        literal pos_l(v, false);
        literal neg_l(v, true);
        unsigned num_bin_pos = simp.num_nonlearned_bin(pos_l);
        if (num_bin_pos > m_max_literals) return false;
        unsigned num_bin_neg = simp.num_nonlearned_bin(neg_l);
        if (num_bin_neg > m_max_literals) return false;
        clause_use_list & pos_occs = simp.m_use_list.get(pos_l);
        clause_use_list & neg_occs = simp.m_use_list.get(neg_l);
        unsigned clause_size = num_bin_pos + num_bin_neg + pos_occs.num_irredundant() + neg_occs.num_irredundant();
        if (clause_size == 0) {
            return false;
        }
        reset_mark();
        mark_var(v);
        if (!mark_literals(pos_occs)) return false;
        if (!mark_literals(neg_occs)) return false;
        if (!mark_literals(pos_l)) return false;
        if (!mark_literals(neg_l)) return false;
        
        // associate index with each variable.
        sort_marked();
        dd::bdd b1 = elim_var(v);
        double sz1 = b1.cnf_size();
        if (sz1 > 2*clause_size) {
            ++m_miss;
            return false;
        }        
        if (sz1 <= clause_size) {
            ++m_hit1;
            return elim_var(v, b1);
        }
        m.try_cnf_reorder(b1);
        sz1 = b1.cnf_size();
        if (sz1 <= clause_size) {
            ++m_hit2;
            return elim_var(v, b1);
        } 
        ++m_miss;
        return false;
    }

    bool elim_vars::elim_var(bool_var v, dd::bdd const& b) {
        literal pos_l(v, false);
        literal neg_l(v, true);
        clause_use_list & pos_occs = simp.m_use_list.get(pos_l);
        clause_use_list & neg_occs = simp.m_use_list.get(neg_l);

        // eliminate variable
        simp.m_pos_cls.reset();
        simp.m_neg_cls.reset();
        simp.collect_clauses(pos_l, simp.m_pos_cls);
        simp.collect_clauses(neg_l, simp.m_neg_cls);
        VERIFY(!simp.is_external(v));

        model_converter::entry & mc_entry = s.m_mc.mk(model_converter::ELIM_VAR, v);
        simp.save_clauses(mc_entry, simp.m_pos_cls);
        simp.save_clauses(mc_entry, simp.m_neg_cls);
        s.m_eliminated[v] = true;
        ++s.m_stats.m_elim_var_bdd;
        simp.remove_bin_clauses(pos_l);
        simp.remove_bin_clauses(neg_l);
        simp.remove_clauses(pos_occs, pos_l);
        simp.remove_clauses(neg_occs, neg_l);
        pos_occs.reset();
        neg_occs.reset();
        literal_vector lits;
        add_clauses(v, b, lits);         
        return true;
    }

    dd::bdd elim_vars::elim_var(bool_var v) {
        unsigned index = 0;
        for (bool_var w : m_vars) {
            m_var2index[w] = index++;
        }
        literal pos_l(v, false);
        literal neg_l(v, true);
        clause_use_list & pos_occs = simp.m_use_list.get(pos_l);
        clause_use_list & neg_occs = simp.m_use_list.get(neg_l);

        dd::bdd b1 = make_clauses(pos_l);
        dd::bdd b2 = make_clauses(neg_l);
        dd::bdd b3 = make_clauses(pos_occs);
        dd::bdd b4 = make_clauses(neg_occs);
        dd::bdd b0 = b1 && b2 && b3 && b4;
        dd::bdd b =  m.mk_exists(m_var2index[v], b0);       
        TRACE("elim_vars",
              tout << "eliminate " << v << "\n";
              for (watched const& w : simp.get_wlist(~pos_l)) {
                  if (w.is_binary_non_learned_clause()) {
                      tout << pos_l << " " << w.get_literal() << "\n";
                  }
              }
              m.display(tout, b1);
              for (watched const& w : simp.get_wlist(~neg_l)) {
                  if (w.is_binary_non_learned_clause()) {
                      tout << neg_l << " " << w.get_literal() << "\n";
                  }
              }
              m.display(tout, b2);
              clause_use_list::iterator itp = pos_occs.mk_iterator();
              while (!itp.at_end()) {
                  clause const& c = itp.curr();
                  tout << c << "\n";
                  itp.next();
              }
              m.display(tout, b3);
              clause_use_list::iterator itn = neg_occs.mk_iterator();
              while (!itn.at_end()) {
                  clause const& c = itn.curr();
                  tout << c << "\n";
                  itn.next();
              }
              m.display(tout, b4);
              tout << "eliminated:\n";
              tout << b << "\n";
              tout << b.cnf_size() << "\n";
              );

        return b;
    }

    void elim_vars::add_clauses(bool_var v0, dd::bdd const& b, literal_vector& lits) {
        if (b.is_true()) {
            // no-op
        }
        else if (b.is_false()) {
            SASSERT(lits.size() > 0);
            literal_vector c(lits);
            if (simp.cleanup_clause(c)) 
                return;
            
            switch (c.size()) {
            case 0:
                s.set_conflict();
                break;
            case 1: 
                simp.propagate_unit(c[0]);
                break;
            case 2:
                s.m_stats.m_mk_bin_clause++;
                simp.add_non_learned_binary_clause(c[0], c[1]);
                simp.back_subsumption1(c[0], c[1], false);
                break;
            default: {
                if (c.size() == 3)
                    s.m_stats.m_mk_ter_clause++;
                else
                    s.m_stats.m_mk_clause++;
                clause* cp = s.alloc_clause(c.size(), c.c_ptr(), false);
                s.m_clauses.push_back(cp);
                simp.m_use_list.insert(*cp);
                if (simp.m_sub_counter > 0)
                    simp.back_subsumption1(*cp);
                else
                    simp.back_subsumption0(*cp);
                break;
            }
            }
        }
        else {
            unsigned v = m_vars[b.var()];
            lits.push_back(literal(v, false));
            add_clauses(v0, b.lo(), lits);
            lits.pop_back();
            lits.push_back(literal(v, true));
            add_clauses(v0, b.hi(), lits);
            lits.pop_back();
        }
    }


    void elim_vars::get_clauses(dd::bdd const& b, literal_vector & lits, clause_vector& clauses, literal_vector& units) {
        if (b.is_true()) {
            return;
        }
        if (b.is_false()) {
            if (lits.size() > 1) {
                clause* c = s.alloc_clause(lits.size(), lits.c_ptr(), false);
                clauses.push_back(c);
            }
            else {
                units.push_back(lits.back());
            }
            return;
        }

        // if (v hi lo)
        // (v | lo) & (!v | hi)
        // if (v T lo) -> (v | lo) 
        unsigned v = m_vars[b.var()];
        lits.push_back(literal(v, false));
        get_clauses(b.lo(), lits, clauses, units);
        lits.pop_back();
        lits.push_back(literal(v, true));
        get_clauses(b.hi(), lits, clauses, units);
        lits.pop_back();
    }

    void elim_vars::reset_mark() {
        m_vars.reset();
        m_mark.resize(s.num_vars());
        m_var2index.resize(s.num_vars());
        m_occ.resize(s.num_vars());
        ++m_mark_lim;
        if (m_mark_lim == 0) {
            ++m_mark_lim;
            m_mark.fill(0);
        }
    }

    class elim_vars::compare_occ {
        elim_vars& ev;
    public:
        compare_occ(elim_vars& ev):ev(ev) {}

        bool operator()(bool_var v1, bool_var v2) const {
            return ev.m_occ[v1] < ev.m_occ[v2];
        }
    };

    void elim_vars::sort_marked() {
        std::sort(m_vars.begin(), m_vars.end(), compare_occ(*this));
    }

    void elim_vars::shuffle_vars() {
        unsigned sz = m_vars.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned x = m_rand(sz);
            unsigned y = m_rand(sz);
            std::swap(m_vars[x], m_vars[y]);
        }
    }

    void elim_vars::mark_var(bool_var v) {
        if (m_mark[v] != m_mark_lim) {
            m_mark[v] = m_mark_lim;
            m_vars.push_back(v);
            m_occ[v] = 1;
        }
        else {
            ++m_occ[v];
        }
    }

    bool elim_vars::mark_literals(clause_use_list & occs) {
        clause_use_list::iterator it = occs.mk_iterator();
        while (!it.at_end()) {
            clause const& c = it.curr();
            for (literal l : c) {
                mark_var(l.var());
            }
            if (num_vars() > m_max_literals) return false;
            it.next();
        }
        return true;
    }

    bool elim_vars::mark_literals(literal lit) {
        watch_list& wl = simp.get_wlist(lit);
        for (watched const& w : wl) {
            if (w.is_binary_non_learned_clause()) {
                mark_var(w.get_literal().var());
            }
        }
        return num_vars() <= m_max_literals;
    }

    dd::bdd elim_vars::make_clauses(clause_use_list & occs) {
        dd::bdd result = m.mk_true();       
        for (auto it = occs.mk_iterator(); !it.at_end(); it.next()) {
            clause const& c = it.curr();
            dd::bdd cl = m.mk_false();
            for (literal l : c) {
                cl |= mk_literal(l);
            }           
            result &= cl;            
        }
        return result;
    }

    dd::bdd elim_vars::make_clauses(literal lit) {
        dd::bdd result = m.mk_true();
        watch_list& wl = simp.get_wlist(~lit);
        for (watched const& w : wl) {
            if (w.is_binary_non_learned_clause()) {
                result &= (mk_literal(lit) || mk_literal(w.get_literal()));
            }
        }        
        return result;
    }

    dd::bdd elim_vars::mk_literal(literal l) {
        return l.sign() ? m.mk_nvar(m_var2index[l.var()]) : m.mk_var(m_var2index[l.var()]);
    }

};

