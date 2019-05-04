/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_binspr.cpp

  Abstract:
   
    Inprocessing step for creating SPR binary clauses.

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-29

  Notes:
  

  --*/

#include "sat/sat_binspr.h"
#include "sat/sat_solver.h"
#include "sat/sat_big.h"

namespace sat {

    struct binspr::report {
        binspr& m_binspr;
        stopwatch m_watch;
        report(binspr& b): 
            m_binspr(b) {
            m_watch.start();
        }
        ~report() {
            m_watch.stop();
            unsigned nb = m_binspr.m_bin_clauses;
            IF_VERBOSE(2, verbose_stream() << " (sat-binspr :binary " << nb << " " << mem_stat() << m_watch << ")\n");
        }
            
    };

    void binspr::operator()() {
        unsigned num = s.num_vars();

        report _rep(*this);

        big big(s.rand());        
        big.init(s, true);
        m_use_list.reset();
        m_use_list.reserve(num*2);
        for (clause* c : s.m_clauses) {
            if (!c->frozen()) 
                for (literal lit : *c) {
                    m_use_list[lit.index()].push_back(c);
                }
        }
        
        m_bin_clauses = 0;

        for (unsigned i = 0, count = 0; i < num && count <= m_limit1 && !s.inconsistent(); ++i) {
            s.checkpoint();
            bool_var v = (m_stopped_at + i) % num;
            m_stopped_at = v;
            if (s.value(v) != l_undef || s.was_eliminated(v)) {
                continue;
            }
            literal lit1(v, false);
            if (big.is_root(lit1)) {
                check_spr(big, lit1);
            }
            lit1.neg();
            if (big.is_root(lit1)) {
                check_spr(big, lit1);
            }
            ++count;
        }        
        m_limit1 *= 2;
        m_limit2 *= 2;
    }
    
    void binspr::check_spr(big& big, literal lit1) {
        TRACE("sat", tout << lit1 << "\n";);
        s.push();
        s.assign_scoped(lit1);
        s.propagate(false);
        if (s.inconsistent()) {
            s.pop(1);
            s.assign_unit(~lit1);
            return;
        }
        unsigned num = s.num_vars() - lit1.var() - 1;
        unsigned start = s.rand()(); 
        // break symmetries: only consider variables larger than lit1
        for (unsigned i = 0, count = 0; i < num && count <= m_limit2; ++i) {
            bool_var v = ((i + start) % num) + lit1.var() + 1;
            s.checkpoint();
            if (s.value(v) != l_undef || s.was_eliminated(v)) {
                continue;
            }
            literal lit2(v, false);
            if (big.is_root(lit2)) {
                check_spr(lit1, lit2);
            }
            lit2.neg();
            if (big.is_root(lit2)) {
                check_spr(lit1, lit2);
            }
            ++count;
        }
        s.pop(1);
    }

    void binspr::check_spr(literal lit1, literal lit2) {
        s.push();
        s.assign_scoped(lit2);
        s.propagate(false);
        if (s.inconsistent()) {
            block_binary(lit1, lit2, true);
        }
        else {
            if (binary_are_unit_implied(lit1) &&
                binary_are_unit_implied(lit2) &&
                clauses_are_unit_implied(lit1, lit2) &&
                clauses_are_unit_implied(lit2, lit1)) {
                // claim: SPR is confluent for binary clauses when G is empty.
                // In other words, we can add binary clauses at will without
                // considering the effect of adding a binary clause.
                // Thus, we can just add learned binary clauses.
                // If we allow the case where G is non-empty there are the
                // following cases for clauses in G:
                // lit1
                // lit2
                // ~lit1
                // ~lit2
                // (lit1 or lit2)
                // (~lit1 or ~lit2)  **
                // (~lit1 or lit2)
                // (lit1 or ~lit2)
                // Given that satisfiability is checked with respect to **
                // additional clauses create either equivalence constraints
                // or units.
                block_binary(lit1, lit2, false);
            }
        }
        s.pop(1);
    }

    void binspr::block_binary(literal lit1, literal lit2, bool learned) {
        s.mk_clause(~lit1, ~lit2, learned);
        ++m_bin_clauses;
    }

    bool binspr::binary_are_unit_implied(literal lit) {
        for (watched const& w : s.get_wlist(lit)) {
            if (w.is_binary_clause() && s.value(w.get_literal()) != l_true) {
                TRACE("sat", tout << "Binary clause not unit implied " << lit << " " << w.get_literal() << "\n";);
                return false;
            }
        }
        return true;
    }

    bool binspr::clauses_are_unit_implied(literal lit1, literal lit2) {        
        for (clause* cp : m_use_list[lit1.index()]) {
            if (!clause_is_unit_implied(lit1, lit2, *cp)) {
                return false;
            }
        }
        return true;
    }

    bool binspr::clause_is_unit_implied(literal lit1, literal lit2, clause& c) {
        if (c.was_removed()) {
            return true;
        }
        bool is_implied = false;
        bool found = false;
        s.push();
        for (literal lit : c) {
            if (lit == lit1 || lit == lit2) {
                found = true;
            }
            else if (s.value(lit) == l_true) {
                is_implied = true;
                break;
            }
            else if (s.value(lit) != l_false) {
                s.assign_scoped(~lit);
            }
        }
        SASSERT(found);
        if (!is_implied) {
            s.propagate(false);
            is_implied = s.inconsistent();
            CTRACE("sat", !is_implied, tout << "not unit implied " << lit1 << " " << lit2 << ": " << c << "\n";);            
        }
        s.pop(1);
        return is_implied;
    }


}

