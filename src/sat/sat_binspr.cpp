/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_binspr.cpp

  Abstract:
   
    Inprocessing step for creating SPR binary clauses.

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-29

  Notes:

  Alternative loop is to prune candidate pairings to p 
  with respect to failed literals.
  
  Candidates = literals
  for p in literals: 
      push(1)
      propagate(p)
      for (C or p) in use(p):
          push(1)
          propagate(~C)
          if (!inconsistent()): 
             for q in Candidates, q is unassigned
                 push(1)
                 propagate(q)
                 if (!inconsistent()):
                    update G, Candidates for C or p
                 pop(1)
             for q in C or ~q in C, q in Candidates, q != p
                 update G, Candidates for C or p or q or C or p or ~q
          pop(1)
      for (q, G) in Candidates:
          for (C or q) in use(q):
              push(1)
              propagate(~C) (remove p if p in C)
              if (!inconsistent):
                  update G, Candidates for C or q
              pop(1)
      pop(1)

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
            IF_VERBOSE(2, verbose_stream() << " (sat-binspr :binary " << nb << m_watch << ")\n");
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
        unsigned offset = m_stopped_at;
        for (unsigned i = 0, count = 0; i < num && count <= m_limit1 && !s.inconsistent(); ++i) {
            s.checkpoint();
            bool_var v = (offset + i) % num;
            m_stopped_at = v;
            if (s.value(v) == l_undef && !s.was_eliminated(v)) {
                literal lit1(v, false);
                check_spr(big, lit1);            
                check_spr(big, ~lit1);            
                ++count;
            }
        }        
        m_limit1 *= 2;
        m_limit2 *= 2;
    }
    
    void binspr::check_spr(big & big, literal lit1) {
        // if (!big.is_root(lit1)) return;
        TRACE("sat", tout << lit1 << "\n";);
        s.push();
        s.assign_scoped(lit1);
        s.propagate(false);
        unsigned num = s.num_vars() - lit1.var() - 1;
        unsigned start = s.rand()(); 
        // break symmetries: only consider variables larger than lit1
        for (unsigned i = 0, count = 0; i < num && count <= m_limit2 && !s.inconsistent(); ++i) {
            bool_var v = ((i + start) % num) + lit1.var() + 1;
            s.checkpoint();
            if (s.value(v) == l_undef && !s.was_eliminated(v)) {
                literal lit2(v, false);
                check_spr(big, lit1, lit2);            
                check_spr(big, lit1, ~lit2);            
                ++count;
            }
        }
        if (s.inconsistent()) {
            s.pop(1);
            s.assign_unit(~lit1);
            s.propagate(false);
        }
        else {
            s.pop(1);
        }
    }

    void binspr::check_spr(big& big, literal lit1, literal lit2) {
        // if (!big.is_root(lit2)) return;
        s.push();
        reset_g(lit1, lit2);
        s.assign_scoped(lit2);
        s.propagate(false);
        if (s.inconsistent()) {
            s.pop(1);
            block_binary(lit1, lit2, true);
            s.propagate(false);
        }
        else if (binary_are_unit_implied(lit1, lit2) &&
                 binary_are_unit_implied(lit2, lit1) &&
                 clauses_are_unit_implied(lit1, lit2) &&
                 clauses_are_unit_implied(lit2, lit1)) {
            s.pop(1);
            block_binary(lit1, lit2, false);
            s.propagate(false);
        }
        else {
            s.pop(1);
        }
    }

    void binspr::block_binary(literal lit1, literal lit2, bool learned) {
        s.mk_clause(~lit1, ~lit2, learned);
        ++m_bin_clauses;
    }

    bool binspr::binary_are_unit_implied(literal lit1, literal lit2) {
        if (m_units.contains(lit1)) return true;
        for (watched const& w : s.get_wlist(~lit1)) {
            if (!w.is_binary_non_learned_clause()) {
                continue;
            }
            literal lit3 = w.get_literal();
            SASSERT(lit3 != lit1);
            bool is_implied = true;
            if (lit3 == lit2) {
                is_implied = add_g(lit1, lit2);
            }
            else if (s.value(lit3) == l_true) {
                continue;
            }
            else if (s.value(lit3) == l_false) {
                return add_g(lit1);
            }
            else {
                s.push();
                s.assign_scoped(~lit3);
                s.propagate(false);
                is_implied = s.inconsistent() || add_g(lit1);
                s.pop(1);
            }
            if (!is_implied) {
                return false;
            }
        }
        return true;
    }

    void binspr::reset_g(literal lit1, literal lit2) {
        m_units.reset();
        m_bins.reset();
        m_bins.push_back(std::make_pair(~lit1, ~lit2));
    }

    // If we allow the case where G is non-empty there are the
    // following cases for clauses in G:
    // lit1
    // lit2
    // ~lit1
    // ~lit2
    //  (lit1 or  lit2)
    // (~lit1 or ~lit2)  **
    // (~lit1 or  lit2)
    //  (lit1 or ~lit2)
    // Given that satisfiability is checked with respect to **
    // additional clauses create either equivalence constraints
    // or units.
    bool binspr::add_g(literal lit1, literal lit2) {
        if (lit1 == lit2) {
            return add_g(lit1);
        }
        if (lit1 == ~lit2) {
            return true;
        }
        for (literal lit3 : m_units) {
            if (lit3 == lit1 || lit3 == lit2) return true;
            if (lit3 == ~lit1) return add_g(lit2);
            if (lit3 == ~lit2) return add_g(lit1);
        } 
        SASSERT(m_units.empty());
        if (lit1.var() > lit2.var()) {
            std::swap(lit1, lit2);
        }
        for (auto const& p : m_bins) {
            if (p.first == lit1  && p.second ==  lit2) return true;
            if (p.first == ~lit1 && p.second ==  lit2) return add_g(lit2);
            if (p.first == lit1  && p.second == ~lit2) return add_g(lit1);
            // if (p.first == ~lit1 && p.second == ~lit2) continue;            
        }
        m_bins.push_back(std::make_pair(lit1, lit2));
        return true;
    }

    bool binspr::add_g(literal lit1) {
        for (literal lit2 : m_units) {
            if (lit2 == lit1) return true;
            if (lit2 == ~lit1) return false;
        }
        m_units.push_back(lit1);
        bool r = true;
        for (auto const& p : m_bins) {
            if (p.first == ~lit1) {
                r = add_g(p.second);
                break;
            }
            if (p.second == ~lit1) {
                r = add_g(p.first);
                break;
            }
        }
        m_bins.reset();
        return r;
    }

    bool binspr::clauses_are_unit_implied(literal lit1, literal lit2) {        
        for (clause* cp : m_use_list[lit1.index()]) {
            if (!clause_is_unit_implied(lit1, lit2, *cp)) {
                return false;
            }
            if (m_units.contains(lit1)) {
                break;
            }
        }
        return true;
    }

    bool binspr::clause_is_unit_implied(literal lit1, literal lit2, clause& c) {
        if (c.was_removed()) {
            return true;
        }
        literal lit2_ = lit1;
        bool is_implied = false;
        bool found = false;
        s.push();
        for (literal lit : c) {
            if (lit == lit1) {
                found = true;
            }
            else if (lit.var() == lit2.var()) {
                lit2_ = lit2;
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
        if (!is_implied) {
            is_implied = add_g(lit1, lit2_);
        }
        s.pop(1);
        return is_implied;
    }


}

