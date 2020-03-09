/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_binspr.cpp

  Abstract:
   
    Inprocessing step for creating SPR binary clauses.

  Author:

    Nikolaj Bjorner, Marijn Heule 2019-4-29

  Notes:


  L = { lit1, lit2 }
  G := { touched_L(C) |  C in F and C intersects with L, and not F|L |-_unit untouch_L(C) }
  G & ~L is satisfiable
  ------------
  Learn ~lit1 or ~lit2


Marijn's version:

  L = { lit1, lit2 }
  alpha = L + units in F|L
  G := { touched_alpha(C) |  C in F and C intersects with L, and not F|L |-_unit untouch_alpha(C) }
  G & ~L is satisfiable
  ---------------------
  Learn ~L

    


  Alternative:   

  for p in literals:
      push(1)
      propagate(p)
      candidates = literals \ units
      for (C or p) in use(p) and candidates != empty:
          push(1)
          propagate(~C)
          if inconsistent():
             learn C (subsumes C or p)
          else:
             candidates' := C union ~(consequencs of propagate(~C))
             candidates  := candidates' intersect candidates
          pop(1)
      for q in candidates:
          add (~q or ~p)
      pop(1) 

  The idea is that all clauses using p must satisfy 
      q in C or F|pq |-1 untouched(C)
  The clauses that contain q are not restricted: We directly create G := (~p or ~q) & q, which is satisfiable
  Let pqM |= F, we claim then that ~pqM |= F 
  
  - every clause (C or q) that contains q is satisfied by ~pqM
  - every clause (C or p) that does not contain q positively, but contains p satisfies F|pq |-1 untouched(C)
    Therefore pqM |= untouched(C) and therefore already M |= untouched(C)
  - all other clauses are satisfied by pqM, but contain neither p, nor q, 
    so it is already the case that M satisfies the clause.

  Alternative:

  for p in literals:
      push(1)
      propagate(p)
      candidates = {}
      for (C or p) in use(p):
          push(1)
          propagate(~C)
          if inconsistent():
             learn C (subsumes C or p)
          else:
             candidates := candicates union C union ~(consequencs of propagate(~C))
          pop(1)
      for q in candidates:
          push(1)
          propagate(q)
          incons := true
          for (C or p) in use(p) and incons:
              push(1)
              propagate(~C)
              incons := inconsistent()
              pop(1)
          pop(1)
          if incons:
             add (~p or ~q)
      pop(1) 

  The idea is similar to the previous alternative, but it allows a candidate to
  not be directly unit derivable in all clauses C or p, but could be a failed literal
  under the assumption ~C. 
  The motivation for this variant is that it is unlikely that we need failed literals to
  close both (C_1 or p),..., (C_n or p) for all clauses containing p.

  Alternative:


  1. extract BIG
     Use BIG to limit cone enumeration
  2. for each literal lit:
        enumerate k1 in cone of lit
           enumerate lit2 in use(~k1)
              check if cone of lit2 contains k2 such that lit1 in use(~k2)

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
        s = alloc(solver, m_solver.params(), m_solver.rlimit());
        m_solver.pop_to_base_level();
        s->copy(m_solver, true);
        unsigned num = s->num_vars();
        m_bin_clauses = 0;

        report _rep(*this);
        m_use_list.reset();
        m_use_list.reserve(num * 2);
        for (clause* c : s->m_clauses) {
            if (!c->frozen() && !c->was_removed()) { 
                for (literal lit : *c) {
                    m_use_list[lit.index()].push_back(c);
                }
            }
        }
        TRACE("sat", s->display(tout););
        algorithm2();
        if (!s->inconsistent()) {
            params_ref p;
            p.set_uint("sat.max_conflicts", 10000);
            p.set_bool("sat.binspr", false);
            s->updt_params(p);
            s->check(0, nullptr);
        }

        if (s->inconsistent()) {
            s->set_conflict();
        }
        else {
            s->pop_to_base_level();
            for (unsigned i = m_solver.init_trail_size(); i < s->init_trail_size(); ++i) {
                literal lit = s->trail_literal(i);
                m_solver.assign(lit, s->get_justification(lit));
            }
            TRACE("sat", tout << "added " << (s->init_trail_size() - m_solver.init_trail_size()) << " units\n";);
        }
    }


    /**
       F, p |- ~u, 
       F, p, q |- ~v, 
       { p, v } u C in F
       { q, u } u D in F
  
       Then use { p, ~u, q, ~v } as alpha, L = { p, q }

      for u in ~consequences of p:
          for (u u D) in use(u):
              for q in D, unassigned:              
                  for v in ~consequences(q) | ({p, v} u C) in use(v):
                   check_spr(p, q, u, v)                
    */

    void binspr::algorithm2() {
        mk_masks();
        unsigned num_lits = 2 * s->num_vars();
        for (unsigned l_idx = 0; l_idx < num_lits && !s->inconsistent(); ++l_idx) {
            s->checkpoint();
            literal p = to_literal(l_idx);
            TRACE("sat", tout << "p " << p << " " << s->value(p) << "\n";);
            if (is_used(p) && s->value(p) == l_undef) {
                s->push();
                s->assign_scoped(p);
                unsigned sz_p = s->m_trail.size();
                s->propagate(false);
                if (s->inconsistent()) {
                    s->pop(1);
                    s->assign_unit(~p);
                    s->propagate(false);
                    TRACE("sat", s->display(tout << "unit\n"););
                    IF_VERBOSE(0, verbose_stream() << "unit " << (~p) << "\n");
                    continue;
                }
                for (unsigned i = sz_p; !s->inconsistent() && i < s->m_trail.size(); ++i) {
                    literal u = ~s->m_trail[i];
                    TRACE("sat", tout << "p " << p << " u " << u << "\n";);
                    for (clause* cp : m_use_list[u.index()]) {
                        for (literal q : *cp) {
                            if (s->inconsistent()) 
                                break;
                            if (s->value(q) != l_undef) 
                                continue;

                            s->push();
                            s->assign_scoped(q);
                            unsigned sz_q = s->m_trail.size();
                            s->propagate(false);
                            if (s->inconsistent()) {
                                // learn ~p or ~q
                                s->pop(1);
                                block_binary(p, q, true);
                                s->propagate(false);
                                continue;
                            }
                            bool found = false;
                            for (unsigned j = sz_q; !found && j < s->m_trail.size(); ++j) {
                                literal v = ~s->m_trail[j];
                                for (clause* cp2 : m_use_list[v.index()]) {                                    
                                    if (cp2->contains(p)) {
                                        if (check_spr(p, q, u, v)) {
                                            found = true;
                                            break;
                                        }
                                    }
                                }
                            }
                            s->pop(1);
                            if (found) {
                                block_binary(p, q, false);
                                s->propagate(false);
                                TRACE("sat", s->display(tout););
                            }
                        }
                    }
                }
                s->pop(1);
            }
        }               
    }

    bool binspr::is_used(literal lit) const {
        return !m_use_list[lit.index()].empty() || !s->get_wlist(~lit).empty();
    }
    
    bool binspr::check_spr(literal p, literal q, literal u, literal v) {
        SASSERT(s->value(p) == l_true);
        SASSERT(s->value(q) == l_true);
        SASSERT(s->value(u) == l_false);
        SASSERT(s->value(v) == l_false);
        init_g(p, q, u, v);
        literal lits[4] = { p, q, ~u, ~v };
        for (unsigned i = 0; g_is_sat() && i < 4; ++i) {
            binary_are_unit_implied(lits[i]);
            clauses_are_unit_implied(lits[i]);
        }
        TRACE("sat", tout << p << " " << q << " " << u << " " << v << " " << g_is_sat() << "\n";);
        return g_is_sat();
    }

    void binspr::binary_are_unit_implied(literal p) {
        for (watched const& w : s->get_wlist(~p)) {
            if (!g_is_sat()) {
                break;
            }
            if (!w.is_binary_non_learned_clause()) {
                continue;
            }            

            clear_alpha();
            VERIFY(touch(p));
            literal lit = w.get_literal();
            SASSERT(lit != p);
            
            if (touch(lit)) {
                add_touched();
                continue;
            }

            bool inconsistent = (s->value(lit) == l_true);
            if (s->value(lit) == l_undef) {
                s->push();
                s->assign_scoped(~lit);
                s->propagate(false);
                inconsistent = s->inconsistent();
                s->pop(1);
            }

            if (!inconsistent) {            
                TRACE("sat", tout << "not implied: " << p << " " << lit << "\n";);
                m_state = 0;
                add_touched();
            }
        }
    }

    void binspr::clauses_are_unit_implied(literal p) {
        for (clause* cp : m_use_list[p.index()]) {
            if (!g_is_sat()) break;
            clause_is_unit_implied(*cp);
        }
    }

    void binspr::clause_is_unit_implied(clause const& c) {
        s->push();
        clear_alpha();
        for (literal lit : c) {
            if (touch(lit)) {
                continue;
            }
            else if (s->value(lit) == l_true) {
                s->pop(1);
                return;
            }
            else if (s->value(lit) != l_false) {
                s->assign_scoped(~lit);
            }
        }
        s->propagate(false);
        bool inconsistent = s->inconsistent();
        s->pop(1);
        if (!inconsistent) {
            add_touched();
        }
    }


    void binspr::block_binary(literal lit1, literal lit2, bool learned) {
        IF_VERBOSE(2, verbose_stream() << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n");
        TRACE("sat", tout << "SPR: " << learned << " " << ~lit1 << " " << ~lit2 << "\n";);
        s->mk_clause(~lit1, ~lit2, learned);
        ++m_bin_clauses;
    }

    void binspr::g_add_unit(literal lit1, literal lit2) {
        if (lit1.var() < lit2.var()) {
            m_state &= 0x2;
        }
        else {
            m_state &= 0x4;
        }
    }

    void binspr::g_add_binary(literal lit1, literal lit2, bool flip2) {
        bool flip1 = false;
        if (lit1.var() > lit2.var()) { std::swap(flip1, flip2); }
        m_state &= ((flip1?0x5:0xA) | (flip2?0x3:0xC)); 
    }

    // 0 -> 10
    // 1 -> 01
    // * -> 11
    // 00 -> 1000
    // 10 -> 0100
    // 01 -> 0010
    // 11 -> 0001
    // *1 -> 00110011
    // *0 -> 11001100
    // 0* -> 10101010
    // 1* -> 01010101
    // **1 -> 00001111
    // **0 -> 11110000

    /**
       \brief create masks (lsb is left)
       i = 0: 1010101010101010
       i = 1: 1100110011001100
       i = 2: 1111000011110000
     */
    unsigned binspr::mk_mask(unsigned i) {
        // variable number i is false.
        unsigned mask0 = (1 << (1 << i)) - 1;  // 2^i bits of ones
        unsigned pos = 1 << (i+1);                  // how many bits in mask 

        unsigned mask = mask0;
        while (pos < 32) {
            mask |= (mask0 << pos);
            pos += 1 << (i + 1);
        }
        return mask;
    }

    void binspr::mk_masks() {
        for (unsigned i = 0; i < max_lits; ++i) {
            m_false[i] = mk_mask(i);
            m_true[i]  = m_false[i] << (1 << i);
        }
    }

    /**
       \brief create Boolean function table
       corresponding to disjunction of literals
    */
    
    void binspr::add_touched() {

        unsigned mask = 0;
        for (unsigned i = 0; i < 4; ++i) {
            switch (m_vals[i]) {
            case l_true:
                mask |= m_true[i];
                break;
            case l_false:
                mask |= m_false[i];
                break;
            default:
                break;
            }
        }
        m_state &= mask;
        TRACE("sat", 
              {
                  bool_var vars[4];
                  vars[0] = m_p; vars[1] = m_q; vars[2] = m_u; vars[3] = m_v;
                  tout << "touched: ";
                  for (unsigned i = 0; i < 4; ++i) {
                      switch (m_vals[i]) {
                      case l_true:
                          tout << literal(vars[i], false) << " ";
                          break;
                      case l_false:
                          tout << literal(vars[i], true) << " ";
                          break;
                      default:
                          break;
                      }
                  }
                  display_mask(tout << "  ", m_state);
              });
    }

    void binspr::init_g(literal p, literal q, literal u, literal v) {
        m_p = p.var();
        m_q = q.var();
        m_u = u.var();
        m_v = v.var();
        m_state = ~0;
        clear_alpha();
        VERIFY(touch(~p));
        VERIFY(touch(~q));
        add_touched();
    }

    void binspr::clear_alpha() {
        m_vals[0] = m_vals[1] = m_vals[2] = m_vals[3] = l_undef;
    }

    bool binspr::touch(literal p) {
        bool_var v = p.var();
        if (v == m_p) m_vals[0] = to_lbool(!p.sign());
        else if (v == m_q) m_vals[1] = to_lbool(!p.sign());
        else if (v == m_u) m_vals[2] = to_lbool(!p.sign());
        else if (v == m_v) m_vals[3] = to_lbool(!p.sign());
        else return false;
        return true;
    }

    std::ostream& binspr::display_mask(std::ostream& out, unsigned mask) const {
        for (unsigned i = 0; i < 4; ++i) {
            out << m_vals[i] << " ";
        }
        out << " - ";
        for (unsigned i = 0; i < 32; ++i) {
            out << (0 != (mask & (1 << i)) ? 1 : 0);           
        }
        return out << "\n";
    }
}

