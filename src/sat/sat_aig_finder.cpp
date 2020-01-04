/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_finder.cpp

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  
    AIG finder

  --*/

#pragma once;

#include "sat/sat_aig_finder.h"

namespace sat {

    void aig_finder::operator()(clause_vector const& clauses) {
        m_big.init(s, true);

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() <= 2) continue;
            if (find_aig(c)) continue;
            if (find_if(c)) continue;
        }
    }

    bool aig_finder::implies(literal a, literal b) {
        if (m_big.connected(a, b)) 
            return true;
        for (auto const& w : s.get_wlist(a)) {
            if (w.is_binary_clause() && b == w.get_literal()) 
                return true;
        }
        return false;
    }

    // a = ~b & ~c 
    //        if (~a | ~b) (~a | ~c), (b | c | a)

    bool aig_finder::find_aig(clause& c) {
        bool is_aig = false;
        for (literal head : c) {
            is_aig = true;
            for (literal tail : c) {
                if (head == tail) 
                    continue;
                if (!implies(head, ~tail)) {
                    is_aig = false;
                    break;
                }
            }
            if (is_aig) {
                m_ands.reset();
                for (literal tail : c) 
                    if (tail != head) 
                        m_ands.push_back(~tail);
                m_aig_def(head, m_ands, c);
                break;
            }
        }
        return is_aig;
    }

    //
    // x = if y then z else u
    //       if x, y -> z
    //          x, ~y -> u
    //          y, z -> x
    //          ~y, u -> x
    // 

    bool aig_finder::find_if(clause& c) {
        return false;
#if 0
        if (c.size() != 3) return false;

        literal x = c[0], y = c[1], z = c[2];
        if (find_if(~x, ~y, z, c)) return true;
        if (find_if(~x, ~z, y, c)) return true;
        if (find_if(~y, ~x, z, c)) return true;
        if (find_if(~y, ~z, x, c)) return true;
        if (find_if(~z, ~x, y, c)) return true;
        if (find_if(~z, ~y, x, c)) return true;
        return false;
#endif

    }

#if 0
    
    // x, y -> z
    // x, ~y -> u
    // y, z -> x
    // ~y, u -> x

    // x + yz + (1 + y)u = 0

    bool aig_finder::check_if(literal x, literal y, literal z, clause& c) {
        clause* c2 = find_clause(~y, ~z, x);
        if (!c2) {
            return false;
        }
        for (clause* c3 : ternay_clauses_with(~x, y)) {
            literal u = third_literal(~x, y, *c3);
            clause* c4 = find_clause(y, ~u, x);
            if (c4) {
                m_if_def(x, y, z, u, c, *c2, *c3, *c4);
                return true;
            }
        }
    }

    literal aig_finder::third_literal(literal a, literal b, clause const& c) {
        for (literal lit : c) 
            if (lit != a && lit != b)
                return lit;
        return null_literal;
    }

    clause* aig_finder::find_clause(literal a, literal b, literal c) {
        for (auto const& w : s.get_wlist(~a)) {
            if (w.is_ternary() &&
                (b == w.get_literal1() && c == w.get_literal2()) || 
                (c == w.get_literal1() && b == w.get_literal2())) {
                for (clause* cp : s.clauses()) {
                    clause& cl = *cp;

#define pair_eq(a, b, x, y) ((a == x && b == y) || (a == y && b == x))
#define tern_eq(a, b, c, cl)                                            \
                    cl.size() == 3 &&                                   \
                        ((cl[0] == a && pair_eq(b, c, c1[1], c1[2])) || \
                         (cl[0] == b && pair_eq(a, c, cl[1], cl[2])) || \
                         (cl[0] == c && pair_eq(a, b, cl[1], cl[2]))))

                    if (tern_eq(a, b, c, *cp)) return cp;
                }
            }
            if (w.is_clause() && tern_eq(a, b, c, s.get_clause(w)))
                return &s.get_clause(w);
        }
        return nullptr;
    }
#endif

}
