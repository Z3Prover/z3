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

    void aig_finder::operator()(clause_vector& clauses) {
        m_big.init(s, true);
        find_aigs(clauses);
        find_ifs(clauses);
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


    void aig_finder::find_aigs(clause_vector& clauses) {
        if (!m_on_aig) {
            return;
        }
        unsigned j = 0;
        for (clause* cp : clauses) {
            clause& c = *cp;
            if (!find_aig(c)) {
                clauses[j++] = cp;
            }
        }
        clauses.shrink(j);
    }

    // a = ~b & ~c 
    //        if (~a | ~b) (~a | ~c), (b | c | a)

    bool aig_finder::find_aig(clause& c) {
        bool is_aig = false;
        if (c.size() <= 2) {
            return false;
        } 
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
                m_on_aig(head, m_ands);
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
    // So there are clauses 
    //        y -> (x = z)
    //        u -> (x = ~y)
    //
    // from clause x, y, z
    // then         ~x, ~y -> z
    // look for     ~y, z -> ~x - contains ternary(y, ~z, ~x)
    // look for     ~x, y -> u  - u is used in a ternary claues (~y, x)
    // look for     y, u -> ~x  - contains ternary(~u, ~x, ~y)
    // then ~x = if ~y then z else u

    void aig_finder::find_ifs(clause_vector& clauses) {

        if (!m_on_if) {
            return;
        }

        for (clause* cp : clauses) cp->unmark_used();

        typedef svector<std::pair<literal, clause*>> use_list_t;
        struct binary {
            literal x, y;
            use_list_t* use_list;
            binary(literal x, literal y, use_list_t* u): x(x), y(y), use_list(u) {
                if (x.index() > y.index()) std::swap(x, y);
            }
            binary():x(null_literal), y(null_literal), use_list(nullptr) {}
            struct hash {
                unsigned operator()(binary const& t) const { return t.x.hash() + 2* t.y.hash(); }
            };
            struct eq {
                bool operator()(binary const& a, binary const& b) const { 
                    return a.x == b.x && a.y == b.y;
                }
            };

        };
        hashtable<binary, binary::hash, binary::eq> binaries;
        scoped_ptr_vector<use_list_t> use_lists;
        auto insert_binary = [&](literal x, literal y, literal z, clause* c) {
            binary b(x, y, nullptr);
            auto* e = binaries.insert_if_not_there2(b);
            if (e->get_data().use_list == nullptr) {
                use_list_t* use_list = alloc(use_list_t);
                use_lists.push_back(use_list);
                e->get_data().use_list = use_list;
            }
            e->get_data().use_list->push_back(std::make_pair(z, c));
        };

        struct ternary {
            literal x, y, z;
            clause* orig;
            ternary(literal x, literal y, literal z, clause* c):
                x(x), y(y), z(z), orig(c) {
                if (x.index() > y.index()) std::swap(x, y);
                if (y.index() > z.index()) std::swap(y, z);
                if (x.index() > y.index()) std::swap(x, y);
            }
            ternary():x(null_literal), y(null_literal), z(null_literal), orig(nullptr) {}
            struct hash {
                unsigned operator()(ternary const& t) const { return mk_mix(t.x.hash(), t.y.hash(), t.z.hash()); }
            };
            struct eq {
                bool operator()(ternary const& a, ternary const& b) const { 
                    return a.x == b.x && a.y == b.y && a.z == b.z; 
                }
            };
        };

        hashtable<ternary, ternary::hash, ternary::eq> ternaries;
        auto has_ternary = [&](literal x, literal y, literal z, clause*& c) {
            ternary t(x, y, z, nullptr);
            if (ternaries.find(t, t)) {
                c = t.orig;
                return true;
            }
            if (implies(~y, z) || implies(~x, y) || implies(~x, z)) {
                c = nullptr;
                return true;
            }
            return false;
        };
        
        auto insert_ternary = [&](clause& c) {
            if (c.size() == 3) {
                ternaries.insert(ternary(c[0], c[1], c[2], &c));
                insert_binary(c[0], c[1], c[2], &c);
                insert_binary(c[0], c[2], c[1], &c);
                insert_binary(c[2], c[1], c[0], &c);
            }
        };
        for (clause* cp : s.learned()) {
            insert_ternary(*cp);
        }
        for (clause* cp : s.clauses()) {
            insert_ternary(*cp);
        }
        auto try_ite = [&,this](literal x, literal y, literal z, clause& c) {
            clause* c1, *c3;
            if (has_ternary(y, ~z, ~x, c1)) {
                binary b(~y, x, nullptr);
                if (!binaries.find(b, b)) {
                    return false;
                }
                for (auto p : *b.use_list) {
                    literal u = p.first;
                    clause* c2 = p.second;
                    if (has_ternary(~u, ~x, ~y, c3)) {
                        c.mark_used();
                        if (c1) c1->mark_used();
                        if (c2) c2->mark_used();
                        if (c3) c3->mark_used();
                        m_on_if(~x, ~y, z, u);
                        return true;
                    }
                }
            }
            return false;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 3 || c.was_used()) continue;
            literal x = c[0], y = c[1], z = c[2];
            if (try_ite(x, y, z, c)) continue;
            if (try_ite(y, x, z, c)) continue;
            if (try_ite(z, y, x, c)) continue;            
        }
        
        std::function<bool(clause*)> not_used = [](clause* cp) { return !cp->was_used(); };
        clauses.filter_update(not_used);        
    }


}
