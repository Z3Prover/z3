/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_npn3_finder.cpp

  Author:

    Mathias Soeken 2020-02-20

  Notes:

    NPN3 finder

  --*/

#include "sat/sat_npn3_finder.h"
#include "sat/sat_solver.h"

namespace sat {

    // binary
    npn3_finder::binary::binary(literal _x, literal _y, use_list_t* u) : x(_x), y(_y), use_list(u) {
        if (x.index() > y.index()) std::swap(x, y);
    }
    npn3_finder::binary::binary() : x(null_literal), y(null_literal), use_list(nullptr) {}
    unsigned npn3_finder::binary::hash::operator()(binary const& t) const { return mk_mix(t.x.index(), t.y.index(), 3); }
    bool npn3_finder::binary::eq::operator()(binary const& a, binary const& b) const {
        return a.x == b.x && a.y == b.y;
    }

    // ternary
    npn3_finder::ternary::ternary(literal _x, literal _y, literal _z, clause* c) :
        x(_x), y(_y), z(_z), orig(c) {
        if (x.index() > y.index()) std::swap(x, y);
        if (y.index() > z.index()) std::swap(y, z);
        if (x.index() > y.index()) std::swap(x, y);
    }
    npn3_finder::ternary::ternary() :x(null_literal), y(null_literal), z(null_literal), orig(nullptr) {}
    unsigned npn3_finder::ternary::hash::operator()(ternary const& t) const { return mk_mix(t.x.hash(), t.y.hash(), t.z.hash()); }
    bool npn3_finder::ternary::eq::operator()(ternary const& a, ternary const& b) const {
        return a.x == b.x && a.y == b.y && a.z == b.z;
    }

    // quaternary
    npn3_finder::quaternary::quaternary(literal _w, literal _x, literal _y, literal _z, clause* c) :
        w(_w), x(_x), y(_y), z(_z), orig(c) {
            if (w.index() > x.index()) std::swap(w, x);
            if (y.index() > z.index()) std::swap(y, z);
            if (w.index() > y.index()) std::swap(w, y);
            if (x.index() > z.index()) std::swap(x, z);
            if (x.index() > y.index()) std::swap(x, y);
    }
    npn3_finder::quaternary::quaternary() :w(null_literal), x(null_literal), y(null_literal), z(null_literal), orig(nullptr) {}
    unsigned npn3_finder::quaternary::hash::operator()(quaternary const& t) const { return mk_mix(t.w.hash(), t.x.hash(), mk_mix(t.y.hash(), t.z.hash(), 3)); }
    bool npn3_finder::quaternary::eq::operator()(quaternary const& a, quaternary const& b) const {
        return a.w == b.w && a.x == b.x && a.y == b.y && a.z == b.z;
    }

    npn3_finder::npn3_finder(solver& s) : s(s), m_big(s.rand()) {}

    void npn3_finder::operator()(clause_vector& clauses) {
        m_big.init(s, true);
        find_mux(clauses);
        find_maj(clauses);
        find_orand(clauses);
        find_and(clauses);
        find_xor(clauses);
        find_andxor(clauses);
        find_xorand(clauses);
        find_onehot(clauses);
        find_gamble(clauses);
        find_dot(clauses);
    }

    bool npn3_finder::implies(literal a, literal b) const {
        if (m_big.connected(a, b))
            return true;
        for (auto const& w : s.get_wlist(a)) {
            if (w.is_binary_clause() && b == w.get_literal())
                return true;
        }
        return false;
    }

    void npn3_finder::process_clauses(clause_vector& clauses, npn3_finder::binary_hash_table_t& binaries, npn3_finder::ternary_hash_table_t& ternaries)
    {
        for (clause* cp : clauses) cp->unmark_used();

        auto insert_binary = [&](literal x, literal y, literal z, clause* c) {
            binary b(x, y, nullptr);
            auto* e = binaries.insert_if_not_there2(b);
            if (e->get_data().use_list == nullptr) {
                use_list_t* use_list = alloc(use_list_t);
                m_use_lists.push_back(use_list);
                e->get_data().use_list = use_list;
            }
            e->get_data().use_list->push_back(std::make_pair(z, c));
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
    }

    void npn3_finder::process_more_clauses(clause_vector& clauses, npn3_finder::binary_hash_table_t& binaries, npn3_finder::ternary_hash_table_t& ternaries, npn3_finder::quaternary_hash_table_t& quaternaries)
    {
        for (clause* cp : clauses) cp->unmark_used();

        auto insert_binary = [&](literal x, literal y, literal z, clause* c) {
            binary b(x, y, nullptr);
            auto* e = binaries.insert_if_not_there2(b);
            if (e->get_data().use_list == nullptr) {
                use_list_t* use_list = alloc(use_list_t);
                m_use_lists.push_back(use_list);
                e->get_data().use_list = use_list;
            }
            e->get_data().use_list->push_back(std::make_pair(z, c));
        };

        auto insert = [&](clause& c) {
            if (c.size() == 3) {
                ternaries.insert(ternary(c[0], c[1], c[2], &c));
                insert_binary(c[0], c[1], c[2], &c);
                insert_binary(c[0], c[2], c[1], &c);
                insert_binary(c[2], c[1], c[0], &c);
            } else if (c.size() == 4) {
                quaternaries.insert(quaternary(c[0], c[1], c[2], c[3], &c));
            }
        };

        for (clause* cp : s.learned()) {
            insert(*cp);
        }
        for (clause* cp : s.clauses()) {
            insert(*cp);
        }
    }

    bool npn3_finder::has_ternary(ternary_hash_table_t const& ternaries, literal x, literal y, literal z, clause*& c) const
    {
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
    }

    bool npn3_finder::has_quaternary(quaternary_hash_table_t const& quaternaries, ternary_hash_table_t const& ternaries, literal w, literal x, literal y, literal z, clause*& c) const
    {
        quaternary q(w, x, y, z, nullptr);
        if (quaternaries.find(q, q)) {
            c = q.orig;
            return true;
        }
        if (has_ternary(ternaries, w, x, y, c) || has_ternary(ternaries, w, x, z, c) || has_ternary(ternaries, w, y, z, c) || has_ternary(ternaries, x, y, z, c)) {
            return true;
        }
        return false;
    }

    void npn3_finder::filter(clause_vector& clauses) const
    {
        //std::function<bool(clause*)> not_used = [](clause* cp) { return !cp->was_used(); };
        //clauses.filter_update(not_used);
    }

    void npn3_finder::find_npn3(clause_vector& clauses, on_function_t const& on_function, std::function<bool(binary_hash_table_t const&, ternary_hash_table_t const&, literal, literal, literal, clause&)> const& checker)
    {
        if (!on_function) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        process_clauses(clauses, binaries, ternaries);

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 3 || c.was_used()) continue;
            literal x = c[0], y = c[1], z = c[2];
            if (checker(binaries, ternaries, x, z, y, c)) continue;
            if (checker(binaries, ternaries, x, y, z, c)) continue;
            if (checker(binaries, ternaries, y, x, z, c)) continue;
            if (checker(binaries, ternaries, z, x, y, c)) continue;
            if (checker(binaries, ternaries, z, y, x, c)) continue;
            if (checker(binaries, ternaries, y, z, x, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_mux(clause_vector& clauses) {
        auto try_ite = [&, this](binary_hash_table_t const& binaries, ternary_hash_table_t const& ternaries, literal x, literal y, literal z, clause& c) {
            literal u;
            clause* c1, * c2, * c3;
            if (!has_ternary(ternaries, y, ~z, ~x, c1)) {
                return false;
            }
            binary b(~y, x, nullptr);
            if (!binaries.find(b, b)) {
                return false;
            }
            for (auto p : *b.use_list) {
                u = p.first;
                c2 = p.second;
                if (!has_ternary(ternaries, ~u, ~x, ~y, c3)) {
                    continue;
                }
                c.mark_used();
                if (c1) c1->mark_used();
                if (c2) c2->mark_used();
                if (c3) c3->mark_used();
                m_on_mux(~x, ~y, z, u);
                return true;
            }
            return false;
        };

        find_npn3(clauses, m_on_mux, try_ite);
    }

    void npn3_finder::find_maj(clause_vector& clauses) {
        // assume that x is head
        auto try_maj = [&, this](binary_hash_table_t const& binaries, ternary_hash_table_t const& ternaries, literal x, literal y, literal z, clause& c) {
            literal u;
            clause *c1, *c2, *c3, *c4, *c5, *c6;
            if (!has_ternary(ternaries, ~x, ~y, ~z, c1)) {
                return false;
            }
            binary b(x, y, nullptr);
            if (!binaries.find(b, b)) {
                return false;
            }
            for (auto p : *b.use_list) {
                u = p.first;
                if (u == z) continue;
                c2 = p.second;
                if (!has_ternary(ternaries, x, y, u, c3)) {
                    continue;
                }
                if (!has_ternary(ternaries, ~x, ~y, ~u, c4)) {
                    continue;
                }
                if (!has_ternary(ternaries, x, z, u, c5)) {
                    continue;
                }
                if (!has_ternary(ternaries, ~x, ~z, ~u, c6)) {
                    continue;
                }
                c.mark_used();
                if (c1) c1->mark_used();
                if (c2) c2->mark_used();
                if (c3) c3->mark_used();
                if (c4) c4->mark_used();
                if (c5) c5->mark_used();
                if (c6) c6->mark_used();
                m_on_maj(~x, y, z, u);
                return true;
            }
            return false;
        };
        
        find_npn3(clauses, m_on_maj, try_maj);
    }

    void npn3_finder::find_orand(clause_vector& clauses) {
        // assume that x = head, y = x
        auto try_orand = [&, this](binary_hash_table_t const& binaries, ternary_hash_table_t const& ternaries, literal x, literal y, literal z, clause& c) {
            if (!implies(x, ~y)) return false;

            literal u;
            clause *c1, *c2;
            binary b(x, y, nullptr);
            if (!binaries.find(b, b)) return false;

            for (auto p : *b.use_list) {
                u = p.first;
                if (u == z) continue;
                c1 = p.second;
                if (!has_ternary(ternaries, ~z, ~u, ~x, c2)) {
                    continue;
                }
                c.mark_used();
                if (c1) c1->mark_used();
                if (c2) c2->mark_used();
                m_on_orand(x, ~y, ~z, ~u);
                return true;
            }
            return false;
        };

        find_npn3(clauses, m_on_orand, try_orand);
    }

    void npn3_finder::find_xor(clause_vector& clauses) {
        if (!m_on_xor) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_xor = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3, *c4, *c5, *c6, *c7;
          if (!has_quaternary(quaternaries, ternaries, ~x, ~y, z, w, c1)) return false;
          if (!has_quaternary(quaternaries, ternaries, ~x, y, ~z, w, c2)) return false;
          if (!has_quaternary(quaternaries, ternaries, ~x, y, z, ~w, c3)) return false;
          if (!has_quaternary(quaternaries, ternaries, ~x, ~y, ~z, ~w, c4)) return false;
          if (!has_quaternary(quaternaries, ternaries, x, y, ~z, ~w, c5)) return false;
          if (!has_quaternary(quaternaries, ternaries, x, ~y, z, ~w, c6)) return false;
          if (!has_quaternary(quaternaries, ternaries, x, ~y, ~z, w, c7)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          if (c4) c4->mark_used();
          if (c5) c5->mark_used();
          if (c6) c6->mark_used();
          if (c7) c7->mark_used();
          m_on_xor(w, ~x, y, z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_xor(w, x, y, z, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_and(clause_vector& clauses) {
        if (!m_on_and) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        process_clauses(clauses, binaries, ternaries);

        const auto try_and = [&](literal w, literal x, literal y, literal z, clause &c) {
          if (!implies(w, ~x)) return false;
          if (!implies(w, ~y)) return false;
          if (!implies(w, ~z)) return false;

          c.mark_used();
          m_on_and(w, ~x, ~y, ~z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_and(w, x, y, z, c)) continue;
            if (try_and(x, w, y, z, c)) continue;
            if (try_and(y, w, x, z, c)) continue;
            if (try_and(z, w, x, y, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_andxor(clause_vector& clauses) {
        if (!m_on_andxor) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_andxor = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3, *c4, *c5;
          if (!has_quaternary(quaternaries, ternaries, ~x, y, z, ~w, c1)) return false;
          if (!has_ternary(ternaries, ~x, ~y, w, c2)) return false;
          if (!has_ternary(ternaries, ~x, ~z, w, c3)) return false;
          if (!has_ternary(ternaries, x, ~y, ~w, c4)) return false;
          if (!has_ternary(ternaries, x, ~z, ~w, c5)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          if (c4) c4->mark_used();
          if (c5) c5->mark_used();
          m_on_andxor(~w, x, ~y, ~z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_andxor(w, x, y, z, c)) continue;
            if (try_andxor(w, y, x, z, c)) continue;
            if (try_andxor(w, z, x, y, c)) continue;
            if (try_andxor(x, w, y, z, c)) continue;
            if (try_andxor(x, y, w, z, c)) continue;
            if (try_andxor(x, z, w, y, c)) continue;
            if (try_andxor(y, w, x, z, c)) continue;
            if (try_andxor(y, x, w, z, c)) continue;
            if (try_andxor(y, z, w, x, c)) continue;
            if (try_andxor(z, w, x, y, c)) continue;
            if (try_andxor(z, x, w, y, c)) continue;
            if (try_andxor(z, y, w, x, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_xorand(clause_vector& clauses) {
        if (!m_on_xorand) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_xorand = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3;
          if (!has_quaternary(quaternaries, ternaries, x, ~y, ~z, w, c1)) return false;
          if (!has_ternary(ternaries, ~y, z, ~w, c2)) return false;
          if (!has_ternary(ternaries, y, ~z, ~w, c3)) return false;
          if (!implies(w, ~x)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          m_on_xorand(w, ~x, y, ~z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_xorand(w, x, y, z, c)) continue;
            if (try_xorand(w, y, x, z, c)) continue;
            if (try_xorand(w, z, x, y, c)) continue;
            if (try_xorand(x, w, y, z, c)) continue;
            if (try_xorand(x, y, w, z, c)) continue;
            if (try_xorand(x, z, w, y, c)) continue;
            if (try_xorand(y, w, x, z, c)) continue;
            if (try_xorand(y, x, w, z, c)) continue;
            if (try_xorand(y, z, w, x, c)) continue;
            if (try_xorand(z, w, x, y, c)) continue;
            if (try_xorand(z, x, w, y, c)) continue;
            if (try_xorand(z, y, w, x, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_gamble(clause_vector& clauses) {
        if (!m_on_gamble) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_gamble = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3, *c4;
          if (!has_quaternary(quaternaries, ternaries, ~x, ~y, ~z, w, c1)) return false;
          if (!has_ternary(ternaries, ~x, y, ~w, c2)) return false;
          if (!has_ternary(ternaries, ~y, z, ~w, c3)) return false;
          if (!has_ternary(ternaries, x, ~z, ~w, c4)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          if (c4) c4->mark_used();
          m_on_gamble(w, x, y, z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_gamble(w, x, y, z, c)) continue;
            if (try_gamble(x, w, y, z, c)) continue;
            if (try_gamble(y, w, x, z, c)) continue;
            if (try_gamble(z, w, x, y, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_onehot(clause_vector& clauses) {
        if (!m_on_onehot) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_onehot = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3, *c4, *c5, *c6;
          if (!has_quaternary(quaternaries, ternaries, ~x, y, z, ~w, c1)) return false;
          if (!has_quaternary(quaternaries, ternaries, x, ~y, z, ~w, c2)) return false;
          if (!has_quaternary(quaternaries, ternaries, x, y, ~z, ~w, c3)) return false;
          if (!has_ternary(ternaries, ~x, ~y, w, c4)) return false;
          if (!has_ternary(ternaries, ~x, ~z, w, c5)) return false;
          if (!has_ternary(ternaries, ~y, ~z, w, c6)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          if (c4) c4->mark_used();
          if (c5) c5->mark_used();
          if (c6) c6->mark_used();
          m_on_onehot(~w, x, y, z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_onehot(w, x, y, z, c)) continue;
            if (try_onehot(x, w, y, z, c)) continue;
            if (try_onehot(y, w, x, z, c)) continue;
            if (try_onehot(z, w, x, y, c)) continue;
        }

        filter(clauses);
    }

    void npn3_finder::find_dot(clause_vector& clauses) {
        if (!m_on_dot) return;

        binary_hash_table_t binaries;
        ternary_hash_table_t ternaries;
        quaternary_hash_table_t quaternaries;
        process_more_clauses(clauses, binaries, ternaries, quaternaries);

        const auto try_dot = [&](literal w, literal x, literal y, literal z, clause &c) {
          clause *c1, *c2, *c3, *c4;
          if (!has_ternary(ternaries, ~x, z, ~w, c1)) return false;
          if (!has_ternary(ternaries, x, ~y, ~w, c2)) return false;
          if (!has_ternary(ternaries, x, ~z, ~w, c3)) return false;
          if (!has_ternary(ternaries, ~x, ~z, w, c4)) return false;

          c.mark_used();
          if (c1) c1->mark_used();
          if (c2) c2->mark_used();
          if (c3) c3->mark_used();
          if (c4) c4->mark_used();
          m_on_dot(w, ~x, y, z);
          return true;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 4 || c.was_used()) continue;
            literal w = c[0], x = c[1], y = c[2], z = c[3];

            if (try_dot(w, x, y, z, c)) continue;
            if (try_dot(w, x, z, y, c)) continue;
            if (try_dot(w, y, x, z, c)) continue;
            if (try_dot(w, y, z, x, c)) continue;
            if (try_dot(w, z, x, y, c)) continue;
            if (try_dot(w, z, y, x, c)) continue;
            if (try_dot(x, w, y, z, c)) continue;
            if (try_dot(x, w, z, y, c)) continue;
            if (try_dot(x, y, w, z, c)) continue;
            if (try_dot(x, y, z, w, c)) continue;
            if (try_dot(x, z, w, y, c)) continue;
            if (try_dot(x, z, y, w, c)) continue;
            if (try_dot(y, w, x, z, c)) continue;
            if (try_dot(y, w, z, x, c)) continue;
            if (try_dot(y, x, w, z, c)) continue;
            if (try_dot(y, x, z, w, c)) continue;
            if (try_dot(y, z, w, x, c)) continue;
            if (try_dot(y, z, x, w, c)) continue;
            if (try_dot(z, w, x, y, c)) continue;
            if (try_dot(z, w, y, x, c)) continue;
            if (try_dot(z, x, w, y, c)) continue;
            if (try_dot(z, x, y, w, c)) continue;
            if (try_dot(z, y, w, x, c)) continue;
            if (try_dot(z, y, x, w, c)) continue;
        }

        filter(clauses);
    }

}
