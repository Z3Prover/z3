/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_finder.cpp

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  
    AIG finder

  --*/

#include "sat/sat_aig_finder.h"
#include "sat/sat_solver.h"

namespace sat {

    aig_finder::aig_finder(solver& s): s(s), m_big(s.rand()) {}

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
            if (!find_aig(*cp)) {
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
                if (head != tail && !implies(head, ~tail)) {
                    is_aig = false;
                    break;
                }
            }
            if (is_aig) {
                m_ands.reset();
                for (literal tail : c) 
                    if (tail != head) 
                        m_ands.push_back(~tail);
                // DEBUG_CODE(validate_and(head, m_ands, c););
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
            binary(literal _x, literal _y, use_list_t* u): x(_x), y(_y), use_list(u) {
                if (x.index() > y.index()) std::swap(x, y);
            }
            binary():x(null_literal), y(null_literal), use_list(nullptr) {}
            struct hash {
                unsigned operator()(binary const& t) const { return mk_mix(t.x.index(), t.y.index(), 3); }
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
            ternary(literal _x, literal _y, literal _z, clause* c):
                x(_x), y(_y), z(_z), orig(c) {
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
            literal u;
            clause* c1, *c2, *c3;
            if (!has_ternary(y, ~z, ~x, c1)) {
                return false;
            }
            binary b(~y, x, nullptr);
            if (!binaries.find(b, b)) {
                return false;
            }
            for (auto p : *b.use_list) {
                u  = p.first;
                c2 = p.second;
                if (!has_ternary(~u, ~x, ~y, c3)) {
                    continue;
                }
                c.mark_used();
                if (c1) c1->mark_used();
                if (c2) c2->mark_used();
                if (c3) c3->mark_used();
                // DEBUG_CODE(validate_if(~x, ~y, z, u, c, c1, c2, c3););
                m_on_if(~x, ~y, z, u);
                return true;
            }
            return false;
        };

        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.size() != 3 || c.was_used()) continue;
            literal x = c[0], y = c[1], z = c[2];
            if (try_ite(x, z, y, c)) continue;
            if (try_ite(x, y, z, c)) continue;
            if (try_ite(y, x, z, c)) continue;
            if (try_ite(z, x, y, c)) continue;
            if (try_ite(z, y, x, c)) continue;
            if (try_ite(y, z, x, c)) continue;
        }
        
        std::function<bool(clause*)> not_used = [](clause* cp) { return !cp->was_used(); };
        clauses.filter_update(not_used);        
    }

    void aig_finder::validate_clause(literal_vector const& clause, vector<literal_vector> const& clauses) {
        solver vs(s.params(), s.rlimit());
        for (unsigned i = 0; i < s.num_vars(); ++i) {
            vs.mk_var();
        }
        svector<solver::bin_clause> bins;
        s.collect_bin_clauses(bins, true, false);
        for (auto b : bins) {
            vs.mk_clause(b.first, b.second);
        }
        for (auto const& cl : clauses) {
            vs.mk_clause(cl);
        }
        for (literal l : clause) {
            literal nl = ~l;
            vs.mk_clause(1, &nl);
        }
        lbool r = vs.check();
        if (r != l_false) {
            vs.display(verbose_stream());
            UNREACHABLE();
        }
    }

    void aig_finder::validate_clause(literal x, literal y, literal z, vector<literal_vector> const& clauses) {
        literal_vector clause;
        clause.push_back(x);
        clause.push_back(y);
        clause.push_back(z);
        validate_clause(clause, clauses);
    }

    void aig_finder::validate_and(literal head, literal_vector const& ands, clause const& c) {
        IF_VERBOSE(2, verbose_stream() << "validate and: " << head << " == " << ands << "\n");
        vector<literal_vector> clauses;
        clauses.push_back(literal_vector(c.size(), c.begin()));
        literal_vector clause;
        clause.push_back(head);
        for (literal l : ands) clause.push_back(~l);
        validate_clause(clause, clauses);
        for (literal l : ands) {
            clause.reset();
            clause.push_back(~head);
            clause.push_back(l);
            validate_clause(clause, clauses);
        }
    }

    void aig_finder::validate_if(literal x, literal c, literal t, literal e, clause const& c0, clause const* c1, clause const* c2, clause const* c3) {
        IF_VERBOSE(2, verbose_stream() << "validate if: " << x << " == " << c << " ? " << t << " : " << e << "\n");
        vector<literal_vector> clauses;
        clauses.push_back(literal_vector(c0.size(), c0.begin()));
        if (c1) clauses.push_back(literal_vector(c1->size(), c1->begin()));
        if (c2) clauses.push_back(literal_vector(c2->size(), c2->begin()));
        if (c3) clauses.push_back(literal_vector(c3->size(), c3->begin()));
        literal_vector clause;
        validate_clause(~x, ~c, t, clauses);
        validate_clause(~x,  c, e, clauses);
        validate_clause(~t, ~c, x, clauses);
        validate_clause(~e,  c, x, clauses);
    }


}
