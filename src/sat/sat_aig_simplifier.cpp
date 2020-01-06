/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_simplifier.cpp

  Abstract:
   
    extract AIG definitions from clauses
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "util/union_find.h"
#include "sat/sat_aig_simplifier.h"
#include "sat/sat_xor_finder.h"
#include "sat/sat_elim_eqs.h"

namespace sat {
    
    struct aig_simplifier::report {
        aig_simplifier& s;
        aig_cuts&       c;
        stopwatch       m_watch;
        report(aig_simplifier& s, aig_cuts& c): s(s), c(c) { m_watch.start(); }
        ~report() {
            IF_VERBOSE(2, 
                       verbose_stream() << "(sat.aig-simplifier" 
                       << " :num-eqs " << s.m_stats.m_num_eqs 
                       << " :num-cuts " << s.m_stats.m_num_cuts 
                       << " :mb " << mem_stat()
                       << m_watch 
                       << ")\n");
        }
    };

    void aig_simplifier::operator()() {
        aig_cuts aigc;
        report _report(*this, aigc);
        TRACE("aig_simplifier", s.display(tout););
        clauses2aig(aigc);
        aig2clauses(aigc);
    }

    /**
       \brief extract AIG definitions from clauses
       Ensure that they are sorted and variables have unique definitions.
     */
    void aig_simplifier::clauses2aig(aig_cuts& aigc) {
        struct aig_def {
            literal head;
            bool_op  op;
            unsigned sz;
            unsigned offset;
            aig_def(literal h, bool_op op, unsigned sz, unsigned o): head(h), op(op), sz(sz), offset(o) {}
        };
        svector<aig_def> aig_defs;
        literal_vector literals;
        std::function<void (literal head, literal_vector const& ands)> on_and = 
            [&,this](literal head, literal_vector const& ands) {            
            aig_defs.push_back(aig_def(head, and_op, ands.size(), literals.size()));
            literals.append(ands);
            m_stats.m_num_ands++;
        };
        std::function<void (literal head, literal c, literal t, literal e)> on_ite = 
            [&,this](literal head, literal c, literal t, literal e) {            
            aig_defs.push_back(aig_def(head, ite_op, 3, literals.size()));
            literal args[3] = { c, t, e };
            literals.append(3, args);
            m_stats.m_num_ites++;
        };
        aig_finder af(s);
        af.set(on_and);
        af.set(on_ite);
        clause_vector clauses(s.clauses());
        af(clauses);

        literal_vector _xors;
        std::function<void (literal_vector const&)> on_xor = 
            [&,this](literal_vector const& xors) {
            SASSERT(xors.size() > 1);
            unsigned max_level = s.def_level(xors.back().var());
            unsigned index = xors.size() - 1;
            for (unsigned i = index; i-- > 0; ) {
                literal l = xors[i];
                if (s.def_level(l.var()) > max_level) {
                    max_level = s.def_level(l.var());
                    index = i;
                }
            }
            // head + t1 + t2 + .. = 1 
            // <=> 
            // ~head = t1 + t2 + ..
            literal head = ~xors[index];
            unsigned sz = xors.size() - 1;
            aig_defs.push_back(aig_def(head, xor_op, sz, literals.size()));
            for (unsigned i = xors.size(); i-- > 0; ) {
                if (i != index) 
                    literals.push_back(xors[i]);
            }
            m_stats.m_num_xors++;            
        };
        xor_finder xf(s);
        xf.set(on_xor);
        xf(clauses);

        svector<bool> outs(s.num_vars(), false);
        svector<bool> ins(s.num_vars(), false);
        for (auto a : aig_defs) {
            outs[a.head.var()] = true;
        }

        for (auto a : aig_defs) {
            for (unsigned i = 0; i < a.sz; ++i) {
                unsigned v = literals[a.offset+i].var();
                if (!outs[v]) ins[v] = true;
            }
        }

        std::function<void(aig_def)> force_var = [&, this] (aig_def a) {
            for (unsigned i = 0; i < a.sz; ++i) {
                unsigned v = literals[a.offset + i].var();
                if (!ins[v]) {
                    aigc.add_var(v);
                    ins[v] = true;
                }
            }
        };
        std::function<void(unsigned)> add_var = [&, this] (unsigned v) {
            if (!outs[v] && ins[v]) {
                aigc.add_var(v);
                outs[v] = true;
            }
        };
        for (auto a : aig_defs) {
            for (unsigned i = 0; i < a.sz; ++i) {
                add_var(literals[a.offset+i].var());
            }
        }

        while (true) {
            unsigned j = 0;
            for (auto a : aig_defs) {
                bool visited = true;
                for (unsigned i = 0; visited && i < a.sz; ++i) {
                    visited &= ins[literals[a.offset + i].var()];
                }
                unsigned h = a.head.var();                
                if (!ins[h] && visited) {
                    ins[h] = true;
                    aigc.add_node(a.head, a.op, a.sz, literals.c_ptr() + a.offset);
                }
                else if (!ins[h]) {
                    aig_defs[j++] = a;
                }
                else {
                    TRACE("aig_simplifier", tout << "skip " << a.head << " == .. \n";);
                    force_var(a);                    
                }
            }
            if (j == 0) {
                break;
            }
            if (j == aig_defs.size()) {
                IF_VERBOSE(2, verbose_stream() << "break cycle " << j << "\n");
                force_var(aig_defs.back());
            }
            aig_defs.shrink(j);
        }
    }

    void aig_simplifier::aig2clauses(aig_cuts& aigc) {
        vector<cut_set> cuts = aigc.get_cuts(m_config.m_max_cut_size, m_config.m_max_cutset_size);
        map<cut const*, unsigned, cut::hash_proc, cut::eq_proc> cut2id;
        literal_vector roots(s.num_vars(), null_literal);
        
        union_find_default_ctx ctx;
        union_find<> uf(ctx);
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf.mk_var();
        auto add_eq = [&](literal l1, literal l2) {
            uf.merge(l1.index(), l2.index());
            uf.merge((~l1).index(), (~l2).index());
        };
        unsigned old_num_eqs = m_stats.m_num_eqs;
        for (unsigned i = cuts.size(); i-- > 0; ) {
            m_stats.m_num_cuts += cuts[i].size();
            for (auto& cut : cuts[i]) {
                unsigned j = 0;
                if (cut2id.find(&cut, j)) {
                    VERIFY(i != j);
                    literal v(i, false);
                    literal w(j, false);
                    add_eq(v, w);
                    TRACE("aig_simplifier", tout << v << " == " << ~w << "\n";);
                    ++m_stats.m_num_eqs;
                    break;
                }
                cut.negate();
                if (cut2id.find(&cut, j)) {
                    literal v(i, false);
                    literal w(j, true);
                    add_eq(v, w);
                    TRACE("aig_simplifier", tout << v << " == " << w << "\n";);
                    ++m_stats.m_num_eqs;
                    break;
                }
                cut.negate();
                cut2id.insert(&cut, i);                
            }
        }        
        if (old_num_eqs == m_stats.m_num_eqs) {
            return;
        }
        bool_var_vector to_elim;
        for (unsigned i = s.num_vars(); i-- > 0; ) {
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
        elim_eqs elim(s);
        elim(roots, to_elim);
    }

    void aig_simplifier::collect_statistics(statistics& st) const {
        st.update("sat-aig.eqs",  m_stats.m_num_eqs);
        st.update("sat-aig.cuts", m_stats.m_num_cuts);
        st.update("sat-aig.ands", m_stats.m_num_ands);
        st.update("sat-aig.ites", m_stats.m_num_ites);
        st.update("sat-aig.xors", m_stats.m_num_xors);
    }

    vector<cut_set> aig_cuts::get_cuts(unsigned max_cut_size, unsigned max_cutset_size) {
        unsigned_vector sorted = top_sort();
        vector<cut_set> cuts;    
        cuts.resize(m_aig.size());
        max_cut_size = std::min(cut::max_cut_size, max_cut_size);
        cut_set cut_set2;
        cut_set2.init(m_region, max_cutset_size + 1);
        for (unsigned id : sorted) {
            node const& n = m_aig[id];
            if (!n.is_valid()) {
                continue;
            }
            auto& cut_set = cuts[id];
            cut_set.init(m_region, max_cutset_size + 1);
            if (n.is_var()) {
                SASSERT(!n.sign());
            }
            else if (n.is_ite()) {
                literal l1 = child(n, 0);
                literal l2 = child(n, 1);
                literal l3 = child(n, 2);
                for (auto const& a : cuts[l1.var()]) {
                    for (auto const& b : cuts[l2.var()]) {
                        cut ab;
                        if (!ab.merge(a, b, max_cut_size)) {
                            continue;
                        }
                        for (auto const& c : cuts[l3.var()]) {
                            cut abc;
                            if (!abc.merge(ab, c, max_cut_size)) {
                                continue;
                            }
                            if (cut_set.size() >= max_cutset_size) break;
                            uint64_t t1 = a.shift_table(abc);
                            uint64_t t2 = b.shift_table(abc);
                            uint64_t t3 = c.shift_table(abc);
                            if (l1.sign()) t1 = ~t1;
                            if (l2.sign()) t2 = ~t2;
                            if (l3.sign()) t3 = ~t3;
                            abc.set_table((t1 & t2) | (~t1 & t3));
                            if (n.sign()) abc.negate();
                            // extract tree size: abc.m_tree_size = a.m_tree_size + b.m_tree_size + c.m_tree_size + 1;
                            cut_set.insert(abc);
                        } 
                    }
                }
            }
            else if (n.num_children() == 2) {
                SASSERT(n.is_and() || n.is_xor());
                literal l1 = child(n, 0);
                literal l2 = child(n, 1);
                for (auto const& a : cuts[l1.var()]) {
                    for (auto const& b : cuts[l2.var()]) {
                        if (cut_set.size() >= max_cutset_size) break;
                        cut c;
                        if (c.merge(a, b, max_cut_size)) {
                            uint64_t t1 = a.shift_table(c);
                            uint64_t t2 = b.shift_table(c);
                            if (l1.sign()) t1 = ~t1;
                            if (l2.sign()) t2 = ~t2;
                            uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                            c.set_table(t3);
                            if (n.sign()) c.negate();
                            cut_set.insert(c);
                        }
                    }
                    if (cut_set.size() >= max_cutset_size) break;
                }
            }
            else if (n.num_children() < max_cut_size) {
                SASSERT(n.is_and() || n.is_xor());
                literal lit = child(n, 0);
                for (auto const& a : cuts[lit.var()]) {
                    cut_set.push_back(a);
                    if (lit.sign()) {
                        cut_set.back().negate();
                    }
                }
                for (unsigned i = 1; i < n.num_children(); ++i) {
                    cut_set2.reset();
                    literal lit = child(n, i);
                    for (auto const& a : cut_set) {
                        for (auto const& b : cuts[lit.var()]) {
                            cut c;
                            if (cut_set2.size() >= max_cutset_size) 
                                break;
                            if (c.merge(a, b, max_cut_size)) {
                                uint64_t t1 = a.shift_table(c);
                                uint64_t t2 = b.shift_table(c);
                                if (lit.sign()) t2 = ~t2;
                                uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                                c.set_table(t3);
                                if (i + 1 == n.num_children() && n.sign()) c.negate();
                                cut_set2.insert(c);
                            }
                        }
                        if (cut_set2.size() >= max_cutset_size) 
                            break;
                    }
                    cut_set.swap(cut_set2);
                }
            }
            cut_set.push_back(cut(id));
        }
        return cuts;
    }

    void aig_cuts::add_var(unsigned v) {
        m_aig.reserve(v + 1);
        m_aig[v] = node(v);
        SASSERT(m_aig[v].is_valid());
    }

    void aig_cuts::add_node(literal head, bool_op op, unsigned sz, literal const* args) {
        TRACE("aig_simplifier", tout << head << " == " << op << " " << literal_vector(sz, args) << "\n";);
        unsigned v = head.var();
        m_aig.reserve(v + 1);
        m_aig[v] = node(head.sign(), op, sz, m_literals.size());        
        m_literals.append(sz, args);
        DEBUG_CODE(
            for (unsigned i = 0; i < sz; ++i) {
                SASSERT(m_aig[args[i].var()].is_valid());
            });
        SASSERT(m_aig[v].is_valid());
    }

    unsigned_vector aig_cuts::top_sort() {
        unsigned_vector result;
        svector<bool> visit;
        visit.reserve(m_aig.size(), false);
        unsigned_vector todo;
        unsigned id = 0;
        for (node const& n : m_aig) {
            if (n.is_valid()) todo.push_back(id);
            ++id;
        }
        while (!todo.empty()) {
            unsigned id = todo.back();
            if (visit[id]) {
                todo.pop_back();
                continue;
            }
            bool all_visit = true;
            node const& n = m_aig[id];
            SASSERT(n.is_valid());
            if (!n.is_var()) {
                for (unsigned i = 0; i < n.num_children(); ++i) {
                    bool_var v = child(n, i).var();
                    if (!visit[v]) {
                        todo.push_back(v); 
                        all_visit = false;
                    }
                }
            }
            if (all_visit) {
                visit[id] = true;
                result.push_back(id);
                todo.pop_back();
            }
        }
        return result;
    }
}

