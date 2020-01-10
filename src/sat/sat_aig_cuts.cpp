/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_cuts.cpp

  Abstract:
   
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "sat/sat_aig_cuts.h"
#include "util/trace.h"

namespace sat {
        
    aig_cuts::aig_cuts() {
        m_config.m_max_cut_size = std::min(cut().max_cut_size, m_config.m_max_cut_size);
        m_cut_set1.init(m_region, m_config.m_max_cutset_size + 1);
        m_cut_set2.init(m_region, m_config.m_max_cutset_size + 1);
        m_num_cut_calls = 0;
    }

    vector<cut_set> const& aig_cuts::operator()() {
        flush_roots();
        unsigned_vector node_ids = filter_valid_nodes();
        TRACE("aig_simplifier", display(tout););
        augment(node_ids);
        TRACE("aig_simplifier", display(tout););
        ++m_num_cut_calls;
        return m_cuts;
    }

    void aig_cuts::augment(unsigned_vector const& ids) {
        for (unsigned id : ids) {
            if (m_aig[id].empty()) {
                continue;
            }
            IF_VERBOSE(3, m_cuts[id].display(verbose_stream() << "augment " << id << "\nbefore\n"));
            for (node const& n : m_aig[id]) {
                augment(id, n);
            }
            IF_VERBOSE(3, m_cuts[id].display(verbose_stream() << "after\n"));            
        }
    }

    void aig_cuts::augment(unsigned id, node const& n) {
        unsigned nc = n.size();
        m_insertions = 0;
        cut_set& cs = m_cuts[id];
        if (!is_touched(n)) {
            // no-op
        }
        else if (n.is_var()) {
            SASSERT(!n.sign());
        }
        else if (n.is_ite()) {
            augment_ite(n, cs);
        }
        else if (nc == 0) {
            augment_aig0(n, cs);
        }
        else if (nc == 1) {
            augment_aig1(n, cs);
        }
        else if (nc == 2) {
            augment_aig2(n, cs);
        }
        else if (nc < m_config.m_max_cut_size) {
            augment_aigN(n, cs);
        }
        if (m_insertions > 0) {
            touch(id);
        }
    }

    bool aig_cuts::insert_cut(cut const& c, cut_set& cs) {
        if (!cs.insert(c)) {
            return true;
        }
        if (++m_insertions > m_config.m_max_insertions) {
            return false;
        }
        while (cs.size() >= m_config.m_max_cutset_size) {
            // never evict the first entry, it is used for the starting point
            unsigned idx = 1 + (m_rand() % (cs.size() - 1));
            cs.evict(idx);
        }
        return true;
    }

    void aig_cuts::augment_ite(node const& n, cut_set& cs) {
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        literal l3 = child(n, 2);
        for (auto const& a : m_cuts[l1.var()]) {
            for (auto const& b : m_cuts[l2.var()]) {
                cut ab;
                if (!ab.merge(a, b, m_config.m_max_cut_size)) {
                    continue;
                }
                for (auto const& c : m_cuts[l3.var()]) {
                    cut abc;
                    if (!abc.merge(ab, c, m_config.m_max_cut_size)) {
                        continue;
                    }
                    uint64_t t1 = a.shift_table(abc);
                    uint64_t t2 = b.shift_table(abc);
                    uint64_t t3 = c.shift_table(abc);
                    if (l1.sign()) t1 = ~t1;
                    if (l2.sign()) t2 = ~t2;
                    if (l3.sign()) t3 = ~t3;
                    abc.set_table((t1 & t2) | (~t1 & t3));
                    if (n.sign()) abc.negate();
                    // extract tree size: abc.m_tree_size = a.m_tree_size + b.m_tree_size + c.m_tree_size + 1;
                    if (!insert_cut(abc, cs)) return;
                } 
            }
        }
    }

    void aig_cuts::augment_aig0(node const& n, cut_set& cs) {
        SASSERT(n.is_and());
        cs.reset();
        cut c;          
        c.m_table = (n.sign() ? 0x0 : 0x1);
        cs.push_back(c);
    }

    void aig_cuts::augment_aig1(node const& n, cut_set& cs) {
        SASSERT(n.is_and());
        literal lit = child(n, 0);
        for (auto const& a : m_cuts[lit.var()]) {
            cut c(a);
            if (n.sign()) c.negate();
            if (!insert_cut(c, cs)) return; 
        }
    }

    void aig_cuts::augment_aig2(node const& n, cut_set& cs) {
        SASSERT(n.is_and() || n.is_xor());
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        for (auto const& a : m_cuts[l1.var()]) {
            for (auto const& b : m_cuts[l2.var()]) {
                cut c;
                if (c.merge(a, b, m_config.m_max_cut_size)) {
                    uint64_t t1 = a.shift_table(c);
                    uint64_t t2 = b.shift_table(c);
                    if (l1.sign()) t1 = ~t1;
                    if (l2.sign()) t2 = ~t2;
                    uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                    c.set_table(t3);
                    if (n.sign()) c.negate();
                    if (!insert_cut(c, cs)) return;
                }
            }
        }
    }

    void aig_cuts::augment_aigN(node const& n, cut_set& cs) {
        m_cut_set1.reset();
        SASSERT(n.is_and() || n.is_xor());
        literal lit = child(n, 0);
        for (auto const& a : m_cuts[lit.var()]) {
            m_cut_set1.push_back(a);
            if (lit.sign()) {
                m_cut_set1.back().negate();
            }
        }
        for (unsigned i = 1; i < n.size(); ++i) {
            m_cut_set2.reset();
            literal lit = child(n, i);
            m_insertions = 0;
            for (auto const& a : m_cut_set1) {
                for (auto const& b : m_cuts[lit.var()]) {
                    cut c;
                    if (c.merge(a, b, m_config.m_max_cut_size)) {
                        uint64_t t1 = a.shift_table(c);
                        uint64_t t2 = b.shift_table(c);
                        if (lit.sign()) t2 = ~t2;
                        uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                        c.set_table(t3);
                        if (i + 1 == n.size() && n.sign()) c.negate();
                        if (!insert_cut(c, m_cut_set2)) goto next_child;
                    }
                }
            }
        next_child:
            m_cut_set1.swap(m_cut_set2);
        }
        m_insertions = 0;
        for (auto & cut : m_cut_set1) {
            if (!insert_cut(cut, cs)) {
                break;
            }
        }        
    }

    bool aig_cuts::is_touched(node const& n) {
        for (unsigned i = 0; i < n.size(); ++i) {
            literal lit = m_literals[n.offset() + i];
            if (is_touched(lit)) {
                return true;
            }
        }
        return false;
    }

    void aig_cuts::reserve(unsigned v) {
        m_aig.reserve(v + 1);
        m_cuts.reserve(v + 1);
        m_last_touched.reserve(v + 1, 0);
    }

    void aig_cuts::add_var(unsigned v) {
        reserve(v);
        if (m_aig[v].empty()) {
            m_aig[v].push_back(node(v));
            init_cut_set(v);
            touch(v);
        }
    }

    void aig_cuts::add_node(literal head, bool_op op, unsigned sz, literal const* args) {
        TRACE("aig_simplifier", tout << head << " == " << op << " " << literal_vector(sz, args) << "\n";);
        unsigned v = head.var();
        reserve(v);
        unsigned offset = m_literals.size();
        node n(head.sign(), op, sz, offset);
        m_literals.append(sz, args);
        if (op == and_op || op == xor_op) {
            std::sort(m_literals.c_ptr() + offset, m_literals.c_ptr() + offset + sz);
        }
        for (unsigned i = 0; i < sz; ++i) {
            if (m_aig[args[i].var()].empty()) {
                add_var(args[i].var());
            }
        }
        if (m_aig[v].empty() || n.is_const()) {
            m_aig[v].reset();
            m_aig[v].push_back(n);
            init_cut_set(v);
            if (n.is_const()) {
                augment_aig0(n, m_cuts[v]);
            }
            touch(v);
            IF_VERBOSE(2, display(verbose_stream() << "add " << head.var() << " == ", n) << "\n");
        }
        else if (m_aig[v][0].is_const() || !insert_aux(v, n)) {
            m_literals.shrink(m_literals.size() - sz);
            TRACE("aig_simplifier", tout << "duplicate\n";);
        }
        SASSERT(!m_aig[v].empty());
    }

    void aig_cuts::set_root(bool_var v, literal r) {
        IF_VERBOSE(2, verbose_stream() << "set-root " << v << " -> " << r << "\n");
        m_roots.push_back(std::make_pair(v, r));
    }

    void aig_cuts::flush_roots() {
        if (m_roots.empty()) return;
        literal_vector to_root;
        for (unsigned i = 0; i < m_aig.size(); ++i) {
            to_root.push_back(literal(i, false));
        }
        for (unsigned i = m_roots.size(); i-- > 0; ) {
            bool_var v = m_roots[i].first;
            literal  r = m_roots[i].second;
            literal rr = to_root[r.var()];
            to_root[v] = r.sign() ? ~rr : rr;
        }
        for (unsigned i = 0; i < m_aig.size(); ++i) {
            // invalidate nodes that have been rooted
            if (to_root[i] != literal(i, false)) {
                m_aig[i].reset();
                m_cuts[i].reset();
            }
            else {
                for (node & n : m_aig[i]) {
                    flush_roots(to_root, n);
                }
            }
        }
        for (cut_set& cs : m_cuts) {
            flush_roots(to_root, cs);
        }
        m_roots.reset();
        TRACE("aig_simplifier", display(tout););
    }

    void aig_cuts::flush_roots(literal_vector const& to_root, node& n) {
        bool changed = false;
        for (unsigned i = 0; i < n.size(); ++i) {
            literal& lit = m_literals[n.offset() + i];
            if (to_root[lit.var()] != lit) {
                changed = true;
                lit = lit.sign() ? ~to_root[lit.var()] : to_root[lit.var()];
            }
        }
        if (changed && (n.is_and() || n.is_xor())) {
            std::sort(m_literals.c_ptr() + n.offset(), m_literals.c_ptr() + n.offset() + n.size());
        }
    }

    void aig_cuts::flush_roots(literal_vector const& to_root, cut_set& cs) {
        unsigned j = 0;        
        for (cut& c : cs) {
            bool has_stale = false;
            for (unsigned v : c) {
                has_stale |= (to_root[v] != literal(v, false));
            }
            if (!has_stale) {
                cs[j++] = c;
            }
        }
        cs.shrink(j);
    }

    void aig_cuts::init_cut_set(unsigned id) {
        SASSERT(m_aig[id].size() == 1);
        node const& n = m_aig[id][0];
        SASSERT(n.is_valid());
        auto& cut_set = m_cuts[id];
        cut_set.init(m_region, m_config.m_max_cutset_size + 1);
        cut_set.reset();
        cut_set.push_back(cut(id));  
    }

    bool aig_cuts::eq(node const& a, node const& b) {
        if (a.is_valid() != b.is_valid()) return false;
        if (!a.is_valid()) return true;
        if (a.op() != b.op() || a.sign() != b.sign() || a.size() != b.size()) return false;
        for (unsigned i = 0; i < a.size(); ++i) {
            if (m_literals[a.offset() + i] != m_literals[b.offset() + i]) return false;
        }
        return true;
    }

    bool aig_cuts::insert_aux(unsigned v, node const& n) {
        unsigned num_gt = 0, num_eq = 0;
        for (node const& n2 : m_aig[v]) {
            if (eq(n, n2)) return false;
            else if (n.size() < n2.size()) num_gt++;
            else if (n.size() == n2.size()) num_eq++;
        }
        if (m_aig[v].size() < m_config.m_max_aux) {
            m_aig[v].push_back(n);
            touch(v);
            return true;
        }
        if (num_gt > 0) {
            unsigned idx = rand() % num_gt;
            for (node const& n2 : m_aig[v]) {
                if (n.size() < n2.size()) {
                    if (idx == 0) {
                        m_aig[v][idx] = n;
                        touch(v);
                        return true;
                    }
                    --idx;
                }
            }
        }
        if (num_eq > 0) {
            unsigned idx = rand() % num_eq;
            for (node const& n2 : m_aig[v]) {
                if (n.size() == n2.size()) {
                    if (idx == 0) {
                        m_aig[v][idx] = n;
                        touch(v);
                        return true;
                    }
                    --idx;
                }
            }
        }
        return false;
    }

    unsigned_vector aig_cuts::filter_valid_nodes() const {
        unsigned id = 0;
        unsigned_vector result;
        for (auto& v : m_aig) {
            if (!v.empty()) result.push_back(id);
            ++id;
        }
        return result;
    }

    std::ostream& aig_cuts::display(std::ostream& out) const {
        auto ids = filter_valid_nodes();
        for (auto id : ids) {
            out << id << " == ";
            bool first = true;
            for (auto const& n : m_aig[id]) {
                if (first) first = false; else out << "   ";
                display(out, n) << "\n";
            }
            m_cuts[id].display(out);
        }
        return out;
    }

    std::ostream& aig_cuts::display(std::ostream& out, node const& n) const {
        out << (n.sign() ? "! " : "  ");
        switch (n.op()) {
        case var_op: out << "var "; break;
        case and_op: out << "& "; break;
        case xor_op: out << "^ "; break;
        case ite_op: out << "? "; break;
        default: break;
        }
        for (unsigned i = 0; i < n.size(); ++i) {
            out << m_literals[n.offset() + i] << " ";
        }
        return out;
    }

}

