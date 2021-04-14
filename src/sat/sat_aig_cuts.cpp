/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_cuts.cpp

  Abstract:
   
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "util/trace.h"
#include "sat/sat_aig_cuts.h"
#include "sat/sat_solver.h"
#include "sat/sat_lut_finder.h"

namespace sat {
        
    aig_cuts::aig_cuts() {
        m_cut_set1.init(m_region, m_config.m_max_cutset_size + 1, UINT_MAX);
        m_cut_set2.init(m_region, m_config.m_max_cutset_size + 1, UINT_MAX);
        m_empty_cuts.init(m_region, m_config.m_max_cutset_size + 1, UINT_MAX);
        m_num_cut_calls = 0;
        m_num_cuts = 0;
    }

    vector<cut_set> const& aig_cuts::operator()() {
        if (m_config.m_full) flush_roots();
        unsigned_vector node_ids = filter_valid_nodes();
        TRACE("cut_simplifier", display(tout););
        augment(node_ids);
        TRACE("cut_simplifier", display(tout););
        ++m_num_cut_calls;
        return m_cuts;
    }

    void aig_cuts::augment(unsigned_vector const& ids) {
        for (unsigned id : ids) {
            if (m_aig[id].empty()) {
                continue;
            }
            IF_VERBOSE(20, m_cuts[id].display(verbose_stream() << "augment " << id << "\nbefore\n"));
            for (node const& n : m_aig[id]) {
                augment(id, n);
            }

#if 0
            // augment cuts directly       
            m_cut_save.reset();
            cut_set& cs = m_cuts[id];
            for (cut const& c : cs) {
                if (c.size() > 1) m_cut_save.push_back(c);
            }
            for (cut const& c : m_cut_save) {
                lut lut(*this, c);
                augment_lut(id, lut, cs);
            }
#endif
            IF_VERBOSE(20, m_cuts[id].display(verbose_stream() << "after\n"));            
        }
    }

    void aig_cuts::augment(unsigned id, node const& n) {
        unsigned nc = n.size();
        m_insertions = 0;
        cut_set& cs = m_cuts[id];
        if (!is_touched(id, n)) {
            // no-op
        }
        else if (n.is_var()) {
            SASSERT(!n.sign());
        }
        else if (n.is_lut()) {
            lut lut(*this, n);
            augment_lut(id, lut, cs);
        }
        else if (n.is_ite()) {
            augment_ite(id, n, cs);
        }
        else if (nc == 0) { 
            augment_aig0(id, n, cs);
        }
        else if (nc == 1) {
            augment_aig1(id, n, cs);
        }
        else if (nc == 2) {
            augment_aig2(id, n, cs);
        }
        else if (nc <= cut::max_cut_size()) {
            augment_aigN(id, n, cs);
        }
        if (m_insertions > 0) {
            touch(id);
        }
    }

    bool aig_cuts::insert_cut(unsigned v, cut const& c, cut_set& cs) {
        if (!cs.insert(m_on_cut_add, m_on_cut_del, c)) {
            return true;
        }
        m_num_cuts++;
        if (++m_insertions > max_cutset_size(v)) {
            return false;
        }
        while (cs.size() >= max_cutset_size(v)) {
            // never evict the first entry, it is used for the starting point
            unsigned idx = 1 + (m_rand() % (cs.size() - 1));
            evict(cs, idx);
        }
        return true;
    }

    void aig_cuts::augment_lut(unsigned v, lut const& n, cut_set& cs) {
        IF_VERBOSE(4, n.display(verbose_stream() << "augment_lut " << v << " ") << "\n");
        literal l1 = n.child(0);
        VERIFY(&cs != &lit2cuts(l1));
        for (auto const& a : lit2cuts(l1)) {
            m_tables[0] = &a;
            m_lits[0] = l1;
            cut b(a);
            augment_lut_rec(v, n, b, 1, cs);                        
        }
    }

    void aig_cuts::augment_lut_rec(unsigned v, lut const& n, cut& a, unsigned idx, cut_set& cs) {
        if (idx < n.size()) {
            literal lit = n.child(idx); 
            VERIFY(&cs != &lit2cuts(lit));
            for (auto const& b : lit2cuts(lit)) {
                cut ab;
                if (!ab.merge(a, b)) continue;
                m_tables[idx] = &b;
                m_lits[idx] = lit;
                augment_lut_rec(v, n, ab, idx + 1, cs);                
            }
            return;
        }
        for (unsigned i = n.size(); i-- > 0; ) { 
            m_luts[i] = m_tables[i]->shift_table(a);            
        }
        uint64_t r = 0;
        SASSERT(a.size() <= 6);
        SASSERT(n.size() <= 6);
        for (unsigned j = (1u << a.size()); j-- > 0; ) {
            unsigned w = 0;
            // when computing the output at position j, 
            // the i'th bit to index into n.lut() is 
            // based on the j'th output bit in lut[i]
            // m_lits[i].sign() tracks if output bit is negated
            for (unsigned i = n.size(); i-- > 0; ) {
                w |= (((m_luts[i] >> j) ^ (uint64_t)m_lits[i].sign()) & 1u) << i;
            }
            r |= ((n.table() >> w) & 1u) << j;
        } 
        a.set_table(r);
        IF_VERBOSE(8,
            verbose_stream() << "lut: " << v << " - " << a << "\n";
            for (unsigned i = 0; i < n.size(); ++i) {
                verbose_stream() << m_lits[i] << ": " << *m_tables[i] << "\n";
            });
        insert_cut(v, a, cs);
    }  

    void aig_cuts::augment_ite(unsigned v, node const& n, cut_set& cs) {
        IF_VERBOSE(4, display(verbose_stream() << "augment_ite " << v << " ", n) << "\n");
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        literal l3 = child(n, 2);
        VERIFY(&cs != &lit2cuts(l1)); 
        VERIFY(&cs != &lit2cuts(l2));  
        VERIFY(&cs != &lit2cuts(l3));  
        for (auto const& a : lit2cuts(l1)) {
            for (auto const& b : lit2cuts(l2)) {
                cut ab;
                if (!ab.merge(a, b)) continue;                
                for (auto const& c : lit2cuts(l3)) {
                    cut abc;
                    if (!abc.merge(ab, c)) continue;                    
                    uint64_t t1 = a.shift_table(abc);
                    uint64_t t2 = b.shift_table(abc);
                    uint64_t t3 = c.shift_table(abc);
                    if (l1.sign()) t1 = ~t1;
                    if (l2.sign()) t2 = ~t2;
                    if (l3.sign()) t3 = ~t3;
                    abc.set_table((t1 & t2) | ((~t1) & t3));
                    if (n.sign()) abc.negate();
                    if (!insert_cut(v, abc, cs)) return;
                } 
            }
        }
    }

    void aig_cuts::augment_aig0(unsigned v, node const& n, cut_set& cs) {
        IF_VERBOSE(4, display(verbose_stream() << "augment_unit " << v << " ", n) << "\n");
        SASSERT(n.is_and() && n.size() == 0);
        reset(cs);
        cut c;
        c.set_table(n.sign() ? 0x0 : 0x1);
        push_back(cs, c);
    }

    void aig_cuts::augment_aig1(unsigned v, node const& n, cut_set& cs) {
        IF_VERBOSE(4, display(verbose_stream() << "augment_aig1 " << v << " ", n) << "\n");
        SASSERT(n.is_and());
        literal lit = child(n, 0);
        VERIFY(&cs != &lit2cuts(lit));
        for (auto const& a : lit2cuts(lit)) {
            cut c(a);
            if (n.sign()) c.negate();
            if (!insert_cut(v, c, cs)) return;             
        }
    }

    void aig_cuts::augment_aig2(unsigned v, node const& n, cut_set& cs) {
        IF_VERBOSE(4, display(verbose_stream() << "augment_aig2 " << v << " ", n) << "\n");
        SASSERT(n.is_and() || n.is_xor());
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        VERIFY(&cs != &lit2cuts(l1));
        VERIFY(&cs != &lit2cuts(l2));
        for (auto const& a : lit2cuts(l1)) {
            for (auto const& b : lit2cuts(l2)) {
                cut c;            
                if (!c.merge(a, b)) continue;                
                uint64_t t1 = a.shift_table(c);
                uint64_t t2 = b.shift_table(c);
                if (l1.sign()) t1 = ~t1;
                if (l2.sign()) t2 = ~t2;
                uint64_t t3 = n.is_and() ? (t1 & t2) : (t1 ^ t2);
                c.set_table(t3);
                if (n.sign()) c.negate();
                // validate_aig2(a, b, v, n, c); 
                if (!insert_cut(v, c, cs)) return;                
            }
        }
    }

    void aig_cuts::augment_aigN(unsigned v, node const& n, cut_set& cs) {
        IF_VERBOSE(4, display(verbose_stream() << "augment_aigN " << v << " ", n) << "\n");
        m_cut_set1.reset(m_on_cut_del);
        SASSERT(n.is_and() || n.is_xor());
        literal lit = child(n, 0);
        for (auto const& a : lit2cuts(lit)) {
            cut b(a);
            if (lit.sign()) {
                b.negate();
            }            
            m_cut_set1.push_back(m_on_cut_add, b);
        }
        for (unsigned i = 1; i < n.size(); ++i) {
            m_cut_set2.reset(m_on_cut_del);
            lit = child(n, i);
            m_insertions = 0;
            for (auto const& a : m_cut_set1) {
                for (auto const& b : lit2cuts(lit)) {
                    cut c;
                    if (!c.merge(a, b)) continue;
                    uint64_t t1 = a.shift_table(c);
                    uint64_t t2 = b.shift_table(c);
                    if (lit.sign()) t2 = ~t2;
                    uint64_t t3 = n.is_and() ? (t1 & t2) : (t1 ^ t2);
                    c.set_table(t3);
                    if (i + 1 == n.size() && n.sign()) c.negate();
                    if (!insert_cut(UINT_MAX, c, m_cut_set2)) goto next_child;                    
                }
            }
        next_child:
            m_cut_set1.swap(m_cut_set2);
        }
        m_insertions = 0;
        for (auto & cut : m_cut_set1) {
            // validate_aigN(v, n, cut);
            if (!insert_cut(v, cut, cs)) {
                break;
            }
        }        
    }

    bool aig_cuts::is_touched(bool_var v, node const& n) {
        for (unsigned i = 0; i < n.size(); ++i) {
            literal lit = m_literals[n.offset() + i];
            if (is_touched(lit)) {
                return true;
            }
        }
        return is_touched(v);
    }

    void aig_cuts::reserve(unsigned v) {
        m_aig.reserve(v + 1);
        m_cuts.reserve(v + 1);
        m_max_cutset_size.reserve(v + 1, m_config.m_max_cutset_size);
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

    void aig_cuts::add_node(bool_var v, node const& n) {
        for (unsigned i = 0; i < n.size(); ++i) {
            reserve(m_literals[i].var());
            if (m_aig[m_literals[i].var()].empty()) {
                add_var(m_literals[i].var());
            }
        }
        if (m_aig[v].empty() || n.is_const()) {
            m_aig[v].reset();
            m_aig[v].push_back(n); 
            on_node_add(v, n);            
            init_cut_set(v);
            if (n.is_const()) {
                augment_aig0(v, n, m_cuts[v]);
            }
            touch(v);
            IF_VERBOSE(12, display(verbose_stream() << "add " << v << " == ", n) << "\n");            
        }
        else if (m_aig[v][0].is_const() || !insert_aux(v, n)) {
            m_literals.shrink(m_literals.size() - n.size());
            TRACE("cut_simplifier", tout << "duplicate\n";);
        }
        SASSERT(!m_aig[v].empty());
    }

    void aig_cuts::add_node(bool_var v, uint64_t lut, unsigned sz, bool_var const* args) {
        TRACE("cut_simplifier", tout << v << " == " << cut::table2string(sz, lut) << " " << bool_var_vector(sz, args) << "\n";);
        reserve(v);
        unsigned offset = m_literals.size();
        node n(lut, sz, offset);
        for (unsigned i = 0; i < sz; ++i) {
            reserve(args[i]);
            m_literals.push_back(literal(args[i], false));
        }
        add_node(v, n);
    }

    void aig_cuts::add_node(literal head, bool_op op, unsigned sz, literal const* args) {
        TRACE("cut_simplifier", tout << head << " == " << op << " " << literal_vector(sz, args) << "\n";);
        unsigned v = head.var();
        reserve(v);
        unsigned offset = m_literals.size();
        node n(head.sign(), op, sz, offset);
        m_literals.append(sz, args);
        for (unsigned i = 0; i < sz; ++i) reserve(args[i].var());
        if (op == and_op || op == xor_op) {
            std::sort(m_literals.data() + offset, m_literals.data() + offset + sz);
        }
        add_node(v, n);
    }

    void aig_cuts::add_cut(bool_var v, uint64_t lut, bool_var_vector const& args) {
        // args can be assumed to be sorted
        DEBUG_CODE(for (unsigned i = 0; i + 1 < args.size(); ++i) VERIFY(args[i] < args[i+1]););
        add_var(v);
        for (bool_var w : args) add_var(w); 
        cut c;
        for (bool_var w : args) VERIFY(c.add(w));
        c.set_table(lut);
        insert_cut(v, c, m_cuts[v]);
    }


    void aig_cuts::set_root(bool_var v, literal r) {
        IF_VERBOSE(10, verbose_stream() << "set-root " << v << " -> " << r << "\n");
        m_roots.push_back(std::make_pair(v, r));
    }

    void aig_cuts::flush_roots() {
        if (m_roots.empty()) return;
        to_root to_root;
        for (unsigned i = m_roots.size(); i-- > 0; ) {
            bool_var v = m_roots[i].first;
            literal  r = m_roots[i].second;
            reserve(v);
            reserve(r.var());
            literal rr = to_root[r.var()];
            to_root[v] = r.sign() ? ~rr : rr;
        }
        for (unsigned i = 0; i < m_aig.size(); ++i) {
            // invalidate nodes that have been rooted
            if (to_root[i] != literal(i, false)) {
                m_aig[i].reset();
                reset(m_cuts[i]);
            }
            else {
                unsigned j = 0;
                for (node & n : m_aig[i]) {
                    if (flush_roots(i, to_root, n)) {
                        m_aig[i][j++] = n;
                    }
                }
                m_aig[i].shrink(j);
            }
        }
        for (cut_set& cs : m_cuts) {
            flush_roots(to_root, cs);
        }
        m_roots.reset();
        TRACE("cut_simplifier", display(tout););
    }

    bool aig_cuts::flush_roots(bool_var var, to_root const& to_root, node& n) {
        bool changed = false;
        for (unsigned i = 0; i < n.size(); ++i) {
            literal& lit = m_literals[n.offset() + i];
            literal r = to_root[lit.var()];
            if (r != lit) {
                changed = true;
                lit = lit.sign() ? ~r : r;
            }
            if (lit.var() == var) {
                return false;
            }
        }
        if (changed && (n.is_and() || n.is_xor())) {
            std::sort(m_literals.data() + n.offset(), m_literals.data() + n.offset() + n.size());
        }
        return true;
    }

    void aig_cuts::flush_roots(to_root const& to_root, cut_set& cs) {
        for (unsigned j = 0; j < cs.size(); ++j) {
            for (unsigned v : cs[j]) {
                if (to_root[v] != literal(v, false)) {
                    evict(cs, j--);
                    break;
                }
            }
        }
    }

    lbool aig_cuts::get_value(bool_var v) const {
        return (m_aig[v].size() == 1 && m_aig[v][0].is_const()) ? 
            (m_aig[v][0].sign() ? l_false : l_true) : 
            l_undef;
    }

    void aig_cuts::init_cut_set(unsigned id) {
        SASSERT(m_aig[id].size() == 1);
        SASSERT(m_aig[id][0].is_valid());
        auto& cut_set = m_cuts[id];
        reset(cut_set);
        cut_set.init(m_region, m_config.m_max_cutset_size + 1, id);
        push_back(cut_set, cut(id));
    }

    bool aig_cuts::eq(node const& a, node const& b) {
        if (a.is_valid() != b.is_valid()) return false;
        if (!a.is_valid()) return true;
        if (a.op() != b.op() || a.sign() != b.sign() || a.size() != b.size()) 
            return false;
        for (unsigned i = a.size(); i-- > 0; ) {
            if (m_literals[a.offset() + i] != m_literals[b.offset() + i]) 
                return false;
        }
        return true;
    }

    bool aig_cuts::similar(node const& a, node const& b) {
        bool sim = true;
        sim = a.is_lut() && !b.is_lut() && a.size() == b.size();
        for (unsigned i = a.size(); sim && i-- > 0; ) {
            sim = m_literals[a.offset() + i].var() == m_literals[b.offset() + i].var();
        }
        return sim;
    }

    bool aig_cuts::insert_aux(unsigned v, node const& n) {
        if (!m_config.m_full) return false;
        unsigned num_gt = 0, num_eq = 0;
        for (node const& n2 : m_aig[v]) {
            if (eq(n, n2) || similar(n, n2)) return false;
            else if (n.size() < n2.size()) num_gt++;
            else if (n.size() == n2.size()) num_eq++;
        }
        if (m_aig[v].size() < m_config.m_max_aux) {
            on_node_add(v, n);
            m_aig[v].push_back(n);
            touch(v);
            return true;
        }
        if (num_gt > 0) {
            unsigned idx = rand() % num_gt;
            for (node const& n2 : m_aig[v]) {
                if (n.size() < n2.size()) {
                    if (idx == 0) {
                        on_node_del(v, m_aig[v][idx]);
                        on_node_add(v, n);
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
                        on_node_del(v, m_aig[v][idx]);
                        on_node_add(v, n);
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

    cut_val aig_cuts::eval(node const& n, cut_eval const& env) const {
        uint64_t result;
        switch (n.op()) {
        case var_op:
            UNREACHABLE();
            break;
        case and_op:
            result = ~0ull;
            for (unsigned i = 0; i < n.size(); ++i) {
                literal u = m_literals[n.offset() + i];
                uint64_t uv = u.sign() ? env[u.var()].m_f : env[u.var()].m_t;
                result &= uv;
            }
            break;
        case xor_op: 
            result = 0ull;
            for (unsigned i = 0; i < n.size(); ++i) {
                literal u = m_literals[n.offset() + i];
                uint64_t uv = u.sign() ? env[u.var()].m_f : env[u.var()].m_t;
                result ^= uv;
            }
            break;
        case ite_op: {
            literal u = m_literals[n.offset() + 0]; 
            literal v = m_literals[n.offset() + 1]; 
            literal w = m_literals[n.offset() + 2]; 
            uint64_t uv = u.sign() ? env[u.var()].m_f : env[u.var()].m_t;
            uint64_t vv = v.sign() ? env[v.var()].m_f : env[v.var()].m_t;
            uint64_t wv = w.sign() ? env[w.var()].m_f : env[w.var()].m_t;
            result = (uv & vv) | ((~uv) & wv);
            break;
        }
        default:
            UNREACHABLE();
        }
        if (n.sign()) result = ~result;
        return cut_val(result, ~result);
    }
    
    cut_eval aig_cuts::simulate(unsigned num_rounds) {
        cut_eval result;
        for (unsigned i = 0; i < m_cuts.size(); ++i) {
            uint64_t r = 
                (uint64_t)m_rand() + ((uint64_t)m_rand() << 16ull) + 
                ((uint64_t)m_rand() << 32ull) + ((uint64_t)m_rand() << 48ull);
            result.push_back(cut_val(r, ~r));
        }
        for (unsigned i = 0; i < num_rounds; ++i) {
            for (unsigned j = 0; j < m_cuts.size(); ++j) {
                cut_set const& cs = m_cuts[j];
                if (cs.size() <= 1) {
                    if (!m_aig[j].empty() && !m_aig[j][0].is_var()) {
                        result[j] = eval(m_aig[j][0], result);
                    }
                }
                else if (cs.size() > 1) {
                    cut const& c = cs[1 + (m_rand() % (cs.size() - 1))];
                    result[j] = c.eval(result);
                }
            }
        }
        return result;
    }


    void aig_cuts::on_node_add(unsigned v, node const& n) {
        if (m_on_clause_add) {
            node2def(m_on_clause_add, n, literal(v, false));
        }
    }

    void aig_cuts::on_node_del(unsigned v, node const& n) {
        if (m_on_clause_del) {
            node2def(m_on_clause_del, n, literal(v, false));        
        }
    }

    void aig_cuts::set_on_clause_add(on_clause_t& on_clause_add) {
        m_on_clause_add = on_clause_add;
        std::function<void(unsigned v, cut const& c)> _on_cut_add = 
            [this](unsigned v, cut const& c) { cut2def(m_on_clause_add, c, literal(v, false)); };
        m_on_cut_add = _on_cut_add;
    }

    void aig_cuts::set_on_clause_del(on_clause_t& on_clause_del) {
        m_on_clause_del = on_clause_del;
        std::function<void(unsigned v, cut const& c)> _on_cut_del = 
            [this](unsigned v, cut const& c) { cut2def(m_on_clause_del, c, literal(v, false)); };
        m_on_cut_del = _on_cut_del;
    }

    /**
     * Encode the cut (variables and truth-table) in a set of clauses.
     * r is the result.
     */

    void aig_cuts::cut2def(on_clause_t& on_clause, cut const& c, literal r) {
        IF_VERBOSE(10, verbose_stream() << "cut2def: " << r << " == " << c << "\n");
        VERIFY(r != null_literal);
        unsigned sz = c.size();
        unsigned num_assigns = 1 << sz;
        for (unsigned i = 0; i < num_assigns; ++i) {
            m_clause.reset();
            for (unsigned j = 0; j < sz; ++j) {
                literal lit(c[j], 0 != (i & (1ull << j)));
                m_clause.push_back(lit);                
            }
            literal rr = r;
            if (0 == (c.table() & (1ull << i))) rr.neg();
            m_clause.push_back(rr);
            on_clause(m_clause);
        }
    }

    void aig_cuts::node2def(on_clause_t& on_clause, node const& n, literal r) {
        IF_VERBOSE(10, display(verbose_stream() << "node2def " << r << " == ", n) << "\n");
        SASSERT(on_clause);
        literal c, t, e;
        if (n.sign()) r.neg();
        m_clause.reset();
        unsigned num_comb = 0;
        switch (n.op()) {
        case var_op:
            return;
        case and_op:
            for (unsigned i = 0; i < n.size(); ++i) {
                m_clause.push_back(~r);
                m_clause.push_back(m_literals[n.offset() + i]);
                on_clause(m_clause);
                m_clause.reset();
            }
            for (unsigned i = 0; i < n.size(); ++i) {
                m_clause.push_back(~m_literals[n.offset()+i]);
            }
            m_clause.push_back(r);
            on_clause(m_clause);
            return;
        case ite_op:
            // r & c => t, r & ~c => e
            // ~r & c => ~t, ~r & ~c => ~e
            SASSERT(n.size() == 3);
            c = m_literals[n.offset()+0];
            t = m_literals[n.offset()+1];
            e = m_literals[n.offset()+2];
            m_clause.push_back(~r, ~c, t);
            on_clause(m_clause);
            m_clause.reset();
            m_clause.push_back(~r, c, e);
            on_clause(m_clause);
            m_clause.reset();
            m_clause.push_back(r, ~c, ~t);
            on_clause(m_clause);
            m_clause.reset();
            m_clause.push_back(r, c, ~e);
            on_clause(m_clause);
            return;
        case xor_op: 
            // r = a ^ b ^ c
            // <=>
            // ~r ^ a ^ b ^ c = 1
            if (n.size() > 10) {
                throw default_exception("cannot handle large xors");
            }
            num_comb = (1 << n.size());
            for (unsigned i = 0; i < num_comb; ++i) {
                bool parity = n.size() % 2 == 1;
                m_clause.reset();
                for (unsigned j = 0; j < n.size(); ++j) {
                    literal lit = m_literals[n.offset() + j];
                    if (0 == (i & (1 << j))) {
                        lit.neg();
                    }
                    else {
                        parity ^= true;
                    }
                    m_clause.push_back(lit);
                }
                m_clause.push_back(parity ? r : ~r);
                TRACE("cut_simplifier", tout << "validate: " << m_clause << "\n";);
                on_clause(m_clause);
            }
            return;
        case lut_op: 
            // r = LUT(v0, v1, v2)
            num_comb = (1 << n.size());
            for (unsigned i = 0; i < num_comb; ++i) {
                m_clause.reset();
                for (unsigned j = 0; j < n.size(); ++j) {
                    literal lit = m_literals[n.offset() + j];
                    if (0 != (i & (1 << j))) lit.neg();
                    m_clause.push_back(lit);
                }
                m_clause.push_back(0 == (n.lut() & (1ull << i)) ? ~r : r);
                TRACE("cut_simplifier", tout << n.lut() << " " <<  m_clause << "\n";);
                on_clause(m_clause);
            }
            return;
        default:
            UNREACHABLE();
            break;
        }
    }

    /**
     * compile the truth table from c into clauses that define ~v.
     * compile definitions for nodes until all inputs have been covered.
     * Assume only the first definition for a node is used for all cuts.
     */
    void aig_cuts::cut2clauses(on_clause_t& on_clause, unsigned v, cut const& c) {
        bool_vector visited(m_aig.size(), false);
        for (unsigned u : c) visited[u] = true;
        unsigned_vector todo;
        todo.push_back(v);

        while (!todo.empty()) {
            unsigned u = todo.back();
            todo.pop_back();
            if (visited[u]) {
                continue;
            }
            visited[u] = true;
            node const& n = m_aig[u][0];
            node2def(on_clause, n, literal(u, false));
            for (unsigned i = 0; i < n.size(); ++i) {
                todo.push_back(m_literals[n.offset()+i].var());
            }
        }        
        cut2def(on_clause, c, literal(v, true));
    }

    /**
     * simplify a set of cuts by removing don't cares.
     */
    void aig_cuts::simplify() {        
        uint64_t masks[7];
        for (unsigned i = 0; i <= 6; ++i) {
            masks[i] = cut::effect_mask(i);
        }
        unsigned dont_cares = 0;
        for (cut_set & cs : m_cuts) {
            for (cut const& c : cs) {
                uint64_t t = c.table();
                for (unsigned i = 0; i < std::min(6u, c.size()); ++i) {
                    uint64_t diff = masks[i] & (t ^ (t >> (1ull << i)));
                    if (diff == 0ull) {
                        cut d(c);
                        d.remove_elem(i);
                        cs.insert(m_on_cut_add, m_on_cut_del, d);
                        cs.evict(m_on_cut_del, c);
                        ++dont_cares;
                        break;
                    }
                }
            }
        }
        IF_VERBOSE(0, verbose_stream() << "#don't cares " << dont_cares << "\n");
    }

    struct aig_cuts::validator {
        aig_cuts& t;
        params_ref p;
        reslimit lim;
        solver s;
        unsigned_vector vars;
        bool_vector   is_var;

        validator(aig_cuts& t):t(t),s(p, lim) {
            p.set_bool("cut_simplifier", false);
            s.updt_params(p);
        }

        void on_clause(literal_vector const& clause) {
            IF_VERBOSE(20, verbose_stream() << clause << "\n");
            for (literal lit : clause) {
                while (lit.var() >= s.num_vars()) s.mk_var();
                is_var.reserve(lit.var() + 1, false);
                if (!is_var[lit.var()]) { vars.push_back(lit.var()); is_var[lit.var()] = true; }
            }
            s.mk_clause(clause);            
        }
        
        void check() {
            lbool r = s.check();
            IF_VERBOSE(10, verbose_stream() << "check: " << r << "\n");
            if (r == l_true) {
                std::sort(vars.begin(), vars.end());
                s.display(std::cout);
                for (auto v : vars) std::cout << v << " := " << s.get_model()[v] << "\n";
                std::string line;
                std::getline(std::cin, line);
            }
        }
    };

    void aig_cuts::validate_aig2(cut const& a, cut const& b, unsigned v, node const& n, cut const& c) {
        validator val(*this);
        on_clause_t on_clause = [&](literal_vector const& clause) { val.on_clause(clause); };
        cut2def(on_clause, a, literal(child(n, 0).var(), false));
        cut2def(on_clause, b, literal(child(n, 1).var(), false));
        cut2def(on_clause, c, literal(v, false));
        node2def(on_clause, n, literal(v, true));
        val.check();
    } 

    void aig_cuts::validate_aigN(unsigned v, node const& n, cut const& c) {
        IF_VERBOSE(10, verbose_stream() << "validate_aigN " << v << " == " << c << "\n");
        validator val(*this);
        on_clause_t on_clause = [&](literal_vector const& clause) { val.on_clause(clause); };
        for (unsigned i = 0; i < n.size(); ++i) {
            unsigned w = m_literals[n.offset() + i].var();
            for (cut const& d : m_cuts[w]) {
                cut2def(on_clause, d, literal(w, false));
            }
        }
        cut2def(on_clause, c, literal(v, false));
        node2def(on_clause, n, literal(v, true));
        val.check();
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

