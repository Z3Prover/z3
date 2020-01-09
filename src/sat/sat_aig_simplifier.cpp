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
        stopwatch       m_watch;
        report(aig_simplifier& s): s(s) { m_watch.start(); }
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

    aig_simplifier::aig_simplifier(solver& s):
        s(s), 
        m_aig_cuts(m_config.m_max_cut_size, m_config.m_max_cutset_size),
        m_trail_size(0) {        
    }

    void aig_simplifier::add_and(literal head, unsigned sz, literal const* lits) {
        m_aig_cuts.add_node(head, and_op, sz, lits);
        m_stats.m_num_ands++;
    }

    //      head == l1 or l2 or l3 
    // <=> 
    //     ~head == ~l1 and ~l2 and ~l3
    void aig_simplifier::add_or(literal head, unsigned sz, literal const* lits) {
        m_lits.reset();
        m_lits.append(sz, lits);
        for (unsigned i = 0; i < sz; ++i) m_lits[i].neg();
        m_aig_cuts.add_node(~head, and_op, sz, m_lits.c_ptr());
        m_stats.m_num_ands++;
    }

    void aig_simplifier::add_xor(literal head, unsigned sz, literal const* lits) {
        m_aig_cuts.add_node(head, xor_op, sz, lits);
        m_stats.m_num_xors++;
    }

    void aig_simplifier::add_ite(literal head, literal c, literal t, literal e) {
        literal lits[3] = { c, t, e };
        m_aig_cuts.add_node(head, ite_op, 3, lits);
        m_stats.m_num_ites++;
    }

    void aig_simplifier::add_iff(literal head, literal l1, literal l2) {
        literal lits[2] = { l1, ~l2 };
        m_aig_cuts.add_node(head, xor_op, 2, lits);
        m_stats.m_num_xors++;
    }

    void aig_simplifier::operator()() {
        report _report(*this);
        TRACE("aig_simplifier", s.display(tout););
        clauses2aig();
        aig2clauses();
    }

    /**
       \brief extract AIG definitions from clauses
       Ensure that they are sorted and variables have unique definitions.
     */
    void aig_simplifier::clauses2aig() {

        // update units
        for (; m_trail_size < s.init_trail_size(); ++m_trail_size) {
            literal lit = s.trail_literal(m_trail_size);
            m_aig_cuts.add_node(lit, and_op, 0, 0);
        }
        
        
        std::function<void (literal head, literal_vector const& ands)> on_and = 
            [&,this](literal head, literal_vector const& ands) {
            m_aig_cuts.add_node(head, and_op, ands.size(), ands.c_ptr());
            m_stats.m_num_ands++;
        };
        std::function<void (literal head, literal c, literal t, literal e)> on_ite = 
            [&,this](literal head, literal c, literal t, literal e) {            
            literal args[3] = { c, t, e };            
            m_aig_cuts.add_node(head, ite_op, 3, args);
            m_stats.m_num_ites++;
        };
        aig_finder af(s);
        af.set(on_and);
        af.set(on_ite);
        clause_vector clauses(s.clauses());
        af(clauses);

        std::function<void (literal_vector const&)> on_xor = 
            [&,this](literal_vector const& xors) {
            SASSERT(xors.size() > 1);
            unsigned max_level = xors.back().var();
            unsigned index = xors.size() - 1;
            for (unsigned i = index; i-- > 0; ) {
                literal l = xors[i];
                if (l.var() > max_level) {
                    max_level = l.var();
                    index = i;
                }
            }
            // head + t1 + t2 + .. = 1 
            // <=> 
            // ~head = t1 + t2 + ..
            literal head = ~xors[index];
            unsigned sz = xors.size() - 1;
            for (unsigned i = xors.size(); i-- > 0; ) {
                if (i != index) 
                    m_lits.push_back(xors[i]);
            }
            m_aig_cuts.add_node(head, xor_op, sz, m_lits.c_ptr());
            m_lits.reset();
            m_stats.m_num_xors++;            
        };
        xor_finder xf(s);
        xf.set(on_xor);
        xf(clauses);       
    }

    void aig_simplifier::aig2clauses() {
        vector<cut_set> const& cuts = m_aig_cuts.get_cuts();
        map<cut const*, unsigned, cut::hash_proc, cut::eq_proc> cut2id;
        
        union_find_default_ctx ctx;
        union_find<> uf(ctx), uf2(ctx);
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf.mk_var();
        auto add_eq = [&](literal l1, literal l2) {
            uf.merge(l1.index(), l2.index());
            uf.merge((~l1).index(), (~l2).index());
        };
        bool new_eq = false;
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
                    new_eq = true;
                    break;
                }
                cut.negate();
                if (cut2id.find(&cut, j)) {
                    literal v(i, false);
                    literal w(j, true);
                    add_eq(v, w);
                    TRACE("aig_simplifier", tout << v << " == " << w << "\n";);
                    new_eq = true;
                    break;
                }
                cut.negate();
                cut2id.insert(&cut, i);                
            }
        }        
        if (!new_eq) {
            return;
        }
        new_eq = false;
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf2.mk_var();
        // extract equivalences over non-eliminated literals.
        for (unsigned idx = 0; idx < uf.get_num_vars(); ++idx) {
            if (!uf.is_root(idx) || 1 == uf.size(idx)) continue;
            literal root = null_literal;
            unsigned first = idx;
            do {
                literal lit = to_literal(idx);
                if (!s.was_eliminated(lit)) {
                    if (root == null_literal) {
                        root = lit;
                    }
                    else {
                        uf2.merge(lit.index(), root.index());
                        new_eq = true;
                        ++m_stats.m_num_eqs;
                    }
                }
                idx = uf.next(idx);
            }
            while (first != idx);
        }
        if (!new_eq) {
            return;
        }
        elim_eqs elim(s);
        elim(uf2);        
    }

    void aig_simplifier::collect_statistics(statistics& st) const {
        st.update("sat-aig.eqs",  m_stats.m_num_eqs);
        st.update("sat-aig.cuts", m_stats.m_num_cuts);
        st.update("sat-aig.ands", m_stats.m_num_ands);
        st.update("sat-aig.ites", m_stats.m_num_ites);
        st.update("sat-aig.xors", m_stats.m_num_xors);
    }
    
    aig_cuts::aig_cuts(unsigned max_cut_size, unsigned max_cutset_size) {
        m_max_cut_size = std::min(cut().max_cut_size, max_cut_size);
        m_max_cutset_size = max_cutset_size;
    }

    vector<cut_set> const& aig_cuts::get_cuts() {
        unsigned_vector node_ids = filter_valid_nodes();
        m_cut_set1.init(m_region, m_max_cutset_size + 1);
        m_cut_set2.init(m_region, m_max_cutset_size + 1);
        augment(node_ids, m_cuts);
        return m_cuts;
    }

    void aig_cuts::augment(unsigned_vector const& ids, vector<cut_set>& cuts) {
        for (unsigned id : ids) {
            node const& n = m_aig[id];
            SASSERT(n.is_valid());
            auto& cut_set = cuts[id];
            if (n.is_var()) {
                SASSERT(!n.sign());
            }
            else if (n.is_ite()) {
                augment_ite(n, cut_set, cuts);
            }
            else if (n.num_children() == 0) {
                augment_aig0(n, cut_set, cuts);
            }
            else if (n.num_children() == 1) {
                augment_aig1(n, cut_set, cuts);
            }
            else if (n.num_children() == 2) {
                augment_aig2(n, cut_set, cuts);
            }
            else if (n.num_children() < m_max_cut_size && cut_set.size() < m_max_cutset_size) {
                augment_aigN(n, cut_set, cuts);
            }
        }
    }

    void aig_cuts::augment_ite(node const& n, cut_set& cs, vector<cut_set>& cuts) {
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        literal l3 = child(n, 2);
        for (auto const& a : cuts[l1.var()]) {
            for (auto const& b : cuts[l2.var()]) {
                cut ab;
                if (!ab.merge(a, b, m_max_cut_size)) {
                    continue;
                }
                for (auto const& c : cuts[l3.var()]) {
                    cut abc;
                    if (!abc.merge(ab, c, m_max_cut_size)) {
                        continue;
                    }
                    if (cs.size() >= m_max_cutset_size) break;
                    uint64_t t1 = a.shift_table(abc);
                    uint64_t t2 = b.shift_table(abc);
                    uint64_t t3 = c.shift_table(abc);
                    if (l1.sign()) t1 = ~t1;
                    if (l2.sign()) t2 = ~t2;
                    if (l3.sign()) t3 = ~t3;
                    abc.set_table((t1 & t2) | (~t1 & t3));
                    if (n.sign()) abc.negate();
                    // extract tree size: abc.m_tree_size = a.m_tree_size + b.m_tree_size + c.m_tree_size + 1;
                    cs.insert(abc);
                } 
            }
        }
    }

    void aig_cuts::augment_aig0(node const& n, cut_set& cs, vector<cut_set>& cuts) {
        SASSERT(n.is_and());
        cut c;          
        cs.reset();
        if (n.sign()) {
            c.m_table = 0;   // constant false
        }
        else {
            c.m_table = 0x3; // constant true
        }
        cs.insert(c);
    }

    void aig_cuts::augment_aig1(node const& n, cut_set& cs, vector<cut_set>& cuts) {
        SASSERT(n.is_and());
        literal lit = child(n, 0);
        for (auto const& a : cuts[lit.var()]) {
            if (cs.size() >= m_max_cutset_size) break;
            cut c;
            c.set_table(a.m_table);
            if (n.sign()) c.negate();
            cs.insert(c);
        }
    }

    void aig_cuts::augment_aig2(node const& n, cut_set& cs, vector<cut_set>& cuts) {
        SASSERT(n.is_and() || n.is_xor());
        literal l1 = child(n, 0);
        literal l2 = child(n, 1);
        for (auto const& a : cuts[l1.var()]) {
            for (auto const& b : cuts[l2.var()]) {
                if (cs.size() >= m_max_cutset_size) break;
                cut c;
                if (c.merge(a, b, m_max_cut_size)) {
                    uint64_t t1 = a.shift_table(c);
                    uint64_t t2 = b.shift_table(c);
                    if (l1.sign()) t1 = ~t1;
                    if (l2.sign()) t2 = ~t2;
                    uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                    c.set_table(t3);
                    if (n.sign()) c.negate();
                    cs.insert(c);
                }
            }
            if (cs.size() >= m_max_cutset_size) 
                break;
        }
    }

    void aig_cuts::augment_aigN(node const& n, cut_set& cs, vector<cut_set>& cuts) {
        m_cut_set1.reset();
        SASSERT(n.is_and() || n.is_xor());
        literal lit = child(n, 0);
        for (auto const& a : cuts[lit.var()]) {
            m_cut_set1.push_back(a);
            if (lit.sign()) {
                m_cut_set1.back().negate();
            }
        }
        for (unsigned i = 1; i < n.num_children(); ++i) {
            m_cut_set2.reset();
            literal lit = child(n, i);
            for (auto const& a : m_cut_set1) {
                for (auto const& b : cuts[lit.var()]) {
                    cut c;
                    if (m_cut_set2.size() + cs.size() >= m_max_cutset_size) 
                        break;
                    if (c.merge(a, b, m_max_cut_size)) {
                        uint64_t t1 = a.shift_table(c);
                        uint64_t t2 = b.shift_table(c);
                        if (lit.sign()) t2 = ~t2;
                        uint64_t t3 = n.is_and() ? t1 & t2 : t1 ^ t2;
                        c.set_table(t3);
                        if (i + 1 == n.num_children() && n.sign()) c.negate();
                        m_cut_set2.insert(c);
                    }
                }
                if (m_cut_set2.size() + cs.size() >= m_max_cutset_size) 
                    break;
            }
            m_cut_set1.swap(m_cut_set2);
        }
        for (auto & cut : m_cut_set1) {
            cs.insert(cut);
        }
    }

    void aig_cuts::add_var(unsigned v) {
        m_aig.reserve(v + 1);
        m_cuts.reserve(v + 1);
        if (!m_aig[v].is_valid()) {
            m_aig[v] = node(v);
            init_cut_set(v);
        }
        SASSERT(m_aig[v].is_valid());
    }

    void aig_cuts::add_node(literal head, bool_op op, unsigned sz, literal const* args) {
        TRACE("aig_simplifier", tout << head << " == " << op << " " << literal_vector(sz, args) << "\n";);
        unsigned v = head.var();
        m_aig.reserve(v + 1);
        unsigned offset = m_literals.size();
        node n(head.sign(), op, sz, offset);
        m_literals.append(sz, args);
        for (unsigned i = 0; i < sz; ++i) {
            if (!m_aig[args[i].var()].is_valid()) {
                add_var(args[i].var());
            }
        }
        if (!m_aig[v].is_valid() || m_aig[v].is_var() || (sz == 0)) {
            m_aig[v] = n;
            init_cut_set(v);
        }
        else {
            insert_aux(v, n);
        }
        SASSERT(m_aig[v].is_valid());
    }

    void aig_cuts::init_cut_set(unsigned id) {
        node const& n = m_aig[id];
        SASSERT(n.is_valid());
        auto& cut_set = m_cuts[id];
        cut_set.init(m_region, m_max_cutset_size + 1);
        cut_set.push_back(cut(id));    // TBD: if entry is a constant?
        if (m_aux_aig.size() < id) {
            m_aux_aig[id].reset();
        }
    }

    void aig_cuts::insert_aux(unsigned v, node const& n) {
        // TBD: throttle and replacement strategy
        m_aux_aig.reserve(v + 1);
        m_aux_aig[v].push_back(n);
    }

    unsigned_vector aig_cuts::filter_valid_nodes() {
        unsigned id = 0;
        unsigned_vector result;
        for (node const& n : m_aig) {
            if (n.is_valid()) result.push_back(id);
            ++id;
        }
        return result;
    }
}

