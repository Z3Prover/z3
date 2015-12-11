/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hilbert_basis.cpp

Abstract:

    Basic Hilbert Basis computation.

Author:

    Nikolaj Bjorner (nbjorner) 2013-02-09.

Revision History:

--*/

#include "hilbert_basis.h"
#include "heap.h"
#include "map.h"
#include "heap_trie.h"
#include "stopwatch.h"


typedef int_hashtable<int_hash, default_eq<int> > int_table;


class hilbert_basis::value_index1 {
    struct stats {
        unsigned m_num_comparisons;
        unsigned m_num_hit;
        unsigned m_num_miss;

        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };    

    hilbert_basis&     hb;
    int_table          m_table;
    stats              m_stats;

public:
    value_index1(hilbert_basis& hb):
        hb(hb)
    {}

    void insert(offset_t idx, values const& vs) {
        m_table.insert(idx.m_offset);
    }

    void remove(offset_t idx, values const& vs) {
        m_table.remove(idx.m_offset);
    }

    void reset() {
        m_table.reset();
    }

    bool find(offset_t idx, values const& vs) {
        // display_profile(idx, std::cout);
        int_table::iterator it = m_table.begin(), end = m_table.end();
        for (; it != end; ++it) {
            offset_t offs(*it);
            ++m_stats.m_num_comparisons;
            if (*it != static_cast<int>(idx.m_offset) && hb.is_subsumed(idx, offs)) {
                ++m_stats.m_num_hit;
                return true;
            }
        }
        ++m_stats.m_num_miss;
        return false;
    }

    void collect_statistics(statistics& st) const {
        st.update("hb.index.num_comparisons", m_stats.m_num_comparisons);
        st.update("hb.index.num_hit", m_stats.m_num_hit);
        st.update("hb.index.num_miss", m_stats.m_num_miss);
    }

    void reset_statistics() {
        m_stats.reset();
    }

    unsigned size() const {
        return m_table.size();
    }

    void display(std::ostream& out) const {
        int_table::iterator it = m_table.begin(), end = m_table.end();
        for (; it != end; ++it) {
            offset_t offs(*it);
            hb.display(out, offs);            
        }
        display_profile(out);
    }

private:

    typedef hashtable<numeral, numeral::hash_proc, numeral::eq_proc> numeral_set;

    void display_profile(std::ostream& out) const {
        vector<numeral_set> weights;
        weights.resize(hb.get_num_vars()+1);
        int_table::iterator it = m_table.begin(), end = m_table.end();
        for (; it != end; ++it) {
            offset_t offs(*it);
            values const& ws = hb.vec(offs);
            weights[0].insert(ws.weight());
            for (unsigned i = 0; i < hb.get_num_vars(); ++i) {
                weights[i+1].insert(ws[i]);
            }            
        }
        out << "profile: "; 
        for (unsigned i = 0; i < weights.size(); ++i) {
            out << weights[i].size() << " ";
        }
        out << "\n";
    }

    void display_profile(offset_t idx, std::ostream& out) {
        unsigned_vector leq;
        unsigned nv = hb.get_num_vars();
        values const& vs = hb.vec(idx);
        leq.resize(nv+1);
        numeral maxw(0);
        for (unsigned i = 0; i < nv; ++i) {
            if (!hb.is_abs_geq(maxw, vs[i])) {
                maxw = vs[i];
            }
        }
        unsigned num_below_max = 0;
        int_table::iterator it = m_table.begin(), end = m_table.end();
        for (; it != end; ++it) {
            offset_t offs(*it);
            values const& ws = hb.vec(offs);
            if (ws.weight() <= vs.weight()) {
                leq[0]++;
            }
            bool filtered = false;
            for (unsigned i = 0; i < nv; ++i) {
                if (hb.is_abs_geq(vs[i], ws[i])) {
                    leq[i+1]++;
                }
                if (!hb.is_abs_geq(maxw, ws[i])) {
                    filtered = true;
                }
            }
            if (!filtered) {
                ++num_below_max;
            }
        }
        out << vs.weight() << ":" << leq[0] << " ";
        for (unsigned i = 0; i < nv; ++i) {
            out << vs[i] << ":" << leq[i+1] << " ";
        }
        out << " max<= " << num_below_max;
        out << "\n";
    }
};

class hilbert_basis::value_index2 {
    struct key_le {
        hilbert_basis& hb;
        key_le(hilbert_basis& hb): hb(hb) {}
        bool le(numeral const& n1, numeral const& n2) const {
            return hb.is_abs_geq(n2, n1);
        }
    };

    typedef heap_trie<numeral, key_le, numeral::hash_proc, unsigned> ht;

    struct checker : public ht::check_value {
        hilbert_basis* hb;
        offset_t  m_value;
        checker(): hb(0) {}
        virtual bool operator()(unsigned const& v) {            
            if (m_value.m_offset != v) { //  && hb->is_subsumed(m_value, offset_t(v))) {
                return true;
            }
            else {
                return false;
            }
        }
    };
    hilbert_basis&               hb;
    key_le                       m_le;
    ht                           m_trie;
    checker                      m_checker;
    unsigned                     m_offset;

    numeral const* get_keys(values const& vs) {
        return vs()-m_offset;
    }

public:
    value_index2(hilbert_basis& hb): 
        hb(hb), 
        m_le(hb),
        m_trie(m_le),
        m_offset(1) {
        m_checker.hb = &hb;
    }

    void insert(offset_t idx, values const& vs) {
        m_trie.insert(get_keys(vs), idx.m_offset);
    }

    void remove(offset_t idx, values const& vs) {
        m_trie.remove(get_keys(vs));
    }

    void reset(unsigned offset) {
        m_offset = offset;
        m_trie.reset(hb.get_num_vars()+m_offset);
    }

    bool find(offset_t idx, values const& vs) {
        m_checker.m_value = idx;
        return m_trie.find_le(get_keys(vs), m_checker);
    }

    void collect_statistics(statistics& st) const {
        m_trie.collect_statistics(st);
    }

    void reset_statistics() {
        m_trie.reset_statistics();
    }

    unsigned size() const {
        return m_trie.size();
    }

    void display(std::ostream& out) const {
        // m_trie.display(out);
    }
};



class hilbert_basis::index {
    // for each non-positive weight a separate index.
    // for positive weights a shared value index.

    // typedef value_index1 value_index;
    typedef value_index2 value_index;
    // typedef value_index3 value_index;

    struct stats {
        unsigned m_num_find;
        unsigned m_num_insert;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };        

    template<typename Value>
    class numeral_map : public map<numeral, Value, numeral::hash_proc, numeral::eq_proc> {};

    typedef numeral_map<value_index*> value_map;
    hilbert_basis&   hb;
    value_map        m_neg;
    value_index      m_pos;
    value_index      m_zero;
    stats            m_stats;
    unsigned         m_num_ineqs;

public:
    index(hilbert_basis& hb): hb(hb), m_pos(hb), m_zero(hb), m_num_ineqs(0) {}
    
    void insert(offset_t idx, values const& vs) {
        ++m_stats.m_num_insert;
        if (vs.weight().is_pos()) {
            m_pos.insert(idx, vs);
        }
        else if (vs.weight().is_zero()) {
            m_zero.insert(idx, vs);
        }
        else {
            value_index* map = 0;
            if (!m_neg.find(vs.weight(), map)) {
                map = alloc(value_index, hb);
                map->reset(m_num_ineqs);
                m_neg.insert(vs.weight(), map);
            }
            map->insert(idx, vs);
        }
    }

    void remove(offset_t idx, values const& vs) {
        if (vs.weight().is_pos()) {
            m_pos.remove(idx, vs);
        }
        else if (vs.weight().is_zero()) {
            m_zero.remove(idx, vs);
        }
        else {
            m_neg.find(vs.weight())->remove(idx, vs);
        }        
    }

    bool find(offset_t idx, values const& vs) {
        ++m_stats.m_num_find;
        if (vs.weight().is_pos()) {
            return m_pos.find(idx,  vs);
        }
        else if (vs.weight().is_zero()) {
            return m_zero.find(idx, vs);
        }
        else {
            value_index* map;
            return
                m_neg.find(vs.weight(), map) && 
                map->find(idx, vs);
        }        
    }    

    void reset(unsigned num_ineqs) {
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_pos.reset(num_ineqs);
        m_zero.reset(num_ineqs);
        m_num_ineqs = num_ineqs;
        m_neg.reset();
    }

    void collect_statistics(statistics& st) const {
        m_pos.collect_statistics(st);
        m_zero.collect_statistics(st);
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            it->m_value->collect_statistics(st);
        }
        st.update("hb.index.num_find",   m_stats.m_num_find);
        st.update("hb.index.num_insert", m_stats.m_num_insert);
        st.update("hb.index.size",       size());
    }

    void reset_statistics() {
        m_pos.reset_statistics();
        m_zero.reset_statistics();
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            it->m_value->reset_statistics();
        }
    }

    void display(std::ostream& out) const {
        m_pos.display(out);
        m_zero.display(out);
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            it->m_value->display(out);
        }
    }
    
private:
    unsigned size() const {
        unsigned sz = m_pos.size();
        sz += m_zero.size();
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            sz += it->m_value->size();
        }        
        return sz;
    }
};

/**
   \brief priority queue for passive list.
*/

class hilbert_basis::passive {
    struct lt {
        passive** p;
        lt(passive** p): p(p) {}
        bool operator()(int v1, int v2) const {
            return (**p)(v1, v2);
        }
    };
    hilbert_basis&      hb;
    svector<offset_t>   m_passive;
    unsigned_vector     m_free_list;
    passive*            m_this;
    lt                  m_lt;
    heap<lt>            m_heap;    // binary heap over weights

    numeral sum_abs(offset_t idx) const {
        numeral w(0);
        unsigned nv = hb.get_num_vars();
        for (unsigned i = 0; i < nv; ++i) {
            w += abs(hb.vec(idx)[i]);
        }
        return w;
    }
    
public:
    
    passive(hilbert_basis& hb): 
        hb(hb),
        m_lt(&m_this),
        m_heap(10, m_lt)
    {
        m_this = this;
    }

    void reset() {
        m_heap.reset();
        m_free_list.reset();
        m_passive.reset();
    }
    
    bool empty() const {
        return m_heap.empty();
    }

    offset_t pop() {
        SASSERT(!empty());
        unsigned val = static_cast<unsigned>(m_heap.erase_min());        
        offset_t result = m_passive[val];
        m_free_list.push_back(val);
        m_passive[val] = mk_invalid_offset();
        return result;
    }
    
    void insert(offset_t idx) {
        unsigned v;
        if (m_free_list.empty()) {
            v = m_passive.size();
            m_passive.push_back(idx);
            m_heap.set_bounds(v+1);
        }
        else {
            v = m_free_list.back();
            m_free_list.pop_back();
            m_passive[v] = idx;
        }
        m_heap.insert(v);
    }

    class iterator {
        passive& p;
        unsigned m_idx;
        void fwd() {
            while (m_idx < p.m_passive.size() && 
                   is_invalid_offset(p.m_passive[m_idx])) {
                ++m_idx;
            }
        }
    public:
        iterator(passive& p, unsigned i): p(p), m_idx(i) { fwd(); }
        offset_t operator*() const { return p.m_passive[m_idx]; }
        iterator& operator++() { ++m_idx; fwd(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& it) const {return m_idx == it.m_idx; }
        bool operator!=(iterator const& it) const {return m_idx != it.m_idx; }
    };

    iterator begin() {
        return iterator(*this, 0);
    }

    iterator end() {
        return iterator(*this, m_passive.size());
    }

    bool operator()(int v1, int v2) const {
        offset_t idx1 = m_passive[v1];
        offset_t idx2 = m_passive[v2];
        return sum_abs(idx1) < sum_abs(idx2);
    }
};


class hilbert_basis::vector_lt_t {
    hilbert_basis& hb;
public:
    vector_lt_t(hilbert_basis& hb): hb(hb) {}
    bool operator()(offset_t idx1, offset_t idx2) const {
        return hb.vector_lt(idx1, idx2);
    }
};


class hilbert_basis::passive2 {
    struct lt {
        passive2** p;
        lt(passive2** p): p(p) {}
        bool operator()(int v1, int v2) const {
            return (**p)(v1, v2);
        }
    };
    hilbert_basis&      hb;
    svector<offset_t>   m_pos_sos;
    svector<offset_t>   m_neg_sos;
    vector<numeral>     m_pos_sos_sum;
    vector<numeral>     m_neg_sos_sum;
    vector<numeral>     m_sum_abs;
    unsigned_vector     m_psos;
    svector<offset_t>   m_pas;
    vector<numeral>     m_weight;
    unsigned_vector     m_free_list;
    passive2*           m_this;
    lt                  m_lt;
    heap<lt>            m_heap;    // binary heap over weights

    numeral sum_abs(offset_t idx) const {
        numeral w(0);
        unsigned nv = hb.get_num_vars();
        for (unsigned i = 0; i < nv; ++i) {
            w += abs(hb.vec(idx)[i]);
        }
        return w;
    }

public:
    passive2(hilbert_basis& hb): 
        hb(hb),
        m_lt(&m_this),
        m_heap(10, m_lt)
    {
        m_this = this;
    }

    void init(svector<offset_t> const& I) {
        for (unsigned i = 0; i < I.size(); ++i) {
            numeral const& w = hb.vec(I[i]).weight();
            if (w.is_pos()) {
                m_pos_sos.push_back(I[i]);
                m_pos_sos_sum.push_back(sum_abs(I[i]));
            }
            else {
                m_neg_sos.push_back(I[i]);
                m_neg_sos_sum.push_back(sum_abs(I[i]));
            }
        }
    }

    void reset() {
        m_heap.reset();
        m_free_list.reset();
        m_psos.reset();
        m_pas.reset();
        m_sum_abs.reset();
        m_pos_sos.reset();
        m_neg_sos.reset();
        m_pos_sos_sum.reset();
        m_neg_sos_sum.reset();
        m_weight.reset();
    }

    void insert(offset_t idx, unsigned offset) {
        SASSERT(!m_pos_sos.empty());
        unsigned v;
        if (m_free_list.empty()) {
            v = m_pas.size();
            m_pas.push_back(idx);
            m_psos.push_back(offset);
            m_weight.push_back(numeral(0));
            m_heap.set_bounds(v+1);
            m_sum_abs.push_back(sum_abs(idx));
        }
        else {
            v = m_free_list.back();
            m_free_list.pop_back();
            m_pas[v] = idx;
            m_psos[v] = offset;
            m_weight[v] = numeral(0);
            m_sum_abs[v] = sum_abs(idx);
        }
        next_resolvable(hb.vec(idx).weight().is_pos(), v);
    }

    bool empty() const {
        return m_heap.empty();
    }

    unsigned pop(offset_t& sos, offset_t& pas) {
        SASSERT (!empty());
        unsigned val = static_cast<unsigned>(m_heap.erase_min());
        pas = m_pas[val];
        numeral old_weight = hb.vec(pas).weight();
        bool is_positive = old_weight.is_pos();
        unsigned psos = m_psos[val];
        sos = is_positive?m_neg_sos[psos]:m_pos_sos[psos];
        m_psos[val]++;
        next_resolvable(is_positive, val);
        numeral new_weight = hb.vec(sos).weight() + old_weight;
        if (new_weight.is_pos() != old_weight.is_pos()) {
            psos = 0;
        }
        return psos;
    }

    bool operator()(int v1, int v2) const {
        return m_weight[v1] < m_weight[v2];
    }

    class iterator {
        passive2& p;
        unsigned m_idx;
        void fwd() {
            while (m_idx < p.m_pas.size() && 
                   is_invalid_offset(p.m_pas[m_idx])) {
                ++m_idx;
            }
        }
    public:
        iterator(passive2& p, unsigned i): p(p), m_idx(i) { fwd(); }
        offset_t pas() const { return p.m_pas[m_idx]; }
        offset_t sos() const { return (p.hb.vec(pas()).weight().is_pos()?p.m_neg_sos:p.m_pos_sos)[p.m_psos[m_idx]]; }
        iterator& operator++() { ++m_idx; fwd(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& it) const {return m_idx == it.m_idx; }
        bool operator!=(iterator const& it) const {return m_idx != it.m_idx; }
    };

    iterator begin() {
        return iterator(*this, 0);
    }

    iterator end() {
        return iterator(*this, m_pas.size());
    }    
private:
    void next_resolvable(bool is_positive, unsigned v) {
        offset_t pas = m_pas[v];
        svector<offset_t> const& soss = is_positive?m_neg_sos:m_pos_sos;
        while (m_psos[v] < soss.size()) {
            unsigned psos = m_psos[v];
            offset_t sos = soss[psos];
            if (hb.can_resolve(sos, pas, false)) {
                m_weight[v] = m_sum_abs[v] + (is_positive?m_neg_sos_sum[psos]:m_pos_sos_sum[psos]);
                m_heap.insert(v);
                return;
            }
            ++m_psos[v];
        }
        // add pas to free-list for hb if it is not in sos.
        m_free_list.push_back(v);
        m_psos[v] = UINT_MAX;
        m_pas[v] = mk_invalid_offset();
    }
};


hilbert_basis::hilbert_basis(reslimit& lim):
    m_limit(lim),
    m_use_support(true),
    m_use_ordered_support(true),
    m_use_ordered_subsumption(true)
{
    m_index = alloc(index, *this);
    m_passive = alloc(passive, *this);
    m_passive2 = alloc(passive2, *this);
}

hilbert_basis::~hilbert_basis() {
    dealloc(m_index);
    dealloc(m_passive);
    dealloc(m_passive2);
}

hilbert_basis::offset_t hilbert_basis::mk_invalid_offset() {
    return offset_t(UINT_MAX);
}

bool hilbert_basis::is_invalid_offset(offset_t offs) {
    return offs.m_offset == UINT_MAX;
}

void hilbert_basis::reset() {
    m_ineqs.reset();
    m_iseq.reset();
    m_store.reset();
    m_basis.reset();
    m_free_list.reset();
    m_sos.reset();
    m_zero.reset();
    m_active.reset();
    if (m_passive) {
        m_passive->reset();
    }
    if (m_passive2) {
        m_passive2->reset();
    }
    if (m_index) {
        m_index->reset(1);
    }
    m_ints.reset();
    m_current_ineq = 0;
    
}

void hilbert_basis::collect_statistics(statistics& st) const {
    st.update("hb.num_subsumptions", m_stats.m_num_subsumptions);
    st.update("hb.num_resolves", m_stats.m_num_resolves);
    st.update("hb.num_saturations", m_stats.m_num_saturations);
    st.update("hb.basis_size", get_basis_size());
    m_index->collect_statistics(st);
}

void hilbert_basis::reset_statistics() {
    m_stats.reset();
    m_index->reset_statistics();
}

void hilbert_basis::add_ge(rational_vector const& v, rational const& b) {
    SASSERT(m_ineqs.empty() || v.size() + 1 == m_ineqs.back().size());
    num_vector w;
    w.push_back(to_numeral(-b));
    for (unsigned i = 0; i < v.size(); ++i) {
        w.push_back(to_numeral(v[i]));
    }
    m_ineqs.push_back(w);
    m_iseq.push_back(false);
}

void hilbert_basis::add_le(rational_vector const& v, rational const& b) {
    rational_vector w(v);
    for (unsigned i = 0; i < w.size(); ++i) {
        w[i].neg();
    }
    add_ge(w, -b);
}

void hilbert_basis::add_eq(rational_vector const& v, rational const& b) {
    SASSERT(m_ineqs.empty() || v.size() + 1 == m_ineqs.back().size());
    num_vector w;
    w.push_back(to_numeral(-b));
    for (unsigned i = 0; i < v.size(); ++i) {
        w.push_back(to_numeral(v[i]));
    }
    m_ineqs.push_back(w);
    m_iseq.push_back(true);
}

void hilbert_basis::add_ge(rational_vector const& v) {
    add_ge(v, rational(0));
}

void hilbert_basis::add_le(rational_vector const& v) {
    add_le(v, rational(0));
}

void hilbert_basis::add_eq(rational_vector const& v) {
    add_eq(v, rational(0));
}

void hilbert_basis::set_is_int(unsigned var_index) {
    //
    // The 0'th index is reserved for the constant
    // coefficient. Shift indices by 1.
    //
    m_ints.push_back(var_index+1);
}

bool hilbert_basis::get_is_int(unsigned var_index) const {    
    return m_ints.contains(var_index+1);
}

unsigned hilbert_basis::get_num_vars() const {
    if (m_ineqs.empty()) {
        return 0;
    }
    else {
        SASSERT(m_ineqs.back().size() > 1);
        return m_ineqs.back().size();
    }
}

hilbert_basis::values hilbert_basis::vec(offset_t offs) const {
    return values(m_ineqs.size(), m_store.c_ptr() + offs.m_offset);
}

void hilbert_basis::init_basis() {
    m_basis.reset();
    m_store.reset();
    m_free_list.reset();
    unsigned nv = get_num_vars();
    for (unsigned i = 0; i < nv; ++i) {
        add_unit_vector(i, numeral(1));
    }
    for (unsigned i = 0; i < m_ints.size(); ++i) {
        add_unit_vector(m_ints[i], numeral(-1));
    }
}
 
void hilbert_basis::add_unit_vector(unsigned i, numeral const& e) {
    unsigned num_vars = get_num_vars();
    num_vector w(num_vars, numeral(0));
    w[i] = e;
    offset_t idx = alloc_vector();
    values v = vec(idx);
    for (unsigned j = 0; j < num_vars; ++j) {
        v[j] = w[j];
    }
    m_basis.push_back(idx);            
}

lbool hilbert_basis::saturate() {
    init_basis();
    m_current_ineq = 0;
    while (checkpoint() && m_current_ineq < m_ineqs.size()) {
        select_inequality();
        stopwatch sw;
        sw.start();
        lbool r = saturate(m_ineqs[m_current_ineq], m_iseq[m_current_ineq]);
        IF_VERBOSE(3,  
                   { statistics st; 
                       collect_statistics(st); 
                       st.display(verbose_stream()); 
                       sw.stop(); 
                       verbose_stream() << "time: " << sw.get_seconds() << "\n";
                   });

        ++m_stats.m_num_saturations;
        if (r != l_true) {
            return r;
        }        
        ++m_current_ineq;
    }
    if (!checkpoint()) {
        return l_undef;
    }
    return l_true;
}

lbool hilbert_basis::saturate_orig(num_vector const& ineq, bool is_eq) {
    m_active.reset();
    m_passive->reset();
    m_zero.reset();
    m_index->reset(m_current_ineq+1);
    int_table support;
    TRACE("hilbert_basis", display_ineq(tout, ineq, is_eq););
    iterator it = begin();
    for (; it != end(); ++it) {
        offset_t idx = *it;
        values v = vec(idx);
        v.weight() = get_weight(v, ineq);
        for (unsigned k = 0; k < m_current_ineq; ++k) {
            v.weight(k) = get_weight(v, m_ineqs[k]);        
        }
        add_goal(idx);
        if (m_use_support) {
            support.insert(idx.m_offset);
        }
    }
    TRACE("hilbert_basis", display(tout););
    // resolve passive into active
    offset_t j = alloc_vector();
    while (!m_passive->empty()) {
        if (!checkpoint()) {
            return l_undef;
        }
        offset_t idx = m_passive->pop();
        TRACE("hilbert_basis", display(tout););
        if (is_subsumed(idx)) {
            recycle(idx);
            continue;
        }
        for (unsigned i = 0; checkpoint() && i < m_active.size(); ++i) {
            if ((!m_use_support || support.contains(m_active[i].m_offset)) && can_resolve(idx, m_active[i], true)) {
                resolve(idx, m_active[i], j);
                if (add_goal(j)) {
                    j = alloc_vector();
                }
            }
        }
        m_active.push_back(idx);
    }
    m_free_list.push_back(j);
    // Move positive from active and zeros to new basis.
    m_basis.reset();
    m_basis.append(m_zero);
    for (unsigned i = 0; !is_eq && i < m_active.size(); ++i) {
        offset_t idx = m_active[i];
        if (vec(idx).weight().is_pos()) {
            m_basis.push_back(idx);
        }
        else {
            m_free_list.push_back(idx);
        }
    }
    m_active.reset();
    m_passive->reset();
    m_zero.reset();
    TRACE("hilbert_basis", display(tout););
    return m_basis.empty()?l_false:l_true;
}

bool hilbert_basis::vector_lt(offset_t idx1, offset_t idx2) const {
    values v = vec(idx1);
    values w = vec(idx2);
    numeral a(0), b(0);
    for (unsigned i = 0; i < get_num_vars(); ++i) {
        a += abs(v[i]);
        b += abs(w[i]);
    }
    return a < b;
}

lbool hilbert_basis::saturate(num_vector const& ineq, bool is_eq) {
    m_zero.reset();
    m_index->reset(m_current_ineq+1);
    m_passive2->reset();
    m_sos.reset();
    TRACE("hilbert_basis", display_ineq(tout, ineq, is_eq););
    unsigned init_basis_size = 0;
    for (unsigned i = 0; i < m_basis.size(); ++i) {
        offset_t idx = m_basis[i];
        values v = vec(idx);
        v.weight() = get_weight(v, ineq);
        for (unsigned k = 0; k < m_current_ineq; ++k) {
            v.weight(k) = get_weight(v, m_ineqs[k]);        
        }
        m_index->insert(idx, v);
        if (v.weight().is_zero()) {
            m_zero.push_back(idx);
        }
        else {
            if (v.weight().is_pos()) {
                m_basis[init_basis_size++] = idx;
            }
            m_sos.push_back(idx);
        }
    }
    m_basis.resize(init_basis_size);
    m_passive2->init(m_sos);
    // ASSERT basis is sorted by weight.

    // initialize passive
    for (unsigned i = 0; (init_basis_size > 0) && i < m_sos.size(); ++i) {
        if (vec(m_sos[i]).weight().is_neg()) {
            m_passive2->insert(m_sos[i], 0);         
        }   
    }

    TRACE("hilbert_basis", display(tout););
    // resolve passive into active
    offset_t idx = alloc_vector();
    while (checkpoint() && !m_passive2->empty()) {
        offset_t sos, pas;
        TRACE("hilbert_basis", display(tout); );
        unsigned offset = m_passive2->pop(sos, pas);
        SASSERT(can_resolve(sos, pas, true));
        resolve(sos, pas, idx);
        if (is_subsumed(idx)) {
            continue;
        }
        values v = vec(idx);
        m_index->insert(idx, v);
        if (v.weight().is_zero()) {
            m_zero.push_back(idx);
        }
        else {
            if (!m_use_ordered_support) {
                offset = 0;
            }
            m_passive2->insert(idx, offset);
            if (v.weight().is_pos()) {
                m_basis.push_back(idx);
            }
        }
        idx = alloc_vector();
    }
    if (!checkpoint()) {
        return l_undef;
    }

    m_free_list.push_back(idx);
    // remove positive values from basis if we are looking for an equality.
    while (is_eq && !m_basis.empty()) {
        m_free_list.push_back(m_basis.back());
        m_basis.pop_back();
    }
    m_basis.append(m_zero);
    std::sort(m_basis.begin(), m_basis.end(), vector_lt_t(*this));
    m_zero.reset();
    TRACE("hilbert_basis", display(tout););
    return m_basis.empty()?l_false:l_true;
}

void hilbert_basis::get_basis_solution(unsigned i, rational_vector& v, bool& is_initial) {
    offset_t offs = m_basis[i];
    v.reset();
    for (unsigned i = 1; i < get_num_vars(); ++i) {
        v.push_back(to_rational(vec(offs)[i]));
    }
    is_initial = !vec(offs)[0].is_zero();
}

void hilbert_basis::get_ge(unsigned i, rational_vector& v, rational& b, bool& is_eq) {
    v.reset();
    for (unsigned j = 1; j < m_ineqs[i].size(); ++j) {
        v.push_back(to_rational(m_ineqs[i][j]));
    }
    b = to_rational(-m_ineqs[i][0]);
    is_eq = m_iseq[i];
}


void hilbert_basis::select_inequality() {
    SASSERT(m_current_ineq < m_ineqs.size());
    unsigned best = m_current_ineq;
    unsigned non_zeros = get_num_nonzeros(m_ineqs[best]);
    unsigned prod      = get_ineq_product(m_ineqs[best]);
    for (unsigned j = best+1; prod != 0 && j < m_ineqs.size(); ++j) {
        unsigned non_zeros2 = get_num_nonzeros(m_ineqs[j]);
        unsigned prod2 = get_ineq_product(m_ineqs[j]);
        if (prod2 == 0) {
            prod = prod2;
            non_zeros = non_zeros2;
            best = j;
            break;
        }
        if (non_zeros2 < non_zeros || (non_zeros2 == non_zeros && prod2 < prod)) {
            prod = prod2;
            non_zeros = non_zeros2;
            best = j;
        }
    }
    if (best != m_current_ineq) {
        std::swap(m_ineqs[m_current_ineq], m_ineqs[best]);
        std::swap(m_iseq[m_current_ineq], m_iseq[best]);
    }
}

unsigned hilbert_basis::get_num_nonzeros(num_vector const& ineq) {
    unsigned count = 0;
    for (unsigned i = 0; i < ineq.size(); ++i) {
        if (!ineq[i].is_zero()) {
            ++count;
        }
    }
    return count;
}

unsigned hilbert_basis::get_ineq_product(num_vector const& ineq) {
    unsigned num_pos = 0, num_neg = 0;
    iterator it = begin();
    for (; it != end(); ++it) {
        values v = vec(*it);
        numeral w = get_weight(v, ineq);
        if (w.is_pos()) {
            ++num_pos;
        }
        else if (w.is_neg()) {
            ++num_neg;
        }
    }
    return num_pos * num_neg;
}

hilbert_basis::numeral hilbert_basis::get_ineq_diff(num_vector const& ineq) {
    numeral max_pos(0), min_neg(0);
    iterator it = begin();
    for (; it != end(); ++it) {
        values v = vec(*it);
        numeral w = get_weight(v, ineq);
        if (w > max_pos) {
            max_pos = w;
        }
        else if (w < min_neg) {
            min_neg = w;
        }
    }
    return max_pos - min_neg;
}

void hilbert_basis::recycle(offset_t idx) {
    m_index->remove(idx, vec(idx));
    m_free_list.push_back(idx);
}

void hilbert_basis::resolve(offset_t i, offset_t j, offset_t r) {
    ++m_stats.m_num_resolves;
    values v = vec(i);
    values w = vec(j);
    values u = vec(r);
    unsigned nv = get_num_vars();
    for (unsigned k = 0; k < nv; ++k) {
        u[k] = v[k] + w[k];
    }
    u.weight() = v.weight() + w.weight();
    for (unsigned k = 0; k < m_current_ineq; ++k) {
        u.weight(k) = v.weight(k) + w.weight(k);
    }
    TRACE("hilbert_basis_verbose",
          display(tout, i); 
          display(tout, j); 
          display(tout, r); 
          );
}


hilbert_basis::offset_t hilbert_basis::alloc_vector() {
    if (m_free_list.empty()) {
        unsigned sz  =  m_ineqs.size() + get_num_vars();
        unsigned idx =  m_store.size();   
        m_store.resize(idx + sz);
        // std::cout << "alloc vector: " << idx << " " << sz << " " << m_store.c_ptr() + idx << " " << m_ineqs.size() << "\n";
        return offset_t(idx);
    }
    else {
        offset_t result = m_free_list.back();
        m_free_list.pop_back();
        return result;
    }
}

bool hilbert_basis::checkpoint() {
    return m_limit.inc();
}

bool hilbert_basis::add_goal(offset_t idx) {
    TRACE("hilbert_basis", display(tout, idx););
    values v = vec(idx);
    if (is_subsumed(idx)) {
        return false;
    }
    m_index->insert(idx, v);
    if (v.weight().is_zero()) {
        m_zero.push_back(idx);
    }
    else {
        m_passive->insert(idx);
    }
    return true;
}

bool hilbert_basis::is_subsumed(offset_t idx)  {

    if (m_index->find(idx, vec(idx))) {        
        ++m_stats.m_num_subsumptions;
        return true;
    }
    return false;
}

bool hilbert_basis::can_resolve(offset_t i, offset_t j, bool check_sign) const {
    if (check_sign && get_sign(i) == get_sign(j)) {
        return false;
    }
    SASSERT(get_sign(i) != get_sign(j));
    values const& v1 = vec(i);
    values const& v2 = vec(j);
    if (v1[0].is_one() && v2[0].is_one()) {
        return false;
    }
    for (unsigned i = 0; i < m_ints.size(); ++i) {
        unsigned j = m_ints[i];
        if (v1[j].is_pos() && v2[j].is_neg()) {
            return false;
        }
        if (v1[j].is_neg() && v2[j].is_pos()) {
            return false;
        }
    }
    return true;
}

hilbert_basis::sign_t hilbert_basis::get_sign(offset_t idx) const {
    numeral const& val = vec(idx).weight();
    if (val.is_pos()) {
        return pos;
    }
    if (val.is_neg()) {
        return neg;
    }
    return zero;
}

hilbert_basis::numeral hilbert_basis::get_weight(values const & val, num_vector const& ineq) const {
    numeral result(0);
    unsigned num_vars = get_num_vars();
    for (unsigned i = 0; i < num_vars; ++i) {
        result += val[i]*ineq[i];
    }
    return result;
}

void hilbert_basis::display(std::ostream& out) const {
    out << "inequalities:\n";
    for (unsigned i = 0; i < m_ineqs.size(); ++i) {
        display_ineq(out, m_ineqs[i], m_iseq[i]);
    }
    if (!m_basis.empty()) {
        out << "basis:\n";
        for (iterator it = begin(); it != end(); ++it) {
            display(out, *it);
        }
    }
    if (!m_active.empty()) {
        out << "active:\n";
        for (unsigned i = 0; i < m_active.size(); ++i) {
            display(out, m_active[i]);
        }
    }
    if (!m_passive->empty()) {
        passive::iterator it = m_passive->begin();
        passive::iterator end = m_passive->end();
        out << "passive:\n";
        for (; it != end; ++it) {
            display(out, *it);
        }
    }
    if (!m_passive2->empty()) {
        passive2::iterator it = m_passive2->begin();
        passive2::iterator end = m_passive2->end();
        out << "passive:\n";
        for (; it != end; ++it) {
            display(out << "sos:", it.sos());
            display(out << "pas:", it.pas());
        }
    }
    if (!m_zero.empty()) {
        out << "zero:\n";
        for (unsigned i = 0; i < m_zero.size(); ++i) {
            display(out, m_zero[i]);
        }
    }
    if (m_index) {
        m_index->display(out);
    }
}

void hilbert_basis::display(std::ostream& out, offset_t o) const {
    display(out, vec(o));
    out << " -> " << vec(o).weight() << "\n";    
}

void hilbert_basis::display(std::ostream& out, values const& v) const {
    unsigned nv = get_num_vars();
    for (unsigned j = 0; j < nv; ++j) {            
        out << v[j] << " ";
    }
}

void hilbert_basis::display_ineq(std::ostream& out, num_vector const& v, bool is_eq) const {
    unsigned nv = v.size();
    for (unsigned j = 1; j < nv; ++j) {
        if (!v[j].is_zero()) {
            if (j > 0) {
                if (v[j].is_pos()) {
                    out << " + ";
                }
                else {
                    out << " - ";
                }
            }
            else if (j == 0 && v[0].is_neg()) {
                out << "-";
            }
            if (!v[j].is_one() && !v[j].is_minus_one()) {
                out << abs(v[j]) << "*";
            }
            out << "x" << j;            
        }
    }
    if (is_eq) {
        out << " = " << -v[0] << "\n";
    }
    else {
        out << " >= " << -v[0] << "\n";
    }
}


/**
   Vector v is subsumed by vector w if
       
       v[i] >= w[i] for each index i.
       
       a*v >= a*w  for the evaluation of vectors with respect to a.
       
       . a*v < 0 => a*v = a*w
       . a*v > 0 => a*w > 0
       . a*v = 0 => a*w = 0

   Justification:
       
       let u := v - w, then
       
       u[i] >= 0  for each index i
       
       a*u = a*(v-w) >= 0
       
       So v = u + w, where a*u >= 0, a*w >= 0.
       
       If a*v >= a*w >= 0 then v and w are linear 
       solutions of e_i, and also v-w is a solution.

       If a*v = a*w < 0, then a*(v-w) = 0, so v can be obtained from w + (v - w).
       
*/

bool hilbert_basis::is_subsumed(offset_t i, offset_t j) const {
    values v = vec(i);
    values w = vec(j);
    numeral const& n = v.weight();
    numeral const& m = w.weight();
    bool r = 
        i.m_offset != j.m_offset &&         
        n >= m && (!m.is_neg() || n == m) &&
        is_geq(v, w);
    for (unsigned k = 0; r && k < m_current_ineq; ++k) {
        r = v.weight(k) >= w.weight(k);
    }
    CTRACE("hilbert_basis", r, 
           display(tout, i);
           tout << " <= \n";
           display(tout, j);
           tout << "\n";);
    return r;
}

bool hilbert_basis::is_geq(values const& v, values const& w) const {
    unsigned nv = get_num_vars();
    for (unsigned i = 0; i < nv; ++i) {
        if (!is_abs_geq(v[i], w[i])) {
            return false;
        }
    }
    return true;
}

bool hilbert_basis::is_abs_geq(numeral const& v, numeral const& w) const {
    if (w.is_neg()) {
        return v <= w;
    }
    else {
        return v >= w;
    }
}
