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

template<typename Value>
class rational_map : public map<rational, Value, rational::hash_proc, rational::eq_proc> {};


class hilbert_basis::value_index1 {
    struct stats {
        unsigned m_num_comparisons;
        unsigned m_num_hit;
        unsigned m_num_miss;

        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };    

    typedef int_hashtable<int_hash, default_eq<int> > int_table;
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

    bool find(offset_t idx, values const& vs, offset_t& found_idx) {
        // display_profile(idx, std::cout);
        int_table::iterator it = m_table.begin(), end = m_table.end();
        for (; it != end; ++it) {
            offset_t offs(*it);
            ++m_stats.m_num_comparisons;
            if (*it != static_cast<int>(idx.m_offset) && hb.is_subsumed(idx, offs)) {
                found_idx = offs;
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
        static bool le(numeral const& n1, numeral const& n2) {
            return hilbert_basis::is_abs_geq(n2, n1);
        }
    };
    struct checker : public heap_trie<numeral, key_le, unsigned>::check_value {
        hilbert_basis* hb;
        offset_t  m_value;
        offset_t* m_found;
        checker(): hb(0), m_found(0) {}
        virtual bool operator()(unsigned const& v) {
            if (m_value.m_offset != v && hb->is_subsumed(m_value, offset_t(v))) {
                *m_found = offset_t(v);
                return true;
            }
            else {
                return false;
            }
        }
    };
    hilbert_basis&               hb;
    heap_trie<numeral, key_le, unsigned> m_trie;
    vector<unsigned>             m_found;
    bool                         m_init;
    checker                      m_checker;
    vector<numeral>              m_keys;

#if 1    
    numeral const* get_keys(values const& vs) {
        return vs()-1;
    }
#else
    numeral const* get_keys(values const& vs) {
        unsigned sz = m_keys.size();
        for (unsigned i = 0; i < sz; ++i) {
            m_keys[sz-i-1] = vs()[i-1];
        }
        return m_keys.c_ptr();
    }
#endif

public:
    value_index2(hilbert_basis& hb): hb(hb), m_init(false) {
        m_checker.hb = &hb;
    }

    void insert(offset_t idx, values const& vs) {
        init();
        m_trie.insert(get_keys(vs), idx.m_offset);
    }

    void remove(offset_t idx, values const& vs) {
        m_trie.remove(get_keys(vs));
    }

    void reset() {
        m_trie.reset(hb.get_num_vars()+1);
        m_keys.resize(hb.get_num_vars()+1);
    }

    bool find(offset_t idx, values const& vs, offset_t& found_idx) {
        init();
        m_checker.m_value = idx;
        m_checker.m_found = &found_idx;
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

private:
    void init() {
        if (!m_init) {
            reset();
            m_init = true;
        }
    }
};



class hilbert_basis::index {
    // for each non-positive weight a separate index.
    // for positive weights a shared value index.

    // typedef value_index1 value_index;
    typedef value_index2 value_index;

    struct stats {
        unsigned m_num_find;
        unsigned m_num_insert;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };        

    typedef rational_map<value_index*> value_map;
    hilbert_basis&   hb;
    value_map        m_neg;
    value_index      m_pos;
    value_index      m_zero;
    stats            m_stats;

public:
    index(hilbert_basis& hb): hb(hb), m_pos(hb), m_zero(hb) {}
    
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

    bool find(offset_t idx, values const& vs, offset_t& found_idx) {
        ++m_stats.m_num_find;
        if (vs.weight().is_pos()) {
            return m_pos.find(idx,  vs, found_idx);
        }
        else if (vs.weight().is_zero()) {
            return m_zero.find(idx, vs, found_idx);
        }
        else {
            value_index* map;
            return
                m_neg.find(vs.weight(), map) && 
                map->find(idx, vs, found_idx);
        }        
    }    

    void reset() {
        value_map::iterator it = m_neg.begin(), end = m_neg.end();
        for (; it != end; ++it) {
            it->m_value->reset();
        }
        m_pos.reset();
        m_zero.reset();
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

hilbert_basis::hilbert_basis(): 
    m_cancel(false) 
{
    m_index = alloc(index, *this);
    m_passive = alloc(passive, *this);
}

hilbert_basis::~hilbert_basis() {
    dealloc(m_index);
    dealloc(m_passive);
}

hilbert_basis::offset_t hilbert_basis::mk_invalid_offset() {
    return offset_t(UINT_MAX);
}

bool hilbert_basis::is_invalid_offset(offset_t offs) {
    return offs.m_offset == UINT_MAX;
}

void hilbert_basis::reset() {
    m_ineqs.reset();
    m_basis.reset();
    m_store.reset();
    m_free_list.reset();
    m_active.reset();
    m_passive->reset();
    m_zero.reset();
    m_index->reset();
    m_cancel = false;
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

void hilbert_basis::add_ge(num_vector const& v, numeral const& b) {
    SASSERT(m_ineqs.empty() || v.size() + 1 == m_ineqs.back().size());
    num_vector w;
    w.push_back(-b);
    w.append(v);
    m_ineqs.push_back(w);
    m_iseq.push_back(false);
}

void hilbert_basis::add_le(num_vector const& v, numeral const& b) {
    num_vector w(v);
    for (unsigned i = 0; i < w.size(); ++i) {
        w[i].neg();
    }
    add_ge(w, -b);
}

void hilbert_basis::add_eq(num_vector const& v, numeral const& b) {
    SASSERT(m_ineqs.empty() || v.size() + 1 == m_ineqs.back().size());
    num_vector w;
    w.push_back(-b);
    w.append(v);
    m_ineqs.push_back(w);
    m_iseq.push_back(true);
}

void hilbert_basis::add_ge(num_vector const& v) {
    add_ge(v, numeral(0));
}

void hilbert_basis::add_le(num_vector const& v) {
    add_le(v, numeral(0));
}

void hilbert_basis::add_eq(num_vector const& v) {
    add_eq(v, numeral(0));
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
    return values(m_store.c_ptr() + (get_num_vars() + 1)*offs.m_offset);
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
    while (!m_cancel && m_current_ineq < m_ineqs.size()) {
        select_inequality();
        lbool r = saturate(m_ineqs[m_current_ineq], m_iseq[m_current_ineq]);
        ++m_stats.m_num_saturations;
        if (r != l_true) {
            return r;
        }        
        ++m_current_ineq;
    }
    if (m_cancel) {
        return l_undef;
    }
    return l_true;
}

lbool hilbert_basis::saturate(num_vector const& ineq, bool is_eq) {
    m_active.reset();
    m_passive->reset();
    m_zero.reset();
    m_index->reset();
    TRACE("hilbert_basis", display_ineq(tout, ineq, is_eq););
    bool has_non_negative = false;
    iterator it = begin();
    for (; it != end(); ++it) {
        values v = vec(*it);
        v.weight() = get_weight(v, ineq);
        add_goal(*it);
        if (v.weight().is_nonneg()) {
            has_non_negative = true;
        }
    }
    TRACE("hilbert_basis", display(tout););
    if (!has_non_negative) {
        return l_false;
    }
    // resolve passive into active
    while (!m_passive->empty()) {
        if (m_cancel) {
            return l_undef;
        }
        offset_t idx = m_passive->pop();
        TRACE("hilbert_basis", display(tout););
        if (is_subsumed(idx)) {
            recycle(idx);
            continue;
        }
        for (unsigned i = 0; !m_cancel && i < m_active.size(); ++i) {
            if (can_resolve(idx, m_active[i])) {
                offset_t j = alloc_vector();
                resolve(idx, m_active[i], j);
                add_goal(j);
            }
        }
        m_active.push_back(idx);
    }
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
    return l_true;
}

void hilbert_basis::get_basis_solution(unsigned i, num_vector& v, bool& is_initial) {
    offset_t offs = m_basis[i];
    v.reset();
    for (unsigned i = 1; i < get_num_vars(); ++i) {
        v.push_back(vec(offs)[i]);
    }
    is_initial = !vec(offs)[0].is_zero();
}

void hilbert_basis::get_ge(unsigned i, num_vector& v, numeral& b, bool& is_eq) {
    v.reset();
    v.append(m_ineqs[i].size() - 1, m_ineqs[i].c_ptr() + 1);
    b = -m_ineqs[i][0];
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
    TRACE("hilbert_basis_verbose",
          display(tout, i); 
          display(tout, j); 
          display(tout, r); 
          );
}


hilbert_basis::offset_t hilbert_basis::alloc_vector() {
    if (m_free_list.empty()) {
        unsigned num_vars = get_num_vars();
        unsigned idx =  m_store.size();
        m_store.resize(idx + 1 + num_vars);
        return offset_t(idx/(1+num_vars));
    }
    else {
        offset_t result = m_free_list.back();
        m_free_list.pop_back();
        return result;
    }
}

void hilbert_basis::add_goal(offset_t idx) {
    TRACE("hilbert_basis", display(tout, idx););
    values v = vec(idx);
    if (is_subsumed(idx)) {
        return;
    }
    m_index->insert(idx, v);
    if (v.weight().is_zero()) {
        m_zero.push_back(idx);
    }
    else {
        m_passive->insert(idx);
    }
}

bool hilbert_basis::is_subsumed(offset_t idx)  {

    offset_t found_idx;
    if (m_index->find(idx, vec(idx), found_idx)) {        
        ++m_stats.m_num_subsumptions;
        return true;
    }
    return false;
}

bool hilbert_basis::can_resolve(offset_t i, offset_t j) const {
    if (get_sign(i) == get_sign(j)) {
        return false;
    }
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
    numeral val = vec(idx).weight();
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
        r = get_weight(vec(i), m_ineqs[k]) >= get_weight(vec(j), m_ineqs[k]);
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

bool hilbert_basis::is_abs_geq(numeral const& v, numeral const& w) {
    if (w.is_neg()) {
        return v <= w;
    }
    else {
        return v >= w;
    }
}
