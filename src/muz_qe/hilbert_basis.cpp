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

typedef u_map<unsigned> offset_refs_t;

template<typename Value>
class rational_map : public map<rational, Value, rational::hash_proc, rational::eq_proc> {};

class rational_abs_lt {
    vector<rational> & m_values;
public:
    rational_abs_lt(vector<rational> & values):
        m_values(values) {
    }
    bool operator()(int v1, int v2) const {
        return m_values[v1] < m_values[v2];
    }
};


class hilbert_basis::rational_heap {
    vector<numeral>          m_u2r;     // [index |-> weight]
    rational_map<unsigned>   m_r2u;     // [weight |-> index]
    rational_abs_lt          m_lt;      // less_than on indices
    heap<rational_abs_lt>    m_heap;    // binary heap over weights
public:

    rational_heap(): m_lt(m_u2r), m_heap(10, m_lt) {}

    vector<numeral>& u2r() { return m_u2r; }

    void insert(unsigned v) {
        m_heap.insert(v);
    }

    void reset() {
        m_u2r.reset();
        m_r2u.reset();
        m_heap.reset();
    }

    bool is_declared(numeral const& r, unsigned& val) const {
        return m_r2u.find(r, val);
    }

    unsigned declare(numeral const& r) {
        SASSERT(!m_r2u.contains(r));
        unsigned val = m_u2r.size();
        m_u2r.push_back(r);
        m_r2u.insert(r, val);
        m_heap.set_bounds(val+1);
        return val;
    }

    void find_le(unsigned val, int_vector & result) {
        m_heap.find_le(val, result);
    }

};

class hilbert_basis::weight_map {
    struct stats {
        unsigned m_num_comparisons;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };    

    rational_heap            m_heap;         
    vector<unsigned_vector>  m_offsets;      // [index |-> offset-list]
    int_vector               m_le;           // recycled set of indices with lesser weights
    stats                    m_stats;
    svector<offset_t>&       m_found;
    offset_refs_t&           m_refs;
    unsigned                 m_cost;

    unsigned get_value(numeral const& w) {
        numeral r = abs(w);
        unsigned val;
        if (!m_heap.is_declared(r, val)) {
            val = m_heap.declare(r);
            SASSERT(val == m_offsets.size());
            if (r.is_nonneg()) {
                m_heap.insert(val);
            }
            m_offsets.push_back(unsigned_vector());
        }
        return val;
    }
public:
    weight_map(svector<offset_t>& found, offset_refs_t& refs): m_found(found), m_refs(refs) {}
    
    void insert(offset_t idx, numeral const& w) {
        unsigned val = get_value(w);
        m_offsets[val].push_back(idx.m_offset);
    }

    void remove(offset_t idx, numeral const& w) {
        unsigned val = get_value(w);
        m_offsets[val].erase(idx.m_offset);
    }

    unsigned get_size() const {
        unsigned sz = 0;
        for (unsigned i = 0; i < m_offsets.size(); ++i) {
            sz += m_offsets[i].size();
        }
        return sz;
    }

    void reset() {
        m_offsets.reset();
        m_heap.reset();
        m_le.reset();
    }
    
    unsigned get_cost() const { return m_cost; }

    /**
       retrieve 
     */
    bool init_find(numeral const& w, offset_t idx) {
        m_le.reset();
        m_found.reset();
        m_cost = 0;
        unsigned val = get_value(w);
        // for positive values, the weights should be less or equal.
        // for non-positive values, the weights have to be the same.
        if (w.is_pos()) {
            m_heap.find_le(val, m_le);
        }
        else {
            m_le.push_back(val);
        }
        for (unsigned i = 0; i < m_le.size(); ++i) {
            if (m_heap.u2r()[m_le[i]].is_zero() && !w.is_zero()) {
                continue;
            } 
            unsigned_vector const& offsets = m_offsets[m_le[i]];
            for (unsigned j = 0; j < offsets.size(); ++j) {
                unsigned offs = offsets[j];
                ++m_stats.m_num_comparisons;
                ++m_cost;
                if (offs != idx.m_offset) {
                    m_refs.insert(offs, 0);
                    m_found.push_back(offset_t(offs));
                }
            }
        }
        return !m_found.empty();
    }

    unsigned get_find_cost(numeral const& w) {
        m_le.reset();
        unsigned cost = 0;
        unsigned val = get_value(w);
        m_heap.find_le(val, m_le);
        for (unsigned i = 0; i < m_le.size(); ++i) {
            cost += m_offsets[m_le[i]].size();
        }
        return cost;        
    }
    
    bool update_find(unsigned round, numeral const& w, offset_t idx) {
        m_found.reset();
        m_le.reset();
        m_cost = 0;
        unsigned vl = get_value(w);
        m_heap.find_le(vl, m_le);
        for (unsigned i = 0; i < m_le.size(); ++i) {
            unsigned_vector const& offsets = m_offsets[m_le[i]];
            for (unsigned j = 0; j < offsets.size(); ++j) {
                unsigned offs = offsets[j];
                ++m_stats.m_num_comparisons;
                ++m_cost;
                if (offs != idx.m_offset && m_refs.find(offs, vl) && vl == round) {
                    m_refs.insert(offs, round + 1);
                    m_found.push_back(offset_t(offs));
                }
            }
        }
        return !m_found.empty();
    }    

    void collect_statistics(statistics& st) const {
        st.update("hb.index.num_comparisons", m_stats.m_num_comparisons);
    }

    void reset_statistics() {
        m_stats.reset();
    }
};


class hilbert_basis::index {
    // for each index, a heap of weights.
    // for each weight a list of offsets

    struct stats {
        unsigned m_num_comparisons;
        unsigned m_num_find;
        unsigned m_num_insert;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };    
    
    hilbert_basis&     hb;
    offset_refs_t      m_refs;
    svector<offset_t>  m_found;
    ptr_vector<weight_map> m_values;
    weight_map         m_weight;
    stats              m_stats;

public:

    index(hilbert_basis& hb): hb(hb), m_weight(m_found, m_refs) {}

    ~index() {
        for (unsigned i = 0; i < m_values.size(); ++i) {
            dealloc(m_values[i]);
        }
    }

    void init(unsigned num_vars) {
        if (m_values.empty()) {
            for (unsigned i = 0; i < num_vars; ++i) {
                m_values.push_back(alloc(weight_map, m_found, m_refs));
            }
        }
        SASSERT(m_values.size() == num_vars);
    }
    
    void insert(offset_t idx, values const& vs) {
        ++m_stats.m_num_insert;
#if 0
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_values[i]->insert(idx, vs[i]);
        }
#endif
        m_weight.insert(idx, vs.value());
    }

    void remove(offset_t idx, values const& vs) {
#if 0
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_values[i]->remove(idx, vs[i]);
        }
#endif
        m_weight.remove(idx, vs.value());
    }

    bool find(values const& vs, offset_t idx, offset_t& found_idx) {
        ++m_stats.m_num_find;
        m_refs.reset();
        bool found = m_weight.init_find(vs.value(), idx);
        TRACE("hilbert_basis", tout << "init: " << m_found.size() << " cost: " << m_weight.get_cost() << "\n";);
#if 0
        std::cout << vs.value() << " " << m_found.size() << " ";
        for (unsigned i = 0; i < m_values.size(); ++i) {
            std::cout << vs[i] << ": " << m_values[i]->get_find_cost(vs[i]) << " ";
        }
        std::cout << "\n";
#endif
#if 0
        for (unsigned i = 0; found && i < m_values.size(); ++i) {
            found = m_values[i]->update_find(i, vs[i], idx);
            std::cout << vs[i] << ": " << m_found.size() << " ";
            TRACE("hilbert_basis", tout << "update " << i << ": " << m_found.size() << " cost: " << m_values[i]->get_cost() << "\n";);
        }
#else
        for (unsigned i = 0; i < m_found.size(); ++i) {
            if (is_subsumed(idx, m_found[i])) {
                found_idx = m_found[i];
                return true;
            }
        }
        return false;
#endif

        if (found) {
            found_idx = m_found[0];
        }
        return found;
    }

    void reset() {
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_values[i]->reset();
        }
        m_weight.reset();
        m_refs.reset();
    }

    void collect_statistics(statistics& st) const {
        m_weight.collect_statistics(st);
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_values[i]->collect_statistics(st);
        }        
        st.update("hb.index.num_find", m_stats.m_num_find);
        st.update("hb.index.num_insert", m_stats.m_num_insert);
        st.update("hb.index.size", m_weight.get_size());
    }

    void reset_statistics() {
        m_stats.reset();
        m_weight.reset_statistics();
        for (unsigned i = 0; i < m_values.size(); ++i) {
            m_values[i]->reset_statistics();
        }        
    }


    /**
       Vector v is subsumed by vector w if
       
       v[i] >= w[i] for each index i.
       
       a*v >= a*w  for the evaluation of vectors with respect to a.
       
       a*v < 0 => a*v = a*w
       

       Justification:
       
       let u := v - w, then
       
       u[i] >= 0  for each index i
       
       a*u = a*(v-w) >= 0
       
       So v = u + w, where a*u >= 0, a*w >= 0.
       
       If a*v >= a*w >= 0 then v and w are linear 
       solutions of e_i, and also v-w is a solution.

       If a*v = a*w < 0, then a*(v-w) = 0, so v can be obtained from w + (v - w).
       
    */

    bool is_subsumed(offset_t i, offset_t j) const {
        values v = hb.vec(i);
        values w = hb.vec(j);
        numeral const& n = v.value();
        numeral const& m = w.value();
        bool r = 
            i.m_offset != j.m_offset &&         
            n >= m && (!m.is_neg() || n == m) &&
            is_geq(v, w);
        CTRACE("hilbert_basis", r, 
               hb.display(tout, i);
               tout << " <= \n";
               hb.display(tout, j);
               tout << "\n";);
        return r;
    }

    bool is_geq(values v, values w) const {
        unsigned nv = hb.get_num_vars();
        for (unsigned i = 0; i < nv; ++i) {
            if (v[i] < w[i]) {
                return false;
            }
        }
        return true;
    }


};

/**
   \brief priority queue for passive list.
*/

class hilbert_basis::passive {
    hilbert_basis&         hb;
    svector<offset_t>      m_passive;
    vector<numeral>        m_weights;
    unsigned_vector        m_free_list;
    rational_abs_lt        m_lt;      // less_than on indices
    heap<rational_abs_lt>  m_heap;    // binary heap over weights

    numeral get_weight(offset_t idx) {
        numeral w(0);
        unsigned nv = hb.get_num_vars();
        for (unsigned i = 0; i < nv; ++i) {
            w += hb.vec(idx)[i];
        }
        return w;
    }
    
public:
    
    passive(hilbert_basis& hb): 
        hb(hb) ,
        m_lt(m_weights),
        m_heap(10, m_lt)
    {}

    void reset() {
        m_heap.reset();
        m_free_list.reset();
        m_weights.reset();
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
            m_weights.push_back(get_weight(idx));
            m_heap.set_bounds(v+1);
        }
        else {
            v = m_free_list.back();
            m_free_list.pop_back();
            m_passive[v] = idx;
            m_weights[v] = get_weight(idx);
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
    m_index->collect_statistics(st);
}

void hilbert_basis::reset_statistics() {
    m_stats.reset();
    m_index->reset_statistics();
}

void hilbert_basis::add_ge(num_vector const& v, numeral const& b) {
    SASSERT(m_ineqs.empty() || v.size() + 1 == get_num_vars());
    num_vector w;
    w.push_back(-b);
    w.append(v);
    if (m_ineqs.empty()) {
        m_index->init(w.size());
    }
    m_ineqs.push_back(w);
}

void hilbert_basis::add_le(num_vector const& v, numeral const& b) {
    num_vector w(v);
    for (unsigned i = 0; i < w.size(); ++i) {
        w[i].neg();
    }
    add_ge(w, -b);
}

void hilbert_basis::add_eq(num_vector const& v, numeral const& b) {
    add_le(v, b);
    add_ge(v, b);
}

void hilbert_basis::add_ge(num_vector const& v) {
    add_ge(v, numeral(0));
}

void hilbert_basis::add_le(num_vector const& v) {
    add_le(v, numeral(0));
}

void hilbert_basis::add_eq(num_vector const& v) {
    add_le(v);
    add_ge(v);
}

unsigned hilbert_basis::get_num_vars() const {
    if (m_ineqs.empty()) {
        return 0;
    }
    else {
        return m_ineqs.back().size();
    }
}

hilbert_basis::values hilbert_basis::vec(offset_t offs) const {
    return values(m_store.c_ptr() + offs.m_offset);
}

void hilbert_basis::init_basis() {
    m_basis.reset();
    m_store.reset();
    m_free_list.reset();
    unsigned num_vars = get_num_vars();
    for (unsigned i = 0; i < num_vars; ++i) {
        num_vector w(num_vars, numeral(0));
        w[i] = numeral(1);
        offset_t idx = alloc_vector();
        values v = vec(idx);
        for (unsigned i = 0; i < num_vars; ++i) {
            v[i] = w[i];
        }
        m_basis.push_back(idx);
    }
}

lbool hilbert_basis::saturate() {
    init_basis();    
    for (unsigned i = 0; !m_cancel && i < m_ineqs.size(); ++i) {
        lbool r = saturate(m_ineqs[i]);
        ++m_stats.m_num_saturations;
        if (r != l_true) {
            return r;
        }
        
    }
    if (m_cancel) {
        return l_undef;
    }
    return l_true;
}

lbool hilbert_basis::saturate(num_vector const& ineq) {
    m_active.reset();
    m_passive->reset();
    m_zero.reset();
    m_index->reset();
    TRACE("hilbert_basis", display_ineq(tout, ineq););
    bool has_non_negative = false;
    iterator it = begin();
    for (; it != end(); ++it) {
        values v = vec(*it);
        set_eval(v, ineq);
        add_goal(*it);
        if (v.value().is_nonneg()) {
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
    for (unsigned i = 0; i < m_active.size(); ++i) {
        offset_t idx = m_active[i];
        if (vec(idx).value().is_pos()) {
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
    u.value() = v.value() + w.value();
    // std::cout << "resolve: " << v.value() << " + " << w.value() << " = " << u.value() << "\n";
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
        m_store.resize(idx + 1 + get_num_vars());
        return offset_t(idx);
    }
    else {
        offset_t result = m_free_list.back();
        m_free_list.pop_back();
        return result;
    }
}

void hilbert_basis::add_goal(offset_t idx) {
    values v = vec(idx);
    if (is_subsumed(idx)) {
        return;
    }
    m_index->insert(idx, v);
    if (v.value().is_zero()) {
        m_zero.push_back(idx);
    }
    else {
        m_passive->insert(idx);
    }
}

bool hilbert_basis::is_subsumed(offset_t idx)  {

    offset_t found_idx;
    if (m_index->find(vec(idx), idx, found_idx)) {        
        TRACE("hilbert_basis",  
           display(tout, idx);
           tout << " <= \n";
           display(tout, found_idx);
           tout << "\n";);
        ++m_stats.m_num_subsumptions;
        return true;
    }
    return false;
}

bool hilbert_basis::can_resolve(offset_t i, offset_t j) const {
    sign_t s1 = get_sign(i);
    sign_t s2 = get_sign(j);
    return s1 != s2 && abs(vec(i)[0] + vec(j)[0]) <= numeral(1);
}

hilbert_basis::sign_t hilbert_basis::get_sign(offset_t idx) const {
    numeral val = vec(idx).value();
    if (val.is_pos()) {
        return pos;
    }
    if (val.is_neg()) {
        return neg;
    }
    return zero;
}

void hilbert_basis::set_eval(values& val, num_vector const& ineq) const {
    numeral result(0);
    unsigned num_vars = get_num_vars();
    for (unsigned i = 0; i < num_vars; ++i) {
        result += val[i]*ineq[i];
    }
    val.value() = result;
}

void hilbert_basis::display(std::ostream& out) const {
    unsigned nv = get_num_vars();
    out << "inequalities:\n";
    for (unsigned i = 0; i < m_ineqs.size(); ++i) {
        display_ineq(out, m_ineqs[i]);
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

}

void hilbert_basis::display(std::ostream& out, offset_t o) const {
    display(out, vec(o));
    out << " -> " << vec(o).value() << "\n";    
}

void hilbert_basis::display(std::ostream& out, values const& v) const {
    unsigned nv = get_num_vars();
    for (unsigned j = 0; j < nv; ++j) {            
        out << v[j] << " ";
    }
}

void hilbert_basis::display_ineq(std::ostream& out, num_vector const& v) const {
    unsigned nv = get_num_vars();
    for (unsigned j = 0; j < nv; ++j) {
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
    out << " >= 0\n";
}


void hilbert_isl_basis::add_le(num_vector const& v, numeral bound) {
    unsigned sz = v.size();
    num_vector w;
    w.push_back(-bound);
    w.push_back(bound);
    for (unsigned i = 0; i < sz; ++i) {
        w.push_back(v[i]);
        w.push_back(-v[i]);
    }
    m_basis.add_le(w);
}
