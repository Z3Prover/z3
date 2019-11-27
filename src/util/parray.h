/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    parray.h

Abstract:

    Persistent Arrays.

Author:

    Leonardo de Moura (leonardo) 2011-02-21.

Revision History:

--*/
#ifndef PARRAY_H_
#define PARRAY_H_

#include "util/vector.h"
#include "util/trace.h"

template<typename C>
class parray_manager {
public:
    typedef typename C::value         value;
    typedef typename C::value_manager value_manager;
    typedef typename C::allocator     allocator;
private:
    static size_t capacity(value * vs) {
        return vs == nullptr ? 0 : (reinterpret_cast<size_t*>(vs))[-1];
    }

    value * allocate_values(size_t c) {
        size_t * mem = static_cast<size_t*>(m_allocator.allocate(sizeof(value)*c + sizeof(size_t)));
        *mem = c;
        ++mem;
        value * r = reinterpret_cast<value*>(mem);
        SASSERT(capacity(r) == c);
        TRACE("parray_mem", tout << "allocated values[" << c << "]: " << r << "\n";);
        return r;
    }

    void deallocate_values(value * vs) {
        if (vs == nullptr)
            return;
        size_t c     = capacity(vs);
        TRACE("parray_mem", tout << "deallocated values[" << c << "]: " << vs << "\n";);
        size_t * mem = reinterpret_cast<size_t*>(vs);
        --mem;
        m_allocator.deallocate(sizeof(value)*c + sizeof(size_t), mem);
    }

    enum ckind { SET, PUSH_BACK, POP_BACK, ROOT };
    struct cell {
        unsigned m_ref_count:30;
        unsigned m_kind:2;
        union {
            unsigned m_idx;
            unsigned m_size;
        };
        value m_elem;
        union {
            cell  * m_next;
            value * m_values;
        };

        ckind kind() const { return static_cast<ckind>(m_kind); }

        unsigned idx() const { SASSERT(kind() != ROOT); return m_idx; }
        unsigned size() const { SASSERT(kind() == ROOT); return m_size; }
        cell * next() const { SASSERT(kind() != ROOT); return m_next; }
        value const & elem() const { SASSERT(kind() == SET || kind() == PUSH_BACK); return m_elem; }
        cell(ckind k):m_ref_count(1), m_kind(k), m_size(0), m_values(nullptr) {}
    };

    value_manager &  m_vmanager;
    allocator  &     m_allocator;
    ptr_vector<cell> m_get_values_tmp;
    ptr_vector<cell> m_reroot_tmp;

    void inc_ref(value const & v) {
        if (C::ref_count)
            m_vmanager.inc_ref(v);
    }

    void dec_ref(value const & v) {
        if (C::ref_count)
            m_vmanager.dec_ref(v);
    }

    void dec_ref(unsigned sz, value * vs) {
        if (C::ref_count) 
            for (unsigned i = 0; i < sz; i++)
                m_vmanager.dec_ref(vs[i]);
    }

    cell * mk(ckind k) {
        cell * r = new (m_allocator.allocate(sizeof(cell))) cell(k);
        TRACE("parray_mem", tout << "allocated cell: " << r << "\n";);
        return r;
    }

    void del(cell * c) {
        while (true) {
            cell * next = nullptr;
            switch (c->kind()) {
            case SET:
            case PUSH_BACK:
                dec_ref(c->elem());
                next = c->next();
                break;
            case POP_BACK:
                next = c->next();
                break;
            case ROOT:
                dec_ref(c->size(), c->m_values);
                deallocate_values(c->m_values);
                break;
            }
            TRACE("parray_mem", tout << "deallocated cell: " << c << "\n";);
            c->~cell();
            m_allocator.deallocate(sizeof(cell), c);
            if (next == nullptr)
                return;
            SASSERT(next->m_ref_count > 0);
            next->m_ref_count--;
            if (next->m_ref_count > 0)
                return;
            c = next;
        }
    }

    void inc_ref(cell * c) {
        if (!c) return;
        c->m_ref_count++;
    }

    void dec_ref(cell * c) {
        if (!c) return;
        TRACE("parray_mem", tout << "dec_ref(" << c << "), ref_count: " << c->m_ref_count << "\n";);
        SASSERT(c->m_ref_count > 0);
        c->m_ref_count--;
        if (c->m_ref_count == 0)
            del(c);
    }

    void expand(value * & vs) {
        size_t curr_capacity = capacity(vs);
        size_t new_capacity  = curr_capacity == 0 ? 2 : (3 * curr_capacity + 1) >> 1;
        value * new_vs       = allocate_values(new_capacity);
        if (curr_capacity > 0) {
            for (size_t i = 0; i < curr_capacity; i++) 
                new_vs[i] = vs[i];
            deallocate_values(vs);
        }
        vs = new_vs;
    }

    void rset(value * vs, unsigned i, value const & v) {
        inc_ref(v);
        dec_ref(vs[i]);
        vs[i] = v;
    }

    void rset(cell * c, unsigned i, value const & v) {
        SASSERT(c->kind() == ROOT);
        SASSERT(i < c->size());
        rset(c->m_values, i, v);
    }

    void rpush_back(value * & vs, unsigned & sz, value const & v) {
        if (sz == capacity(vs))
            expand(vs);
        SASSERT(sz < capacity(vs));
        inc_ref(v);
        vs[sz] = v;
        sz++;
    }     

    void rpush_back(cell * c, value const & v) {
        SASSERT(c->kind() == ROOT);
        rpush_back(c->m_values, c->m_size, v);
    }

    void rpop_back(value * vs, unsigned & sz) {
        sz--;
        dec_ref(vs[sz]);
    }

    void rpop_back(cell * c) {
        SASSERT(c->kind() == ROOT);
        rpop_back(c->m_values, c->m_size);
    }

    void copy_values(value * s, unsigned sz, value * & t) {
        SASSERT(t == 0);
        t = allocate_values(capacity(s));
        for (unsigned i = 0; i < sz; i++) {
            t[i] = s[i];
            inc_ref(t[i]);
        }
    }

    unsigned get_values(cell * s, value * & vs) {
        ptr_vector<cell> & cs = m_get_values_tmp;
        cs.reset();
        cell * r = s;
        while (r->kind() != ROOT) {
            cs.push_back(r);
            r = r->next();
        }
        SASSERT(r->kind() == ROOT);
        unsigned sz = r->m_size;
        vs = nullptr;
        copy_values(r->m_values, sz, vs);
        for (unsigned i = cs.size(); i-- > 0; ) {
            cell * curr = cs[i];
            switch (curr->kind()) {
            case SET:
                rset(vs, curr->m_idx, curr->m_elem);
                break;
            case POP_BACK:
                rpop_back(vs, sz);
                break;
            case PUSH_BACK:
                rpush_back(vs, sz, curr->m_elem);
                break;
            case ROOT:
                UNREACHABLE();
                break;
            }
        }
        return sz;
    }

    void unfold(cell * c) {
        if (c->kind() == ROOT)
            return;
        value * vs;
        unsigned sz   = get_values(c, vs);
        dec_ref(c->m_next);
        if (c->kind() == SET || c->kind() == PUSH_BACK)
            dec_ref(c->m_elem);
        c->m_next     = nullptr;
        c->m_kind     = ROOT;
        c->m_size     = sz;
        c->m_values   = vs;
        SASSERT(c->kind() == ROOT);
    }

public:
    class ref {
        cell *    m_ref;
        unsigned  m_updt_counter; // counter for minimizing memory consumption when using preserve_roots option
        ref(cell * r):m_ref(r), m_updt_counter(0) {}
        bool root() const { return m_ref->kind() == ROOT; }
        bool unshared() const { return m_ref->m_ref_count == 1; }
        friend class parray_manager;
    public:
        ref():m_ref(nullptr), m_updt_counter(0) {}
    };

public:
    parray_manager(value_manager & m, allocator & a):
        m_vmanager(m),
        m_allocator(a) {
    }

    value_manager & manager() { return m_vmanager; }
    
    void mk(ref & r) {
        dec_ref(r.m_ref);
        cell * new_c = mk(ROOT);
        r.m_ref          = new_c;
        r.m_updt_counter = 0;
        SASSERT(new_c->m_ref_count == 1);
    }

    void del(ref & r) {
        dec_ref(r.m_ref);
        r.m_ref          = nullptr;
        r.m_updt_counter = 0;
    }
    
    void copy(ref const & s, ref & t) {
        inc_ref(s.m_ref);
        dec_ref(t.m_ref);
        t.m_ref = s.m_ref;
        t.m_updt_counter = 0; 
    }

    unsigned size(ref const & r) const {
        cell * c = r.m_ref;
        if (c == nullptr) return 0;
        while (true) {
            switch (c->kind()) {
            case SET:
                c = c->next();
                break;
            case PUSH_BACK:
                return c->idx() + 1;
            case POP_BACK:
                return c->idx() - 1;
            case ROOT:
                return c->size();
            }
        }
    }

    void check_size(cell* c) const {
        unsigned r;
        while (c) {
            switch (c->kind()) {
            case SET:
                break;
            case PUSH_BACK:
                r = size(c->next());
                break;
            case POP_BACK:
                r = size(c->next());
                SASSERT(c->idx() == r);
                break;
            case ROOT:
                return;
            }
            c = c->next();
        }
    }

    bool empty(ref const & r) const { return size(r) == 0; }

    value const & get(ref const & r, unsigned i) const {
        SASSERT(i < size(r));
        
        unsigned trail_sz = 0;
        cell * c = r.m_ref;

        while (true) {
            if (trail_sz > C::max_trail_sz) {
                const_cast<parray_manager*>(this)->reroot(const_cast<ref&>(r));
                SASSERT(r.m_ref->kind() == ROOT);
                return r.m_ref->m_values[i];
            }
            switch (c->kind()) {
            case SET:
            case PUSH_BACK:
                if (i == c->idx())
                    return c->elem();
                trail_sz++;
                c = c->next();
                break;
            case POP_BACK:
                trail_sz++;
                c = c->next();
                break;
            case ROOT:
                return c->m_values[i];
            }
        }
    }

    void set(ref & r, unsigned i, value const & v) {
        SASSERT(i < size(r));
        if (r.root()) {
            if (r.unshared()) {
                rset(r.m_ref, i, v);
                return;
            }
            if (C::preserve_roots) {
                if (r.m_updt_counter > size(r)) {
                    unshare(r);
                    SASSERT(r.unshared());
                    SASSERT(r.m_updt_counter == 0);
                    rset(r.m_ref, i, v);
                    return;
                }
                r.m_updt_counter++;
                cell * c        = r.m_ref;
                cell * new_c    = mk(ROOT);
                new_c->m_size   = c->m_size;
                new_c->m_values = c->m_values;
                inc_ref(new_c);
                c->m_kind       = SET;
                c->m_idx        = i;
                c->m_elem       = c->m_values[i];
                inc_ref(c->m_elem);
                c->m_next       = new_c;
                dec_ref(c);
                r.m_ref         = new_c;
                rset(new_c, i, v);
                SASSERT(new_c->m_ref_count == 2);
                return;
            }
        }
        cell * new_c  = mk(SET);
        new_c->m_idx       = i;
        inc_ref(v);
        new_c->m_elem      = v;
        new_c->m_next      = r.m_ref;
        r.m_ref = new_c;
        SASSERT(new_c->m_ref_count == 1);
    }

    void set(ref const & s, unsigned i, value const & v, ref & r) {
        SASSERT(i < size(s));
        if (&s == &r) {
            set(r, i, v);
            return;
        }
        copy(s, r);
        set(r, i, v);
    }

    void push_back(ref & r, value const & v) {
        if (r.m_ref == nullptr)
            mk(r);
        if (r.root()) {
            if (r.unshared()) {
                rpush_back(r.m_ref, v);
                return;
            }
            if (C::preserve_roots) {
                if (r.m_updt_counter > size(r)) {
                    unshare(r);
                    SASSERT(r.unshared());
                    SASSERT(r.m_updt_counter == 0);
                    rpush_back(r.m_ref, v);
                    return;
                }
                r.m_updt_counter++;
                cell * c        = r.m_ref;
                SASSERT(c->m_ref_count > 1);
                cell * new_c    = mk(ROOT);
                new_c->m_size   = c->m_size;
                new_c->m_values = c->m_values;
                inc_ref(new_c);
                c->m_kind       = POP_BACK;
                c->m_idx        = new_c->m_size + 1;
                c->m_next       = new_c;
                dec_ref(c);
                r.m_ref         = new_c;
                rpush_back(new_c, v);
                SASSERT(new_c->m_ref_count == 2);
                return;
            }
        }
        cell * new_c  = mk(PUSH_BACK);
        new_c->m_idx       = size(r.m_ref);
        inc_ref(v);
        new_c->m_elem      = v;
        new_c->m_next      = r.m_ref;
        r.m_ref            = new_c; 
        SASSERT(new_c->m_ref_count == 1);
    }

    void push_back(ref const & s, value const & v, ref & r) {
        if (&s == &r) {
            push_back(r, v);
            return;
        }
        copy(s, r);
        push_back(r, v);
    }

    void pop_back(ref & r) {
        SASSERT(!empty(r));
        if (r.root()) {
            if (r.unshared()) {
                rpop_back(r.m_ref);
                return;
            }
            if (C::preserve_roots) {
                if (r.m_updt_counter > size(r)) {
                    unshare(r);
                    SASSERT(r.unshared());
                    SASSERT(r.m_updt_counter == 0);
                    rpop_back(r.m_ref);
                    return;
                }
                r.m_updt_counter++;
                cell * c        = r.m_ref;
                SASSERT(c->m_ref_count > 1);
                cell * new_c    = mk(ROOT);
                new_c->m_size   = c->m_size;
                new_c->m_values = c->m_values;
                inc_ref(new_c);
                c->m_kind       = PUSH_BACK;
                c->m_idx        = new_c->m_size - 1;
                c->m_elem       = new_c->m_values[c->m_idx];
                inc_ref(c->m_elem);
                c->m_next       = new_c;
                dec_ref(c);
                r.m_ref         = new_c;
                rpop_back(new_c);
                SASSERT(new_c->m_ref_count == 2);
                return;
            }
        }
        cell * new_c = mk(POP_BACK);
        new_c->m_idx  = size(r.m_ref);
        new_c->m_next = r.m_ref;
        r.m_ref       = new_c;
        SASSERT(new_c->m_ref_count == 1);
    }

    void pop_back(ref const & s, ref & r) {
        SASSERT(!empty(s));
        if (&s == &r) {
            pop_back(r);
            return;
        }
        copy(s, r);
        pop_back(r);
    }

    void unshare(ref & r) {
        if (r.root() && r.unshared())
            return;
        cell * c      = r.m_ref;
        cell * new_c  = mk(ROOT);
        new_c->m_size = get_values(c, new_c->m_values);
        SASSERT(new_c->m_ref_count == 1);
        dec_ref(c);
        r.m_ref       = new_c;
        r.m_updt_counter = 0;
        SASSERT(r.root());
        SASSERT(r.unshared());
    }

    void unfold(ref & r) {
        if (r.root())
            return;
        unfold(r.m_ref);
        r.m_updt_counter = 0;
        SASSERT(r.root());
    }
    
    void reroot(ref & r) {
        if (r.root())
            return;
        ptr_vector<cell> & cs = m_reroot_tmp;
        cs.reset();
        unsigned r_sz = size(r);
        unsigned trail_split_idx = r_sz / C::factor;
        unsigned i = 0;
        cell * c   = r.m_ref;        
        while (c->kind() != ROOT && i < trail_split_idx) {
            cs.push_back(c);
            c = c->next();
            i++;
        }
        if (c->kind() != ROOT) {
            // root is too far away.
            unfold(c);
        }
        DEBUG_CODE(check_size(c););
        SASSERT(c->kind() == ROOT);      
        for (i = cs.size(); i-- > 0; ) {
            cell * p = cs[i];
            SASSERT(c->m_kind == ROOT);
            unsigned sz = c->m_size;
            value * vs  = c->m_values;
            SASSERT(p->m_kind != ROOT);
            SASSERT(p->m_next == c);
            switch (p->m_kind) {
            case SET:
                c->m_kind    = SET;
                c->m_idx     = p->m_idx;
                c->m_elem    = vs[c->m_idx];
                vs[p->m_idx] = p->m_elem;
                break;
            case PUSH_BACK:
                c->m_kind = POP_BACK;
                if (sz == capacity(vs))
                    expand(vs);                
                vs[sz] = p->m_elem;
                ++sz;
                c->m_idx = sz;
                break;
            case POP_BACK:
                c->m_kind = PUSH_BACK;
                --sz;
                c->m_idx  = sz;
                c->m_elem = vs[sz];
                break;
            case ROOT:
                UNREACHABLE();
                break;
            }
            inc_ref(p);
            c->m_next   = p;

            p->m_kind   = ROOT;
            p->m_size   = sz;
            p->m_values = vs;
            // p does not point to c anymore
            dec_ref(c);
            c = p;
        }
        SASSERT(c == r.m_ref);
        SASSERT(c->kind() == ROOT);
        SASSERT(c->m_size == r_sz);
        r.m_updt_counter = 0;
        SASSERT(r.root());
    }

    void display_info(std::ostream & out, ref const & r) {
        cell * c = r.m_ref;
        if (c == 0) {
            out << "<null>";
            return;
        }
        while (true) {
            out << "cell[" << c << ", ";
            switch (c->kind()) {
            case SET: out << "set, " << c->m_idx; break;
            case PUSH_BACK: out << "push, " << c->m_idx; break;
            case POP_BACK: out << "pop, " << c->m_idx; break;
            case ROOT: out << "root, " << c->m_size << ", " << capacity(c->m_values); break;
            }
            out << "]#" << c->m_ref_count;
            if (c->kind() == ROOT) {
                out << "\n";
                break;
            }
            out << " -> \n";
            c = c->next();
        }
    }
};

template<typename T>
struct dummy_value_manager {
    void inc_ref(T const &) {}
    void dec_ref(T const &) {}
};

#endif
