/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    union_find.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-31.

Revision History:

--*/
#pragma once

#include "util/trail.h"
#include "util/trace.h"

class union_find_default_ctx {
public:
    typedef trail_stack _trail_stack;
       
    void unmerge_eh(unsigned, unsigned) {}
    void merge_eh(unsigned, unsigned, unsigned, unsigned) {}
    void after_merge_eh(unsigned, unsigned, unsigned, unsigned) {}

    _trail_stack& get_trail_stack() { return m_stack; }

private:
    _trail_stack m_stack;
};

template<typename Ctx = union_find_default_ctx, typename StackCtx = Ctx>
class union_find {
    Ctx &                         m_ctx;
    trail_stack &                 m_trail_stack;
    svector<unsigned>             m_find;
    svector<unsigned>             m_size;
    svector<unsigned>             m_next;
    
    class mk_var_trail;
    friend class mk_var_trail;

    class mk_var_trail : public trail {
        union_find & m_owner;
    public:
        mk_var_trail(union_find & o):m_owner(o) {}
        void undo() override {
            m_owner.m_find.pop_back();
            m_owner.m_size.pop_back();
            m_owner.m_next.pop_back();
        }
    };

    mk_var_trail                  m_mk_var_trail;

    class merge_trail;
    friend class merge_trail;

    class merge_trail : public trail {
        union_find & m_owner;
        unsigned     m_r1;
    public:
        merge_trail(union_find & o, unsigned r1):m_owner(o), m_r1(r1) {}
        void undo() override { m_owner.unmerge(m_r1); }
    };

    void unmerge(unsigned r1) {
        unsigned r2 = m_find[r1];
        TRACE("union_find", tout << "unmerging " << r1 << " " << r2 << "\n";);
        SASSERT(find(r2) == r2);
        m_size[r2] -= m_size[r1];
        m_find[r1]  = r1;
        std::swap(m_next[r1], m_next[r2]);
        m_ctx.unmerge_eh(r2, r1);
        CASSERT("union_find", check_invariant());
    }

public:    
    union_find(Ctx & ctx):m_ctx(ctx), m_trail_stack(ctx.get_trail_stack()), m_mk_var_trail(*this) {}

    unsigned mk_var() {
        unsigned r = m_find.size();
        m_find.push_back(r);
        m_size.push_back(1);
        m_next.push_back(r);
        m_trail_stack.push_ptr(&m_mk_var_trail);
        return r;
    }

    unsigned get_num_vars() const { return m_find.size(); }


    unsigned find(unsigned v) const {
        while (true) {
            SASSERT(v < m_find.size());
            unsigned new_v = m_find[v];
            if (new_v == v)
                return v;
            v = new_v;
        }
    }

    unsigned next(unsigned v) const { return m_next[v]; }

    unsigned size(unsigned v) const { return m_size[find(v)]; }

    bool is_root(unsigned v) const { return m_find[v] == v; }

    void merge(unsigned v1, unsigned v2) {
        unsigned r1 = find(v1);
        unsigned r2 = find(v2);
        TRACE("union_find", tout << "merging " << r1 << " " << r2 << "\n";);
        if (r1 == r2)
            return;
        if (m_size[r1] > m_size[r2]) {
            std::swap(r1, r2);
            std::swap(v1, v2);
        }
        m_ctx.merge_eh(r2, r1, v2, v1);
        m_find[r1] = r2;
        m_size[r2] += m_size[r1];
        std::swap(m_next[r1], m_next[r2]);
        m_trail_stack.push(merge_trail(*this, r1));
        m_ctx.after_merge_eh(r2, r1, v2, v1);
        CASSERT("union_find", check_invariant());
    }

    void set_root(unsigned v, unsigned root) {
        TRACE("union_find", tout << "merging " << v << " " << root << "\n";);
        SASSERT(v != root);
        m_find[v] = root;
        m_size[root] += m_size[v];
        std::swap(m_next[root], m_next[v]);
    }

    // dissolve equivalence class of v
    // this method cannot be used with backtracking.
    void dissolve(unsigned v) {
        unsigned w;
        do {
            w = next(v);                        
            m_size[v] = 1;
            m_find[v] = v;
            m_next[v] = v;            
        }
        while (w != v);
    }

    void display(std::ostream & out) const {
        unsigned num = get_num_vars(); 
        for (unsigned v = 0; v < num; v++) {
            out << "v" << v << " --> v" << m_find[v] << " (" << size(v) << ")\n";
        }
    }

#ifdef Z3DEBUG
    bool check_invariant() const {
        unsigned num = get_num_vars(); 
        for (unsigned v = 0; v < num; v++) {
            if (is_root(v)) {
                unsigned curr = v;
                unsigned sz   = 0;
                do {
                    SASSERT(find(curr) == v);
                    sz++;
                    curr = next(curr);
                }
                while (curr != v);
                SASSERT(m_size[v] == sz);
            }
        }
        return true;
    }
#endif
};


class basic_union_find {
    unsigned_vector   m_find;
    unsigned_vector   m_size;
    unsigned_vector   m_next;
    
    void ensure_size(unsigned v) {
        while (v >= get_num_vars()) {
            mk_var();
        }
    }
 public:
    unsigned mk_var() {
        unsigned r = m_find.size();
        m_find.push_back(r);
        m_size.push_back(1);
        m_next.push_back(r);
        return r;
    }
    unsigned get_num_vars() const { return m_find.size(); }
    
    unsigned find(unsigned v) const {
        if (v >= get_num_vars()) {
            return v;
        }
        while (true) {
            unsigned new_v = m_find[v];
            if (new_v == v)
                return v;
            v = new_v;
        }
    }
    
    unsigned next(unsigned v) const { 
        if (v >= get_num_vars()) {
            return v;
        }
        return m_next[v]; 
    }
    
    bool is_root(unsigned v) const { 
        return v >= get_num_vars() || m_find[v] == v; 
    }
    
    void merge(unsigned v1, unsigned v2) {
        unsigned r1 = find(v1);
        unsigned r2 = find(v2);
        if (r1 == r2)
            return;
        ensure_size(v1);
        ensure_size(v2);
        if (m_size[r1] > m_size[r2])
            std::swap(r1, r2);
        m_find[r1] = r2;
        m_size[r2] += m_size[r1];
        std::swap(m_next[r1], m_next[r2]);
    }
    
    void reset() {
        m_find.reset();
        m_next.reset();
        m_size.reset();
    }
};



