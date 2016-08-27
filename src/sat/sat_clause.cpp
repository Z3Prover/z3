/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause.cpp

Abstract:

    Clauses

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#include<memory.h>
#include"sat_clause.h"
#include"z3_exception.h"
#include"trace.h"

namespace sat {

    clause::clause(unsigned id, unsigned sz, literal const * lits, bool learned):
        m_id(id),
        m_size(sz),
        m_capacity(sz),
        m_removed(false),
        m_learned(learned),
        m_used(false),
        m_frozen(false),
        m_reinit_stack(false),
        m_inact_rounds(0) {
        memcpy(m_lits, lits, sizeof(literal) * sz);
        mark_strengthened();
        SASSERT(check_approx());
        SASSERT(sz > 1);
    }

    var_approx_set clause::approx(unsigned num, literal const * lits) {
        var_approx_set r;
        for (unsigned i = 0; i < num; i++) 
            r.insert(lits[i].var());
        return r;
    }
    
    void clause::update_approx() {
        m_approx = approx(m_size, m_lits);
    }

    bool clause::check_approx() const {
        var_approx_set curr = m_approx;
        (void)curr;
        const_cast<clause*>(this)->update_approx();
        SASSERT(may_eq(curr, m_approx));
        return true;
    }

    bool clause::contains(literal l) const {
        for (unsigned i = 0; i < m_size; i++)
            if (m_lits[i] == l)
                return true;
        return false;
    }

    bool clause::contains(bool_var v) const {
        for (unsigned i = 0; i < m_size; i++)
            if (m_lits[i].var() == v)
                return true;
        return false;
    }

    void clause::elim(literal l) {
        unsigned i;
        for (i = 0; i < m_size; i++)
            if (m_lits[i] == l)
                break;
        SASSERT(i < m_size);
        i++;
        for (; i < m_size; i++)
            m_lits[i-1] = m_lits[i];
        m_size--;
        mark_strengthened();
    }

    bool clause::satisfied_by(model const & m) const {
        for (unsigned i = 0; i < m_size; i++) {
            literal  l = m_lits[i];
            if (l.sign()) {
                if (m[l.var()] == l_false)
                    return true;
            }
            else {
                if (m[l.var()] == l_true)
                    return true;
            }
        }
        return false;
    }

    void tmp_clause::set(unsigned num_lits, literal const * lits, bool learned) {
        if (m_clause && m_clause->m_capacity < num_lits) {
            dealloc_svect(m_clause);
            m_clause = 0;
        }
        if (!m_clause) {
            void * mem = alloc_svect(char, clause::get_obj_size(num_lits));
            m_clause   = new (mem) clause(UINT_MAX, num_lits, lits, learned);
        }
        else {
            SASSERT(m_clause->m_id == UINT_MAX);
            m_clause->m_size = num_lits;
            m_clause->m_learned = learned;
            memcpy(m_clause->m_lits, lits, sizeof(literal) * num_lits);
        }
        SASSERT(m_clause->m_size <= m_clause->m_capacity);
        for (unsigned i = 0; i < num_lits; i++) {
            SASSERT((*m_clause)[i] == lits[i]);
        }
    }

    clause_allocator::clause_allocator():
        m_allocator("clause-allocator") {
#if defined(_AMD64_) 
        m_num_segments = 0;
#if defined(Z3DEBUG)
        m_overflow_valid = false;
#endif
#endif
    }

    clause * clause_allocator::get_clause(clause_offset cls_off) const {
#if defined(_AMD64_) 
#if defined (Z3DEBUG)
        clause const* result;
        if (m_overflow_valid && m_cls_offset2ptr.find(cls_off, result)) {
            return const_cast<clause*>(result);
        }
#endif
        return reinterpret_cast<clause *>(m_segments[cls_off & c_aligment_mask] + (static_cast<size_t>(cls_off) & ~c_aligment_mask));
#else
        return reinterpret_cast<clause *>(cls_off);
#endif
    }

#if defined(_AMD64_) 
    unsigned clause_allocator::get_segment(clause const* cls) {
        size_t ptr = reinterpret_cast<size_t>(cls);

        SASSERT((ptr & c_aligment_mask) == 0);
        ptr &= ~0xFFFFFFFFull; // Keep only high part
        unsigned i = 0;
        for (i = 0; i < m_num_segments; ++i)
            if (m_segments[i] == ptr)
                return i;
        i = m_num_segments;
#if defined(Z3DEBUG)
        SASSERT(i < c_max_segments);
        if (i + 1 == c_max_segments) {
            m_overflow_valid = true;
            i += c_max_segments * m_cls_offset2ptr.size();
            m_ptr2cls_offset.insert(ptr, i);
            m_cls_offset2ptr.insert(i, cls);
        }
        else {
            ++m_num_segments;
            m_segments[i] = ptr;
        }
#else
        SASSERT(i <= c_max_segments);
        if (i == c_max_segments) {
            throw default_exception("segment out of range");
        }
        m_segments[i] = ptr;
        ++m_num_segments;
#endif
        return i;
    }
#endif

    clause_offset clause_allocator::get_offset(clause const * ptr) const {
#if defined(_AMD64_) 
        unsigned segment = const_cast<clause_allocator*>(this)->get_segment(ptr);
#if defined(Z3DEBUG)
        if (segment >= c_max_segments) {
            return m_ptr2cls_offset.find(reinterpret_cast<size_t>(ptr));
        }
#endif
        return static_cast<unsigned>(reinterpret_cast<size_t>(ptr)) + segment;
#else
        return reinterpret_cast<size_t>(ptr);
#endif
    }
    
    clause * clause_allocator::mk_clause(unsigned num_lits, literal const * lits, bool learned) {
        size_t size = clause::get_obj_size(num_lits);
#if defined(_AMD64_) 
        size_t slot = size >> c_cls_alignment;
        if ((size & c_aligment_mask) != 0)
            slot++;
        size = slot << c_cls_alignment;
#endif
        void * mem = m_allocator.allocate(size);
        clause * cls = new (mem) clause(m_id_gen.mk(), num_lits, lits, learned);
        TRACE("sat", tout << "alloc: " << cls->id() << " " << cls << " " << *cls << " " << (learned?"l":"a") << "\n";);
        SASSERT(!learned || cls->is_learned());
        return cls;
    }

    void clause_allocator::del_clause(clause * cls) {
        TRACE("sat", tout << "delete: " << cls->id() << " " << cls << " " << *cls << "\n";);
        m_id_gen.recycle(cls->id());
        size_t size = clause::get_obj_size(cls->m_capacity);
#if defined(_AMD64_) 
        size_t slot = size >> c_cls_alignment;
        if ((size & c_aligment_mask) != 0)
            slot++;
        size = slot << c_cls_alignment;
#endif
        cls->~clause();
        m_allocator.deallocate(size, cls);
    }

    std::ostream & operator<<(std::ostream & out, clause const & c) {
        out << "(";
        for (unsigned i = 0; i < c.size(); i++) {
            if (i > 0) out << " ";
            out << c[i];
        }
        out << ")";
        if (c.was_removed()) out << "x";
        if (c.strengthened()) out << "+";
        if (c.is_learned()) out << "*";
        return out;
    }

    std::ostream & operator<<(std::ostream & out, clause_vector const & cs) {
        clause_vector::const_iterator it  = cs.begin();
        clause_vector::const_iterator end = cs.end();
        for (; it != end; ++it) {
            out << *(*it) << "\n";
        }
        return out;
    }
    
    bool clause_wrapper::contains(literal l) const { 
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++)
            if (operator[](i) == l)
                return true;
        return false;
    }
    
    bool clause_wrapper::contains(bool_var v) const { 
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++)
            if (operator[](i).var() == v)
                return true;
        return false;
    }

    std::ostream & operator<<(std::ostream & out, clause_wrapper const & c) {
        out << "(";
        for (unsigned i = 0; i < c.size(); i++) {
            if (i > 0) out << " ";
            out << c[i];
        }
        out << ")";
        return out;
    }

};
