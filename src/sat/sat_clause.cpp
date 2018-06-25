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
#include "sat/sat_clause.h"
#include "util/z3_exception.h"
#include "util/trace.h"

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
        m_inact_rounds(0),
        m_glue(255),
        m_psm(255) {
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
        for (literal l2 : *this) 
            if (l2 == l) 
                return true;
        return false;
    }

    bool clause::contains(bool_var v) const {
        for (literal l : *this) 
            if (l.var() == v)
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

    void clause::shrink(unsigned num_lits) { 
        SASSERT(num_lits <= m_size); 
        if (num_lits < m_size) { 
            m_size = num_lits; 
            mark_strengthened(); 
        } 
    }

    bool clause::satisfied_by(model const & m) const {
        for (literal l : *this) {
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

    clause_offset clause::get_new_offset() const {
        unsigned o1 = m_lits[0].index();
#if defined(_AMD64_) || defined(_M_IA64)
        if (sizeof(clause_offset) == 8) {
            unsigned o2 = m_lits[1].index();
            return (clause_offset)o1 + (((clause_offset)o2) << 32);
        }        
#endif
        return (clause_offset)o1;
    }

    void clause::set_new_offset(clause_offset offset) {
        m_lits[0] = to_literal(static_cast<unsigned>(offset));
#if defined(_AMD64_) || defined(_M_IA64)
        if (sizeof(offset) == 8) {
            m_lits[1] = to_literal(static_cast<unsigned>(offset >> 32));
        }
#endif
    }


    void tmp_clause::set(unsigned num_lits, literal const * lits, bool learned) {
        if (m_clause && m_clause->m_capacity < num_lits) {
            dealloc_svect(m_clause);
            m_clause = nullptr;
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
    }

    void clause_allocator::finalize() {
        m_allocator.reset();
    }

    clause * clause_allocator::get_clause(clause_offset cls_off) const {
        SASSERT(cls_off == reinterpret_cast<clause_offset>(reinterpret_cast<clause*>(cls_off)));
        return reinterpret_cast<clause *>(cls_off);
    }

    clause_offset clause_allocator::get_offset(clause const * cls) const {
        SASSERT(cls == reinterpret_cast<clause *>(reinterpret_cast<size_t>(cls)));
        return reinterpret_cast<size_t>(cls);
    }

    clause * clause_allocator::mk_clause(unsigned num_lits, literal const * lits, bool learned) {
        size_t size = clause::get_obj_size(num_lits);
        void * mem = m_allocator.allocate(size);
        clause * cls = new (mem) clause(m_id_gen.mk(), num_lits, lits, learned);
        TRACE("sat_clause", tout << "alloc: " << cls->id() << " " << *cls << " " << (learned?"l":"a") << "\n";);
        SASSERT(!learned || cls->is_learned());
        return cls;
    }

    clause * clause_allocator::copy_clause(clause const& other) {
        size_t size = clause::get_obj_size(other.size());
        void * mem = m_allocator.allocate(size);
        clause * cls = new (mem) clause(m_id_gen.mk(), other.size(), other.m_lits, other.is_learned());
        cls->m_reinit_stack = other.on_reinit_stack();
        cls->m_glue   = other.glue();
        cls->m_psm    = other.psm();
        cls->m_frozen = other.frozen();
        cls->m_approx = other.approx();
        return cls;
    }

    void clause_allocator::del_clause(clause * cls) {
        TRACE("sat_clause", tout << "delete: " << cls->id() << " " << *cls << "\n";);
        m_id_gen.recycle(cls->id());
        size_t size = clause::get_obj_size(cls->m_capacity);
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
        for (clause *cp : cs) {
            out << *cp << "\n";
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
        if (c.is_binary()) {
            out << "(" << c[0] << " " << c[1] << ")";
        }
        else {
            out << c.get_clause()->id() << ": " << *c.get_clause();
        }
        return out;
    }

};
