/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_justification.h

Abstract:

    An explanation for a (Boolean) assignment in the 
    nlsat procedure

Author:

    Leonardo de Moura (leonardo) 2012-01-10.

Revision History:

--*/
#ifndef _NLSAT_JUSTIFICATION_H_
#define _NLSAT_JUSTIFICATION_H_

#include"nlsat_types.h"
#include"tptr.h"

namespace nlsat {

    // There are two kinds of justifications in nlsat:
    //
    // - clause
    //
    // - lazy_justification: it is a set of arithmetic literals s.t.
    // the maximal variable in each literal is the same. 
    // The set is inconsistent in the current model.
    // Thus, our nonlinear procedure may be applied to it
    // to produce a clause.
    //

    class lazy_justification {
        unsigned m_num_literals;
        literal  m_literals[0];
    public:
        static unsigned get_obj_size(unsigned num) { return sizeof(lazy_justification) + sizeof(literal)*num; }
        lazy_justification(unsigned num, literal const * lits):
            m_num_literals(num) {
            memcpy(m_literals, lits, sizeof(literal)*num);
        }
        unsigned size() const { return m_num_literals; }
        literal operator[](unsigned i) const { SASSERT(i < size()); return m_literals[i]; }
        literal const * lits() const { return m_literals; }
    };

    class justification {
        void * m_data;
    public:
        enum kind { NULL_JST = 0, DECISION, CLAUSE, LAZY };
        justification():m_data(TAG(void *, static_cast<void*>(0), NULL_JST)) { SASSERT(is_null()); }
        justification(bool):m_data(TAG(void *, static_cast<void*>(0), DECISION)) { SASSERT(is_decision()); }
        justification(clause * c):m_data(TAG(void *, c, CLAUSE)) { SASSERT(is_clause()); }
        justification(lazy_justification * j):m_data(TAG(void *, j, LAZY)) { SASSERT(is_lazy()); }
        kind get_kind() const { return static_cast<kind>(GET_TAG(m_data)); }
        bool is_null() const { return get_kind() == NULL_JST; }
        bool is_decision() const { return get_kind() == DECISION; }
        bool is_clause() const { return get_kind() == CLAUSE; }
        bool is_lazy() const { return get_kind() == LAZY; }
        clause * get_clause() const { return UNTAG(clause*, m_data); }
        lazy_justification * get_lazy() const { return UNTAG(lazy_justification*, m_data); }
        bool operator==(justification other) const { return m_data == other.m_data; }
        bool operator!=(justification other) const { return m_data != other.m_data; }
    };
    
    const justification null_justification;
    const justification decided_justification(true);

    inline justification mk_clause_jst(clause const * c) { return justification(const_cast<clause*>(c)); }
    inline justification mk_lazy_jst(small_object_allocator & a, unsigned num, literal const * lits) {
        void * mem = a.allocate(lazy_justification::get_obj_size(num));
        return justification(new (mem) lazy_justification(num, lits));
    }

    inline void del_jst(small_object_allocator & a, justification jst) {
        if (jst.is_lazy()) {
            lazy_justification * ptr = jst.get_lazy();
            unsigned obj_sz = lazy_justification::get_obj_size(ptr->size());
            a.deallocate(obj_sz, ptr);
        }
    }
};

#endif
