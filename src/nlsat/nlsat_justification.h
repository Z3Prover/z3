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
#ifndef NLSAT_JUSTIFICATION_H_
#define NLSAT_JUSTIFICATION_H_

#include "nlsat/nlsat_types.h"
#include "util/tptr.h"

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
        unsigned m_num_clauses;
        char     m_data[0];
        nlsat::clause* const* clauses() const { return (nlsat::clause *const*)(m_data); }
    public:
        static unsigned get_obj_size(unsigned nl, unsigned nc) { return sizeof(lazy_justification) + sizeof(literal)*nl + sizeof(nlsat::clause*)*nc; }
        lazy_justification(unsigned nl, literal const * lits, unsigned nc, nlsat::clause * const* clss):
            m_num_literals(nl),
            m_num_clauses(nc) {
            if (nc > 0) {
                memcpy(m_data + 0,                         clss, sizeof(nlsat::clause*)*nc);
            }
            if (nl > 0) {
                memcpy(m_data + sizeof(nlsat::clause*)*nc, lits, sizeof(literal)*nl);
            }
        }
        unsigned num_lits() const { return m_num_literals; }
        literal lit(unsigned i) const { SASSERT(i < num_lits()); return lits()[i]; }
        literal const * lits() const { return (literal const*)(m_data + m_num_clauses*sizeof(nlsat::clause*)); }

        unsigned num_clauses() const { return m_num_clauses; }
        nlsat::clause const& clause(unsigned i) const { SASSERT(i < num_clauses()); return *(clauses()[i]); }

    };

    class justification {
        void * m_data;
    public:
        enum kind { NULL_JST = 0, DECISION, CLAUSE, LAZY };
        justification():m_data(TAG(void *, nullptr, NULL_JST)) { SASSERT(is_null()); }
        justification(bool):m_data(TAG(void *, nullptr, DECISION)) { SASSERT(is_decision()); }
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

    inline std::ostream& operator<<(std::ostream& out, justification::kind k) {
        switch (k) {
        case justification::NULL_JST: return out << "null";
        case justification::DECISION: return out << "decision";
        case justification::CLAUSE: return out << "clause";
        case justification::LAZY: return out << "lazy";
        default: return out << "??";
        }
    }
    
    const justification null_justification;
    const justification decided_justification(true);

    inline justification mk_clause_jst(clause const * c) { return justification(const_cast<clause*>(c)); }
    inline justification mk_lazy_jst(small_object_allocator & a, unsigned nl, literal const * lits, unsigned nc, clause *const* clauses) {
        void * mem = a.allocate(lazy_justification::get_obj_size(nl, nc));
        return justification(new (mem) lazy_justification(nl, lits, nc, clauses));
    }

    inline void del_jst(small_object_allocator & a, justification jst) {
        if (jst.is_lazy()) {
            lazy_justification * ptr = jst.get_lazy();
            unsigned obj_sz = lazy_justification::get_obj_size(ptr->num_lits(), ptr->num_clauses());
            a.deallocate(obj_sz, ptr);
        }
    }
};

#endif
