/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_b_justification.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef SMT_B_JUSTIFICATION_H_
#define SMT_B_JUSTIFICATION_H_

#include "smt/smt_literal.h"
#include "smt/smt_clause.h"

namespace smt {

    /**
       \brief Proof like object used to track dependencies of boolean propagation. 
       The idea is to reduce the cost of dependency tracking for the most common
       justifications used during boolean propagation: unit propagation
    */
    class b_justification {
        void * m_data;
    public:
        enum kind {
            CLAUSE,       //!< clause of arbitrary size
            BIN_CLAUSE,   //!< binary clause
            AXIOM,        //!< no justification, it is only use if proof generation is disabled
            JUSTIFICATION //!< fallback
        };

        b_justification():
            m_data(reinterpret_cast<void*>(static_cast<size_t>(AXIOM))) {}

        b_justification(b_justification const & source):
            m_data(source.m_data) {
        }

        explicit b_justification(clause * c):
            m_data(TAG(void*, c, CLAUSE)) {
        }
        
        explicit b_justification(literal l):
            m_data(BOXTAGINT(void*, l.index(), BIN_CLAUSE)) {
        }
        
        explicit b_justification(justification * js):            
            m_data(TAG(void*, js, JUSTIFICATION)) {
            SASSERT(js);
        }
        
        kind get_kind() const {
            return static_cast<kind>(GET_TAG(m_data));
        }
        
        clause * get_clause() const {
            SASSERT(get_kind() == CLAUSE);
            return UNTAG(clause*, m_data);
        }

        justification * get_justification() const {
            SASSERT(get_kind() == JUSTIFICATION);
            return UNTAG(justification*, m_data);
        }

        literal get_literal() const {
            SASSERT(get_kind() == BIN_CLAUSE);
            return to_literal(UNBOXINT(m_data));
        }

        bool operator==(b_justification const & other) const { 
            return m_data == other.m_data;
        }

        bool operator!=(b_justification const & other) const {
            return !operator==(other);
        }

        static b_justification mk_axiom() {
            return b_justification();
        }
    };

    const b_justification null_b_justification(static_cast<clause*>(nullptr));

    inline std::ostream& operator<<(std::ostream& out, b_justification::kind k) {
        switch (k) {
        case b_justification::CLAUSE: return out << "clause";
        case b_justification::BIN_CLAUSE: return out << "bin_clause";
        case b_justification::AXIOM: return out << "axiom";
        case b_justification::JUSTIFICATION: return out << "theory";
        }
        return out;
    }

    typedef std::pair<literal, b_justification> justified_literal;
};

#endif /* SMT_B_JUSTIFICATION_H_ */

