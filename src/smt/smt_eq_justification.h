/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_eq_justification.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef SMT_EQ_JUSTIFICATION_H_
#define SMT_EQ_JUSTIFICATION_H_

#include"smt_literal.h"
#include"tptr.h"

namespace smt {

    /**
       \brief Proof like object used to track dependencies of equality propagation. 
       The idea is to reduce the cost of dependency tracking for the most common
       justifications used during equality propagation: (asserted equality & congruence).
    */
    class eq_justification { 
        void * m_data;
    public:
        enum kind {
            AXIOM,           //!< no justification, it is only used when proof generation is disabled
            CONGRUENCE,
            EQUATION,        //!< asserted equation
            JUSTIFICATION    //!< fallback 
        };

        explicit eq_justification():
            m_data(reinterpret_cast<void*>(static_cast<size_t>(AXIOM))) {
        }

        /**
           \brief Create a justification for the congruence rule.
           If commutativity == true, then it means it is a combined justification: commutativity + congruence.
        */
        explicit eq_justification(bool commutativity):
            m_data(BOXTAGINT(void*, static_cast<unsigned>(commutativity), CONGRUENCE)) {
        }
        
        explicit eq_justification(literal l):
            m_data(BOXTAGINT(void*, l.index(), EQUATION)) {
        }
        
        explicit eq_justification(justification * js):
            m_data(TAG(void*, js, JUSTIFICATION)) {
        }
        
        kind get_kind() const {
            return static_cast<kind>(GET_TAG(m_data));
        }

        literal get_literal() const { SASSERT(get_kind() == EQUATION); return to_literal(UNBOXINT(m_data)); }
        
        justification * get_justification() const { SASSERT(get_kind() == JUSTIFICATION); return UNTAG(justification*, m_data); }

        bool used_commutativity() const { SASSERT(get_kind() == CONGRUENCE); return UNBOXINT(m_data) != 0; }
    
        static eq_justification mk_axiom() {
            return eq_justification();
        }

        static eq_justification mk_cg(bool comm = false) {
            return eq_justification(comm);
        }
    };

    const eq_justification null_eq_justification(static_cast<justification*>(0));
};

#endif /* SMT_EQ_JUSTIFICATION_H_ */

