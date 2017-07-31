/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mam.h

Abstract:

    Matching Abstract Machine

Author:

    Leonardo de Moura (leonardo) 2007-02-13.

Revision History:

--*/
#ifndef MAM_H_
#define MAM_H_

#include "ast/ast.h"
#include "smt/smt_types.h"

namespace smt {
    /**
       \brief Matching Abstract Machine (MAM)
    */
    class mam {
    protected:
        context &       m_context;
    public:
        mam(context & ctx):
            m_context(ctx) {
        }
        
        virtual ~mam() {
        }
        
        virtual void add_pattern(quantifier * q, app * mp) = 0;

        virtual void push_scope() = 0;

        virtual void pop_scope(unsigned num_scopes) = 0;

        virtual void match() = 0;
        
        virtual void rematch(bool use_irrelevant = false) = 0;

        virtual bool has_work() const = 0;

        virtual void relevant_eh(enode * n, bool lazy) = 0;
        
        virtual void add_eq_eh(enode * r1, enode * r2) = 0;

        virtual void reset() = 0;

        virtual void display(std::ostream& out) = 0;
        
        virtual void on_match(quantifier * q, app * pat, unsigned num_bindings, enode * const * bindings, unsigned max_generation, ptr_vector<enode> & used_enodes) = 0;
        
        virtual bool is_shared(enode * n) const = 0;

#ifdef Z3DEBUG
        virtual bool check_missing_instances() = 0;
#endif
    };

    mam * mk_mam(context & ctx);
};

#endif /* MAM_H_ */
