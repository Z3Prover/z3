/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_partial_equiv.h

Abstract:

    Rule transformer which identifies predicates that are partial equivalence relations.

Author:

    Nikolaj Bjorner (nbjorner) 2012-05-14

Revision History:

--*/


#ifndef DL_MK_PARTIAL_EQUIVALENCE_TRANSFORMER_H_
#define DL_MK_PARTIAL_EQUIVALENCE_TRANSFORMER_H_

#include "dl_context.h"
#include "dl_rule_transformer.h"

namespace datalog {

    class mk_partial_equivalence_transformer : public rule_transformer::plugin {
        ast_manager & m;
        context &     m_context;
    public:
        mk_partial_equivalence_transformer(context & ctx, unsigned priority=45000)
            : plugin(priority),
            m(ctx.get_manager()),
            m_context(ctx) {}

        rule_set * operator()(rule_set const & source);

    private:

        bool is_symmetry(rule const* r);
        bool is_transitivity(rule const* r);
    };

};

#endif /* DL_MK_PARTIAL_EQUIV_TRANSFORMER_H_ */


