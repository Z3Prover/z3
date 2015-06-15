/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    mk_separate_negated_tails.h

Abstract:

    Rule transformer which creates new rules for predicates
    in negated tails that use free variables not used
    elsewhere. These free variables incur an overhead
    on the instructions compiled using dl_compiler.

    Consider the following transformations:

       P(x)    :- Exists y, z, u . Q(x,y), !R(y,z), !T(z,u).
    => 
       P(x)    :- Exists y, z . Q(x,y), !R(y,z), Exists u . ! T(z,u).
    => 
       P(x)    :- Exists y, z . Q(x,y), !R(y,z), TN(z).
       TN(z)   :- !T(z,u).

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-09

Revision History:

--*/

#ifndef _DL_MK_SEPARAT_NEGATED_TAILS_H_
#define _DL_MK_SEPARAT_NEGATED_TAILS_H_

#include "dl_rule_transformer.h"
#include "dl_context.h"

namespace datalog {

    class mk_separate_negated_tails : public rule_transformer::plugin {
        ast_manager & m;
        rule_manager& rm;
        context &     m_ctx;
        ptr_vector<expr> m_vars;
        expr_free_vars   m_fv;
        
        bool has_private_vars(rule const& r, unsigned j);
        void get_private_vars(rule const& r, unsigned j);
        void abstract_predicate(app* p, app_ref& q, rule_set& rules);
        void create_rule(rule const&r, rule_set& rules);

    public:
        mk_separate_negated_tails(context& ctx, unsigned priority = 21000);
        rule_set * operator()(rule_set const & source);
    };
}

#endif
