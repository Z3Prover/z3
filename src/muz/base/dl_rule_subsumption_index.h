/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_subsumption_index.h

Abstract:

    Subsumption index for rules.
    Currently an underapproximation (fails to identify some subsumptions).

Author:

    Krystof Hoder (t-khoder) 2011-10-10.

Revision History:

--*/

#ifndef DL_RULE_SUBSUMPTION_INDEX_H_
#define DL_RULE_SUBSUMPTION_INDEX_H_

#include "dl_context.h"

namespace datalog {

    class rule_subsumption_index {
        //private and undefined copy constroctor
        rule_subsumption_index(rule_subsumption_index const&);
        //private and undefined operator=
        rule_subsumption_index& operator=(rule_subsumption_index const&);

        typedef obj_hashtable<app> app_set;

        ast_manager & m;
        context & m_context;

        rule_ref_vector m_ref_holder;

        obj_map<func_decl, app_set *> m_unconditioned_heads;

        hashtable<rule *, rule_hash_proc, rule_eq_proc> m_rule_set;

        void handle_unconditioned_rule(rule * r);

    public:
        rule_subsumption_index(context & ctx) :
            m(ctx.get_manager()),
            m_context(ctx),
            m_ref_holder(ctx.get_rule_manager()) {}

        ~rule_subsumption_index() {
            reset_dealloc_values(m_unconditioned_heads);
        }

        void add(rule * r);
        bool is_subsumed(rule * r);
        bool is_subsumed(app * query);
    };

};

#endif /* DL_RULE_SUBSUMPTION_INDEX_H_ */

