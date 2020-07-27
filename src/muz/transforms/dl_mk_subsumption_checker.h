/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mk_subsumption_checker.h

Abstract:

    Rule transformer which checks for subsumption
    (currently just for subsumption with total relations)

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

--*/

#pragma once

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/base/dl_rule_subsumption_index.h"

namespace datalog {

    class mk_subsumption_checker : public rule_transformer::plugin {


        ast_manager & m;
        context & m_context;

        rule_ref_vector m_ref_holder;

        func_decl_set m_total_relations;

        /** Map that for each relation contains the rule which implies its totality.
        If the totality is due to the relation containing all facts, the rule stored 
        here is zero*/
        obj_map<func_decl, rule *> m_total_relation_defining_rules;


        /**
        Contains heads of rules of shape
        R(c1,c2,...cN).
        grouped by their predicate.

        This information helps to improve the results of the 
        scan_for_relations_total_due_to_facts() function.
        */
        obj_map<func_decl, obj_hashtable<app> *> m_ground_unconditional_rule_heads;


        bool m_have_new_total_rule;
        bool m_new_total_relation_discovery_during_transformation;

        bool is_total_rule(const rule * r);



        /** Function to be called when a new total relation is discovered */
        void on_discovered_total_relation(func_decl * pred, rule * r);

        void scan_for_total_rules(rule_set const& rules);
        void scan_for_relations_total_due_to_facts(rule_set const& rules);

        void collect_ground_unconditional_rule_heads(const rule_set & rules);

        /** Return false if rule is unsatisfiable */
        bool transform_rule(rule * r, rule_subsumption_index& subs_index, rule_ref & res);
        /** Return false if the rule set hasn't changed */
        bool transform_rules(const rule_set & orig, rule_set & tgt);
    public:
        mk_subsumption_checker(context & ctx, unsigned priority=31000)
            : plugin(priority),
            m(ctx.get_manager()),
            m_context(ctx),
            m_ref_holder(ctx.get_rule_manager()),
            m_new_total_relation_discovery_during_transformation(true) {}
        ~mk_subsumption_checker() override {
            reset_dealloc_values(m_ground_unconditional_rule_heads);
        }

        rule_set * operator()(rule_set const & source) override;
    };

};


