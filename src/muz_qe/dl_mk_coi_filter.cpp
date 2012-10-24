/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_coi_filter.cpp

Abstract:

    Rule transformer which removes relations which are out of the cone of 
    influence of output relations

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

--*/


#include <sstream>
#include"ast_pp.h"
#include"dl_mk_coi_filter.h"
#include"extension_model_converter.h"

namespace datalog {
  
    // -----------------------------------
    //
    // mk_coi_filter
    //
    // -----------------------------------


    rule_set * mk_coi_filter::operator()(
        rule_set const & source,
        model_converter_ref& mc,
        proof_converter_ref& pc) 
    {
        if (source.get_num_rules()==0) {
            return 0;
        }

        decl_set interesting_preds;
        decl_set pruned_preds;
        ptr_vector<func_decl> todo;
        {
            const decl_set& output_preds = m_context.get_output_predicates();
            decl_set::iterator oend = output_preds.end();
            for (decl_set::iterator it = output_preds.begin(); it!=oend; ++it) {
                todo.push_back(*it);
                interesting_preds.insert(*it);
            }
        }

        const rule_dependencies& deps = source.get_dependencies();

        while (!todo.empty()) {
            func_decl * curr = todo.back();
            todo.pop_back();
            interesting_preds.insert(curr);

            const rule_dependencies::item_set& cdeps = deps.get_deps(curr);
            rule_dependencies::item_set::iterator dend = cdeps.end();
            for (rule_dependencies::item_set::iterator it = cdeps.begin(); it!=dend; ++it) {
                func_decl * dep_pred = *it;
                if (!interesting_preds.contains(dep_pred)) {
                    interesting_preds.insert(dep_pred);
                    todo.push_back(dep_pred);
                }
            }
        }

        scoped_ptr<rule_set> res = alloc(rule_set, m_context);

        rule_set::iterator rend = source.end();
        for (rule_set::iterator rit = source.begin(); rit!=rend; ++rit) {
            rule * r = *rit;
            func_decl * pred = r->get_decl();
            if (interesting_preds.contains(pred)) {
                res->add_rule(r);
            }
            else if (mc.get()) {
                pruned_preds.insert(pred);
            }
        }

        if (res->get_num_rules() == source.get_num_rules()) {
            res = 0;
        }

        if (res && mc) {
            decl_set::iterator end = pruned_preds.end();
            decl_set::iterator it = pruned_preds.begin();
            extension_model_converter* mc0 = alloc(extension_model_converter, m);
            for (; it != end; ++it) {
                mc0->insert(*it, m.mk_true());
            }   
            mc = concat(mc.get(), mc0);
        }

        return res.detach();
    }

};

