/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_transformer.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-20.

Revision History:

--*/
#include <algorithm>
#include<typeinfo>

#include"dl_context.h"

#include"dl_rule_transformer.h"

namespace datalog {

    rule_transformer::rule_transformer(context & ctx) 
        : m_context(ctx), m_rule_manager(m_context.get_rule_manager()), m_dirty(false) {
    }


    rule_transformer::~rule_transformer() {
        plugin_vector::iterator it=m_plugins.begin();
        plugin_vector::iterator end=m_plugins.end();
        for(; it!=end; ++it) {
            dealloc(*it);
        }
    }

    struct rule_transformer::plugin_comparator {
        bool operator()(rule_transformer::plugin * p1, rule_transformer::plugin * p2) {
            return p1->get_priority()>p2->get_priority();
        }
    };

    void rule_transformer::ensure_ordered() {
        if (!m_dirty) {
            return;
        }
        std::sort(m_plugins.begin(), m_plugins.end(), plugin_comparator());
        m_dirty=false;
    }

    void rule_transformer::register_plugin(plugin * p) {
        m_plugins.push_back(p);
        p->attach(*this);
        m_dirty=true;
    }

    bool rule_transformer::operator()(rule_set & rules, model_converter_ref& mc, proof_converter_ref& pc) {
        ensure_ordered();

        bool modified = false;

        TRACE("dl_rule_transf", 
            tout<<"init:\n";
            rules.display(tout);
        );
        plugin_vector::iterator it=m_plugins.begin();
        plugin_vector::iterator end=m_plugins.end();
        for(; it!=end; ++it) {
            plugin & p = **it;

            rule_set * new_rules = p(rules, mc, pc);
            if (!new_rules) {
                continue;
            }
            if (p.can_destratify_negation()) {
                if (!new_rules->is_closed()) {
                    if (!new_rules->close()) {
                        warning_msg("a rule transformation skipped because it destratified negation");
                        dealloc(new_rules);
                        continue;
                    }
                }
            }
            modified = true;
            rules.reset();
            rules.add_rules(*new_rules);
            dealloc(new_rules);
            rules.ensure_closed();

            TRACE("dl_rule_transf", 
                tout << typeid(p).name()<<":\n";
                rules.display(tout);
            );

        }
        return modified;
    }

    //------------------------------
    //
    //rule_transformer::plugin
    //
    //------------------------------

    void rule_transformer::plugin::remove_duplicate_tails(app_ref_vector& tail, svector<bool>& tail_neg)
    {
        //one set for positive and one for negative
        obj_hashtable<app> tail_apps[2];
        unsigned i=0;
        while(i<tail.size()) {
            unsigned set_idx = tail_neg[i] ? 1 : 0;
            if (tail_apps[set_idx].contains(tail[i].get())) {
                if (i!=tail.size()-1) {
                    tail[i] = tail.back();
                    tail_neg[i] = tail_neg.back();
                }
                tail.pop_back();
                tail_neg.pop_back();
            }
            else {
                tail_apps[set_idx].insert(tail[i].get());
                i++;
            }
        }
    }



};
