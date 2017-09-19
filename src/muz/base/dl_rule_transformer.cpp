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

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_transformer.h"
#include "util/stopwatch.h"

namespace datalog {

    rule_transformer::rule_transformer(context & ctx) 
        : m_context(ctx), m_rule_manager(m_context.get_rule_manager()), m_dirty(false) {
    }


    rule_transformer::~rule_transformer() {
        reset();
    }

    void rule_transformer::reset() {
        plugin_vector::iterator it = m_plugins.begin();
        plugin_vector::iterator end = m_plugins.end();
        for(; it!=end; ++it) {            
            dealloc(*it);
        }
        m_plugins.reset();
        m_dirty = false;
    }

    void rule_transformer::cancel() {
        plugin_vector::iterator it = m_plugins.begin();
        plugin_vector::iterator end = m_plugins.end();
        for(; it!=end; ++it) {
            (*it)->cancel();
        }
    }

    struct rule_transformer::plugin_comparator {
        bool operator()(rule_transformer::plugin * p1, rule_transformer::plugin * p2) {
            return p1->get_priority() > p2->get_priority();
        }
    };

    void rule_transformer::ensure_ordered() {
        if (m_dirty) {
            std::sort(m_plugins.begin(), m_plugins.end(), plugin_comparator());
            m_dirty = false;
        }
    }

    void rule_transformer::register_plugin(plugin * p) {
        m_plugins.push_back(p);
        p->attach(*this);
        m_dirty=true;
    }

    bool rule_transformer::operator()(rule_set & rules) {
        ensure_ordered();

        bool modified = false;

        TRACE("dl_rule_transf", 
            tout<<"init:\n";
            rules.display(tout);
        );
        rule_set* new_rules = alloc(rule_set, rules);
        plugin_vector::iterator it = m_plugins.begin();
        plugin_vector::iterator end = m_plugins.end();
        for(; it!=end && !m_context.canceled(); ++it) {
            plugin & p = **it;


            IF_VERBOSE(1, verbose_stream() << "(transform " << typeid(p).name() << "...";);
            stopwatch sw;
            sw.start();
            rule_set * new_rules1 = p(*new_rules);
            sw.stop();
            double sec = sw.get_seconds();
            if (sec < 0.001) sec = 0.0;
            if (!new_rules1) {
                IF_VERBOSE(1, verbose_stream() << "no-op " << sec << "s)\n";);
                continue;
            }
            if (p.can_destratify_negation() && 
                !new_rules1->is_closed() &&
                !new_rules1->close()) {
                warning_msg("a rule transformation skipped "
                            "because it destratified negation");
                dealloc(new_rules1);
                IF_VERBOSE(1, verbose_stream() << "no-op " << sec << "s)\n";);
                continue;
            }
            modified = true;
            dealloc(new_rules);
            new_rules = new_rules1;
            new_rules->ensure_closed();

            IF_VERBOSE(1, verbose_stream() << new_rules->get_num_rules() << " rules " << sec << "s)\n";);
            TRACE("dl_rule_transf", 
                tout << typeid(p).name()<<":\n";
                new_rules->display(tout);
            );
        }
        if (modified) {
            rules.replace_rules(*new_rules);
        }
        dealloc(new_rules);
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
