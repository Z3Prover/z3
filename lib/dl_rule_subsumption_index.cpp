/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_subsumption_index.cpp

Abstract:

    Subsumption index for rules.
    Currently an underapproximation (fails to identify some subsumptions).

Author:

    Krystof Hoder (t-khoder) 2011-10-10.

Revision History:

--*/


#include <sstream>
#include "ast_pp.h"

#include "dl_rule_subsumption_index.h"

namespace datalog {
  
    // -----------------------------------
    //
    // rule_subsumption_index
    //
    // -----------------------------------


    void rule_subsumption_index::handle_unconditioned_rule(rule * r) {
        SASSERT(r->get_tail_size()==0);
        app * head = r->get_head();
        func_decl * pred = head->get_decl();

        app_set * head_set;
        if(!m_unconditioned_heads.find(pred, head_set)) {
            head_set = alloc(app_set);
            m_unconditioned_heads.insert(pred, head_set);
        }
        head_set->insert(head);
    }

    void rule_subsumption_index::add(rule * r) {
        m_ref_holder.push_back(r);
        if(r->get_tail_size()==0) {
            handle_unconditioned_rule(r);
        }
        m_rule_set.insert(r);
    }

    bool rule_subsumption_index::is_subsumed(app * query) {
        func_decl * pred = query->get_decl();

        app_set * head_set;
        if(m_unconditioned_heads.find(pred, head_set)) {
            if(head_set->contains(query)) {
                return true;
            }
        }
        return false;
    }

    bool rule_subsumption_index::is_subsumed(rule * r) {
        
        app * head = r->get_head();
        if(is_subsumed(head)) {
            return true;
        }

        if(m_rule_set.contains(r)) {
            return true;
        }

        return false;
    }

};

