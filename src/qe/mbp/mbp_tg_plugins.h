/*++

  Module Name:

    mbp_tg_plugins.h

Abstract:

    Model Based Projection for a theory

Author:

    Hari Govind V K (hgvk94) 2022-07-12

Revision History:


--*/
#pragma once
#include "ast/ast.h"
#include "qe/mbp/mbp_qel_util.h"
#include "qe/mbp/mbp_term_graph.h"
#include "util/obj_hashtable.h"

class mbp_tg_plugin {
public:
    // iterate through all terms in m_tg and apply all theory MBP rules once
    // returns true if any rules were applied
    virtual bool apply() { return false; };
    virtual ~mbp_tg_plugin() = default;
    virtual void use_model() { };
    virtual void get_new_vars(app_ref_vector*&) { };
    virtual family_id get_family_id() const { return null_family_id; };
};
