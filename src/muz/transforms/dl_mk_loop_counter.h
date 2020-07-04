/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_loop_counter.h

Abstract:

    Add loop counter argument to relations.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-31

Revision History:

--*/
#pragma once

#include "muz/base/dl_rule_transformer.h"
#include "ast/arith_decl_plugin.h"

namespace datalog {

    class mk_loop_counter : public rule_transformer::plugin {
        ast_manager& m;
        context&     m_ctx;
        arith_util   a;
        func_decl_ref_vector m_refs;
        obj_map<func_decl, func_decl*> m_new2old;
        obj_map<func_decl, func_decl*> m_old2new;

        app_ref add_arg(rule_set const& src, rule_set& dst, app* fn, unsigned idx);        
        app_ref del_arg(app* fn);        
    public:
        mk_loop_counter(context & ctx, unsigned priority = 33000);
        ~mk_loop_counter() override;
        
        rule_set * operator()(rule_set const & source) override;

        func_decl* get_old(func_decl* f) const { return m_new2old.find(f); }

        rule_set * revert(rule_set const& source);
    };

};


