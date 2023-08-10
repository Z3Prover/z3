/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    synth_decl_plugin.h

Abstract:

    Plugin for function symbols used for synthesis

Author:

    Petra Hozzova 2023-08-09
    Nikolaj Bjorner (nbjorner) 2023-08-08

--*/
#pragma once

#include "ast/ast.h"

namespace synth {

    enum op_kind {
        OP_DECLARE_OUTPUT,
        OP_DECLARE_GRAMMAR,
	OP_DECLARE_SPECIFICATION,
        LAST_OP
    };
    
    class plugin : public decl_plugin {
    public:
        plugin();
        
        plugin * mk_fresh() override {
            return alloc(plugin);
        }
        
        func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                 unsigned arity, sort * const * domain, sort * range) override;
        
        void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
        
        sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { return nullptr; }
    };
    
    class util {
        ast_manager& m;
        family_id m_fid;
    public:
        util(ast_manager& m): m(m), m_fid(m.get_family_id("synth")) {}
        
        bool is_synthesiz3(expr* e) const { return is_app_of(e, m_fid, OP_DECLARE_OUTPUT); }
        bool is_grammar(expr* e) const { return is_app_of(e, m_fid, OP_DECLARE_GRAMMAR); }
        bool is_specification(expr const* e) const { return is_app_of(e, m_fid, OP_DECLARE_SPECIFICATION); }
        bool is_specification(func_decl const* f) const { return is_decl_of(f, m_fid, OP_DECLARE_SPECIFICATION); }

        MATCH_UNARY(is_specification);
    };
    
}

