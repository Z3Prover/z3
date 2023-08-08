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


enum synth_op_kind {
    OP_SYNTH_DECLARE_OUTPUT,
    OP_SYNTH_DECLARE_GRAMMAR,
    LAST_SYNTH_OP
};

class synth_decl_plugin : public decl_plugin {
public:
    synth_decl_plugin();

    decl_plugin * mk_fresh() override {
        return alloc(synth_decl_plugin);
    }
    
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { return nullptr; }
};



