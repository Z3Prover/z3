/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    synth_decl_plugin.cpp

Abstract:

    Plugin for function symbols used for synthesis

Author:

    Petra Hozzova 2023-08-09
    Nikolaj Bjorner (nbjorner) 2023-08-08

--*/

#include "ast/synth_decl_plugin.h"



synth_decl_plugin::synth_decl_plugin() {}

func_decl * synth_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                            unsigned arity, sort * const * domain, sort * range) {
    auto& m = *m_manager;
    if (!range)
        range = m.mk_bool_sort();
    
    if (!m.is_bool(range))
        m.raise_exception("range of synthesis declaration is Bool");

    if (num_parameters > 0)
        m.raise_exception("no parameters are expected");

    symbol name;
    switch (k) {
    case OP_SYNTH_DECLARE_OUTPUT:
        name = "synthesiz3";
        break;
    case OP_SYNTH_DECLARE_GRAMMAR: 
    default:
        NOT_IMPLEMENTED_YET();
    }
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    return m.mk_func_decl(name, arity, domain, range, info);
}

void synth_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name("synthesiz3", OP_SYNTH_DECLARE_OUTPUT));
    }
}
   



