/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    special_relations_tactic.h

Abstract:

    Detect special relations in an axiomatization, 
    rewrite goal using special relations.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Notes:

--*/
#pragma once

#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/special_relations_decl_plugin.h"
#include "ast/pattern/expr_pattern_match.h"
#include "ast/simplifiers/special_relations_simplifier.h"

class special_relations_tactic : public tactic {
    ast_manager& m;
    params_ref m_params;
    expr_pattern_match m_pm;
    svector<sr_property> m_properties;
    
    struct sp_axioms {
        unsigned_vector m_goal_indices;
        sr_property     m_sp_features;
        sp_axioms():m_sp_features(sr_none) {}
    };

    void collect_feature(goal const& g, unsigned idx, obj_map<func_decl, sp_axioms>& goal_features);
    void insert(obj_map<func_decl, sp_axioms>& goal_features, func_decl* f, unsigned idx, sr_property p);

    void initialize();
    void register_pattern(unsigned index, sr_property);

public:

    special_relations_tactic(ast_manager & m, params_ref const & ref = params_ref()): 
        m(m), m_params(ref), m_pm(m) {}

    void updt_params(params_ref const & p) override { m_params.append(p); }
    
    void collect_param_descrs(param_descrs & r) override { }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;
    
    void cleanup() override {}

    tactic * translate(ast_manager & m) override { return alloc(special_relations_tactic, m, m_params); }

    char const* name() const override { return "special_relations"; }

};

tactic * mk_special_relations_tactic(ast_manager & m, params_ref const & p = params_ref());

inline tactic* mk_special_relations2_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(special_relations_simplifier, m, p, s);
        });
}

/*
  ADD_TACTIC("special-relations", "detect and replace by special relations.", "mk_special_relations_tactic(m, p)")
  ADD_TACTIC("special-relations2", "detect and replace by special relations.", "mk_special_relations2_tactic(m, p)")
  ADD_SIMPLIFIER("special-relations", "detect and replace by special relations.", "alloc(special_relations_simplifier, m, p, s)")
*/

