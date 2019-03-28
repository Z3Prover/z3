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
#ifndef SPECIAL_RELATIONS_TACTIC_H_
#define SPECIAL_RELATIONS_TACTIC_H_

#include "tactic/tactic.h"
#include "tactic/tactical.h"

class special_relations_tactic : public tactic {
    params_ref m_params;
    
    struct sp_axioms {
        unsigned_vector m_goal_indices;
        unsigned        m_sp_features;
    };

    void collect_feature(goal const& g, unsigned idx, obj_map<func_decl, sp_axioms>& goal_features);
    void insert(obj_map<func_decl, sp_axioms>& goal_features, func_decl* p, unsigned idx, sr_property p);

    bool is_transitivity(expr* fml, func_decl_ref& p);
    bool is_anti_symmetry(expr* fml, func_decl_ref& p);
    bool is_left_tree(expr* fml, func_decl_ref& p);
    bool is_right_tree(expr* fml, func_decl_ref& p);
    bool is_reflexivity(expr* fml, func_decl_ref& p);
    bool is_total(expr* fml, func_decl_ref& p);
    bool is_symmetric(expr* fml, func_decl_ref& p);

public:

    special_relations_tactic(ast_manager & m, params_ref const & ref = params_ref()) {}

    ~special_relations_tactic() override {}

    void updt_params(params_ref const & p) override { m_params = p; }
    
    void collect_param_descrs(param_descrs & r) override { }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;
    
    void cleanup() override {}

    tactic * translate(ast_manager & m) override { return alloc(special_relations_tactic, m, m_params); }

};

tactic * mk_special_relations_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("special_relations", "detect and replace by special relations.", "mk_special_relations_tactic(m, p)")
*/

#endif
