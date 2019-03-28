/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    special_relations_tactic.cpp

Abstract:

    Detect special relations in an axiomatization, 
    rewrite goal using special relations.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Notes:

--*/
#include "tactic/core/special_relations.h"

void special_relations_tactic::collect_feature(goal const& g, unsigned idx, 
                                               obj_map<func_decl, sp_axioms>& goal_features) {
    expr* f = g.form(idx);
    func_decl_ref p(m);
    if (is_transitivity(f, p)) {
        insert(goal_features, p, idx, sr_transitive);
    }
}

void specia_relations_tactic::insert(obj_map<func_decl, sp_axioms>& goal_features, func_decl* p, unsigned idx, sr_property p) {
    
}


bool special_relations_tactic::is_transitivity(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_anti_symmetry(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_left_tree(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_right_tree(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_reflexivity(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_total(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_symmetric(expr* fml, func_decl_ref& p) {
    return false;
}

    
void special_relations_tactic::operator()(goal_ref const & g, goal_ref_buffer & result) {
    tactic_report report("special_relations", g);
    obj_map<func_decl, sp_axioms> goal_features;
    unsigned size = g.size();
    for (unsigned idx = 0; idx < size; idx++) {
        collect_feature(g, idx, goal_features);
    }
    if (!goal_features.empty()) {
        
    }
    g->inc_depth();
    result.push_back(g.get());
}
    
