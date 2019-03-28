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
#include "tactic/core/special_relations_tactic.h"
#include "ast/rewriter/func_decl_replace.h"

void special_relations_tactic::collect_feature(goal const& g, unsigned idx, 
                                               obj_map<func_decl, sp_axioms>& goal_features) {
    expr* f = g.form(idx);
    func_decl_ref p(m);
    if (is_transitivity(f, p)) {
        insert(goal_features, p, idx, sr_transitive);
    }
    else if (is_anti_symmetry(f, p)) {
        insert(goal_features, p, idx, sr_antisymmetric);
    }
    else if (is_left_tree(f, p)) {
        insert(goal_features, p, idx, sr_lefttree);
    }
    else if (is_right_tree(f, p)) {
        insert(goal_features, p, idx, sr_righttree);
    }
    else if (is_reflexive(f, p)) {
        insert(goal_features, p, idx, sr_reflexive);
    }
    else if (is_total(f, p)) {
        insert(goal_features, p, idx, sr_total);
    }
}

void special_relations_tactic::insert(obj_map<func_decl, sp_axioms>& goal_features, func_decl* f, unsigned idx, sr_property p) {
    sp_axioms ax;
    goal_features.find(f, ax);
    ax.m_goal_indices.push_back(idx);
    ax.m_sp_features = (sr_property)(p | ax.m_sp_features);
    goal_features.insert(f, ax);
}


bool special_relations_tactic::is_transitivity(expr* fml, func_decl_ref& p) {
    // match Forall x, y, z . p(x,y) & p(y,z) -> p(x,z)
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
bool special_relations_tactic::is_reflexive(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_total(expr* fml, func_decl_ref& p) {
    return false;
}
bool special_relations_tactic::is_symmetric(expr* fml, func_decl_ref& p) {
    return false;
}

    
void special_relations_tactic::operator()(goal_ref const & g, goal_ref_buffer & result) {
    tactic_report report("special_relations", *g);
    obj_map<func_decl, sp_axioms> goal_features;
    unsigned size = g->size();
    for (unsigned idx = 0; idx < size; idx++) {
        collect_feature(*g, idx, goal_features);
    }
    special_relations_util u(m);
    func_decl_replace replace(m);
    unsigned_vector to_delete;
    for(auto const& kv : goal_features) {
        func_decl* sp = nullptr;
        sr_property feature = kv.m_value.m_sp_features;
        switch (feature) {
        case sr_po:
            replace.insert(kv.m_key, u.mk_po_decl(kv.m_key)); 
            to_delete.append(kv.m_value.m_goal_indices);
            break;
        case sr_to:
            replace.insert(kv.m_key, u.mk_to_decl(kv.m_key));                
            to_delete.append(kv.m_value.m_goal_indices);
            break;
        case sr_plo:
            replace.insert(kv.m_key, u.mk_plo_decl(kv.m_key));                
            to_delete.append(kv.m_value.m_goal_indices);
            break;
        case sr_lo:
            replace.insert(kv.m_key, u.mk_lo_decl(kv.m_key));                
            to_delete.append(kv.m_value.m_goal_indices);
            break;
        default:
            TRACE("special_relations", tout << "unprocessed feature " << feature << "\n";);
            break;
        }
    }
    if (!replace.empty()) {
        for (unsigned idx = 0; idx < size; idx++) {
            if (to_delete.contains(idx)) {
                g->update(idx, m.mk_true());
            }
            else {
                expr_ref new_f = replace(g->form(idx));
                g->update(idx, new_f);
            }
        }
        g->elim_true();
    }

    g->inc_depth();
    result.push_back(g.get());
}
    
tactic * mk_special_relations_tactic(ast_manager & m, params_ref const & p) {
    return alloc(special_relations_tactic, m, p);
}

