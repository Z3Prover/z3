/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_finite_set.cpp

Abstract:

    Theory solver for finite sets.
    Implements axiom schemas for finite set operations.

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/

#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_finite_set::theory_finite_set(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("finite_set")),
        u(m),
        m_axioms(m)
    {
        // Setup the add_clause callback for axioms
        std::function<void(expr_ref_vector const &)> add_clause_fn = 
            [this](expr_ref_vector const& clause) {
                this->m_lemmas.push_back(clause);
            };
        m_axioms.set_add_clause(add_clause_fn);
    }

    bool theory_finite_set::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("finite_set", tout << "internalize_atom: " << mk_pp(atom, m) << "\n";);

        internalize_term(atom);
        
        // Track membership elements (set.in)
        expr* elem = nullptr, *set = nullptr;
        if (u.is_in(atom, elem, set)) {
            auto n = ctx.get_enode(elem);
            if (!m_elements.contains(n)) {
                m_elements.insert(n);
                ctx.push_trail(insert_obj_trail(n));
            }
        }
        
        return true;
    }

    bool theory_finite_set::internalize_term(app * term) {
        TRACE("finite_set", tout << "internalize_term: " << mk_pp(term, m) << "\n";);
        
        // Internalize all arguments first
        for (expr* arg : *term) 
            ctx.internalize(arg, false);
        
        // Create boolean variable for Boolean terms
        if (m.is_bool(term) && !ctx.b_internalized(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
        }
        
        // Create enode for the term if needed
        enode* e = nullptr;
        if (ctx.e_internalized(term)) 
            e = ctx.get_enode(term);         
        else 
            e = ctx.mk_enode(term, false, m.is_bool(term), true);        
        
        // Attach theory variable if this is a set
        if (!is_attached_to_var(e))             
            ctx.attach_th_var(e, this, mk_var(e));
                
        return true;
    }

    void theory_finite_set::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE("finite_set", tout << "new_eq_eh: v" << v1 << " = v" << v2 << "\n";);
        // When two sets are equal, propagate membership constraints
        // This is handled by congruence closure, so no additional work needed here
    }

    void theory_finite_set::new_diseq_eh(theory_var v1, theory_var v2) {
        TRACE("finite_set", tout << "new_diseq_eh: v" << v1 << " != v" << v2 << "\n";);
        // Disequalities could trigger extensionality axioms
        // For now, we rely on the final_check to handle this
    }

    final_check_status theory_finite_set::final_check_eh() {
        TRACE("finite_set", tout << "final_check_eh\n";);

        // walk all parents of elem in congruence table.
        // if a parent is of the form elem' in S u T, or similar.
        // create clauses for elem in S u T.

        expr* elem1 = nullptr, *set1 = nullptr;
        m_lemmas.reset();
        for (auto elem : m_elements) {
            for (auto p : enode::parents(elem)) {
                if (!u.is_in(p->get_expr(), elem1, set1)) 
                    continue;
                if (elem->get_root() != p->get_arg(0)->get_root())                    
                    continue; // elem is then equal to set1 but not elem1. This is a different case.
                for (auto sib : *p->get_arg(1))
                    instantiate_axioms(elem->get_expr(), sib->get_expr());
            }
        }
        if (instantiate_false_lemma())
            return FC_CONTINUE;
        if (instantiate_unit_propagation())
            return FC_CONTINUE;
        if (instantiate_free_lemma())
            return FC_CONTINUE;
        
        return FC_DONE;
    }

    void theory_finite_set::instantiate_axioms(expr* elem, expr* set) {
        TRACE("finite_set", tout << "instantiate_axioms: " << mk_pp(elem, m) << " in " << mk_pp(set, m) << "\n";);
        
        // Instantiate appropriate axiom based on set structure
        if (u.is_empty(set)) {
            m_axioms.in_empty_axiom(elem);
        }
        else if (u.is_singleton(set)) {
            m_axioms.in_singleton_axiom(elem, set);
        }
        else if (u.is_union(set)) {
            m_axioms.in_union_axiom(elem, set);
        }
        else if (u.is_intersect(set)) {
            m_axioms.in_intersect_axiom(elem, set);
        }
        else if (u.is_difference(set)) {
            m_axioms.in_difference_axiom(elem, set);
        }
        else if (u.is_range(set)) {
            m_axioms.in_range_axiom(elem, set);
        }
        else if (u.is_map(set)) {
            m_axioms.in_map_axiom(elem, set);
            m_axioms.in_map_image_axiom(elem, set);
        }
        else if (u.is_select(set)) {
            m_axioms.in_select_axiom(elem, set);
        }
        
        // Instantiate size axioms for singleton sets
        // TODO, such axioms don't belong here
        if (u.is_singleton(set)) {
            m_axioms.size_singleton_axiom(set);
        }
    }

    void theory_finite_set::add_clause(expr_ref_vector const& clause) {
        TRACE("finite_set", 
            tout << "add_clause: " << clause << "\n");
        
        // Convert expressions to literals and assert the clause
        literal_vector lits;
        for (expr* e : clause) {
            ctx.internalize(e, false);
            literal lit = ctx.get_literal(lit_expr);
            lits.push_back(lit);
        }
        
        if (!lits.empty()) {
            scoped_trace_stream _sts(*this, lits);
            ctx.mk_th_axiom(get_id(), lits);
        }
    }

    theory * theory_finite_set::mk_fresh(context * new_ctx) {
        return alloc(theory_finite_set, *new_ctx);
    }

    void theory_finite_set::display(std::ostream & out) const {
        out << "theory_finite_set:\n";
    }

    void theory_finite_set::init_model(model_generator & mg) {
        TRACE("finite_set", tout << "init_model\n";);
        // Model generation will use default interpretation for sets
        // The model will be constructed based on the membership literals that are true
    }

    model_value_proc * theory_finite_set::mk_value(enode * n, model_generator & mg) {
        TRACE("finite_set", tout << "mk_value: " << mk_pp(n->get_expr(), m) << "\n";);
        
        // For now, return nullptr to use default model construction
        // A complete implementation would construct explicit set values
        // based on true membership literals
        return nullptr;
    }

}  // namespace smt
