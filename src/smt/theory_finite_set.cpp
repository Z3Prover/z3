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
                this->add_clause(clause);
            };
        m_axioms.set_add_clause(add_clause_fn);
    }

    bool theory_finite_set::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("finite_set", tout << "internalize_atom: " << mk_pp(atom, m) << "\n";);
        
        // Internalize all arguments first
        for (expr* arg : *atom) {
            ctx.internalize(arg, false);
        }
        
        // Create boolean variable for the atom
        if (!ctx.b_internalized(atom)) {
            bool_var bv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }
        
        // Track membership atoms (set.in)
        if (u.is_in(atom)) {
            m_membership_atoms.insert(atom);
            expr* elem = atom->get_arg(0);
            expr* set = atom->get_arg(1);
            
            // Map set to its elements
            if (!m_set_to_elements.contains(set)) {
                m_set_to_elements.insert(set, ptr_vector<expr>());
            }
            ptr_vector<expr>& elems = m_set_to_elements[set];
            if (!elems.contains(elem)) {
                elems.push_back(elem);
            }
        }
        
        return true;
    }

    bool theory_finite_set::internalize_term(app * term) {
        TRACE("finite_set", tout << "internalize_term: " << mk_pp(term, m) << "\n";);
        
        // Internalize all arguments first
        for (expr* arg : *term) {
            ctx.internalize(arg, false);
        }
        
        // Create enode for the term if needed
        enode* e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        
        // Attach theory variable if this is a set
        if (u.is_finite_set(term) && !is_attached_to_var(e)) {
            theory_var v = mk_var(e);
            ctx.attach_th_var(e, this, v);
        }
        
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
        
        // Instantiate axioms for all membership atoms
        for (expr* atom : m_membership_atoms) {
            if (!u.is_in(atom))
                continue;
                
            app* in_app = to_app(atom);
            expr* elem = in_app->get_arg(0);
            expr* set = in_app->get_arg(1);
            
            // Get the root of the set in the congruence closure
            enode* set_node = ctx.get_enode(set);
            if (!set_node)
                continue;
            enode* set_root = set_node->get_root();
            expr* root_expr = set_root->get_expr();
            
            // Instantiate axioms based on the structure of the set
            instantiate_axioms(elem, root_expr);
        }
        
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
        if (u.is_singleton(set)) {
            m_axioms.size_singleton_axiom(set);
        }
    }

    void theory_finite_set::add_clause(expr_ref_vector const& clause) {
        TRACE("finite_set", 
            tout << "add_clause: ";
            for (expr* e : clause) {
                tout << mk_pp(e, m) << " ";
            }
            tout << "\n";
        );
        
        // Convert expressions to literals and assert the clause
        literal_vector lits;
        for (expr* e : clause) {
            expr_ref lit_expr(e, m);
            ctx.internalize(lit_expr, false);
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
        out << "  membership_atoms: " << m_membership_atoms.size() << "\n";
        out << "  sets tracked: " << m_set_to_elements.size() << "\n";
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
