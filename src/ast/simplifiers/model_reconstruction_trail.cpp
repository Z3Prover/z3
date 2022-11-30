/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    model_reconstruction_trail.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-3.
    
--*/


#include "ast/for_each_expr.h"
#include "ast/rewriter/macro_replacer.h"
#include "ast/simplifiers/model_reconstruction_trail.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/converters/generic_model_converter.h"


// accumulate a set of dependent exprs, updating m_trail to exclude loose 
// substitutions that use variables from the dependent expressions.
// TODO: add filters to skip sections of the trail that do not touch the current free variables.

void model_reconstruction_trail::replay(unsigned qhead, dependent_expr_state& st) {
    ast_mark free_vars;
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    for (unsigned i = qhead; i < st.qtail(); ++i) 
        add_vars(st[i], free_vars);

    for (auto& t : m_trail) {
        if (!t->m_active)
            continue;

        if (t->is_hide())
            continue;
        
        // updates that have no intersections with current variables are skipped
        if (!t->intersects(free_vars)) 
            continue;    

        // loose entries that intersect with free vars are deleted from the trail
        // and their removed formulas are added to the resulting constraints.
        if (t->is_loose()) {
            for (auto r : t->m_removed) {
                add_vars(r, free_vars);
                st.add(r);
            }
            m_trail_stack.push(value_trail(t->m_active));
            t->m_active = false;      
            continue;
        }        
        
        if (t->is_def()) {
            macro_replacer mrp(m);
            app_ref head(m);            
            func_decl* d = t->m_decl;
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < d->get_arity(); ++i)
                args.push_back(m.mk_var(i, d->get_domain(i)));
            head = m.mk_app(d, args);
            mrp.insert(head, t->m_def, t->m_dep);
            dependent_expr de(m, t->m_def, t->m_dep);
            add_vars(de, free_vars);

            for (unsigned i = qhead; i < st.qtail(); ++i) {
                auto [f, dep1] = st[i]();
                expr_ref g(m);
                expr_dependency_ref dep2(m);
                mrp(f, dep1, g, dep2);
                CTRACE("simplifier", f != g, tout << "updated " << mk_pp(g, m) << "\n");
                st.update(i, dependent_expr(m, g, dep2));
            }
            continue;
        }

        rp->set_substitution(t->m_subst.get());
        // rigid entries:
        // apply substitution to added in case of rigid model convertions
        ptr_vector<expr> dep_exprs;
        expr_ref_vector trail(m);
        for (unsigned i = qhead; i < st.qtail(); ++i) {
            auto [f, dep1] = st[i]();
            auto [g, dep2] = rp->replace_with_dep(f);
            if (dep1) {
                dep_exprs.reset();
                trail.reset();
                m.linearize(dep1, dep_exprs);                
                for (auto*& d : dep_exprs) {
                    auto [h, dep3] = rp->replace_with_dep(d);
                    if (h != d) {
                        trail.push_back(h);
                        d = h;
                        dep2 = m.mk_join(dep2, dep3);
                    }
                }
                if (!trail.empty()) 
                    dep1 = m.mk_join(dep_exprs.size(), dep_exprs.data());                
            }
            dependent_expr d(m, g, m.mk_join(dep1, dep2));
            CTRACE("simplifier", f != g, tout << "updated " << mk_pp(g, m) << "\n");
            add_vars(d, free_vars);
            st.update(i, d);
        }    
    }
}

/**
 * retrieve the current model converter corresponding to chaining substitutions from the trail.
 */
model_converter_ref model_reconstruction_trail::get_model_converter() {
    generic_model_converter_ref mc = alloc(generic_model_converter, m, "dependent-expr-model");
    unsigned i = 0;
    append(*mc, i);
    return model_converter_ref(mc.get());
}

/**
* Append model conversions starting at index i
*/
void model_reconstruction_trail::append(generic_model_converter& mc, unsigned& i) {
    for (; i < m_trail.size(); ++i) {
        auto* t = m_trail[i];
        if (!t->m_active)
            continue;
        else if (t->is_hide())
            mc.hide(t->m_decl);
        else if (t->is_def())
            mc.add(t->m_decl, t->m_def);
        else {
            for (auto const& [v, def] : t->m_subst->sub())
                mc.add(v, def);
        }
    }
}


void model_reconstruction_trail::append(generic_model_converter& mc) {
    m_trail_stack.push(value_trail(m_trail_index));
    append(mc, m_trail_index);
}

std::ostream& model_reconstruction_trail::display(std::ostream& out) const {
    for (auto* t : m_trail) {
        if (!t->m_active)
            continue;
        else if (t->is_hide())
            out << "hide " << t->m_decl->get_name() << "\n";
        else if (t->is_def())
            out << t->m_decl->get_name() << " <- " << mk_pp(t->m_def, m) << "\n";
        else {
            for (auto const& [v, def] : t->m_subst->sub())
                out << mk_pp(v, m) << " <- " << mk_pp(def, m) << "\n";
        }
    }
    return out;
}