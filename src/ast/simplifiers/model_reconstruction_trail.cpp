/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    model_reconstruction_trail.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-3.
    
--*/


#include "ast/for_each_expr.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/macro_replacer.h"
#include "ast/simplifiers/model_reconstruction_trail.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/converters/generic_model_converter.h"


void model_reconstruction_trail::add_vars(expr* e, ast_mark& free_vars) {
    for (expr* t : subterms::all(expr_ref(e, m))) {
        if (is_app(t) && is_uninterp(t)) {            
            func_decl* f = to_app(t)->get_decl();
            TRACE("simplifier", tout << "add var " << f->get_name() << "\n");
            free_vars.mark(f, true);
            if (m_model_vars.is_marked(f))
                m_intersects_with_model = true;
        }
    }
}


// accumulate a set of dependent exprs, updating m_trail to exclude loose 
// substitutions that use variables from the dependent expressions.

void model_reconstruction_trail::replay(unsigned qhead, expr_ref_vector& assumptions, dependent_expr_state& st) {

    if (m_trail.empty())
        return;
    if (qhead == st.qtail())
        return;

    ast_mark free_vars;
    m_intersects_with_model = false;
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    for (unsigned i = qhead; i < st.qtail(); ++i)        
        add_vars(st[i], free_vars);
    for (expr* a : assumptions)
        add_vars(a, free_vars);

    TRACE("simplifier",
        tout << "intersects " << m_intersects_with_model << "\n";
        for (unsigned i = qhead; i < st.qtail(); ++i)
            tout << mk_bounded_pp(st[i].fml(), m) << "\n";
    );

    if (!m_intersects_with_model)
        return;

    for (auto& t : m_trail) {
        TRACE("simplifier", tout << " active " << t->m_active << " hide " << t->is_hide() << " intersects " << t->intersects(free_vars) << " loose " << t->is_loose() << "\n");
        if (!t->m_active)
            continue;

        if (t->is_hide())
            continue;
        
        // updates that have no intersections with current variables are skipped
        if (!t->intersects(free_vars)) 
            continue;    

        // loose entries that intersect with free vars are deleted from the trail
        // and their removed formulas are added to the resulting constraints.

        if (t->is_loose_subst()) {                
            for (auto const& [k, v] : t->m_subst->sub()) {
                add_vars(v, free_vars);
                st.add(dependent_expr(m, m.mk_eq(k, v), nullptr, nullptr));
            }
            t->m_active = false;
            continue;
        }
        
        if (t->is_loose_constraint()) {                
            for (auto r : t->m_removed) {
                add_vars(r, free_vars);
                TRACE("simplifier", tout << "replay removed " << r << "\n");
                st.add(r);
            }
            t->m_active = false;
            continue;
        }


        bool all_const = true;
        for (auto const& [d, def, dep] : t->m_defs) 
            all_const &= d->get_arity() == 0;

        if (t->is_loose() && (!t->is_def() || !all_const || t->is_subst())) {
            for (auto r : t->m_removed) {
                add_vars(r, free_vars);
                TRACE("simplifier", tout << "replay removed " << r << "\n");
                st.add(r);
            }
            m_trail_stack.push(value_trail(t->m_active));
            t->m_active = false;      
            continue;
        }        
        
        if (t->is_def()) {
            macro_replacer mrp(m);
            for (auto const& [d, def, dep] : t->m_defs) {
                app_ref head(m);
                ptr_buffer<expr> args;
                for (unsigned i = 0; i < d->get_arity(); ++i)
                    args.push_back(m.mk_var(i, d->get_domain(i)));
                head = m.mk_app(d, args);
                mrp.insert(head, def, dep);
                TRACE("simplifier", tout << mk_pp(d, m) << " " << mk_pp(def,m) << " " << "\n");
                dependent_expr de(m, def, nullptr, dep);
                add_vars(de, free_vars);
            }
            
            for (unsigned i = qhead; i < st.qtail(); ++i) {
                auto [f, p, dep1] = st[i]();
                expr_ref g(m);
                expr_dependency_ref dep2(m);
                mrp(f, dep1, g, dep2);
                CTRACE("simplifier", f != g, tout << "updated " << mk_pp(g, m) << "\n");
                if (f != g)
                    st.update(i, dependent_expr(m, g, nullptr, dep2));
            }
            for (unsigned i = 0; i < assumptions.size(); ++i) {
                expr* a = assumptions.get(i);
                expr_ref g(m);
                expr_dependency_ref dep(m);
                mrp(a, nullptr, g, dep);
                if (a != g)
                    assumptions[i] = g;
                // ignore dep.
            }
            if (t->is_loose()) {
                SASSERT(all_const);
                SASSERT(!t->is_subst());
                for (auto const& [d, def, dep] : t->m_defs) 
                    st.add(dependent_expr(m, m.mk_eq(m.mk_const(d), def), nullptr, nullptr));
            }
            continue;
        }

        rp->set_substitution(t->m_subst.get());
        // rigid entries:
        // apply substitution to added in case of rigid model convertions
        ptr_vector<expr> dep_exprs;
        expr_ref_vector trail(m);
        for (unsigned i = qhead; i < st.qtail(); ++i) {
            auto [f, p, dep1] = st[i]();
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
            dependent_expr d(m, g, nullptr, m.mk_join(dep1, dep2));
            CTRACE("simplifier", f != g, tout << "updated " << mk_pp(g, m) << "\n");
            add_vars(d, free_vars);
            st.update(i, d);
        }
        
        for (unsigned i = 0; i < assumptions.size(); ++i) {
            expr* a = assumptions.get(i);
            auto [g, dep2] = rp->replace_with_dep(a);
            if (a != g)
                assumptions[i] = g;
            // ignore dep.
        }        
    }

    TRACE("simplifier", st.display(tout));
}

/**
 * retrieve the current model converter corresponding to chaining substitutions from the trail.
 */
model_converter_ref model_reconstruction_trail::get_model_converter() {
    generic_model_converter_ref mc = alloc(generic_model_converter, m, "dependent-expr-model");
    append(*mc);
    return model_converter_ref(mc.get());
}

/**
* Append model conversions starting at index i
*/
void model_reconstruction_trail::append(generic_model_converter& mc) {
    for (auto* t : m_trail) {
        if (!t->m_active)
            continue;
        else if (t->is_hide())
            mc.hide(t->m_decl);
        else if (t->is_def())
            for (auto const& [f, def, dep] : t->m_defs)
                mc.add(f, def);
        else {
            for (auto const& [v, def] : t->m_subst->sub())
                mc.add(v, def);
        }
    }
    TRACE("simplifier", display(tout); mc.display(tout));
}



std::ostream& model_reconstruction_trail::display(std::ostream& out) const {
    for (auto* t : m_trail) {
        if (!t->m_active)
            continue;
        else if (t->is_hide())
            out << "hide " << t->m_decl->get_name() << "\n";
        else if (t->is_def()) {
            for (auto const& [f, def, dep] : t->m_defs)
                out << "def: " << f->get_name() << " <- " << mk_pp(def, m) << "\n";
        }            
        else {
            for (auto const& [v, def] : t->m_subst->sub())
                out << "sub: " << mk_pp(v, m) << " -> " << mk_pp(def, m) << "\n";
        }
        for (auto const& d : t->m_removed)
            out << "rm: " << d << "\n";
    }
    return out;
}
