/*++
Copyright (c) 2025 Microsoft Corporation

--*/


#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "qe/mbp/mbp_euf.h"
#include "qe/mbp/mbp_term_graph.h"

namespace mbp {
    euf_project_plugin::euf_project_plugin(ast_manager& m): project_plugin(m) {
        
    }

    euf_project_plugin::~euf_project_plugin() {

    }
    
    bool euf_project_plugin::project1(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return false;
    }
    
    family_id euf_project_plugin::get_family_id() {
        return basic_family_id;        
    }
    
    bool euf_project_plugin::operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return false;
    }
    
    bool euf_project_plugin::project(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) {
        if (vars.empty())
            return false;
        flatten_and(lits);
        expr_mark var_set;
        auto is_pure = [&](expr_mark& var_set, expr* v) {
            return all_of(subterms::all(expr_ref(v, m)), [&](expr* w) { return !var_set.is_marked(w); });
        };
        for (auto v : vars)
            var_set.mark(v, true);
        unsigned has_def = false;
#if 1
        // solve trivial equations
        for (auto e : lits) {
            expr* x = nullptr, *y = nullptr;
            if (m.is_eq(e, x, y) && var_set.is_marked(x) && is_pure(var_set, y)) {
                vars.erase(to_app(x));
                defs.push_back({ expr_ref(x, m), expr_ref(y, m) });
                has_def = true;
            }
            else if (m.is_eq(e, y, x) && var_set.is_marked(x) && is_pure(var_set, y)) {
                vars.erase(to_app(x));
                defs.push_back({ expr_ref(x, m), expr_ref(y, m) });
                has_def = true;
            }
        }
        if (has_def)
            return true;
#endif

        // check if there is a variable of uninterp sort
        if (all_of(vars, [&](expr* v) { return !m.is_uninterp(v->get_sort()); }))
            return has_def;

        term_graph tg(m);
        tg.add_lits(lits);
        for (auto v : vars) 
            if (m.is_uninterp(v->get_sort()))
                tg.add_var(v);

        //
        // now what:
        /// walk all subterms of lits.
        // push in partitions by value.
        // add equations from model
        // compute repr from tg.
        // 

        
        return has_def;
    }

}
