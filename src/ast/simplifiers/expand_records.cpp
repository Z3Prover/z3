/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    expand_records.cpp

Abstract:

    See expand_records.h.

Author:

    Lev Nachmanson 2026-05

--*/

#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/expr_substitution.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/expand_records.h"


void expand_records_simplifier::reduce() {
    if (!m_enabled)
        return;

    m_fmls.freeze_suffix();

    // Collect candidate free constants.
    obj_hashtable<expr> seen_vars;
    ptr_vector<app>     vars;
    expr_mark           visited;

    auto visit = [&](expr* e) {
        if (!is_uninterp_const(e))
            return;
        if (seen_vars.contains(e))
            return;
        if (!is_expandable(e->get_sort()))
            return;
        // Skip frozen symbols (e.g., introduced by other simplifiers, or
        // symbols that other modules rely on being preserved verbatim).
        if (m_fmls.frozen(to_app(e)->get_decl()))
            return;
        seen_vars.insert(e);
        vars.push_back(to_app(e));
    };

    for (unsigned i : indices()) {
        for (expr* t : subterms::all(expr_ref(m_fmls[i].fml(), m), nullptr, &visited))
            visit(t);
    }

    if (vars.empty())
        return;

    // Build the substitution v -> (c v!f1 ... v!fn).
    scoped_ptr<expr_substitution> subst = alloc(expr_substitution, m);
    expr_ref_vector pinned(m);

    for (app* v : vars) {
        sort* s = v->get_sort();
        func_decl* ctor = m_dt.get_datatype_constructors(s)->get(0);
        auto const* accs = m_dt.get_constructor_accessors(ctor);
        expr_ref_vector args(m);
        std::string base = v->get_decl()->get_name().str();
        for (func_decl* acc : *accs) {
            std::string nm = base + "!" + acc->get_name().str();
            app* fresh = m.mk_fresh_const(nm.c_str(), acc->get_range());
            args.push_back(fresh);
        }
        expr_ref new_val(m.mk_app(ctor, args.size(), args.data()), m);
        pinned.push_back(new_val);
        subst->insert(v, new_val);
        TRACE(expand_records,
              tout << mk_pp(v, m) << " -> " << mk_pp(new_val, m) << "\n";);
    }

    // Apply the substitution and rewrite.
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    rp->set_substitution(subst.get());

    vector<dependent_expr> old_fmls;
    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        auto [g, dep2] = rp->replace_with_dep(f);
        expr_ref tmp(m);
        m_rewriter(g, tmp);
        if (tmp == f)
            continue;
        expr_dependency_ref new_dep(m.mk_join(d, dep2), m);
        old_fmls.push_back(m_fmls[i]);
        m_fmls.update(i, dependent_expr(m, tmp, nullptr, new_dep));
    }

    if (!old_fmls.empty())
        m_fmls.model_trail().push(subst.detach(), old_fmls, false);
}
