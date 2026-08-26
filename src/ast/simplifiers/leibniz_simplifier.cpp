/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    leibniz_simplifier.cpp

Abstract:

    see leibniz_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2024

--*/

#include "ast/simplifiers/leibniz_simplifier.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"

static bool contains_var_idx(expr* e, unsigned idx, expr_mark& seen) {
    ptr_vector<expr> todo;
    todo.push_back(e);
    while (!todo.empty()) {
        expr* n = todo.back();
        todo.pop_back();
        if (is_var(n)) {
            if (to_var(n)->get_idx() == idx)
                return true;
            continue;
        }
        if (seen.is_marked(n))
            continue;
        seen.mark(n, true);
        if (is_app(n))
            for (expr* arg : *to_app(n))
                todo.push_back(arg);
    }
    return false;
}

void leibniz_simplifier::collect_witnesses(expr* n, unsigned didx, sort* dom, ptr_vector<expr>& witnesses, expr_mark& seen) {
    ptr_vector<expr> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        expr* e = todo.back();
        todo.pop_back();
        if (seen.is_marked(e))
            continue;
        seen.mark(e, true);
        if (is_var(e))
            continue;
        if (m_array.is_select(e)) {
            app* a = to_app(e);
            expr* arr = a->get_arg(0);
            if (is_var(arr) && to_var(arr)->get_idx() == didx && a->get_num_args() == 2) {
                expr* arg = a->get_arg(1);
                // reject witnesses that mention the target variable itself
                // (the witness must be expressible outside the lambda body,
                // it may still depend on other bound vars in the enclosing
                // quantifier, which remain universally quantified around it).
                expr_mark seen2;
                if (arg->get_sort() == dom && witnesses.size() < m_config.m_max_witnesses &&
                    !contains_var_idx(arg, didx, seen2))
                    witnesses.push_back(arg);
            }
        }
        if (is_app(e))
            for (expr* arg : *to_app(e))
                todo.push_back(arg);
        // do not descend into nested quantifiers/lambdas: de Bruijn index
        // didx no longer refers to our target variable inside them.
    }
}

void leibniz_simplifier::try_instantiate(quantifier* q, dependent_expr const& de) {
    if (!is_forall(q))
        return;
    unsigned num_decls = q->get_num_decls();
    sort* bool_sort = m.mk_bool_sort();

    for (unsigned i = 0; i < num_decls; ++i) {
        sort* s = q->get_decl_sort(i);
        if (!m_array.is_array(s) || get_array_arity(s) != 1)
            continue;
        if (get_array_range(s) != bool_sort)
            continue;
        sort* dom = get_array_domain(s, 0);
        // de Bruijn index of decl i, within the body, using q's convention:
        // decl 0 corresponds to the highest index (num_decls - 1).
        unsigned didx = num_decls - i - 1;
        ptr_vector<expr> witnesses;
        expr_mark seen;
        collect_witnesses(q->get_expr(), didx, dom, witnesses, seen);
        if (witnesses.size() < 2)
            continue; // need at least two distinct use-sites to be interesting

        // build remap for the "outer" context (before insertion into
        // witness_pred's own lambda binder): decl j (j != i) moves from old
        // de Bruijn index (num_decls-j-1) to new index (new_num_decls-k-1),
        // shifted by 1 to sit inside the witness lambda's extra binder.
        unsigned new_num_decls = num_decls - 1;
        expr_ref_buffer remap(m);
        {
            unsigned k = 0;
            for (unsigned j = 0; j < num_decls; ++j) {
                if (j == i) {
                    remap.push_back(m.mk_var(0, dom)); // unused: witness excludes didx
                }
                else {
                    remap.push_back(m.mk_var(new_num_decls - k - 1 + 1, q->get_decl_sort(j)));
                    ++k;
                }
            }
        }
        var_subst remap_subst(m);

        for (expr* w : witnesses) {
            // witness predicate: \y:dom. (y = w), with w's free vars remapped
            // to the new (post-instantiation) quantifier context and shifted
            // by 1 to account for the witness's own lambda binder.
            expr_ref w_shifted = remap_subst(w, remap.size(), remap.data());
            var_ref y(m.mk_var(0, dom), m);
            expr_ref eq(m.mk_eq(y, w_shifted), m);
            symbol yn("y");
            expr_ref witness_pred(m.mk_lambda(1, &dom, &yn, eq), m);

            // build substitution: replace decl i by witness_pred (ground),
            // keep remaining decls as a forall with reindexed variables.
            // Decl j has de Bruijn index (num_decls - j - 1) in the body, and
            // var_subst's std order expects args[j] to be the substitution
            // for decl j (args[p] substitutes VAR index (num_decls-1-p)), so
            // we build args directly in declaration order, no reversal.
            ptr_vector<sort> new_sorts;
            svector<symbol> new_names;
            expr_ref_buffer args(m);
            unsigned k = 0;
            for (unsigned j = 0; j < num_decls; ++j) {
                if (j == i) {
                    args.push_back(witness_pred);
                }
                else {
                    new_sorts.push_back(q->get_decl_sort(j));
                    new_names.push_back(q->get_decl_name(j));
                    // new decl position k has de Bruijn index (new_num_decls - k - 1)
                    args.push_back(m.mk_var(new_num_decls - k - 1, q->get_decl_sort(j)));
                    ++k;
                }
            }

            var_subst subst(m);
            expr_ref new_body = subst(q->get_expr(), args.size(), args.data());

            expr_ref new_axiom(m);
            if (new_sorts.empty())
                new_axiom = new_body;
            else
                new_axiom = m.mk_quantifier(forall_k, new_sorts.size(), new_sorts.data(), new_names.data(), new_body);

            proof_ref pr(m);
            expr_ref simplified(m);
            m_rewriter(new_axiom, simplified, pr);
            if (m.is_true(simplified))
                continue;
            m_fmls.add(dependent_expr(m, simplified, nullptr, de.dep()));
            ++m_stats.m_num_instances;
        }
    }
}

void leibniz_simplifier::reduce() {
    unsigned n = std::min(m_config.m_max_quantifiers, qtail());
    for (unsigned idx = 0; idx < n; ++idx) {
        expr* f = m_fmls[idx].fml();
        if (!is_quantifier(f))
            continue;
        quantifier* q = to_quantifier(f);
        if (is_lambda(q))
            continue;
        if (m_processed.is_marked(q))
            continue;
        m_processed.mark(q, true);
        try_instantiate(q, m_fmls[idx]);
    }
}
