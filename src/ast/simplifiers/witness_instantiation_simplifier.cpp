/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    witness_instantiation_simplifier.cpp

Abstract:

    see witness_instantiation_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/

#include "ast/simplifiers/witness_instantiation_simplifier.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"

// walk every subterm (including under quantifiers, but there is nothing to
// gain by descending into non-ground contexts since only ground 0-ary
// applications are of interest) and record the sort of each ground 0-ary
// application (i.e., a ground constant), which is a witness that the sort
// already has some concrete value available for E-matching to use.
void witness_instantiation_simplifier::collect_ground_sorts(obj_hashtable<sort>& ground_sorts) {
    ast_mark visited;
    ptr_vector<expr> todo;
    for (unsigned idx : indices())
        todo.push_back(m_fmls[idx].fml());
    while (!todo.empty()) {
        expr* n = todo.back();
        todo.pop_back();
        if (visited.is_marked(n))
            continue;
        visited.mark(n, true);
        if (is_app(n)) {
            app* a = to_app(n);
            if (a->is_ground() && a->get_num_args() == 0)
                ground_sorts.insert(n->get_sort());
            for (expr* arg : *a)
                todo.push_back(arg);
        }
        else if (is_quantifier(n)) {
            todo.push_back(to_quantifier(n)->get_expr());
        }
    }
}

expr* witness_instantiation_simplifier::get_witness(sort* s) {
    expr* w = nullptr;
    if (m_witness.find(s, w))
        return w;
    app* c = m.mk_fresh_const("witness", s);
    m_pinned.push_back(c);
    m_witness.insert(s, c);
    ++m_stats.m_num_witnesses;
    return c;
}

// Remove declared variable at position `i` from quantifier q, substituting
// it with ground term `witness`, keeping the remaining declared variables
// quantified (reindexed). Returns the new body/quantifier.
static expr_ref remove_decl(ast_manager& m, quantifier* q, unsigned i, expr* witness) {
    unsigned num_decls = q->get_num_decls();
    unsigned new_num_decls = num_decls - 1;
    expr_ref_buffer args(m);
    ptr_vector<sort> new_sorts;
    svector<symbol> new_names;
    unsigned k = 0;
    for (unsigned j = 0; j < num_decls; ++j) {
        if (j == i) {
            args.push_back(witness);
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
    if (new_sorts.empty())
        return new_body;
    return expr_ref(m.mk_quantifier(forall_k, new_sorts.size(), new_sorts.data(), new_names.data(), new_body, q->get_weight()), m);
}

void witness_instantiation_simplifier::try_instantiate(quantifier* q, dependent_expr const& de, obj_hashtable<sort> const& ground_sorts) {
    if (!is_forall(q))
        return;
    unsigned num_decls = q->get_num_decls();
    for (unsigned i = 0; i < num_decls; ++i) {
        sort* s = q->get_decl_sort(i);
        if (!m.is_uninterp(s))
            continue;
        if (ground_sorts.contains(s))
            continue;
        expr* w = get_witness(s);
        expr_ref inst = remove_decl(m, q, i, w);
        proof_ref pr(m);
        expr_ref simplified(m);
        m_rewriter(inst, simplified, pr);
        if (m.is_true(simplified))
            continue;
        m_fmls.add(dependent_expr(m, simplified, nullptr, de.dep()));
    }
}

void witness_instantiation_simplifier::reduce() {
    obj_hashtable<sort> ground_sorts;
    collect_ground_sorts(ground_sorts);

    for (unsigned idx : indices()) {
        expr* f = m_fmls[idx].fml();
        if (!is_quantifier(f))
            continue;
        quantifier* q = to_quantifier(f);
        if (is_lambda(q))
            continue;
        try_instantiate(q, m_fmls[idx], ground_sorts);
    }
}
