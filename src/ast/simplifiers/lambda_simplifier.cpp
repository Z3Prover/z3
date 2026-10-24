/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    lambda_simplifier.cpp

Abstract:

    see lambda_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2024

--*/

#include "ast/simplifiers/lambda_simplifier.h"
#include "ast/occurs.h"
#include "util/uint_set.h"

void lambda_simplifier::collect_macros(obj_map<func_decl, expr*>& raw_defs,
                                        obj_map<func_decl, proof*>& raw_pr,
                                        obj_map<func_decl, unsigned>& def_idx,
                                        expr_ref_vector& pinned,
                                        proof_ref_vector& pinned_pr) {
    for (unsigned idx : indices()) {
        expr* f = m_fmls[idx].fml();
        expr* lhs = nullptr, * rhs = nullptr;
        if (!m.is_eq(f, lhs, rhs))
            continue;
        func_decl* c = nullptr;
        expr* l = nullptr;
        bool swapped = false;
        if (is_uninterp_const(lhs) && is_lambda(rhs)) {
            c = to_app(lhs)->get_decl();
            l = rhs;
        }
        else if (is_uninterp_const(rhs) && is_lambda(lhs)) {
            c = to_app(rhs)->get_decl();
            l = lhs;
            swapped = true;
        }
        else
            continue;
        if (m_fmls.frozen(c))
            continue;
        if (raw_defs.contains(c))
            continue; // multiple definitions of the same constant: keep neither as a macro (be conservative)
        if (occurs(c, l))
            continue; // self-referential definition, cannot be inlined
        pinned.push_back(l);
        raw_defs.insert(c, l);
        def_idx.insert(c, idx);
        // normalize the proof to always establish `(= c l)`, regardless of
        // which side `c` appeared on in the original assertion, so it can be
        // used uniformly as a demodulation antecedent.
        proof* pr = swapped ? m.mk_symmetry(m_fmls[idx].pr()) : m_fmls[idx].pr();
        if (pr)
            pinned_pr.push_back(pr);
        raw_pr.insert(c, pr);
    }
}

void lambda_simplifier::filter_by_occurrences(obj_map<func_decl, expr*>& raw_defs,
                                               obj_map<func_decl, unsigned>& def_idx) {
    if (raw_defs.empty())
        return;
    uint_set def_indices;
    for (auto const& kv : def_idx)
        def_indices.insert(kv.m_value);
    obj_map<func_decl, unsigned> occ_count;
    for (auto const& kv : raw_defs)
        occ_count.insert(kv.m_key, 0);
    for (unsigned idx : indices()) {
        if (def_indices.contains(idx))
            continue; // do not count the constant's own defining equality as a use
        expr* f = m_fmls[idx].fml();
        for (auto const& kv : raw_defs) {
            if (!occurs(kv.m_key, f))
                continue;
            unsigned cnt = 0;
            occ_count.find(kv.m_key, cnt);
            occ_count.insert(kv.m_key, cnt + 1);
        }
    }
    ptr_vector<func_decl> to_remove;
    for (auto const& kv : occ_count)
        if (kv.m_value > m_config.m_max_occs)
            to_remove.push_back(kv.m_key);
    for (func_decl* d : to_remove) {
        raw_defs.erase(d);
        def_idx.erase(d);
    }
}

expr* lambda_simplifier::resolve(func_decl* d,
                                  obj_map<func_decl, expr*> const& raw_defs,
                                  obj_map<func_decl, proof*> const& raw_pr,
                                  obj_map<func_decl, expr*>& resolved,
                                  obj_map<func_decl, proof*>& resolved_pr,
                                  obj_hashtable<func_decl>& in_progress,
                                  obj_hashtable<func_decl>& failed,
                                  expr_ref_vector& pinned,
                                  proof_ref_vector& pinned_pr) {
    expr* r = nullptr;
    if (resolved.find(d, r))
        return r;
    if (failed.contains(d))
        return nullptr;
    if (in_progress.contains(d)) {
        failed.insert(d);
        return nullptr;
    }
    in_progress.insert(d);
    expr* body = nullptr;
    raw_defs.find(d, body);
    expr_safe_replace sub(m);
    proof_ref_vector premises(m);
    bool any = false;
    for (auto const& kv : raw_defs) {
        func_decl* d2 = kv.m_key;
        if (d2 == d)
            continue;
        if (!occurs(d2, body))
            continue;
        expr* r2 = resolve(d2, raw_defs, raw_pr, resolved, resolved_pr, in_progress, failed, pinned, pinned_pr);
        if (!r2)
            continue;
        app_ref c2(m.mk_const(d2), m);
        pinned.push_back(c2);
        sub.insert(c2, r2);
        proof* pr2 = nullptr;
        resolved_pr.find(d2, pr2);
        premises.push_back(pr2);
        any = true;
    }
    expr_ref new_body(body, m);
    if (any) {
        sub(new_body);
        pinned.push_back(new_body);
    }
    in_progress.remove(d);
    if (failed.contains(d))
        return nullptr;
    resolved.insert(d, new_body);
    proof* pr0 = nullptr;
    raw_pr.find(d, pr0);
    proof* final_pr = pr0;
    if (any && new_body.get() != body) {
        // body = new_body by replacing each nested macro constant by its
        // (already resolved) definition; chain with `d`'s own defining
        // equation `d = body` to get `d = new_body`.
        proof* demod_pr = m.mk_demodulation(body, new_body.get(), premises.size(), premises.data());
        if (demod_pr)
            pinned_pr.push_back(demod_pr);
        final_pr = m.mk_transitivity(pr0, demod_pr);
    }
    if (final_pr)
        pinned_pr.push_back(final_pr);
    resolved_pr.insert(d, final_pr);
    return new_body;
}

void lambda_simplifier::reduce() {
    obj_map<func_decl, expr*> raw_defs;
    obj_map<func_decl, proof*> raw_pr;
    obj_map<func_decl, unsigned> def_idx;
    obj_map<func_decl, expr*> resolved;
    obj_map<func_decl, proof*> resolved_pr;
    obj_hashtable<func_decl> in_progress, failed;
    expr_ref_vector pinned(m);
    proof_ref_vector pinned_pr(m);

    collect_macros(raw_defs, raw_pr, def_idx, pinned, pinned_pr);

    if (raw_defs.empty())
        return;

    filter_by_occurrences(raw_defs, def_idx);

    if (raw_defs.empty())
        return;

    for (auto const& kv : raw_defs)
        resolve(kv.m_key, raw_defs, raw_pr, resolved, resolved_pr, in_progress, failed, pinned, pinned_pr);

    if (resolved.empty())
        return;

    m_stats.m_num_macros += resolved.size();

    expr_safe_replace sub(m);
    proof_ref_vector premises(m);
    for (auto const& kv : resolved) {
        app_ref c(m.mk_const(kv.m_key), m);
        pinned.push_back(c);
        sub.insert(c, kv.m_value);
        proof* pr = nullptr;
        resolved_pr.find(kv.m_key, pr);
        premises.push_back(pr);
    }

    uint_set def_indices;
    for (auto const& kv : resolved) {
        unsigned idx = 0;
        if (def_idx.find(kv.m_key, idx))
            def_indices.insert(idx);
    }

    for (unsigned idx : indices()) {
        auto d = m_fmls[idx];
        if (def_indices.contains(idx)) {
            // `d.pr()` already proves exactly `d.fml()` (the macro's own
            // defining equation, unresolved) -- collapsing it to `true` is
            // just `PR_IFF_TRUE` (`d.fml() <-> true`) composed with
            // modus-ponens against `d.pr()` itself, no demodulation needed
            // here. Note this does *not* use the resolved/transitive proof:
            // it is sound regardless of whether `d.fml()`'s own body still
            // mentions other macro constants, since the resolved body is
            // only needed when *using* this equation as a rewrite
            // antecedent elsewhere (below).
            m_fmls.update(idx, dependent_expr(m, m.mk_true(), mp(d.pr(), m.mk_iff_true(d.pr())), d.dep()));
            continue;
        }
        expr_ref new_fml(d.fml(), m);
        sub(new_fml);
        if (new_fml.get() == d.fml())
            continue;
        ++m_stats.m_num_substs;
        // `d.fml() = new_fml` by demodulation: replacing every occurrence of
        // each macro constant `c_k` by its (resolved) definition.
        proof_ref demod_pr(m.mk_demodulation(d.fml(), new_fml.get(), premises.size(), premises.data()), m);
        proof_ref new_pr(m);
        m_rewriter(new_fml, new_fml, new_pr);
        proof_ref combined(m.mk_transitivity(demod_pr.get(), new_pr.get()), m);
        m_fmls.update(idx, dependent_expr(m, new_fml, mp(d.pr(), combined.get()), d.dep()));
    }
}

