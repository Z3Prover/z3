/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    demodulator_simplifier.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-12-4

--*/

#include "ast/simplifiers/demodulator_simplifier.h"
#include "ast/rewriter/var_subst.h"

demodulator_index::~demodulator_index() {
    reset();
}

void demodulator_index::reset() {
    for (auto& [k, v] : m_fwd_index)
        dealloc(v);
    for (auto& [k, v] : m_bwd_index)
        dealloc(v);
    m_fwd_index.reset();
    m_bwd_index.reset();
}

void demodulator_index::add(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map) {
    uint_set* s;
    if (!map.find(f, s)) {
        s = alloc(uint_set);
        map.insert(f, s);
    }
    s->insert(i);
}

void demodulator_index::del(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map) {
    uint_set* s;
    if (map.find(f, s))
        s->remove(i);
}

void demodulator_index::insert_bwd(expr* e, unsigned i) {
    struct proc {
        unsigned i;
        demodulator_index& idx;
        proc(unsigned i, demodulator_index& idx) :i(i), idx(idx) {}
        void operator()(app* a) {
            if (a->get_num_args() > 0 && is_uninterp(a))
                idx.add(a->get_decl(), i, idx.m_bwd_index);
        }
        void operator()(expr* e) {}
    };
    proc p(i, *this);
    for_each_expr(p, e);
}

void demodulator_index::remove_bwd(expr* e, unsigned i) {
    struct proc {
        unsigned i;
        demodulator_index& idx;
        proc(unsigned i, demodulator_index& idx) :i(i), idx(idx) {}
        void operator()(app* a) {
            if (a->get_num_args() > 0 && is_uninterp(a))
                idx.del(a->get_decl(), i, idx.m_bwd_index);
        }
        void operator()(expr* e) {}
    };
    proc p(i, *this);
    for_each_expr(p, e);
}

std::ostream& demodulator_index::display(std::ostream& out) const {
    out << "forward\n";
    for (auto& [k, v] : m_fwd_index)
        out << mk_pp(k, m) << " : " << *v << "\n";
    out << "backward\n";
    for (auto& [k, v] : m_bwd_index)
        out << mk_pp(k, m) << " : " << *v << "\n";
    return out;
}


demodulator_simplifier::demodulator_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& st):
    dependent_expr_simplifier(m, st),
    m_index(m),
    m_util(m),
    m_match_subst(m),
    m_rewriter(m),
    m_pinned(m),
    m_proof_pinned(m)
{
    std::function<bool(func_decl* f, expr_ref_vector const& args, expr_ref& r, proof_ref& pr)> rw =
        [&](func_decl* f, expr_ref_vector const& args, expr_ref& r, proof_ref& pr) {
        return rewrite1(f, args, r, pr);
    };
    m_rewriter.set_rewrite1(rw);
}

void demodulator_simplifier::rewrite(unsigned i) {
    if (m_index.empty())
        return;

    m_dependencies.reset();
    expr* f = fml(i);
    proof_ref step_pr(m);
    expr_ref r = m_rewriter.rewrite(f, step_pr);
    if (r == f)
        return;
    expr_dependency_ref d(dep(i), m);
    for (unsigned j : m_dependencies)
        d = m.mk_join(d, dep(j));
    proof_ref new_pr(m);
    if (m.proofs_enabled() && step_pr)
        new_pr = m.mk_modus_ponens(pr(i), step_pr);
    m_fmls.update(i, dependent_expr(m, r, new_pr, d));
}

/**
   \brief Justify a single demodulator rewrite step `f(args) = np`, where
   `np` was obtained by matching `f(args)` against demodulator `i`'s pattern
   and instantiating its (now ground) variables. Builds:
     qi_pr : (or (not q) qe[s])          -- via PR_QUANT_INST
     raw_pr: qe[s]                       -- via unit-resolution against q's own proof
   and, if `qe[s]` is not already syntactically `f(args) = np` (the
   demodulator may have been stored in reshaped form, e.g. with a `not`
   moved across the equation, or as a bare atom / negated atom rather than
   an explicit equation), bridges the two via a `PR_REWRITE` step (an
   elementary, independently side-condition-checked propositional identity)
   composed with modus ponens.

   Only attempted when every argument is ground: `f(args)` can otherwise
   occur nested inside another (outer) quantifier being demodulated, in
   which case the match binds the demodulator's variables to non-ground
   terms and there is no single ground quantifier instance that justifies
   the step; we then conservatively return nullptr (the term-level rewrite
   itself is unaffected, it simply isn't proof-tracked).
*/
proof* demodulator_simplifier::mk_instance_proof(unsigned i, func_decl* f, expr_ref_vector const& args, expr* np) {
    for (expr* a : args)
        if (!is_ground(a))
            return nullptr;

    expr* d_fml = fml(i);
    if (!is_forall(d_fml))
        return nullptr;
    quantifier* q = to_quantifier(d_fml);
    proof* q_pr = pr(i);
    if (!q_pr)
        return nullptr;

    unsigned n = q->get_num_decls();
    expr_ref_vector bindings(m);
    for (unsigned k = 0; k < n; ++k) {
        expr_ref b(m);
        if (!m_match_subst.get_binding(k, b) || !is_ground(b.get()))
            return nullptr;
        bindings.push_back(b);
    }

    var_subst vs(m, false);
    expr_ref qe_inst = vs(q->get_expr(), bindings.size(), bindings.data());

    expr_ref q_inst(m.mk_or(m.mk_not(q), qe_inst), m);
    proof_ref qi_pr(m.mk_quant_inst(q_inst, bindings.size(), bindings.data()), m);
    proof* prs[2] = { qi_pr.get(), q_pr };
    proof_ref raw_pr(m.mk_unit_resolution(2, prs), m);

    app_ref a(m.mk_app(f, args.size(), args.data()), m);
    expr_ref desired_inst(m.mk_eq(a, np), m);
    if (qe_inst.get() == desired_inst.get()) {
        // `raw_pr` is about to go out of scope; pin it so the object it
        // owns (refcount == 1) isn't deleted before the caller's
        // `proof_ref` can take ownership of the returned raw pointer.
        m_proof_pinned.push_back(raw_pr);
        return raw_pr.get();
    }

    proof_ref bridge(m.mk_rewrite(qe_inst, desired_inst), m);
    proof_ref result(m.mk_modus_ponens(raw_pr, bridge), m);
    m_proof_pinned.push_back(result);
    return result.get();
}

bool demodulator_simplifier::rewrite1(func_decl* f, expr_ref_vector const& args, expr_ref& np, proof_ref& pr) {
    uint_set* set;
    pr = nullptr;
    if (!m_index.find_fwd(f, set))
        return false;

    TRACE(demodulator, tout << "trying to rewrite: " << f->get_name() << " args:" << args << "\n"; m_index.display(tout));

    for (unsigned i : *set) {

        auto const& [lhs, rhs] = m_rewrites[i];

        TRACE(demodulator, tout << "Matching with demodulator: " << i << " " << mk_pp(lhs, m) << "\n");

        if (lhs->get_num_args() != args.size())
            continue;

        SASSERT(lhs->get_decl() == f);


        if (m_match_subst(lhs, rhs, args.data(), np)) {
            TRACE(demodulator_bug, tout << "succeeded...\n" << mk_pp(rhs, m) << "\n===>\n" << np << "\n");
            if (dep(i))
                m_dependencies.insert(i);
            if (m.proofs_enabled())
                pr = mk_instance_proof(i, f, args, np);
            return true;
        }
    }

    return false;
}

void demodulator_simplifier::reschedule_processed(func_decl* f) {
    uint_set* set = nullptr;
    if (!m_index.find_bwd(f, set))
        return;
    uint_set tmp;
    for (auto i : *set)
        if (m_processed.contains(i))
            tmp.insert(i);
    for (auto i : tmp) {
        m_processed.remove(i);
        m_index.remove_fwd(f, i);
        m_index.remove_bwd(fml(i), i);
        m_todo.push_back(i);
    }
}

void demodulator_simplifier::reschedule_demodulators(func_decl* f, expr* lhs) {
    uint_set* set;
    if (!m_index.find_bwd(f, set))
        return;
    uint_set all_occurrences(*set);
    for (unsigned i : all_occurrences) {
        app_expr_pair p;
        if (!m_rewrites.find(i, p))
            continue;        
        if (!m_match_subst.can_rewrite(fml(i), lhs))
            continue;
        SASSERT(f == p.first->get_decl());
        m_index.remove_fwd(f, i);
        m_index.remove_bwd(fml(i), i);
        m_todo.push_back(i);
    }
}

void demodulator_simplifier::reset() {
    m_pinned.reset();
    m_proof_pinned.reset();
    m_index.reset();
    m_rewrites.reset();
    m_processed.reset();
    m_todo.reset();
    unsigned max_vid = 1;
    for (unsigned i = 0; i < qtail(); ++i)
        max_vid = std::max(max_vid, m_util.max_var_id(fml(i)));
    m_match_subst.reserve(max_vid);
}

void demodulator_simplifier::reduce() {
    reset();
    for (unsigned i = 0; i < qhead(); ++i) {
        app_ref large(m);
        expr_ref small(m);
        if (!m_util.is_demodulator(fml(i), large, small))
            continue;
        m_index.insert_fwd(large->get_decl(), i);
        m_rewrites.insert(i, app_expr_pair(large, small));
        m_pinned.push_back(large);
        m_pinned.push_back(small);
    }
    for (unsigned i : indices())
        m_todo.push_back(i);

    app_ref large(m);
    expr_ref small(m);
    while (!m_todo.empty()) {
        unsigned i = m_todo.back();
        m_todo.pop_back();
        rewrite(i);
        if (m_util.is_demodulator(fml(i), large, small)) {
            func_decl* f = large->get_decl();
            TRACE(demodulator, tout << i << " " << mk_pp(fml(i), m) << ": " << large << " ==> " << small << "\n");
            reschedule_processed(f);
            reschedule_demodulators(f, large);
            m_index.insert_fwd(f, i);
            m_rewrites.insert(i, app_expr_pair(large, small));
            m_pinned.push_back(large);
            m_pinned.push_back(small);
        }
        else
            m_processed.insert(i);
        m_index.insert_bwd(fml(i), i);
    }
}
