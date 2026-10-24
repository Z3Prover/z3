/*++
Copyright (c) 2026 Romain Soulat
--*/
#include "sat/smt/ff_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/ff/ff_evidence.h"
#include "params/smt_params_helper.hpp"

namespace ff_sat {
    struct proof_hint : euf::th_proof_hint {
        app *proof;
        explicit proof_hint(app *p) : proof(p) {}
        expr *get_hint(euf::solver &) const override {
            return proof;
        }
    };
    solver::solver(euf::solver &ctx)
        : th_euf_solver(ctx, symbol("finite-field"), ff_util(ctx.get_manager()).get_fid()), ff(m), proofs(m),
          domains(m) {}

    void solver::apply_sort_cnstr(euf::enode *n, sort *) {
        if (!is_attached_to_var(n)) {
            auto v = mk_var(n);
            ctx.attach_th_var(n, this, v);
        }
    }
    bool solver::visited(expr *e) {
        return expr2enode(e) != nullptr;
    }
    bool solver::visit(expr *e) {
        if (visited(e))
            return true;
        if (!ff.is_ff(e)) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }
    bool solver::post_visit(expr *e, bool, bool) {
        auto n = expr2enode(e);
        if (!n)
            n = mk_enode(e);
        if (ff.is_ff(e))
            apply_sort_cnstr(n, e->get_sort());
        return true;
    }
    void solver::internalize(expr *e) {
        visit_rec(m, e, false, false);
    }
    sat::literal solver::internalize(expr *e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto l = ctx.expr2literal(e);
        return sign ? ~l : l;
    }
    bool solver::split_domain(euf::enode *n) {
        expr *term = n->get_expr();
        auto prime = ff.modulus(term->get_sort());
        if (prime > rational(31) || m.is_value(term) ||
            std::find(domains.begin(), domains.end(), term) != domains.end())
            return false;
        expr_ref_vector premises(m);
        sat::literal_vector clause;
        for (unsigned i = 0; i < prime.get_unsigned(); ++i) {
            expr_ref eq(m.mk_eq(term, ff.mk_numeral(rational(i), term->get_sort())), m);
            premises.push_back(m.mk_not(eq));
        }
        app_ref evidence(m);
        proof_hint *hint = nullptr;
        if (ctx.use_drat()) {
            evidence = ff::record_refutation(m, premises, s().params());
            if (!evidence)
                return false;
            ctx.push(restore_vector(proofs));
            proofs.push_back(evidence);
            hint = new (get_region()) proof_hint(evidence);
        }
        for (expr *p : premises)
            clause.push_back(~ctx.internalize(p, false, false));
        ctx.push(restore_vector(domains));
        domains.push_back(term);
        add_clause(clause, hint);
        return true;
    }

    sat::check_result solver::check() {
        ++checks;
        values.reset();
        struct problem {
            ff::solver core;
            ptr_vector<euf::enode> terms;
            problem(ast_manager &m, sort *s, params_ref const &p, ff::ff_encoding_cache *c, ff::basis_cache *b)
                : core(m, s, p, c, b) {}
        };
        obj_map<sort, std::unique_ptr<problem>> problems;
        obj_hashtable<expr> assigned;
        auto get = [&](sort *s) -> problem & {
            auto &p = problems.insert_if_not_there(s, std::unique_ptr<problem>());
            if (!p) {
                auto &c = caches.insert_if_not_there(s, std::unique_ptr<ff::ff_encoding_cache>());
                if (!c)
                    c = std::make_unique<ff::ff_encoding_cache>(m, s);
                if (c->size() > 200000)
                    c->reset();
                p = std::make_unique<problem>(m, s, this->s().params(), c.get(), &basis);
            }
            return *p;
        };
        // Traverse the live e-graph: no assignment or enode survives in a shared
        // cache. Include non-relevant terms for model construction, but only
        // currently assigned equalities constrain their field values.
        for (auto n : ctx.get_egraph().nodes()) {
            expr *e = n->get_expr();
            if (ff.is_ff(e)) {
                auto &p = get(e->get_sort());
                p.terms.push_back(n);
                if (!n->is_root())
                    p.core.add(e, n->get_root()->get_expr(), true);
            }
            expr *a, *b;
            if (m.is_eq(e, a, b) && ff.is_ff(a)) {
                auto l = ctx.expr2literal(e);
                if (l != sat::null_literal && s().value(l) != l_undef) {
                    get(a->get_sort()).core.add(a, b, s().value(l) == l_true);
                    assigned.insert(e);
                }
            }
        }
        bool incomplete = false;
        for (auto &kv : problems) {
            auto &p = *kv.m_value;
            try {
                bool recording = ctx.use_drat();
                auto r = p.core.check(recording);
                if (r == l_undef) {
                    for (auto n : p.terms)
                        if (split_domain(n))
                            return sat::check_result::CR_CONTINUE;
                    // The native candidate search can be inconclusive for pure
                    // disequalities. Complete only with an explicit refutation.
                    if (p.core.refute())
                        r = l_false;
                    else {
                        incomplete = true;
                        continue;
                    }
                }
                if (r == l_false) {
                    sat::literal_vector clause;
                    for (auto i : p.core.conflict())
                        clause.push_back(~ctx.internalize(p.core.premise(i), false, false));
                    proof_hint *hint = nullptr;
                    if (recording) {
                        auto evidence = p.core.evidence();
                        if (!evidence) {
                            incomplete = true;
                            continue;
                        }
                        // Pin the replayable DAG for the lifetime of its scoped
                        // SAT proof hint. Equality premises are exact SAT atoms;
                        // the EUF proof layer discharges congruence separately.
                        ctx.push(restore_vector(proofs));
                        proofs.push_back(evidence);
                        hint = new (get_region()) proof_hint(evidence);
                    }
                    add_clause(clause, hint);
                    ++conflicts;
                    return sat::check_result::CR_CONTINUE;
                }
                std::map<rational, euf::enode *> representatives;
                for (auto n : p.terms) {
                    auto v = p.core.value(n->get_expr());
                    values.insert(n->get_expr(), v);
                    if (!ctx.is_shared(n))
                        continue;
                    auto [it, inserted] = representatives.emplace(v, n);
                    if (inserted || n->get_root() == it->second->get_root())
                        continue;
                    // This is a SAT choice, not a field consequence. A false
                    // equality becomes a disequality in the next field check.
                    auto l = eq_internalize(n, it->second);
                    ctx.mark_relevant(l);
                    if (s().value(l) == l_undef) {
                        ++arrangements;
                        return sat::check_result::CR_CONTINUE;
                    }
                    if (s().value(l) == l_false) {
                        // Internalization can immediately discover a disequality
                        // through congruence. Feed that new atom back to algebra.
                        if (!assigned.contains(ctx.bool_var2expr(l.var())))
                            return sat::check_result::CR_CONTINUE;
                        incomplete = true;
                    }
                }
            } catch (ff::exhausted const &) {
                if (!m.limit().is_canceled()) {
                    try {
                        for (auto n : p.terms)
                            if (split_domain(n))
                                return sat::check_result::CR_CONTINUE;
                    } catch (ff::exhausted const &) {
                    }
                }
                incomplete = true;
            }
        }
        return incomplete ? sat::check_result::CR_GIVEUP : sat::check_result::CR_DONE;
    }
    void solver::add_value(euf::enode *n, model &, expr_ref_vector &result) {
        rational v;
        if (!values.find(n->get_expr(), v) && !values.find(n->get_root()->get_expr(), v))
            throw default_exception("finite-field SAT/EUF candidate is unavailable");
        result.set(n->get_root_id(), ff.mk_numeral(v, n->get_sort()));
    }
    void solver::collect_statistics(statistics &st) const {
        st.update("ff euf checks", checks);
        st.update("ff euf conflicts", conflicts);
        st.update("ff euf arrangements", arrangements);
    }
}  // namespace ff_sat
