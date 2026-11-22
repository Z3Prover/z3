/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_proof.cpp

Abstract:

    Collect fact-level derivations stored by facets and close their
    conditional branch refutations independently of the search trail.

--*/

#include "ast/seq/seq_proof.h"
#include "ast/ast_util.h"
#include "ast/seq/seq_ho_facet.h"
#include "ast/seq/seq_lex_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_replace_all_facet.h"
#include "ast/seq/seq_req_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/seq/seq_stoi_facet.h"
#include "util/z3_exception.h"

namespace seq {

    proof_tracker::proof_tracker(ast_manager& m, proof_manager& dm) :
        m(m), u(m), m_dm(dm), m_proof(m), m_fact(m), m_root_state(m), m_context(m), m_pending(m), m_inputs(m) {
        dm.set_manager(m);
    }

    void proof_tracker::reset() {
        m_stack.clear();
        m_proof = nullptr;
        m_fact = nullptr;
        m_root_state = nullptr;
        m_context.reset();
        m_pending.reset();
        m_inputs.reset();
        m_dm.end_rule();
    }

    sort* proof_tracker::side_sort(expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
        if (!lhs.empty())
            return lhs.get(0)->get_sort();
        if (!rhs.empty())
            return rhs.get(0)->get_sort();
        // Empty token lists have lost their sort, but every sequence sort
        // gives the same truth value to these empty/empty obligations.
        return u.str.mk_string_sort();
    }

    void proof_tracker::append_equality(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                        bool equality, expr_ref_vector& facts) {
        sort* s = side_sort(lhs, rhs);
        expr_ref l(u.str.mk_concat(lhs, s), m);
        expr_ref r(u.str.mk_concat(rhs, s), m);
        expr_ref fact(m.mk_eq(l, r), m);
        if (!equality)
            fact = m.mk_not(fact);
        facts.push_back(fact);
    }

    void proof_tracker::append_facts(stx::facet_i const& facet, expr_ref_vector& facts) {
        if (auto* f = dynamic_cast<eq_facet const*>(&facet)) {
            for (auto const& e : f->equations())
                if (e.active())
                    append_equality(e.m_lhs, e.m_rhs, true, facts);
            for (auto const& s : f->substitutions()) {
                expr_ref rhs(u.str.mk_concat(s.m_repl, s.m_var->get_sort()), m);
                expr_ref fact(m.mk_eq(s.m_var, rhs), m);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<deq_facet const*>(&facet)) {
            for (auto const& e : f->disequations())
                if (e.active())
                    append_equality(e.m_lhs, e.m_rhs, false, facts);
        }
        else if (auto* f = dynamic_cast<mem_facet const*>(&facet)) {
            for (auto const& sm : f->memberships()) {
                if (!sm.active())
                    continue;
                expr_ref fact = sm.fact(u);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<ncontains_facet const*>(&facet)) {
            for (auto const& nc : f->ncontains()) {
                if (!nc.active())
                    continue;
                sort* s = side_sort(nc.m_haystack, nc.m_needle);
                expr_ref haystack(u.str.mk_concat(nc.m_haystack, s), m);
                expr_ref needle(u.str.mk_concat(nc.m_needle, s), m);
                expr_ref contains(u.str.mk_contains(haystack, needle), m);
                expr_ref fact(m.mk_not(contains), m);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<power_facet const*>(&facet)) {
            for (auto const& p : f->powers()) {
                if (!p.active())
                    continue;
                expr_ref power(u.str.mk_power(p.m_s, p.m_n), m);
                expr_ref fact(m.mk_eq(p.m_e, power), m);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<replace_all_facet const*>(&facet)) {
            for (auto const& ra : f->obligations()) {
                if (!ra.active())
                    continue;
                sort* s = ra.m_pattern->get_sort();
                expr_ref result(u.str.mk_concat(ra.m_result, s), m);
                expr_ref input(u.str.mk_concat(ra.m_input, s), m);
                expr_ref repl(u.str.mk_concat(ra.m_repl, s), m);
                expr_ref replacement(m.mk_app(u.get_family_id(), OP_SEQ_REPLACE_ALL,
                                             input, ra.m_pattern, repl), m);
                expr_ref fact(m.mk_eq(result, replacement), m);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<req_facet const*>(&facet)) {
            for (auto const& r : f->reqs()) {
                expr_ref fact(m.mk_eq(r.m_p, r.m_q), m);
                if (!r.m_is_eq)
                    fact = m.mk_not(fact);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<lex_facet const*>(&facet)) {
            for (auto const& lx : f->lexs()) {
                sort* s = side_sort(lx.m_lhs, lx.m_rhs);
                expr_ref lhs(u.str.mk_concat(lx.m_lhs, s), m);
                expr_ref rhs(u.str.mk_concat(lx.m_rhs, s), m);
                expr_ref fact(m);
                if (lx.m_strict)
                    fact = u.str.mk_lex_lt(lhs, rhs);
                else
                    fact = u.str.mk_lex_le(lhs, rhs);
                facts.push_back(fact);
            }
        }
        else if (auto* f = dynamic_cast<assumption_facet const*>(&facet)) {
            for (auto const& a : f->assumptions())
                facts.push_back(a.first);
        }
        else if (auto* f = dynamic_cast<solver_facet_i const*>(&facet))
            f->append_proof_facts(facts);
        else if (dynamic_cast<ho_facet const*>(&facet) || dynamic_cast<stoi_facet const*>(&facet)) {
            // These facets track coherence/axiom instantiation, not branch
            // obligations. Resulting equalities and constraints live above.
        }
        else
            throw default_exception("sequence proof: unsupported facet in state snapshot");
    }

    void proof_tracker::collect_proofs(eq_tree::node const& n, proof_ref_vector& proofs) {
        auto add = [&](proof* pr) { if (pr && !proofs.contains(pr)) proofs.push_back(pr); };
        for (unsigned id = 0; id < n.num_facets(); ++id) {
            if (!n.has_facet(id)) continue;
            auto const& facet = n.facet(id);
            if (auto* f = dynamic_cast<eq_facet const*>(&facet)) {
                for (auto const& e : f->equations()) if (e.active()) add(e.m_proof);
                for (auto const& s : f->substitutions()) add(s.m_proof);
            }
            else if (auto* f = dynamic_cast<deq_facet const*>(&facet)) {
                for (auto const& e : f->disequations()) if (e.active()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<mem_facet const*>(&facet)) {
                for (auto const& e : f->memberships()) if (e.active()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<ncontains_facet const*>(&facet)) {
                for (auto const& e : f->ncontains()) if (e.active()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<power_facet const*>(&facet)) {
                for (auto const& e : f->powers()) if (e.active()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<replace_all_facet const*>(&facet)) {
                for (auto const& e : f->obligations()) if (e.active()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<req_facet const*>(&facet)) {
                for (auto const& e : f->reqs()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<lex_facet const*>(&facet)) {
                for (auto const& e : f->lexs()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<assumption_facet const*>(&facet)) {
                for (auto const& e : f->assumptions()) add(e.m_proof);
            }
            else if (auto* f = dynamic_cast<solver_facet_i const*>(&facet))
                f->append_proofs(proofs);
        }
    }

    expr_ref proof_tracker::snapshot(eq_tree::node const& n) {
        expr_ref_vector facts(m);
        for (unsigned id = 0; id < n.num_facets(); ++id)
            if (n.has_facet(id))
                append_facts(n.facet(id), facts);
        if (facts.empty())
            return expr_ref(m.mk_true(), m);
        if (facts.size() == 1)
            return expr_ref(facts.get(0), m);
        return expr_ref(mk_and(facts), m);
    }

    void proof_tracker::append_context(expr_ref_vector const& src, expr_ref_vector& dst) {
        for (expr* fact : src)
            if (!dst.contains(fact))
                dst.push_back(fact);
    }

    expr_ref proof_tracker::conditional_state(expr* state, expr_ref_vector const& context) {
        if (context.empty())
            return expr_ref(state, m);
        expr_ref_vector facts(context);
        if (!facts.contains(state))
            facts.push_back(state);
        return expr_ref(mk_and(facts), m);
    }

    void proof_tracker::collect_context(eq_tree::node const& n, frame& f) {
        expr_ref_vector inputs(m);
        if (m_context_facts)
            m_context_facts(inputs);
        else if (n.ambient())
            throw default_exception("sequence proof: ambient input facts callback is required");
        append_context(inputs, f.m_context);
        append_context(inputs, m_context);
        m_fact = conditional_state(m_root_state, m_context);
    }

    void proof_tracker::begin(eq_tree::node const& n, char const* rule) {
        if (m_stack.empty())
            reset();
        expr_ref state = snapshot(n);
        if (m_stack.empty()) {
            m_root_state = state;
            collect_proofs(n, m_inputs);
        }
        m_stack.push_back(std::make_unique<frame>(m, state, rule));
        m_stack.back()->m_premises.append(m_pending);
        m_pending.reset();
        collect_context(n, *m_stack.back());
    }

    void proof_tracker::start_step(eq_tree::node const& n, char const* rule, bool branch) {
        SASSERT(!m_stack.empty());
        frame& f = *m_stack.back();
        collect_context(n, f);
        proof_ref_vector sources(m);
        collect_proofs(n, sources);
        for (expr* fact : f.m_context)
            sources.push_back(m.mk_hypothesis(fact));
        m_dm.begin_rule(symbol(rule ? rule : "seq-step"), branch, sources);
    }

    void proof_tracker::append_input_proofs(proof_ref_vector& proofs) const {
        proofs.append(m_inputs);
        for (expr* fact : m_context)
            proofs.push_back(m.mk_hypothesis(fact));
    }

    void proof_tracker::finish_step(eq_tree::node const& n, char const* rule, bool committed) {
        if (n.is_conflict()) {
            propagate(n, rule);
            return;
        }
        collect_context(n, *m_stack.back());
        if (committed) {
            m_pending.reset();
            m_pending.append(m_dm.generated());
        }
        m_dm.end_rule();
    }

    void proof_tracker::propagate(eq_tree::node const& n, char const* rule) {
        SASSERT(!m_stack.empty());
        frame& f = *m_stack.back();
        collect_context(n, f);
        if (n.is_conflict() && (m_dm.generated().empty() || !m.is_false(m.get_fact(m_dm.generated().back())))) {
            expr_ref fact(m.mk_false(), m);
            m_dm.mk_proof(symbol(rule ? rule : "seq-conflict"), fact, {nullptr});
        }
        f.m_premises.append(m_dm.generated());
        m_dm.end_rule();
    }

    void proof_tracker::end(eq_tree::node const& n, stx::search_result result) {
        SASSERT(!m_stack.empty());
        collect_context(n, *m_stack.back());
        std::unique_ptr<frame> f = std::move(m_stack.back());
        m_stack.pop_back();
        bool root = m_stack.empty();
        if (result != stx::search_result::unsat || !f->m_complete) {
            if (!root)
                m_stack.back()->m_complete = false;
            return;
        }
        expr_ref falsity(m.mk_false(), m);
        // A frame carries its own and all refuted children's external
        // premises outward. Branch-local facet states never enter this set.
        expr_ref initial = root ? expr_ref(m_fact) : conditional_state(f->m_initial, f->m_context);
        expr_ref conditional(m.mk_implies(initial, falsity), m);
        proof_ref closure(u.mk_proof(symbol(root ? "seq-search" : "seq-split"),
                                     f->m_premises, conditional), m);
        if (root)
            m_proof = closure;
        else {
            proof_ref_vector premises(m);
            premises.push_back(closure);
            symbol rule = f->m_incoming == symbol::null ? symbol("seq-branch") : f->m_incoming;
            proof_ref branch(u.mk_proof(rule, premises, conditional), m);
            m_stack.back()->m_premises.push_back(branch);
            append_context(f->m_context, m_stack.back()->m_context);
        }
    }

}
