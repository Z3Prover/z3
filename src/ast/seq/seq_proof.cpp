/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_proof.cpp

Abstract:

    Owning snapshots of every intermediate sequence search state and
    conditional branch refutations, independent of the search trail.

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

    proof_tracker::proof_tracker(ast_manager& m) :
        m(m), u(m), m_proof(m), m_fact(m), m_root_state(m), m_context(m), m_reach_pin(m) {}

    void proof_tracker::reset() {
        m_stack.clear();
        m_proof = nullptr;
        m_fact = nullptr;
        m_root_state = nullptr;
        m_context.reset();
        m_reach_regex.reset();
        m_reach_pin.reset();
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

    expr_ref proof_tracker::reach_regex(mem_facet const& f, view const& v) {
        expr* cached = nullptr;
        if (m_reach_regex.find(v.m_state, v.m_target, cached))
            return expr_ref(cached, m);

        // Membership facets use the Brzozowski transition relation. The
        // target is an AST state identity, NOT its nullable language. Build
        // the language of paths to that exact state by GNFA elimination.
        auto reachable = f.live().reachable_live(v);
        expr_ref_vector states(m);
        obj_map<expr, unsigned> ids;
        for (expr* state : reachable) {
            ids.insert(state, states.size());
            states.push_back(state);
        }
        if (reachable.failed())
            throw default_exception("sequence proof: reach-view automaton could not be completed");

        sort* seq_sort = u.re.to_seq(v.m_state->get_sort());
        sort* re_sort = v.m_state->get_sort();
        expr_ref empty(u.re.mk_empty(re_sort), m);
        expr_ref empty_word(u.str.mk_empty(seq_sort), m);
        expr_ref epsilon(u.re.mk_to_re(empty_word), m);
        expr_ref result(empty);
        unsigned source = 0, target = 0;
        if (ids.find(v.m_state, source) && ids.find(v.m_target, target)) {
            unsigned count = states.size();
            // Two extra vertices keep the source and target intact while
            // eliminating all original states (including their loops).
            unsigned start = count, finish = count + 1, size = count + 2;
            vector<expr_ref_vector> edges;
            for (unsigned i = 0; i < size; ++i) {
                edges.push_back(expr_ref_vector(m));
                for (unsigned j = 0; j < size; ++j)
                    edges[i].push_back(empty);
            }
            edges[start].set(source, epsilon);
            edges[target].set(finish, epsilon);
            sort* elem_sort = nullptr;
            VERIFY(u.is_seq(seq_sort, elem_sort));
            symbol name("element");
            seq_rewriter& rw = f.get_rewriter();
            for (unsigned i = 0; i < count; ++i) {
                expr_ref_pair_vector cofactors(rw.get_derive().get_cached_cofactors(
                    transition_mode::brzozowski_tm, states.get(i)));
                for (auto const& [guard, next] : cofactors) {
                    unsigned j = 0;
                    if (!ids.find(next, j) || u.re.is_empty(next))
                        continue;
                    expr_ref predicate(m.mk_lambda(1, &elem_sort, &name, guard), m);
                    expr_ref label(u.re.mk_of_pred(predicate), m);
                    if (!u.re.is_empty(edges[i].get(j)))
                        label = u.re.mk_union(edges[i].get(j), label);
                    edges[i].set(j, label);
                }
            }
            for (unsigned k = 0; k < count; ++k) {
                if (!m.limit().inc())
                    throw default_exception("sequence proof: reach-view elimination canceled");
                expr_ref loop(epsilon);
                if (!u.re.is_empty(edges[k].get(k)))
                    loop = u.re.mk_star(edges[k].get(k));
                for (unsigned i = k + 1; i < size; ++i) {
                    if (u.re.is_empty(edges[i].get(k)))
                        continue;
                    expr_ref prefix(u.re.mk_concat(edges[i].get(k), loop), m);
                    for (unsigned j = k + 1; j < size; ++j) {
                        if (u.re.is_empty(edges[k].get(j)))
                            continue;
                        expr_ref path(u.re.mk_concat(prefix, edges[k].get(j)), m);
                        if (!u.re.is_empty(edges[i].get(j)))
                            path = u.re.mk_union(edges[i].get(j), path);
                        edges[i].set(j, path);
                    }
                }
            }
            result = edges[start].get(finish);
        }
        m_reach_pin.push_back(v.m_state);
        m_reach_pin.push_back(v.m_target);
        m_reach_pin.push_back(result);
        m_reach_regex.insert(v.m_state, v.m_target, result);
        return result;
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
                expr_ref regex(sm.m_view.m_state);
                if (sm.m_view.is_reach())
                    regex = reach_regex(*f, sm.m_view);
                sort* seq_sort = u.re.to_seq(regex->get_sort());
                expr_ref word(u.str.mk_concat(sm.m_str, seq_sort), m);
                expr_ref fact(u.re.mk_in_re(word, regex), m);
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

    expr_ref proof_tracker::snapshot(eq_tree::node const& n, bool include_conflict) {
        expr_ref_vector facts(m);
        for (unsigned id = 0; id < n.num_facets(); ++id)
            if (n.has_facet(id))
                append_facts(n.facet(id), facts);
        // Keep the actual conflict state alongside false, even if the
        // conflicting obligation was discharged during propagation.
        if (include_conflict && n.is_conflict()) {
            expr_ref conflict(m.mk_false(), m);
            facts.push_back(conflict);
        }
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
        if (m_stack.empty())
            m_root_state = state;
        m_stack.push_back(std::make_unique<frame>(m, state, rule));
        collect_context(n, *m_stack.back());
    }

    void proof_tracker::propagate(eq_tree::node const& n, char const* rule) {
        SASSERT(!m_stack.empty());
        frame& f = *m_stack.back();
        expr_ref after = snapshot(n, true);
        collect_context(n, f);
        // Newly observed external premises strengthen the theorem's
        // antecedent; they are never claimed to follow from the old state.
        expr_ref before = conditional_state(f.m_current, f.m_context);
        expr_ref transition(m.mk_implies(before, after), m);
        proof_ref lemma(u.mk_proof(symbol(rule ? rule : "seq-propagate"), 0, nullptr, transition), m);
        f.m_premises.push_back(lemma);
        f.m_current = after;
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
