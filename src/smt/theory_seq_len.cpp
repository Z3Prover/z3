/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_seq_len.cpp

Abstract:

    Theory solver for sequence length constraints using partial axiom
    instantiation. See theory_seq_len.h for details.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#include "smt/theory_seq_len.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_seq_len::theory_seq_len(context& ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("seq")),
          m_util(ctx.get_manager()),
          m_autil(ctx.get_manager()) {}

    // -----------------------------------------------------------------------
    // Internalization
    // -----------------------------------------------------------------------

    bool theory_seq_len::internalize_atom(app* atom, bool /*gate_ctx*/) {
        expr* s = nullptr, *r = nullptr;

        // Handle (str.in_re s r): register a bool_var so assign_eh fires.
        if (m_util.str.is_in_re(atom, s, r)) {
            // Ensure the string argument has an enode.
            if (!ctx.e_internalized(s))
                ctx.internalize(s, false);
            if (!ctx.b_internalized(atom)) {
                bool_var bv = ctx.mk_bool_var(atom);
                ctx.set_var_theory(bv, get_id());
                ctx.mark_as_relevant(bv);
            }
            // Ensure the string has a theory variable so length is accessible.
            mk_var(ctx.get_enode(s));
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_seq_len::internalize_term(app* term) {
        // Internalize all children first.
        for (expr* arg : *term) {
            if (!ctx.e_internalized(arg))
                ctx.internalize(arg, false);
        }

        if (!ctx.e_internalized(term))
            ctx.mk_enode(term, false, false, true);

        enode* n = ctx.get_enode(term);
        if (!is_attached_to_var(n))
            mk_var(n);

        // If this is a seq.len term, assert non-negativity immediately.
        expr* inner = nullptr;
        if (m_util.str.is_length(term, inner))
            add_length_non_neg(inner);

        return true;
    }

    // -----------------------------------------------------------------------
    // assign_eh: fires when a bool_var (e.g. str.in_re) is assigned.
    // -----------------------------------------------------------------------

    void theory_seq_len::assign_eh(bool_var v, bool is_true) {
        if (!is_true)
            return; // only axiomatize positive memberships
        expr* e = ctx.bool_var2expr(v);
        expr* s = nullptr, *r = nullptr;
        if (!m_util.str.is_in_re(e, s, r))
            return;
        literal lit(v, false); // positive literal for the membership
        add_regex_length_axioms(s, r, lit);
    }

    // -----------------------------------------------------------------------
    // Model building
    // -----------------------------------------------------------------------

    void theory_seq_len::init_model(model_generator& mg) {
        mg.register_factory(alloc(seq_factory, m, get_family_id(), mg.get_model()));
    }

    // -----------------------------------------------------------------------
    // mk_fresh: create a copy of this theory for a fresh context.
    // -----------------------------------------------------------------------

    theory* theory_seq_len::mk_fresh(context* new_ctx) {
        return alloc(theory_seq_len, *new_ctx);
    }

    // -----------------------------------------------------------------------
    // display
    // -----------------------------------------------------------------------

    void theory_seq_len::display(std::ostream& out) const {
        out << "theory_seq_len\n";
    }

    // -----------------------------------------------------------------------
    // add_length_non_neg: assert (seq.len e) >= 0
    // -----------------------------------------------------------------------

    void theory_seq_len::add_length_non_neg(expr* e) {
        expr_ref len(m_util.str.mk_length(e), m);
        expr_ref ge0(m_autil.mk_ge(len, m_autil.mk_int(0)), m);
        if (!ctx.b_internalized(ge0))
            ctx.internalize(ge0, true);
        literal lit = ctx.get_literal(ge0);
        ctx.mark_as_relevant(lit);
        literal_vector lits;
        lits.push_back(lit);
        assert_axiom(lits);
    }

    // -----------------------------------------------------------------------
    // has_fixed_length: true when min_length(r) == max_length(r) < UINT_MAX
    // -----------------------------------------------------------------------

    bool theory_seq_len::has_fixed_length(expr* r, unsigned& len) const {
        unsigned mn = m_util.re.min_length(r);
        unsigned mx = m_util.re.max_length(r);
        if (mn == mx && mx != UINT_MAX) {
            len = mn;
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // get_length_arms
    //
    // Compute the semi-linear set of valid string lengths for the regex r.
    // Each returned arm represents one arithmetic progression:
    //   ∃ k_0,...,k_{n-1} ≥ 0 :  |s| = base + ∑ periods[i] * k_i
    //
    // Handles:
    //   - Fixed-length regexes (e.g. "abc", [a-z]{3}): single arm, no periods.
    //   - (R)* where R has fixed length n:  {0, n, 2n, ...}
    //   - (R)+ where R has fixed length n:  {n, 2n, 3n, ...}
    //   - (R){lo,hi} where R has fixed length n: lo*n + k*n, 0 ≤ k ≤ hi-lo
    //     (upper bound is handled separately by max_length; here we use period n)
    //   - (R){lo,} where R has fixed length n:  lo*n + k*n
    //   - (R)?  — two fixed arms: 0 and the body's constraint set
    //   - R1|R2 — union: arms(R1) ∪ arms(R2)          [NEW]
    //   - R1++R2 — Minkowski sum: for every pair (a1,a2) in arms(R1)×arms(R2)
    //              produce {base=a1.base+a2.base, periods=a1.periods++a2.periods}
    //              (capped at MAX_LEN_ARMS to avoid explosion)  [IMPROVED]
    //
    // Returns empty when no useful constraint can be extracted.
    // -----------------------------------------------------------------------

    theory_seq_len::len_arms theory_seq_len::get_length_arms(expr* r) const {
        len_arms result;
        expr* r1 = nullptr, *r2 = nullptr;
        unsigned lo = 0, hi = 0;

        // Empty regex: no string can match; handled upstream via conflict.
        if (m_util.re.is_empty(r))
            return result;

        // Full sequence: any length is possible — no useful constraint.
        if (m_util.re.is_full_seq(r))
            return result;

        // Fixed-length regex (min == max).
        {
            unsigned flen = 0;
            if (has_fixed_length(r, flen)) {
                result.push_back({flen, {}});
                return result;
            }
        }

        // (R)* where R has fixed length n:  lengths = {k*n : k ≥ 0}
        if (m_util.re.is_star(r, r1)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                result.push_back({0, {n}});
                return result;
            }
            // Body length not fixed — no constraint extracted.
            return result;
        }

        // (R)+ where R has fixed length n:  lengths = {n + k*n : k ≥ 0}
        if (m_util.re.is_plus(r, r1)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                result.push_back({n, {n}});
                return result;
            }
            return result;
        }

        // (R){lo,hi} where R has fixed length n
        if (m_util.re.is_loop(r, r1, lo, hi)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n)) {
                // Lengths ∈ {lo*n, (lo+1)*n, ..., hi*n}.
                // Represent as lo*n + k*n (k ≥ 0); the upper bound hi*n is
                // already asserted via max_length.
                svector<unsigned> periods;
                if (hi > lo && n > 0)
                    periods.push_back(n);
                result.push_back({lo * n, std::move(periods)});
                return result;
            }
            return result;
        }

        // (R){lo,} where R has fixed length n
        if (m_util.re.is_loop(r, r1, lo)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                result.push_back({lo * n, {n}});
                return result;
            }
            return result;
        }

        // (R)? — option: lengths are {0} ∪ lengths(R).
        // Handled as the union (R | ε) where ε has the single fixed arm {0,[]}.
        if (m_util.re.is_opt(r, r1)) {
            len_arms sub = get_length_arms(r1);
            if (sub.empty())
                return result;           // body unconstrained → union is too
            sub.push_back({0, {}});      // add the empty-string arm
            return sub;
        }

        // R1 | R2 — union: arms(R1) ∪ arms(R2).
        // If either side yields no arms (unconstrained), the whole union is
        // unconstrained too, so we return empty.
        if (m_util.re.is_union(r, r1, r2)) {
            len_arms arms1 = get_length_arms(r1);
            len_arms arms2 = get_length_arms(r2);
            if (arms1.empty() || arms2.empty())
                return result;
            result.append(arms1);
            result.append(arms2);
            return result;
        }

        // R1 ++ R2 — concatenation: Minkowski sum of the two sets.
        // For each pair of arms (a1, a2) the combined arm has
        //   base   = a1.base + a2.base
        //   periods = a1.periods ++ a2.periods   (fresh k_i for each entry)
        // This correctly handles different-period components, e.g.
        //   (aa)* ++ (bbb)*  →  |s| = 2*k1 + 3*k2,  k1,k2 ≥ 0.
        if (m_util.re.is_concat(r, r1, r2)) {
            len_arms arms1 = get_length_arms(r1);
            len_arms arms2 = get_length_arms(r2);
            if (arms1.empty() || arms2.empty())
                return result;
            for (const len_arm& a1 : arms1) {
                for (const len_arm& a2 : arms2) {
                    len_arm combined;
                    combined.base = a1.base + a2.base;
                    combined.periods.append(a1.periods);
                    combined.periods.append(a2.periods);
                    result.push_back(std::move(combined));
                    if (result.size() >= MAX_LEN_ARMS) {
                        TRACE(seq, tout << "seq_len: concat arm cap reached at "
                                        << MAX_LEN_ARMS << " arms\n";);
                        return result;  // cap — still sound, just less precise
                    }
                }
            }
            return result;
        }

        return result;   // no constraint extracted for other regex forms
    }

    // -----------------------------------------------------------------------
    // assert_one_arm
    //
    // Assert the existential encoding for one arm under a guard:
    //   cond_lit → ∃ k_0,...,k_{n-1} ≥ 0 : |s| = base + ∑ periods[i] * k_i
    //
    // Each k_i is a fresh Int skolem constant.  The implications are encoded
    // as two-literal clauses (¬cond_lit ∨ constraint).
    // -----------------------------------------------------------------------

    void theory_seq_len::assert_one_arm(expr* s, literal cond_lit, const len_arm& arm) {
        expr_ref len(m_util.str.mk_length(s), m);
        expr_ref_vector addends(m);
        if (arm.base > 0 || arm.periods.empty())
            addends.push_back(m_autil.mk_int(arm.base));

        for (unsigned p : arm.periods) {
            // Introduce a fresh non-negative integer variable.
            app_ref k(m.mk_fresh_const("_k_period_", m_autil.mk_int()), m);
            // cond_lit → k ≥ 0
            {
                literal_vector lits;
                lits.push_back(~cond_lit);
                lits.push_back(mk_literal(m_autil.mk_ge(k, m_autil.mk_int(0))));
                assert_axiom(lits);
            }
            addends.push_back(m_autil.mk_mul(m_autil.mk_int(p), k));
        }

        // Build the right-hand side: base + ∑ p_i * k_i
        expr_ref rhs(m);
        if (addends.empty())
            rhs = m_autil.mk_int(0);
        else if (addends.size() == 1)
            rhs = addends[0].get();
        else
            rhs = expr_ref(m_autil.mk_add(addends.size(), addends.data()), m);

        // cond_lit → |s| = rhs
        {
            literal_vector lits;
            lits.push_back(~cond_lit);
            lits.push_back(mk_literal(m.mk_eq(len, rhs)));
            assert_axiom(lits);
        }

        TRACE(seq, tout << "seq_len arm: cond=" << cond_lit
                        << " base=" << arm.base
                        << " #periods=" << arm.periods.size()
                        << " s=" << mk_pp(s, m) << "\n";);
    }

    // -----------------------------------------------------------------------
    // assert_len_arms
    //
    // Assert the disjunction of length arms under the membership literal:
    //   mem_lit → (arm_0 ∨ arm_1 ∨ ... ∨ arm_{n-1})
    //
    // Single arm: delegate directly to assert_one_arm (no guards needed).
    //
    // Multiple arms (union encoding):
    //   Introduce fresh guard Boolean g_i for each arm.
    //   Assert:  ¬mem_lit ∨ g_0 ∨ g_1 ∨ ...   (the disjunction selector)
    //   Assert:  g_i → arm_i constraints        (per-arm implications)
    //
    // The SAT/DPLL engine freely picks a guard; the arithmetic theory then
    // verifies (and if necessary refutes) the arithmetic constraints for that
    // arm, driving the search toward a consistent assignment.
    // -----------------------------------------------------------------------

    void theory_seq_len::assert_len_arms(expr* s, literal mem_lit, const len_arms& arms) {
        if (arms.empty())
            return;

        if (arms.size() == 1) {
            assert_one_arm(s, mem_lit, arms[0]);
            return;
        }

        // Multiple arms — introduce guard Booleans.
        literal_vector guard_lits;
        for (const len_arm& arm : arms) {
            app_ref g(m.mk_fresh_const("_len_guard_", m.mk_bool_sort()), m);
            bool_var bv = ctx.mk_bool_var(g);
            ctx.mark_as_relevant(bv);
            literal gl(bv, false);
            guard_lits.push_back(gl);
            assert_one_arm(s, gl, arm);    // gl → arm constraints
        }

        // mem_lit → g_0 ∨ g_1 ∨ ...
        literal_vector clause;
        clause.push_back(~mem_lit);
        for (literal g : guard_lits)
            clause.push_back(g);
        assert_axiom(clause);

        TRACE(seq, tout << "seq_len: union disjunction with "
                        << guard_lits.size() << " arms for s="
                        << mk_pp(s, m) << "\n";);
    }

    // -----------------------------------------------------------------------
    // add_regex_length_axioms
    // -----------------------------------------------------------------------

    void theory_seq_len::add_regex_length_axioms(expr* s, expr* r, literal lit) {
        expr_ref len(m_util.str.mk_length(s), m);

        // Always assert the minimum length constraint:
        // (s in R) => |s| >= min_length(R)
        unsigned min_len = m_util.re.min_length(r);
        if (min_len > 0) {
            expr_ref ge_min(m_autil.mk_ge(len, m_autil.mk_int(min_len)), m);
            if (!ctx.b_internalized(ge_min))
                ctx.internalize(ge_min, true);
            literal ge_min_lit = ctx.get_literal(ge_min);
            ctx.mark_as_relevant(ge_min_lit);
            literal_vector lits;
            lits.push_back(~lit);
            lits.push_back(ge_min_lit);
            assert_axiom(lits);
        }
        else {
            // At minimum assert non-negativity.
            add_length_non_neg(s);
        }

        // Assert maximum length constraint if finite:
        // (s in R) => |s| <= max_length(R)
        unsigned max_len = m_util.re.max_length(r);
        if (max_len != UINT_MAX) {
            expr_ref le_max(m_autil.mk_le(len, m_autil.mk_int(max_len)), m);
            if (!ctx.b_internalized(le_max))
                ctx.internalize(le_max, true);
            literal le_max_lit = ctx.get_literal(le_max);
            ctx.mark_as_relevant(le_max_lit);
            literal_vector lits;
            lits.push_back(~lit);
            lits.push_back(le_max_lit);
            assert_axiom(lits);
        }

        // Extract and assert the semi-linear length constraint.
        len_arms arms = get_length_arms(r);
        assert_len_arms(s, lit, arms);
    }

    // -----------------------------------------------------------------------
    // Helper: mk_literal
    // -----------------------------------------------------------------------

    literal theory_seq_len::mk_literal(expr* e) {
        if (!ctx.b_internalized(e))
            ctx.internalize(e, true);
        literal lit = ctx.get_literal(e);
        ctx.mark_as_relevant(lit);
        return lit;
    }

    // -----------------------------------------------------------------------
    // Helper: assert_axiom (th_axiom in the SMT context)
    // -----------------------------------------------------------------------

    void theory_seq_len::assert_axiom(literal_vector& lits) {
        // Skip if already satisfied.
        for (literal l : lits)
            if (ctx.get_assignment(l) == l_true)
                return;
        for (literal l : lits)
            ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
    }

}
