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
    // get_length_constraint: extract a semi-linear length constraint from r.
    //
    // On success, sets:
    //   period == 0: lengths in r are exactly {base}
    //   period > 0:  lengths in r are {base + k*period : k >= 0}
    //
    // Returns false if no useful constraint can be extracted.
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

    bool theory_seq_len::get_length_constraint(expr* r, unsigned& base, unsigned& period) const {
        expr* r1 = nullptr, *r2 = nullptr;
        unsigned lo = 0, hi = 0;

        // Empty regex: no string can match -> handled by conflict, not length.
        if (m_util.re.is_empty(r))
            return false;

        // Full sequence: any length is possible.
        if (m_util.re.is_full_seq(r))
            return false;

        // Fixed-length regex (min == max).
        {
            unsigned flen = 0;
            if (has_fixed_length(r, flen)) {
                base   = flen;
                period = 0;
                return true;
            }
        }

        // (R1)* where R1 has fixed length n: lengths = {k*n : k >= 0}
        if (m_util.re.is_star(r, r1)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                base   = 0;
                period = n;
                return true;
            }
            return false;
        }

        // (R1)+ where R1 has fixed length n: lengths = {k*n : k >= 1} = {n + k*n : k >= 0}
        if (m_util.re.is_plus(r, r1)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                base   = n;
                period = n;
                return true;
            }
            return false;
        }

        // Loop {lo, hi} where R1 has fixed length n:
        // lengths = {lo*n, (lo+1)*n, ..., hi*n} (a range, not necessarily simple period)
        // For now, just assert the lower bound as "base" and give min length as constraint.
        if (m_util.re.is_loop(r, r1, lo, hi)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n)) {
                // Lengths are exactly multiples of n between lo*n and hi*n.
                // We express this as a range: the constraint len = lo*n + k*n for 0<=k<=hi-lo.
                // Since our schema only handles one arithmetic progression, just use
                // base=lo*n, period=n (and an upper bound will be added separately).
                base   = lo * n;
                period = (hi > lo) ? n : 0;
                return true;
            }
            return false;
        }

        // Loop with lower bound only (no upper bound).
        if (m_util.re.is_loop(r, r1, lo)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n) && n > 0) {
                base   = lo * n;
                period = n;
                return true;
            }
            return false;
        }

        // Concatenation R1 ++ R2: if both parts have constraints, combine.
        if (m_util.re.is_concat(r, r1, r2)) {
            unsigned b1 = 0, p1 = 0, b2 = 0, p2 = 0;
            bool ok1 = get_length_constraint(r1, b1, p1);
            bool ok2 = get_length_constraint(r2, b2, p2);
            if (ok1 && ok2) {
                // If both are fixed length:
                if (p1 == 0 && p2 == 0) {
                    base   = b1 + b2;
                    period = 0;
                    return true;
                }
                // If one is fixed and the other periodic:
                if (p1 == 0) {
                    base   = b1 + b2;
                    period = p2;
                    return true;
                }
                if (p2 == 0) {
                    base   = b1 + b2;
                    period = p1;
                    return true;
                }
                // Both periodic: only combine if same period.
                if (p1 == p2) {
                    base   = b1 + b2;
                    period = p1;
                    return true;
                }
                // Incompatible periods: fall through.
            }
            // Partial: at least assert minimum length.
            return false;
        }

        // Option (R1)?: lengths = {0, n} where n is fixed length of R1.
        if (m_util.re.is_opt(r, r1)) {
            unsigned n = 0;
            if (has_fixed_length(r1, n)) {
                // lengths are 0 or n
                base   = 0;
                period = (n > 0) ? n : 0;
                return true;
            }
            return false;
        }

        return false;
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

        // Extract semi-linear length constraint.
        unsigned base = 0, period = 0;
        if (!get_length_constraint(r, base, period))
            return;

        if (period == 0) {
            // Fixed length: (s in R) => |s| = base
            expr_ref eq_base(m.mk_eq(len, m_autil.mk_int(base)), m);
            if (!ctx.b_internalized(eq_base))
                ctx.internalize(eq_base, true);
            literal eq_lit = ctx.get_literal(eq_base);
            ctx.mark_as_relevant(eq_lit);
            literal_vector lits;
            lits.push_back(~lit);
            lits.push_back(eq_lit);
            assert_axiom(lits);
        }
        else {
            // Semi-linear: lengths are {base + k * period : k >= 0}
            // Introduce a fresh variable (non-negative integer) and assert:
            //   (s in R) => |s| = base + period * k
            //   (s in R) => k >= 0
            // mk_fresh_const appends a unique numeric suffix, so each call
            // produces a distinct variable even with the same prefix.
            sort* int_sort = m_autil.mk_int();
            app* period_multiplier = m.mk_fresh_const("seq_len_k", int_sort, false);

            // k >= 0
            expr_ref x_ge0(m_autil.mk_ge(period_multiplier, m_autil.mk_int(0)), m);
            if (!ctx.b_internalized(x_ge0))
                ctx.internalize(x_ge0, true);
            literal x_ge0_lit = ctx.get_literal(x_ge0);
            ctx.mark_as_relevant(x_ge0_lit);
            {
                literal_vector lits;
                lits.push_back(~lit);
                lits.push_back(x_ge0_lit);
                assert_axiom(lits);
            }

            // |s| = base + period * k
            expr_ref period_times_x(m_autil.mk_mul(m_autil.mk_int(period), period_multiplier), m);
            expr_ref rhs(m_autil.mk_add(m_autil.mk_int(base), period_times_x), m);
            expr_ref eq_len(m.mk_eq(len, rhs), m);
            if (!ctx.b_internalized(eq_len))
                ctx.internalize(eq_len, true);
            literal eq_lit = ctx.get_literal(eq_len);
            ctx.mark_as_relevant(eq_lit);
            {
                literal_vector lits;
                lits.push_back(~lit);
                lits.push_back(eq_lit);
                assert_axiom(lits);
            }

            TRACE(seq, tout << "seq_len: (s in R) => |s| = " << base << " + "
                            << period << " * k for s=" << mk_pp(s, m)
                            << " r=" << mk_pp(r, m) << "\n";);
        }
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
