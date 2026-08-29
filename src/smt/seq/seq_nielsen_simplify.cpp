/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_simplify.cpp

Abstract:

    Nielsen graph: nielsen_node::simplify_and_init and its passes --
    trivial-constraint removal, prefix/suffix cancellation, power
    normalisation and cross-side power cancellation (CommPower),
    derivative-based character consumption and regex widening.


Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    // true if `side` provably denotes a non-empty sequence: it contains a
    // token that is not eliminable by a var/power → ε substitution (concrete
    // characters, units, literals, …).  Single early-exit scan — a char is
    // itself non-eliminable, so the former separate has_char test was subsumed.
    // Iterates the tokens instead of materializing them: this is called per
    // equation/disequality on every simplification sweep.
    static bool side_cannot_be_empty(euf::snode const* side) {
        for (euf::snode const* t : *side) {
            if (!t->is_var() && !t->is_power())
                return true;
        }
        return false;
    }

    // Strip common leading and trailing tokens of (lhs, rhs).  Tokens equal
    // under m.are_equal cancel (equal tokens contribute equal lengths, so the
    // first differing position stays character-aligned); a pair of provably
    // distinct units at such a position stops the scan and reports a CLASH
    // instead — for an equality that is a symbol-clash conflict, for a
    // disequality it discharges the constraint.  Returns true on a clash;
    // otherwise rewrites lhs/rhs in place and sets `changed` if anything was
    // cancelled.
    static bool cancel_common_affixes(euf::sgraph& sg, ast_manager& m,
                                      euf::snode const*& lhs, euf::snode const*& rhs,
                                      bool& changed) {
        euf::snode_vector lhs_toks, rhs_toks;
        lhs->collect_tokens(lhs_toks);
        rhs->collect_tokens(rhs_toks);

        // --- prefix ---
        unsigned prefix = 0;
        while (prefix < lhs_toks.size() && prefix < rhs_toks.size()) {
            euf::snode const* lt = lhs_toks[prefix];
            euf::snode const* rt = rhs_toks[prefix];
            if (m.are_equal(lt->get_expr(), rt->get_expr()))
                ++prefix;
            else if (sg.are_unit_distinct(lt, rt))
                return true;
            else
                break;
        }

        // --- suffix (only among the tokens not already consumed by prefix) ---
        const unsigned lsz = lhs_toks.size(), rsz = rhs_toks.size();
        unsigned suffix = 0;
        while (suffix < lsz - prefix && suffix < rsz - prefix) {
            euf::snode const* lt = lhs_toks[lsz - 1 - suffix];
            euf::snode const* rt = rhs_toks[rsz - 1 - suffix];
            if (m.are_equal(lt->get_expr(), rt->get_expr()))
                ++suffix;
            else if (sg.are_unit_distinct(lt, rt))
                return true;
            else
                break;
        }

        if (prefix > 0 || suffix > 0) {
            lhs = sg.drop_left(sg.drop_right(lhs, suffix), prefix);
            rhs = sg.drop_left(sg.drop_right(rhs, suffix), prefix);
            changed = true;
        }
        return false;
    }

    // Right-derivative helper used by backward str_mem simplification:
    // dR(re, c) = reverse( derivative(c, reverse(re)) ).
    // Takes the caller's persistent rewriters (nielsen_graph::m_deriv_rw /
    // m_rw): this runs once per consumed suffix character, and constructing
    // a seq_rewriter + th_rewriter per call dominated the simplification cost.
    static euf::snode const* reverse_brzozowski_deriv(euf::sgraph &sg, seq_rewriter &rw, th_rewriter &tr,
                                                      euf::snode const* re, euf::snode const* elem) {
        if (!re || !elem || !re->get_expr() || !elem->get_expr())
            return nullptr;
        ast_manager &m = sg.get_manager();
        seq_util &seq = sg.get_seq_util();

        expr *elem_expr = elem->get_expr();
        expr *ch = nullptr;
        if (seq.str.is_unit(elem_expr, ch))
            elem_expr = ch;

        const expr_ref re_rev(seq.re.mk_reverse(re->get_expr()), m);
        const expr_ref d = rw.mk_derivative(elem_expr, re_rev);
        if (!d.get())
            return nullptr;
        expr_ref result(seq.re.mk_reverse(d), m);
        tr(result);
        return sg.mk(result);
    }

    // -----------------------------------------------------------------------
    // nielsen_node: simplify_and_init
    // -----------------------------------------------------------------------

    bool nielsen_node::check_empty_side_conflict(euf::snode const* non_empty_side,
                                                 dep_tracker const& dep) {
        if (side_cannot_be_empty(non_empty_side)) {
            set_simplify_conflict(backtrack_reason::symbol_clash, dep);
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Length-forced positional constant clash
    // -----------------------------------------------------------------------
    //
    // Both sides of `lhs = rhs` denote the SAME string, so a character position
    // can be measured from the left of that common string.  The offset of a
    // token is then a linear form over token lengths, and a concrete character
    // sits at a symbolic offset  P = sum_t c_t·|t| + k.  The equation supplies
    // one linear hypothesis for free:
    //
    //     Lv := |lhs| - |rhs| = 0.
    //
    // Two concrete characters a != b at offsets P and Q refute the node as soon
    // as Lv = 0 entails P = Q -- that is, as soon as P - Q lies in span{Lv}.
    //
    // Neither ingredient refutes on its own: length/Parikh reasoning never looks
    // at characters, and prefix/suffix cancellation only ever aligns the two
    // *ends* of the sides.  This rule aligns an INTERIOR position.
    //
    // Worked example --  y·2·z·1·x = x·2·z·1·x·2·z :
    //     Lv          = |y| - |x| - |z| - 1
    //     left  '2' at |y|
    //     right '1' at |x| + |z| + 1
    // the difference of the two offsets is exactly Lv, so the positions coincide
    // and 2 != 1 closes the node.  Note the length identity alone is perfectly
    // satisfiable here (|y| = |x|+|z|+1 has solutions), so no amount of integer
    // reasoning finds this on its own.
    //
    // Testing "P - Q in span{Lv}" pairwise is avoided by normalizing each offset
    // against a fixed pivot coordinate i0 of Lv:
    //
    //     canon(P) := Lv[i0]·P - P[i0]·Lv
    //
    // which is integral, zeroes coordinate i0, and applies the same scale factor
    // Lv[i0] to every offset -- so P == Q mod span{Lv} iff the canonical forms
    // agree.  When Lv is syntactically zero the normalization is the identity.
    //
    // Soundness note: a coordinate is keyed on the token's snode id, and a
    // token's length is a function of the term it denotes, so two occurrences
    // sharing an id do have equal length.  Distinct ids that happen to denote
    // equal lengths merely cost refutations, never soundness.
    bool nielsen_node::check_positional_clash() {
        if (!m_graph.m_positional_clash)
            return false;

        for (str_eq const& eq : m_str_eq) {
            if (eq.is_trivial())
                continue;

            euf::snode const* const sides[2] = { eq.m_lhs, eq.m_rhs };

            // Cheap pre-filter, before any allocation: the rule can only fire if
            // the equation carries at least two DISTINCT concrete characters.
            // This is what keeps it off the hot path -- most nodes never get
            // past here, and the scan below allocates per equation per node.
            {
                unsigned seen = UINT_MAX;
                bool distinct = false;
                for (euf::snode const* side : sides) {
                    for (euf::snode const* t : *side) {
                        if (!t->is_char())
                            continue;
                        if (seen == UINT_MAX)
                            seen = t->id();
                        else if (seen != t->id()) {
                            distinct = true;
                            break;
                        }
                    }
                    if (distinct)
                        break;
                }
                if (!distinct)
                    continue;
            }

            euf::snode_vector toks[2];
            eq.m_lhs->collect_tokens(toks[0]);
            eq.m_rhs->collect_tokens(toks[1]);

            // Pass 1: fix the coordinate system, one coordinate per distinct
            // token of unknown length.  Chars and units contribute a known 1.
            unsigned_vector atoms;
            unsigned nchars = 0;
            for (auto const& side : toks)
                for (euf::snode const* t : side) {
                    if (t->is_char())
                        ++nchars;
                    else if (!t->is_unit() && !atoms.contains(t->id()))
                        atoms.push_back(t->id());
                }

            // The scan below is quadratic in the character count, so a long
            // string literal would make a cheap refuter expensive on exactly
            // the nodes where it cannot fire.
            if (nchars > m_graph.m_positional_clash_limit)
                continue;

            const unsigned n = atoms.size();
            auto coord = [&](unsigned id) {
                for (unsigned i = 0; i < n; ++i)
                    if (atoms[i] == id)
                        return i;
                UNREACHABLE();
                return 0u;
            };

            // Pass 2: the offset of every concrete character, and Lv.
            vector<svector<int>> pc;     // coefficients of each character offset
            svector<int>         pk;     // constant term of each character offset
            unsigned_vector      pch;    // the character itself (snode id)
            svector<int>         lv;
            int                  lk = 0;
            lv.resize(n, 0);

            for (unsigned s = 0; s < 2; ++s) {
                const int sign = (s == 0) ? 1 : -1;
                svector<int> cur;
                int cur_k = 0;
                cur.resize(n, 0);
                for (euf::snode const* t : toks[s]) {
                    if (t->is_char()) {
                        pc.push_back(cur);
                        pk.push_back(cur_k);
                        pch.push_back(t->id());
                        ++cur_k;
                    }
                    else if (t->is_unit())
                        ++cur_k;            // length 1, character not concrete
                    else
                        ++cur[coord(t->id())];
                }
                for (unsigned i = 0; i < n; ++i)
                    lv[i] += sign * cur[i];
                lk += sign * cur_k;
            }

            unsigned pivot = n;
            for (unsigned i = 0; i < n; ++i)
                if (lv[i] != 0) {
                    pivot = i;
                    break;
                }

            // Lv has no variable part but a nonzero constant: the two sides can
            // never have equal length, so the equation is refuted outright.
            if (pivot == n && lk != 0) {
                set_simplify_conflict(backtrack_reason::symbol_clash, eq.m_dep);
                ++m_graph.m_stats.m_num_positional_clash;
                return true;
            }

            // Normalize every offset into the quotient by span{Lv}.
            const int64_t scale = (pivot == n) ? 1 : lv[pivot];
            vector<svector<int64_t>> cc;
            svector<int64_t>         ck;
            for (unsigned p = 0; p < pch.size(); ++p) {
                const int64_t f = (pivot == n) ? 0 : pc[p][pivot];
                svector<int64_t> row;
                row.resize(n, 0);
                for (unsigned i = 0; i < n; ++i)
                    row[i] = scale * pc[p][i] - f * lv[i];
                cc.push_back(row);
                ck.push_back(scale * pk[p] - f * lk);
            }

            // Any two differing characters forced onto the same position refute
            // the node -- including two positions of the same side, which the
            // length identity can just as well collapse onto each other.
            for (unsigned i = 0; i + 1 < pch.size(); ++i)
                for (unsigned j = i + 1; j < pch.size(); ++j) {
                    if (pch[i] == pch[j] || ck[i] != ck[j])
                        continue;
                    bool aligned = true;
                    for (unsigned c = 0; aligned && c < n; ++c)
                        aligned = cc[i][c] == cc[j][c];
                    if (!aligned)
                        continue;
                    TRACE(seq, tout << "positional clash " << eq_pp(eq) << "\n");
                    set_simplify_conflict(backtrack_reason::symbol_clash, eq.m_dep);
                    ++m_graph.m_stats.m_num_positional_clash;
                    return true;
                }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Power simplification helpers
    // -----------------------------------------------------------------------

    // Check if exponent b equals exponent a + diff for some rational constant diff.
    // Uses syntactic matching on Z3 expression structure: pointer equality
    // detects shared sub-expressions created during ConstNumUnwinding.
    //
    bool get_const_power_diff(expr* b, expr* a, arith_util& arith, rational& diff) {
        if (a == b) { diff = rational(0); return true; }
        expr* x = nullptr, *y = nullptr;
        rational val;
        // b = (+ a k) ?
        if (arith.is_add(b, x, y)) {
            if (x == a && arith.is_numeral(y, val)) { diff = val; return true; }
            if (y == a && arith.is_numeral(x, val)) { diff = val; return true; }
        }
        // a = (+ b k) → diff = -k
        if (arith.is_add(a, x, y)) {
            if (x == b && arith.is_numeral(y, val)) { diff = -val; return true; }
            if (y == b && arith.is_numeral(x, val)) { diff = -val; return true; }
        }
        // b = (- a k) → diff = -k
        if (arith.is_sub(b, x, y) && x == a && arith.is_numeral(y, val)) { diff = -val; return true; }
        // a = (- b k) → diff = k
        if (arith.is_sub(a, x, y) && x == b && arith.is_numeral(y, val)) { diff = val; return true; }
        return false;
    }

    // Merge adjacent tokens with the same power base on one side of an equation.
    // Handles: char(c) · power(c^e) → power(c^(e+1)),
    //          power(c^e) · char(c) → power(c^(e+1)),
    //          power(c^e1) · power(c^e2) → power(c^(e1+e2)).
    // Returns new snode if merging happened, nullptr otherwise.
    static euf::snode const* merge_adjacent_powers(euf::sgraph& sg, arith_util& arith, th_rewriter& rw,
                                                   euf::snode const* side) {
        if (!side || side->is_empty() || side->is_token())
            return nullptr;

        euf::snode_vector tokens;
        side->collect_tokens(tokens);
        if (tokens.size() < 2)
            return nullptr;

        ast_manager& m = sg.get_manager();
        seq_util& seq = sg.get_seq_util();

        // Directional peel guards.  Power unwinding peels one base copy to the
        // side's directional END: u · u^(n-1) at the front (fwd) or
        // u^(n-1) · u at the back (bwd).  Re-absorbing a char of the leading or
        // trailing char run into an adjacent power would re-roll the peel and
        // recreate the pre-peel node — an infinite peel/merge cycle (the child
        // becomes string-identical to its parent, differing only in the n >= 1
        // side constraint, so the sibling loop-cut fires on a loop that makes
        // no progress).  Chars strictly inside the token list (bounded by a
        // non-char token on both sides) can never be peel artifacts and merge
        // freely.
        unsigned lead_end = 0;
        while (lead_end < tokens.size() && tokens[lead_end]->is_char())
            ++lead_end;
        unsigned trail_start = tokens.size();
        while (trail_start > lead_end && tokens[trail_start - 1]->is_char())
            --trail_start;

        bool merged = false;
        euf::snode_vector result;

        unsigned i = 0;
        while (i < tokens.size()) {
            euf::snode const* tok = tokens[i];

            // Case 1: current is a power token — absorb following same-base tokens.
            // Skip at leading position (i == 0) to keep exponents small: CommPower
            // cross-side cancellation works better with unmerged leading powers
            // (e.g., w^k trivially ≤ 1+k, but w^(2k) vs 1+k requires k ≥ 1).
            if (tok->is_power() && i > 0) {
                expr* base_e = get_power_base_expr(tok, seq);
                expr* exp_acc = get_power_exp_expr(tok, seq);
                if (!base_e || !exp_acc) { result.push_back(tok); ++i; continue; }

                bool local_merged = false;
                unsigned j = i + 1;
                while (j < tokens.size()) {
                    euf::snode const* next = tokens[j];
                    if (next->is_power()) {
                        const expr * nb = get_power_base_expr(next, seq);
                        if (nb == base_e) {
                            exp_acc = arith.mk_add(exp_acc, get_power_exp_expr(next, seq));
                            local_merged = true; ++j; continue;
                        }
                    }
                    // chars of the trailing run are excluded: absorbing them
                    // would undo a backward peel (see peel guards above)
                    if (j < trail_start && next->is_char() && next->get_expr() == base_e) {
                        exp_acc = arith.mk_add(exp_acc, arith.mk_int(1));
                        local_merged = true; ++j; continue;
                    }
                    break;
                }
                if (local_merged) {
                    merged = true;
                    expr_ref norm_exp = normalize_arith(rw, exp_acc);
                    expr_ref new_pow(seq.str.mk_power(base_e, norm_exp), m);
                    result.push_back(sg.mk(new_pow));
                }
                else
                    result.push_back(tok);
                i = j;
                continue;
            }

            // Case 2: current is a char — check if next is a same-base power.
            // Skip chars of the LEADING run (not just i == 0) to avoid undoing
            // forward power unwinding: a peel produces u · u^(n-1) and repeated
            // peels u · u · u^(n-2) …; merging any of the run back into the
            // power re-creates the pre-peel node (infinite cycle).
            if (i >= lead_end && tok->is_char() && tok->get_expr() && i + 1 < tokens.size()) {
                euf::snode const* next = tokens[i + 1];
                if (next->is_power() && get_power_base_expr(next, seq) == tok->get_expr()) {
                    expr* base_e = tok->get_expr();
                    // Use same arg order as Case 1: add(exp, 1), not add(1, exp),
                    // so that merging "c · c^e" and "c^e · c" both produce add(e, 1)
                    // and the resulting power expression is hash-consed identically.
                    expr* exp_acc = arith.mk_add(get_power_exp_expr(next, seq), arith.mk_int(1));
                    unsigned j = i + 2;
                    while (j < tokens.size()) {
                        euf::snode const* further = tokens[j];
                        if (further->is_power() && get_power_base_expr(further, seq) == base_e) {
                            exp_acc = arith.mk_add(exp_acc, get_power_exp_expr(further, seq));
                            ++j; continue;
                        }
                        // trailing-run chars excluded (backward peel guard)
                        if (j < trail_start && further->is_char() && further->get_expr() == base_e) {
                            exp_acc = arith.mk_add(exp_acc, arith.mk_int(1));
                            ++j; continue;
                        }
                        break;
                    }
                    merged = true;
                    expr_ref norm_exp = normalize_arith(rw, exp_acc);
                    expr_ref new_pow(seq.str.mk_power(base_e, norm_exp), m);
                    result.push_back(sg.mk(new_pow));
                    i = j;
                    continue;
                }
            }

            result.push_back(tok);
            ++i;
        }

        if (!merged)
            return nullptr;

        euf::snode const* rebuilt = nullptr;
        for (const auto tok : result)
            rebuilt = rebuilt ? sg.mk_concat(rebuilt, tok) : tok;
        if (!rebuilt)
            rebuilt = sg.mk_empty_seq(side->get_sort());
        return rebuilt;
    }

    // Simplify constant-exponent powers: base^0 → ε, base^1 → base.
    // Returns new snode if any simplification happened, nullptr otherwise.
    static euf::snode const* simplify_const_powers(nielsen_node* node, euf::sgraph& sg, euf::snode const* side, dep_tracker& dep) {
        dep = nullptr;
        SASSERT(side);
        if (side->is_empty())
            return nullptr;

        euf::snode_vector tokens;
        side->collect_tokens(tokens);

        seq_util& seq = sg.get_seq_util();

        bool simplified = false;
        euf::snode_vector result;

        for (euf::snode const* tok : tokens) {
            if (tok->is_power()) {
                expr* exp_e = get_power_exp_expr(tok, seq);
                rational ub;
                dep_tracker ub_dep = nullptr;
                if (exp_e && node->upper_bound(exp_e, ub, ub_dep)) {
                    if (ub.is_zero()) {
                        // base^0 → ε (skip this token entirely)
                        dep = node->graph().dep_mgr().mk_join(dep, ub_dep);
                        simplified = true;
                        continue;
                    }
                    if (ub.is_one()) {
                        // base^1 → base — only sound when the exponent is exactly 1.
                        // An upper bound of 1 alone still admits n = 0 (u^0 = ε), so
                        // also require a lower bound >= 1 before rewriting.
                        rational lb;
                        dep_tracker lb_dep = nullptr;
                        if (node->lower_bound(exp_e, lb, lb_dep) && lb.is_pos()) {
                            euf::snode const* base_sn = tok->arg0();
                            if (base_sn) {
                                dep = node->graph().dep_mgr().mk_join(dep, ub_dep);
                                dep = node->graph().dep_mgr().mk_join(dep, lb_dep);
                                result.push_back(base_sn);
                                simplified = true;
                                continue;
                            }
                        }
                    }
                }
            }
            result.push_back(tok);
        }

        if (!simplified)
            return nullptr;

        euf::snode const* rebuilt = nullptr;
        for (euf::snode const* tok : result) {
            rebuilt = rebuilt ? sg.mk_concat(rebuilt, tok) : tok;
        }
        if (!rebuilt)
            rebuilt = sg.mk_empty_seq(side->get_sort());
        return rebuilt;
    }

    // Shared per-constraint side simplification, used for equalities and
    // disequalities alike: constant-exponent power rewriting (base^0 → ε,
    // base^1 → base) on both sides followed by common prefix/suffix
    // cancellation.  Bound dependencies used by the power rewriting are joined
    // into `dep`; `changed` is set when anything was rewritten.  Returns true
    // when an aligned, provably-distinct unit pair was found — a symbol clash,
    // which refutes an equality and discharges a disequality.
    static bool simplify_side_pair(nielsen_node* node, euf::sgraph& sg,
                                   euf::snode const*& lhs, euf::snode const*& rhs,
                                   dep_tracker& dep, bool& changed) {
        dep_manager& dm = node->graph().dep_mgr();
        dep_tracker pow_dep = nullptr;
        if (euf::snode const* s = simplify_const_powers(node, sg, lhs, pow_dep)) {
            lhs = s;
            dep = dm.mk_join(dep, pow_dep);
            changed = true;
        }
        pow_dep = nullptr;
        if (euf::snode const* s = simplify_const_powers(node, sg, rhs, pow_dep)) {
            rhs = s;
            dep = dm.mk_join(dep, pow_dep);
            changed = true;
        }
        return cancel_common_affixes(sg, sg.get_manager(), lhs, rhs, changed);
    }

    // CommPower: count how many times a power's base pattern appears in
    // the directional prefix of the other side (fwd=true: left prefix,
    // fwd=false: right suffix).
    // Returns (count_expr, num_tokens_consumed).  count_expr is nullptr
    // when no complete base-pattern match is found.
    std::pair<expr_ref, unsigned> comm_power(
            euf::snode const* base_sn, euf::snode const* side, ast_manager& m, arith_util& arith,
            seq_util& seq, const bool fwd) {
        euf::snode_vector base_tokens, side_tokens;
        collect_tokens_dir(base_sn, fwd, base_tokens);
        collect_tokens_dir(side, fwd, side_tokens);
        if (base_tokens.empty() || side_tokens.empty())
            return {expr_ref(nullptr, m), 0};

        expr* sum = nullptr;
        unsigned pos = 0;
        expr* last_stable_sum = nullptr;
        unsigned last_stable_idx = 0;

        unsigned i = 0;
        for (; i < side_tokens.size(); i++) {
            euf::snode const* t = side_tokens[i];
            if (pos == 0) {
                last_stable_idx = i;
                last_stable_sum = sum;
            }
            // Case 1: direct token match with base pattern
            if (pos < base_tokens.size() && t == base_tokens[pos]) {
                pos++;
                if (pos >= base_tokens.size()) {
                    pos = 0;
                    sum = sum ? arith.mk_add(sum, arith.mk_int(1))
                              : arith.mk_int(1);
                }
                continue;
            }
            // Case 2: power token whose base matches our base pattern — ONLY at a
            // pattern boundary (pos == 0).  Mid-pattern the power cannot be
            // absorbed: a·(ab)^k·b ≠ (ab)^(k+1) — only the ROTATED base commutes
            // across a partial match, and we match the base verbatim here.
            // Skip at leading position (i == 0) to avoid undoing power unwinding:
            // unwind produces u · u^(n-1); merging it back to u^n creates an infinite cycle.
            if (pos == 0 && i > 0 && t->is_power()) {
                euf::snode const* pow_base = t->arg0();
                if (pow_base) {
                    euf::snode_vector pb_tokens;
                    collect_tokens_dir(pow_base, fwd, pb_tokens);
                    if (pb_tokens.size() == base_tokens.size()) {
                        bool match = true;
                        for (unsigned j = 0; j < pb_tokens.size() && match; j++)
                            match = (pb_tokens[j] == base_tokens[j]);
                        if (match) {
                            expr* pow_exp = get_power_exp_expr(t, seq);
                            if (pow_exp) {
                                sum = sum ? arith.mk_add(sum, pow_exp) : pow_exp;
                                continue;
                            }
                        }
                    }
                }
            }
            break;
        }
        // After loop: i = break index or side_tokens.size()
        if (pos == 0) {
            last_stable_idx = i;
            last_stable_sum = sum;
        }
        return {expr_ref(last_stable_sum, m), last_stable_idx};
    }

    simplify_result nielsen_node::simplify_and_init(ptr_vector<nielsen_edge> const& cur_path) {
        if (m_is_extended)
            return simplify_result::proceed;

        // Memoization: the passes below are idempotent, and their outcome
        // depends only on this node's constraints and the per-solve external
        // context (outer arith bounds, the LP path constraints — both fixed
        // for the node while one solve() runs).  Iterative deepening and hot
        // paths revisit non-extended frontier nodes many times; with a valid
        // stamp nothing can come out differently, so skip all passes
        // (including the expensive regex-widening product searches).  Every
        // constraint mutator clears the stamp — in particular the Parikh /
        // node-length constraints added after the first visit's simplification
        // trigger exactly one re-simplification under the richer LP context —
        // and solve() bumps the epoch so a new outer assignment is re-examined.
        if (m_simplify_stamp == m_graph.m_simplify_epoch)
            return is_satisfied() ? simplify_result::satisfied : simplify_result::proceed;

        euf::sgraph& sg = m_graph.sg();
        ast_manager& m = sg.get_manager();
        seq_util& seq = this->graph().seq();
        bool changed = true;

        // drop memberships that have become trivially satisfied
        auto remove_trivial_mems = [&]() {
            unsigned w = 0;
            for (unsigned j = 0; j < m_str_mem.size(); ++j) {
                if (m_str_mem[j].is_trivial(this))
                    continue;
                m_str_mem[w++] = m_str_mem[j];
            }
            if (w == m_str_mem.size())
                return;
            m_str_mem.shrink(w);
        };

        // Merge memberships that have become identical.  The derivative
        // consumption below rewrites m_str/m_regex in place, bypassing
        // add_str_mem's dedup, so two constraints can converge onto the same
        // (str, regex, kind, root, ν) and both survive — inflating the node
        // signature (which costs sibling / unsat-cache hits) and paying an extra
        // widening product search per duplicate
        auto dedup_mems = [&]() {
            unsigned w = 0;
            for (unsigned j = 0; j < m_str_mem.size(); ++j) {
                unsigned k = 0;
                for (; k < w; ++k) {
                    if (m_str_mem[k] == m_str_mem[j])
                        break;
                }
                if (k < w) {
                    m_str_mem[k].m_dep = m_graph.dep_mgr().mk_join(m_str_mem[k].m_dep, m_str_mem[j].m_dep);
                    continue;
                }
                m_str_mem[w++] = m_str_mem[j];
            }
            m_str_mem.shrink(w);
        };

        // Negative LP-entailment results are stable for the whole call: the
        // subsolver context (path constraints + the constraints asserted before
        // this call) does not change during simplification (check_lp_le's probe
        // is push/pop-scoped and constraints added here are only asserted
        // afterwards).  The fixpoint sweeps would nonetheless re-issue the same
        // FAILING queries — each a full subsolver check() — on every sweep, so
        // cache them.  Successful queries rewrite the equation and do not repeat.
        std::unordered_set<uint64_t> lp_not_entailed;
        auto lp_le = [&](expr* lhs, expr* rhs, dep_tracker& dep) {
            const uint64_t key = (static_cast<uint64_t>(lhs->get_id()) << 32) | rhs->get_id();
            if (lp_not_entailed.count(key))
                return false;
            if (m_graph.check_lp_le(lhs, rhs, this, dep))
                return true;
            lp_not_entailed.insert(key);
            return false;
        };

        // DON'T add rules here that add new constraints or apply substitutions
        // add them to apply_det_modifier instead

        while (changed) {
            changed = false;

            // pass 1: remove trivially satisfied equalities and memberships
            unsigned wi = 0;
            for (unsigned i = 0; i < m_str_eq.size(); ++i) {
                str_eq& eq = m_str_eq[i];
                if (eq.is_trivial())
                    continue;
                m_str_eq[wi++] = eq;
            }
            if (wi < m_str_eq.size()) {
                m_str_eq.shrink(wi);
                changed = true;
            }

            remove_trivial_mems();

            unsigned wk = 0;
            for (unsigned k = 0; k < m_str_deq.size(); ++k) {
                str_deq& deq = m_str_deq[k];

                // lhs == rhs (or both ε): the disequality is refuted
                if (deq.m_lhs == deq.m_rhs || (deq.m_lhs->is_empty() && deq.m_rhs->is_empty()))
                    return set_simplify_conflict(backtrack_reason::symbol_clash, deq.m_dep);

                // single unit vs single unit: hand off as a character disequality
                if (deq.m_lhs->length() == 1 && deq.m_rhs->length() == 1) {
                    expr* l, *r;
                    if (seq.str.is_unit(deq.m_lhs->get_expr(), l) &&
                        seq.str.is_unit(deq.m_rhs->get_expr(), r)) {
                        add_constraint(constraint(m.mk_not(m.mk_eq(l, r)), deq.m_dep, m));
                        continue;   // dropped from the deq list
                    }
                }

                // ε != s with s provably non-empty: discharged
                // (both-empty was refuted above, so the other side is non-empty)
                if (deq.m_lhs->is_empty() && side_cannot_be_empty(deq.m_rhs))
                    continue;
                if (deq.m_rhs->is_empty() && side_cannot_be_empty(deq.m_lhs))
                    continue;

                // shared power simplification + affix cancellation; an aligned
                // provably-distinct unit pair means the disequality holds — drop it
                if (simplify_side_pair(this, sg, deq.m_lhs, deq.m_rhs, deq.m_dep, changed))
                    continue;

                // cancellation may have made the two sides equal: refuted
                if (deq.m_lhs == deq.m_rhs || (deq.m_lhs->is_empty() && deq.m_rhs->is_empty()))
                    return set_simplify_conflict(backtrack_reason::symbol_clash, deq.m_dep);

                m_str_deq[wk++] = deq;
            }
            if (wk < m_str_deq.size()) {
                m_str_deq.shrink(wk);
                changed = true;
            }

            // pass 2: per-equation side simplification shared with the deq pass
            // (constant-exponent powers + prefix/suffix cancellation, see
            // simplify_side_pair), plus empty-side conflict detection
            for (str_eq& eq : m_str_eq) {
                SASSERT(eq.well_formed());
                if (eq.is_trivial())
                    continue;   // may have become trivial earlier in this pass

                // power simplification (base^0 → ε, base^1 → base) and affix
                // cancellation.  A provably-distinct unit pair at an aligned
                // position is a symbol clash.
                if (simplify_side_pair(this, sg, eq.m_lhs, eq.m_rhs, eq.m_dep, changed))
                    return set_simplify_conflict(backtrack_reason::symbol_clash, eq.m_dep);

                // one side empty, the other not empty => conflict check
                // (the actual substitution is done in apply_det_modifier)
                if (eq.m_lhs->is_empty() && !eq.m_rhs->is_empty()) {
                    if (check_empty_side_conflict(eq.m_rhs, eq.m_dep))
                        return simplify_result::conflict;
                }
                else if (eq.m_rhs->is_empty() && !eq.m_lhs->is_empty()) {
                    if (check_empty_side_conflict(eq.m_lhs, eq.m_dep))
                        return simplify_result::conflict;
                }
            }

            // pass 3: power simplification.
            // (What used to be pass 3a — constant-exponent power rewriting —
            // now runs in pass 2 via simplify_side_pair; the labels 3b–3e are
            // kept stable since other comments reference them.)
            for (str_eq& eq : m_str_eq) {
                SASSERT(eq.well_formed());
                if (eq.is_trivial())
                    continue;

                // 3b: merge adjacent same-base tokens into combined powers
                if (euf::snode const* s = merge_adjacent_powers(sg, m_graph.a, m_graph.m_rw, eq.m_lhs))
                    { eq.m_lhs = s; changed = true; }
                if (euf::snode const* s = merge_adjacent_powers(sg, m_graph.a, m_graph.m_rw, eq.m_rhs))
                    { eq.m_rhs = s; changed = true; }

                // 3c: CommPower-based power elimination — when one side starts
                // with a power w^p, count base-pattern occurrences c on the
                // other side's prefix.  If we can determine the ordering between
                // p and c, cancel the matched portion.
                // Spec: CommPower cancellation.
                //   Given: pow_side = w^p · rest_pow  and  other_side = w^c · rest_other
                //   where c is the number of times the base pattern w occurs in the
                //   directional prefix of other_side.
                //   - If p ≤ c: pow_side := rest_pow,            other_side := w^(c-p) · rest_other
                //   - If c ≤ p: pow_side := w^(p-c) · rest_pow,  other_side := rest_other
                //   - If p = c: both reduce completely (handled by both conditions above).
                SASSERT(eq.well_formed());
                bool comm_changed = false;
                for (int side = 0; side < 2 && !comm_changed; ++side) {
                    euf::snode const*& pow_side = side == 0 ? eq.m_lhs : eq.m_rhs;
                    euf::snode const*& other_side = side == 0 ? eq.m_rhs : eq.m_lhs;
                    if (!pow_side || !other_side)
                        continue;
                    for (unsigned od = 0; od < 2 && !comm_changed; ++od) {
                        bool fwd = od == 0;
                        euf::snode const* end_tok = dir_token(pow_side, fwd);
                        if (!end_tok || !end_tok->is_power())
                            continue;
                        euf::snode const* base_sn = end_tok->arg0();
                        expr* pow_exp = get_power_exp_expr(end_tok, seq);
                        if (!base_sn || !pow_exp)
                            continue;

                        auto [count, consumed] =
                            comm_power(base_sn, other_side, m, m_graph.a, seq, fwd);
                        if (!count.get() || consumed == 0)
                            continue;

                        expr_ref norm_count = normalize_arith(m_graph.m_rw, count);
                        bool pow_le_count = false, count_le_pow = false;
                        dep_tracker pow_le_dep = nullptr, count_le_dep = nullptr;
                        rational diff;
                        if (get_const_power_diff(norm_count, pow_exp, m_graph.a, diff)) {
                            count_le_pow = diff.is_nonpos();
                            pow_le_count = diff.is_nonneg();
                        }
                        else if (!cur_path.empty()) {
                            pow_le_count = lp_le(pow_exp, norm_count, pow_le_dep);
                            count_le_pow = lp_le(norm_count, pow_exp, count_le_dep);
                        }
                        if (!pow_le_count && !count_le_pow)
                            continue;

                        eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, pow_le_dep);
                        eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, count_le_dep);

                        pow_side = dir_drop(sg, pow_side, 1, fwd);
                        other_side = dir_drop(sg, other_side, consumed, fwd);
                        expr* base_e = get_power_base_expr(end_tok, seq);
                        if (pow_le_count && count_le_pow) {
                            // equal: both cancel completely
                        }
                        else if (pow_le_count) {
                            // pow <= count: remainder goes to other_side
                            expr_ref rem = normalize_arith(m_graph.m_rw, m_graph.a.mk_sub(norm_count, pow_exp));
                            expr_ref pw(seq.str.mk_power(base_e, rem), m);
                            other_side = dir_concat(sg, sg.mk(pw), other_side, fwd);
                        }
                        else {
                            // count <= pow: remainder goes to pow_side
                            expr_ref rem = normalize_arith(m_graph.m_rw, m_graph.a.mk_sub(pow_exp, norm_count));
                            expr_ref pw(seq.str.mk_power(base_e, rem), m);
                            pow_side = dir_concat(sg, sg.mk(pw), pow_side, fwd);
                        }
                        comm_changed = true;
                    }
                }
                if (comm_changed)
                    changed = true;

                // Once anything changed in this sweep (this equation or an
                // earlier one), defer 3d/3e and let the cheap passes reach a
                // fixpoint first: the while loop re-enters pass 2, which
                // simplifies new constant-exponent powers (e.g. base^1 → base
                // created by 3c) before 3e's LP-based elimination would
                // introduce a needless fresh variable.  This continues the for
                // loop, so 3d/3e are deferred for the REMAINING equations of
                // this sweep as well (they are revisited on the rerun).
                if (changed)
                    continue;

                // 3d: power prefix elimination — when both sides start with a
                // power of the same base, cancel the common power prefix.
                // (Subsumed by 3c for many cases, but handles same-base-power
                // pairs that CommPower may miss when both leading tokens are powers.)
                SASSERT(eq.well_formed());
                for (unsigned od = 0; od < 2 && !changed; ++od) {
                    bool fwd = (od == 0);
                    euf::snode const* lh = dir_token(eq.m_lhs, fwd);
                    euf::snode const* rh = dir_token(eq.m_rhs, fwd);
                    if (!(lh && rh && lh->is_power() && rh->is_power()))
                        continue;
                    expr* lb = get_power_base_expr(lh, seq);
                    expr* rb = get_power_base_expr(rh, seq);
                    if (!(lb && rb && lb == rb))
                        continue;
                    expr* lp = get_power_exp_expr(lh, seq);
                    expr* rp = get_power_exp_expr(rh, seq);
                    rational diff;
                    if (lp && rp && get_const_power_diff(rp, lp, m_graph.a, diff)) {
                        // rp = lp + diff (constant difference)
                        eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                        eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                        if (diff.is_pos()) {
                            // rp > lp: put base^diff on RHS (direction-aware prepend/append)
                            expr_ref de(m_graph.a.mk_int(diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_rhs = dir_concat(sg, sg.mk(pw), eq.m_rhs, fwd);
                        }
                        else if (diff.is_neg()) {
                            // lp > rp: put base^(-diff) on LHS
                            expr_ref de(m_graph.a.mk_int(-diff), m);
                            expr_ref pw(seq.str.mk_power(lb, de), m);
                            eq.m_lhs = dir_concat(sg, sg.mk(pw), eq.m_lhs, fwd);
                        }
                        // diff == 0: both powers cancel completely
                        changed = true;
                    }
                    // 3e: LP-aware power directional elimination
                    else if (lp && rp && !cur_path.empty()) {
                        dep_tracker lp_le_dep = nullptr, rp_le_dep = nullptr;
                        bool lp_le_rp = lp_le(lp, rp, lp_le_dep);
                        bool rp_le_lp = lp_le(rp, lp, rp_le_dep);
                        if (lp_le_rp || rp_le_lp) {
                            if (lp_le_rp)
                                eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, lp_le_dep);
                            if (rp_le_lp)
                                eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, rp_le_dep);
                            expr* smaller_exp = lp_le_rp ? lp : rp;
                            expr* larger_exp  = lp_le_rp ? rp : lp;
                            eq.m_lhs = dir_drop(sg, eq.m_lhs, 1, fwd);
                            eq.m_rhs = dir_drop(sg, eq.m_rhs, 1, fwd);
                            if (lp_le_rp && rp_le_lp) {
                                // both ≤ -> equal -> both cancel completely
                                add_constraint(m_graph.mk_constraint(m.mk_eq(lp, rp), eq.m_dep));
                            }
                            else {
                                // we only know for sure that one is smaller than the other
                                expr_ref d(m_graph.a.mk_sub(larger_exp, smaller_exp), m);
                                expr_ref zero(m_graph.a.mk_int(0), m);
                                add_constraint(m_graph.mk_constraint(m_graph.a.mk_ge(d, zero), eq.m_dep));
                                expr_ref pw(seq.str.mk_power(lb, d), m);
                                euf::snode const*& larger_side = lp_le_rp ? eq.m_rhs : eq.m_lhs;
                                larger_side = dir_concat(sg, sg.mk(pw), larger_side, fwd);
                            }
                            changed = true;
                        }
                    }
                }
            }
        }

        // consume concrete characters from str_mem via Brzozowski derivatives
        // in both directions (left-to-right, then right-to-left).
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.well_formed());
            if (mem.is_primitive() || !mem.is_plain())
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;
                while (!mem.m_str->is_empty()) {
                    euf::snode const* tok = dir_token(mem.m_str, fwd);
                    if (!tok || !tok->is_char_or_unit())
                        break;
                    euf::snode const* src_re = mem.m_regex;
                    euf::snode const* deriv = fwd
                        ? sg.brzozowski_deriv(mem.m_regex, tok)
                        : reverse_brzozowski_deriv(sg, m_graph.m_deriv_rw, m_graph.m_rw, mem.m_regex, tok);
                    TRACE(seq, tout << mem_pp(mem) << " d: " << spp(deriv, m) << "\n");
                    if (!deriv)
                        break;
                    if (deriv->is_fail())
                        return set_simplify_conflict(backtrack_reason::regex, mem.m_dep);
                    if (fwd) {
                        if (tok->is_char()) {
                            // concrete char: record single edge directly
                            m_graph.record_partial_derivative_edge(src_re, deriv);
                        } else if (src_re->is_ground()
                                   && !m_graph.m_explored_automaton.contains(src_re->get_expr()->get_id())) {
                            // symbolic unit: record all concrete minterm edges for src_re
                            // so cycle_decomp can detect SCCs lazily.  Skip when the
                            // component has already been fully explored
                            // (ensure_automaton_explored) — its edges are recorded.
                            euf::snode_vector mts;
                            sg.compute_minterms(src_re, mts);
                            for (euf::snode const* mt : mts) {
                                euf::snode const* mt_deriv = sg.brzozowski_deriv(src_re, mt);
                                if (mt_deriv && !mt_deriv->is_fail() && mt_deriv->is_ground())
                                    m_graph.record_partial_derivative_edge(src_re, mt_deriv);
                            }
                        }
                    }
                    mem.m_str = dir_drop(sg, mem.m_str, 1, fwd);
                    mem.m_regex = deriv;
                }
            }
        }

        // NOTE: a second "consume symbolic characters via uniform derivatives"
        // loop used to follow here.  It was unreachable: the loop above already
        // consumes every leading char/unit (concrete AND symbolic) through
        // sg.brzozowski_deriv, which canonicalizes with th_rewriter — and being
        // a second, different derivative-construction path it was exactly the
        // canonicalization-divergence hazard the brzozowski_deriv comment warns
        // about, so it was removed rather than kept in sync.

        // consume leading characters of land-state view memberships (paper §5.3).
        // m_regex is the current (plain) derivative state; we gate on whether it
        // lies in Q_ν (projection_state_in_Q) and step with the ordinary
        // derivative, keeping the view annotation.
        for (str_mem& mem : m_str_mem) {
            SASSERT(mem.well_formed());
            if (mem.is_plain())
                continue;
            if (consume_view(mem))
                return simplify_result::conflict;
        }

        // check for regex memberships that are immediately infeasible
        for (str_mem& mem : m_str_mem) {
            if (mem.is_contradiction(this)) {
                TRACE(seq, tout << "contradiction " << mem_pp(mem) << "\n");
                return set_simplify_conflict(backtrack_reason::regex, mem.m_dep);
            }
        }

        // remove trivial membership constraints once again, then merge the ones
        // the in-place derivative consumption has made identical
        remove_trivial_mems();
        dedup_mems();

        // Regex widening: for each remaining str_mem, overapproximate
        // the string by replacing variables with their regex intersection
        // and check if the result intersected with the target regex is empty.
        // Detects infeasible constraints that would otherwise require
        // expensive exploration.
        SASSERT(m_graph.m_seq_regex);
        for (str_mem const& mem : m_str_mem) {
            SASSERT(mem.well_formed());
            if (mem.is_primitive())
                continue;
            // Views are widened as well: check_regex_widening substitutes a
            // sound over-approximation of the view language (see there) and
            // returns false when none applies.
            dep_tracker dep = mem.m_dep;
            if (m_graph.check_regex_widening(*this, mem, dep))
                return set_simplify_conflict(backtrack_reason::regex_widening, dep);
        }

        // Length-forced positional constant clash.  Purely syntactic, and it
        // reaches interior alignments that affix cancellation cannot.  Run last,
        // on the fully canonical node.
        if (check_positional_clash())
            return simplify_result::conflict;

        // Simplification ran to completion: memoize.  Constraint additions made
        // DURING the passes cleared the stamp; setting it here (last) makes the
        // completed state authoritative.  Conflict paths return early and stay
        // unstamped, so a cleared conflict is re-examined from scratch.
        m_simplify_stamp = m_graph.m_simplify_epoch;

        if (is_satisfied()) {
            // pass 1 removed all trivial str_eq entries; is_satisfied() requires
            // the remainder to be trivial, so the vector must be empty here.
            SASSERT(m_str_eq.empty());
            return simplify_result::satisfied;
        }
        return simplify_result::proceed;
    }

    bool nielsen_node::consume_view(str_mem& mem) {
        SASSERT(mem.is_view());
        euf::sgraph& sg = m_graph.sg();

        while (mem.m_str && !mem.m_str->is_empty()) {
            euf::snode const* tok = mem.m_str->first();
            if (!tok || !tok->is_char_or_unit())
                break; // leading token is a variable/power — nothing to consume yet
            euf::snode const* c = mem.m_regex;
            // The gate tests the CURRENT (plain) state c against Q_ν.  An ite
            // state means a previous symbolic step has not been resolved yet;
            // leave it for apply_regex_if_split.
            if (!c->is_ground() || c->kind() == euf::snode_kind::s_ite)
                break;
            if (!m_graph.projection_state_in_Q(c->get_expr(), mem.m_nu)) {
                // a^{-1} L_{Q,F}(c) = ∅ when c ∉ Q.
                set_simplify_conflict(backtrack_reason::regex, mem.m_dep);
                return true;
            }
            // Step with brzozowski_deriv for BOTH concrete and symbolic tokens.
            // This is essential: the partial-DFA states (and m_root) are produced
            // by brzozowski_deriv, so its canonicalization must be used here too —
            // otherwise the resolved state never equals m_root by snode identity.
            // For a symbolic unit it yields a canonical ite residual that
            // apply_regex_if_split later resolves.
            euf::snode const* next = sg.brzozowski_deriv(c, tok);
            if (!next)
                break;
            mem.m_str = sg.drop_left(mem.m_str, 1);
            mem.m_regex = next;
            if (next->is_fail()) {
                // view: derivative collapsed to ∅ — unsatisfiable.
                set_simplify_conflict(backtrack_reason::regex, mem.m_dep);
                return true;
            }
            if (!(next->is_ground() && next->kind() != euf::snode_kind::s_ite))
                break;   // symbolic ite residual: defer to apply_regex_if_split
        }
        return false;
    }

    bool nielsen_node::is_satisfied() const {
        if (!m_str_deq.empty() || !m_str_eq.empty())
            return false;
        if (any_of(m_str_mem, [](auto const &m) { return !m.is_primitive();}))
            return false;
        return true;
    }

    static bool snode_has_rigid(euf::snode const* s) {
        for (euf::snode const* t : *s) {
            if (t->is_rigid())
                return true;
        }
        return false;
    }

    bool nielsen_node::references_rigid() const {
        for (str_eq const& eq : m_str_eq)
            if (snode_has_rigid(eq.m_lhs) || snode_has_rigid(eq.m_rhs))
                return true;
        for (str_deq const& dq : m_str_deq)
            if (snode_has_rigid(dq.m_lhs) || snode_has_rigid(dq.m_rhs))
                return true;
        for (str_mem const& mem : m_str_mem)
            if (snode_has_rigid(mem.m_str) || snode_has_rigid(mem.m_regex))
                return true;
        return false;
    }
}
