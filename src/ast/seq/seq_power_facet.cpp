/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.cpp

Abstract:

    See seq_power_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "ast/seq/seq_power_facet.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"
#include "util/uint_set.h"

namespace seq {

    expr_ref str_power::fact(seq_util& u) const {
        ast_manager& m = u.get_manager();
        return expr_ref(m.mk_eq(m_e, u.str.mk_power(m_s, m_n)), m);
    }

    void power_facet::remove(unsigned idx, symbol rule, proof* pr) {
        SASSERT(idx < m_pows.size());
        if (!m_pows[idx].m_active)
            return;
        if (m_dm.proofs_enabled()) {
            m_trail.push(vector_field_trail<str_power, proof_ref>(m_pows, idx, &str_power::m_proof));
            m_pows[idx].m_proof = m_dm.mk_proof(rule, m.mk_true(), { m_pows[idx].m_proof.get(), pr });
        }
        m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, &str_power::m_active));
        m_pows[idx].m_active = false;
    }

    void power_facet::mark(unsigned idx, bool str_power::* flag) {
        SASSERT(idx < m_pows.size());
        if (m_pows[idx].*flag)
            return;
        m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, flag));
        m_pows[idx].*flag = true;
    }

    void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
        unsigned idx;
        if (find_power(var, idx))
            remove(idx, symbol("power-substitution-discharge"), m_dm.substitution_proof());
        for (expr* t : repl) {
            expr* s = nullptr, *n = nullptr;
            if (!u.str.is_power(t, s, n))
                continue;
            proof_ref pr(m);
            if (m_dm.proofs_enabled()) {
                str_power p(m, t, s, n);
                pr = m_dm.mk_proof(symbol("power-substitution-token-definition"), p.fact(u), { m_dm.substitution_proof() });
            }
            add_power(t, s, n, nullptr, pr, symbol("power-substitution-token-definition"));
        }
        // rebase obligations whose base mentions var; the power token keeps its identity
        for (unsigned i = 0; i < m_pows.size(); ++i) {
            if (!m_pows[i].active())
                continue;
            expr_ref_vector base(m);
            u.str.get_concat_units(m_pows[i].m_s.get(), base);
            if (!base.contains(var))
                continue;
            subst_in(base, var, repl);
            m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
            m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
            if (m_dm.proofs_enabled()) {
                m_trail.push(vector_field_trail<str_power, proof_ref>(m_pows, i, &str_power::m_proof));
                m_pows[i].m_proof = m_dm.mk_proof(symbol("power-substitute-base"), m_pows[i].fact(u),
                                                { m_pows[i].m_proof.get(), m_dm.substitution_proof() });
            }
        }
    }

    stx::facet_i* power_facet::clone(trail_stack& trail) const {
        power_facet* f = alloc(power_facet, trail, m, u, a, m_dm);
        f->m_pows.append(m_pows);
        f->m_max_unfold = m_max_unfold;
        return f;
    }

    std::ostream& power_facet::display(std::ostream& out) const {
        unsigned num_active = 0;
        for (auto const& p : m_pows)
            if (p.active())
                ++num_active;
        out << "power_facet: " << num_active << " power obligation(s) (" << m_pows.size() << " total incl. inactive)\n";
        for (auto const& p : m_pows) {
            if (!p.active())
                continue;
            out << "  " << mk_pp(p.m_e.get(), m) << " = " << mk_pp(p.m_s.get(), m) << "^" << mk_pp(p.m_n.get(), m) << "\n";
        }
        return out;
    }

    // Build the concatenation of `j` copies of `s` (`j >= 1`).
    static expr_ref mk_power_unfold(seq_util& u, ast_manager& m, expr* s, unsigned j) {
        SASSERT(j >= 1);
        expr_ref result(s, m);
        for (unsigned k = 1; k < j; ++k)
            result = expr_ref(u.str.mk_concat(s, result), m);
        return result;
    }

    // Put an exponent expression into arithmetic normal form.
    static expr_ref mk_exp(ast_manager& m, expr* e) {
        th_rewriter rw(m);
        expr_ref r(e, m);
        rw(r);
        return r;
    }

    static expr_ref mk_len_sum(seq_util& u, arith_util& a, ast_manager& m, expr_ref_vector const& toks, unsigned from, unsigned to) {
        expr_ref sum(a.mk_int(0), m);
        for (unsigned i = from; i < to; ++i)
            sum = expr_ref(a.mk_add(sum, u.str.is_unit(toks[i]) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(toks[i])), m);
        return sum;
    }

    stx::simplify_result power_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& sf = ac.solver_facet_ref();
        m_stats.m_num_propagate++;

        bool changed = false;
        // `m_pows` is append-only, so a plain forward scan suffices.
        for (unsigned i = 0; i < f.powers().size(); ++i) {
            if (!f.powers()[i].active())
                continue;
            str_power const& p = f.powers()[i];
            rational v;

            // `epsilon^n = epsilon`; otherwise power_peel unfolds it forever.
            if (u.str.is_empty(p.m_s)) {
                broadcast_subst(n, p.m_e.get(), expr_ref_vector(m), p.m_dep, p.m_proof, symbol("power-empty-base"));
                changed = true;
                continue;
            }

            // Large fixed powers remain tokens, including in extracted witnesses.
            if (a.is_numeral(p.m_n, v) && v <= rational(1024)) {
                expr_ref rhs(m);
                if (!v.is_pos())
                    rhs = u.str.mk_empty(p.m_e.get()->get_sort());
                else
                    rhs = mk_power_unfold(u, m, p.m_s.get(), v.get_unsigned());
                expr_ref_vector repl(m);
                u.str.get_concat_units(rhs.get(), repl);
                broadcast_subst(n, p.m_e.get(), repl, p.m_dep, p.m_proof, symbol("power-fixed-numeral-unfold"));
                changed = true;
                continue;
            }

            // Assert the length-only consequences once.
            if (!p.m_axiomatized) {
                expr_ref len_e(u.str.mk_length(p.m_e.get()), m);
                // token-wise base length: the sub-solver has no sequence theory for len("ab")
                expr_ref_vector base(m);
                u.str.get_concat_units(p.m_s.get(), base);
                expr_ref len_s = mk_len_sum(u, a, m, base, 0, base.size());
                expr_ref emp(u.str.mk_empty(p.m_e.get()->get_sort()), m);
                expr_ref n_ge_1(a.mk_ge(p.m_n.get(), a.mk_int(1)), m);
                expr_ref e_is_emp(m.mk_eq(len_e, a.mk_int(0)), m);
                expr_ref s_is_emp(m.mk_eq(len_s, a.mk_int(0)), m);

                sf.add_constraint(m.mk_or(n_ge_1, e_is_emp), p.m_dep, p.m_proof, symbol("power-nonpositive-length"));
                sf.add_constraint(m.mk_or(m.mk_not(s_is_emp), e_is_emp), p.m_dep, p.m_proof, symbol("power-empty-base-length"));
                // Preserve sharing counts; add_constraint retains the whole clause.
                expr* n_lt_1 = m.mk_not(n_ge_1);
                expr* len_power = a.mk_mul(p.m_n.get(), len_s);
                expr* length_eq = m.mk_eq(len_e, len_power);
                sf.add_constraint(m.mk_or(n_lt_1, length_eq), p.m_dep, p.m_proof, symbol("power-positive-length-product"));
                sf.add_constraint(m.mk_or(n_lt_1, s_is_emp, a.mk_le(p.m_n.get(), len_e)), p.m_dep, p.m_proof, symbol("power-positive-length-lower-bound"));
                f.mark(i, &str_power::m_axiomatized);
                changed = true;
            }
        }
        if (sf.has_conflict()) {
            n.set_conflict(stx::br_plugin_base, sf.conflict_dep());
            return stx::simplify_result::conflict;
        }
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // Thin wrapper around `power_facet::find_power`.
    static bool is_power_token(power_facet const& f, expr* e, unsigned& idx) {
        return f.find_power(e, idx);
    }

    static expr_ref mk_len(seq_util& u, ast_manager& m, expr* e) {
        return expr_ref(u.str.mk_length(e), m);
    }

    bool power_split::iterator::next(eq_tree::edge& out) {
        auto ac = get_ambient(m_n);
        auto& f = ac.power_facet_ref();
        if (m_pow_index >= f.powers().size() || !f.powers()[m_pow_index].active())
            return false; // obligation already discharged by another route
        if (m_next_j > m_bound + 1)
            return false;
        str_power p = f.powers()[m_pow_index]; // copy: broadcast_subst may reallocate m_pows
        unsigned j = m_next_j++;

        if (j > m_bound) {
            // Residual branch `n > bound`: no substitution, obligation stays pending.
            ac.solver_facet_ref().add_constraint(a.mk_ge(p.m_n, a.mk_int(m_bound + 1)), m_dep, nullptr, symbol("power-exponent-residual-guard"));
            f.mark(m_pow_index, &str_power::m_split_exhausted);
            out = eq_tree::edge("power:n>bound", m_dep, false, 0);
            return true;
        }

        expr_ref rhs = mk_power_unfold(u, m, p.m_s, j);
        expr_ref_vector repl(m);
        u.str.get_concat_units(rhs.get(), repl);
        ac.solver_facet_ref().add_constraint(m.mk_eq(p.m_n, a.mk_int(j)), m_dep, nullptr, symbol("power-exponent-case-guard"));
        broadcast_subst(m_n, p.m_e, repl, m_dep, p.m_proof, symbol("power-exponent-case-unfold"));

        out = eq_tree::edge("power:n=j", m_dep, true, 0);
        return true;
    }

    // `U^n := epsilon` under `n <= 0`.
    static void unfold_empty(eq_tree::node& n, power_facet& f, unsigned idx, eq_tree::dep_tracker dep) {
        arith_util& a = f.get_arith_util();
        str_power p = f.powers()[idx]; // copy: broadcast_subst may reallocate m_pows
        expr_ref_vector empty(a.get_manager());
        get_ambient(n).solver_facet_ref().add_constraint(a.mk_le(p.m_n, a.mk_int(0)), dep, nullptr, symbol("power-nonpositive-exponent-guard"));
        broadcast_subst(n, p.m_e, empty, dep, p.m_proof, symbol("power-nonpositive-unfold"));
    }

    // `side` with `k` tokens removed from the chosen end, optionally
    // replaced by `repl`.
    static expr_ref_vector replace_end(expr_ref_vector const& side, bool front, unsigned k, expr* repl) {
        expr_ref_vector r(side.get_manager());
        if (front && repl)
            r.push_back(repl);
        for (unsigned i = front ? k : 0; i < (front ? side.size() : side.size() - k); ++i)
            r.push_back(side.get(i));
        if (!front && repl)
            r.push_back(repl);
        return r;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        // Only a power still present in an equation needs exponent enumeration.
        obj_hashtable<expr> present;
        for (auto const& eq : ac.eq_facet_ref().equations()) {
            if (!eq.active())
                continue;
            for (expr* t : eq.m_lhs) present.insert(t);
            for (expr* t : eq.m_rhs) present.insert(t);
        }

        for (unsigned i = 0; i < f.powers().size(); ++i) {
            if (!f.powers()[i].active() || !present.contains(f.powers()[i].m_e.get()))
                continue;
            str_power p = f.powers()[i]; // copy: broadcast_subst may reallocate m_pows
            rational v;
            if (a.is_numeral(p.m_n, v))
                continue; // resolved by power_propagation
            if (p.m_split_exhausted)
                continue; // residual branch already taken

            eq_tree::dep_tracker dep = p.m_dep;
            unsigned bound = f.max_unfold();

            // First branch: `n <= 0`, so `e := epsilon`.
            unfold_empty(n, f, i, dep);

            iterator* it = alloc(iterator, n, i, bound, dep, m, u, a);
            out = eq_tree::edge("power:n<=0", dep, true, 0);
            committed = true;
            m_stats.m_num_splits++;
            return it;
        }
        return nullptr;
    }

    // -- power_trichotomy --

    // A base made only of constant characters, as a string.
    static bool constant_word(seq_util& u, expr_ref_vector const& toks, zstring& s) {
        s.reset();
        for (expr* t : toks) {
            expr* ch = nullptr;
            unsigned c;
            if (!u.str.is_unit(t, ch) || !u.is_const_char(ch, c))
                return false;
            s += zstring(c);
        }
        return !s.empty();
    }

    static bool has_period(zstring const& s, unsigned r) {
        for (unsigned i = 0; i + r < s.length(); ++i) {
            if (s[i] != s[i + r])
                return false;
        }
        return true;
    }

    static zstring primitive_root(zstring const& s) {
        for (unsigned d = 1; d < s.length(); ++d) {
            if (s.length() % d == 0 && has_period(s, d))
                return s.extract(0, d);
        }
        return s;
    }

    // Collect the ways the tokens `todo` (next token last) can begin. A power is
    // either empty or yields one copy of its base followed by an unknown rest.
    static bool beginnings(power_facet const& f, seq_util& u, ast_manager& m, ptr_vector<expr>& todo,
                           svector<unsigned>& cur, vector<svector<unsigned>>& out, unsigned& budget) {
        if (budget == 0)
            return false;
        --budget;
        ptr_vector<expr> consumed;
        expr* ch = nullptr;
        unsigned c, idx;
        while (!todo.empty() && todo.back() && u.str.is_unit(todo.back(), ch) && u.is_const_char(ch, c)) {
            consumed.push_back(todo.back());
            todo.pop_back();
            cur.push_back(c);
        }
        bool ok = true;
        expr* t = todo.empty() ? nullptr : todo.back();
        if (t && f.find_power(t, idx)) {
            todo.pop_back();
            ok = beginnings(f, u, m, todo, cur, out, budget);
            expr_ref_vector base(m);
            u.str.get_concat_units(f.powers()[idx].m_s, base);
            unsigned sz = todo.size();
            todo.push_back(nullptr);
            for (unsigned i = base.size(); i-- > 0; ) {
                todo.push_back(base.get(i));
            }
            ok = ok && beginnings(f, u, m, todo, cur, out, budget);
            todo.shrink(sz);
            todo.push_back(t);
        }
        else
            out.push_back(cur); // end of the base or unknown continuation
        cur.shrink(cur.size() - consumed.size());
        for (unsigned i = consumed.size(); i-- > 0; ) {
            todo.push_back(consumed[i]);
        }
        return ok;
    }

    // The characters that may occur in base `s` (`can`; false if unbounded) and,
    // outside nested powers, those that surely occur (`must`).
    static bool letters(power_facet const& f, seq_util& u, ast_manager& m, expr* s, bool top, uint_set& must, uint_set& can) {
        expr_ref_vector toks(m);
        u.str.get_concat_units(s, toks);
        for (expr* t : toks) {
            expr* ch = nullptr;
            unsigned c, idx;
            if (u.str.is_unit(t, ch) && u.is_const_char(ch, c)) {
                can.insert(c);
                if (top)
                    must.insert(c);
            }
            else if (!f.find_power(t, idx) || !letters(f, u, m, f.powers()[idx].m_s, false, must, can))
                return false;
        }
        return true;
    }

    // Whether one of the bases `s1`, `s2` can be a prefix of the other.
    static bool may_be_prefix(power_facet const& f, seq_util& u, ast_manager& m, expr* s1, expr* s2) {
        vector<svector<unsigned>> bs[2];
        expr* s[2] = { s1, s2 };
        for (unsigned i = 0; i < 2; ++i) {
            expr_ref_vector toks(m);
            u.str.get_concat_units(s[i], toks);
            ptr_vector<expr> todo;
            for (unsigned j = toks.size(); j-- > 0; ) {
                todo.push_back(toks.get(j));
            }
            svector<unsigned> cur;
            unsigned budget = 256;
            if (!beginnings(f, u, m, todo, cur, bs[i], budget))
                return true;
        }
        for (auto const& p : bs[0]) {
            for (auto const& q : bs[1]) {
                unsigned k = std::min(p.size(), q.size()), i = 0;
                while (i < k && p[i] == q[i]) {
                    ++i;
                }
                if (i == k)
                    return true;
            }
        }
        return false;
    }

    // Both sides start with powers of different bases, not both exponents numerals.
    bool power_trichotomy::find_trigger(eq_tree::node& n, trigger& t) const {
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        for (auto const& eq : ac.eq_facet_ref().equations()) {
            unsigned xi, yi;
            if (!eq.active() || eq.m_lhs.empty() || eq.m_rhs.empty() ||
                !f.find_power(eq.m_lhs[0], xi) || !f.find_power(eq.m_rhs[0], yi))
                continue;
            str_power const& px = f.powers()[xi];
            str_power const& py = f.powers()[yi];
            if (px.m_s == py.m_s || (a.is_numeral(px.m_n) && a.is_numeral(py.m_n)))
                continue; // power_split_elim resp. power_propagation
            // A base starting with a power has no known first character yet; power_peel exposes it.
            expr_ref_vector xs(m), ys(m);
            u.str.get_concat_units(px.m_s, xs);
            u.str.get_concat_units(py.m_s, ys);
            if (xs.empty() || ys.empty() || u.str.is_power(xs.get(0)) || u.str.is_power(ys.get(0)))
                continue;
            t = {xi, yi, eq.m_dep};
            return true;
        }
        return false;
    }

    // Branches 0..4 for `|X^M| <= |Y^N|`, 5..9 mirrored. Constant bases give
    // direct witnesses: f2 its primitive root, f3 one branch per period `r`.
    void power_trichotomy::enumerate(eq_tree::node& n, trigger const& t, branches& out) const {
        auto& f = get_ambient(n).power_facet_ref();
        expr* bases[2] = { f.powers()[t.m_x_idx].m_s, f.powers()[t.m_y_idx].m_s };
        // f1..f4 make one base a prefix of the other
        bool prefix = may_be_prefix(f, u, m, bases[0], bases[1]);
        // fits[d]: base d's letters may occur in the other base. f1 needs it
        // for X, f2..f4 need equal alphabets (f4 with q = 0 is f1).
        uint_set must[2], can[2];
        bool bounded[2];
        for (unsigned d = 0; d < 2; ++d) {
            bounded[d] = letters(f, u, m, bases[d], true, must[d], can[d]);
        }
        bool fits[2] = { !bounded[1] || must[0].subset_of(can[1]), !bounded[0] || must[1].subset_of(can[0]) };
        for (unsigned dir = 0; dir < 2; ++dir) {
            expr_ref_vector xs(m), ys(m);
            u.str.get_concat_units(bases[dir], xs);
            u.str.get_concat_units(bases[1 - dir], ys);
            zstring sx, sy;
            bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);
            unsigned b = 5 * dir;
            out.push_back({b, 0});
            if (!prefix)
                continue;
            if (fits[dir] && !(gx && gy && !sx.prefixof(sy)))
                out.push_back({b + 1, 0});
            if (!fits[0] || !fits[1])
                continue;
            if (!(gx && gy && sx + sy != sy + sx))
                out.push_back({b + 2, 0});
            if (!gx)
                out.push_back({b + 3, 0});
            else {
                for (unsigned r = 1; r < sx.length(); ++r) {
                    if (has_period(sx, r) && (!gy || (sy.length() >= sx.length() + r && (sy.length() - r) % sx.length() == 0)))
                        out.push_back({b + 3, r});
                }
            }
            out.push_back({b + 4, 0});
        }
    }

    void power_trichotomy::apply(eq_tree::node& n, trigger const& t, unsigned b, unsigned param) const {
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();
        auto& sf = ac.solver_facet_ref();
        bool dir_u = b < 5;
        // copies: add_power and broadcast_subst may reallocate m_pows
        str_power px = f.powers()[dir_u ? t.m_x_idx : t.m_y_idx]; // the shorter power X^M
        str_power py = f.powers()[dir_u ? t.m_y_idx : t.m_x_idx]; // the longer power Y^N
        eq_tree::dep_tracker dep = t.m_dep;
        expr* X = px.m_s, *M = px.m_n, *Y = py.m_s, *N = py.m_n;
        expr_ref_vector xs(m), ys(m);
        u.str.get_concat_units(X, xs);
        u.str.get_concat_units(Y, ys);
        zstring sx, sy;
        bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);

        auto constrain = [&](expr* c) { sf.add_constraint(c, dep, nullptr, symbol("power-trichotomy-case-guard")); };
        auto mk_pow = [&](expr* base, expr* exp) {
            expr_ref e = mk_exp(m, exp);
            expr_ref tok(u.str.mk_power(base, e), m);
            proof_ref pr(m);
            if (f.dm().proofs_enabled()) {
                str_power p(m, tok, base, e);
                pr = f.dm().mk_proof(symbol("power-trichotomy-token-definition"), p.fact(u), { px.m_proof.get(), py.m_proof.get() });
            }
            f.add_power(tok, base, e, dep, pr, symbol("power-trichotomy-token-definition"));
            return tok;
        };
        auto fresh_str = [&](char const* name) { return expr_ref(ac.mk_fresh_var(name, px.m_e->get_sort(), { px.m_e.get(), py.m_e.get() }), m); };
        auto fresh_int = [&](char const* name) { return expr_ref(ac.mk_fresh_var(name, a.mk_int(), { px.m_e.get(), py.m_e.get() }), m); };
        auto word = [&](zstring const& s) {
            expr_ref_vector r(m);
            u.str.get_concat_units(u.str.mk_string(s), r);
            return r;
        };
        auto one = [&](expr* e) {
            expr_ref_vector r(m);
            r.push_back(e);
            return r;
        };
        auto cat = [&](std::initializer_list<expr_ref_vector> parts) {
            expr_ref_vector r(m);
            for (auto const& p : parts) {
                r.append(p);
            }
            return r;
        };

        constrain(dir_u ? a.mk_le(mk_len(u, m, px.m_e), mk_len(u, m, py.m_e))
                        : a.mk_lt(mk_len(u, m, px.m_e), mk_len(u, m, py.m_e)));

        // Each case asserts exactly what its substitution `Y^N := X^M . z` needs.
        expr_ref_vector z(m);
        switch (b % 5) {
        case 0:
            // X^M = epsilon
            constrain(m.mk_or(a.mk_le(M, a.mk_int(0)), m.mk_eq(mk_len_sum(u, a, m, xs, 0, xs.size()), a.mk_int(0))));
            broadcast_subst(n, px.m_e, expr_ref_vector(m), dep, px.m_proof, symbol("power-trichotomy-empty"));
            return;
        case 1: {
            // Y = X^M y',  z = y' Y^(N-1)
            expr_ref y1 = fresh_str("power-trichotomy-f1-y");
            constrain(a.mk_ge(N, a.mk_int(1)));
            ef.add_equation(ys, cat({one(px.m_e), one(y1)}), dep, nullptr, symbol("power-trichotomy-base-prefix"));
            z = cat({one(y1), one(mk_pow(Y, a.mk_sub(N, a.mk_int(1))))});
            break;
        }
        case 2: {
            // X = w^i, Y = w^j, M >= 1,  z = w^(jN - iM); `iM <= jN` follows from the length guard.
            expr_ref w(m), i(m), j(m);
            constrain(a.mk_ge(M, a.mk_int(1)));
            if (gx || gy) {
                zstring root = primitive_root(gx ? sx : sy);
                w = u.str.mk_string(root);
                if (gx)
                    i = a.mk_int(sx.length() / root.length());
                if (gy)
                    j = a.mk_int(sy.length() / root.length());
            }
            else
                w = fresh_str("power-trichotomy-f2-w");
            if (!i) {
                i = fresh_int("power-trichotomy-f2-i");
                constrain(a.mk_ge(i, a.mk_int(1)));
                ef.add_equation(xs, one(mk_pow(w, i)), dep, nullptr, symbol("power-trichotomy-short-base-period"));
            }
            if (!j) {
                j = fresh_int("power-trichotomy-f2-j");
                constrain(a.mk_ge(j, a.mk_int(1)));
                ef.add_equation(ys, one(mk_pow(w, j)), dep, nullptr, symbol("power-trichotomy-long-base-period"));
            }
            z = one(mk_pow(w, a.mk_sub(a.mk_mul(j, N), a.mk_mul(i, M))));
            break;
        }
        case 3: {
            // X = (p'p'')^k p', Y = X^(M-1) p'p'',  z = p'' p' X^(M-2) p'p'' Y^(N-2)
            expr_ref_vector p1(m), p2(m);
            constrain(a.mk_ge(M, a.mk_int(2)));
            constrain(a.mk_ge(N, a.mk_int(2)));
            if (param > 0) {
                // constant X with period r: p'p'' = X[0..r), p' = the last |X| mod r characters
                unsigned r = param, l1 = sx.length() % r;
                p1 = word(sx.extract(sx.length() - l1, l1));
                p2 = word(sx.extract(l1, r - l1));
            }
            else {
                expr_ref v1 = fresh_str("power-trichotomy-f3-p1"), v2 = fresh_str("power-trichotomy-f3-p2"), k = fresh_int("power-trichotomy-f3-k");
                p1 = one(v1);
                p2 = one(v2);
                ef.add_equation(xs, cat({one(mk_pow(u.str.mk_concat(v1, v2), k)), p1}), dep, nullptr, symbol("power-trichotomy-periodic-prefix"));
            }
            ef.add_equation(ys, cat({one(mk_pow(X, a.mk_sub(M, a.mk_int(1)))), p1, p2}), dep, nullptr, symbol("power-trichotomy-periodic-long-base"));
            z = cat({p2, p1, one(mk_pow(X, a.mk_sub(M, a.mk_int(2)))), p1, p2, one(mk_pow(Y, a.mk_sub(N, a.mk_int(2))))});
            break;
        }
        default: {
            // M = 1, Y = y'y'', X = Y^q y', q+1 <= N,  z = y'' Y^(N-q-1)
            expr_ref y1 = fresh_str("power-trichotomy-f4-y1"), y2 = fresh_str("power-trichotomy-f4-y2"), q = fresh_int("power-trichotomy-f4-q");
            constrain(m.mk_eq(M, a.mk_int(1)));
            constrain(a.mk_ge(q, a.mk_int(0)));
            constrain(a.mk_le(a.mk_add(q, a.mk_int(1)), N));
            ef.add_equation(ys, cat({one(y1), one(y2)}), dep, nullptr, symbol("power-trichotomy-long-base-cut"));
            ef.add_equation(xs, cat({one(mk_pow(Y, q)), one(y1)}), dep, nullptr, symbol("power-trichotomy-short-base-cut"));
            z = cat({one(y2), one(mk_pow(Y, a.mk_sub(a.mk_sub(N, q), a.mk_int(1))))});
            break;
        }
        }
        broadcast_subst(n, py.m_e, cat({one(px.m_e), z}), dep, py.m_proof, symbol("power-trichotomy-remainder"));
    }

    static char const* const trichotomy_labels[10] = {
        "trichotomy:u:empty", "trichotomy:u:f1", "trichotomy:u:f2", "trichotomy:u:f3", "trichotomy:u:f4",
        "trichotomy:v:empty", "trichotomy:v:f1", "trichotomy:v:f2", "trichotomy:v:f3", "trichotomy:v:f4",
    };

    // Resumption restores the node state of the split, so `m_t` stays valid.
    bool power_trichotomy::iterator::next(eq_tree::edge& out) {
        if (m_next >= m_branches.size())
            return false;
        auto [b, param] = m_branches[m_next++];
        m_owner.apply(m_n, m_t, b, param);
        out = eq_tree::edge(trichotomy_labels[b], m_t.m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_trichotomy::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        trigger t;
        if (!get_ambient(n).fparams().m_seq_power_trichotomy || !find_trigger(n, t))
            return nullptr;
        branches bs;
        enumerate(n, t, bs);
        // With f1 as the only non-empty form this is power_peel plus a fresh variable.
        if (any_of(bs, [](auto const& p) { return p.first % 5 == 1; }) && all_of(bs, [](auto const& p) { return p.first % 5 <= 1; }))
            return nullptr;
        auto [b, param] = bs[0]; // the empty branch is always first
        apply(n, t, b, param);
        has_more = true;
        committed = true;
        m_stats.m_num_splits++;
        out = eq_tree::edge(trichotomy_labels[b], t.m_dep, true, 0);
        return alloc(iterator, *this, n, t, bs);
    }

    // -- power_split_elim --

    // Scan `side` for repeated copies of `base_pattern`, returning the
    // symbolic copy count and the number of participating tokens. At a
    // pattern boundary, a same-base power token is absorbed whole by
    // adding its exponent to the count.
    static bool comm_power(power_facet const& f, expr_ref_vector const& base_pattern,
                            expr_ref_vector const& side, bool fwd,
                            ast_manager& m, arith_util& a, seq_util& u,
                            expr_ref& count, unsigned& consumed) {
        unsigned bn = base_pattern.size();
        unsigned sn = side.size();
        consumed = 0;
        if (bn == 0 || sn == 0)
            return false;

        expr* sum = nullptr;
        unsigned pos = 0;
        expr* last_stable_sum = nullptr;
        unsigned last_stable_idx = 0;

        unsigned i = 0;
        for (; i < sn; ++i) {
            expr* t = fwd ? side[i] : side[sn - 1 - i];
            if (pos == 0) {
                last_stable_idx = i;
                last_stable_sum = sum;
            }
            // Case 1: direct token match.
            expr* pat = fwd ? base_pattern[pos] : base_pattern[bn - 1 - pos];
            if (pos < bn && t == pat) {
                ++pos;
                if (pos >= bn) {
                    pos = 0;
                    sum = sum ? a.mk_add(sum, a.mk_int(1)) : (expr*)a.mk_int(1);
                }
                continue;
            }
            // Case 2: a same-base power token, absorbed whole at a pattern
            // boundary.
            unsigned pidx;
            if (pos == 0 && f.find_power(t, pidx)) {
                str_power const& q = f.powers()[pidx];
                expr_ref_vector qbase(m);
                u.str.get_concat_units(q.m_s.get(), qbase);
                if (qbase.size() == bn) {
                    bool match = true;
                    for (unsigned j = 0; j < bn && match; ++j)
                        match = (qbase[j] == base_pattern[j]);
                    if (match) {
                        sum = sum ? a.mk_add(sum, q.m_n.get()) : q.m_n.get();
                        continue;
                    }
                }
            }
            break;
        }
        if (pos == 0) {
            last_stable_idx = i;
            last_stable_sum = sum;
        }
        consumed = last_stable_idx;
        if (!last_stable_sum)
            return false;
        count = expr_ref(last_stable_sum, m);
        return true;
    }

    // Locate a power-vs-token-run elimination trigger.
    static bool find_split_elim_trigger(power_facet const& f, eq_facet const& ef,
                                         ast_manager& m, arith_util& a, seq_util& u,
                                         elim_trigger& t) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (!eq.active())
                continue;
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool pow_on_lhs : {true, false}) {
                expr_ref_vector const& pow_side = pow_on_lhs ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& other_side = pow_on_lhs ? eq.m_rhs : eq.m_lhs;
                for (bool fwd : {true, false}) {
                    expr* end_tok = fwd ? pow_side[0] : pow_side.back();
                    unsigned pow_idx;
                    if (!is_power_token(f, end_tok, pow_idx))
                        continue;
                    str_power const& p = f.powers()[pow_idx];
                    expr_ref_vector base_pattern(m);
                    u.str.get_concat_units(p.m_s.get(), base_pattern);
                    expr_ref count(m);
                    unsigned consumed;
                    if (!comm_power(f, base_pattern, other_side, fwd, m, a, u, count, consumed) || consumed == 0)
                        continue;
                    // Already resolved: no case split needed.
                    rational vc, vp;
                    if (a.is_numeral(count, vc) && a.is_numeral(p.m_n, vp))
                        continue;
                    t.m_eq_idx = i;
                    t.m_pow_on_lhs = pow_on_lhs;
                    t.m_fwd = fwd;
                    t.m_pow_idx = pow_idx;
                    t.m_consumed = consumed;
                    t.m_count = count;
                    t.m_dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    // Apply one elimination branch: either `e < count` or `e >= count`.
    static void elim_branch(eq_tree::node& n, elim_trigger const& t, bool covered) {
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();
        arith_util& a = f.get_arith_util();
        ast_manager& m = a.get_manager();
        str_power p = f.powers()[t.m_pow_idx]; // copy: add_power may reallocate m_pows
        expr* e = p.m_n, *count = t.m_count;
        ac.solver_facet_ref().add_constraint(covered ? a.mk_ge(count, a.mk_add(e, a.mk_int(1))) : a.mk_ge(e, count), t.m_dep,
                                           nullptr, symbol("power-elimination-exponent-order"));
        expr_ref rest_exp = mk_exp(m, covered ? a.mk_sub(count, e) : a.mk_sub(e, count));
        expr_ref rest(f.get_seq_util().str.mk_power(p.m_s, rest_exp), m);
        proof_ref rest_pr(m);
        if (f.dm().proofs_enabled()) {
            str_power rest_p(m, rest, p.m_s, rest_exp);
            rest_pr = f.dm().mk_proof(symbol("power-elimination-rest-definition"), rest_p.fact(f.get_seq_util()), { p.m_proof.get() });
        }
        f.add_power(rest, p.m_s, rest_exp, nullptr, rest_pr, symbol("power-elimination-rest-definition"));
        eq_facet::equation const& eq = ef.equations()[t.m_eq_idx];
        proof_ref eq_pr(eq.m_proof);
        expr_ref_vector ps = replace_end(t.m_pow_on_lhs ? eq.m_lhs : eq.m_rhs, t.m_fwd, 1, covered ? nullptr : rest.get());
        expr_ref_vector os = replace_end(t.m_pow_on_lhs ? eq.m_rhs : eq.m_lhs, t.m_fwd, t.m_consumed, covered ? rest.get() : nullptr);
        ef.remove_equation_trailed(t.m_eq_idx);
        ef.add_equation(t.m_pow_on_lhs ? ps : os, t.m_pow_on_lhs ? os : ps, t.m_dep, eq_pr,
                        symbol(covered ? "power-eliminate-covered-prefix" : "power-eliminate-base-prefix"));
    }

    bool power_split_elim::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        elim_branch(m_n, m_t, false);
        out = eq_tree::edge("power-split-elim:>=", m_t.m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_split_elim::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();

        elim_trigger t(m);
        if (!find_split_elim_trigger(f, ef, m, a, u, t))
            return nullptr;
        has_more = true;
        committed = true;
        m_stats.m_num_splits++;
        // If exponent ordering is already determined, no split is needed.
        rational d;
        if (a.is_numeral(mk_exp(m, a.mk_sub(t.m_count, f.powers()[t.m_pow_idx].m_n)), d)) {
            elim_branch(n, t, d.is_pos());
            out = eq_tree::edge(d.is_pos() ? "power-split-elim:<" : "power-split-elim:>=", t.m_dep, true, 0);
            return nullptr;
        }
        elim_branch(n, t, true);
        iterator* it = alloc(iterator, n, t);
        out = eq_tree::edge("power-split-elim:<", t.m_dep, true, 0);
        return it;
    }

    // -- power_fixed_exp --

    scoped_ptr<eq_tree::split_iterator_i> power_fixed_exp::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& sf = ac.solver_facet_ref();
        for (unsigned i = 0; i < f.powers().size(); ++i) {
            str_power const& p = f.powers()[i];
            rational v;
            if (!p.active() || !p.m_axiomatized || a.is_numeral(p.m_n) || !sf.value(p.m_n, v) || v > rational(1024))
                continue;
            eq_tree::dep_tracker core = nullptr;
            if (sf.implies(m.mk_eq(p.m_n, a.mk_numeral(v, true)), &core) != l_true)
                continue;
            eq_tree::dep_tracker dep = f.dm().mk_join(p.m_dep, core);
            expr_ref_vector repl(m);
            if (v.is_pos())
                u.str.get_concat_units(mk_power_unfold(u, m, p.m_s.get(), v.get_unsigned()), repl);
            sf.add_constraint(m.mk_eq(p.m_n, a.mk_numeral(v, true)), core, p.m_proof, symbol("power-implied-fixed-exponent"));
            broadcast_subst(n, p.m_e.get(), repl, dep, p.m_proof, symbol("power-implied-exponent-unfold"));
            has_more = true;
            committed = true;
            m_stats.m_num_splits++;
            out = eq_tree::edge("power-fixed-exp", dep, true, 0);
            return nullptr;
        }
        return nullptr;
    }

    // -- power_peel --

    // Locate a power at a directional end of an equation, opposite any
    // other token. Skip powers whose exponent is already a numeral.
    static bool find_peel_trigger(power_facet const& f, eq_facet const& ef, arith_util& a,
                                  unsigned& eq_idx, bool& fwd, unsigned& pow_idx, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (!eq.active() || eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool front : {true, false}) {
                expr* lh = front ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rh = front ? eq.m_rhs[0] : eq.m_rhs.back();
                if (lh == rh)
                    continue;
                for (expr* tok : {lh, rh}) {
                    unsigned pidx;
                    rational v;
                    if (!is_power_token(f, tok, pidx) || a.is_numeral(f.powers()[pidx].m_n, v))
                        continue;
                    eq_idx = i;
                    fwd = front;
                    pow_idx = pidx;
                    dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    bool power_peel::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto ac = get_ambient(m_n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();
        if (m_pow_idx >= f.powers().size() || !f.powers()[m_pow_idx].active()
            || m_eq_idx >= ef.equations().size() || !ef.equations()[m_eq_idx].active())
            return false;
        str_power p = f.powers()[m_pow_idx]; // copy: broadcast_subst may reallocate m_pows

        // Branch 2: `n >= 1`, so `U^n := U . U^(n-1)`.
        expr_ref n_minus_1 = mk_exp(m, a.mk_sub(p.m_n, a.mk_int(1)));
        expr_ref nested_pow(u.str.mk_power(p.m_s, n_minus_1), m);
        expr_ref_vector base(m), repl(m);
        u.str.get_concat_units(p.m_s, base);
        if (m_fwd) { repl.append(base); repl.push_back(nested_pow); }
        else       { repl.push_back(nested_pow); repl.append(base); }
        ac.solver_facet_ref().add_constraint(a.mk_ge(p.m_n, a.mk_int(1)), m_dep, nullptr, symbol("power-peel-positive-guard"));
        broadcast_subst(m_n, p.m_e, repl, m_dep, p.m_proof, symbol("power-peel-positive-unfold"));

        out = eq_tree::edge("power-peel:n>=1", m_dep, false, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_peel::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();

        unsigned eq_idx, pow_idx;
        bool fwd;
        eq_tree::dep_tracker dep;
        if (!find_peel_trigger(f, ef, a, eq_idx, fwd, pow_idx, dep))
            return nullptr;
        has_more = true;
        str_power p = f.powers()[pow_idx]; // copy: broadcast_subst may reallocate m_pows

        // Branch 1: `n <= 0`, so `U^n := epsilon`.
        unfold_empty(n, f, pow_idx, dep);

        iterator* it = alloc(iterator, n, eq_idx, fwd, pow_idx, dep, m, u, a);
        out = eq_tree::edge("power-peel:n<=0", dep, true, 0);
        committed = true;
        m_stats.m_num_splits++;
        return it;
    }

    // -- power_var_decompose --

    // Locate a variable-vs-power decomposition trigger. Skip powers whose
    // exponent is already a numeral.
    static bool find_var_decompose_trigger(power_facet const& f, eq_facet const& ef, arith_util& a, seq_util& u,
                                            unsigned& pow_idx, expr*& var, bool& fwd, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (!eq.active())
                continue;
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool lhs_pow : {true, false}) {
                expr_ref_vector const& pow_side = lhs_pow ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& var_side = lhs_pow ? eq.m_rhs : eq.m_lhs;
                for (bool f2 : {true, false}) {
                    expr* pow_tok = f2 ? pow_side[0] : pow_side.back();
                    expr* var_tok = f2 ? var_side[0] : var_side.back();
                    unsigned pidx;
                    if (!is_power_token(f, pow_tok, pidx))
                        continue;
                    bool is_var = !u.str.is_unit(var_tok) && !u.str.is_power(var_tok);
                    if (!is_var)
                        continue;
                    rational v;
                    if (a.is_numeral(f.powers()[pidx].m_n, v))
                        continue; // resolved directly by power_propagation
                    // Cuts only at token boundaries: complete only for character bases.
                    expr_ref_vector base_toks(f.get_manager());
                    u.str.get_concat_units(f.powers()[pidx].m_s.get(), base_toks);
                    if (!all_of(base_toks, [&](expr* t) { return u.str.is_unit(t); }))
                        continue;
                    pow_idx = pidx;
                    var = var_tok;
                    fwd = f2;
                    dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    bool power_var_decompose::iterator::next(eq_tree::edge& out) {
        auto ac = get_ambient(m_n);
        auto& sf = ac.solver_facet_ref();
        auto& f = ac.power_facet_ref();

        while (m_pos < m_base_toks.size()) {
            unsigned i = m_pos++;
            expr* tok = m_base_toks[i].get();

            // Skip a boundary already covered by the preceding power token.
            unsigned prev_pidx;
            if (i > 0 && is_power_token(f, m_base_toks[i - 1].get(), prev_pidx))
                continue;
            unsigned pidx;
            if (!f.find_power(m_pow_e, pidx))
                return false;
            expr* n_exp = f.powers()[pidx].m_n.get();
            expr_ref pow_m(u.str.mk_power(f.powers()[pidx].m_s, m_fresh_m), m); // U^m, v := U^m . prefix

            // Build the replacement in the direction `v` faces `U^n`.
            expr_ref_vector prefix(m);
            for (unsigned j = 0; j < i; ++j)
                prefix.push_back(m_base_toks[j].get());

            unsigned tok_pidx;
            expr* fresh_inner_m = nullptr;
            expr* inner_exp = nullptr;
            expr_ref suffix_tok(m);
            if (is_power_token(f, tok, tok_pidx)) {
                str_power const& q = f.powers()[tok_pidx];
                inner_exp = q.m_n.get();
                fresh_inner_m = ac.mk_fresh_var("power-var-decompose-m", a.mk_int(), { m_var.get() });
                suffix_tok = expr_ref(u.str.mk_power(q.m_s.get(), fresh_inner_m), m);
            }
            else
                suffix_tok = expr_ref(tok, m);

            expr_ref_vector repl(m);
            if (m_fwd) {
                repl.push_back(pow_m.get());
                for (unsigned j = 0; j < prefix.size(); ++j) repl.push_back(prefix[j].get());
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
            } else {
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
                for (unsigned j = prefix.size(); j-- > 0; ) repl.push_back(prefix[j].get());
                repl.push_back(pow_m.get());
            }
            // In the plain-token case the current token is absorbed into the
            // repeated base and is not appended again literally.

            broadcast_subst(m_n, m_var.get(), repl, m_dep, nullptr, symbol("power-variable-prefix-cut"));
            sf.add_constraint(a.mk_ge(m_fresh_m.get(), a.mk_int(0)), m_dep, nullptr, symbol("power-variable-prefix-exponent"));
            sf.add_constraint(a.mk_ge(n_exp, a.mk_add(m_fresh_m.get(), a.mk_int(1))), m_dep, nullptr, symbol("power-variable-proper-prefix-guard")); // v is a proper prefix of U^n
            if (fresh_inner_m) {
                sf.add_constraint(a.mk_ge(fresh_inner_m, a.mk_int(0)), m_dep, nullptr, symbol("power-variable-inner-prefix-exponent"));
                sf.add_constraint(a.mk_ge(inner_exp, fresh_inner_m), m_dep, nullptr, symbol("power-variable-inner-prefix-bound"));
            }
            out = eq_tree::edge("power-var-decompose:pos", m_dep, true, 0);
            return true;
        }

        if (!m_extend_done) {
            m_extend_done = true;
            // Final non-progress branch: `v` extends past the whole power.
            sort* s = m_var.get()->get_sort();
            expr* vp = ac.mk_fresh_var(m_fwd ? "power-var-decompose-forward-tail" : "power-var-decompose-backward-tail",
                                       s, { m_var.get(), m_pow_e.get() });
            expr_ref_vector repl(m);
            if (m_fwd) { repl.push_back(m_pow_e.get()); repl.push_back(vp); }
            else       { repl.push_back(vp); repl.push_back(m_pow_e.get()); }
            broadcast_subst(m_n, m_var.get(), repl, m_dep, nullptr, symbol("power-variable-extension"));
            sf.add_constraint(a.mk_ge(u.str.mk_length(vp), a.mk_int(0)), m_dep, nullptr, symbol("power-variable-extension-length"));
            out = eq_tree::edge("power-var-decompose:extend", m_dep, false, 0);
            return true;
        }
        return false;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_var_decompose::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();

        unsigned pow_idx;
        expr* var = nullptr;
        bool fwd;
        eq_tree::dep_tracker dep;
        if (!find_var_decompose_trigger(f, ef, a, u, pow_idx, var, fwd, dep))
            return nullptr;

        str_power const& p = f.powers()[pow_idx];
        expr_ref_vector base_toks(m);
        u.str.get_concat_units(p.m_s.get(), base_toks);
        if (base_toks.empty())
            return nullptr;
        if (!fwd) {
            // Store `base_toks` in the direction `v` faces `U^n`.
            expr_ref_vector rev(m);
            for (unsigned j = base_toks.size(); j-- > 0; ) rev.push_back(base_toks[j].get());
            base_toks = std::move(rev);
        }

        expr* fresh_m = ac.mk_fresh_var("power-var-decompose-n", a.mk_int(), { var });
        has_more = true;

        iterator* it = alloc(iterator, n, var, p.m_e.get(), base_toks, fresh_m, fwd, dep, m, u, a);
        // The iterator offers the first branch itself; every decomposition
        // position has the same shape.
        eq_tree::edge first;
        if (!it->next(first)) {
            dealloc(it);
            return nullptr;
        }
        out = first;
        committed = true;
        m_stats.m_num_splits++;
        return it;
    }

    // -- power_gpower_intro --

    // Is `e` a substitutable variable token (neither a unit nor a power)?
    static bool is_gpower_var(seq_util& u, expr* e) {
        return !u.str.is_unit(e) && !u.str.is_power(e);
    }

    // Locate a self-cycle trigger for gpower introduction. `ground_prefix`
    // is returned in the direction `v` faces the cycle.
    static bool find_gpower_trigger(eq_facet const& ef, seq_util& u, ast_manager& m,
                                     unsigned& eq_idx, bool& fwd,
                                     expr_ref_vector& ground_prefix, expr*& var, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (!eq.active())
                continue;
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool f2 : {true, false}) {
                expr* lhead = f2 ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rhead = f2 ? eq.m_rhs[0] : eq.m_rhs.back();
                bool lhead_is_var = is_gpower_var(u, lhead);
                bool rhead_is_var = is_gpower_var(u, rhead);

                // Orientation 1: rhs head is the target variable; scan lhs.
                if (rhead_is_var && !lhead_is_var) {
                    expr_ref_vector prefix(m);
                    expr* target = nullptr;
                    unsigned sz = eq.m_lhs.size();
                    for (unsigned k = 0; k < sz; ++k) {
                        expr* t = f2 ? eq.m_lhs[k] : eq.m_lhs[sz - 1 - k];
                        if (is_gpower_var(u, t)) { target = t; break; }
                        prefix.push_back(t);
                    }
                    if (target && !prefix.empty() && target == rhead) {
                        eq_idx = i;
                        fwd = f2;
                        ground_prefix = std::move(prefix);
                        var = rhead;
                        dep = eq.m_dep;
                        return true;
                    }
                }

                // Orientation 2: symmetric case.
                if (lhead_is_var && !rhead_is_var) {
                    expr_ref_vector prefix(m);
                    expr* target = nullptr;
                    unsigned sz = eq.m_rhs.size();
                    for (unsigned k = 0; k < sz; ++k) {
                        expr* t = f2 ? eq.m_rhs[k] : eq.m_rhs[sz - 1 - k];
                        if (is_gpower_var(u, t)) { target = t; break; }
                        prefix.push_back(t);
                    }
                    if (target && !prefix.empty() && target == lhead) {
                        eq_idx = i;
                        fwd = f2;
                        ground_prefix = std::move(prefix);
                        var = lhead;
                        dep = eq.m_dep;
                        return true;
                    }
                }
            }
        }
        return false;
    }

    bool power_gpower_intro::iterator::next(eq_tree::edge& out) {
        auto ac = get_ambient(m_n);
        auto& sf = ac.solver_facet_ref();
        auto& f = ac.power_facet_ref();

        while (m_pos < m_base_toks.size()) {
            unsigned i = m_pos++;
            expr* tok = m_base_toks[i].get();

            // Skip a boundary already covered by the preceding power token.
            unsigned prev_pidx;
            if (i > 0 && is_power_token(f, m_base_toks[i - 1].get(), prev_pidx))
                continue;

            expr_ref_vector prefix(m);
            for (unsigned j = 0; j < i; ++j)
                prefix.push_back(m_base_toks[j].get());

            unsigned tok_pidx;
            expr* fresh_inner_m = nullptr;
            expr* inner_exp = nullptr;
            expr_ref suffix_tok(m);
            if (is_power_token(f, tok, tok_pidx)) {
                str_power const& q = f.powers()[tok_pidx];
                inner_exp = q.m_n.get();
                fresh_inner_m = ac.mk_fresh_var("power-gpower-intro-m", a.mk_int(), { m_var.get() });
                suffix_tok = expr_ref(u.str.mk_power(q.m_s.get(), fresh_inner_m), m);
            }
            else
                suffix_tok = expr_ref(tok, m);

            expr_ref_vector repl(m);
            if (m_fwd) {
                repl.push_back(m_pow_e.get());
                for (unsigned j = 0; j < prefix.size(); ++j) repl.push_back(prefix[j].get());
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
            } else {
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
                for (unsigned j = prefix.size(); j-- > 0; ) repl.push_back(prefix[j].get());
                repl.push_back(m_pow_e.get());
            }

            broadcast_subst(m_n, m_var.get(), repl, m_dep, nullptr, symbol("power-ground-prefix-cut"));
            sf.add_constraint(a.mk_ge(m_fresh_n.get(), a.mk_int(0)), m_dep, nullptr, symbol("power-ground-prefix-exponent"));
            if (fresh_inner_m) {
                sf.add_constraint(a.mk_ge(fresh_inner_m, a.mk_int(0)), m_dep, nullptr, symbol("power-ground-inner-prefix-exponent"));
                sf.add_constraint(a.mk_ge(inner_exp, fresh_inner_m), m_dep, nullptr, symbol("power-ground-inner-prefix-bound"));
            }
            out = eq_tree::edge("power-gpower-intro:pos", m_dep, true, 0);
            return true;
        }
        return false;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_gpower_intro::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& ef = ac.eq_facet_ref();

        unsigned eq_idx;
        bool fwd;
        expr_ref_vector ground_prefix_orig(m);
        expr* var = nullptr;
        eq_tree::dep_tracker dep;
        if (!find_gpower_trigger(ef, u, m, eq_idx, fwd, ground_prefix_orig, var, dep))
            return nullptr;

        // Compress the ground prefix to its minimal repeating period.
        unsigned gn = ground_prefix_orig.size();
        unsigned period = gn;
        for (unsigned p = 1; p <= gn / 2; ++p) {
            if (gn % p != 0)
                continue;
            bool match = true;
            for (unsigned i = p; i < gn && match; ++i)
                match = ground_prefix_orig[i].get() == ground_prefix_orig[i % p].get();
            if (match) { period = p; break; }
        }
        expr_ref_vector compressed(m);
        for (unsigned i = 0; i < period; ++i)
            compressed.push_back(ground_prefix_orig[i].get());

        // If the compressed prefix is a single power token, unwrap it to
        // its own base tokens to avoid a nested power-of-power.
        if (compressed.size() == 1) {
            unsigned pidx;
            if (is_power_token(f, compressed[0].get(), pidx)) {
                expr_ref_vector inner_base_toks(m);
                u.str.get_concat_units(f.powers()[pidx].m_s.get(), inner_base_toks);
                if (!inner_base_toks.empty()) {
                    expr_ref_vector rev(m);
                    if (fwd)
                        for (unsigned j = 0; j < inner_base_toks.size(); ++j) rev.push_back(inner_base_toks[j].get());
                    else
                        for (unsigned j = inner_base_toks.size(); j-- > 0; ) rev.push_back(inner_base_toks[j].get());
                    compressed = std::move(rev);
                }
            }
        }
        if (compressed.empty())
            return nullptr;

        // Build the power base in natural left-to-right order.
        expr_ref_vector natural(m);
        if (fwd)
            for (unsigned j = 0; j < compressed.size(); ++j) natural.push_back(compressed[j].get());
        else
            for (unsigned j = compressed.size(); j-- > 0; ) natural.push_back(compressed[j].get());

        expr_ref base_str(natural[0].get(), m);
        for (unsigned j = 1; j < natural.size(); ++j)
            base_str = expr_ref(u.str.mk_concat(base_str.get(), natural[j].get()), m);

        expr* fresh_n = ac.mk_fresh_var("power-gpower-intro-n", a.mk_int(), { var });
        expr_ref power_expr(u.str.mk_power(base_str.get(), fresh_n), m);

        // Register the fresh power obligation shared by every branch.
        proof_ref power_pr(m);
        if (f.dm().proofs_enabled()) {
            str_power fresh_power(m, power_expr, base_str, fresh_n);
            power_pr = f.dm().mk_proof(symbol("power-ground-prefix-definition"), fresh_power.fact(u), { nullptr });
        }
        f.add_power(power_expr.get(), base_str.get(), fresh_n, dep, power_pr, symbol("power-ground-prefix-definition"));
        has_more = true;

        iterator* it = alloc(iterator, n, var, power_expr.get(), compressed, fresh_n, fwd, dep, m, u, a);
        eq_tree::edge first;
        if (!it->next(first)) {
            dealloc(it);
            return nullptr;
        }
        out = first;
        committed = true;
        m_stats.m_num_splits++;
        return it;
    }

} // namespace seq
