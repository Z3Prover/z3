/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Parikh abstraction for word equations, see seq_parikh.h

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/rewriter/seq_parikh.h"
#include "ast/ast_util.h"

namespace seq {

parikh::parikh(ast_manager& _m, config const& c):
    m(_m), m_util(_m), m_autil(_m), m_pinned(_m) {
    updt_config(c);
}

void parikh::updt_config(config const& c) {
    m_config = c;
    // the boundary encoding is exact only up to factors of length two
    if (m_config.m_k > 2)
        m_config.m_k = 2;
    if (m_config.m_n == 0)
        m_config.m_n = 1;
}

expr_ref parikh::mk_sk(char const* name, std::initializer_list<expr*> args, sort* range) {
    return expr_ref(m_util.mk_skolem(symbol(name), args.size(), args.begin(), range), m);
}

expr_ref parikh::num(int i) {
    return expr_ref(m_autil.mk_int(i), m);
}

expr_ref parikh::sum(expr_ref_vector const& args) {
    if (args.empty())
        return num(0);
    return expr_ref(m_autil.mk_add(args), m);
}

expr_ref parikh::conj(expr_ref_vector const& args) {
    expr_ref_vector as(m);
    for (expr* e : args) {
        if (m.is_false(e))
            return expr_ref(m.mk_false(), m);
        if (!m.is_true(e))
            as.push_back(e);
    }
    return mk_and(as);
}

void parikh::push_impl(expr_ref_vector& defs, expr* cond, expr* e) {
    if (m.is_false(cond))
        return;
    defs.push_back(m.is_true(cond) ? e : m.mk_implies(cond, e));
}

// true the first time a symbol is seen, so that its definition is emitted once
bool parikh::fresh(expr* key) {
    if (m_defined.contains(key))
        return false;
    m_defined.insert(key);
    m_pinned.push_back(key);
    return true;
}

rational parikh::num_grams(unsigned level) const {
    // There is one coordinate for every word in the projected alphabet A of this length:
    // |A^level| = |A|^level.  See Eisenhofer et al., Section 6.
    return power(rational(m_p), level);
}

unsigned parikh::char_index(unsigned ch) const {
    for (unsigned i = 0; i < m_chars.size(); ++i) {
        if (m_chars[i] == ch)
            return i;
    }
    return m_chars.size();
}

bool parikh::has_char(expr_ref_vector const& side) const {
    return any_of(side, [&](expr* e) {
        expr* c = nullptr;
        return m_util.str.is_unit(e, c) && m_util.is_const_char(c);
    });
}

void parikh::collect_chars(expr_ref_vector const& side) {
    expr* c = nullptr;
    unsigned ch = 0;
    for (expr* e : side) {
        if (!m_util.str.is_unit(e, c) || !m_util.is_const_char(c, ch))
            continue;
        if (m_chars.size() < m_config.m_max_chars && char_index(ch) == m_chars.size())
            m_chars.push_back(ch);
    }
}

void parikh::collect_blocks(expr_ref_vector const& side, vector<block>& blocks) {
    expr* c = nullptr;
    unsigned ch = 0;
    for (expr* e : side) {
        block b;
        b.m_e = e;
        b.m_unit = m_util.str.is_unit(e, c);
        // a character beyond the projection bound falls into the catch-all class, which is
        // still a letter of the abstract alphabet
        if (b.m_unit && m_util.is_const_char(c, ch)) {
            b.m_is_char = true;
            b.m_char = char_index(ch);
        }
        blocks.push_back(b);
    }
}

// pairs of blocks that can end up next to each other: everything in between has to be able
// to be empty, and a unit never is
void parikh::adjacent(vector<block> const& blocks, svector<block_pair>& out) {
    for (unsigned i = 0; i < blocks.size(); ++i) {
        for (unsigned j = i + 1; j < blocks.size(); ++j) {
            out.push_back(block_pair(i, j));
            if (blocks[j].m_unit)
                break;
        }
    }
}

expr_ref parikh::len(block const& b) {
    if (b.m_unit)
        return num(1);
    return expr_ref(m_util.str.mk_length(b.m_e), m);
}

expr_ref parikh::is_empty(block const& b) {
    if (b.m_unit)
        return expr_ref(m.mk_false(), m);
    auto length = len(b);
    auto zero = num(0);
    return expr_ref(m.mk_eq(length.get(), zero.get()), m);
}

expr_ref parikh::first(block const& b, unsigned c) {
    if (b.m_is_char)
        return expr_ref(b.m_char == c ? m.mk_true() : m.mk_false(), m);
    auto c_ref = num(c);
    auto p_ref = num(m_p);
    return mk_sk("seq.parikh.first", { b.m_e, c_ref.get(), p_ref.get() }, m.mk_bool_sort());
}

expr_ref parikh::last(block const& b, unsigned c) {
    if (b.m_is_char)
        return expr_ref(b.m_char == c ? m.mk_true() : m.mk_false(), m);
    auto c_ref = num(c);
    auto p_ref = num(m_p);
    return mk_sk("seq.parikh.last", { b.m_e, c_ref.get(), p_ref.get() }, m.mk_bool_sort());
}

expr_ref parikh::count(block const& b, unsigned level, unsigned gram, unsigned r) {
    if (b.m_is_char)
        return num(level == 1 && gram == b.m_char && r == 0 ? 1 : 0);
    auto level_ref = num(level);
    auto gram_ref = num(gram);
    auto r_ref = num(r);
    auto mod_ref = num(m_mod);
    auto p_ref = num(m_p);
    return mk_sk("seq.parikh", { b.m_e, level_ref.get(), gram_ref.get(), r_ref.get(), mod_ref.get(), p_ref.get() }, m_autil.mk_int());
}

// The number of length-k windows of w is max(0, |w| - k + 1);
// this is the marginal sum of its generalized Parikh image.
expr_ref parikh::window(block const& b, unsigned level, expr_ref_vector& defs) {
    if (level == 1)
        return len(b);
    if (b.m_unit)
        return num(0);
    auto level_ref = num(level);
    expr_ref w = mk_sk("seq.parikh.w", { b.m_e, level_ref.get() }, m_autil.mk_int());
    if (fresh(w)) {
        auto length = len(b);
        auto zero = num(0);
        auto level_minus_one = num(level - 1);
        expr_ref fits(m_autil.mk_ge(length.get(), level_ref.get()), m);
        defs.push_back(m_autil.mk_ge(w.get(), zero.get()));
        push_impl(defs, fits.get(), m.mk_eq(w.get(), m_autil.mk_sub(length.get(), level_minus_one.get())));
        push_impl(defs, mk_not(m, fits), m.mk_eq(w.get(), zero.get()));
    }
    return w;
}

// 1 if cond holds, 0 otherwise; keying on cond lets equal conditions share the variable
expr_ref parikh::indicator(expr* cond, expr_ref_vector& defs) {
    if (m.is_true(cond))
        return num(1);
    if (m.is_false(cond))
        return num(0);
    expr_ref v = mk_sk("seq.parikh.ind", { cond }, m_autil.mk_int());
    if (fresh(v)) {
        auto one = num(1);
        auto zero = num(0);
        defs.push_back(m.mk_implies(cond, m.mk_eq(v.get(), one.get())));
        defs.push_back(m.mk_implies(mk_not(m, cond), m.mk_eq(v.get(), zero.get())));
    }
    return v;
}

// position clock: the length of a prefix of a side, taken modulo m_mod
expr_ref parikh::clock(expr* prefix_len, expr_ref_vector& defs) {
    if (m_mod == 1)
        return num(0);
    auto mod_ref = num(m_mod);
    expr_ref v = mk_sk("seq.parikh.clk", { prefix_len, mod_ref.get() }, m_autil.mk_int());
    if (fresh(v)) {
        auto zero = num(0);
        auto mod_minus_one = num(m_mod - 1);
        expr_ref q = mk_sk("seq.parikh.clkq", { prefix_len, mod_ref.get() }, m_autil.mk_int());
        defs.push_back(m_autil.mk_ge(v.get(), zero.get()));
        defs.push_back(m_autil.mk_le(v.get(), mod_minus_one.get()));
        defs.push_back(m_autil.mk_ge(q.get(), zero.get()));
        defs.push_back(m.mk_eq(prefix_len, m_autil.mk_add(m_autil.mk_mul(mod_ref.get(), q.get()), v.get())));
    }
    return v;
}

expr_ref parikh::clock_is(expr* clk, unsigned v) {
    if (m_mod == 1)
        return expr_ref(v == 0 ? m.mk_true() : m.mk_false(), m);
    auto v_ref = num(v);
    return expr_ref(m.mk_eq(clk, v_ref.get()), m);
}

// a block has a first and a last letter exactly when it is non-empty
void parikh::define_letters(block const& b, expr_ref_vector& defs) {
    if (b.m_is_char || !fresh(first(b, 0)))
        return;

    expr_ref_vector fs(m), ls(m);
    for (unsigned c = 0; c < m_p; ++c) {
        fs.push_back(first(b, c));
        ls.push_back(last(b, c));
    }
    for (unsigned c = 0; c < m_p; ++c) {
        for (unsigned d = c + 1; d < m_p; ++d) {
            defs.push_back(m.mk_or(m.mk_not(fs.get(c)), m.mk_not(fs.get(d))));
            defs.push_back(m.mk_or(m.mk_not(ls.get(c)), m.mk_not(ls.get(d))));
        }
    }
    expr_ref emp = is_empty(b);
    defs.push_back(m.mk_iff(emp, mk_not(m, mk_or(fs))));
    defs.push_back(m.mk_iff(emp, mk_not(m, mk_or(ls))));
    expr_ref one(m);
    if (b.m_unit)
        one = m.mk_true();
    else {
        auto length = len(b);
        auto numeral_one = num(1);
        one = m.mk_eq(length.get(), numeral_one.get());
    }
    for (unsigned c = 0; c < m_p; ++c) {
        push_impl(defs, one, m.mk_iff(fs.get(c), ls.get(c)));
    }
}

// For O[k,n](w)[u,r] = |{ i : w[i..i+k) = u, i = r (mod n) }|,
// summing over u gives the number of length-k windows at residue r.
void parikh::define_level(block const& b, unsigned level, expr_ref_vector& defs) {
    if (b.m_is_char || !fresh(count(b, level, 0, 0)))
        return;

    // w = m_mod * q + rem, so residue r covers q windows, and one more when r < rem
    expr_ref w = window(b, level, defs);
    expr_ref q = w, rem(m);
    auto zero = num(0);
    if (m_mod > 1) {
        auto level_ref = num(level);
        auto mod_ref = num(m_mod);
        auto mod_minus_one = num(m_mod - 1);
        q = mk_sk("seq.parikh.q", { b.m_e, level_ref.get(), mod_ref.get() }, m_autil.mk_int());
        rem = mk_sk("seq.parikh.rem", { b.m_e, level_ref.get(), mod_ref.get() }, m_autil.mk_int());
        defs.push_back(m_autil.mk_ge(q.get(), zero.get()));
        defs.push_back(m_autil.mk_ge(rem.get(), zero.get()));
        defs.push_back(m_autil.mk_le(rem.get(), mod_minus_one.get()));
        defs.push_back(m.mk_eq(w.get(), m_autil.mk_add(m_autil.mk_mul(mod_ref.get(), q.get()), rem.get())));
    }

    for (unsigned r = 0; r < m_mod; ++r) {
        expr_ref_vector row(m);
        rational factor_count = num_grams(level);
        if (factor_count > rational(m_config.m_max_size))
            return;
        unsigned gram_count = factor_count.get_unsigned();
        for (unsigned g = 0; g < gram_count; ++g) {
            expr_ref c = count(b, level, g, r);
            defs.push_back(m_autil.mk_ge(c.get(), zero.get()));
            row.push_back(c);
        }
        expr_ref extra = zero;
        if (m_mod > 1) {
            auto r_plus_one = num(r + 1);
            extra = indicator(m_autil.mk_ge(rem.get(), r_plus_one.get()), defs);
        }
        defs.push_back(m.mk_eq(sum(row), m_autil.mk_add(q, extra)));
    }
}

// The de-Bruijn flow equations project pair counts onto letter counts:
// sum_d O[2,n](w)[cd,r] = O[1,n](w)[c,r] - [c is the last letter at r],
// with the dual equation for incoming pairs and the first letter.
void parikh::define_flow(block const& b, expr_ref_vector& defs) {
    if (b.m_is_char || m_config.m_k < 2)
        return;
    auto mod_ref = num(m_mod);
    auto p_ref = num(m_p);
    auto flow = mk_sk("seq.parikh.flow", { b.m_e, mod_ref.get(), p_ref.get() }, m.mk_bool_sort());
    if (!fresh(flow))
        return;

    expr_ref rem(m);
    if (m_mod > 1) {
        auto one = num(1);
        rem = mk_sk("seq.parikh.rem", { b.m_e, one.get(), mod_ref.get() }, m_autil.mk_int());
    }

    for (unsigned c = 0; c < m_p; ++c) {
        for (unsigned r = 0; r < m_mod; ++r) {
            expr_ref_vector right(m), left(m);
            for (unsigned d = 0; d < m_p; ++d) {
                right.push_back(count(b, 2, c + d * m_p, r));
                left.push_back(count(b, 2, d + c * m_p, (r + m_mod - 1) % m_mod));
            }
            // the last letter opens the last window, at residue (len - 1) mod m_mod
            expr_ref at_end = last(b, c);
            if (m_mod > 1) {
                auto residue = num((r + 1) % m_mod);
                at_end = m.mk_and(at_end, m.mk_eq(rem.get(), residue.get()));
            }
            defs.push_back(m.mk_eq(sum(right), m_autil.mk_sub(count(b, 1, c, r), indicator(at_end, defs))));

            // the first letter opens the first window, at residue 0
            expr_ref at_start = r == 0 ? first(b, c) : expr_ref(m.mk_false(), m);
            defs.push_back(m.mk_eq(sum(left), m_autil.mk_sub(count(b, 1, c, r), indicator(at_start, defs))));
        }
    }
}

void parikh::define_block(block const& b, expr_ref_vector& defs) {
    define_letters(b, defs);
    for (unsigned level = 1; level <= m_config.m_k; ++level) {
        define_level(b, level, defs);
    }
    define_flow(b, defs);
}

// Concatenation rotates each block image by the preceding length:
// O[k,n](xy)[u,r] = O[k,n](x)[u,r] + O[k,n](y)[u,r-|x|] + boundary[u,r].
// out[gram * m_mod + r] stores this coordinate.
void parikh::totals(vector<block> const& blocks, unsigned level, expr_ref_vector& out, expr_ref_vector& defs) {
    vector<expr_ref_vector> acc;
    rational factor_count = num_grams(level);
    if (factor_count > rational(m_config.m_max_size))
        return;
    unsigned gram_count = factor_count.get_unsigned();
    rational total = factor_count * rational(m_mod);
    if (total > rational(m_config.m_max_counters))
        return;
    for (unsigned i = 0; i < total.get_unsigned(); ++i) {
        acc.push_back(expr_ref_vector(m));
    }

    // clocks[i] is the clock reached in front of block i
    expr_ref_vector lens(m), clocks(m);
    auto zero = num(0);
    clocks.push_back(clock(zero.get(), defs));
    for (block const& b : blocks) {
        lens.push_back(len(b));
        clocks.push_back(clock(sum(lens), defs));
    }

    for (unsigned i = 0; i < blocks.size(); ++i) {
        block const& b = blocks[i];
        expr* pre = clocks.get(i);
        if (b.m_is_char) {
            if (level == 1) {
                for (unsigned r = 0; r < m_mod; ++r) {
                    acc[b.m_char * m_mod + r].push_back(indicator(clock_is(pre, r), defs));
                }
            }
            continue;
        }
        for (unsigned g = 0; g < gram_count; ++g) {
            if (m_mod == 1) {
                acc[g].push_back(count(b, level, g, 0));
                continue;
            }
            for (unsigned r = 0; r < m_mod; ++r) {
                // The clock is an argument, so positions whose clocks agree share the
                // rotation by congruence.  That is wanted within one observer, but clocks of
                // different moduli can agree by accident, hence m_mod in the key.
                auto level_ref = num(level);
                auto gram_ref = num(g);
                auto r_ref = num(r);
                auto mod_ref = num(m_mod);
                auto p_ref = num(m_p);
                expr_ref rot = mk_sk("seq.parikh.rot", { b.m_e, level_ref.get(), gram_ref.get(), r_ref.get(), pre, mod_ref.get(), p_ref.get() }, m_autil.mk_int());
                if (fresh(rot)) {
                    for (unsigned v = 0; v < m_mod; ++v) {
                        push_impl(defs, clock_is(pre, v), m.mk_eq(rot, count(b, level, g, (r + m_mod - v) % m_mod)));
                    }
                }
                acc[g * m_mod + r].push_back(rot);
            }
        }
    }

    // factors straddling a boundary between two blocks that can be adjacent
    if (level == 2) {
        svector<block_pair> pairs;
        adjacent(blocks, pairs);
        for (auto const& p : pairs) {
            expr_ref_vector cnd(m);
            cnd.push_back(mk_not(m, is_empty(blocks[p.first])));
            cnd.push_back(mk_not(m, is_empty(blocks[p.second])));
            for (unsigned t = p.first + 1; t < p.second; ++t) {
                cnd.push_back(is_empty(blocks[t]));
            }
            expr_ref gap = conj(cnd);
            for (unsigned c = 0; c < m_p; ++c) {
                expr_ref lc = last(blocks[p.first], c);
                if (m.is_false(lc))
                    continue;
                for (unsigned d = 0; d < m_p; ++d) {
                    expr_ref fd = first(blocks[p.second], d);
                    if (m.is_false(fd))
                        continue;
                    for (unsigned r = 0; r < m_mod; ++r) {
                        // the factor opens on the last letter of the first block, one
                        // position before the clock that block leaves behind
                        expr_ref_vector at(m);
                        at.push_back(gap);
                        at.push_back(lc);
                        at.push_back(fd);
                        at.push_back(clock_is(clocks.get(p.first + 1), (r + 1) % m_mod));
                        acc[(c + d * m_p) * m_mod + r].push_back(indicator(conj(at), defs));
                    }
                }
            }
        }
    }

    for (auto const& v : acc) {
        out.push_back(sum(v));
    }
}

void parikh::add_observer(vector<block> const& l, vector<block> const& r, unsigned mod,
                                expr_ref_vector& defs, expr_ref_vector& eqs) {
    m_mod = mod;
    for (block const& b : l) {
        define_block(b, defs);
    }
    for (block const& b : r) {
        define_block(b, defs);
    }
    for (unsigned level = 1; level <= m_config.m_k; ++level) {
        expr_ref_vector tl(m), tr(m);
        totals(l, level, tl, defs);
        totals(r, level, tr, defs);
        SASSERT(tl.size() == tr.size());
        for (unsigned i = 0; i < tl.size(); ++i) {
            eqs.push_back(m.mk_eq(tl.get(i), tr.get(i)));
        }
    }
}

bool parikh::over_budget(vector<block> const& l, vector<block> const& r, unsigned_vector const& moduli) {
    svector<block_pair> pairs;
    adjacent(l, pairs);
    adjacent(r, pairs);
    rational blocks = rational(l.size()) + rational(r.size()) + rational(1);
    rational per_observer(0);
    for (unsigned level = 1; level <= m_config.m_k; ++level) {
        rational gram_count = num_grams(level);
        if (gram_count > rational(m_config.m_max_size))
            return true;
        per_observer += blocks * gram_count;
    }
    // the boundary factors dominate: one variable per pair of blocks and per factor
    if (m_config.m_k >= 2)
        per_observer += rational(pairs.size()) * num_grams(2);
    rational counters(0);
    for (unsigned n : moduli) {
        counters += per_observer * rational(n);
    }
    return counters > rational(m_config.m_max_counters);
}

bool parikh::operator()(expr_ref_vector const& l, expr_ref_vector const& r,
                              expr_ref_vector& defs, expr_ref_vector& eqs) {
    if (m_config.m_k == 0)
        return false;
    m_defined.reset();
    m_pinned.reset();
    // without a constant all factors fall into the catch-all class and the observations
    // collapse to the length equation, which the solver already has
    if (!has_char(l) && !has_char(r))
        return false;
    collect_chars(l);
    collect_chars(r);
    m_p = m_chars.size() + 1;

    vector<block> bl, br;
    collect_blocks(l, bl);
    collect_blocks(r, br);

    // a modulus is redundant as soon as a proper multiple of it is in range as well
    unsigned_vector moduli;
    for (unsigned n = 1; n <= m_config.m_n; ++n) {
        if (2 * n > m_config.m_n)
            moduli.push_back(n);
    }
    if (over_budget(bl, br, moduli))
        return false;

    for (unsigned n : moduli) {
        add_observer(bl, br, n, defs, eqs);
    }
    return !eqs.empty();
}

}
