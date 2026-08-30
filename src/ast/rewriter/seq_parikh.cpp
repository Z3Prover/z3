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

seq_parikh::seq_parikh(ast_manager& _m, config const& c):
    m(_m), m_util(_m), m_autil(_m), m_pinned(_m) {
    updt_config(c);
}

void seq_parikh::updt_config(config const& c) {
    m_config = c;
    // the boundary encoding is exact only up to factors of length two
    if (m_config.m_k > 2)
        m_config.m_k = 2;
    if (m_config.m_n == 0)
        m_config.m_n = 1;
}

expr_ref seq_parikh::mk_sk(char const* name, std::initializer_list<expr*> args, sort* range) {
    return expr_ref(m_util.mk_skolem(symbol(name), args.size(), args.begin(), range), m);
}

// numerals are handed around as raw pointers, so keep them alive for the whole encoding
expr* seq_parikh::num(int i) {
    expr* e = m_autil.mk_int(i);
    m_pinned.push_back(e);
    return e;
}

expr_ref seq_parikh::sum(expr_ref_vector const& args) {
    if (args.empty())
        return expr_ref(num(0), m);
    return expr_ref(m_autil.mk_add(args), m);
}

expr_ref seq_parikh::conj(expr_ref_vector const& args) {
    expr_ref_vector as(m);
    for (expr* e : args) {
        if (m.is_false(e))
            return expr_ref(m.mk_false(), m);
        if (!m.is_true(e))
            as.push_back(e);
    }
    return mk_and(as);
}

void seq_parikh::push_impl(expr_ref_vector& defs, expr* cond, expr* e) {
    if (m.is_false(cond))
        return;
    defs.push_back(m.is_true(cond) ? e : m.mk_implies(cond, e));
}

// true the first time a symbol is seen, so that its definition is emitted once
bool seq_parikh::fresh(expr* key) {
    if (m_defined.contains(key))
        return false;
    m_defined.insert(key);
    m_pinned.push_back(key);
    return true;
}

unsigned seq_parikh::num_grams(unsigned level) const {
    unsigned n = 1;
    for (unsigned i = 0; i < level; ++i) {
        n *= m_p;
    }
    return n;
}

unsigned seq_parikh::char_index(unsigned ch) const {
    for (unsigned i = 0; i < m_chars.size(); ++i) {
        if (m_chars[i] == ch)
            return i;
    }
    return m_chars.size();
}

bool seq_parikh::has_char(expr_ref_vector const& side) const {
    expr* c = nullptr;
    for (expr* e : side) {
        if (m_util.str.is_unit(e, c) && m_util.is_const_char(c))
            return true;
    }
    return false;
}

void seq_parikh::collect_chars(expr_ref_vector const& side) {
    expr* c = nullptr;
    unsigned ch = 0;
    for (expr* e : side) {
        if (!m_util.str.is_unit(e, c) || !m_util.is_const_char(c, ch))
            continue;
        if (char_index(ch) == m_chars.size() && m_chars.size() < m_config.m_max_chars)
            m_chars.push_back(ch);
    }
}

void seq_parikh::collect_blocks(expr_ref_vector const& side, vector<block>& blocks) {
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
void seq_parikh::adjacent(vector<block> const& blocks, svector<block_pair>& out) {
    for (unsigned i = 0; i < blocks.size(); ++i) {
        for (unsigned j = i + 1; j < blocks.size(); ++j) {
            out.push_back(block_pair(i, j));
            if (blocks[j].m_unit)
                break;
        }
    }
}

expr_ref seq_parikh::len(block const& b) {
    if (b.m_unit)
        return expr_ref(num(1), m);
    return expr_ref(m_util.str.mk_length(b.m_e), m);
}

expr_ref seq_parikh::is_empty(block const& b) {
    if (b.m_unit)
        return expr_ref(m.mk_false(), m);
    return expr_ref(m.mk_eq(len(b), num(0)), m);
}

expr_ref seq_parikh::first(block const& b, unsigned c) {
    if (b.m_is_char)
        return expr_ref(b.m_char == c ? m.mk_true() : m.mk_false(), m);
    return mk_sk("seq.parikh.first", { b.m_e, num(c), num(m_p) }, m.mk_bool_sort());
}

expr_ref seq_parikh::last(block const& b, unsigned c) {
    if (b.m_is_char)
        return expr_ref(b.m_char == c ? m.mk_true() : m.mk_false(), m);
    return mk_sk("seq.parikh.last", { b.m_e, num(c), num(m_p) }, m.mk_bool_sort());
}

expr_ref seq_parikh::count(block const& b, unsigned level, unsigned gram, unsigned r) {
    if (b.m_is_char)
        return expr_ref(num(level == 1 && gram == b.m_char && r == 0 ? 1 : 0), m);
    return mk_sk("seq.parikh", { b.m_e, num(level), num(gram), num(r), num(m_mod), num(m_p) }, m_autil.mk_int());
}

// number of factor windows of the given level: max(0, len - level + 1)
expr_ref seq_parikh::window(block const& b, unsigned level, expr_ref_vector& defs) {
    if (level == 1)
        return len(b);
    if (b.m_unit)
        return expr_ref(num(0), m);
    expr_ref w = mk_sk("seq.parikh.w", { b.m_e, num(level) }, m_autil.mk_int());
    if (fresh(w)) {
        expr_ref fits(m_autil.mk_ge(len(b), num(level)), m);
        defs.push_back(m_autil.mk_ge(w, num(0)));
        push_impl(defs, fits, m.mk_eq(w, m_autil.mk_sub(len(b), num(level - 1))));
        push_impl(defs, mk_not(m, fits), m.mk_eq(w, num(0)));
    }
    return w;
}

// 1 if cond holds, 0 otherwise; keying on cond lets equal conditions share the variable
expr_ref seq_parikh::indicator(expr* cond, expr_ref_vector& defs) {
    if (m.is_true(cond))
        return expr_ref(num(1), m);
    if (m.is_false(cond))
        return expr_ref(num(0), m);
    expr_ref v = mk_sk("seq.parikh.ind", { cond }, m_autil.mk_int());
    if (fresh(v)) {
        defs.push_back(m.mk_implies(cond, m.mk_eq(v, num(1))));
        defs.push_back(m.mk_implies(mk_not(m, cond), m.mk_eq(v, num(0))));
    }
    return v;
}

// position clock: the length of a prefix of a side, taken modulo m_mod
expr_ref seq_parikh::clock(expr* prefix_len, expr_ref_vector& defs) {
    if (m_mod == 1)
        return expr_ref(num(0), m);
    expr_ref v = mk_sk("seq.parikh.clk", { prefix_len, num(m_mod) }, m_autil.mk_int());
    if (fresh(v)) {
        expr_ref q = mk_sk("seq.parikh.clkq", { prefix_len, num(m_mod) }, m_autil.mk_int());
        defs.push_back(m_autil.mk_ge(v, num(0)));
        defs.push_back(m_autil.mk_le(v, num(m_mod - 1)));
        defs.push_back(m_autil.mk_ge(q, num(0)));
        defs.push_back(m.mk_eq(prefix_len, m_autil.mk_add(m_autil.mk_mul(num(m_mod), q), v)));
    }
    return v;
}

expr_ref seq_parikh::clock_is(expr* clk, unsigned v) {
    if (m_mod == 1)
        return expr_ref(v == 0 ? m.mk_true() : m.mk_false(), m);
    return expr_ref(m.mk_eq(clk, num(v)), m);
}

// a block has a first and a last letter exactly when it is non-empty
void seq_parikh::define_letters(block const& b, expr_ref_vector& defs) {
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
    expr_ref one = b.m_unit ? expr_ref(m.mk_true(), m) : expr_ref(m.mk_eq(len(b), num(1)), m);
    for (unsigned c = 0; c < m_p; ++c) {
        push_impl(defs, one, m.mk_iff(fs.get(c), ls.get(c)));
    }
}

// counters of one level, tied to the window count split over the residue classes
void seq_parikh::define_level(block const& b, unsigned level, expr_ref_vector& defs) {
    if (b.m_is_char || !fresh(count(b, level, 0, 0)))
        return;

    // w = m_mod * q + rem, so residue r covers q windows, and one more when r < rem
    expr_ref w = window(b, level, defs);
    expr_ref q = w, rem(m);
    if (m_mod > 1) {
        q = mk_sk("seq.parikh.q", { b.m_e, num(level), num(m_mod) }, m_autil.mk_int());
        rem = mk_sk("seq.parikh.rem", { b.m_e, num(level), num(m_mod) }, m_autil.mk_int());
        defs.push_back(m_autil.mk_ge(q, num(0)));
        defs.push_back(m_autil.mk_ge(rem, num(0)));
        defs.push_back(m_autil.mk_le(rem, num(m_mod - 1)));
        defs.push_back(m.mk_eq(w, m_autil.mk_add(m_autil.mk_mul(num(m_mod), q), rem)));
    }

    for (unsigned r = 0; r < m_mod; ++r) {
        expr_ref_vector row(m);
        for (unsigned g = 0; g < num_grams(level); ++g) {
            expr_ref c = count(b, level, g, r);
            defs.push_back(m_autil.mk_ge(c, num(0)));
            row.push_back(c);
        }
        expr_ref extra(num(0), m);
        if (m_mod > 1)
            extra = indicator(m_autil.mk_ge(rem, num(r + 1)), defs);
        defs.push_back(m.mk_eq(sum(row), m_autil.mk_add(q, extra)));
    }
}

// de-Bruijn flow: an occurrence of a letter extends to a two-letter factor unless it sits
// at the corresponding end of the block
void seq_parikh::define_flow(block const& b, expr_ref_vector& defs) {
    if (b.m_is_char || m_config.m_k < 2)
        return;
    if (!fresh(mk_sk("seq.parikh.flow", { b.m_e, num(m_mod), num(m_p) }, m.mk_bool_sort())))
        return;

    expr_ref rem(m);
    if (m_mod > 1)
        rem = mk_sk("seq.parikh.rem", { b.m_e, num(1), num(m_mod) }, m_autil.mk_int());

    for (unsigned c = 0; c < m_p; ++c) {
        for (unsigned r = 0; r < m_mod; ++r) {
            expr_ref_vector right(m), left(m);
            for (unsigned d = 0; d < m_p; ++d) {
                right.push_back(count(b, 2, c + d * m_p, r));
                left.push_back(count(b, 2, d + c * m_p, (r + m_mod - 1) % m_mod));
            }
            // the last letter opens the last window, at residue (len - 1) mod m_mod
            expr_ref at_end = last(b, c);
            if (m_mod > 1)
                at_end = m.mk_and(at_end, m.mk_eq(rem, num((r + 1) % m_mod)));
            defs.push_back(m.mk_eq(sum(right), m_autil.mk_sub(count(b, 1, c, r), indicator(at_end, defs))));

            // the first letter opens the first window, at residue 0
            expr_ref at_start = r == 0 ? first(b, c) : expr_ref(m.mk_false(), m);
            defs.push_back(m.mk_eq(sum(left), m_autil.mk_sub(count(b, 1, c, r), indicator(at_start, defs))));
        }
    }
}

void seq_parikh::define_block(block const& b, expr_ref_vector& defs) {
    define_letters(b, defs);
    for (unsigned level = 1; level <= m_config.m_k; ++level) {
        define_level(b, level, defs);
    }
    define_flow(b, defs);
}

// out[gram * m_mod + r] counts the occurrences of gram starting at a position congruent to r
void seq_parikh::totals(vector<block> const& blocks, unsigned level, expr_ref_vector& out, expr_ref_vector& defs) {
    vector<expr_ref_vector> acc;
    for (unsigned i = 0; i < num_grams(level) * m_mod; ++i) {
        acc.push_back(expr_ref_vector(m));
    }

    // clocks[i] is the clock reached in front of block i
    expr_ref_vector lens(m), clocks(m);
    clocks.push_back(clock(num(0), defs));
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
        for (unsigned g = 0; g < num_grams(level); ++g) {
            if (m_mod == 1) {
                acc[g].push_back(count(b, level, g, 0));
                continue;
            }
            for (unsigned r = 0; r < m_mod; ++r) {
                // The clock is an argument, so positions whose clocks agree share the
                // rotation by congruence.  That is wanted within one observer, but clocks of
                // different moduli can agree by accident, hence m_mod in the key.
                expr_ref rot = mk_sk("seq.parikh.rot", { b.m_e, num(level), num(g), num(r), pre, num(m_mod), num(m_p) }, m_autil.mk_int());
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

void seq_parikh::add_observer(vector<block> const& l, vector<block> const& r, unsigned mod,
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

bool seq_parikh::over_budget(vector<block> const& l, vector<block> const& r, unsigned_vector const& moduli) {
    svector<block_pair> pairs;
    adjacent(l, pairs);
    adjacent(r, pairs);
    unsigned blocks = l.size() + r.size() + 1;
    unsigned per_observer = 0;
    for (unsigned level = 1; level <= m_config.m_k; ++level) {
        per_observer += blocks * num_grams(level);
    }
    // the boundary factors dominate: one variable per pair of blocks and per factor
    if (m_config.m_k >= 2)
        per_observer += pairs.size() * num_grams(2);
    unsigned counters = 0;
    for (unsigned n : moduli) {
        counters += per_observer * n;
    }
    return counters > m_config.m_max_counters;
}

bool seq_parikh::operator()(expr_ref_vector const& l, expr_ref_vector const& r,
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
