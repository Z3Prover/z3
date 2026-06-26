/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.cpp

Abstract:

    Regex split decomposition (the split function sigma).  See seq_split.h.

Author:

    Clemens Eisenhofer 2026-6-10

--*/

#include "ast/rewriter/seq_split.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include "util/stack.h"

seq_split::seq_split(seq_rewriter& rw) :
    m(rw.m()), m_rw(rw), m_subset(rw.u().re) {}

seq_util&      seq_split::seq() const { return m_rw.u(); }
seq_util::rex& seq_split::re()  const { return m_rw.u().re; }

// Add <d, n> unless the (optional) lookahead oracle prunes it.
void seq_split::push(split_set& out, split_oracle const& oracle, expr* d, expr* n) const {
    if (!oracle || oracle(d, n))
        out.push_back(split_pair(d, n, m));
}

// Cross-product intersection of two split-sets (split algebra):
//   S1 cap S2 = { <D1 cap D2, N1 cap N2> | <D1,N1> in S1, <D2,N2> in S2 }.
// Pairs where any component is bottom (the empty regex) are dropped.
bool seq_split::intersect(split_set const& s1, split_set const& s2, split_set& result,
                          unsigned threshold, split_oracle const& oracle) const {
    const seq_util::rex& r = re();
    for (auto const& p1 : s1) {
        for (auto const& p2 : s2) {
            if (r.is_empty(p1.m_d) || r.is_empty(p2.m_d) ||
                r.is_empty(p1.m_n) || r.is_empty(p2.m_n))
                continue;
            const expr_ref di(m_rw.mk_regex_inter_normalize(p1.m_d, p2.m_d), m);
            const expr_ref ni(m_rw.mk_regex_inter_normalize(p1.m_n, p2.m_n), m);
            push(result, oracle, di, ni);
            if (result.size() > threshold)
                return false;
        }
    }
    return true;
}

// Complement of a split-set via De Morgan: ~S = cap_{s in S} ~s with
//   ~<D,N> = { <~D, .*>, <.*, ~N> }  and  ~{} = { <.*, .*> }.
// May produce up to 2^|sp| pairs (bounded by the threshold).  A threshold
// overrun must abort entirely: a partial fold is a strictly weaker (unsound)
// split-set, since each ~sp[i] further constrains ~S.
bool seq_split::complement(sort* seq_sort, split_set const& sp, split_set& result,
    const unsigned threshold, split_oracle const& oracle) const {

    seq_util::rex& r = re();
    sort* re_sort = r.mk_re(seq_sort);
    const expr_ref full(r.mk_full_seq(re_sort), m);   // .*
    if (sp.empty()) {                                   // ~{} = <.*, .*>
        push(result, oracle, full, full);
        return true;
    }
    // The acc/next pairs carry genuine output-orientation N components (the De
    // Morgan ~<D,N> = {<~D,.*>, <.*,~N>}), so the oracle prunes them soundly and
    // keeps the 2^|sp| fold from blowing up.
    split_set acc;
    push(acc, oracle, r.mk_complement(sp[0].m_d), full);
    push(acc, oracle, full, r.mk_complement(sp[0].m_n));
    for (unsigned i = 1; i < sp.size(); ++i) {
        split_set next;
        push(next, oracle, r.mk_complement(sp[i].m_d), full);
        push(next, oracle, full, r.mk_complement(sp[i].m_n));
        split_set tmp;
        if (!intersect(acc, next, tmp, threshold, oracle))
            return false;
        acc = std::move(tmp);
        if (acc.empty())            // intersection empty => ~S is empty
            break;
        if (acc.size() > threshold)
            return false;
    }
    result.append(acc);
    return true;
}

bool seq_split::compute(expr* r, split_set& result, unsigned threshold, split_mode mode,
                        split_oracle const& oracle) {
    SASSERT(r);
    seq_util& sq = seq();
    seq_util::rex& rex = re();

    sort* seq_sort = nullptr;
    if (!sq.is_re(r, seq_sort))
        return false;

    // bottom: sigma(empty) = {} (the empty split-set)
    if (rex.is_empty(r))
        return true;

    // epsilon: sigma(eps) = { <eps, eps> }
    if (rex.is_epsilon(r)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        push(result, oracle, eps, eps);
        return true;
    }

    expr* a = nullptr, *b = nullptr;

    // to_re(s): split the literal word s at every position.
    expr* s = nullptr;
    if (rex.is_to_re(r, s)) {
        zstring str;
        vector<expr*> stack;
        stack.push_back(s);

        while (!stack.empty()) {
            expr* cur = stack.back();
            stack.pop_back();
            if (seq().str.is_concat(cur, a, b)) {
                stack.push_back(b);
                stack.push_back(a);
            }
            else {
                expr* ch;
                unsigned cv;
                if (seq().str.is_unit(cur, ch) && seq().is_const_char(ch, cv)) {
                    str += zstring(cv);
                    continue;
                }
                zstring str2;
                if (sq.str.is_string(s, str2)) {
                    str = str2;
                    continue;
                }
                // not a constant string; unsupported for now
                return false;
            }
        }
        for (unsigned i = 0; i <= str.length(); ++i) {
            const expr_ref p(rex.mk_to_re(sq.str.mk_string(str.extract(0, i))), m);
            const expr_ref q(rex.mk_to_re(sq.str.mk_string(str.extract(i, str.length() - i))), m);
            push(result, oracle, p, q);
        }
        return true;
    }

    // single-character class alpha (., [lo-hi], of_pred):
    //   sigma(alpha) = { <eps, alpha>, <alpha, eps> }
    if (rex.is_full_char(r) || rex.is_range(r) || rex.is_of_pred(r)) {
        const expr_ref ex(r, m);
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        push(result, oracle, eps, ex);
        push(result, oracle, ex, eps);
        return true;
    }

    // .* : sigma(.*) = { <.*, .*> }
    if (rex.is_full_seq(r)) {
        const expr_ref ex(r, m);
        push(result, oracle, ex, ex);
        return true;
    }

    // union: sigma(r0 | ... | r_{n-1}) = U sigma(ri)   (re.union may be n-ary)
    if (rex.is_union(r)) {
        app* ap = to_app(r);
        for (unsigned i = 0; i < ap->get_num_args(); ++i) {
            if (!compute(ap->get_arg(i), result, threshold, mode, oracle))
                return false;
        }
        return true;
    }

    // concat: sigma(r0...r_{n-1}) = U_i  (r0...r_{i-1}) . sigma(ri) . (r_{i+1}...r_{n-1})
    // (re.++ may be n-ary)
    if (rex.is_concat(r)) {
        app* ap = to_app(r);
        const unsigned n = ap->get_num_args();
        for (unsigned i = 0; i < n; ++i) {
            // Sound to pass the oracle into the sub-computation: N_inner.Sigma*
            // over-approximates the final N_inner.right, so a prune here is a
            // prune of the final pair too (prefix-compatible test).
            split_set sigma_arg;
            if (!compute(ap->get_arg(i), sigma_arg, threshold, mode, oracle))
                return false;

            expr_ref left(m), right(m);
            if (i == 0)
                left = rex.mk_epsilon(seq_sort);
            else {
                for (unsigned j = 0; j < i; ++j) {
                    expr* arg = ap->get_arg(j);
                    left = left ? expr_ref(rex.mk_concat(left, arg), m) : expr_ref(arg, m);
                }
            }
            if (i == n - 1)
                right = rex.mk_epsilon(seq_sort);
            else {
                right = ap->get_arg(i + 1);
                for (unsigned j = i + 2; j < n; ++j) {
                    expr* arg = ap->get_arg(j);
                    right = rex.mk_concat(right, arg);
                }
            }

            for (auto const& [d, nn] : sigma_arg) {
                const expr_ref p = m_rw.mk_re_append(left, d);
                const expr_ref q = m_rw.mk_re_append(nn, right);
                push(result, oracle, p, q);
            }
        }
        return true;
    }

    // star: sigma(a*) = { <eps, eps> } cup a*.sigma(a).a*
    if (rex.is_star(r, a)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        push(result, oracle, eps, eps);
        split_set sa;
        if (!compute(a, sa, threshold, mode, oracle))
            return false;
        for (auto const& [d, n] : sa) {
            const expr_ref p = m_rw.mk_re_append(r, d);   // a*.D
            const expr_ref q = m_rw.mk_re_append(n, r);   // N.a*
            push(result, oracle, p, q);
        }
        return true;
    }

    // plus: a+ = a.a* ; sigma(a+) = a*.sigma(a).a*  (star rule without <eps,eps>)
    if (rex.is_plus(r, a)) {
        const expr_ref star(rex.mk_star(a), m);          // a*
        split_set sa;
        if (!compute(a, sa, threshold, mode, oracle))
            return false;
        for (auto const& [d, n] : sa) {
            const expr_ref p = m_rw.mk_re_append(star, d);
            const expr_ref q = m_rw.mk_re_append(n, star);
            push(result, oracle, p, q);
        }
        return true;
    }

    // intersection: sigma(r0 & ... & r_{n-1}) = cap sigma(ri)   (re.inter may be n-ary)
    if (rex.is_intersection(r)) {
        if (mode == split_mode::weak)
            return false;
        app* ap = to_app(r);
        const unsigned n = ap->get_num_args();
        split_set current;
        if (!compute(ap->get_arg(0), current, threshold, mode, oracle))
            return false;
        // A give-up on any conjunct must propagate as a give-up: silently treating
        // it as the empty split-set would collapse the whole intersection to bottom
        // and be misreported as an (unsound) conflict.
        for (unsigned i = 1; i < n && !current.empty(); ++i) {
            split_set arg_i, tmp;
            if (!compute(ap->get_arg(i), arg_i, threshold, mode, oracle))
                return false;
            if (!intersect(current, arg_i, tmp, threshold, oracle))
                return false;
            current = std::move(tmp);
        }
        result.append(current);
        return true;
    }

    // complement: sigma(~a) = ~sigma(a).
    // The body is computed WITHOUT the oracle (the body's pairs are inverted, so
    // their N is unrelated to the output N); the oracle is re-applied in complement().
    if (rex.is_complement(r, a)) {
        if (mode == split_mode::weak)
            return false;
        split_set sa;
        if (!compute(a, sa, threshold, mode))
            return false;
        return complement(seq_sort, sa, result, threshold, oracle);
    }

    // difference: a \ b = a & ~b ; sigma(a \ b) = sigma(a) cap ~sigma(b).
    // sigma(b) (used only inside the complement) is computed WITHOUT the oracle.
    if (rex.is_diff(r, a, b)) {
        if (mode == split_mode::weak)
            return false;
        split_set sa, sb, sb_compl, tmp;
        if (!compute(a, sa, threshold, mode, oracle))
            return false;
        if (!compute(b, sb, threshold, mode))
            return false;
        if (!complement(seq_sort, sb, sb_compl, threshold, oracle))
            return false;
        if (!intersect(sa, sb_compl, tmp, threshold, oracle))
            return false;
        result.append(tmp);
        return true;
    }

    // bounded loop / ite / other: not handled (paper "v1: bail").
    TRACE(seq, tout << "seq_split: unsupported regex " << mk_pp(r, m) << "\n";);
    return false;
}

// same-D / same-N merge (paper eqs. 1 & 2):
//   { <D,N>, <D,N'> } -> <D, N | N'>      (by_left = true,  group by D)
//   { <D,N>, <D',N> } -> <D | D', N>      (by_left = false, group by N)
// Only fires on syntactically-identical (perfectly-shared) key components, so
// it is a conservative instance of the rule.
void seq_split::merge_by(split_set& pairs, const bool by_left) const {
    obj_map<expr, unsigned> idx;   // key component -> position in `out`
    split_set out;
    for (auto const& p : pairs) {
        expr* key   = by_left ? p.m_d.get() : p.m_n.get();
        expr* other = by_left ? p.m_n.get() : p.m_d.get();
        unsigned pos;
        if (idx.find(key, pos)) {
            expr* prev = by_left ? out[pos].m_n.get() : out[pos].m_d.get();
            const expr_ref u(m_rw.mk_regex_union_normalize(prev, other), m);
            if (by_left)
                out[pos].m_n = u;
            else
                out[pos].m_d = u;
        }
        else {
            idx.insert(key, out.size());
            out.push_back(p);
        }
    }
    pairs.swap(out);
}

void seq_split::simplify(split_set& pairs) const {
    seq_util::rex& r = re();

    // 1. drop pairs with a bottom (empty-language) component.
    unsigned w = 0;
    for (unsigned i = 0; i < pairs.size(); ++i) {
        if (r.is_empty(pairs[i].m_d) || r.is_empty(pairs[i].m_n))
            continue;
        if (w != i)
            pairs[w] = pairs[i];
        ++w;
    }
    pairs.shrink(w);
    if (pairs.size() <= 1)
        return;

    // 2. same-D / same-N merge rules.
    merge_by(pairs, true);
    merge_by(pairs, false);
    if (pairs.size() <= 1)
        return;

    // 3. subsumption: drop <D_i,N_i> when L(D_i) subseteq L(D_j) and
    //    L(N_i) subseteq L(N_j) for some kept j.  seq_subset is conservative
    //    (returns true only for definite containment), so we never drop a
    //    needed split.
    //if (pairs.size() > 64)
    //    return;

    struct row { expr* d; expr* n; unsigned idx; };
    vector<row> rows;
    for (unsigned i = 0; i < pairs.size(); ++i)
        rows.push_back({ pairs[i].m_d.get(), pairs[i].m_n.get(), i });

    auto subsumes = [&](row const& a, row const& b) {
        return m_subset.is_subset(b.d, a.d) && m_subset.is_subset(b.n, a.n);
    };

    vector<row> kept;
    for (row const& row_r : rows) {
        bool redundant = false;
        for (row const& k : kept)
            if (subsumes(k, row_r)) { redundant = true; break; }
        if (redundant)
            continue;
        // drop already-kept rows strictly subsumed by row_r
        unsigned kw = 0;
        for (unsigned t = 0; t < kept.size(); ++t) {
            if (subsumes(row_r, kept[t]))
                continue;
            kept[kw++] = kept[t];
        }
        kept.shrink(kw);
        kept.push_back(row_r);
    }

    split_set result;
    for (row const& k : kept)
        result.push_back(pairs[k.idx]);
    pairs.swap(result);
}

std::pair<expr_ref, expr_ref> seq_split::split_membership(expr* str, expr* regex, unsigned threshold, split_set& result) const {
    expr_ref_vector tokens(m);
    vector<expr*> stack;
    stack.push_back(str);

    while (!stack.empty()) {
        expr* cur = stack.back();
        stack.pop_back();
        expr* l, *r;
        if (seq().str.is_concat(cur, l, r)) {
            stack.push_back(r);
            stack.push_back(l);
        }
        else
            tokens.push_back(expr_ref(cur, m));
    }

    expr* ch;
    unsigned i = 0;

    while (i < tokens.size() && (seq().str.is_string(tokens.get(i)) || (seq().str.is_unit(tokens.get(i), ch) && seq().is_const_char(ch)))) {
        zstring s;
        if (seq().str.is_string(tokens.get(i), s)) {
            if (s.empty()) {
                i++;
                continue;
            }
            ch = seq().mk_char(s[0]);
            tokens[i] = seq().str.mk_string(s.extract(1, s.length() - 1));
        }
        else
            i++;
        regex = m_rw.mk_derivative(ch, regex);
    }

    if (i > 0) {
        unsigned j = 0;
        for (; i < tokens.size(); i++, j++) {
            tokens[j] = tokens.get(i);
        }
        tokens.shrink(j);
    }

    // TODO: Do this for the back as well (also, why did no rule before do that?)

    if (tokens.empty())
        return { expr_ref(m), expr_ref(m) };

    // Choose the factorization boundary so the tail starts with the
    // longest run of concrete characters c.
    // This gives the split-engine lookahead oracle the most pruning information.
    // head = u' (tokens before the run), tail = c · u''' (tokens from the run onward).
    const unsigned total = tokens.size();
    unsigned run_start = 0, run_len = 0;
    for (i = 1; i < total; ) {
        if (!(seq().str.is_unit(tokens.get(i), ch) && seq().is_const_char(ch))) {
            i++;
            continue;
        }
        unsigned j = i;
        while (j < total && seq().str.is_unit(tokens.get(j), ch) && seq().is_const_char(ch)) {
            j++;
        }
        if (j - i > run_len) {
            run_len = j - i;
            run_start = i;
        }
        i = j;
    }
    // No constant run => fall back to splitting off the first token.
    const unsigned p = run_len == 0 ? 1 : run_start;
    SASSERT(p >= 1);
    expr* head = tokens.get(0);
    for (i = 1; i < p; i++) {
        head = seq().str.mk_concat(head, tokens.get(i));
    }
    expr* tail = seq().str.mk_empty(head->get_sort());
    if (tokens.size() > p + run_len) {
        tail = tokens.get(p + run_len);
        for (i = p + run_len + 1; i < tokens.size(); i++) {
            tail = seq().str.mk_concat(tail, tokens.get(i));
        }
    }
    SASSERT(head && tail);

    // Build the constant lookahead c and (if non-empty) an oracle that
    // prunes splits whose postfix cannot match c.
    zstring c;
    for (i = 0; i < run_len; ++i) {
        unsigned cv;
        VERIFY(seq().str.is_unit(tokens.get(run_start + i), ch));
        VERIFY(seq().is_const_char(ch, cv));
        c = c + zstring(cv);
    }
    split_oracle oracle;
    if (!c.empty())
        oracle = [this, &c](expr*, expr* n) { return split_lookahead_viable(n, c); };

    // Decompose the regex into a split-set via the shared seq_split engine
    if (!m_rw.split(regex, result, threshold, split_mode::strong, oracle)) {
        result.clear();
        return { expr_ref(m), expr_ref(m) };
    }

    m_rw.simplify_split(result);

    // Eagerly consume the constant run c from the tail by taking the c-derivative
    // of each postfix
    if (!c.empty()) {
        unsigned w = 0;
        for (i = 0; i < result.size(); ++i) {
            expr* d = result[i].m_n;
            for (unsigned k = 0; d && !seq().re.is_empty(d) && k < c.length(); ++k) {
                d = m_rw.mk_derivative(seq().mk_char(c[k]), d);
            }
            SASSERT(d);
            if (re().is_empty(d))
                continue;   // postfix can't start with c => infeasible split, drop
            result[w++] = split_pair(result[i].m_d, d, m);
        }
        result.shrink(w);
    }

    return { expr_ref(head, m), expr_ref(tail, m) };
}

bool seq_split::split_lookahead_viable(expr* regex, zstring const& c) const {
    SASSERT(regex);
    for (unsigned i = 0; i < c.length(); i++) {
        if (m.is_true(m_rw.is_nullable(regex)))
            return true;            // N accepts the prefix c[0..i) => a suffix completes it
        regex = m_rw.mk_derivative(seq().mk_char(c[i]), regex);
        SASSERT(regex);
        if (re().is_empty(regex))
            return false;           // N went (syntactically) dead before reaching c
    }
    return !re().is_empty(regex);
}