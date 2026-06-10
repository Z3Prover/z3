/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.cpp

Abstract:

    Regex split decomposition (the split function sigma).  See seq_split.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026-6-10
    Clemens Eisenhofer 2026-6-10

--*/

#include "ast/rewriter/seq_split.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"

seq_split::seq_split(seq_rewriter& rw) :
    m_rw(rw), m_subset(rw.u().re) {}

ast_manager&   seq_split::m()   const { return m_rw.m(); }
seq_util&      seq_split::seq() const { return m_rw.u(); }
seq_util::rex& seq_split::re()  const { return m_rw.u().re; }

// Cross-product intersection of two split-sets (split algebra):
//   S1 cap S2 = { <D1 cap D2, N1 cap N2> | <D1,N1> in S1, <D2,N2> in S2 }.
// Pairs where any component is bottom (the empty regex) are dropped.
bool seq_split::intersect(split_set const& s1, split_set const& s2, split_set& result, unsigned threshold) {
    seq_util::rex& r = re();
    for (auto const& p1 : s1) {
        for (auto const& p2 : s2) {
            if (r.is_empty(p1.m_d) || r.is_empty(p2.m_d) ||
                r.is_empty(p1.m_n) || r.is_empty(p2.m_n))
                continue;
            result.push_back(split_pair(m_rw.mk_regex_inter_normalize(p1.m_d, p2.m_d),
                                        m_rw.mk_regex_inter_normalize(p1.m_n, p2.m_n), m()));
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
bool seq_split::complement(sort* seq_sort, split_set const& sp, split_set& result, unsigned threshold) {
    seq_util::rex& r = re();
    sort* re_sort = r.mk_re(seq_sort);
    const expr_ref full(r.mk_full_seq(re_sort), m());   // .*
    if (sp.empty()) {                                   // ~{} = <.*, .*>
        result.push_back(split_pair(full, full, m()));
        return true;
    }
    split_set acc;
    acc.push_back(split_pair(r.mk_complement(sp[0].m_d), full, m()));
    acc.push_back(split_pair(full, r.mk_complement(sp[0].m_n), m()));
    for (unsigned i = 1; i < sp.size(); ++i) {
        split_set next;
        next.push_back(split_pair(r.mk_complement(sp[i].m_d), full, m()));
        next.push_back(split_pair(full, r.mk_complement(sp[i].m_n), m()));
        split_set tmp;
        if (!intersect(acc, next, tmp, threshold))
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

bool seq_split::compute(expr* r, split_set& result, unsigned threshold, split_mode mode) {
    SASSERT(r);
    seq_util& sq = seq();
    seq_util::rex& rex = re();
    ast_manager& mm = m();

    // std::cout << "compute " << mk_pp(r, m()) << std::endl;

    sort* seq_sort = nullptr;
    if (!sq.is_re(r, seq_sort))
        return false;

    // bottom: sigma(empty) = {} (the empty split-set)
    if (rex.is_empty(r))
        return true;

    // epsilon: sigma(eps) = { <eps, eps> }
    if (rex.is_epsilon(r)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), mm);
        result.push_back(split_pair(eps, eps, mm));
        return true;
    }

    expr* a = nullptr, *b = nullptr;

    // to_re(s): split the literal word s at every position.
    expr* s = nullptr;
    if (rex.is_to_re(r, s)) {
        zstring str;
        if (sq.str.is_string(s, str)) {
            for (unsigned i = 0; i <= str.length(); ++i) {
                const expr_ref p(rex.mk_to_re(sq.str.mk_string(str.extract(0, i))), mm);
                const expr_ref q(rex.mk_to_re(sq.str.mk_string(str.extract(i, str.length() - i))), mm);
                result.push_back(split_pair(p, q, mm));
            }
            return true;
        }
        // a single symbolic unit behaves like one token: { <eps, u>, <u, eps> }
        if (sq.str.is_unit(s)) {
            const expr_ref ex(r, mm);
            const expr_ref eps(rex.mk_epsilon(seq_sort), mm);
            result.push_back(split_pair(eps, ex, mm));
            result.push_back(split_pair(ex, eps, mm));
            return true;
        }
        // to_re over a non-literal sequence: not handled.
        return false;
    }

    // single-character class alpha (., [lo-hi], of_pred):
    //   sigma(alpha) = { <eps, alpha>, <alpha, eps> }
    if (rex.is_full_char(r) || rex.is_range(r) || rex.is_of_pred(r)) {
        const expr_ref ex(r, mm);
        const expr_ref eps(rex.mk_epsilon(seq_sort), mm);
        result.push_back(split_pair(eps, ex, mm));
        result.push_back(split_pair(ex, eps, mm));
        return true;
    }

    // .* : sigma(.*) = { <.*, .*> }
    if (rex.is_full_seq(r)) {
        const expr_ref ex(r, mm);
        result.push_back(split_pair(ex, ex, mm));
        return true;
    }

    // union: sigma(r0 | ... | r_{n-1}) = U sigma(ri)   (re.union may be n-ary)
    if (rex.is_union(r)) {
        app* ap = to_app(r);
        for (unsigned i = 0; i < ap->get_num_args(); ++i) {
            if (!compute(ap->get_arg(i), result, threshold, mode))
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
            split_set sigma_arg;
            if (!compute(ap->get_arg(i), sigma_arg, threshold, mode))
                return false;

            expr_ref left(mm), right(mm);
            if (i == 0)
                left = rex.mk_epsilon(seq_sort);
            else
                for (unsigned j = 0; j < i; ++j) {
                    expr* arg = ap->get_arg(j);
                    left = left ? expr_ref(rex.mk_concat(left, arg), mm) : expr_ref(arg, mm);
                }
            if (i == n - 1)
                right = rex.mk_epsilon(seq_sort);
            else
                for (unsigned j = i + 1; j < n; ++j) {
                    expr* arg = ap->get_arg(j);
                    right = right ? expr_ref(rex.mk_concat(right, arg), mm) : expr_ref(arg, mm);
                }

            for (auto const& [d, nn] : sigma_arg) {
                const expr_ref p = m_rw.mk_re_append(left, d);
                const expr_ref q = m_rw.mk_re_append(nn, right);
                result.push_back(split_pair(p, q, mm));
            }
        }
        return true;
    }

    // star: sigma(a*) = { <eps, eps> } cup a*.sigma(a).a*
    if (rex.is_star(r, a)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), mm);
        result.push_back(split_pair(eps, eps, mm));
        split_set sa;
        if (!compute(a, sa, threshold, mode))
            return false;
        for (auto const& [d, n] : sa) {
            const expr_ref p = m_rw.mk_re_append(r, d);   // a*.D
            const expr_ref q = m_rw.mk_re_append(n, r);   // N.a*
            result.push_back(split_pair(p, q, mm));
        }
        return true;
    }

    // plus: a+ = a.a* ; sigma(a+) = a*.sigma(a).a*  (star rule without <eps,eps>)
    if (rex.is_plus(r, a)) {
        const expr_ref star(rex.mk_star(a), mm);          // a*
        split_set sa;
        if (!compute(a, sa, threshold, mode))
            return false;
        for (auto const& [d, n] : sa) {
            const expr_ref p = m_rw.mk_re_append(star, d);
            const expr_ref q = m_rw.mk_re_append(n, star);
            result.push_back(split_pair(p, q, mm));
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
        if (!compute(ap->get_arg(0), current, threshold, mode))
            return false;
        // A give-up on any conjunct must propagate as a give-up: silently treating
        // it as the empty split-set would collapse the whole intersection to bottom
        // and be misreported as an (unsound) conflict.
        for (unsigned i = 1; i < n && !current.empty(); ++i) {
            split_set arg_i, tmp;
            if (!compute(ap->get_arg(i), arg_i, threshold, mode))
                return false;
            if (!intersect(current, arg_i, tmp, threshold))
                return false;
            current = std::move(tmp);
        }
        result.append(current);
        return true;
    }

    // complement: sigma(~a) = ~sigma(a)
    if (rex.is_complement(r, a)) {
        if (mode == split_mode::weak)
            return false;
        split_set sa;
        if (!compute(a, sa, threshold, mode))
            return false;
        return complement(seq_sort, sa, result, threshold);
    }

    // difference: a \ b = a & ~b ; sigma(a \ b) = sigma(a) cap ~sigma(b)
    if (rex.is_diff(r, a, b)) {
        if (mode == split_mode::weak)
            return false;
        split_set sa, sb, sb_compl, tmp;
        if (!compute(a, sa, threshold, mode))
            return false;
        if (!compute(b, sb, threshold, mode))
            return false;
        if (!complement(seq_sort, sb, sb_compl, threshold))
            return false;
        if (!intersect(sa, sb_compl, tmp, threshold))
            return false;
        result.append(tmp);
        return true;
    }

    // bounded loop / ite / other: not handled (paper "v1: bail").
    TRACE(seq, tout << "seq_split: unsupported regex " << mk_pp(r, mm) << "\n";);
    std::cout << "seq_split: unsupported regex " << mk_pp(r, mm) << std::endl;
    return false;
}

// same-D / same-N merge (paper eqs. 1 & 2):
//   { <D,N>, <D,N'> } -> <D, N | N'>      (by_left = true,  group by D)
//   { <D,N>, <D',N> } -> <D | D', N>      (by_left = false, group by N)
// Only fires on syntactically-identical (perfectly-shared) key components, so
// it is a conservative instance of the rule.
void seq_split::merge_by(split_set& pairs, bool by_left) const {
    seq_util::rex& r = re();
    ast_manager& mm = m();
    obj_map<expr, unsigned> idx;   // key component -> position in `out`
    split_set out;
    for (auto const& p : pairs) {
        expr* key   = by_left ? p.m_d.get() : p.m_n.get();
        expr* other = by_left ? p.m_n.get() : p.m_d.get();
        unsigned pos;
        if (idx.find(key, pos)) {
            expr* prev = by_left ? out[pos].m_n.get() : out[pos].m_d.get();
            seq_rewriter rw(m());
            const expr_ref u(m_rw.mk_regex_union_normalize(prev, other), mm);
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

void seq_split::simplify(split_set& pairs) {
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
