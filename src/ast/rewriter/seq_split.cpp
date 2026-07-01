
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
    m(rw.m()), m_rw(rw), m_subset(rw.u().re),
    m_set_sort(m),
    m_d_empty(m), m_d_single(m), m_d_fromre(m), m_d_union(m),
    m_d_inter(m), m_d_compl(m), m_d_lcat(m), m_d_rcat(m),
    m_empty_app(m) {}

// ---------------------------------------------------------------------------
// Suspended split-set representation (split algebra over `expr`).
// ---------------------------------------------------------------------------

void seq_split::ensure_decls(sort* seq_sort) {
    SASSERT(seq_sort);
    if (m_seq_sort == seq_sort)
        return;
    sort* re_sort = re().mk_re(seq_sort);
    m_set_sort  = m.mk_uninterpreted_sort(symbol("seq.split.set"));
    sort* ss    = m_set_sort;
    m_d_empty   = m.mk_func_decl(symbol("seq.split.empty"),   0u, nullptr, ss);
    m_d_single  = m.mk_func_decl(symbol("seq.split.single"),  re_sort, re_sort, ss);
    m_d_fromre  = m.mk_func_decl(symbol("seq.split.from_re"), re_sort, ss);
    m_d_union   = m.mk_func_decl(symbol("seq.split.union"),   ss, ss, ss);
    m_d_inter   = m.mk_func_decl(symbol("seq.split.inter"),   ss, ss, ss);
    m_d_compl   = m.mk_func_decl(symbol("seq.split.compl"),   ss, ss);
    m_d_lcat    = m.mk_func_decl(symbol("seq.split.lcat"),    re_sort, ss, ss);
    m_d_rcat    = m.mk_func_decl(symbol("seq.split.rcat"),    ss, re_sort, ss);
    m_empty_app = m.mk_const(m_d_empty);
    m_seq_sort  = seq_sort;
}

// --- smart constructors ----------------------------------------------------

expr_ref seq_split::mk_empty() {
    SASSERT(m_empty_app);
    return m_empty_app;
}

expr_ref seq_split::mk_single(expr* d, expr* n) {
    SASSERT(d && n);
    if (re().is_empty(d) || re().is_empty(n))
        return mk_empty();
    return expr_ref(m.mk_app(m_d_single, d, n), m);
}

expr_ref seq_split::mk_fromre(expr* r) {
    SASSERT(r);
    sort* seq_sort = nullptr;
    VERIFY(seq().is_re(r, seq_sort));
    ensure_decls(seq_sort);
    if (re().is_empty(r))
        return mk_empty();
    return expr_ref(m.mk_app(m_d_fromre, r), m);
}

expr_ref seq_split::mk_union(expr* a, expr* b) {
    SASSERT(a && b);
    if (is_empty_ss(a))
        return expr_ref(b, m);
    if (is_empty_ss(b))
        return expr_ref(a, m);
    return expr_ref(m.mk_app(m_d_union, a, b), m);
}

expr_ref seq_split::mk_inter(expr* a, expr* b) {
    SASSERT(a && b);
    if (is_empty_ss(a) || is_empty_ss(b))
        return mk_empty();
    return expr_ref(m.mk_app(m_d_inter, a, b), m);
}

expr_ref seq_split::mk_compl(expr* a) {
    SASSERT(a);
    return expr_ref(m.mk_app(m_d_compl, a), m);
}

expr_ref seq_split::mk_lcat(expr* r, expr* s) {
    SASSERT(r && s);
    if (is_empty_ss(s))
        return mk_empty();
    if (re().is_epsilon(r))            // eps . S = S
        return expr_ref(s, m);
    return expr_ref(m.mk_app(m_d_lcat, r, s), m);
}

expr_ref seq_split::mk_rcat(expr* s, expr* r) {
    SASSERT(r && s);
    if (is_empty_ss(s))
        return mk_empty();
    if (re().is_epsilon(r))            // S . eps = S
        return expr_ref(s, m);
    return expr_ref(m.mk_app(m_d_rcat, s, r), m);
}

// --- recognizers -----------------------------------------------------------

bool seq_split::is_empty_ss(expr* e) const {
    return is_app(e) && to_app(e)->get_decl() == m_d_empty;
}
bool seq_split::is_single(expr* e, expr*& d, expr*& n) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_single)
        return false;
    d = to_app(e)->get_arg(0);
    n = to_app(e)->get_arg(1);
    return true;
}
bool seq_split::is_fromre(expr* e, expr*& r) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_fromre)
        return false;
    r = to_app(e)->get_arg(0);
    return true;
}
bool seq_split::is_union(expr* e, expr*& a, expr*& b) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_union)
        return false;
    a = to_app(e)->get_arg(0);
    b = to_app(e)->get_arg(1);
    return true;
}
bool seq_split::is_inter(expr* e, expr*& a, expr*& b) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_inter)
        return false;
    a = to_app(e)->get_arg(0);
    b = to_app(e)->get_arg(1);
    return true;
}
bool seq_split::is_compl(expr* e, expr*& a) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_compl)
        return false;
    a = to_app(e)->get_arg(0);
    return true;
}
bool seq_split::is_lcat(expr* e, expr*& r, expr*& s) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_lcat)
        return false;
    r = to_app(e)->get_arg(0);
    s = to_app(e)->get_arg(1);
    return true;
}
bool seq_split::is_rcat(expr* e, expr*& s, expr*& r) const {
    if (!is_app(e) || to_app(e)->get_decl() != m_d_rcat)
        return false;
    s = to_app(e)->get_arg(0);
    r = to_app(e)->get_arg(1);
    return true;
}
bool seq_split::is_frontier(expr* e) const {
    expr *a = nullptr, *b = nullptr;
    return is_empty_ss(e) || is_single(e, a, b) || is_union(e, a, b);
}

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

// One level of the sigma rules.  Mirrors the historic eager `compute`, except it
// emits *suspended* split-algebra terms (from_re / lcat / rcat / inter / compl) for
// the subterms instead of recursing.  `mode` is irrelevant here: weak vs. strong is
// decided when `head_normalize` reaches an inter / compl node.
expr_ref seq_split::expand_fromre(expr* r, bool& ok) {
    ok = true;
    seq_util& sq = seq();
    seq_util::rex& rex = re();

    sort* seq_sort = nullptr;
    if (!sq.is_re(r, seq_sort)) {
        ok = false;
        return expr_ref(m);
    }
    ensure_decls(seq_sort);

    // bottom: sigma(empty) = {}
    if (rex.is_empty(r))
        return mk_empty();

    // epsilon: sigma(eps) = { <eps, eps> }
    if (rex.is_epsilon(r)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        return mk_single(eps, eps);
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
                ok = false;
                return expr_ref(m);
            }
        }
        expr_ref acc = mk_empty();
        for (unsigned i = 0; i <= str.length(); ++i) {
            const expr_ref p(rex.mk_to_re(sq.str.mk_string(str.extract(0, i))), m);
            const expr_ref q(rex.mk_to_re(sq.str.mk_string(str.extract(i, str.length() - i))), m);
            acc = mk_union(acc, mk_single(p, q));
        }
        return acc;
    }

    // single-character class alpha (., [lo-hi], of_pred):
    //   sigma(alpha) = { <eps, alpha>, <alpha, eps> }
    if (rex.is_full_char(r) || rex.is_range(r) || rex.is_of_pred(r)) {
        const expr_ref ex(r, m);
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        return mk_union(mk_single(eps, ex), mk_single(ex, eps));
    }

    // .* : sigma(.*) = { <.*, .*> }
    if (rex.is_full_seq(r)) {
        const expr_ref ex(r, m);
        return mk_single(ex, ex);
    }

    // union: sigma(r0 | ... | r_{n-1}) = U from_re(ri)   (re.union may be n-ary)
    if (rex.is_union(r)) {
        app* ap = to_app(r);
        expr_ref acc = mk_empty();
        for (expr* arg : *ap) {
            acc = mk_union(acc, mk_fromre(arg));
        }
        return acc;
    }

    // concat: sigma(r0...r_{n-1}) = U_i  (r0...r_{i-1}) . sigma(ri) . (r_{i+1}...r_{n-1})
    // emitted as U_i  lcat(left, rcat(from_re(ri), right))   (re.++ may be n-ary)
    if (rex.is_concat(r)) {
        app* ap = to_app(r);
        const unsigned n = ap->get_num_args();
        expr_ref acc = mk_empty();
        for (unsigned i = 0; i < n; ++i) {
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
            expr_ref term = mk_lcat(left, mk_rcat(mk_fromre(ap->get_arg(i)), right));
            acc = mk_union(acc, term);
        }
        return acc;
    }

    // star: sigma(a*) = { <eps, eps> } cup a*.sigma(a).a*
    if (rex.is_star(r, a)) {
        const expr_ref eps(rex.mk_epsilon(seq_sort), m);
        expr_ref body = mk_lcat(r, mk_rcat(mk_fromre(a), r));  // a*.from_re(a).a*
        return mk_union(mk_single(eps, eps), body);
    }

    // plus: a+ = a.a* ; sigma(a+) = a*.sigma(a).a*  (star rule without <eps,eps>)
    if (rex.is_plus(r, a)) {
        const expr_ref star(rex.mk_star(a), m);          // a*
        return mk_lcat(star, mk_rcat(mk_fromre(a), star));
    }

    // intersection: sigma(r0 & ... & r_{n-1}) = cap from_re(ri)   (re.inter may be n-ary)
    if (rex.is_intersection(r)) {
        app* ap = to_app(r);
        const unsigned n = ap->get_num_args();
        expr_ref acc = mk_fromre(ap->get_arg(0));
        for (unsigned i = 1; i < n; ++i)
            acc = mk_inter(acc, mk_fromre(ap->get_arg(i)));
        return acc;
    }

    // complement: sigma(~a) = ~sigma(a).
    if (rex.is_complement(r, a))
        return mk_compl(mk_fromre(a));

    // difference: a \ b = a & ~b ; sigma(a \ b) = sigma(a) cap ~sigma(b).
    if (rex.is_diff(r, a, b))
        return mk_inter(mk_fromre(a), mk_compl(mk_fromre(b)));

    // bounded loop / ite / other: not handled (paper "v1: bail").
    TRACE(seq, tout << "seq_split: unsupported regex " << mk_pp(r, m) << "\n";);
    ok = false;
    return expr_ref(m);
}

// r . hs : push the left regex onto the D component of a head-normal split-set.
expr_ref seq_split::distribute_lcat(expr* r, expr* hs) {
    expr *a = nullptr, *b = nullptr, *d = nullptr, *n = nullptr;
    if (is_empty_ss(hs))
        return mk_empty();
    if (is_single(hs, d, n))
        return mk_single(m_rw.mk_re_append(r, d), n);   // r.D
    if (is_union(hs, a, b))
        return mk_union(mk_lcat(r, a), mk_lcat(r, b));
    UNREACHABLE();
    return expr_ref(hs, m);
}

// hs . r : push the right regex onto the N component of a head-normal split-set.
expr_ref seq_split::distribute_rcat(expr* hs, expr* r) {
    expr *a = nullptr, *b = nullptr, *d = nullptr, *n = nullptr;
    if (is_empty_ss(hs))
        return mk_empty();
    if (is_single(hs, d, n))
        return mk_single(d, m_rw.mk_re_append(n, r));    // N.r
    if (is_union(hs, a, b))
        return mk_union(mk_rcat(a, r), mk_rcat(b, r));
    UNREACHABLE();
    return expr_ref(hs, m);
}

expr_ref seq_split::from_split_set(split_set const& s) {
    expr_ref acc = mk_empty();
    for (auto const& p : s)
        acc = mk_union(acc, mk_single(p.m_d, p.m_n));
    return acc;
}

expr_ref seq_split::head_normalize(expr* t, split_mode mode, unsigned threshold,
                                   split_oracle const& oracle, bool& ok) {
    ok = true;
    expr *a = nullptr, *b = nullptr, *r = nullptr, *s = nullptr;

    // already a frontier node
    if (is_frontier(t))
        return expr_ref(t, m);

    // from_re(r): one level of sigma; recurse to settle a non-frontier head
    // (plus / inter / compl / diff expand to lcat / inter / compl nodes).
    if (is_fromre(t, r)) {
        expr_ref e = expand_fromre(r, ok);
        if (!ok)
            return expr_ref(m);
        if (is_frontier(e))
            return e;
        return head_normalize(e, mode, threshold, oracle, ok);
    }

    // r.S : head-normalize S, then distribute r over the frontier.
    if (is_lcat(t, r, s)) {
        expr_ref hs = head_normalize(s, mode, threshold, oracle, ok);
        if (!ok)
            return expr_ref(m);
        return distribute_lcat(r, hs);
    }
    if (is_rcat(t, s, r)) {
        expr_ref hs = head_normalize(s, mode, threshold, oracle, ok);
        if (!ok)
            return expr_ref(m);
        return distribute_rcat(hs, r);
    }

    // inter / compl are eager by nature: a single split of S1 cap S2 (or ~S)
    // cannot be produced without materializing the operand split-sets.
    if (is_inter(t, a, b)) {
        if (mode == split_mode::weak) {
            ok = false;
            return expr_ref(m);
        }
        split_set sa, sb, tmp;
        if (!materialize(a, mode, threshold, oracle, sa) ||
            !materialize(b, mode, threshold, oracle, sb) ||
            !intersect(sa, sb, tmp, threshold, oracle)) {
            ok = false;
            return expr_ref(m);
        }
        return from_split_set(tmp);
    }
    if (is_compl(t, a)) {
        if (mode == split_mode::weak) {
            ok = false;
            return expr_ref(m);
        }
        // The body is materialized WITHOUT the oracle (its pairs are inverted, so
        // their N is unrelated to the output N); the oracle is re-applied in
        // complement().
        split_set sa, res;
        if (!materialize(a, mode, threshold, split_oracle{}, sa) ||
            !complement(m_seq_sort, sa, res, threshold, oracle)) {
            ok = false;
            return expr_ref(m);
        }
        return from_split_set(res);
    }

    UNREACHABLE();
    ok = false;
    return expr_ref(m);
}

bool seq_split::materialize(expr* node, split_mode mode, unsigned threshold,
                            split_oracle const& oracle, split_set& out) {
    iterator it(*this, node, mode, threshold, oracle);
    expr_ref d(m), n(m);
    while (it.next(d, n))
        out.push_back(split_pair(d, n, m));
    return !it.gave_up();
}

expr_ref seq_split::make(expr* r) {
    SASSERT(r);
    sort* seq_sort = nullptr;
    if (!seq().is_re(r, seq_sort))
        return expr_ref(m);
    return mk_fromre(r);
}

// --- Lazy enumerator --------------------------------------------------------
// The worklist holds suspended split-sets.  Each next() pops a node, head-
// normalizes it to a frontier (empty | single | union), and either returns the
// single split, pushes the two union branches back, or skips an empty.  All the
// expansion work happens lazily, one split per next() call.

seq_split::iterator::iterator(seq_split& engine, expr* node, split_mode mode,
                              unsigned threshold, split_oracle oracle) :
    m_engine(engine), m(engine.m), m_mode(mode), m_threshold(threshold),
    m_oracle(std::move(oracle)), m_work(engine.m) {
    SASSERT(node);
    m_work.push_back(node);
}

bool seq_split::iterator::next(expr_ref& out_d, expr_ref& out_n) {
    if (m_giveup)
        return false;                  // a prior give-up is sticky
    while (!m_work.empty()) {
        expr_ref t(m_work.back(), m);
        m_work.pop_back();

        bool ok = true;
        expr_ref hn = m_engine.head_normalize(t, m_mode, m_threshold, m_oracle, ok);
        if (!ok) {
            m_giveup = true;           // unsupported / weak Boolean / overrun
            return false;
        }

        expr *a = nullptr, *b = nullptr, *d = nullptr, *n = nullptr;
        if (m_engine.is_empty_ss(hn))
            continue;
        if (m_engine.is_single(hn, d, n)) {
            if (m_oracle && !m_oracle(d, n))
                continue;              // pruned by lookahead
            if (++m_count > m_threshold) {
                m_giveup = true;       // safety cap against space bloat
                return false;
            }
            out_d = d;
            out_n = n;
            return true;
        }
        if (m_engine.is_union(hn, a, b)) {
            m_work.push_back(a);
            m_work.push_back(b);
            continue;
        }
        UNREACHABLE();
    }
    return false;                      // exhausted (m_giveup stays false)
}

seq_split::iterator seq_split::iterate(expr* node, split_mode mode, unsigned threshold,
                                       split_oracle const& oracle) {
    return iterator(*this, node, mode, threshold, oracle);
}

// Eager wrapper: drain the lazy enumeration into `out`.  Semantics (give-up cases,
// oracle discipline) match the historic engine.
bool seq_split::compute(expr* r, split_set& result, unsigned threshold, split_mode mode,
                        split_oracle const& oracle) {
    SASSERT(r);
    sort* seq_sort = nullptr;
    if (!seq().is_re(r, seq_sort))
        return false;
    expr_ref node = mk_fromre(r);
    return materialize(node, mode, threshold, oracle, result);
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

    simplify(result);

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