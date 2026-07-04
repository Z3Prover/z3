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

struct split_set::imp {
    ast_manager &m;
    seq_rewriter &rw;
    seq_util &seq;
    seq_util::rex &re;
    expr_ref r;
    unsigned m_threshold = UINT_MAX;
    split_oracle m_filter;
    sort *m_re_sort = nullptr;
    sort *m_seq_sort = nullptr;  // sequence sort the decls are built for
    bool m_failure = false;

    imp(seq_rewriter &rw, expr *r, unsigned threshold, split_oracle const &filter) : m(rw.m()), rw(rw), 
        seq(rw.u()), re(rw.u().re), r(r, m), m_threshold(threshold), m_filter(filter) {
        if (r) {
            VERIFY(seq.is_re(r, m_seq_sort));
            m_re_sort = r->get_sort();
        }
        if (m_threshold == 0)
            m_threshold = UINT_MAX;
    }
};

class split_set::consumer {
protected:
    split_set::iterator::imp *ip = nullptr;
public:
    virtual ~consumer() = default;
    virtual void consume() = 0;
    void set_parent(split_set::iterator::imp &i) {
        ip = &i;
    }
    split_set::iterator::imp &parent() {
        return *ip;
    }
};

struct split_set::iterator::imp {
    struct intersection : public split_set::consumer {

        split_set a_s, b_s;
        split_set::iterator a_it, a_end;
        split_set::iterator b_it, b_end;
        intersection(seq_rewriter& rw, split_set&& a_src, split_set&& b_src)
            : a_s(std::move(a_src)), b_s(std::move(b_src)),
            a_it(a_s.begin()), a_end(a_s.end()), 
            b_it(b_s.begin()), b_end(b_s.end()) {}
        bool at_end() const {
            return b_it == b_end || a_it == a_end || a_it.failed() || b_it.failed();
        }
        void next() {
            SASSERT(!at_end());
            SASSERT(b_it != b_end);
            ++b_it;

            if (b_it == b_end) {
                ++a_it;
                if (a_it != a_end) {
                    b_it.m_imp->rewind();
                    SASSERT(b_it != b_end);
                }
            }
        }
        void consume() override {
            TRACE(seq, tout << "intersection consume\n");
            while (!at_end() && !parent().has_split()) {
                auto [a1, a2] = *a_it;
                auto [b1, b2] = *b_it;
                auto a = parent().i.rw.mk_regex_inter_normalize(a1, b1);
                auto b = parent().i.rw.mk_regex_inter_normalize(a2, b2);
                parent().push_split(a, b);
                next();
            }
            if (b_it.failed() || a_it.failed())
                parent().set_failure();           
        }
    };

    // Complement of a split-set via De Morgan: ~S = cap_{s in S} ~s with
    //   ~<D,N> = { <~D, .*>, <.*, ~N> }  and  ~{} = { <.*, .*> }.
    // May produce up to 2^|sp| pairs (bounded by the threshold).  A threshold
    // overrun must abort entirely: a partial fold is a strictly weaker (unsound)
    // split-set, since each ~sp[i] further constrains ~S.

    struct complement : public split_set::consumer {

        split_set a_s;
        split_set::iterator it, end;
        bool m_init = false;
        scoped_ptr<consumer> m_intersection;
        

        complement(split_set&& a) : a_s(std::move(a)), it(a_s.begin()), end(a_s.end())
        { }

        void init() {
            if (m_init)
                return;
            m_init = true;    
            auto &p = parent();
            expr_ref full(p.seq.re.mk_full_seq(p.i.m_re_sort), p.m);
            m_intersection = nullptr;

            while (it != end && !it.failed()) {
                auto [a, b] = *it;
                split_set A(p.i.rw, nullptr, p.i.m_threshold, p.i.m_filter);                               
                split_set B(p.i.rw, nullptr, p.i.m_threshold, p.i.m_filter);
                auto inter = alloc(intersection, p.i.rw, std::move(A), std::move(B));
                if (m_intersection) {
                    m_intersection->set_parent(*inter->a_it.m_imp);
                    inter->a_it.m_imp->m_consumer = m_intersection.detach();
                }
                else 
                    inter->a_it.m_imp->push_split(full, full);  
                inter->b_it.m_imp->push_split(full, p.i.rw.mk_complement(b));
                inter->b_it.m_imp->push_split(p.i.rw.mk_complement(a), full);
                inter->a_it.m_imp->init();
                inter->b_it.m_imp->init();
                m_intersection = inter;
                ++it;
            }
            if (m_intersection)
                m_intersection->set_parent(p);
            else 
                p.push_split(full, full);
            if (it.failed())
                p.set_failure();
        }

        void consume() override {
            TRACE(seq, tout << "complement consume\n");
            init();
            if (m_intersection)
                m_intersection->consume();
        }
    };

    struct concat_sandwitch : public split_set::consumer {
        expr_ref a;        
        split_set b_s;
        expr_ref c;
        split_set::iterator b_it;
        split_set::iterator b_end;
        concat_sandwitch(expr* a, split_set&& b_src, expr* c) : 
            a(a, b_src.m_imp->m), b_s(std::move(b_src)), c(c, b_s.m_imp->m), b_it(b_s.begin()), b_end(b_s.end()) {}

        void consume() override {
            while (b_it != b_end && !parent().has_split()) {
                auto [p, q] = *b_it;
                parent().push_split(parent().i.rw.mk_re_append(a, p), parent().i.rw.mk_re_append(q, c));
                ++b_it;
            }
            if (b_it.failed())
                parent().set_failure();
        }
    };

    struct concat : split_set::consumer {
        expr_ref a, b;
        split_set a_s, b_s;
        split_set::iterator a_it, a_end;
        split_set::iterator b_it, b_end;
        concat(seq_rewriter& rw, expr *a, expr *b, unsigned threshold)
            : a(a, rw.m()), b(b, rw.m()), 
              a_s(rw, a, threshold, {}), b_s(rw, b, threshold, {}), 
              a_it(a_s.begin()), a_end(a_s.end()), b_it(b_s.begin()), b_end(b_s.end()) {}

        bool at_end() const {            
            return a_it == a_end && b_it == b_end;
        }

        void consume() override {
            while (!parent().has_split() && !at_end() && !a_it.failed() && !b_it.failed()) {
                if (a_it == a_end) {
                    auto [p, q] = *b_it;
                    parent().push_split(parent().i.rw.mk_re_append(a, p), q);
                    ++b_it;
                }
                else {
                    auto [p, q] = *a_it;
                    parent().push_split(p, parent().i.rw.mk_re_append(q, b));
                    ++a_it;
                }
            }
            if (a_it.failed() || b_it.failed())
                parent().set_failure();
        }

    };
    split_set &s;
    split_set::imp &i;
    ast_manager &m;
    seq_util &seq;
    seq_util::rex &re;
    expr_ref_vector m_cont;
    vector<std::pair<expr_ref, expr_ref>> m_splits;
    bool m_init = false;
    unsigned m_qhead = 0;
    scoped_ptr<split_set::consumer> m_consumer;
    bool m_end_marker;
    bool m_at_end = false;
    bool m_failure = false;
    imp(split_set &s, bool at_end) : s(s), i(*s.m_imp), m(i.m), seq(i.seq), re(i.re), m_cont(m), m_end_marker(at_end) {
        if (at_end)
            m_init = true;
        else if (i.r) {
            m_cont.push_back(i.r);
            init();
        }        
    }

    void set_failure() {
        m_failure = true;
        s.m_imp->m_failure = true;
    }

    bool has_split() {
        SASSERT(m_init);     
        return m_qhead < m_splits.size();
    }

    void rewind() {
        TRACE(seq, tout << "rewind: " << m_splits.size() << "\n";);
        m_qhead = 0;
        m_at_end = m_qhead == m_splits.size();
        SASSERT(m_cont.empty());
        SASSERT(!m_consumer);
    }

    void init() {
        if (!m_init)
            next();
        m_init = true;
    }

    void next() {
        m_init = true;
        while (!m_failure && !m_at_end) {
            if (has_split())
                return;
            if (m_consumer) {
                m_consumer->consume();
                if (has_split())
                    return;
                m_consumer = nullptr;
            }
            if (m_cont.empty()) {
                m_at_end = true;
                return;
            }
            expr_ref last(m_cont.back(), m);
            m_cont.pop_back();
            unfold(last);
        }
    }

    void push_split(expr *_a, expr *_b) {
        expr_ref a(_a, m), b(_b, m);
        if (m_failure)
            return;
        if (i.m_filter && !i.m_filter(a, b))
            return;   
        if (re.is_empty(a) || re.is_empty(b))
            return;
        if (re.get_info(a).min_length == UINT_MAX)
            return;
        if (re.get_info(b).min_length == UINT_MAX)
            return;
        // subsumption checking
        for (auto const &[p, q] : m_splits) {
            if (i.rw.is_subset(a, p) && i.rw.is_subset(b, q))
                return;
        }
        for (unsigned j = m_qhead; j < m_splits.size(); ++j) {
            auto const &[p, q] = m_splits[j];
            if (i.rw.is_subset(p, a) && i.rw.is_subset(q, b)) {
                m_splits[j] = {a, b};            
                return;
            }
            if (a == p) {
                b = i.rw.mk_union(q, b);
                m_splits[j] = {a, b};
                return;
            }
            if (b == q) {
                a = i.rw.mk_union(p, a);
                m_splits[j] = {a, b};
                return;
            }
        }
        TRACE(seq, tout << "push <" << a << ", " << b << ">\n");
        m_splits.push_back({a, b});
        if (m_splits.size() > i.m_threshold) {
            TRACE(seq, tout << "size of split set exceeds threshold");
            set_failure();
        }
    }

    bool is_cheap(expr* r) {
        if (re.is_empty(r))
            return true;
        if (re.is_union(r))
            return true;
        if (re.is_to_re(r))
            return true;
        if (re.is_full_char(r) || re.is_range(r) || re.is_of_pred(r))
            return true;
        if (re.is_full_seq(r))
            return true;

        return false;
    }

    void push_cont(expr* r) {
        if (is_cheap(r))
            unfold(r);
        else
            m_cont.push_back(r);
    }

    void unfold(expr* r) {        
        TRACE(seq, tout << "unfold " << mk_pp(r, m) << "\n");
        SASSERT(seq.is_re(r));
        if (re.is_empty(r))
            return;

        SASSERT(!m_consumer);
        auto mk_eps = [&]() { return expr_ref(re.mk_epsilon(i.m_seq_sort), m); };
        expr *a, *b;
        if (re.is_union(r, a, b)) {
            push_cont(a);
            push_cont(b);
            return;
        }

        if (re.is_intersection(r, a, b)) {
            split_set a_s(i.rw, a, i.m_threshold, {});
            split_set b_s(i.rw, b, i.m_threshold, {});
            m_consumer = alloc(intersection, i.rw, std::move(a_s), std::move(b_s));
            m_consumer->set_parent(*this);
            return;
        }

        if (re.is_complement(r, a)) {
            split_set sigma_a(i.rw, a, i.m_threshold, {});
            m_consumer = alloc(complement, std::move(sigma_a)); 
            m_consumer->set_parent(*this);
            return;
        }

        if (re.is_concat(r, a, b)) {
            TRACE(seq, tout << "concat-start: " << mk_pp(a, i.m) << " " << mk_pp(b, i.m) << "\n");
            m_consumer = alloc(concat, i.rw, a, b, i.m_threshold);
            m_consumer->set_parent(*this);
            return;
        }

        if (re.is_to_re(r, a)) {
            zstring str;
            if (seq.str.is_concat(a, a, b)) {
                m_cont.push_back(re.mk_concat(re.mk_to_re(a), re.mk_to_re(b)));
            }
            else if (seq.str.is_unit(a, b)) {
                auto eps = mk_eps();
                push_split(eps, r);
                push_split(r, eps);
            }
            else if (seq.str.is_string(a, str)) {
                for (unsigned i = 0; i <= str.length(); ++i) {
                    const expr_ref p(re.mk_to_re(seq.str.mk_string(str.extract(0, i))), m);
                    const expr_ref q(re.mk_to_re(seq.str.mk_string(str.extract(i, str.length() - i))), m);
                    push_split(p, q);
                }
            }
            else 
                set_failure(r);
            return;
        }

        if (re.is_epsilon(r)) {
            push_split(r, r);
            return;
        }

        // left . sigma(a) . right
        auto add_sandwitch = [&](expr *left, expr *a, expr *right) {
            split_set sigma_a(i.rw, a, i.m_threshold, {});
            m_consumer = alloc(concat_sandwitch, left, std::move(sigma_a), right);
            m_consumer->set_parent(*this);
        };

        // star: sigma(a*) = { <eps, eps> } cup a*.sigma(a).a*
        if (re.is_star(r, a)) {
            auto eps = mk_eps();
            push_split(eps, eps);
            add_sandwitch(r, a, r);
            return;
        }

        // plus: a+ = a.a* ; sigma(a+) = a*.sigma(a).a*  (star rule without <eps,eps>)
        if (re.is_plus(r, a)) {
            const expr_ref star(re.mk_star(a), m);  // a*
            add_sandwitch(star, a, star);
            return;
        }

        if (re.is_diff(r, a, b)) {
            m_cont.push_back(i.rw.mk_inter(a, i.rw.mk_complement(b)));
            return;            
        }

         if (re.is_full_char(r) || re.is_range(r) || re.is_of_pred(r)) {
            auto eps = mk_eps();
            push_split(r, eps);
            push_split(eps, r);
            return;
        }

        // .* : sigma(.*) = { <.*, .*> }
        if (re.is_full_seq(r)) {
            push_split(r, r);
            return;
        }

         // abbreviation
        // optional: a? = eps | a ; sigma(a?) = sigma(eps | a) = eps cup sigma(a)
        if (re.is_opt(r, a)) {
            auto eps = mk_eps();
            push_split(eps, eps);
            push_cont(a);
            return;
        }

        // loop: r{l,h} = \bigcup_{l <= j <= h} r^j.
        // A split either singles out the i-th copy of a (0 <= i < h) as
        // <r^i . D, N . r{lo_i,hi_i}> for <D,N> in sigma(a),
        // where r{lo_i,hi_i} folds the tail counts j-i-1, over every remaining
        // j in [l,h] with j > i, into a single loop [<eps,eps> when l == 0]
        unsigned l, h;
        if (re.is_loop(r, a, l, h)) {
            if (l == 0) {
                auto eps = mk_eps();
                push_split(eps, eps);
            }
            for (unsigned i = 0; i < h; i++) {
                const expr_ref pre(re.mk_loop_proper(a, i, i), m);
                const unsigned lo_i = l > i + 1 ? l - i - 1 : 0;
                const unsigned hi_i = h - i - 1;
                const expr_ref post(re.mk_loop_proper(a, lo_i, hi_i), m);
                add_sandwitch(pre, a, post);               
            }
            return;
        }

        set_failure(r);
    }

    void set_failure(expr* r) {
        TRACE(seq, tout << "split_set::iterator::unfold: unhandled regex: " << mk_pp(r, m) << "\n");
        set_failure();
        m_at_end = true;
    }

    bool at_end() const {
        return m_end_marker || ((m_failure || m_at_end) && m_qhead == m_splits.size());
    }
};

split_set::split_set(seq_rewriter &rw, expr *r, unsigned threshold, split_oracle const &oracle) {
    m_imp = alloc(imp, rw, r, threshold, oracle);
}

split_set::~split_set() {
    dealloc(m_imp);
}

split_set::split_set(split_set&& other) noexcept : m_imp(other.m_imp) {
    other.m_imp = nullptr;
}

split_set::iterator::iterator(split_set const &s, bool at_end) {
    m_imp = alloc(imp, const_cast<split_set&>(s), at_end);
}

split_set::iterator::~iterator() {
    dealloc(m_imp);
}

split_set::iterator split_set::begin() const {
    return iterator(*this, false);
}

split_set::iterator split_set::end() const {
    return iterator(*this, true);
}

split_set::iterator& split_set::iterator::operator++() {
    SASSERT(m_imp->m_init);
    m_imp->m_qhead++;
    m_imp->next();
    return *this;
}

std::pair<expr_ref, expr_ref> split_set::iterator::operator*() const {  
    SASSERT(m_imp->m_init);
    return m_imp->m_splits[m_imp->m_qhead];
}

bool split_set::iterator::operator==(split_set::iterator const &other) const {
    return m_imp->at_end() && other.m_imp->at_end();
}

bool split_set::iterator::failed() const {
    return m_imp->m_failure;
}

bool split_set::failed() const {
    return m_imp->m_failure;
}

std::pair<expr_ref, expr_ref> split_set::try_split_sequence(expr *str) {
    ast_manager &m = m_imp->m;
    auto &seq = m_imp->seq;

    if (!seq.str.is_concat(str))
        return {expr_ref(m), expr_ref(m)};
    expr_ref_vector tokens(m);
    seq.str.get_concat(str, tokens);
    SASSERT(tokens.size() > 1);

    expr *ch;
    unsigned i = 0;


    // Choose the factorization boundary so the tail starts with the
    // longest run of concrete characters c.
    // This gives the split-engine lookahead oracle the most pruning information.
    // head = u' (tokens before the run), tail = c � u''' (tokens from the run onward).
    const unsigned total = tokens.size();
    unsigned run_start = 0, run_len = 0;
    for (i = 1; i < total;) {
        if (!(seq.str.is_unit(tokens.get(i), ch) && m.is_value(ch))) {
            i++;
            continue;
        }
        unsigned j = i;
        while (j < total && seq.str.is_unit(tokens.get(j), ch) && m.is_value(ch)) {
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
    SASSERT(p < total);
    expr_ref head(tokens.get(p - 1), m);
    for (unsigned i = p - 1; i-- > 0;) 
        head = seq.str.mk_concat(tokens.get(i), head);
        
    expr_ref tail(tokens.back(), m);
    for (unsigned i = tokens.size() - 1; i-- > p;)
        tail = seq.str.mk_concat(tokens.get(i), tail);
    
    TRACE(seq, tout << "split_set::try_split_sequence: " << mk_pp(str, m) << " -> " << head << " | "
                    << tail << "\n");
    return { head, tail };
}

#if 0
// One level of the sigma rules.  Mirrors the historic eager `compute`, except it
// emits *suspended* split-algebra terms (from_re / lcat / rcat / inter / compl) for
// the subterms instead of recursing.  `mode` is irrelevant here: weak vs. strong is
// decided when `head_normalize` reaches an inter / compl node.
namespace {
    // Cofactor path condition `pred` (a Boolean over x = (:var 0)) -> the canonical
    // range_predicate (union of ranges) of the characters satisfying it.  Returns
    // false on a construct outside {true,false,and,or,not,=,char.<=} over x.
    static bool pred_to_rp(ast_manager &m, seq_util &sq, expr *x, expr *pred, unsigned maxc,
                           seq::range_predicate &out) {
        expr *a = nullptr, *b = nullptr;
        unsigned c = 0;
        if (m.is_true(pred)) {
            out = seq::range_predicate::top(maxc);
            return true;
        }
        if (m.is_false(pred)) {
            out = seq::range_predicate::empty(maxc);
            return true;
        }
        if (m.is_eq(pred, a, b)) {
            if (a == x && sq.is_const_char(b, c)) {
                out = seq::range_predicate::singleton(c, maxc);
                return true;
            }
            if (b == x && sq.is_const_char(a, c)) {
                out = seq::range_predicate::singleton(c, maxc);
                return true;
            }
            return false;
        }
        if (sq.is_char_le(pred, a, b)) {
            if (b == x && sq.is_const_char(a, c)) {
                out = seq::range_predicate::range(c, maxc, maxc);
                return true;
            }
            if (a == x && sq.is_const_char(b, c)) {
                out = seq::range_predicate::range(0, c, maxc);
                return true;
            }
            return false;
        }
        if (m.is_not(pred, a)) {
            seq::range_predicate s(maxc);
            if (!pred_to_rp(m, sq, x, a, maxc, s))
                return false;
            out = ~s;
            return true;
        }
        if (m.is_and(pred)) {
            out = seq::range_predicate::top(maxc);
            for (expr *arg : *to_app(pred)) {
                seq::range_predicate s(maxc);
                if (!pred_to_rp(m, sq, x, arg, maxc, s))
                    return false;
                out = out & s;
            }
            return true;
        }
        if (m.is_or(pred)) {
            out = seq::range_predicate::empty(maxc);
            for (expr *arg : *to_app(pred)) {
                seq::range_predicate s(maxc);
                if (!pred_to_rp(m, sq, x, arg, maxc, s))
                    return false;
                out = out | s;
            }
            return true;
        }
        return false;
    }
}  // namespace

// Single-character regex for a cofactor path condition `pred` (a Boolean over the
// character (:var 0)).  Materialized via the canonical seq::range_predicate as a
// union-of-ranges regex (fully supported by the derivative / emptiness / primitive
// path, and canonical so equivalent classes share AST identity).  Falls back to
// of_pred(lambda) only for predicates outside the recognized range fragment.
expr_ref seq_split::mk_charclass_re(expr *pred, sort *seq_sort) {
    seq_util &sq = seq();
    sort *cs = sq.mk_char_sort();
    expr_ref var0(m.mk_var(0, cs), m);
    seq::range_predicate rp(sq.max_char());
    // NSB: can we be lazy about expanding to range predicate normal form, just use lambdas as defalt
    // and use general purpose processing to handle of_pred?
    if (pred_to_rp(m, sq, var0, pred, sq.max_char(), rp))
        return seq::range_predicate_to_regex(sq, rp, seq_sort);
    symbol nm("c");
    expr_ref lam(m.mk_lambda(1, &cs, &nm, pred), m);
    return expr_ref(re().mk_of_pred(lam), m);
}

// r == E(r) | RE(LF(delta(r))): peel one character through the symbolic derivative
// (Brzozowski cofactors) and recurse.  Shared by the complement and intersection
// cases to avoid the De Morgan / cross-product blow-up.  delta distributes over
// both ~ and &, so LF(delta(r)) = { (alpha_i, tgt_i) } with tgt_i the (complement /
// intersection of) character-derivatives.  Records `r` in `deriv_memo` as a cycle
// guard.  Returns a null expr_ref when nullability of `r` is not statically
// decidable (the caller then falls back to its structural rule).
bool seq_split::iterator::imp::try_derivative_split(expr *r, sort *seq_sort, obj_hashtable<expr> &deriv_memo) {
    seq_util::rex &rex = re();
    expr_ref nb = m_rw.is_nullable(r);
    if (!m.is_true(nb) && !m.is_false(nb))
        return false;  // undecidable -> fall back
    deriv_memo.insert(r);
    // NSB: take a reference count on r here for the table?
    sort *re_sort = rex.mk_re(seq_sort);
    expr_ref unfolded(m);
    if (m.is_true(nb)) {
        auto eps = re.mk_epsilon(seq_sort);
        push_split(eps, eps);
    }
    expr_ref_pair_vector cofs(m);
    m_rw.brz_derivative_cofactors(r, cofs);  // { (alpha_i, tgt_i) } = LF(delta(r))
    for (auto const &[cond, tgt] : cofs) {
        expr_ref alpha = mk_charclass_re(cond, seq_sort);  // single-char regex
        expr_ref term(rex.mk_concat(alpha, tgt), m);       // alpha_i . tgt_i
        push_cont(term);
    }
    return true;
}

#endif