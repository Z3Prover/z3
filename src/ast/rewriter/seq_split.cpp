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
            TRACE(seq, tout << "split_set::imp: " << this << " " << mk_pp(r, m) << " threshold: " << m_threshold << "\n");
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
            return (a_it == a_end && b_it == b_end) || a_it.failed() || b_it.failed();
        }
        void next() {
            SASSERT(!at_end());
            if (b_it != b_end)
                ++b_it;

            if (b_it == b_end) {
                ++a_it;
                if (a_it != a_end)
                    b_it.m_imp->rewind();
            }
        }
        void consume() override {
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
            init();
            if (m_intersection)
                m_intersection->consume();
        }
    };

    struct concat_left : public split_set::consumer {
        split_set a_s;
        split_set::iterator a_it;
        split_set::iterator a_end;
        expr_ref b;
        concat_left(split_set&& a_src, expr *b)
            :  a_s(std::move(a_src)), a_it(a_s.begin()), a_end(a_s.end()), b(b, a_s.m_imp->m) {}

        void consume() override {
            while (a_it != a_end && !parent().has_split()) {
                auto [p, q] = *a_it;
                parent().push_split(p, parent().i.rw.mk_re_append(q, b));
                ++a_it;
            }
            if (a_it.failed())
                parent().set_failure();
        }
    };

    struct concat_right : public split_set::consumer {
        expr_ref a;        
        split_set b_s;
        split_set::iterator b_it;
        split_set::iterator b_end;
        concat_right(expr* a, split_set&& b_src) : a(a, b_src.m_imp->m), b_s(std::move(b_src)), b_it(b_s.begin()), b_end(b_s.end()) {}

        void consume() override {
            while (b_it != b_end && !parent().has_split()) {
                auto [p, q] = *b_it;
                parent().push_split(parent().i.rw.mk_re_append(a, p), q);
                ++b_it;
            }
            if (b_it.failed())
                parent().set_failure();
        }
    };


    // TODO: can be written as a.sigma(b) u sigma(a).b filtering out eps on one union.
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
    bool m_at_end;
    bool m_failure = false;
    imp(split_set &s, bool at_end) : s(s), i(*s.m_imp), m(i.m), seq(i.seq), re(i.re), m_cont(m), m_at_end(at_end) {
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
            // TODO: we can be strategic about choosing what to unfold, 
            // and perform early subsumption check
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

    void unfold(expr* r) {
        TRACE(seq, tout << "unfold " << mk_pp(r, m) << "\n");
        SASSERT(seq.is_re(r));
        if (re.is_empty(r))
            return;

        SASSERT(!m_consumer);
        auto mk_eps = [&]() { return expr_ref(re.mk_epsilon(i.m_seq_sort), m); };
        expr *a, *b;
        if (re.is_union(r, a, b)) {
            m_cont.push_back(a);
            m_cont.push_back(b);
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

        // star: sigma(a*) = { <eps, eps> } cup a*.sigma(a).a*
        auto add_star = [&](expr *r, expr* a) {
            split_set sigma_a(i.rw, a, i.m_threshold, {});
            auto *c_left = alloc(concat_left, std::move(sigma_a), r);
            split_set sigma_aa(i.rw, nullptr, i.m_threshold, {});
            auto *c_right = alloc(concat_right, r, std::move(sigma_aa));
            auto &parent = *c_right->b_it.m_imp;
            parent.m_consumer = c_left;
            c_left->set_parent(parent);
            parent.init();
            m_consumer = c_right;
            m_consumer->set_parent(*this);
        };

        if (re.is_star(r, a)) {
            auto eps = mk_eps();
            push_split(eps, eps);
            add_star(r, a);
            return;
        }

        // plus: a+ = a.a* ; sigma(a+) = a*.sigma(a).a*  (star rule without <eps,eps>)
        if (re.is_plus(r, a)) {
            const expr_ref star(re.mk_star(a), m);  // a*
            add_star(star, a);
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

        set_failure(r);
    }

    void set_failure(expr* r) {
        TRACE(seq, tout << "split_set::iterator::unfold: unhandled regex: " << mk_pp(r, m) << "\n");
        set_failure();
        m_at_end = true;
    }

    bool at_end() const {
        TRACE(seq, tout << "split_set::iterator::at_end: " << this << " " << m_at_end << " " << m_qhead << "/" << m_splits.size() << "\n");
        return m_failure || (m_at_end && m_qhead == m_splits.size());
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

    expr_ref_vector tokens(m);
    vector<expr *> stack;
    stack.push_back(str);

    while (!stack.empty()) {
        expr *cur = stack.back();
        stack.pop_back();
        expr *l, *r;
        if (seq.str.is_concat(cur, l, r)) {
            stack.push_back(r);
            stack.push_back(l);
        }
        else
            tokens.push_back(expr_ref(cur, m));
    }

    expr *ch;
    unsigned i = 0;

    // TODO: Do this for the back as well (also, why did no rule before do that?)

    if (tokens.empty())
        return {expr_ref(m), expr_ref(m)};

    // Choose the factorization boundary so the tail starts with the
    // longest run of concrete characters c.
    // This gives the split-engine lookahead oracle the most pruning information.
    // head = u' (tokens before the run), tail = c � u''' (tokens from the run onward).
    const unsigned total = tokens.size();
    unsigned run_start = 0, run_len = 0;
    for (i = 1; i < total;) {
        if (!(seq.str.is_unit(tokens.get(i), ch) && seq.is_const_char(ch))) {
            i++;
            continue;
        }
        unsigned j = i;
        while (j < total && seq.str.is_unit(tokens.get(j), ch) && seq.is_const_char(ch)) {
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
    expr *head = tokens.get(0);
    for (i = 1; i < p; i++) {
        head = seq.str.mk_concat(head, tokens.get(i));
    }
    expr *tail = seq.str.mk_empty(head->get_sort());
    if (tokens.size() > p + run_len) {
        tail = tokens.get(p + run_len);
        for (i = p + run_len + 1; i < tokens.size(); i++) {
            tail = seq.str.mk_concat(tail, tokens.get(i));
        }
    }
    return {expr_ref(head, m), expr_ref(tail, m)};
}
