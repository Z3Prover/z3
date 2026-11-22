/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regular_rewriter.h

Abstract:

    Shared local regular-language rewrites. Contextual assertion propagation
    and aggregate-first scheduling remain in seq_regular_simplifier.

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/rewriter/th_rewriter.h"
#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <unordered_map>
#include <vector>

class seq_regular_rewriter {
public:
    enum class failure { unsupported, budget, canceled };
protected:

    ast_manager& m;
    seq_util u;
    arith_util a;
    seq_rewriter rw;
    bool_rewriter br;
    expr_ref_vector pin;
    expr_ref empty, epsilon, character, all;
    unsigned max_steps;
    unsigned& steps;
    unsigned& preimages;
    enum class comparison_kind { eq, ne, le, ge, lt, gt };
    std::map<std::pair<comparison_kind, rational>, expr*> decimal_languages;
    struct decimal_rewrite {
        expr* original;
        expr* replacement;
        bool magnitude;
    };
    std::vector<decimal_rewrite> decimal_rewrites;
    struct linear {
        rational constant;
        std::map<expr*, rational> terms;
        void add(linear const& b, rational const& scale) {
            constant += scale * b.constant;
            for (auto const& [e, n] : b.terms) {
                rational value = terms[e] + scale * n;
                if (value.is_zero()) terms.erase(e);
                else terms[e] = value;
            }
        }
        bool operator==(linear const& b) const { return constant == b.constant && terms == b.terms; }
    };
    std::unordered_map<expr*, linear> linears;
    struct scalar_range {
        std::optional<rational> lo, hi;
    };
    using range_map = std::unordered_map<expr*, scalar_range>;
    range_map scalar_ranges;
    std::unordered_map<expr*, unsigned> length_bounds;
    struct bounded_occurrences {
        expr* character_class;
        zstring needle;
        unsigned maximum;
    };
    std::unordered_map<expr*, bounded_occurrences> occurrence_languages;

    // A recognized "split s at the first occurrence of delimiter" shape:
    // prefix/prefix_including is the part of `source` before/through that
    // occurrence, tail/tail_including is the part at/after it. See
    // first_cut() below for how this is recognized from str.extract's
    // begin/length arguments, and preimage() for how it is used.
    struct cut {
        enum kind { prefix, prefix_including, tail, tail_including } type;
        expr* source;
        zstring delimiter;
    };

    void tick() {
        if (!m.inc()) throw failure::canceled;
        if (++steps > max_steps) throw failure::budget;
    }
    expr* keep(expr* e) { pin.push_back(e); return e; }
    expr* keep(expr_ref const& e) { return keep(e.get()); }
    bool numeral(expr* e, rational const& n) { rational v; return a.is_numeral(e, v) && v == n; }
    bool is_literal_binding(expr* e) {
        expr* x;
        expr* y;
        if (!m.is_eq(e, x, y))
            return false;
        if (u.str.is_string(x))
            std::swap(x, y);
        return is_uninterp_const(x) && u.is_string(x->get_sort()) && u.str.is_string(y);
    }
    linear const& affine(expr* e, unsigned depth = 0) {
        tick();
        auto it = linears.find(e);
        if (it != linears.end()) return it->second;
        if (depth > 256) throw failure::budget;
        linear result;
        rational value;
        if (a.is_numeral(e, value))
            result.constant = value;
        else if (a.is_add(e) || a.is_sub(e) || a.is_uminus(e)) {
            app* t = to_app(e);
            for (unsigned i = 0; i < t->get_num_args(); ++i) {
                rational sign((a.is_uminus(e) || (a.is_sub(e) && i > 0)) ? -1 : 1);
                result.add(affine(t->get_arg(i), depth + 1), sign);
            }
        }
        else if (a.is_mul(e) && to_app(e)->get_num_args() == 2 &&
                 (a.is_numeral(to_app(e)->get_arg(0), value) ||
                  a.is_numeral(to_app(e)->get_arg(1), value))) {
            app* t = to_app(e);
            expr* other = a.is_numeral(t->get_arg(0)) ? t->get_arg(1) : t->get_arg(0);
            result.add(affine(other, depth + 1), value);
        }
        else
            result.terms[e] = rational(1);
        keep(e);
        return linears.emplace(e, std::move(result)).first->second;
    }
    bool same(expr* e, expr* f) { return affine(e) == affine(f); }
    bool single(linear const& l, expr* e, rational const& coefficient = rational(1)) {
        return l.terms.size() == 1 && l.terms.begin()->first == e && l.terms.begin()->second == coefficient;
    }
    unsigned bounded_length(expr* e, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        auto it = length_bounds.find(e);
        if (it != length_bounds.end()) return it->second;
        unsigned result = UINT_MAX;
        expr *source, *offset, *count, *condition, *yes, *no;
        if (u.str.is_extract(e, source, offset, count)) {
            linear const& size = affine(count);
            if (size.terms.empty()) {
                if (size.constant <= 0) result = 0;
                else if (size.constant.is_unsigned())
                    result = std::min(result, size.constant.get_unsigned());
            }
            if (result != 0)
                result = std::min(result, bounded_length(source, depth + 1));
        }
        else if (u.str.is_concat(e)) {
            result = 0;
            for (expr* arg : *to_app(e))
                result = add_truncate(result, bounded_length(arg, depth + 1));
        }
        else if (m.is_ite(e, condition, yes, no)) {
            unsigned left = bounded_length(yes, depth + 1);
            unsigned right = bounded_length(no, depth + 1);
            result = std::max(left, right);
        }
        else
            result = u.str.max_length(e);
        length_bounds.emplace(e, result);
        return result;
    }
    // Recognizes str.extract(s, begin, length) as a `cut` of `s` at the
    // first occurrence of a single delimiter character, i.e. the common
    // manual-split idiom built from str.indexof(s, ch, 0) (one-character
    // needle, searched from position 0): begin/length are affine in that
    // indexof term, and the four cases below are exactly
    //   prefix:           s.extract(0, indexof)            (before ch)
    //   prefix_including: s.extract(0, indexof + 1)         (through ch)
    //   tail:             s.extract(indexof + 1, len(s) - indexof - 1)  (after ch)
    //   tail_including:   s.extract(indexof, len(s) - indexof)          (at/after ch)
    // Returns false (not a recognized cut) for any other extract shape.
    bool first_cut(expr* e, cut& out) {
        expr *s, *begin, *length;
        if (!u.str.is_extract(e, s, begin, length)) return false;
        linear b = affine(begin), len = affine(length);
        std::set<expr*> candidates;
        for (auto const& [t, _] : b.terms) candidates.insert(t);
        for (auto const& [t, _] : len.terms) candidates.insert(t);
        for (expr* t : candidates) {
            expr *source, *needle, *offset;
            zstring ch;
            if (!u.str.is_index(t, source, needle, offset) || source != s ||
                !numeral(offset, rational(0)) || !u.str.is_string(needle, ch) || ch.length() != 1)
                continue;
            if (numeral(begin, rational(0)) && single(len, t) &&
                (len.constant.is_zero() || len.constant.is_one())) {
                out = {len.constant.is_zero() ? cut::prefix : cut::prefix_including, s, ch};
                return true;
            }
            linear sum = len;
            sum.add(b, rational(1));
            expr_ref slen(u.str.mk_length(s), m);
            if (sum == affine(slen) && single(b, t) &&
                (b.constant.is_zero() || b.constant.is_one())) {
                out = {b.constant.is_zero() ? cut::tail_including : cut::tail, s, ch};
                return true;
            }
        }
        return false;
    }
    expr* boolean(bool conjunction, expr_ref_vector const& es) {
        expr_ref result(m);
        if (conjunction) br.mk_and(es.size(), es.data(), result);
        else br.mk_or(es.size(), es.data(), result);
        return keep(result);
    }
    expr* neg(expr* e) {
        expr_ref result(m);
        br.mk_not(e, result);
        return keep(result);
    }
    expr* normalize_node(app* t, expr_ref_vector const& args) {
        tick();
        if (m.is_and(t) || m.is_or(t)) return boolean(m.is_and(t), args);
        if (m.is_not(t)) return neg(args[0]);
        expr* e = keep(m.mk_app(t->get_decl(), args.size(), args.data()));
        expr *x, *y, *c, *yes, *no;
        if (m.is_eq(e, x, y)) {
            if (x == y) return keep(m.mk_true());
            for (unsigned i = 0; i < 2; ++i) {
                if (m.is_ite(x, c, yes, no) && numeral(yes, rational(1)) && numeral(no, rational(0))) {
                    if (numeral(y, rational(1))) return c;
                    if (numeral(y, rational(0))) return neg(c);
                }
                std::swap(x, y);
            }
        }
        if (a.is_int(e) && (a.is_add(e) || a.is_sub(e) || a.is_uminus(e))) {
            auto const& l = affine(e);
            if (l.terms.empty()) return keep(a.mk_numeral(l.constant, true));
            if (l.constant.is_zero() && l.terms.size() == 1 && l.terms.begin()->second.is_one())
                return l.terms.begin()->first;
        }
        expr *s, *begin, *length;
        if (u.str.is_extract(e, s, begin, length) && numeral(begin, rational(0))) {
            expr_ref slen(u.str.mk_length(s), m);
            if (same(length, slen)) return s;
        }
        if (u.str.is_concat(e) && args.size() == 2) {
            expr *source, *needle, *replacement;
            if (u.str.is_replace(args[0], source, needle, replacement)) {
                expr *right = args[1], *rs, *rn, *rr;
                bool twice = u.str.is_replace(right, rs, rn, rr);
                cut l, r;
                zstring n, repl;
                if (first_cut(source, l) && first_cut(twice ? rs : right, r) &&
                    l.type == cut::prefix_including && r.type == cut::tail &&
                    l.source == r.source && l.delimiter == r.delimiter &&
                    u.str.is_string(needle, n) && n == l.delimiter) {
                    expr* once = keep(u.str.mk_replace(l.source, needle, replacement));
                    if (!twice) return once;
                    if (rn == needle && rr == replacement && u.str.is_string(replacement, repl) && !repl.contains(n))
                        return keep(u.str.mk_replace(once, needle, replacement));
                }
            }
        }
        return e;
    }
    expr* lit(zstring const& s) {
        tick();
        expr_ref str(u.str.mk_string(s), m);
        return keep(rw.mk_to_re(str));
    }
    expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
    expr* cat(std::initializer_list<expr*> xs) {
        expr* result = epsilon;
        for (expr* x : xs) result = cat(result, x);
        return result;
    }
    expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
    expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
    expr* meet(expr* x, expr* y) {
        tick();
        return keep(rw.mk_inter(x, y));
    }
    expr* complement(expr* x) {
        tick();
        // Avoid expanding De Morgan's law; keep Boolean languages shared.
        expr* child;
        if (u.re.is_complement(x, child)) return child;
        if (u.re.is_empty(x)) return all;
        if (u.re.is_full_seq(x)) return empty;
        return keep(u.re.mk_complement(x));
    }
    // decimal_greater/decimal_language build a digit-by-digit lexicographic
    // comparison automaton for an optionally-zero-padded decimal numeral
    // (str.to_int's encoding): going from the least significant digit
    // backwards, `greater` accumulates "equal here, decided later" plus
    // "strictly higher digit here, anything after" alternatives, sharing
    // the common `suffix` language so the result stays linear in the
    // numeral's digit count instead of enumerating numbers.
    expr* decimal_range(unsigned lo, unsigned hi) {
        tick();
        return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
    }
    expr* decimal_greater(rational const& bound) {
        SASSERT(bound.is_int() && bound >= 0);
        std::string text = bound.to_string();
        if (text.size() > 4096) throw failure::budget;
        unsigned size = static_cast<unsigned>(text.size());
        expr* digits = decimal_range(0, 9);
        expr* suffix = epsilon;
        expr* greater = empty;
        // Shared suffixes keep the lexicographic comparison linear in the numeral's size.
        for (unsigned i = size; i-- > 0;) {
            tick();
            unsigned digit = text[i] - '0';
            expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
            greater = cat(exact, greater);
            if (digit < 9) {
                expr* higher = decimal_range(digit + 1, 9);
                expr* alternative = cat(higher, suffix);
                greater = join(greater, alternative);
            }
            suffix = cat(digits, suffix);
        }
        expr* nonzero = decimal_range(1, 9);
        expr* arbitrary = star(digits);
        expr* longer = cat({nonzero, suffix, arbitrary});
        greater = join(greater, longer);
        expr* zeros = lit(zstring("0"));
        zeros = star(zeros);
        return cat(zeros, greater);
    }
    expr* decimal_language(comparison_kind op, rational const& bound) {
        tick();
        auto key = std::make_pair(op, bound);
        auto found = decimal_languages.find(key);
        if (found != decimal_languages.end()) return found->second;
        expr* digits = decimal_range(0, 9);
        expr* repeated = star(digits);
        expr* valid = cat(digits, repeated);
        expr* language = nullptr;
        if (bound < 0) {
            switch (op) {
            case comparison_kind::eq: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
            case comparison_kind::ne: language = bound.is_minus_one() ? valid : all.get(); break;
            case comparison_kind::le: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
            case comparison_kind::lt: language = empty; break;
            case comparison_kind::ge: language = all; break;
            case comparison_kind::gt: language = bound.is_minus_one() ? valid : all.get(); break;
            default: UNREACHABLE(); break;
            }
        }
        else if (op == comparison_kind::eq || op == comparison_kind::ne) {
            std::string text = bound.to_string();
            if (text.size() > 4096) throw failure::budget;
            expr* zeros = lit(zstring("0"));
            zeros = star(zeros);
            expr* number = lit(zstring(text.c_str()));
            language = cat(zeros, number);
            if (op == comparison_kind::ne) language = complement(language);
        }
        else {
            if ((op == comparison_kind::ge || op == comparison_kind::lt) && bound.is_zero())
                language = valid;
            else {
                rational threshold = bound;
                if (op == comparison_kind::ge || op == comparison_kind::lt) --threshold;
                language = decimal_greater(threshold);
            }
            if (op == comparison_kind::le || op == comparison_kind::lt) language = complement(language);
        }
        decimal_languages.emplace(std::move(key), language);
        return language;
    }
    static comparison_kind reverse_comparison(comparison_kind op) {
        switch (op) {
        case comparison_kind::le: return comparison_kind::ge;
        case comparison_kind::ge: return comparison_kind::le;
        case comparison_kind::lt: return comparison_kind::gt;
        case comparison_kind::gt: return comparison_kind::lt;
        default: return op;
        }
    }
    expr* comparison(comparison_kind op, expr* term, rational const& bound) {
        expr* value = keep(a.mk_numeral(bound, true));
        switch (op) {
        case comparison_kind::eq: return keep(m.mk_eq(term, value));
        case comparison_kind::ne: {
            expr* eq = keep(m.mk_eq(term, value));
            return neg(eq);
        }
        case comparison_kind::le: return keep(a.mk_le(term, value));
        case comparison_kind::ge: return keep(a.mk_ge(term, value));
        case comparison_kind::lt: return keep(a.mk_lt(term, value));
        case comparison_kind::gt: return keep(a.mk_gt(term, value));
        default: UNREACHABLE(); return nullptr;
        }
    }
    bool comparison_operator(app* e, comparison_kind& op) {
        if (e->get_num_args() != 2 || !a.is_int(e->get_arg(0))) return false;
        if (m.is_eq(e)) op = comparison_kind::eq;
        else if (m.is_distinct(e)) op = comparison_kind::ne;
        else if (a.is_le(e)) op = comparison_kind::le;
        else if (a.is_ge(e)) op = comparison_kind::ge;
        else if (a.is_lt(e)) op = comparison_kind::lt;
        else if (a.is_gt(e)) op = comparison_kind::gt;
        else return false;
        return true;
    }
    // Cheap, cached interval bounds for str.stoi/str.len/ite terms (not a
    // general solve - just enough to let range_comparison() below decide a
    // comparison outright when the bounds alone already settle it).
    scalar_range range(linear const& value, unsigned depth = 0, range_map* context = nullptr) {
        scalar_range result{value.constant, value.constant};
        for (auto const& [term, coefficient] : value.terms) {
            scalar_range r = range(term, depth, context);
            if (coefficient.is_neg()) std::swap(r.lo, r.hi);
            if (result.lo && r.lo) *result.lo += coefficient * *r.lo;
            else result.lo.reset();
            if (result.hi && r.hi) *result.hi += coefficient * *r.hi;
            else result.hi.reset();
        }
        return result;
    }
    scalar_range range(expr* e, unsigned depth = 0, range_map* context = nullptr) {
        tick();
        if (depth > 256) throw failure::budget;
        auto& cache = context ? *context : scalar_ranges;
        auto it = cache.find(e);
        if (it != cache.end()) return it->second;
        scalar_range result;
        expr *s, *condition, *yes, *no;
        if (u.str.is_stoi(e, s)) {
            result.lo = rational(-1);
            unsigned size = bounded_length(s);
            if (size <= 4096) {
                rational limit(1);
                for (unsigned i = 0; i < size; ++i) {
                    tick();
                    limit *= rational(10);
                }
                result.hi = size ? limit - rational(1) : rational(-1);
            }
        }
        else if (u.str.is_length(e, s)) {
            result.lo = rational(0);
            unsigned size = bounded_length(s);
            if (size != UINT_MAX) result.hi = rational(size);
        }
        else if (m.is_ite(e, condition, yes, no)) {
            scalar_range y = range(affine(yes), depth + 1, context);
            scalar_range n = range(affine(no), depth + 1, context);
            if (y.lo && n.lo) result.lo = std::min(*y.lo, *n.lo);
            if (y.hi && n.hi) result.hi = std::max(*y.hi, *n.hi);
        }
        cache.emplace(e, result);
        return result;
    }
    expr* range_comparison(comparison_kind op, scalar_range const& r) {
        bool nonnegative = r.lo && *r.lo >= 0;
        bool positive = r.lo && *r.lo > 0;
        bool nonpositive = r.hi && *r.hi <= 0;
        bool negative = r.hi && *r.hi < 0;
        switch (op) {
        case comparison_kind::eq:
        case comparison_kind::ne:
            if (positive || negative) return keep(m.mk_bool_val(op == comparison_kind::ne));
            if (nonnegative && nonpositive) return keep(m.mk_bool_val(op == comparison_kind::eq));
            break;
        case comparison_kind::le:
            if (nonpositive || positive) return keep(m.mk_bool_val(nonpositive));
            break;
        case comparison_kind::lt:
            if (negative || nonnegative) return keep(m.mk_bool_val(negative));
            break;
        case comparison_kind::ge:
            if (nonnegative || negative) return keep(m.mk_bool_val(nonnegative));
            break;
        case comparison_kind::gt:
            if (positive || nonpositive) return keep(m.mk_bool_val(positive));
            break;
        }
        return nullptr;
    }
    // Simplifies `op(value, 0)` for a single-term affine value. Tries the
    // cheap range_comparison() short-circuit first, then - if the term is
    // an ite - pushes the comparison into both branches, folding it away
    // entirely when the ite is a min/max of the two comparison operands.
    expr* scalar_comparison(comparison_kind op, linear const& value, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (expr* result = range_comparison(op, range(value))) return result;
        if (value.terms.size() != 1) return nullptr;
        auto [term, coefficient] = *value.terms.begin();
        if (coefficient == rational(-1)) op = reverse_comparison(op);
        else if (!coefficient.is_one()) return nullptr;
        rational bound = -value.constant * coefficient;
        expr *condition, *yes, *no;
        if (!m.is_ite(term, condition, yes, no)) return nullptr;
        auto branch = [&](expr* e) {
            linear l = affine(e);
            l.constant -= bound;
            expr* result = scalar_comparison(op, l, depth + 1);
            return result ? result : comparison(op, e, bound);
        };
        expr* y = branch(yes);
        expr* n = branch(no);
        expr *left, *right;
        if ((op == comparison_kind::le || op == comparison_kind::lt ||
             op == comparison_kind::ge || op == comparison_kind::gt) &&
            (a.is_lt(condition, left, right) || a.is_le(condition, left, right) ||
             a.is_gt(condition, left, right) || a.is_ge(condition, left, right))) {
            bool ascending = a.is_lt(condition) || a.is_le(condition);
            bool minimum = ascending ? same(left, yes) && same(right, no) :
                                       same(right, yes) && same(left, no);
            bool maximum = ascending ? same(right, yes) && same(left, no) :
                                       same(left, yes) && same(right, no);
            if (minimum || maximum) {
                expr_ref_vector args(m);
                args.push_back(y);
                args.push_back(n);
                bool lower = op == comparison_kind::ge || op == comparison_kind::gt;
                return boolean(minimum == lower, args);
            }
        }
        return keep(m.mk_ite(condition, y, n));
    }
    expr* lower_scalar(app* e) {
        expr *child, *left, *right, *source;
        if (m.is_not(e, child) && m.is_eq(child, left, right)) {
            for (unsigned i = 0; i < 2; ++i) {
                // A failed conversion is exactly -1, not an arbitrary negative integer.
                if (u.str.is_stoi(left, source) && numeral(right, rational(-1)))
                    return comparison(comparison_kind::ge, left, rational(0));
                std::swap(left, right);
            }
        }
        comparison_kind op;
        if (!comparison_operator(e, op)) return e;
        linear value = affine(e->get_arg(0));
        value.add(affine(e->get_arg(1)), rational(-1));
        expr* result = scalar_comparison(op, value);
        return result ? result : e;
    }
    // scalar_comparison's counterpart for exact decimal text rather than
    // numeric bounds: for a single str.stoi term, lowers `op(stoi(s), bound)`
    // to a membership in decimal_language(op, bound) (pushed through an ite
    // the same way); `magnitude` records whether any such bound was
    // nonnegative, i.e. actually distinguishes valid conversions rather
    // than only ever testing the -1 failure sentinel.
    expr* decimal_comparison(comparison_kind op, linear const& l, bool& changed,
                             bool& magnitude, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (l.terms.size() != 1) return nullptr;
        auto [term, coefficient] = *l.terms.begin();
        if (coefficient == rational(-1))
            op = reverse_comparison(op);
        else if (!coefficient.is_one())
            return nullptr;
        rational bound = -l.constant * coefficient;
        if (!bound.is_int()) return nullptr;
        expr *source, *condition, *yes, *no;
        if (u.str.is_stoi(term, source)) {
            changed = true;
            magnitude |= bound >= 0 &&
                !(bound.is_zero() && (op == comparison_kind::ge || op == comparison_kind::lt));
            return membership(source, decimal_language(op, bound));
        }
        if (!m.is_ite(term, condition, yes, no)) return nullptr;
        auto branch = [&](expr* e) {
            linear value = affine(e);
            value.constant -= bound;
            expr* result = decimal_comparison(op, value, changed, magnitude, depth + 1);
            return result ? result : comparison(op, e, bound);
        };
        expr* y = branch(yes);
        expr* n = branch(no);
        expr_ref_vector args(m);
        args.push_back(condition);
        args.push_back(y);
        expr* positive = boolean(true, args);
        args.reset();
        args.push_back(neg(condition));
        args.push_back(n);
        expr* negative = boolean(true, args);
        args.reset();
        args.push_back(positive);
        args.push_back(negative);
        return boolean(false, args);
    }
    expr* lower_decimal(app* e) {
        comparison_kind op;
        if (!comparison_operator(e, op)) return e;
        linear value = affine(e->get_arg(0));
        value.add(affine(e->get_arg(1)), rational(-1));
        bool changed = false, magnitude = false;
        expr* result = decimal_comparison(op, value, changed, magnitude);
        if (changed) decimal_rewrites.push_back({e, result, magnitude});
        return changed ? result : e;
    }
    expr* avoiding(zstring const& ch) {
        auto excluded = seq::range_predicate::singleton(ch[0], u.max_char());
        expr_ref allowed = seq::range_predicate_to_regex(u, ~excluded, u.str.mk_string_sort());
        return star(allowed);
    }
    bool nullable(expr* r) {
        tick();
        expr_ref test = rw.is_nullable(r);
        if (!m.is_true(test) && !m.is_false(test)) throw failure::unsupported;
        return m.is_true(test);
    }
    expr* length(int lo, int hi = -1) {
        tick();
        if (hi != -1 && hi < lo) return empty;
        if (lo < 0 || lo > 4096 || hi > 4096) throw failure::budget;
        if (hi == 0) return epsilon;
        if (lo == 0 && hi == -1) return all;
        if (lo == 1 && hi == 1) return character;
        if (hi == -1) {
            expr* fixed = length(lo, lo);
            return cat(fixed, all);
        }
        return keep(rw.mk_loop(character, lo, hi));
    }
    expr* derivative_char(expr* r, unsigned ch, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (u.re.is_empty(r)) return empty;
        if (u.re.is_full_seq(r)) return all;
        seq::range_predicate chars(u.max_char());
        if (seq::regex_to_range_predicate(u, r, chars))
            return chars.contains(ch) ? epsilon.get() : empty.get();
        expr *x, *y;
        zstring text;
        if (u.re.is_to_re(r, x) && u.str.is_string(x, text))
            return !text.empty() && text[0] == ch ? lit(text.extract(1, text.length() - 1)) : empty.get();
        if (u.re.is_union(r, x, y)) {
            expr* dx = derivative_char(x, ch, depth + 1);
            expr* dy = derivative_char(y, ch, depth + 1);
            return join(dx, dy);
        }
        if (u.re.is_intersection(r, x, y)) {
            expr* dx = derivative_char(x, ch, depth + 1);
            expr* dy = derivative_char(y, ch, depth + 1);
            return meet(dx, dy);
        }
        if (u.re.is_complement(r, x))
            return complement(derivative_char(x, ch, depth + 1));
        if (u.re.is_diff(r, x, y)) {
            expr* dx = derivative_char(x, ch, depth + 1);
            expr* dy = complement(derivative_char(y, ch, depth + 1));
            return meet(dx, dy);
        }
        if (u.re.is_concat(r, x, y)) {
            expr* dx = derivative_char(x, ch, depth + 1);
            expr* first = cat(dx, y);
            if (!nullable(x)) return first;
            expr* dy = derivative_char(y, ch, depth + 1);
            return join(first, dy);
        }
        if (u.re.is_star(r, x)) {
            expr* dx = derivative_char(x, ch, depth + 1);
            return cat(dx, r);
        }
        unsigned lo, hi;
        if (u.re.is_loop(r, x, lo, hi) && seq::regex_to_range_predicate(u, x, chars)) {
            if (!hi || !chars.contains(ch)) return empty;
            return keep(rw.mk_loop(x, lo ? lo - 1 : 0, hi - 1));
        }
        throw failure::unsupported;
    }
    expr* derivative(expr* r, zstring const& word) {
        for (unsigned ch : word) {
            r = derivative_char(r, ch);
        }
        return r;
    }
    expr* reverse(expr* r) { tick(); return keep(rw.mk_reverse(r)); }

    // Indistinguishable letters can be changed at any positions, including just the first occurrence.
    bool replacement_invariant(expr* r, unsigned from, unsigned to, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (from == to || u.re.is_empty(r) || u.re.is_full_seq(r) || u.re.is_full_char(r))
            return true;
        seq::range_predicate chars(u.max_char());
        if (seq::regex_to_range_predicate(u, r, chars))
            return chars.contains(from) == chars.contains(to);
        expr* x;
        zstring word;
        if (u.re.is_to_re(r, x) && u.str.is_string(x, word)) {
            for (unsigned ch : word)
                if (ch == from || ch == to) return false;
            return true;
        }
        if (u.re.is_concat(r) || u.re.is_union(r) ||
            u.re.is_intersection(r) || u.re.is_diff(r)) {
            for (expr* arg : *to_app(r))
                if (!replacement_invariant(arg, from, to, depth + 1)) return false;
            return true;
        }
        if (u.re.is_complement(r) || u.re.is_star(r) || u.re.is_plus(r) ||
            u.re.is_opt(r) || u.re.is_loop(r) || u.re.is_reverse(r))
            return replacement_invariant(to_app(r)->get_arg(0), from, to, depth + 1);
        return false;
    }

    expr* replace_preimage(expr* r, zstring const& needle, zstring const& replacement, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (needle.empty()) return derivative(r, replacement);
        if (needle.length() > 16 || replacement.length() > 64) throw failure::budget;
        if (u.re.is_empty(r) || u.re.is_full_seq(r)) return r;
        if (needle.length() == 1 && replacement.length() == 1 &&
            replacement_invariant(r, needle[0], replacement[0]))
            return r;
        auto known = occurrence_languages.find(r);
        bool known_counts = known != occurrence_languages.end() && known->second.needle == needle;
        expr *x, *y;
        if (u.re.is_complement(r, x))
            return complement(replace_preimage(x, needle, replacement, depth + 1));
        if (!known_counts &&
            (u.re.is_union(r, x, y) || u.re.is_intersection(r, x, y) || u.re.is_diff(r, x, y))) {
            expr* left = replace_preimage(x, needle, replacement, depth + 1);
            expr* right = replace_preimage(y, needle, replacement, depth + 1);
            if (u.re.is_union(r)) return join(left, right);
            if (u.re.is_diff(r)) right = complement(right);
            return meet(left, right);
        }
        zstring target;
        if (u.re.is_to_re(r, x) && u.str.is_string(x, target)) {
            if (target.length() > 64) throw failure::budget;
            expr* result = target.replace(needle, replacement) == target ? r : empty.get();
            for (unsigned i = 0; i <= target.length(); ++i) {
                tick();
                if (replacement.length() > target.length() - i ||
                    target.extract(i, replacement.length()) != replacement) continue;
                zstring candidate = target.extract(0, i) + needle +
                                    target.extract(i + replacement.length(), target.length() - i - replacement.length());
                if (candidate.replace(needle, replacement) == target) {
                    expr* word = lit(candidate);
                    result = join(result, word);
                }
            }
            return result;
        }
        seq::range_predicate chars(u.max_char());
        expr* body = nullptr;
        unsigned occurrences = 0;
        if (known_counts) {
            body = known->second.character_class;
            occurrences = known->second.maximum;
        }
        else if (!u.re.is_star(r, body)) {
            unsigned lo, hi;
            expr *left, *loop, *piece, *word, *tail, *letter;
            zstring n;
            if (!u.re.is_concat(r, left, loop) || !u.re.is_star(left, body) ||
                !u.re.is_loop(loop, piece, lo, hi) || lo != 0 || hi > 64 ||
                !u.re.is_concat(piece, word, tail) || tail != left ||
                !u.re.is_to_re(word, letter) || !u.str.is_string(letter, n) || n != needle)
                throw failure::unsupported;
            occurrences = hi;
        }
        if (needle.length() != 1 || !seq::regex_to_range_predicate(u, body, chars))
            throw failure::unsupported;
        bool replacement_allowed = true;
        for (unsigned ch : replacement) replacement_allowed &= chars.contains(ch);
        if (chars.contains(needle[0])) {
            if (occurrences) throw failure::unsupported;
            if (replacement_allowed) return r;
            auto allowed = chars - seq::range_predicate::singleton(needle[0], u.max_char());
            expr_ref restricted = seq::range_predicate_to_regex(u, allowed, u.str.mk_string_sort());
            return star(restricted);
        }
        if (!replacement_allowed) {
            if (occurrences) throw failure::unsupported;
            return r;
        }
        if (occurrences == 64) throw failure::budget;
        // C* (a C*){0,k} gains one permitted occurrence when the first a
        // is replaced by a word in C*, with a outside C.
        expr* cstar = star(body);
        expr* one = lit(needle);
        expr* piece = cat(one, cstar);
        expr* optional = keep(u.re.mk_loop(piece, 0, occurrences + 1));
        expr* result = cat(cstar, optional);
        occurrence_languages.insert_or_assign(result, bounded_occurrences{body, needle, occurrences + 1});
        return result;
    }
    // The preimage of a selector/replacement function under a known
    // membership fact: given `term = f(source, ...)` where `term in r`
    // holds, computes `result` such that the equivalent fact `source in
    // result` holds instead - i.e. pulls the membership fact from a derived
    // term back onto the variable it was built from. Handles:
    //  - str.replace(source, needle, repl) via replace_preimage() below;
    //  - str.at(source, i): a fixed small i, or i = len(source)-1 (last
    //    character);
    //  - str.extract(source, i, len): the first_cut()-recognized
    //    delimiter-split shapes, a fixed-length prefix/suffix, or a
    //    fixed-length *substring* at a fixed offset (the three nested
    //    length/offset cases);
    //  - source ++ literal / literal ++ source: via a derivative step
    //    through the literal (reversed for the trailing-literal case).
    // Returns false if `term`'s shape is not one of the above.
    bool preimage(expr* term, expr* r, expr*& source, expr*& result) {
        tick();
        expr *s, *i, *len, *needle, *replacement;
        zstring n, repl;
        rational v;
        if (u.str.is_replace(term, s, needle, replacement) &&
            u.str.is_string(needle, n) && u.str.is_string(replacement, repl)) {
            source = s;
            result = replace_preimage(r, n, repl);
            ++preimages;
            return true;
        }
        if (u.str.is_at(term, s, i)) {
            expr* one = meet(r, character);
            source = s;
            if (a.is_numeral(i, v) && v.is_unsigned() && v <= rational(64)) {
                unsigned k = v.get_unsigned();
                expr* yes = cat({length(k, k), one, all});
                result = join(yes, nullable(r) ? length(0, k) : empty);
            }
            else {
                expr_ref slen(u.str.mk_length(s), m);
                linear offset = affine(i);
                if (!single(offset, slen) || offset.constant != rational(-1)) return false;
                expr* yes = cat(all, one);
                result = join(yes, nullable(r) ? epsilon : empty);
            }
            ++preimages;
            return true;
        }
        if (u.str.is_extract(term, s, i, len)) {
            source = s;
            cut c;
            if (first_cut(term, c)) {
                expr* delimiter = lit(c.delimiter);
                expr* before = avoiding(c.delimiter);
                expr* present;
                expr* absent = nullable(r) ? before : empty;
                switch (c.type) {
                case cut::prefix: {
                    expr* prefix = meet(r, before);
                    present = cat({prefix, delimiter, all});
                    break;
                }
                case cut::prefix_including: {
                    expr* prefix = cat(before, delimiter);
                    prefix = meet(r, prefix);
                    present = cat(prefix, all);
                    break;
                }
                case cut::tail:
                    present = cat({before, delimiter, r});
                    absent = meet(before, r);
                    break;
                default: {
                    expr* tail = cat(delimiter, all);
                    tail = meet(r, tail);
                    present = cat(before, tail);
                    break;
                }
                }
                result = join(present, absent);
                ++preimages;
                return true;
            }
            expr_ref slen(u.str.mk_length(s), m);
            linear l = affine(len);
            if (numeral(i, rational(0)) && single(l, slen) &&
                l.constant <= rational(0) && l.constant >= rational(-64)) {
                unsigned k = (-l.constant).get_unsigned();
                expr* yes = cat(r, length(k, k));
                result = join(yes, nullable(r) && k ? length(0, k - 1) : empty);
                ++preimages;
                return true;
            }
            if (a.is_numeral(i, v) && v.is_unsigned() && v <= rational(64)) {
                unsigned k = v.get_unsigned();
                linear sum = l;
                sum.add(affine(i), rational(1));
                bool tail = sum == affine(slen);
                if (!tail) {
                    params_ref params;
                    params.set_bool("seq_regular_rewrite", false);
                    th_rewriter simplify(m, params);
                    simplify(slen);
                    tail = sum == affine(slen);
                }
                if (tail) {
                    expr* yes = cat(length(k, k), r);
                    result = join(yes, nullable(r) && k ? length(0, k - 1) : empty);
                    ++preimages;
                    return true;
                }
                if (a.is_numeral(len, v) && v.is_unsigned() && v <= rational(64)) {
                    unsigned count = v.get_unsigned();
                    if (!count) result = nullable(r) ? all : empty;
                    else {
                        expr* short_result = meet(r, length(0, count - 1));
                        expr* full_result = meet(r, length(count, count));
                        full_result = cat(full_result, all);
                        expr* prefix = join(short_result, full_result);
                        expr* yes = cat(length(k, k), prefix);
                        result = join(yes, nullable(prefix) && k ? length(0, k - 1) : empty);
                    }
                    ++preimages;
                    return true;
                }
            }
        }
        if (u.str.is_concat(term) && to_app(term)->get_num_args() == 2) {
            app* t = to_app(term);
            if (u.str.is_string(t->get_arg(0), n)) {
                source = t->get_arg(1);
                result = derivative(r, n);
                ++preimages;
                return true;
            }
            if (u.str.is_string(t->get_arg(1), n)) {
                source = t->get_arg(0);
                expr* reversed = reverse(r);
                reversed = derivative(reversed, n.reverse());
                result = reverse(reversed);
                ++preimages;
                return true;
            }
        }
        return false;
    }
    expr* membership(expr* source, expr* language) {
        zstring text;
        if (u.re.is_empty(language)) return keep(m.mk_false());
        if (u.re.is_full_seq(language)) return keep(m.mk_true());
        if (u.str.is_string(source, text))
            return keep(m.mk_bool_val(nullable(derivative(language, text))));
        return keep(u.re.mk_in_re(source, language));
    }
    // Recognizes one Boolean leaf as a string observation and converts it
    // to a `(source, language)` pair meaning `source in language`, using
    // the regex DSL above to build `language`. Covers str.in_re itself,
    // str.contains/prefixof/suffixof against a literal, literal
    // (dis)equality, and linear comparisons of str.len/str.indexof against
    // a small constant bound (the str.indexof cases rely on SMT-LIB's
    // "-1 means not found" encoding, e.g. `indexof(s, "ab", 0) >= 0` is
    // `s in Sigma*.ab.Sigma*`). Recurses through `not` by complementing the
    // resulting language. Throws failure::unsupported for a str.in_re whose
    // regex is not ground, since that is a case this compiler cannot help
    // with regularizing further.
    bool atom(expr* e, expr*& source, expr*& language, unsigned depth = 0, bool lower_lengths = true) {
        tick();
        if (depth > 256) throw failure::budget;
        if (is_literal_binding(e))
            return false;
        expr *x, *y, *offset;
        zstring text;
        if (m.is_not(e, x)) {
            if (!atom(x, source, language, depth + 1, lower_lengths)) return false;
            language = complement(language);
            return true;
        }
        if (u.str.is_in_re(e, source, language)) {
            if (!u.is_string(source->get_sort()) || !u.re.is_ground(language))
                throw failure::unsupported;
            return true;
        }
        if (u.str.is_contains(e, x, y) && u.str.is_string(y, text)) {
            source = x;
            if (text.length() == 1) {
                language = complement(avoiding(text));
                return true;
            }
            expr* word = lit(text);
            language = cat({all, word, all});
            return true;
        }
        if (u.str.is_contains(e, x, y) && u.str.is_string(x, text) && u.str.max_length(y) <= 1) {
            source = y;
            language = epsilon;
            for (unsigned ch : text)
                language = join(language, lit(zstring(ch)));
            return true;
        }
        if ((u.str.is_prefix(e, x, y) || u.str.is_suffix(e, x, y)) && u.str.is_string(x, text)) {
            source = y;
            expr* word = lit(text);
            language = u.str.is_prefix(e) ? cat(word, all) : cat(all, word);
            return true;
        }
        if (m.is_eq(e, x, y)) {
            if (u.str.is_string(x, text)) std::swap(x, y);
            if (u.is_string(x->get_sort()) && u.str.is_string(y, text)) {
                source = x; language = lit(text); return true;
            }
        }
        bool eq = m.is_eq(e, x, y), ge = a.is_ge(e, x, y), le = a.is_le(e, x, y);
        bool gt = a.is_gt(e, x, y), lt = a.is_lt(e, x, y);
        if (!(eq || ge || le || gt || lt) || !a.is_int(x)) return false;
        linear l = affine(x);
        l.add(affine(y), rational(-1));
        if (l.terms.empty()) {
            bool truth = eq ? l.constant.is_zero() : ge ? l.constant >= rational(0) :
                         le ? l.constant <= rational(0) : gt ? l.constant > rational(0) : l.constant < rational(0);
            source = keep(u.str.mk_string(zstring()));
            language = truth ? all : empty;
            return true;
        }
        if (l.terms.size() == 1) {
            auto [term, coefficient] = *l.terms.begin();
            if (coefficient == rational(-1)) {
                l.constant.neg();
                std::swap(ge, le); std::swap(gt, lt);
            }
            else if (!coefficient.is_one()) return false;
            rational bound = -l.constant;
            if (!bound.is_int() || bound < rational(-4096) || bound > rational(4096))
                return false;
            int b = bound.get_int32();
            if (u.str.is_length(term, source)) {
                if (!lower_lengths) return false;
                if (!u.is_string(source->get_sort()))
                    return false;
                if (eq) language = b < 0 ? empty.get() : length(b, b);
                else if (ge || gt) language = length(std::max(0, b + (gt ? 1 : 0)));
                else language = b - (lt ? 1 : 0) < 0 ? empty.get() : length(0, b - (lt ? 1 : 0));
                return true;
            }
            if (u.str.is_index(term, source, y, offset) &&
                numeral(offset, rational(0)) && u.str.is_string(y, text)) {
                bool negative = (eq && b == -1) || ((le || lt) && b - (lt ? 1 : 0) == -1);
                bool positive = (ge || gt) && b + (gt ? 1 : 0) == 0;
                if (negative || positive) {
                    if (text.length() == 1) language = complement(avoiding(text));
                    else {
                        expr* word = lit(text);
                        language = cat({all, word, all});
                    }
                    if (negative) language = complement(language);
                    return true;
                }
            }
        }
        // Bounds valid for every zero-offset search for one character.
        if (ge) {
            for (auto const& [term, coefficient] : l.terms) {
                expr *s, *needle;
                if (!u.str.is_index(term, s, needle, offset) || !numeral(offset, rational(0)) ||
                    !u.str.is_string(needle, text) || text.length() != 1)
                    continue;
                expr_ref slen(u.str.mk_length(s), m);
                linear expected;
                expected.terms[term] = rational(1);
                bool valid = l.terms == expected.terms && l.constant >= rational(1);
                expected.terms[term] = rational(-1);
                expected.terms[slen] = rational(1);
                valid |= l.terms == expected.terms && l.constant >= rational(-1);
                if (valid) { source = s; language = all; return true; }
            }
        }
        return false;
    }
    // Combines sibling membership facts that share one subject term before
    // falling back to a generic Boolean reconstruction: `s in R1 /\ s in R2`
    // becomes `s in (R1 /\ R2)` (meet, conjunction) and `s in R1 \/ s in R2`
    // becomes `s in (R1 \/ R2)` (join, disjunction) - a `not (s in R)` arg
    // contributes its complement. If the args do not all share one subject,
    // falls back to `boolean()` (an ordinary and/or/not reconstruction).
    // This is what lets `translate()` below group e.g. the ten digit-value
    // alternatives of a decimal comparison into one combined language
    // before `preimage()` is asked to pull it back onto its root variable,
    // rather than pulling each alternative back separately.
    expr* regular_boolean(bool conjunction, expr_ref_vector const& args) {
        expr* subject = nullptr;
        expr_ref_vector languages(m);
        for (expr* arg : args) {
            tick();
            if (m.is_true(arg) || m.is_false(arg)) {
                if (m.is_true(arg) != conjunction) return arg;
                continue;
            }
            expr *s, *r, *child;
            bool negative = m.is_not(arg, child);
            if (!u.str.is_in_re(negative ? child : arg, s, r) || (subject && subject != s))
                return boolean(conjunction, args);
            subject = s;
            languages.push_back(negative ? complement(r) : r);
        }
        if (!subject) return keep(m.mk_bool_val(conjunction));
        expr* language = conjunction ? all : empty;
        for (expr* r : languages)
            language = conjunction ? meet(language, r) : join(language, r);
        return membership(subject, language);
    }
    expr* finite_conversion(expr* s, unsigned mask) {
        expr* result = keep(a.mk_int(-1));
        for (unsigned d = 10; d-- > 0;) {
            if (!(mask & (1u << d))) continue;
            expr* word = keep(u.str.mk_string(zstring('0' + d)));
            expr* guard = keep(m.mk_eq(s, word));
            expr* number = keep(a.mk_int(d));
            result = keep(m.mk_ite(guard, number, result));
        }
        return result;
    }
public:
    seq_regular_rewriter(ast_manager& m, unsigned limit, unsigned& steps, unsigned& preimages):
        m(m), u(m), a(m), rw(m), br(m), pin(m), empty(m), epsilon(m), character(m), all(m),
        max_steps(limit), steps(steps), preimages(preimages) {
        sort* s = u.str.mk_string_sort();
        sort* re = u.re.mk_re(s);
        empty = u.re.mk_empty(re);
        epsilon = u.re.mk_epsilon(s);
        character = u.re.mk_full_char(re);
        all = u.re.mk_full_seq(re);
        params_ref params;
        params.set_bool("seq_regular_rewrite", false);
        rw.updt_params(params);
    }
    expr* rewrite(app* e) {
        expr_ref_vector args(m);
        args.append(e->get_num_args(), e->get_args());
        expr* normalized = normalize_node(e, args);
        if (normalized != e) return normalized;
        expr* source;
        if (u.str.is_stoi(e, source) && !u.str.is_string(source) && bounded_length(source) <= 1)
            return finite_conversion(source, (1u << 10) - 1);
        if (!m.is_bool(e)) return e;
        expr* result = lower_scalar(e);
        if (result != e) return result;
        result = lower_decimal(e);
        if (result != e) return result;
        expr* language;
        // Preserve arithmetic length guards outside contextual aggregation.
        if (!atom(e, source, language, 0, false)) return e;
        expr *parent, *inverse;
        unsigned previous_preimages = preimages;
        while (!u.re.is_empty(language) && !u.re.is_full_seq(language) &&
               preimage(source, language, parent, inverse)) {
            source = parent;
            language = inverse;
        }
        // Do not preempt native equality rules without improving the subject.
        if (m.is_eq(e) && preimages == previous_preimages) return e;
        return membership(source, language);
    }
};
