/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regular_simplifier.cpp

Abstract:

    Lower decimal constant comparisons, then aggregate regular observations
    before taking selector/replacement preimages. The latter phase is transactional.

--*/
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "params/smt_params_helper.hpp"
#include <algorithm>
#include <map>
#include <set>
#include <unordered_map>
#include <vector>

namespace {
enum class failure { unsupported, budget, canceled };

class regular_compiler {
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
    std::unordered_map<expr*, expr*> normalized;
    std::unordered_map<expr*, expr*> decimal_normalized;
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
    struct bounded_occurrences {
        expr* character_class;
        zstring needle;
        unsigned maximum;
    };
    std::unordered_map<expr*, bounded_occurrences> occurrence_languages;
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
        if (e->get_num_args() != 2 || !a.is_int(e->get_arg(0))) return e;
        comparison_kind op;
        if (m.is_eq(e)) op = comparison_kind::eq;
        else if (m.is_distinct(e)) op = comparison_kind::ne;
        else if (a.is_le(e)) op = comparison_kind::le;
        else if (a.is_ge(e)) op = comparison_kind::ge;
        else if (a.is_lt(e)) op = comparison_kind::lt;
        else if (a.is_gt(e)) op = comparison_kind::gt;
        else return e;
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

    expr* replace_preimage(expr* r, zstring const& needle, zstring const& replacement, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (needle.empty()) return derivative(r, replacement);
        if (needle.length() > 16 || replacement.length() > 64) throw failure::budget;
        if (u.re.is_empty(r) || u.re.is_full_seq(r)) return r;
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
                if (sum == affine(slen)) {
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
    bool atom(expr* e, expr*& source, expr*& language, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (is_literal_binding(e))
            return false;
        expr *x, *y, *offset;
        zstring text;
        if (m.is_not(e, x)) {
            if (!atom(x, source, language, depth + 1)) return false;
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
    expr* translate(expr* e, bool defer = false, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (m.is_true(e) || m.is_false(e)) return e;
        if (m.is_and(e) || m.is_or(e)) {
            bool conjunction = m.is_and(e);
            expr_ref_vector children(m), rest(m);
            std::map<unsigned, expr*> pending;
            std::unordered_map<expr*, expr*> groups;
            for (expr* arg : *to_app(e)) {
                expr* child = translate(arg, conjunction, depth + 1);
                expr *s, *r;
                if (conjunction && u.str.is_in_re(child, s, r)) {
                    auto it = groups.find(s);
                    groups[s] = it == groups.end() ? r : meet(it->second, r);
                    pending[s->get_id()] = s;
                }
                else rest.push_back(child);
            }
            // AST depth orders parents after their children, independent of allocation IDs.
            std::unordered_map<expr*, unsigned> depths;
            auto term_depth = [&](expr* t) {
                ptr_vector<expr> stack;
                stack.push_back(t);
                while (!stack.empty()) {
                    tick();
                    expr* cur = stack.back();
                    if (depths.count(cur)) { stack.pop_back(); continue; }
                    unsigned d = 0;
                    bool ready = true;
                    if (is_app(cur)) for (expr* arg : *to_app(cur)) {
                        if (!depths.count(arg)) { stack.push_back(arg); ready = false; break; }
                        d = std::max(d, depths[arg] + 1);
                    }
                    if (ready) { depths[cur] = d; stack.pop_back(); }
                }
                return depths[t];
            };
            while (!pending.empty()) {
                auto chosen = pending.begin();
                unsigned deepest = term_depth(chosen->second);
                for (auto it = std::next(chosen); it != pending.end(); ++it) {
                    unsigned d = term_depth(it->second);
                    if (d > deepest) { chosen = it; deepest = d; }
                }
                expr* s = chosen->second;
                pending.erase(chosen);
                expr* r = groups[s];
                if (u.re.is_empty(r)) return keep(m.mk_false());
                if (u.re.is_full_seq(r)) { groups.erase(s); continue; }
                expr *parent, *inverse;
                if (preimage(s, r, parent, inverse)) {
                    groups.erase(s);
                    auto it = groups.find(parent);
                    groups[parent] = it == groups.end() ? inverse : meet(it->second, inverse);
                    pending[parent->get_id()] = parent;
                }
            }
            for (auto const& [s, r] : groups) rest.push_back(membership(s, r));
            return boolean(conjunction, rest);
        }
        expr *source, *language, *child;
        if (atom(e, source, language)) {
            if (!defer) {
                expr *parent, *inverse;
                while (!u.re.is_empty(language) && !u.re.is_full_seq(language) &&
                       preimage(source, language, parent, inverse)) {
                    source = parent; language = inverse;
                }
            }
            return membership(source, language);
        }
        if (m.is_not(e, child)) return neg(translate(child, false, depth + 1));
        return e;
    }
public:
    regular_compiler(ast_manager& m, unsigned limit, unsigned& steps, unsigned& preimages):
        m(m), u(m), a(m), rw(m), br(m), pin(m), empty(m), epsilon(m), character(m), all(m),
        max_steps(limit), steps(steps), preimages(preimages) {
        sort* s = u.str.mk_string_sort();
        sort* re = u.re.mk_re(s);
        empty = u.re.mk_empty(re);
        epsilon = u.re.mk_epsilon(s);
        character = u.re.mk_full_char(re);
        all = u.re.mk_full_seq(re);
    }
    bool retain_shared_conversions(expr_ref_vector& formulas) {
        if (decimal_rewrites.empty()) return true;
        obj_hashtable<expr> shared, seen;
        ptr_vector<expr> todo;
        todo.append(formulas.size(), formulas.data());
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            if (u.str.is_stoi(e)) shared.insert(e);
            if (is_app(e)) for (expr* arg : *to_app(e)) todo.push_back(arg);
        }
        if (shared.empty()) return true;
        if (std::none_of(decimal_rewrites.begin(), decimal_rewrites.end(),
                         [](decimal_rewrite const& r) { return r.magnitude; }))
            return false;
        expr_safe_replace sub(m);
        for (auto const& rewrite : decimal_rewrites) {
            if (m.is_true(rewrite.replacement) || m.is_false(rewrite.replacement)) continue;
            seen.reset();
            todo.push_back(rewrite.original);
            bool uses_shared = false;
            while (!todo.empty()) {
                tick();
                expr* e = todo.back();
                todo.pop_back();
                if (seen.contains(e)) continue;
                seen.insert(e);
                uses_shared |= shared.contains(e);
                if (is_app(e)) for (expr* arg : *to_app(e)) todo.push_back(arg);
            }
            if (!uses_shared) continue;
            // Keep arithmetic information when the conversion still participates in coupled arithmetic.
            // Validity already has a digit-language axiom; only magnitude bounds add a new regex lemma.
            expr* retained = rewrite.original;
            if (rewrite.magnitude) retained = keep(m.mk_and(retained, rewrite.replacement));
            sub.insert(rewrite.replacement, retained);
        }
        if (sub.empty()) return true;
        for (unsigned i = 0; i < formulas.size(); ++i) {
            tick();
            expr_ref result(m);
            sub(formulas.get(i), result);
            formulas.set(i, result);
        }
        return true;
    }
    expr* normalize(expr* e, bool decimal_only = false) {
        auto& cache = decimal_only ? decimal_normalized : normalized;
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            tick();
            expr* cur = todo.back();
            if (cache.count(cur)) { todo.pop_back(); continue; }
            if (!is_app(cur)) throw failure::unsupported;
            bool ready = true;
            for (expr* arg : *to_app(cur)) {
                if (!cache.count(arg)) { todo.push_back(arg); ready = false; break; }
            }
            if (!ready) continue;
            expr_ref_vector args(m);
            for (expr* arg : *to_app(cur)) args.push_back(cache[arg]);
            if (decimal_only) {
                app* rebuilt = to_app(keep(m.mk_app(to_app(cur)->get_decl(), args.size(), args.data())));
                cache[cur] = lower_decimal(rebuilt);
            }
            else
                cache[cur] = normalize_node(to_app(cur), args);
            todo.pop_back();
        }
        return cache[e];
    }
    bool is_root_regular(expr* e) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(e);
        while (!todo.empty()) {
            tick();
            expr* cur = todo.back(); todo.pop_back();
            if (seen.contains(cur)) continue;
            seen.insert(cur);
            if (m.is_true(cur) || m.is_false(cur) || is_literal_binding(cur)) continue;
            expr *s, *r;
            if (u.str.is_in_re(cur, s, r) && is_uninterp_const(s) &&
                u.is_string(s->get_sort()) && u.re.is_ground(r))
                continue;
            if (m.is_and(cur) || m.is_or(cur) || m.is_not(cur)) {
                for (expr* arg : *to_app(cur)) todo.push_back(arg);
                continue;
            }
            return false;
        }
        return true;
    }
    expr_ref compile(expr* e) {
        if (is_root_regular(e))
            return expr_ref(e, m);
        expr_ref result(translate(normalize(e)), m);
        if (!is_root_regular(result))
            throw failure::unsupported;
        return result;
    }
};
}

bool seq_regular_simplifier::has_string_terms(ast_manager& m, expr* e) {
    seq_util u(m);
    ptr_vector<expr> todo;
    obj_hashtable<expr> seen;
    todo.push_back(e);
    while (!todo.empty()) {
        expr* current = todo.back();
        todo.pop_back();
        if (seen.contains(current))
            continue;
        seen.insert(current);
        if (u.is_string(current->get_sort()))
            return true;
        if (!m.inc())
            return false;
        if (is_app(current))
            for (expr* arg : *to_app(current))
                todo.push_back(arg);
    }
    return false;
}

seq_regular_simplifier::seq_regular_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s, bool automatic):
    dependent_expr_simplifier(m, s), m_automatic(automatic) {
    updt_params(p);
}

void seq_regular_simplifier::updt_params(params_ref const& p) {
    if (m_automatic) {
        smt_params_helper params(p);
        m_enabled = params.seq_regular() && params.string_solver() == "nseq";
        m_max_steps = params.seq_regular_max_steps();
    }
    else
        m_max_steps = p.get_uint("seq_regular.max_steps", m_max_steps);
}

void seq_regular_simplifier::collect_param_descrs(param_descrs& r) {
    r.insert("seq_regular.max_steps", CPK_UINT, "maximum work for a transactional regular-preimage pass", "100000");
}

void seq_regular_simplifier::reduce() {
    if (!m_enabled || qhead() == qtail()) return;
    if (m_automatic) {
        bool has_strings = false;
        for (unsigned i = qhead(); !has_strings && i < qtail(); ++i)
            has_strings = has_string_terms(m, m_fmls[i].fml());
        if (!has_strings)
            return;
    }
    scoped_watch watch(m_watch);
    if (proofs_enabled() || m_fmls.has_quantifiers()) { ++m_skipped; return; }
    unsigned preimages_before = m_preimages;
    unsigned steps = 0;
    regular_compiler compiler(m, m_max_steps, steps, m_preimages);
    expr_ref_vector decimals(m), results(m);
    bool labeled = false;
    for (unsigned i = qhead(); i < qtail(); ++i) labeled |= m_fmls[i].dep() != nullptr;
    bool decimal_changed = false;
    try {
        for (unsigned i = qhead(); i < qtail(); ++i) {
            expr* input = m_fmls[i].fml();
            expr* result = compiler.normalize(input, true);
            decimals.push_back(result);
        }
        if (!compiler.retain_shared_conversions(decimals)) {
            decimals.reset();
            for (unsigned i = qhead(); i < qtail(); ++i)
                decimals.push_back(m_fmls[i].fml());
        }
        for (unsigned i = qhead(); i < qtail(); ++i)
            decimal_changed |= decimals.get(i - qhead()) != m_fmls[i].fml();
    }
    catch (failure why) {
        m_steps += steps;
        if (why == failure::unsupported) ++m_unsupported;
        else if (why == failure::budget) ++m_budget;
        return;
    }
    try {
        if (labeled) {
            for (expr* input : decimals)
                results.push_back(compiler.compile(input));
        }
        else {
            expr_ref input(mk_and(decimals), m);
            results.push_back(compiler.compile(input));
            if (results.back() == input && !decimal_changed) {
                m_steps += steps;
                return;
            }
            for (unsigned i = qhead() + 1; i < qtail(); ++i) results.push_back(m.mk_true());
        }
    }
    catch (failure why) {
        if (why == failure::unsupported) ++m_unsupported;
        else if (why == failure::budget) ++m_budget;
        if (!decimal_changed || why == failure::canceled) {
            m_steps += steps;
            return;
        }
        results.reset();
        results.append(decimals);
    }
    m_steps += steps;
    if (m_automatic && !decimal_changed && m_preimages == preimages_before &&
        !std::all_of(results.begin(), results.end(), [&](expr* e) { return m.is_true(e) || m.is_false(e); }))
        return;
    unsigned end = qtail();
    for (unsigned i = qhead(); i < end && !m_fmls.inconsistent(); ++i) {
        auto const& old = m_fmls[i];
        expr* result = results.get(i - qhead());
        if (result != old.fml()) {
            if (decimals.get(i - qhead()) != old.fml()) ++m_stoi_rewritten;
            m_fmls.update(i, dependent_expr(m, result, nullptr, old.dep()));
            ++m_rewritten;
        }
    }
}

void seq_regular_simplifier::reset_statistics() {
    m_steps = m_preimages = m_rewritten = m_stoi_rewritten = m_unsupported = m_budget = m_skipped = 0;
    m_watch.reset();
}

void seq_regular_simplifier::collect_statistics(statistics& st) const {
    st.update("seq-regular-steps", m_steps);
    st.update("seq-regular-preimages", m_preimages);
    st.update("seq-regular-rewritten", m_rewritten);
    st.update("seq-regular-stoi-rewritten", m_stoi_rewritten);
    st.update("seq-regular-unsupported", m_unsupported);
    st.update("seq-regular-budget", m_budget);
    st.update("seq-regular-skipped", m_skipped);
    st.update("seq-regular-time-ms", 1000.0 * m_watch.get_seconds());
}
