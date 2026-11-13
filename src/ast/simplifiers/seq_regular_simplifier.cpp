/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regular_simplifier.cpp

Abstract:

    Aggregate regular observations before taking selector/replacement preimages.
    No assertions are changed unless the entire pending goal is regular.

--*/
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/rewriter/bool_rewriter.h"
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
    std::unordered_map<expr*, expr*> normalized;
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
    dependent_expr rewrite(dependent_expr const& d, expr* result) {
        proof_ref pr(d.pr(), m);
        if (pr && d.fml() != result) {
            proof_ref step(m.mk_rewrite(d.fml(), result), m);
            pr = m.mk_modus_ponens(pr, step);
        }
        return dependent_expr(m, result, pr, d.dep());
    }
    void aggregate(vector<dependent_expr> const& inputs, vector<dependent_expr>& results) {
        std::map<unsigned, expr*> pending;
        std::unordered_map<expr*, dependent_expr> groups;
        auto add = [&](dependent_expr const& d) {
            expr *source = nullptr, *language = nullptr;
            VERIFY(u.str.is_in_re(d.fml(), source, language));
            auto it = groups.find(source);
            if (it == groups.end())
                groups.emplace(source, d);
            else {
                auto const& previous = it->second;
                expr_ref intersection(meet(to_app(previous.fml())->get_arg(1), language), m);
                expr_ref result(u.re.mk_in_re(source, intersection), m);
                expr_ref conjunction(m.mk_and(previous.fml(), d.fml()), m);
                proof_ref pr(m);
                if (previous.pr() && d.pr()) {
                    expr_ref not_previous(m.mk_not(previous.fml()), m);
                    expr_ref not_current(m.mk_not(d.fml()), m);
                    expr_ref clause(m.mk_or(not_previous, not_current, conjunction), m);
                    proof_ref axiom(m.mk_def_axiom(clause), m);
                    proof* premises[] = {axiom, previous.pr(), d.pr()};
                    pr = m.mk_unit_resolution(3, premises, conjunction);
                }
                expr_dependency_ref dep(m.mk_join(previous.dep(), d.dep()), m);
                dependent_expr combined(m, conjunction, pr, dep);
                it->second = rewrite(combined, result);
            }
            pending[source->get_id()] = source;
        };
        for (auto const& d : inputs) {
            if (m.is_false(d.fml())) {
                results.reset();
                results.push_back(d);
                return;
            }
            expr *source = nullptr, *language = nullptr;
            if (u.str.is_in_re(d.fml(), source, language))
                add(d);
            else if (!m.is_true(d.fml()))
                results.push_back(d);
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
            expr* source = chosen->second;
            pending.erase(chosen);
            dependent_expr current(groups.at(source));
            expr* language = to_app(current.fml())->get_arg(1);
            if (u.re.is_empty(language)) {
                results.reset();
                results.push_back(rewrite(current, m.mk_false()));
                return;
            }
            if (u.re.is_full_seq(language)) {
                groups.erase(source);
                continue;
            }
            expr *parent, *inverse;
            if (preimage(source, language, parent, inverse)) {
                expr_ref result(u.re.mk_in_re(parent, inverse), m);
                dependent_expr next = rewrite(current, result);
                groups.erase(source);
                add(next);
            }
        }
        for (auto const& [source, d] : groups) {
            expr* language = to_app(d.fml())->get_arg(1);
            results.push_back(rewrite(d, membership(source, language)));
        }
    }
    expr* translate(expr* e, bool defer = false, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (m.is_true(e) || m.is_false(e)) return e;
        if (m.is_and(e) || m.is_or(e)) {
            bool conjunction = m.is_and(e);
            expr_ref_vector children(m);
            vector<dependent_expr> inputs, results;
            for (expr* arg : *to_app(e)) {
                expr* child = translate(arg, conjunction, depth + 1);
                if (conjunction)
                    inputs.push_back(dependent_expr(m, child, nullptr, nullptr));
                else
                    children.push_back(child);
            }
            if (conjunction) {
                aggregate(inputs, results);
                for (auto const& d : results)
                    children.push_back(d.fml());
            }
            return boolean(conjunction, children);
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
    void translate_assertion(dependent_expr const& d, vector<dependent_expr>& results) {
        if (m.is_and(d.fml())) {
            unsigned index = 0;
            for (expr* arg : *to_app(d.fml())) {
                proof_ref pr(d.pr() ? m.mk_and_elim(d.pr(), index) : nullptr, m);
                translate_assertion(dependent_expr(m, arg, pr, d.dep()), results);
                ++index;
            }
        }
        else
            results.push_back(rewrite(d, translate(d.fml(), true)));
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
    expr* normalize(expr* e) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            tick();
            expr* cur = todo.back();
            if (normalized.count(cur)) { todo.pop_back(); continue; }
            if (!is_app(cur)) throw failure::unsupported;
            bool ready = true;
            for (expr* arg : *to_app(cur)) {
                if (!normalized.count(arg)) { todo.push_back(arg); ready = false; break; }
            }
            if (!ready) continue;
            expr_ref_vector args(m);
            for (expr* arg : *to_app(cur)) args.push_back(normalized[arg]);
            normalized[cur] = normalize_node(to_app(cur), args);
            todo.pop_back();
        }
        return normalized[e];
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
    void compile(vector<dependent_expr>& formulas) {
        bool root_regular = true;
        for (auto const& d : formulas)
            root_regular &= is_root_regular(d.fml());
        if (root_regular)
            return;
        vector<dependent_expr> inputs, results;
        for (auto const& d : formulas)
            translate_assertion(rewrite(d, normalize(d.fml())), inputs);
        aggregate(inputs, results);
        for (auto const& d : results)
            if (!is_root_regular(d.fml()))
                throw failure::unsupported;
        formulas.swap(results);
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
    if (m_fmls.has_quantifiers()) { ++m_skipped; return; }
    if (proofs_enabled())
        for (unsigned i = qhead(); i < qtail(); ++i)
            if (!m_fmls[i].pr()) { ++m_skipped; return; }
    unsigned preimages_before = m_preimages;
    unsigned steps = 0;
    regular_compiler compiler(m, m_max_steps, steps, m_preimages);
    vector<dependent_expr> results;
    for (unsigned i = qhead(); i < qtail(); ++i)
        results.push_back(m_fmls[i]);
    try {
        compiler.compile(results);
    }
    catch (failure why) {
        m_steps += steps;
        if (why == failure::unsupported) ++m_unsupported;
        else if (why == failure::budget) ++m_budget;
        return;
    }
    m_steps += steps;
    if (m_automatic && m_preimages == preimages_before &&
        !std::all_of(results.begin(), results.end(),
                     [&](dependent_expr const& d) { return m.is_true(d.fml()) || m.is_false(d.fml()); }))
        return;
    unsigned end = qtail();
    unsigned count = std::max(end - qhead(), results.size());
    dependent_expr truth(m, m.mk_true(), proofs_enabled() ? m.mk_true_proof() : nullptr, nullptr);
    for (unsigned j = 0; j < count && !m_fmls.inconsistent(); ++j) {
        unsigned i = qhead() + j;
        auto const& result = j < results.size() ? results[j] : truth;
        if (i >= end) {
            m_fmls.add(result);
            ++m_rewritten;
        }
        else if (auto const& old = m_fmls[i];
                 result.fml() != old.fml() || result.dep() != old.dep() || result.pr() != old.pr()) {
            m_fmls.update(i, result);
            ++m_rewritten;
        }
    }
}

void seq_regular_simplifier::reset_statistics() {
    m_steps = m_preimages = m_rewritten = m_unsupported = m_budget = m_skipped = 0;
    m_watch.reset();
}

void seq_regular_simplifier::collect_statistics(statistics& st) const {
    st.update("seq-regular-steps", m_steps);
    st.update("seq-regular-preimages", m_preimages);
    st.update("seq-regular-rewritten", m_rewritten);
    st.update("seq-regular-unsupported", m_unsupported);
    st.update("seq-regular-budget", m_budget);
    st.update("seq-regular-skipped", m_skipped);
    st.update("seq-regular-time-ms", 1000.0 * m_watch.get_seconds());
}
