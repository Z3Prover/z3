/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regular_simplifier.cpp

Abstract:

    Lower decimal constant comparisons, then aggregate regular observations
    before taking selector/replacement preimages. The latter phase is transactional.

--*/
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "ast/simplifiers/bound_propagator.h"
#include "ast/rewriter/seq_regular_rewriter.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "params/smt_params_helper.hpp"
#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <unordered_map>
#include <vector>

namespace {
using failure = seq_regular_rewriter::failure;
enum class normalization_kind { structural, decimal, scalar };

// Retain contextual conversion propagation, shared-conversion retention,
// definitions, and aggregate-first scheduling around the shared local rules.
class regular_compiler : public seq_regular_rewriter {
    std::unordered_map<expr*, expr*> normalized;
    std::unordered_map<expr*, expr*> decimal_normalized;
    std::unordered_map<expr*, expr*> scalar_normalized;
    std::unordered_map<expr*, expr*> definitions;
    obj_hashtable<expr> definition_formulas;
    // The recursive compiler at the core of this module: walks ite/and/or
    // structure, calls `atom()` at the leaves, and merges sibling
    // membership facts that share a subject via `regular_boolean()` before
    // grounding them onto a root string variable via `preimage()`.
    //
    // `defer`, when true, means "the caller is itself an and/or that may
    // still combine this result with siblings sharing the same subject, so
    // do not force a preimage pull-back yet if the result is already just
    // one ungrounded `source in language` fact" - that's the `groups.size()
    // == 1` short-circuit a few lines below. This matters because
    // `preimage()` pull-back can be expensive and is only sound/useful to
    // do once per *combined* language: e.g. a decimal comparison's ten
    // digit-value alternatives each produce their own observation on a
    // nested selector path, but they all ultimately share one ancestor
    // variable. Deferring lets `regular_boolean()` merge all ten via `join`
    // first, so the (identical, in this example) preimage chain back to
    // that ancestor is computed once instead of ten times.
    //
    // Inside one and/or, `pending`/`groups` accumulate one merged language
    // per distinct subject seen so far, and the main loop repeatedly picks
    // the *deepest* remaining subject (by AST depth, `term_depth`) and
    // either resolves it immediately (empty/full language) or calls
    // `preimage()` to fold it into its parent's group - deepest-first so a
    // subject is only ever pulled back after every sibling fact about it
    // (at every nesting level under this and/or) has already been merged in.
    expr* translate(expr* e, bool defer = false, unsigned depth = 0) {
        tick();
        if (depth > 256) throw failure::budget;
        if (m.is_true(e) || m.is_false(e)) return e;
        expr *condition, *yes, *no;
        if (m.is_ite(e, condition, yes, no)) {
            expr* guard = translate(condition, false, depth + 1);
            expr_ref_vector positive(m), negative(m), branches(m);
            positive.push_back(guard);
            positive.push_back(translate(yes, false, depth + 1));
            negative.push_back(neg(guard));
            negative.push_back(translate(no, false, depth + 1));
            branches.push_back(regular_boolean(true, positive));
            branches.push_back(regular_boolean(true, negative));
            return regular_boolean(false, branches);
        }
        if (m.is_and(e) || m.is_or(e)) {
            bool conjunction = m.is_and(e);
            expr_ref_vector children(m), rest(m);
            std::map<unsigned, expr*> pending;
            std::map<expr*, expr*, ast_lt_proc> groups;
            for (expr* arg : *to_app(e)) {
                expr* child = translate(arg, true, depth + 1);
                if (m.is_true(child) || m.is_false(child)) {
                    if (m.is_true(child) != conjunction) return child;
                    continue;
                }
                expr *s, *r;
                if (u.str.is_in_re(child, s, r)) {
                    auto it = groups.find(s);
                    groups[s] = it == groups.end() ? r :
                        conjunction ? meet(it->second, r) : join(it->second, r);
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
                // Combine observations at a shared selector before pulling them back.
                if (defer && rest.empty() && groups.size() == 1) {
                    auto const& [s, r] = *groups.begin();
                    return membership(s, r);
                }
                auto chosen = pending.begin();
                unsigned deepest = term_depth(chosen->second);
                for (auto it = std::next(chosen); it != pending.end(); ++it) {
                    unsigned d = term_depth(it->second);
                    if (d > deepest) { chosen = it; deepest = d; }
                }
                expr* s = chosen->second;
                pending.erase(chosen);
                expr* r = groups[s];
                if (u.re.is_empty(r)) {
                    if (conjunction) return keep(m.mk_false());
                    groups.erase(s);
                    continue;
                }
                if (u.re.is_full_seq(r)) {
                    if (!conjunction) return keep(m.mk_true());
                    groups.erase(s);
                    continue;
                }
                expr *parent, *inverse;
                if (preimage(s, r, parent, inverse)) {
                    groups.erase(s);
                    auto it = groups.find(parent);
                    groups[parent] = it == groups.end() ? inverse :
                        conjunction ? meet(it->second, inverse) : join(it->second, inverse);
                    pending[parent->get_id()] = parent;
                }
            }
            for (auto const& [s, r] : groups) rest.push_back(membership(s, r));
            return regular_boolean(conjunction, rest);
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
        if (m.is_not(e, child)) {
            expr* result = translate(child, true, depth + 1);
            if (u.str.is_in_re(result, source, language)) {
                language = complement(language);
                if (!defer) {
                    expr *parent, *inverse;
                    while (!u.re.is_empty(language) && !u.re.is_full_seq(language) &&
                           preimage(source, language, parent, inverse)) {
                        source = parent; language = inverse;
                    }
                }
                return membership(source, language);
            }
            return neg(result);
        }
        return e;
    }
public:
    void prepare_conversions(expr_ref_vector const& inputs, expr_ref_vector& outputs,
                             bool& contextual, unsigned& finite) {
        obj_hashtable<expr> seen;
        ptr_vector<expr> todo;
        todo.append(inputs.size(), inputs.data());
        bool bounded = false;
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            expr* s;
            bounded |= u.str.is_stoi(e, s) && !u.str.is_string(s) && bounded_length(s) <= 4096;
            if (is_app(e)) for (expr* arg : *to_app(e)) todo.push_back(arg);
        }
        if (!bounded) {
            outputs.append(inputs);
            return;
        }

        params_ref rewrite_params;
        rewrite_params.set_bool("seq_regular_rewrite", false);
        th_rewriter simplify(m, rewrite_params);
        for (expr* input : inputs) {
            expr_ref result(input, m);
            simplify(result);
            keep(result);
            result = normalize(result, normalization_kind::scalar);
            simplify(result);
            outputs.push_back(result);
        }

        using branches = std::pair<expr_ref_vector, expr_ref_vector>;
        std::map<expr*, branches> guarded;
        expr_ref_vector unconditional(m);
        std::function<void(expr*, bool, expr*, bool, unsigned)> collect =
            [&](expr* e, bool positive, expr* guard, bool branch, unsigned depth) {
                tick();
                if (depth > 256) throw failure::budget;
                while (m.is_not(e, e)) positive = !positive;
                if ((positive && m.is_and(e)) || (!positive && m.is_or(e))) {
                    for (expr* arg : *to_app(e)) collect(arg, positive, guard, branch, depth + 1);
                    return;
                }
                expr *condition, *yes, *no;
                if (!guard && m.is_ite(e, condition, yes, no) && m.is_bool(e)) {
                    collect(yes, positive, condition, true, depth + 1);
                    collect(no, positive, condition, false, depth + 1);
                    return;
                }
                expr* fact = positive ? e : neg(e);
                if (!guard) unconditional.push_back(fact);
                else {
                    auto it = guarded.try_emplace(guard, expr_ref_vector(m), expr_ref_vector(m)).first;
                    (branch ? it->second.first : it->second.second).push_back(fact);
                }
            };
        for (expr* input : outputs) collect(input, true, nullptr, false, 0);
        expr_safe_replace decisions(m);
        expr_ref_vector consequences(m), facts(m);
        for (auto const& [guard, bs] : guarded) {
            for (bool positive : {true, false}) {
                facts.reset();
                facts.append(unconditional);
                facts.append(positive ? bs.first : bs.second);
                if (arithmetic_conflict(facts)) {
                    decisions.insert(guard, positive ? m.mk_false() : m.mk_true());
                    consequences.push_back(positive ? neg(guard) : guard);
                    contextual = true;
                    break;
                }
            }
        }
        if (!decisions.empty()) {
            for (unsigned i = 0; i < outputs.size(); ++i) {
                expr_ref result(m);
                decisions(outputs.get(i), result);
                simplify(result);
                outputs.set(i, result);
            }
            expr_ref_vector retained(m);
            for (expr* consequence : consequences)
                if (!consequence_implied(consequence, outputs))
                    retained.push_back(consequence);
            // Retain guard values unless the substituted constraints still imply them.
            retained.push_back(outputs.get(0));
            outputs.set(0, boolean(true, retained));
        }

        expr_ref_vector propagated(m);
        if (arithmetic_conflict(outputs, &propagated)) {
            outputs.set(0, m.mk_false());
            contextual = true;
        }
        else if (!propagated.empty()) {
            outputs.reset();
            for (expr* formula : propagated) {
                expr_ref result(formula, m);
                simplify(result);
                outputs.push_back(result);
            }
            contextual = true;
        }

        constexpr unsigned all_digits = (1u << 10) - 1;
        std::unordered_map<expr*, unsigned> masks;
        std::function<unsigned(expr*, unsigned)> digit_mask = [&](expr* r, unsigned depth) {
            tick();
            if (depth > 256) throw failure::budget;
            auto it = masks.find(r);
            if (it != masks.end()) return it->second;
            unsigned mask = all_digits;
            expr *x, *y;
            zstring lo, hi;
            if (u.re.is_empty(r)) mask = 0;
            else if (u.re.is_to_re(r, x) && u.str.is_string(x, lo)) {
                mask = 0;
                for (unsigned ch : lo) {
                    tick();
                    if ('0' <= ch && ch <= '9') mask |= 1u << (ch - '0');
                }
            }
            else if (u.re.is_range(r, x, y) && u.str.is_string(x, lo) &&
                     u.str.is_string(y, hi) && lo.length() == 1 && hi.length() == 1) {
                mask = 0;
                for (unsigned d = 0; d < 10; ++d)
                    if (lo[0] <= '0' + d && '0' + d <= hi[0]) mask |= 1u << d;
            }
            else if (u.re.is_concat(r) || u.re.is_union(r) || u.re.is_intersection(r)) {
                bool intersection = u.re.is_intersection(r);
                mask = intersection ? all_digits : 0;
                for (expr* arg : *to_app(r)) {
                    unsigned child = digit_mask(arg, depth + 1);
                    if (intersection) mask &= child;
                    else mask |= child;
                }
            }
            else if (u.re.is_star(r, x) || u.re.is_plus(r, x) ||
                     u.re.is_opt(r, x) || u.re.is_loop(r))
                mask = digit_mask(to_app(r)->get_arg(0), depth + 1);
            masks.emplace(r, mask);
            return mask;
        };
        std::unordered_map<expr*, unsigned> alphabets;
        todo.append(outputs.size(), outputs.data());
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (m.is_and(e)) {
                for (expr* arg : *to_app(e)) todo.push_back(arg);
            }
            else {
                expr *s, *r;
                if (!u.str.is_in_re(e, s, r)) continue;
                unsigned mask = digit_mask(r, 0);
                auto [it, fresh] = alphabets.emplace(s, mask);
                if (!fresh) it->second &= mask;
            }
        }
        expr_safe_replace conversions(m);
        seen.reset();
        todo.append(outputs.size(), outputs.data());
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            expr* s;
            if (u.str.is_stoi(e, s) && !u.str.is_string(s) && u.str.max_length(s) <= 1) {
                unsigned mask = all_digits;
                expr* root = s;
                expr *parent, *index, *length;
                while (u.str.is_at(root, parent, index) || u.str.is_extract(root, parent, index, length)) {
                    tick();
                    auto it = alphabets.find(root);
                    if (it != alphabets.end()) mask &= it->second;
                    root = parent;
                }
                auto it = alphabets.find(root);
                if (it != alphabets.end()) mask &= it->second;
                contextual |= mask != all_digits;
                conversions.insert(e, finite_conversion(s, mask));
                ++finite;
            }
            if (is_app(e)) for (expr* arg : *to_app(e)) todo.push_back(arg);
        }
        if (!conversions.empty()) {
            for (unsigned i = 0; i < outputs.size(); ++i) {
                tick();
                expr_ref result(m);
                conversions(outputs.get(i), result);
                simplify(result);
                outputs.set(i, result);
            }
        }
    }
    bool consequence_implied(expr* consequence, expr_ref_vector const& inputs) {
        expr_ref_vector facts(m);
        facts.append(inputs);
        facts.push_back(neg(consequence));
        if (arithmetic_conflict(facts)) return true;
        expr *predicate, *source, *word;
        if (!m.is_not(consequence, predicate)) return false;
        if (!u.str.is_prefix(predicate, word, source) &&
            !u.str.is_suffix(predicate, word, source) &&
            !u.str.is_contains(predicate, source, word))
            return false;
        zstring text;
        if (!u.str.is_string(word, text)) return false;
        bool nondecimal = false;
        for (unsigned ch : text) {
            tick();
            nondecimal |= ch < '0' || ch > '9';
        }
        if (!nondecimal) return false;
        // A valid decimal string cannot contain a literal nondecimal character.
        expr* conversion = keep(u.str.mk_stoi(source));
        facts.set(facts.size() - 1, comparison(comparison_kind::lt, conversion, rational(0)));
        return arithmetic_conflict(facts);
    }
    bool arithmetic_conflict(expr_ref_vector const& inputs, expr_ref_vector* simplified = nullptr) {
        unsynch_mpq_manager nm;
        small_object_allocator allocator;
        bound_propagator bounds(nm, allocator, params_ref());
        std::unordered_map<expr*, unsigned> variables;
        obj_hashtable<expr> seen;
        ptr_vector<expr> todo;
        expr_ref_vector premises(m);
        for (expr* input : inputs) todo.push_back(input);
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            expr* literal = e;
            bool positive = true;
            while (m.is_not(e, e)) {
                tick();
                positive = !positive;
            }
            if (m.is_true(e) || m.is_false(e)) {
                if (m.is_true(e) != positive) return true;
                continue;
            }
            if (positive && m.is_and(e)) {
                for (expr* arg : *to_app(e)) todo.push_back(arg);
                continue;
            }
            if (!is_app(e) || to_app(e)->get_num_args() != 2) continue;
            app* t = to_app(e);
            if (!a.is_int(t->get_arg(0)) && !a.is_real(t->get_arg(0))) continue;
            bool equality = m.is_eq(e);
            bool lower = a.is_ge(e) || a.is_gt(e);
            bool strict = a.is_lt(e) || a.is_gt(e);
            if (!equality && !lower && !a.is_le(e) && !a.is_lt(e)) continue;
            linear value = affine(t->get_arg(0));
            value.add(affine(t->get_arg(1)), rational(-1));
            if (value.terms.empty()) {
                bool holds = equality ? value.constant.is_zero() :
                    lower ? (strict ? value.constant > 0 : value.constant >= 0) :
                            (strict ? value.constant < 0 : value.constant <= 0);
                if (holds != positive) return true;
                continue;
            }
            if (value.terms.size() != 1 || (equality && !positive)) continue;
            if (!positive) { lower = !lower; strict = !strict; }
            auto [term, coefficient] = *value.terms.begin();
            if (coefficient.is_neg()) lower = !lower;
            rational limit = -value.constant / coefficient;
            auto [it, fresh] = variables.emplace(term, static_cast<unsigned>(variables.size()));
            unsigned v = it->second;
            if (fresh) {
                bounds.mk_var(v, a.is_int(term));
                scalar_range r = range(term);
                scoped_mpq n(nm);
                if (r.lo) {
                    nm.set(n, r.lo->to_mpq());
                    bounds.assert_lower(v, n, false);
                }
                if (r.hi) {
                    nm.set(n, r.hi->to_mpq());
                    bounds.assert_upper(v, n, false);
                }
            }
            scoped_mpq n(nm);
            nm.set(n, limit.to_mpq());
            if (equality || lower) bounds.assert_lower(v, n, strict);
            if (equality || !lower) bounds.assert_upper(v, n, strict);
            if (bounds.inconsistent()) return true;
            if (simplified) premises.push_back(literal);
        }
        if (!simplified || variables.empty()) return false;
        range_map context;
        for (auto const& [term, v] : variables) {
            scalar_range r;
            if (bounds.has_lower(v)) r.lo = rational(bounds.lower(v));
            if (bounds.has_upper(v)) r.hi = rational(bounds.upper(v));
            context.emplace(term, r);
        }
        expr_safe_replace sub(m);
        seen.reset();
        todo.append(inputs.size(), inputs.data());
        while (!todo.empty()) {
            tick();
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            if (!is_app(e)) continue;
            app* t = to_app(e);
            comparison_kind op;
            if (comparison_operator(t, op)) {
                linear value = affine(t->get_arg(0));
                value.add(affine(t->get_arg(1)), rational(-1));
                if (value.terms.size() > 1)
                    if (expr* result = range_comparison(op, range(value, 0, &context)))
                        sub.insert(e, result);
            }
            for (expr* arg : *t) todo.push_back(arg);
        }
        if (sub.empty()) return false;
        for (expr* input : inputs) {
            expr_ref result(m);
            sub(input, result);
            simplified->push_back(result);
        }
        // Contextual consequences must not remove their supporting bounds.
        premises.push_back(simplified->get(0));
        simplified->set(0, boolean(true, premises));
        return false;
    }

    regular_compiler(ast_manager& m, unsigned limit, unsigned& steps, unsigned& preimages):
        seq_regular_rewriter(m, limit, steps, preimages) {}
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
    expr* normalize(expr* e, normalization_kind kind = normalization_kind::structural) {
        auto& cache = kind == normalization_kind::decimal ? decimal_normalized :
                      kind == normalization_kind::scalar ? scalar_normalized : normalized;
        ptr_vector<expr> todo;
        obj_hashtable<expr> active;
        bool expand = kind == normalization_kind::structural && !definitions.empty();
        auto push = [&](expr* t) {
            if (expand) {
                if (active.contains(t)) throw failure::unsupported;
                active.insert(t);
            }
            todo.push_back(t);
        };
        auto pop = [&]() {
            if (expand) active.erase(todo.back());
            todo.pop_back();
        };
        push(e);
        while (!todo.empty()) {
            tick();
            expr* cur = todo.back();
            if (cache.count(cur)) { pop(); continue; }
            if (expand) {
                if (definition_formulas.contains(cur)) {
                    cache[cur] = keep(m.mk_true());
                    pop();
                    continue;
                }
                auto it = definitions.find(cur);
                if (it != definitions.end()) {
                    if (!cache.count(it->second)) { push(it->second); continue; }
                    cache[cur] = cache[it->second];
                    pop();
                    continue;
                }
            }
            if (!is_app(cur)) throw failure::unsupported;
            bool ready = true;
            for (expr* arg : *to_app(cur)) {
                if (!cache.count(arg)) { push(arg); ready = false; break; }
            }
            if (!ready) continue;
            expr_ref_vector args(m);
            for (expr* arg : *to_app(cur)) args.push_back(cache[arg]);
            if (kind != normalization_kind::structural) {
                app* rebuilt = to_app(keep(m.mk_app(to_app(cur)->get_decl(), args.size(), args.data())));
                cache[cur] = kind == normalization_kind::decimal ? lower_decimal(rebuilt) : lower_scalar(rebuilt);
            }
            else
                cache[cur] = normalize_node(to_app(cur), args);
            pop();
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
    bool has_nonregular_arithmetic(expr* e) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(e);
        while (!todo.empty()) {
            tick();
            expr* current = todo.back();
            todo.pop_back();
            if (seen.contains(current)) continue;
            seen.insert(current);
            if (m.is_and(current) || m.is_or(current) || m.is_not(current) || m.is_ite(current)) {
                for (expr* arg : *to_app(current)) todo.push_back(arg);
                continue;
            }
            comparison_kind op;
            if (!is_app(current) || !comparison_operator(to_app(current), op)) continue;
            linear value = affine(to_app(current)->get_arg(0));
            value.add(affine(to_app(current)->get_arg(1)), rational(-1));
            for (auto const& [term, coefficient] : value.terms)
                if (!u.str.is_length(term) && !u.str.is_index(term)) return true;
        }
        return false;
    }
    expr_ref compile(expr* e) {
        if (is_root_regular(e))
            return expr_ref(e, m);
        expr_ref result(normalize(e), m);
        // Avoid speculative preimage allocation for unsupported arithmetic.
        if (has_nonregular_arithmetic(result)) throw failure::unsupported;
        result = translate(result);
        if (!is_root_regular(result))
            throw failure::unsupported;
        return result;
    }
    expr_ref compile_definitions(expr* e, unsigned& count) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        expr_ref_vector retained(m);
        todo.push_back(e);
        while (!todo.empty()) {
            tick();
            expr* current = todo.back();
            todo.pop_back();
            if (seen.contains(current)) continue;
            seen.insert(current);
            if (m.is_and(current)) {
                for (expr* arg : *to_app(current)) todo.push_back(arg);
                continue;
            }
            expr *x, *y;
            if (!m.is_eq(current, x, y)) continue;
            for (unsigned i = 0; i < 2; ++i) {
                if (is_uninterp_const(x) && u.is_string(x->get_sort()) &&
                    is_app(y) && to_app(y)->get_num_args() != 0) {
                    definitions.emplace(x, y);
                    definition_formulas.insert(current);
                    retained.push_back(current);
                    break;
                }
                std::swap(x, y);
            }
        }
        if (retained.empty()) throw failure::unsupported;
        normalized.clear();
        expr_ref result = compile(e);
        count = retained.size();
        // Keep definitions for the usual equation solver and model reconstruction.
        retained.push_back(result);
        return expr_ref(boolean(true, retained), m);
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
        m_enabled = params.seq_regular();
        m_max_steps = params.seq_regular_max_steps();
    }
    else
        m_max_steps = p.get_uint("seq_regular.max_steps", m_max_steps);
}

void seq_regular_simplifier::collect_param_descrs(param_descrs& r) {
    r.insert("seq_regular.max_steps", CPK_UINT, "maximum work for a transactional regular-preimage pass", "100000");
}

// The staged pipeline, each stage preserving as much progress as it safely
// can if a later one fails (regular_compiler's internal `failure` exceptions
// signal "cannot do more", not "this is wrong" - unsupported syntax, a step
// budget, or cancellation are all expected, ordinary outcomes here):
//
//  1. arithmetic_conflict(): a cheap pre-check with the generic bound
//     propagator, screening for a plain arithmetic contradiction among the
//     original assertions before paying for any regex compilation at all.
//  2. normalize(..., decimal): lowers decimal constant comparisons (a
//     concern parallel to, and independent of, regularization proper - see
//     the `comparison`/`decimal_language` family) and retries if nothing
//     shared was lost (retain_shared_conversions).
//  3. compile(): the main regularization pass (normalize + translate, see
//     their own comments) over either every formula individually (if any
//     carries its own unsat-core dependency - "labeled") or their
//     conjunction (letting the compiler exploit cross-formula sharing).
//  4. On a failure::unsupported from (3), compile_definitions() is a
//     weaker fallback: it retains simple `var = f(...)` equations verbatim
//     (for the ordinary equation solver and model reconstruction) and
//     retries compiling the rest.
//  5. If even that fails, this reduce() call still keeps whatever the
//     decimal-lowering stage (2) already achieved, unless the failure was
//     cancellation.
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
    expr_ref_vector originals(m), prepared(m), decimals(m), results(m);
    expr_dependency_ref context_dep(m);
    bool labeled = false;
    for (unsigned i = qhead(); i < qtail(); ++i) {
        labeled |= m_fmls[i].dep() != nullptr;
        context_dep = m.mk_join(context_dep, m_fmls[i].dep());
        originals.push_back(m_fmls[i].fml());
    }
    bool decimal_changed = false;
    bool contextual = false;
    unsigned finite = 0;
    try {
        if (compiler.arithmetic_conflict(originals)) {
            expr_dependency_ref dep(m);
            for (unsigned i = qhead(); i < qtail(); ++i)
                dep = m.mk_join(dep, m_fmls[i].dep());
            m_fmls.update(qhead(), dependent_expr(m, m.mk_false(), nullptr, dep));
            m_steps += steps;
            ++m_arith_refuted;
            ++m_rewritten;
            return;
        }
        compiler.prepare_conversions(originals, prepared, contextual, finite);
        for (expr* input : prepared) {
            expr* result = compiler.normalize(input, normalization_kind::decimal);
            decimals.push_back(result);
        }
        if (!compiler.retain_shared_conversions(decimals)) {
            decimals.reset();
            decimals.append(prepared);
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
        bool recovered = false;
        if (why == failure::unsupported) {
            try {
                unsigned definitions = 0;
                expr_ref input(mk_and(decimals), m);
                expr_ref result(compiler.compile_definitions(input, definitions), m);
                results.reset();
                results.push_back(result);
                for (unsigned i = qhead() + 1; i < qtail(); ++i) results.push_back(m.mk_true());
                m_definitions += definitions;
                contextual = true;
                recovered = true;
            }
            catch (failure reason) {
                why = reason;
            }
        }
        if (!recovered) {
            if (why == failure::unsupported) ++m_unsupported;
            else if (why == failure::budget) ++m_budget;
            if (!decimal_changed || why == failure::canceled) {
                m_steps += steps;
                return;
            }
            results.reset();
            results.append(decimals);
        }
    }
    m_steps += steps;
    if (m_automatic && !decimal_changed && m_preimages == preimages_before &&
        !std::all_of(results.begin(), results.end(), [&](expr* e) { return m.is_true(e) || m.is_false(e); }))
        return;
    unsigned end = qtail();
    m_finite_rewritten += finite;
    for (unsigned i = qhead(); i < end && !m_fmls.inconsistent(); ++i) {
        auto const& old = m_fmls[i];
        expr* result = results.get(i - qhead());
        if (result != old.fml()) {
            if (decimals.get(i - qhead()) != old.fml()) ++m_stoi_rewritten;
            m_fmls.update(i, dependent_expr(m, result, nullptr, contextual ? context_dep.get() : old.dep()));
            ++m_rewritten;
        }
    }
}

void seq_regular_simplifier::reset_statistics() {
    m_steps = m_preimages = m_rewritten = m_stoi_rewritten = m_finite_rewritten = m_unsupported = m_budget = m_skipped = m_arith_refuted = m_definitions = 0;
    m_watch.reset();
}

void seq_regular_simplifier::collect_statistics(statistics& st) const {
    st.update("seq-regular-steps", m_steps);
    st.update("seq-regular-preimages", m_preimages);
    st.update("seq-regular-rewritten", m_rewritten);
    st.update("seq-regular-stoi-rewritten", m_stoi_rewritten);
    st.update("seq-regular-finite-conversions", m_finite_rewritten);
    st.update("seq-regular-arith-refuted", m_arith_refuted);
    st.update("seq-regular-definitions", m_definitions);
    st.update("seq-regular-unsupported", m_unsupported);
    st.update("seq-regular-budget", m_budget);
    st.update("seq-regular-skipped", m_skipped);
    st.update("seq-regular-time-ms", 1000.0 * m_watch.get_seconds());
}
