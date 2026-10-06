/*++
Copyright (c) 2026 Romain Soulat

    Assertion-independent summaries for the Boolean-domain preservation
    heuristic. This analysis does not prove that a term is Boolean.
--*/
#pragma once
#include "ast/ff_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/common_msgs.h"

class ff_domain_analysis {
    struct summary {
        expr* variable = nullptr;
        unsigned degree = 0;
        rational zero{0}, one{0};
        bool valid = true;
    };
    ast_manager& m;
    ff_util ff;
    obj_map<expr, summary> cache;
    expr_ref_vector pins;

    summary const& analyze(expr* root) {
        ptr_vector<expr> pending;
        pending.push_back(root);
        while (!pending.empty()) {
            if (!m.inc())
                throw rewriter_exception(Z3_CANCELED_MSG);
            expr* e = pending.back();
            if (cache.contains(e)) {
                pending.pop_back();
                continue;
            }
            summary value;
            rational c;
            if (!is_app(e))
                value.valid = false;
            else if (!ff.is_interp(e)) {
                // A foreign field-valued application is one opaque variable.
                // Its arguments belong to the other theory, not this polynomial.
                value.variable = e;
                value.degree = 1;
                value.one = rational(1);
            }
            else if (ff.is_numeral(e, c))
                value.zero = value.one = c;
            else if (!ff.is_add(e) && !ff.is_mul(e) && !ff.is_neg(e))
                value.valid = false;
            else {
                bool ready = true;
                for (expr* arg : *to_app(e))
                    if (!cache.contains(arg)) {
                        pending.push_back(arg);
                        ready = false;
                    }
                if (!ready)
                    continue;
                bool mul = ff.is_mul(e);
                if (mul)
                    value.zero = value.one = rational(1);
                rational const& p = ff.modulus(e->get_sort());
                for (expr* arg : *to_app(e)) {
                    auto const& child = cache.find(arg);
                    if (!child.valid || (value.variable && child.variable && value.variable != child.variable)) {
                        value.valid = false;
                        break;
                    }
                    if (child.variable)
                        value.variable = child.variable;
                    value.degree = mul ? value.degree + child.degree : std::max(value.degree, child.degree);
                    if (value.degree > 2) {
                        value.valid = false;
                        break;
                    }
                    value.zero = mod(mul ? value.zero * child.zero : value.zero + child.zero, p);
                    value.one = mod(mul ? value.one * child.one : value.one + child.one, p);
                }
                if (ff.is_neg(e)) {
                    value.zero = mod(-value.zero, p);
                    value.one = mod(-value.one, p);
                }
            }
            cache.insert(e, value);
            pins.push_back(e);
        }
        return cache.find(root);
    }

public:
    explicit ff_domain_analysis(ast_manager& m) : m(m), ff(m), pins(m) {}

    // Summaries depend only on immutable terms, never an assertion's truth or
    // a chosen candidate variable. A single instance may analyze many roots:
    // total traversal is linear in their distinct DAG nodes and argument edges.
    // Pin keys because callers may replace assertions or release temporary ASTs.
    unsigned cache_size() const { return cache.size(); }
    expr* variable(expr* formula) {
        expr *a, *b;
        if (!m.is_eq(formula, a, b) || !ff.is_ff(a))
            return nullptr;
        if ((!ff.is_interp(a) && ff.is_numeral(b)) || (!ff.is_interp(b) && ff.is_numeral(a)))
            return nullptr;
        auto lhs = analyze(a);
        auto rhs = analyze(b);
        if (!lhs.valid || !rhs.valid || (lhs.variable && rhs.variable && lhs.variable != rhs.variable))
            return nullptr;
        // Degree and two samples preserve the old heuristic, including its
        // possible match of an identically-zero polynomial. A match is only
        // a reason to preserve an equation, never evidence of Booleanity.
        return std::max(lhs.degree, rhs.degree) == 2 && lhs.zero == rhs.zero && lhs.one == rhs.one ?
            (lhs.variable ? lhs.variable : rhs.variable) : nullptr;
    }
};
