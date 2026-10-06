/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_field_problem.h

Abstract:

    AST-level prime-field problem builder: normalizes and polynomial-encodes
    ground equalities/disequalities over a single field sort, then hands them
    to the Groebner-basis algebra engine (math/ff). Used by theory_ff and
    available to any future consumer that needs the same combination without
    depending on a particular SMT core's enode representation.

Author:

    Romain Soulat

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ff_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/ff/ff_params.h"
#include "math/ff/ff_polynomial.h"
#include "params/smt_params_helper.hpp"
#include "util/dependency.h"
#include <memory>
#include <set>
#include <vector>

namespace ff {
    // Polynomial encodings of field terms, shared across final checks.
    // Not used with compact encodings, whose fresh definitional variables
    // belong to a single problem.
    struct ff_encoding_cache {
        obj_map<expr, ff::polynomial> cache;
        obj_map<expr, unsigned> variable_ids;
        unsigned num_variables = 0;
        expr_ref_vector pins;
        explicit ff_encoding_cache(ast_manager &m) : pins(m) {}
        void reset() {
            cache.reset();
            variable_ids.reset();
            num_variables = 0;
            pins.reset();
        }
    };

    struct field_problem {
        ast_manager &m;
        ff_util ff;
        smt_params_helper options;
        ff::engine algebra;
        ff_encoding_cache local;
        ff_encoding_cache &enc;
        obj_map<expr, ff::polynomial> &cache;
        unsigned &num_variables;
        std::vector<ff::polynomial> eqs, neqs;
        expr_ref_vector premises;
        struct constraint {
            expr *a, *b;
            bool equality;
        };
        std::vector<constraint> inputs;
        obj_map<expr, expr *> normalized;
        u_dependency_manager dep;
        obj_map<expr, u_dependency *> normalization_deps;
        obj_map<expr, unsigned> &variable_ids;
        obj_map<expr, rational> evaluated;
        expr_ref_vector pins;
        th_rewriter rw;

        field_problem(ast_manager &m, sort *s, params_ref const &p, ff_encoding_cache *shared)
            : m(m), ff(m), options(p), algebra(ff.modulus(s), m.limit(), options.ff_max_steps(),
                                   options.ff_max_terms(), options.ff_bit_propagation(),
                                   options.ff_batch(), options.ff_sparse_witness()),
              local(m), enc(shared && !options.ff_compact_encoding() ? *shared : local),
              cache(enc.cache), num_variables(enc.num_variables), premises(m), variable_ids(enc.variable_ids),
              pins(m), rw(m) {
            ff::configure_engine(algebra, options);

        }

        expr *normalize(expr *root) {
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (normalized.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                if (!ff.is_interp(e)) {
                    // Foreign applications are opaque to this field.
                    normalized.insert(e, e);
                    todo.pop_back();
                    continue;
                }
                bool ready = true;
                for (expr *arg : *a)
                    if (!normalized.contains(arg)) {
                        todo.push_back(arg);
                        ready = false;
                    }
                if (!ready)
                    continue;
                expr_ref_vector args(m);
                u_dependency *deps = nullptr;
                for (expr *arg : *a) {
                    args.push_back(normalized.find(arg));
                    u_dependency *used = nullptr;
                    normalization_deps.find(arg, used);
                    deps = dep.mk_join(deps, used);
                }
                normalization_deps.insert(e, deps);
                expr_ref value = rw.mk_app(a->get_decl(), args);
                pins.push_back(value);
                normalized.insert(e, value);
                todo.pop_back();
            }
            return normalized.find(root);
        }

        void prepare() {
            obj_map<expr, unsigned> definitions;
            std::vector<unsigned> chosen;
            ptr_vector<expr> vars, defs;
            for (unsigned i = 0; i < inputs.size(); ++i) {
                auto [a, b, equality] = inputs[i];
                if (!equality)
                    continue;
                if (!is_uninterp_const(a))
                    std::swap(a, b);
                if (!is_uninterp_const(a) || definitions.contains(a))
                    continue;
                definitions.insert(a, vars.size());
                vars.push_back(a);
                defs.push_back(b);
                chosen.push_back(i);
            }
            std::vector<std::vector<unsigned>> uses(vars.size());
            std::vector<unsigned> degree(vars.size(), 0), order;
            for (unsigned i = 0; i < defs.size(); ++i) {
                std::set<expr *> seen;
                ptr_vector<expr> todo;
                todo.push_back(defs[i]);
                while (!todo.empty()) {
                    if (!m.inc())
                        throw ff::exhausted();
                    expr *e = todo.back();
                    todo.pop_back();
                    if (!seen.insert(e).second)
                        continue;
                    unsigned use_id;
                    if (definitions.find(e, use_id)) {
                        uses[use_id].push_back(i);
                        ++degree[i];
                    }
                    if (ff.is_interp(e))
                        for (expr *arg : *to_app(e))
                            todo.push_back(arg);
                }
                if (!degree[i])
                    order.push_back(i);
            }
            for (unsigned pos = 0; pos < order.size(); ++pos)
                for (unsigned j : uses[order[pos]])
                    if (!--degree[j])
                        order.push_back(j);
            std::set<unsigned> removed;
            // Substitute acyclic x=t definitions along the DAG; cycles and
            // competing definitions remain residual constraints. Record
            // each substitution's transitive support so a conflict only
            // depends on the definitions its terms actually used.
            for (unsigned i : order) {
                expr *value = normalize(defs[i]);
                normalized.insert(vars[i], value);
                u_dependency *deps = nullptr;
                normalization_deps.find(defs[i], deps);
                deps = dep.mk_join(deps, dep.mk_leaf(chosen[i]));
                normalization_deps.insert(vars[i], deps);
                removed.insert(chosen[i]);
            }
            for (unsigned i = 0; i < inputs.size(); ++i) {
                if (removed.contains(i))
                    continue;
                auto [a, b, equality] = inputs[i];
                expr *lhs_term = normalize(a), *rhs_term = normalize(b);
                u_dependency *dependencies = nullptr;
                normalization_deps.find(a, dependencies);
                u_dependency *rhs_deps = nullptr;
                normalization_deps.find(b, rhs_deps);
                dependencies = dep.mk_join(dependencies, rhs_deps);
                a = lhs_term;
                b = rhs_term;
                // After substitution, t=t imposes no residual constraint.
                if (a == b && equality)
                    continue;
                ff::polynomial f;
                if (a != b) {
                    auto lhs = encode(a);
                    auto rhs = encode(b);
                    f = algebra.add(std::move(lhs), rhs, rational(-1));
                }
                if (f.empty() && equality)
                    continue;
                dependencies = dep.mk_join(dependencies, dep.mk_leaf(i));
                vector<unsigned, false> flat;
                dep.linearize(dependencies, flat);
                f.dependencies.insert(flat.begin(), flat.end());
                (equality ? eqs : neqs).push_back(std::move(f));
            }
        }

        rational evaluate(expr *root, std::vector<rational> const &values) {
            root = normalize(root);
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (evaluated.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                rational value;
                if (ff.is_numeral(e, value)) {
                }
                else if (!ff.is_interp(e)) {
                    unsigned vid;
                    value = variable_ids.find(e, vid) ? values[vid] : rational(0);
                }
                else {
                    bool ready = true;
                    for (expr *arg : *a)
                        if (!evaluated.contains(arg)) {
                            todo.push_back(arg);
                            ready = false;
                        }
                    if (!ready)
                        continue;
                    bool mul = ff.is_mul(e);
                    value = rational(mul ? 1 : 0);
                    rational weight(1);
                    for (expr *arg : *a) {
                        rational const &v = evaluated.find(arg);
                        value = mod(mul ? value * v : value + weight * v, ff.modulus(e->get_sort()));
                        if (ff.is_bitsum(e))
                            weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                    }
                    if (ff.is_neg(e))
                        value = mod(-value, ff.modulus(e->get_sort()));
                }
                evaluated.insert(e, value);
                todo.pop_back();
            }
            return evaluated.find(root);
        }

        ff::polynomial compact(ff::polynomial f, bool force = false) {
            if (!algebra.compact_encoding || f.empty()) return f;
            // Preserve affine packs for bit propagation; introduce a wire
            // only for nonlinear growth, or before a product exceeds the bound.
            if (!force && (f.begin()->first.size() <= 1 || (f.size() <= 64 && f.begin()->first.size() <= 32))) return f;
            if (f.size() == 1 && f.begin()->first.size() <= 1) return f;
            // z=f is a definitional extension and needs no asserted premise.
            unsigned v = num_variables++;
            auto z = algebra.variable(v);
            eqs.push_back(algebra.add(z, f, rational(-1)));
            algebra.definition_variables.insert(v);
            return z;
        }
        ff::polynomial const &encode(expr *root) {
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (cache.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                app *a = to_app(e);
                bool interpreted = ff.is_interp(e);
                bool ready = true;
                if (interpreted)
                    for (expr *arg : *a)
                        if (!cache.contains(arg)) {
                            todo.push_back(arg);
                            ready = false;
                        }
                if (!ready)
                    continue;
                ff::polynomial f;
                rational value;
                if (ff.is_numeral(e, value))
                    f = algebra.constant(value);
                else if (!interpreted) {
                    // A foreign application is an atomic field value; its
                    // equalities from other theories are added below.
                    variable_ids.insert(e, num_variables);
                    f = algebra.variable(num_variables++);
                }
                else if (ff.is_neg(e))
                    f = algebra.scale(cache.find(a->get_arg(0)), rational(-1));
                else {
                    bool mul = ff.is_mul(e);
                    f = algebra.constant(rational(mul ? 1 : 0));
                    rational weight(1);
                    for (expr *arg : *a) {
                        auto const &b = cache.find(arg);
                        if (mul && algebra.compact_encoding && f.size() && b.size() > 256 / f.size()) {
                            // Abstract before the Cartesian product, not after.
                            f = compact(std::move(f), true);
                            auto operand = compact(b, true);
                            f = algebra.mul(f, operand);
                        }
                        else f = mul ? algebra.mul(f, b) : algebra.add(std::move(f), b, weight);
                        f = compact(std::move(f));
                        if (ff.is_bitsum(e))
                            weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                    }
                }
                cache.insert(e, std::move(f));
                enc.pins.push_back(e);
                todo.pop_back();
            }
            return cache.find(root);
        }

        void add(expr *a, expr *b, bool equality) {
            expr_ref premise(m.mk_eq(a, b), m);
            if (!equality)
                premise = m.mk_not(premise);
            premises.push_back(premise);
            inputs.push_back({a, b, equality});
        }
    };
}  // namespace ff
