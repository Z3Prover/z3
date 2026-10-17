/*++
Copyright (c) 2026 Microsoft Corporation

Abstract:
    Arithmetic evidence with dependency erasure.
--*/
#pragma once

#include <memory>
#include <unordered_map>
#include "util/dependency.h"
#include "math/lp/lp_utils.h"

namespace lp {

    class evidence_manager : public u_dependency_manager {
    public:
        using ref = u_dependency *;
        enum class rule {
            input,
            linear,
            integer_tighten,
            integer_lattice,
            gomory,
            monomial_substitute,
            monomial_interval,
            discharge,
            unsupported
        };

        struct fact {
            vector<std::pair<mpq, lpvar>> lhs;
            lconstraint_kind kind = EQ;
            impq rhs;
            bool contradiction = false;
        };

        struct premise {
            ref evidence;
            mpq coefficient;
            premise(ref e, mpq const &c) : evidence(e), coefficient(c) {}
        };

        struct column_bounds {
            lpvar column;
            unsigned lower = UINT_MAX;
            unsigned upper = UINT_MAX;
        };

        struct recipe {
            rule kind = rule::unsupported;
            fact conclusion;
            vector<premise> premises;
            ref assumption = nullptr;
            constraint_index input = UINT_MAX;
            unsigned id = 0;
            bool has_fact = false;
            fact equation;
            lpvar pivot = UINT_MAX;
            vector<column_bounds> bounds;
            unsigned definition = UINT_MAX;
            lpvar source = UINT_MAX;
            mpq divisor = mpq(1);
        };

        struct proof_step {
            rule kind = rule::unsupported;
            fact conclusion;
            unsigned_vector premises;
            vector<mpq> coefficients;
            constraint_index input = UINT_MAX;
            unsigned assumption = UINT_MAX;
            unsigned id = 0;
            fact equation;
            lpvar pivot = UINT_MAX;
            vector<column_bounds> bounds;
            unsigned definition = UINT_MAX;
            lpvar source = UINT_MAX;
            mpq divisor = mpq(1);
        };

        struct variable {
            bool is_int = false;
            vector<std::pair<mpq, lpvar>> definition;
        };

        struct monomial {
            lpvar column;
            unsigned_vector factors;
        };

        struct proof_expression {
            vector<variable> variables;
            vector<monomial> monomials;
            vector<proof_step> steps;
            unsigned root = UINT_MAX;
            bool complete = true;
            bool check() const;
        };

    private:
        bool m_enabled = false;
        vector<std::unique_ptr<recipe>> m_recipes;
        ptr_vector<u_dependency> m_inputs;
        unsigned_vector m_scopes;
        unsigned_vector m_variable_scopes;
        unsigned_vector m_current_variables;
        vector<variable> m_variables;
        vector<monomial> m_monomials;

        void snapshot(fact &f) const {
            for (auto &[c, j] : f.lhs) {
                SASSERT(j < m_current_variables.size());
                j = m_current_variables[j];
            }
        }

        ref attach(ref support, std::unique_ptr<recipe> r) {
            snapshot(r->conclusion);
            snapshot(r->equation);
            if (r->pivot != UINT_MAX)
                r->pivot = m_current_variables[r->pivot];
            if (r->source != UINT_MAX)
                r->source = m_current_variables[r->source];
            for (auto &bound : r->bounds)
                bound.column = m_current_variables[bound.column];
            r->id = m_recipes.size();
            auto *p = r.get();
            m_recipes.push_back(std::move(r));
            return mk_annotation(support, p);
        }

    public:
        explicit evidence_manager(bool enabled = false) : m_enabled(enabled) {}

        fact snapshot_fact(fact f) const {
            snapshot(f);
            return f;
        }

        void snapshot_context(proof_expression& result) const {
            result.variables = m_variables;
            result.monomials = m_monomials;
        }

        bool proofs_enabled() const {
            return m_enabled;
        }

        unsigned num_current_variables() const { return m_current_variables.size(); }
        unsigned variable_id(lpvar column) const { return m_current_variables[column]; }

        void reset() {
            m_recipes.reset();
            m_inputs.reset();
            m_scopes.reset();
            m_variable_scopes.reset();
            m_current_variables.reset();
            m_variables.reset();
            m_monomials.reset();
            u_dependency_manager::reset();
        }

        void register_variable(lpvar column, bool is_int, vector<std::pair<mpq, lpvar>> const &definition = {}) {
            if (!m_enabled)
                return;
            SASSERT(column == m_current_variables.size());
            variable v;
            v.is_int = is_int;
            for (auto const &[c, j] : definition) {
                SASSERT(j < m_current_variables.size());
                v.definition.push_back({c, m_current_variables[j]});
            }
            m_current_variables.push_back(m_variables.size());
            m_variables.push_back(std::move(v));
        }

        void register_monomial(lpvar column, unsigned size, lpvar const *factors) {
            if (!m_enabled)
                return;
            monomial m;
            m.column = m_current_variables[column];
            for (unsigned i = 0; i < size; ++i)
                m.factors.push_back(m_current_variables[factors[i]]);
            m_monomials.push_back(std::move(m));
        }

        unsigned monomial_definition(lpvar column) const {
            for (unsigned i = m_monomials.size(); i-- > 0;)
                if (m_monomials[i].column == m_current_variables[column])
                    return i;
            return UINT_MAX;
        }

        ref mk_leaf(unsigned ci) {
            if (!m_enabled)
                return u_dependency_manager::mk_leaf(ci);
            if (ci < m_inputs.size() && m_inputs[ci])
                return m_inputs[ci];
            auto r = std::make_unique<recipe>();
            r->kind = rule::input;
            r->input = ci;
            ref result = attach(u_dependency_manager::mk_leaf(ci), std::move(r));
            m_inputs.resize(std::max(m_inputs.size(), ci + 1), nullptr);
            m_inputs[ci] = result;
            return result;
        }

        static recipe const *get_recipe(ref e) {
            return get_annotation<recipe>(e);
        }

        void set_input_fact(ref e, fact f) {
            SASSERT(m_enabled && get_recipe(e) && get_recipe(e)->kind == rule::input);
            auto *r = m_recipes[get_recipe(e)->id].get();
            SASSERT(!r->has_fact);
            snapshot(f);
            r->conclusion = std::move(f);
            r->has_fact = true;
        }

        template <typename Capture> ref derive(ref support, Capture &&capture) {
            if (!m_enabled)
                return support;
            return attach(support, std::make_unique<recipe>(capture()));
        }

        void push_scope() {
            if (!m_enabled)
                u_dependency_manager::push_scope();
            else {
                m_scopes.push_back(m_inputs.size());
                m_variable_scopes.push_back(m_current_variables.size());
            }
        }

        void pop_scope(unsigned n) {
            if (!m_enabled) {
                u_dependency_manager::pop_scope(n);
                return;
            }
            SASSERT(n <= m_scopes.size());
            if (n) {
                m_inputs.shrink(m_scopes[m_scopes.size() - n]);
                m_scopes.shrink(m_scopes.size() - n);
                m_current_variables.shrink(m_variable_scopes[m_variable_scopes.size() - n]);
                m_variable_scopes.shrink(m_variable_scopes.size() - n);
            }
            // Recipes can escape an LP probe via assumption discharge. Retain their
            // nodes until the manager dies, including leaves with recycled indices.
        }

        bool linearize_coefficients(ref root, mpq const &coefficient,
                                    vector<std::pair<constraint_index, mpq>> &result) const {
            std::unordered_map<ref, unsigned> indices;
            ptr_vector<u_dependency> order, todo;
            if (root)
                todo.push_back(root);
            while (!todo.empty()) {
                auto *e = todo.back();
                auto *r = get_recipe(e);
                if (!r || (r->kind != rule::input && r->kind != rule::linear))
                    return false;
                if (r->kind == rule::input && !r->has_fact)
                    return false;
                if (indices.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                bool ready = true;
                for (auto const &p : r->premises)
                    if (!indices.contains(p.evidence)) {
                        todo.push_back(p.evidence);
                        ready = false;
                    }
                if (ready) {
                    indices.emplace(e, order.size());
                    order.push_back(e);
                    todo.pop_back();
                }
            }
            vector<mpq> weights;
            weights.resize(order.size(), mpq(0));
            if (root)
                weights[indices.at(root)] = coefficient;
            std::unordered_map<constraint_index, mpq> leaves;
            for (unsigned i = order.size(); i-- > 0;) {
                auto *r = get_recipe(order[i]);
                if (r->kind == rule::input)
                    leaves[r->input] += weights[i];
                else
                    for (auto const &p : r->premises)
                        weights[indices.at(p.evidence)] += weights[i] * p.coefficient;
            }
            for (auto const &[ci, c] : leaves)
                if (!c.is_zero())
                    result.push_back({ci, c});
            return true;
        }

        void reconstruct(ref root, proof_expression &result) const {
            result = proof_expression();
            snapshot_context(result);
            if (!root) {
                result.complete = false;
                return;
            }
            std::unordered_map<ref, unsigned> indices;
            ptr_vector<u_dependency> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                auto *e = todo.back();
                if (indices.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                auto *r = get_recipe(e);
                bool ready = true;
                if (r) {
                    for (auto const &p : r->premises)
                        if (!indices.contains(p.evidence)) {
                            todo.push_back(p.evidence);
                            ready = false;
                        }
                    if (r->assumption && !indices.contains(r->assumption)) {
                        todo.push_back(r->assumption);
                        ready = false;
                    }
                }
                if (!ready)
                    continue;
                proof_step step;
                if (r) {
                    step.kind = r->kind;
                    if (r->kind == rule::input && !r->has_fact)
                        step.kind = rule::unsupported;
                    step.conclusion = r->conclusion;
                    step.input = r->input;
                    step.id = r->id;
                    step.equation = r->equation;
                    step.pivot = r->pivot;
                    step.bounds = r->bounds;
                    step.definition = r->definition;
                    step.source = r->source;
                    step.divisor = r->divisor;
                    for (auto const &p : r->premises) {
                        step.premises.push_back(indices.at(p.evidence));
                        step.coefficients.push_back(p.coefficient);
                    }
                    if (r->assumption)
                        step.assumption = indices.at(r->assumption);
                }
                if (step.kind == rule::unsupported)
                    result.complete = false;
                indices.emplace(e, result.steps.size());
                result.steps.push_back(std::move(step));
                todo.pop_back();
            }
            result.root = indices.at(root);
        }
    };

}  // namespace lp
