/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_field_problem.cpp

Abstract:

    Shared field normalization, polynomial encoding, candidate evaluation and
    reconstruction. No frontend equality-engine or SAT state is stored.

--*/
#include "ast/ff/ff_field_problem.h"
#include "math/ff/ff_params.h"
#include "util/z3_exception.h"
#include "ast/simplifiers/rewriter_simplifier.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/simplifiers/ff_simplify.h"
#include "model/model.h"
#include "model/model_evaluator.h"
#include "util/stopwatch.h"

namespace ff {
    // Polynomial encodings of field terms, shared across final checks.
    // Encoding a term only depends on the term (and on the variable ids given
    // to foreign atoms), so it can be reused as long as the keys stay alive;
    // every key is pinned here. Not used with compact encodings, whose fresh
    // definitional variables belong to a single problem.
    struct ff_encoding_cache::imp {
        obj_map<expr, ff::polynomial> cache;
        obj_map<expr, unsigned> variable_ids;
        obj_map<expr, expr *> purified;
        unsigned num_variables = 0;
        expr_ref_vector pins;
        sort_ref field;
        imp(ast_manager &m, sort *s) : pins(m), field(s, m) {}
        void reset() {
            cache.reset();
            variable_ids.reset();
            purified.reset();
            num_variables = 0;
            pins.reset();
        }
    };


    struct field_problem::imp {
        ast_manager &m;
        ff_util ff;
        smt_params_helper options;
        ff::engine algebra;
        ff_encoding_cache::imp local;
        ff_encoding_cache::imp &enc;
        obj_map<expr, ff::polynomial> &cache;
        unsigned &num_variables;
        std::vector<ff::polynomial> eqs, neqs;
        expr_ref_vector premises, labels;
        std::vector<rational> values;
        bool checked = false, encoding = false;
        unsigned bit_facts = 0;
        stopwatch encode_time, solve_time, validate_time;
        lbool result = l_undef;
        struct constraint {
            expr *a, *b;
            bool equality;
        };
        std::vector<constraint> inputs;
        obj_map<expr, unsigned> &variable_ids;
        base_dependent_expr_state state;
        obj_map<expr, unsigned> premise_ids;
        std::set<unsigned> conflict;
        params_ref params;
        model_ref candidate;
        scoped_ptr<model_evaluator> evaluator;

        imp(ast_manager &m, sort *s, params_ref const &p, ff_encoding_cache::imp *shared)
            : m(m), ff(m), options(p), algebra(ff.modulus(s), m.limit(), options.ff_max_steps(),
                                   options.ff_max_terms(), options.ff_bit_propagation(),
                                   options.ff_batch(), options.ff_sparse_witness()),
              local(m, s), enc(shared && !options.ff_compact_encoding() ? *shared : local),
              cache(enc.cache), num_variables(enc.num_variables), premises(m), labels(m),
              variable_ids(enc.variable_ids), state(m), params(p) {
            ff::configure_engine(algebra, options);
        }

        expr *purify(expr *root) {
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw ff::exhausted();
                expr *e = todo.back();
                if (enc.purified.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                if (!is_app(e) || !ff.is_ff(e))
                    throw ff::exhausted();
                expr_ref result(m);
                if (!ff.is_interp(e)) {
                    // Foreign field terms are opaque to algebra. Give each a
                    // private constant so generic solve-eqs cannot rewrite their
                    // arguments or assign a UF/ITE declaration as a free variable.
                    // The frontend supplies interface equalities and checks the
                    // resulting field candidate against the other theories.
                    result = is_uninterp_const(e) ? e : m.mk_fresh_const("ff.leaf", e->get_sort());
                }
                else {
                    bool ready = true;
                    for (expr *arg : *to_app(e))
                        if (!enc.purified.contains(arg)) {
                            todo.push_back(arg);
                            ready = false;
                        }
                    if (!ready)
                        continue;
                    expr_ref_vector args(m);
                    for (expr *arg : *to_app(e))
                        args.push_back(enc.purified.find(arg));
                    result = m.mk_app(to_app(e)->get_decl(), args);
                }
                enc.purified.insert(e, result);
                enc.pins.push_back(e);
                enc.pins.push_back(result);
                todo.pop_back();
            }
            return enc.purified.find(root);
        }

        void dependencies(expr_dependency *dep, std::set<unsigned> &out) {
            ptr_vector<expr> leaves;
            m.linearize(dep, leaves);
            for (expr *leaf : leaves) {
                unsigned index;
                if (!premise_ids.find(leaf, index))
                    throw default_exception("unexpected finite-field preprocessing dependency");
                out.insert(index);
            }
        }

        void prepare() {
            for (unsigned i = 0; i < inputs.size(); ++i) {
                auto [a, b, equality] = inputs[i];
                expr *lhs = purify(a), *rhs = purify(b);
                expr_ref f(m.mk_eq(lhs, rhs), m);
                if (!equality)
                    f = m.mk_not(f);
                // Dependency leaves are labels, not formulas: solve-eqs freezes
                // symbols in dependency leaves. Keep the original signed atom
                // in premises, and use a fresh Boolean label for its index.
                expr_ref label(m.mk_fresh_const("ff.premise", m.mk_bool_sort()), m);
                labels.push_back(label);
                premise_ids.insert(label, i);
                state.add(dependent_expr(m, f, nullptr, m.mk_leaf(label)));
            }
            // Process the current assignment, not the original Boolean formula.
            // Standard simplifiers own substitution order, dependency propagation
            // and reconstruction of eliminated variables; no FF-local solve-eqs.
            // Inputs are a conjunction of assigned literals. There is no need
            // to search for definitions under Boolean contexts.
            params_ref preprocess_params(params);
            preprocess_params.set_bool("context_solve", false);
            rewriter_simplifier rewrite(m, preprocess_params, state);
            euf::solve_eqs solve(m, state);
            solve.updt_params(preprocess_params);
            rewrite.reduce();
            freeze_ff_domain_variables(m, state);
            solve.reduce();
            rewrite.reduce();
            if (m.limit().is_canceled())
                throw ff::exhausted();
            for (unsigned i = 0; i < state.qtail(); ++i) {
                auto const &d = state[i];
                if (m.is_false(d.fml())) {
                    dependencies(d.dep(), conflict);
                    result = l_false;
                    return;
                }
            }
            for (unsigned i = 0; i < state.qtail(); ++i) {
                if (!m.inc())
                    throw ff::exhausted();
                auto const &d = state[i];
                expr *f = d.fml(), *a, *b;
                if (m.is_true(f))
                    continue;
                bool equality = !m.is_not(f, f);
                if (!m.is_eq(f, a, b) || !ff.is_ff(a))
                    throw ff::exhausted();
                auto lhs = encode(a);
                auto rhs = encode(b);
                auto poly = algebra.add(std::move(lhs), rhs, rational(-1));
                dependencies(d.dep(), poly.dependencies);
                (equality ? eqs : neqs).push_back(std::move(poly));
            }
        }

        void reconstruct() {
            candidate = alloc(model, m);
            for (auto const &kv : variable_ids) {
                expr *var = &kv.get_key();
                candidate->register_decl(to_app(var)->get_decl(),
                    ff.mk_numeral(values[kv.get_value()], var->get_sort()));
            }
            model_converter_ref mc = state.model_trail().get_model_converter();
            if (mc)
                (*mc)(candidate);
            evaluator = alloc(model_evaluator, *candidate);
            evaluator->set_model_completion(true);
        }

        rational evaluate(expr *root) {
            expr_ref value(m);
            (*evaluator)(purify(root), value);
            rational number;
            if (!ff.is_numeral(value, number))
                throw ff::exhausted();
            return number;
        }

        ff::polynomial compact(ff::polynomial f, bool force = false) {
            if (!algebra.compact_encoding || f.empty()) return f;
            // Preserve affine packs for bit propagation. Introduce a wire only
            // for nonlinear growth, or before a product would exceed the bound.
            if (!force && (f.begin()->first.size() <= 1 || (f.size() <= 64 && f.begin()->first.size() <= 32))) return f;
            if (f.size() == 1 && f.begin()->first.size() <= 1) return f;
            // z=f is a definitional extension: each original assignment has
            // exactly one value of the fresh z. The equation needs no asserted
            // premise, and later conflicts still depend on the original facts.
            // Bound local expansion structurally, independent of field or input.
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
                    // A foreign application is an atomic field value. Its
                    // arguments and congruence belong to the other theories;
                    // the frontend supplies equalities from their classes.
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
                            // Definitional abstraction happens before the
                            // Cartesian product, not after a size exception.
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


    ff_encoding_cache::ff_encoding_cache(ast_manager &m, sort *s) : m_imp(std::make_unique<imp>(m, s)) {}
    ff_encoding_cache::~ff_encoding_cache() = default;
    unsigned ff_encoding_cache::size() const { return m_imp->cache.size() + m_imp->purified.size(); }
    void ff_encoding_cache::reset() { m_imp->reset(); }

    field_problem::field_problem(ast_manager &m, sort *s, params_ref const &p, ff_encoding_cache *cache, basis_cache *basis) {
        if (cache && (cache->m_imp->field != s || &cache->m_imp->pins.get_manager() != &m))
            throw default_exception("finite-field encoding cache belongs to a different manager or field");
        m_imp = std::make_unique<imp>(m, s, p, cache ? cache->m_imp.get() : nullptr);
        if (m_imp->options.ff_basis_cache())
            m_imp->algebra.set_basis_cache(basis);
    }
    field_problem::~field_problem() = default;
    void field_problem::add(expr *a, expr *b, bool equality) {
        if (m_imp->checked)
            throw default_exception("finite-field solver problem has already been checked");
        if (a->get_sort() != m_imp->local.field || b->get_sort() != m_imp->local.field)
            throw default_exception("finite-field solver constraint has the wrong field");
        m_imp->add(a, b, equality);
    }
    lbool field_problem::check() {
        if (m_imp->checked)
            throw default_exception("finite-field solver problem has already been checked");
        m_imp->checked = true;
        try {
            m_imp->encoding = true;
            scoped_watch watch(m_imp->encode_time);
            m_imp->prepare();
            if (m_imp->result != l_false)
                m_imp->bit_facts = m_imp->algebra.propagate_bits(m_imp->eqs);
            m_imp->encoding = false;
        }
        catch (rewriter_exception const &) {
            throw ff::exhausted();
        }
        if (m_imp->result == l_false)
            return l_false;
        m_imp->values.resize(m_imp->num_variables);
        lbool result;
        {
            scoped_watch watch(m_imp->solve_time);
            result = m_imp->algebra.solve(m_imp->eqs, m_imp->neqs, m_imp->values);
        }
        if (result == l_false)
            m_imp->conflict = m_imp->algebra.conflict();
        if (result == l_true) {
            scoped_watch watch(m_imp->validate_time);
            m_imp->reconstruct();
            // Definitions extend the residual model. Validate the original problem,
            // not only residual polynomials, before exposing any candidate values.
            for (auto [a, b, equality] : m_imp->inputs)
                if ((m_imp->evaluate(a) == m_imp->evaluate(b)) != equality)
                    return l_undef;
        }
        return m_imp->result = result;
    }
    rational field_problem::value(expr *term) {
        if (m_imp->result != l_true)
            throw default_exception("finite-field candidate is unavailable");
        if (term->get_sort() != m_imp->local.field)
            throw default_exception("finite-field candidate term has the wrong field");
        return m_imp->evaluate(term);
    }
    expr *field_problem::premise(unsigned index) const { return m_imp->premises.get(index); }
    std::set<unsigned> const &field_problem::conflict() const {
        SASSERT(m_imp->result == l_false);
        return m_imp->conflict;
    }
    void field_problem::collect_statistics(statistics &st) const {
        m_imp->algebra.collect_statistics(st);
        st.update("ff bit facts", m_imp->bit_facts);
        st.update("ff encode seconds", m_imp->encode_time.get_seconds());
        st.update("ff solve seconds", m_imp->solve_time.get_seconds());
        st.update("ff validate seconds", m_imp->validate_time.get_seconds());
    }
    bool field_problem::encoding_limit_hit() const {
        return m_imp->encoding && m_imp->algebra.polynomial_limit_hit();
    }
    unsigned field_problem::encoding_steps() const { return m_imp->algebra.steps(); }
} // namespace ff
