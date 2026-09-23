#include "tactic/arith/ff_solve_tactic.h"
#include "tactic/tactical.h"
#include "ast/ff_decl_plugin.h"
#include "ast/converters/model_converter.h"
#include "math/polynomial/ff_polynomial.h"
#include "model/model_evaluator.h"
#include "util/stopwatch.h"
#include <memory>
#include "params/smt_params_helper.hpp"
#include <unordered_map>
#include <set>

namespace {
    struct field_problem {
        ast_manager &m;
        ff_util ff;
        ff::engine algebra;
        expr_ref_vector variables;
        std::unordered_map<expr *, ff::polynomial> cache;
        std::vector<ff::polynomial> eqs, neqs;
        std::vector<expr_dependency *> dependencies;
        field_problem(ast_manager &m, sort *s, params_ref const &p)
            : m(m), ff(m),
              algebra(ff.modulus(s), m.limit(), p.get_uint("ff.max_steps", 2000000), p.get_uint("ff.max_terms", 4096), p.get_bool("ff.bit_propagation", true),
                                       smt_params_helper(p).ff_batch(), smt_params_helper(p).ff_sparse_witness()),
              variables(m) {
                algebra.linear_split = smt_params_helper(p).ff_linear_split();
                algebra.basis_bits = smt_params_helper(p).ff_basis_bits();
                algebra.compact_matrix = smt_params_helper(p).ff_compact_matrix();
                algebra.model_search = smt_params_helper(p).ff_model_search();
                algebra.root_completion = smt_params_helper(p).ff_root_completion();
                algebra.quotient_field = smt_params_helper(p).ff_quotient_field();
                algebra.bit_bounds = smt_params_helper(p).ff_bit_bounds();
                algebra.adaptive_reduction = smt_params_helper(p).ff_adaptive_reduction();
                algebra.adaptive_matrix = smt_params_helper(p).ff_adaptive_matrix();
                algebra.bounded_elimination = smt_params_helper(p).ff_bounded_elimination();
                algebra.sugar_pairs = smt_params_helper(p).ff_sugar_pairs();
                algebra.gm_pairs = smt_params_helper(p).ff_gm_pairs();
                algebra.div_masks = smt_params_helper(p).ff_div_masks();
                algebra.geobucket = smt_params_helper(p).ff_geobucket();
                algebra.small_coefficients = smt_params_helper(p).ff_small_coefficients();
                algebra.compact_encoding = smt_params_helper(p).ff_compact_encoding();

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
            unsigned v = variables.size();
            variables.push_back(nullptr);
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
                if (!is_app(e))
                    throw tactic_exception("ff-solve requires quantifier-free field terms");
                app *a = to_app(e);
                if (!ff.is_ff(e))
                    throw tactic_exception("ff-solve requires field terms");
                if (a->get_family_id() != ff.get_fid() && !is_uninterp_const(a))
                    throw tactic_exception("ff-solve: unsupported term; use ff2bv");
                bool ready = true;
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
                else if (is_uninterp_const(a)) {
                    f = algebra.variable(variables.size());
                    variables.push_back(a);
                }
                else {
                    switch (a->get_decl_kind()) {
                    case OP_FF_NEG: f = algebra.scale(cache.at(a->get_arg(0)), rational(-1)); break;
                    case OP_FF_ADD:
                    case OP_FF_MUL:
                    case OP_FF_BITSUM: {
                        bool mul = a->get_decl_kind() == OP_FF_MUL;
                        f = algebra.constant(rational(mul ? 1 : 0));
                        rational weight(1);
                        for (expr *arg : *a) {
                            auto const &b = cache.at(arg);
                            if (mul && algebra.compact_encoding && f.size() && b.size() > 256 / f.size()) {
                                // Definitional abstraction happens before the
                                // Cartesian product, not after a size exception.
                                f = compact(std::move(f), true);
                                auto operand = compact(b, true);
                                f = algebra.mul(f, operand);
                            }
                            else f = mul ? algebra.mul(f, b) : algebra.add(std::move(f), b, weight);
                            f = compact(std::move(f));
                            if (a->get_decl_kind() == OP_FF_BITSUM)
                                weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                        }
                        break;
                    }
                    default: throw tactic_exception("ff-solve: unsupported operator");
                    }
                }
                cache.emplace(e, std::move(f));
                todo.pop_back();
            }
            return cache.at(root);
        }
        void add(expr *a, expr *b, bool equality, expr_dependency *dep) {
            auto lhs = encode(a);  // copy: encoding b can rehash the cache
            auto rhs = encode(b);
            auto f = algebra.add(std::move(lhs), rhs, rational(-1));
            if (dep)
                f.dependencies.insert(dependencies.size());
            dependencies.push_back(dep);
            (equality ? eqs : neqs).push_back(std::move(f));
        }

        unsigned bit_facts = 0;
        void decompose_bitsums() {
            bit_facts = algebra.propagate_bits(eqs);
        }

    };
    class ff_solve_tactic : public tactic {
        ast_manager &m;
        params_ref p;
        statistics m_stats;
        bool m_encoding_size_failure = false;
        unsigned m_encoding_work = 0;
        stopwatch m_encode_time, m_solve_time, m_validate_time;

        // After wire elimination, a large circuit may have just a few bit
        // inputs left. Evaluate its shared DAG instead of expanding it into
        // high-degree polynomials. UNSAT requires exhaustive coverage and
        // explicit Booleanity for every free variable (except in F2).
        bool small_bits(goal const &g, model_ref &mdl, lbool &status) {
            ff_util ff(m);
            std::set<expr *> bits, seen;
            expr_ref_vector vars(m);
            ptr_vector<expr> todo;
            unsigned cap = std::min(p.get_uint("ff.enum_bits", 8), 12u);
            for (unsigned i = 0; i < g.size(); ++i) {
                expr *a = nullptr, *b = nullptr;
                if (m.is_eq(g.form(i), a, b)) {
                    // An asserted b*b=b means b*(b-1)=0, so the only roots
                    // are 0 and 1. This is an actual premise, unlike the
                    // preprocessing heuristic that merely protects likely bits.
                    auto is_square = [&](expr *v, expr *t) {
                        return is_uninterp_const(v) && is_app_of(t, ff.get_fid(), OP_FF_MUL) &&
                               to_app(t)->get_num_args() == 2 && to_app(t)->get_arg(0) == v &&
                               to_app(t)->get_arg(1) == v;
                    };
                    if (is_square(a, b))
                        bits.insert(a);
                    if (is_square(b, a))
                        bits.insert(b);
                }
                todo.push_back(g.form(i));
            }
            while (!todo.empty()) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                expr *e = todo.back();
                todo.pop_back();
                if (!seen.insert(e).second)
                    continue;
                if (!is_app(e))
                    return false;
                if (is_uninterp_const(e)) {
                    // F_2 already has exactly these two elements; in any larger
                    // field every enumerated variable needs its own bit premise.
                    if (!ff.is_ff(e) || (!bits.contains(e) && ff.modulus(e->get_sort()) != rational(2)))
                        return false;
                    vars.push_back(e);
                    if (vars.size() > cap)
                        return false;
                }
                else if (to_app(e)->get_family_id() != ff.get_fid() &&
                         to_app(e)->get_family_id() != m.get_basic_family_id())
                    return false;
                for (expr *arg : *to_app(e))
                    todo.push_back(arg);
            }
            if (vars.empty())
                return false;
            for (unsigned mask = 0; mask < (1u << vars.size()); ++mask) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                m_stats.update("ff bit assignments", 1u);
                mdl = alloc(model, m);
                for (unsigned j = 0; j < vars.size(); ++j)
                    mdl->register_decl(to_app(vars.get(j))->get_decl(),
                                       ff.mk_numeral(rational((mask >> j) & 1), vars[j]->get_sort()));
                model_evaluator eval(*mdl);
                bool ok = true;
                for (unsigned j = 0; j < g.size(); ++j) {
                    expr_ref value(m);
                    eval(g.form(j), value);
                    if (m.is_false(value)) {
                        ok = false;
                        break;
                    }
                    if (!m.is_true(value))
                        return false;
                }
                if (ok) {
                    status = l_true;
                    return true;
                }
            }
            // Every admissible assignment was refuted by a false assertion.
            // An unevaluated assertion returns above instead of counting as
            // false; only exhaustive, conclusive evaluation justifies UNSAT.
            status = l_false;
            return true;
        }

    public:
        ff_solve_tactic(ast_manager &m, params_ref const &p) : m(m), p(p) {}
        char const *name() const override {
            return "ff-solve";
        }
        tactic *translate(ast_manager &target) override {
            return alloc(ff_solve_tactic, target, p);
        }
        void cleanup() override {}
        void updt_params(params_ref const &q) override {
            p.append(q);
        }
        void collect_param_descrs(param_descrs &ds) override {
            ds.insert("ff.max_steps", CPK_UINT, "maximum modular algebra operations before exact BV fallback",
                      "2000000");
            ds.insert("ff.max_terms", CPK_UINT, "maximum terms in an expanded field polynomial", "4096");
            ds.insert("ff.bit_propagation", CPK_BOOL, "repeat no-wrap bit-sum propagation after algebraic elimination", "true");
            ds.insert("ff.batch", CPK_BOOL, "batch small-field critical pairs using sparse modular elimination", "true");
            ds.insert("ff.sparse_witness", CPK_BOOL, "try bounded univariate slices for underdetermined systems", "true");
            ds.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
            ds.insert("ff.linear_split", CPK_BOOL, "exchange bounded linear and nonlinear basis consequences before elimination", "false");
            ds.insert("ff.basis_bits", CPK_BOOL, "recover Boolean domains and digit equalities from basis consequences", "false");
            ds.insert("ff.compact_matrix", CPK_BOOL, "use packed sparse matrix rows and smaller critical-pair batches", "false");
            ds.insert("ff.model_search", CPK_BOOL, "derive bounded quotient minimal polynomials and diversify witness probes", "true");
            ds.insert("ff.root_completion", CPK_BOOL, "derive bounded quotient minimal polynomials without extra witness probes", "false");
            ds.insert("ff.quotient_field", CPK_BOOL, "adjoin bounded quotient reductions of finite-field Frobenius axioms", "false");
            ds.insert("ff.bit_bounds", CPK_BOOL, "propagate Boolean digits using no-wrap signed interval bounds", "true");
            ds.insert("ff.adaptive_reduction", CPK_BOOL, "fall back to scalar basis reduction when a matrix exceeds its storage budget", "false");
            ds.insert("ff.adaptive_matrix", CPK_BOOL, "allow more symbolic matrix reducers within a bounded storage allowance", "false");
            ds.insert("ff.bounded_elimination", CPK_BOOL, "retain nonlinear definitions when substitution predicts polynomial growth", "false");
            ds.insert("ff.sugar_pairs", CPK_BOOL, "rank critical pairs by propagated sugar degree in all field sizes", "false");
            ds.insert("ff.gm_pairs", CPK_BOOL, "install critical pairs using minimal lcm and strict chain criteria", "false");
            ds.insert("ff.div_masks", CPK_BOOL, "filter reducer divisibility tests using support masks", "false");
            ds.insert("ff.geobucket", CPK_BOOL, "accumulate scalar polynomial reductions in geometric buckets", "false");
            ds.insert("ff.small_coefficients", CPK_BOOL, "use exact machine arithmetic for small-field polynomial coefficients", "false");
            ds.insert("ff.compact_retry", CPK_BOOL, "retry the algebra tactic with compact definitions after an encoding size limit", "true");
            ds.insert("ff.compact_encoding", CPK_BOOL, "retain compact definitions when polynomial expansion would grow", "false");
            ds.insert("ff.enum_bits", CPK_UINT, "maximum residual bit inputs to enumerate (capped at 12)", "8");
        }
        void collect_statistics(statistics &st) const override {
            st.copy(m_stats);
            st.update("ff encode seconds", m_encode_time.get_seconds());
            st.update("ff solve seconds", m_solve_time.get_seconds());
            st.update("ff validate seconds", m_validate_time.get_seconds());
        }
        void reset_statistics() override {
            m_stats.reset();
            m_encode_time.reset();
            m_solve_time.reset();
            m_validate_time.reset();
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            try { solve_goal(g, result); }
            catch (tactic_exception const &) {
                if (!m_encoding_size_failure || !smt_params_helper(p).ff_compact_retry() ||
                    smt_params_helper(p).ff_compact_encoding() || m.limit().is_canceled() ||
                    m_encoding_work >= p.get_uint("ff.max_steps", 2000000)) throw;
                // A failed encoding has not changed the goal. Rebuild from its
                // original literals with exact fresh-variable definitions. Both
                // attempts remain charged to the shared cancellation/rlimit and
                // statistics. Subtract the largest per-field encoding spend
                // from the retry cap, so no field exceeds ff.max_steps in total.
                // This is a single retry, not a loop, and cannot bypass a timeout.
                params_ref saved(p);
                on_scope_exit restore([&]() { p.reset(); p.append(saved); });
                unsigned cap = p.get_uint("ff.max_steps", 2000000);
                // A representation retry is a speculative probe. Reserve most
                // of the work allowance for the established fallback strategies.
                // The fraction is independent of circuit, modulus and outcome.
                p.set_uint("ff.max_steps", std::min(cap - m_encoding_work, std::max(1u, cap / 16)));
                p.set_bool("ff.compact_encoding", true);
                m_stats.update("ff compact retries", 1u);
                solve_goal(g, result);
            }
        }
        void solve_goal(goal_ref const &g, goal_ref_buffer &result) {
            m_encoding_size_failure = false;
            m_encoding_work = 0;
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            ff_util ff(m);
            model_ref bit_model;
            lbool bit_status = l_undef;
            if (small_bits(*g, bit_model, bit_status)) {
                expr_dependency_ref deps(m);
                for (unsigned i = 0; i < g->size(); ++i)
                    deps = m.mk_join(deps, g->dep(i));
                g->reset();
                if (bit_status == l_false)
                    g->assert_expr(m.mk_false(), nullptr, deps);
                else if (g->models_enabled())
                    g->add(model2model_converter(bit_model.get()));
                g->inc_depth();
                result.push_back(g.get());
                return;
            }
            std::map<sort *, std::unique_ptr<field_problem>> fields;
            m_stats.update("ff algebra calls", 1u);
            // Retain work from unsuccessful alternatives and budget exhaustion.
            on_scope_exit collect([&]() {
                for (auto const &[s, q] : fields) {
                    q->algebra.collect_statistics(m_stats);
                    m_stats.update("ff bit facts", q->bit_facts);
                }
            });
            auto field = [&](sort *s) -> field_problem & {
                auto &q = fields[s];
                if (!q)
                    q = std::make_unique<field_problem>(m, s, p);
                return *q;
            };
            expr_dependency_ref deps(m), conflict(m);
            bool unsat = false, unknown = false;
            model_ref mdl = alloc(model, m);
            bool encoding = true;
            try {
                {
                    scoped_watch watch(m_encode_time);
                    for (unsigned i = 0; i < g->size(); ++i) {
                        deps = m.mk_join(deps, g->dep(i));
                        expr *f = g->form(i), *a = nullptr, *b = nullptr;
                        bool neg = m.is_not(f);
                        if (neg)
                            f = to_app(f)->get_arg(0);
                        if (m.is_true(f) || m.is_false(f)) {
                            unsat |= (m.is_false(f) != neg);
                            continue;
                        }
                        if (m.is_eq(f, a, b) && ff.is_ff(a))
                            field(a->get_sort()).add(a, b, !neg, g->dep(i));
                        else if (!neg && m.is_distinct(f) && ff.is_ff(to_app(f)->get_arg(0))) {
                            auto *d = to_app(f);
                            for (unsigned j = 0; j < d->get_num_args(); ++j)
                                for (unsigned k = 0; k < j; ++k)
                                    field(d->get_arg(j)->get_sort())
                                        .add(d->get_arg(j), d->get_arg(k), false, g->dep(i));
                        }
                        else
                            throw tactic_exception("ff-solve requires a conjunction of field literals");
                    }
                    for (auto &[s, q] : fields)
                        q->decompose_bitsums();
                }
                encoding = false;
                scoped_watch watch(m_solve_time);
                for (auto &[s, q] : fields) {
                    if (unsat)
                        break;
                    std::vector<rational> values(q->variables.size(), rational(0));
                    lbool status = q->algebra.solve(q->eqs, q->neqs, values);
                    unsat |= status == l_false;
                    if (status == l_false)
                        for (unsigned j : q->algebra.conflict())
                            conflict = m.mk_join(conflict, q->dependencies[j]);
                    unknown |= status == l_undef;
                    if (status == l_true)
                        for (unsigned i = 0; i < values.size(); ++i)
                            if (q->variables.get(i)) mdl->register_decl(to_app(q->variables.get(i))->get_decl(), ff.mk_numeral(values[i], s));
                }
            } catch (ff::exhausted const &) {
                if (encoding)
                    for (auto const &[s, q] : fields) {
                        m_encoding_size_failure |= q->algebra.polynomial_limit_hit();
                        m_encoding_work = std::max(m_encoding_work, q->algebra.steps());
                    }
                m_stats.update("ff budget exhausted", 1u);
                throw tactic_exception("ff-solve algebra budget exhausted");
            }
            if (!unsat && unknown)
                throw tactic_exception("ff-solve requires complete BV fallback");
            if (!unsat) {
                scoped_watch watch(m_validate_time);
                // Check the original AST too, independently of polynomial conversion.
                model_evaluator eval(*mdl);
                for (unsigned i = 0; i < g->size(); ++i) {
                    expr_ref value(m);
                    eval(g->form(i), value);
                    if (!m.is_true(value))
                        throw tactic_exception("ff-solve could not validate field model");
                }
            }
            goal_ref out = alloc(goal, *g, true);
            if (unsat)
                out->assert_expr(m.mk_false(), nullptr, conflict ? conflict.get() : deps.get());
            else if (g->models_enabled())
                out->add(model2model_converter(mdl.get()));
            g->reset_all();
            g->copy_from(*out);
            g->inc_depth();
            result.push_back(g.get());
        }
    };
}  // namespace
tactic *mk_ff_solve_tactic(ast_manager &m, params_ref const &p) {
    return alloc(ff_solve_tactic, m, p);
}
