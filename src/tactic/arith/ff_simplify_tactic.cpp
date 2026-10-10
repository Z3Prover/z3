#include "tactic/arith/ff_solve_tactic.h"
#include "tactic/tactical.h"
#include "tactic/probe.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "ast/ff_decl_plugin.h"
#include "ast/converters/generic_model_converter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/occurs.h"
#include "ast/ast_util.h"
#include "util/stopwatch.h"
#include "params/smt_params_helper.hpp"
#include <unordered_map>
#include <set>
#include <map>
#include <vector>

namespace {
    // Preserve Boolean domain constraints, including both b*b=b and
    // b*(b-1)=0. Eliminating such a variable through a wide linear sum
    // would hide the domain from the algebraic bit-decomposition recognizer.
    // A nonzero univariate polynomial of degree <= 2 with roots 0 and 1
    // is a nonzero multiple of b*(b-1). This detector only computes an upper
    // degree bound and two samples: an identically zero polynomial may match
    // too. It is a preservation heuristic, never evidence that b is Boolean.
    expr *domain_variable(ast_manager &m, ff_util &ff, expr *f) {
        expr *a = nullptr, *b = nullptr;
        if (!m.is_eq(f, a, b) || !ff.is_ff(a))
            return nullptr;
        rational c;
        if ((is_uninterp_const(a) && ff.is_numeral(b, c)) || (is_uninterp_const(b) && ff.is_numeral(a, c)))
            return nullptr;
        expr *var = nullptr;
        ptr_vector<expr> todo;
        todo.push_back(a);
        todo.push_back(b);
        std::set<expr *> seen;
        while (!todo.empty()) {
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            expr *e = todo.back();
            todo.pop_back();
            if (!seen.insert(e).second)
                continue;
            if (!is_app(e))
                return nullptr;
            if (is_uninterp_const(e)) {
                if (var && var != e)
                    return nullptr;
                var = e;
            }
            for (expr *arg : *to_app(e))
                todo.push_back(arg);
        }
        if (!var)
            return nullptr;
        struct sample {
            unsigned degree = 0;
            rational zero{0}, one{0};
        };
        std::unordered_map<expr *, sample> values;
        todo.push_back(a);
        todo.push_back(b);
        rational const &p = ff.modulus(a->get_sort());
        while (!todo.empty()) {
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            expr *e = todo.back();
            if (values.contains(e)) {
                todo.pop_back();
                continue;
            }
            if (e == var) {
                values[e] = {1, rational(0), rational(1)};
                todo.pop_back();
                continue;
            }
            if (ff.is_numeral(e, c)) {
                values[e] = {0, c, c};
                todo.pop_back();
                continue;
            }
            if (!is_app(e) || to_app(e)->get_family_id() != ff.get_fid())
                return nullptr;
            bool ready = true;
            for (expr *arg : *to_app(e))
                if (!values.contains(arg)) {
                    todo.push_back(arg);
                    ready = false;
                }
            if (!ready)
                continue;
            auto kind = to_app(e)->get_decl_kind();
            if (kind != OP_FF_ADD && kind != OP_FF_MUL && kind != OP_FF_NEG)
                return nullptr;
            sample v;
            if (kind == OP_FF_MUL)
                v.zero = v.one = rational(1);
            for (expr *arg : *to_app(e)) {
                auto const &w = values.at(arg);
                if (kind == OP_FF_MUL) {
                    v.degree += w.degree;
                    v.zero *= w.zero;
                    v.one *= w.one;
                }
                else {
                    v.degree = std::max(v.degree, w.degree);
                    v.zero += w.zero;
                    v.one += w.one;
                }
                if (v.degree > 2)
                    return nullptr;
                v.zero = mod(v.zero, p);
                v.one = mod(v.one, p);
            }
            if (kind == OP_FF_NEG) {
                v.zero = mod(-v.zero, p);
                v.one = mod(-v.one, p);
            }
            values[e] = v;
            todo.pop_back();
        }
        auto const &lhs = values.at(a), &rhs = values.at(b);
        return std::max(lhs.degree, rhs.degree) == 2 && lhs.zero == rhs.zero && lhs.one == rhs.one ? var : nullptr;
    }
    class ff_disjunctive_tactic : public tactic {
        ast_manager &m;
        params_ref p;
    public:
        ff_disjunctive_tactic(ast_manager &m, params_ref const &p) : m(m), p(p) {}
        char const *name() const override { return "ff-disjunctive"; }
        tactic *translate(ast_manager &target) override { return alloc(ff_disjunctive_tactic, target, p); }
        void cleanup() override {}
        void updt_params(params_ref const &q) override { p.append(q); }
        void collect_param_descrs(param_descrs &ds) override {
            ds.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            if (g->proofs_enabled()) throw tactic_exception("QF_FF certificates are not supported in v1");
            if (smt_params_helper(p).ff_disjunctive_bits()) {
                ast_manager &m = g->m();
                ff_util ff(m);
                th_rewriter rw(m);
                for (unsigned i = 0; i < g->size(); ++i) {
                    expr *f = g->form(i), *a, *b, *c, *d;
                    if (!m.is_or(f) || to_app(f)->get_num_args() != 2 ||
                        !m.is_eq(to_app(f)->get_arg(0), a, b) || !m.is_eq(to_app(f)->get_arg(1), c, d) ||
                        !ff.is_ff(a) || a->get_sort() != c->get_sort())
                        continue;
                    expr_ref_vector args(m);
                    args.push_back(b);
                    expr_ref nb(ff.mk_app(OP_FF_NEG, 1, args.data()), m);
                    args.reset(); args.push_back(a); args.push_back(nb);
                    expr_ref lhs(ff.mk_app(OP_FF_ADD, 2, args.data()), m);
                    args.reset(); args.push_back(d);
                    expr_ref nd(ff.mk_app(OP_FF_NEG, 1, args.data()), m);
                    args.reset(); args.push_back(c); args.push_back(nd);
                    expr_ref rhs(ff.mk_app(OP_FF_ADD, 2, args.data()), m);
                    args.reset(); args.push_back(lhs); args.push_back(rhs);
                    expr_ref product(ff.mk_app(OP_FF_MUL, 2, args.data()), m);
                    expr_ref eq(m.mk_eq(product, ff.mk_numeral(rational(0), a->get_sort())), m);
                    rw(eq);
                    // In a field, uv=0 iff u=0 or v=0. This equivalence needs
                    // no division and retains the original assertion's support.
                    // Restrict its use to univariate candidate bit domains as a
                    // cost heuristic; the detector itself proves no Booleanity.
                    if (domain_variable(m, ff, eq))
                        g->update(i, eq, nullptr, g->dep(i));
                }
            }
            result.push_back(g.get());
        }
    };
    class has_bits_probe : public probe {
        result operator()(goal const &g) override {
            ff_util ff(g.m());
            for (unsigned i = 0; i < g.size(); ++i)
                if (domain_variable(g.m(), ff, g.form(i)))
                    return true;
            return false;
        }
    };
    // Normalize acyclic wire definitions once, bottom-up, with a shared cache.
    // This avoids repeatedly rewriting the expanded transitive definition of
    // every intermediate wire. Cyclic definitions stay for the general solver.
    // For x absent from t, (x=t and G(x)) is equisatisfiable with G(t): any
    // residual model extends by x:=t. The original definition is retained in
    // the model converter, not asserted after substitution. Acyclic dependency
    // order makes these extensions well-defined for a collection of wires.
    class ff_wire_tactic : public tactic {
        ast_manager &m;
        unsigned eliminated = 0;
        stopwatch elapsed;

    public:
        explicit ff_wire_tactic(ast_manager &m) : m(m) {}
        char const *name() const override {
            return "ff-wires";
        }
        tactic *translate(ast_manager &m) override {
            return alloc(ff_wire_tactic, m);
        }
        void cleanup() override {}
        void collect_statistics(statistics &st) const override {
            st.update("ff wire definitions", eliminated);
            st.update("ff wire seconds", elapsed.get_seconds());
        }
        void reset_statistics() override {
            eliminated = 0;
            elapsed.reset();
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            scoped_watch watch(elapsed);
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            ff_util ff(m);
            std::unordered_map<expr *, unsigned> ids;
            ptr_vector<expr> vars, defs;
            std::vector<unsigned> defining_forms;
            std::set<expr *> bits;
            for (unsigned i = 0; i < g->size(); ++i)
                if (expr *v = domain_variable(m, ff, g->form(i)))
                    bits.insert(v);
            expr_dependency_ref deps(m);
            for (unsigned i = 0; i < g->size(); ++i) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                if (has_quantifiers(g->form(i))) {
                    result.push_back(g.get());
                    return;
                }
                deps = m.mk_join(deps, g->dep(i));
                expr *v = nullptr, *rhs = nullptr;
                if (!m.is_eq(g->form(i), v, rhs))
                    continue;
                if (!is_uninterp_const(v))
                    std::swap(v, rhs);
                // Keep one defining equality per variable; other equalities
                // remain constraints, so conflicting definitions cannot vanish.
                if (!is_uninterp_const(v) || !ff.is_ff(v) || bits.contains(v) || ids.contains(v) || occurs(v, rhs))
                    continue;
                ids.emplace(v, vars.size());
                vars.push_back(v);
                defs.push_back(rhs);
                defining_forms.push_back(i);
            }
            std::vector<std::vector<unsigned>> uses(vars.size());
            std::vector<unsigned> degree(vars.size(), 0), ready;
            for (unsigned i = 0; i < defs.size(); ++i) {
                std::set<expr *> seen;
                ptr_vector<expr> todo;
                todo.push_back(defs[i]);
                while (!todo.empty()) {
                    if (!m.inc())
                        throw tactic_exception(m.limit().get_cancel_msg());
                    expr *e = todo.back();
                    todo.pop_back();
                    if (!seen.insert(e).second)
                        continue;
                    if (!is_app(e)) {
                        result.push_back(g.get());
                        return;
                    }
                    if (auto it = ids.find(e); it != ids.end()) {
                        uses[it->second].push_back(i);
                        ++degree[i];
                    }
                    for (expr *arg : *to_app(e))
                        todo.push_back(arg);
                }
                if (!degree[i])
                    ready.push_back(i);
            }
            std::vector<unsigned> order;
            // Only remove definitions reached by topological sorting. A cycle
            // (or a definition depending on it) has no justified free extension
            // and therefore remains among the residual constraints.
            for (unsigned pos = 0; pos < ready.size(); ++pos) {
                unsigned i = ready[pos];
                order.push_back(i);
                for (unsigned j : uses[i])
                    if (!--degree[j])
                        ready.push_back(j);
            }
            if (order.empty()) {
                result.push_back(g.get());
                return;
            }
            std::set<unsigned> removed;
            for (unsigned i : order)
                removed.insert(defining_forms[i]);
            auto finish = [&](goal_ref &out) {
                if (g->models_enabled()) {
                    generic_model_converter_ref mc = alloc(generic_model_converter, m, "ff-wires");
                    // This converter evaluates entries in reverse insertion
                    // order, so insert backwards to reconstruct inputs first.
                    for (auto it = order.rbegin(); it != order.rend(); ++it)
                        mc->add(vars[*it], defs[*it]);
                    out->add(mc.get());
                }
                eliminated += order.size();
                g->reset();
                g->copy_from(*out);
                g->inc_depth();
                result.push_back(g.get());
            };
            // A pure acyclic circuit imposes no restriction on its inputs.
            // Every free-input assignment extends uniquely along the DAG;
            // with no residual assertions the existential problem is SAT.
            // Keep the compact definitions for model construction; expanding
            // them symbolically would do work without simplifying any residual.
            if (removed.size() == g->size()) {
                goal_ref out = alloc(goal, *g, true);
                finish(out);
                return;
            }
            th_rewriter rw(m);
            std::unordered_map<expr *, expr *> cache;
            expr_ref_vector pins(m);
            auto normalize = [&](expr *root) -> expr * {
                ptr_vector<expr> todo;
                todo.push_back(root);
                while (!todo.empty()) {
                    if (!m.inc())
                        throw tactic_exception(m.limit().get_cancel_msg());
                    expr *e = todo.back();
                    if (cache.contains(e)) {
                        todo.pop_back();
                        continue;
                    }
                    if (!is_app(e)) {
                        pins.push_back(e);
                        cache[e] = e;
                        todo.pop_back();
                        continue;
                    }
                    bool done = true;
                    for (expr *arg : *to_app(e))
                        if (!cache.contains(arg)) {
                            todo.push_back(arg);
                            done = false;
                        }
                    if (!done)
                        continue;
                    expr_ref_vector args(m);
                    for (expr *arg : *to_app(e))
                        args.push_back(cache.at(arg));
                    expr_ref value = rw.mk_app(to_app(e)->get_decl(), args);
                    pins.push_back(value);
                    cache[e] = value;
                    todo.pop_back();
                }
                return cache.at(root);
            };
            for (unsigned i : order)
                cache[vars[i]] = normalize(defs[i]);
            // Congruence permits replacing equal subterms in every remaining
            // assertion. A rewritten assertion may depend on multiple removed
            // definitions; joining all input dependencies conservatively keeps
            // cores sound (it is provenance, not a reconstruction proof).
            goal_ref out = alloc(goal, *g, true);
            for (unsigned i = 0; i < g->size(); ++i) {
                if (removed.contains(i))
                    continue;
                expr *f = normalize(g->form(i));
                out->assert_expr(f, nullptr, f == g->form(i) ? g->dep(i) : deps.get());
            }
            finish(out);
        }
    };
    // Recover a circuit zero-test from x*z=0 and z=1+c*x*u (c != 0).
    // Both equations are retained. The derived definition removes the arbitrary
    // inverse witness from z's dependencies, making duplicate tests congruent.
    class ff_zero_test_tactic : public tactic {
        ast_manager &m;
        unsigned added = 0;

    public:
        explicit ff_zero_test_tactic(ast_manager &m) : m(m) {}
        char const *name() const override {
            return "ff-zero-test";
        }
        tactic *translate(ast_manager &m) override {
            return alloc(ff_zero_test_tactic, m);
        }
        void cleanup() override {}
        void collect_statistics(statistics &st) const override {
            st.update("ff zero tests", added);
        }
        void reset_statistics() override {
            added = 0;
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            ff_util ff(m);
            auto complement = [&](expr *e) -> expr * {
                // Recognize 1-z using -1=p-1. In characteristic two -z=z,
                // so 1+z is the same complement.
                if (!is_app_of(e, ff.get_fid(), OP_FF_ADD) || to_app(e)->get_num_args() != 2)
                    return nullptr;
                expr *a = to_app(e)->get_arg(0), *b = to_app(e)->get_arg(1);
                rational c;
                if (!ff.is_numeral(a, c))
                    std::swap(a, b);
                if (!ff.is_numeral(a, c) || !c.is_one())
                    return nullptr;
                if (ff.modulus(e->get_sort()) == rational(2))
                    return b;
                if (!is_app_of(b, ff.get_fid(), OP_FF_MUL) || to_app(b)->get_num_args() != 2)
                    return nullptr;
                a = to_app(b)->get_arg(0);
                expr *v = to_app(b)->get_arg(1);
                if (!ff.is_numeral(a, c))
                    std::swap(a, v);
                return ff.is_numeral(a, c) && c == ff.modulus(e->get_sort()) - rational(1) ? v : nullptr;
            };
            struct zero {
                expr_ref_vector factors;
                unsigned premise;
                bool nonzero;
                zero(ast_manager &m, unsigned i, bool nz) : factors(m), premise(i), nonzero(nz) {}
            };
            std::map<expr *, std::vector<zero>> zeros;
            for (unsigned i = 0; i < g->size(); ++i) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                expr *a = nullptr, *b = nullptr;
                rational c;
                if (!m.is_eq(g->form(i), a, b))
                    continue;
                if (ff.is_numeral(a, c) && c.is_zero())
                    std::swap(a, b);
                if (!ff.is_numeral(b, c) || !c.is_zero() || !is_app_of(a, ff.get_fid(), OP_FF_MUL))
                    continue;
                auto *mul = to_app(a);
                for (unsigned j = 0; j < mul->get_num_args(); ++j) {
                    expr *z = mul->get_arg(j);
                    bool nz = false;
                    if (!is_uninterp_const(z)) {
                        z = complement(z);
                        nz = true;
                    }
                    if (!z)
                        continue;
                    if (!is_uninterp_const(z))
                        continue;
                    zero rec(m, i, nz);
                    // The preceding simplify pass folds any zero coefficient
                    // away. Remaining numerical factors are nonzero units and
                    // may be dropped from an equation c*x*z=0 (or c*x*(1-z)=0).
                    for (unsigned k = 0; k < mul->get_num_args(); ++k)
                        if (k != j && !ff.is_numeral(mul->get_arg(k), c))
                            rec.factors.push_back(mul->get_arg(k));
                    if (!rec.factors.empty())
                        zeros[z].push_back(std::move(rec));
                }
            }
            goal_ref out = alloc(goal, *g, true);
            for (unsigned i = 0; i < g->size(); ++i) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                expr *z = nullptr, *rhs = nullptr;
                if (!m.is_eq(g->form(i), z, rhs))
                    continue;
                if (!is_uninterp_const(z))
                    std::swap(z, rhs);
                auto found = zeros.find(z);
                if (found == zeros.end())
                    continue;
                for (auto const &rec : found->second) {
                    rational constant(0), c;
                    expr *term = rhs;
                    bool valid = true;
                    if (!rec.nonzero) {
                        if (!is_app_of(rhs, ff.get_fid(), OP_FF_ADD))
                            continue;
                        term = nullptr;
                        for (expr *arg : *to_app(rhs)) {
                            if (ff.is_numeral(arg, c))
                                constant += c;
                            else if (term) {
                                valid = false;
                                break;
                            }
                            else
                                term = arg;
                        }
                        if (!valid || !constant.is_one() || !term)
                            continue;
                    }
                    ptr_vector<expr> factors;
                    if (is_app_of(term, ff.get_fid(), OP_FF_MUL)) {
                        for (expr *arg : *to_app(term))
                            if (!ff.is_numeral(arg, c))
                                factors.push_back(arg);
                    }
                    else
                        factors.push_back(term);
                    auto remaining = factors;
                    // Match a factorization term=c*x*u structurally, retaining
                    // multiplicities. This does not divide by symbolic x:
                    // the inference below explicitly includes the x=0 case.
                    bool divides = true;
                    for (expr *factor : rec.factors) {
                        unsigned k = 0;
                        while (k < remaining.size() && remaining[k] != factor)
                            ++k;
                        if (k == remaining.size()) {
                            divides = false;
                            break;
                        }
                        remaining[k] = remaining.back();
                        remaining.pop_back();
                    }
                    if (!divides)
                        continue;
                    expr_ref x(m);
                    if (rec.factors.size() == 1)
                        x = rec.factors.get(0);
                    else
                        x = ff.mk_app(OP_FF_MUL, rec.factors.size(), rec.factors.data());
                    expr_ref zero(ff.mk_numeral(rational(0), z->get_sort()), m);
                    expr_ref one(ff.mk_numeral(rational(1), z->get_sort()), m);
                    // Zero indicator: x*z=0 and z=1+c*x*u imply z=1 if
                    // x=0, by the second premise, and z=0 otherwise, by the
                    // first premise and the absence of zero divisors in F_p.
                    // Nonzero indicator: x*(1-z)=0 and z=c*x*u give z=0
                    // if x=0 and z=1 otherwise, by the same two-case argument.
                    // Both premises are needed, even when x is a product.
                    expr_ref def(m.mk_eq(z, rec.nonzero ? m.mk_ite(m.mk_eq(x, zero), zero, one)
                                                        : m.mk_ite(m.mk_eq(x, zero), one, zero)),
                                 m);
                    out->assert_expr(def, nullptr, m.mk_join(g->dep(i), g->dep(rec.premise)));
                    ++added;
                    break;
                }
            }
            // The derived indicator alone need not satisfy the witness equation
            // for u. Retain both original premises; adding their consequence is
            // equivalent, whereas replacing them by that consequence is not.
            for (unsigned i = 0; i < g->size(); ++i)
                out->assert_expr(g->form(i), nullptr, g->dep(i));
            g->reset();
            g->copy_from(*out);
            g->inc_depth();
            result.push_back(g.get());
        }
    };
    class ff_simplify_tactic : public tactic {
        params_ref p;
        tactic_ref impl;
        stopwatch elapsed;
        unsigned boolean_skips = 0;

    public:
        // propagate-values uses substitutivity: x=c permits G(x)->G(c).
        // The existing solve-eqs tactic performs equisatisfiable elimination
        // with its model converter. Skipping it for possible bit domains only
        // preserves useful syntax; all skipped constraints still reach solving.
        ff_simplify_tactic(ast_manager &m, params_ref const &p)
            : p(p), impl(and_then(and_then(mk_simplify_tactic(m, p), mk_propagate_values_tactic(m, p), alloc(ff_disjunctive_tactic, m, p)),
                                  alloc(ff_zero_test_tactic, m), alloc(ff_wire_tactic, m),
                                  cond(alloc(has_bits_probe), mk_skip_tactic(), mk_solve_eqs_tactic(m, p)),
                                  mk_simplify_tactic(m, p))) {}
        char const *name() const override {
            return "ff-simplify";
        }
        tactic *translate(ast_manager &m) override {
            return alloc(ff_simplify_tactic, m, p);
        }
        void cleanup() override {
            impl->cleanup();
        }
        void updt_params(params_ref const &q) override {
            p.append(q);
            impl->updt_params(q);
        }
        void collect_param_descrs(param_descrs &ds) override {
            impl->collect_param_descrs(ds);
            ds.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
            ds.insert("ff.preprocess", CPK_BOOL, "simplify field circuits before modular algebra", "true");
        }
        void collect_statistics(statistics &st) const override {
            impl->collect_statistics(st);
            st.update("ff preprocess seconds", elapsed.get_seconds());
            st.update("ff preprocess Boolean skips", boolean_skips);
        }
        void reset_statistics() override {
            elapsed.reset();
            boolean_skips = 0;
            impl->reset_statistics();
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            if (!p.get_bool("ff.preprocess", true)) {
                result.push_back(g.get());
                return;
            }
            scoped_watch watch(elapsed);
            // Preserve compact theory atoms for lazy Boolean search. Expanding
            // wire definitions across Boolean input choices can turn a small
            // branch-local polynomial into a large shared Boolean/field term.
            // The algebraic strategy still performs its own normalization.
            // This is a cost heuristic: returning the unchanged goal neither
            // assumes a Boolean assignment nor drops any field constraint.
            ptr_vector<expr> todo;
            std::set<expr *> seen;
            for (unsigned i = 0; i < g->size(); ++i)
                todo.push_back(g->form(i));
            while (!todo.empty()) {
                if (!g->m().inc())
                    throw tactic_exception(g->m().limit().get_cancel_msg());
                expr *e = todo.back();
                todo.pop_back();
                if (!seen.insert(e).second)
                    continue;
                if (!is_app(e) || (is_uninterp_const(e) && g->m().is_bool(e))) {
                    ++boolean_skips;
                    result.push_back(g.get());
                    return;
                }
                for (expr *arg : *to_app(e))
                    todo.push_back(arg);
            }
            (*impl)(g, result);
        }
    };
}  // namespace

tactic *mk_ff_simplify_tactic(ast_manager &m, params_ref const &p) {
    return alloc(ff_simplify_tactic, m, p);
}
