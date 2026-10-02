/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_simplify.cpp

Abstract:

    Simplifiers for prime-field ("QF_FF") goals. See ff_simplify.h.

Author:

    Romain Soulat

--*/
#include "ast/simplifiers/ff_simplify.h"
#include "ast/simplifiers/rewriter_simplifier.h"
#include "ast/simplifiers/propagate_values.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/ff_decl_plugin.h"
#include "ast/expr_substitution.h"
#include "ast/occurs.h"
#include "ast/ast_util.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
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
        if ((!ff.is_interp(a) && ff.is_numeral(b, c)) || (!ff.is_interp(b) && ff.is_numeral(a, c)))
            return nullptr;
        expr *var = nullptr;
        ptr_vector<expr> todo;
        todo.push_back(a);
        todo.push_back(b);
        std::set<expr *> seen;
        while (!todo.empty()) {
            if (!m.inc())
                return nullptr;
            expr *e = todo.back();
            todo.pop_back();
            if (!seen.insert(e).second)
                continue;
            if (!is_app(e))
                return nullptr;
            if (!ff.is_interp(e)) {
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
                return nullptr;
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

    // cond(has_bits_probe, skip, solve-eqs): skip generic equality solving
    // when a formula looks like a Boolean domain candidate, for the same
    // reason ff_disjunctive_simplifier and ff_wire_simplifier preserve them.
    class ff_cond_solve_eqs_simplifier : public dependent_expr_simplifier {
        euf::solve_eqs m_solve_eqs;

        bool has_bits() {
            ff_util ff(m);
            for (unsigned i : indices())
                if (domain_variable(m, ff, m_fmls[i].fml()))
                    return true;
            return false;
        }

    public:
        ff_cond_solve_eqs_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s)
            : dependent_expr_simplifier(m, s), m_solve_eqs(m, s) {
            m_solve_eqs.updt_params(p);
        }
        char const *name() const override { return "ff-cond-solve-eqs"; }
        bool supports_proofs() const override { return true; }
        void reduce() override {
            if (!has_bits())
                m_solve_eqs.reduce();
        }
        void updt_params(params_ref const &p) override { m_solve_eqs.updt_params(p); }
        void collect_param_descrs(param_descrs &r) override { m_solve_eqs.collect_param_descrs(r); }
        void collect_statistics(statistics &st) const override { m_solve_eqs.collect_statistics(st); }
        void reset_statistics() override { m_solve_eqs.reset_statistics(); }
    };
}  // namespace

ff_disjunctive_simplifier::ff_disjunctive_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s)
    : dependent_expr_simplifier(m, s) {
    updt_params(p);
}

void ff_disjunctive_simplifier::updt_params(params_ref const &p) { m_params.append(p); }

void ff_disjunctive_simplifier::collect_param_descrs(param_descrs &r) {
    r.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
}

void ff_disjunctive_simplifier::reduce() {
    if (!smt_params_helper(m_params).ff_disjunctive_bits())
        return;
    ff_util ff(m);
    th_rewriter rw(m);
    for (unsigned i : indices()) {
        expr *f = m_fmls[i].fml(), *a, *b, *c, *d;
        if (!m.is_or(f) || to_app(f)->get_num_args() != 2 ||
            !m.is_eq(to_app(f)->get_arg(0), a, b) || !m.is_eq(to_app(f)->get_arg(1), c, d) ||
            !ff.is_ff(a) || a->get_sort() != c->get_sort())
            continue;
        expr_ref nb(ff.mk_neg(b), m);
        expr_ref lhs(ff.mk_add(a, nb), m);
        expr_ref nd(ff.mk_neg(d), m);
        expr_ref rhs(ff.mk_add(c, nd), m);
        expr_ref product(ff.mk_mul(lhs, rhs), m);
        expr_ref eq(m.mk_eq(product, ff.mk_numeral(rational(0), a->get_sort())), m);
        rw(eq);
        // In a field, uv=0 iff u=0 or v=0. This equivalence needs
        // no division and retains the original assertion's support.
        // Restrict its use to univariate candidate bit domains as a
        // cost heuristic; the detector itself proves no Booleanity.
        if (domain_variable(m, ff, eq))
            m_fmls.update(i, dependent_expr(m, eq, nullptr, m_fmls[i].dep()));
    }
}

// Recover a circuit zero-test from x*z=0 and z=1+c*x*u (c != 0).
// Both equations are retained. The derived definition removes the arbitrary
// inverse witness from z's dependencies, making duplicate tests congruent.
void ff_zero_test_simplifier::reduce() {
    ff_util ff(m);
    auto complement = [&](expr *e) -> expr * {
        // Recognize 1-z using -1=p-1. In characteristic two -z=z,
        // so 1+z is the same complement.
        if (!ff.is_add(e) || to_app(e)->get_num_args() != 2)
            return nullptr;
        expr *a = to_app(e)->get_arg(0), *b = to_app(e)->get_arg(1);
        rational c;
        if (!ff.is_numeral(a, c))
            std::swap(a, b);
        if (!ff.is_numeral(a, c) || !c.is_one())
            return nullptr;
        if (ff.modulus(e->get_sort()) == rational(2))
            return b;
        if (!ff.is_mul(b) || to_app(b)->get_num_args() != 2)
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
    for (unsigned i : indices()) {
        if (!m.inc())
            return;
        expr *a = nullptr, *b = nullptr;
        rational c;
        if (!m.is_eq(m_fmls[i].fml(), a, b))
            continue;
        if (ff.is_numeral(a, c) && c.is_zero())
            std::swap(a, b);
        if (!ff.is_numeral(b, c) || !c.is_zero() || !ff.is_mul(a))
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
    for (unsigned i : indices()) {
        if (!m.inc())
            return;
        expr *z = nullptr, *rhs = nullptr;
        if (!m.is_eq(m_fmls[i].fml(), z, rhs))
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
                if (!ff.is_add(rhs))
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
                if (!valid || !term || constant != rational(1))
                    continue;
            }
            ptr_vector<expr> factors;
            if (ff.is_mul(term)) {
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
                x = ff.mk_mul(rec.factors);
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
            m_fmls.add(dependent_expr(m, def, nullptr, m.mk_join(m_fmls[i].dep(), m_fmls[rec.premise].dep())));
            ++m_added;
            break;
        }
    }
}

void ff_zero_test_simplifier::collect_statistics(statistics &st) const { st.update("ff zero tests", m_added); }

// Normalize acyclic wire definitions once, bottom-up, with a shared
// substitution. This avoids repeatedly rewriting the expanded transitive
// definition of every intermediate wire. Cyclic definitions stay for the
// general solver. For x absent from t, (x=t and G(x)) is equisatisfiable
// with G(t): any residual model extends by x:=t. The substitution is
// recorded on the model reconstruction trail, not asserted after
// substitution. Acyclic dependency order makes these extensions
// well-defined for a collection of wires.
void ff_wire_simplifier::reduce() {
    scoped_watch watch(m_elapsed);
    if (m_fmls.has_quantifiers())
        return;
    ff_util ff(m);
    std::unordered_map<expr *, unsigned> ids;
    ptr_vector<expr> vars, defs;
    std::set<expr *> bits;
    for (unsigned i : indices())
        if (expr *v = domain_variable(m, ff, m_fmls[i].fml()))
            bits.insert(v);
    for (unsigned i : indices()) {
        if (!m.inc())
            return;
        expr *v = nullptr, *rhs = nullptr;
        if (!m.is_eq(m_fmls[i].fml(), v, rhs))
            continue;
        if (ff.is_interp(v))
            std::swap(v, rhs);
        // Keep one defining equality per variable; other equalities
        // remain constraints, so conflicting definitions cannot vanish.
        if (ff.is_interp(v) || !ff.is_ff(v) || bits.contains(v) || ids.contains(v) || occurs(v, rhs))
            continue;
        ids.emplace(v, vars.size());
        vars.push_back(v);
        defs.push_back(rhs);
    }
    std::vector<std::vector<unsigned>> uses(vars.size());
    std::vector<unsigned> degree(vars.size(), 0), ready;
    for (unsigned i = 0; i < defs.size(); ++i) {
        std::set<expr *> seen;
        ptr_vector<expr> todo;
        todo.push_back(defs[i]);
        while (!todo.empty()) {
            if (!m.inc())
                return;
            expr *e = todo.back();
            todo.pop_back();
            if (!seen.insert(e).second)
                continue;
            if (!is_app(e))
                return;
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
    // Only eliminate definitions reached by topological sorting. A cycle
    // (or a definition depending on it) has no justified free extension
    // and therefore remains among the residual constraints.
    for (unsigned pos = 0; pos < ready.size(); ++pos) {
        unsigned i = ready[pos];
        order.push_back(i);
        for (unsigned j : uses[i])
            if (!--degree[j])
                ready.push_back(j);
    }
    if (order.empty())
        return;
    scoped_ptr<expr_substitution> subst = alloc(expr_substitution, m);
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    rp->set_substitution(subst.get());
    // Build the substitution bottom-up in dependency order, applying the
    // partial substitution built so far to each definition in turn, mirroring
    // euf::solve_eqs::normalize(). Because `order` only contains variables
    // whose definitions transitively depend on earlier entries, the fully
    // substituted definitions recomputed below coincide with what the final
    // substitution produces when later applied to every formula.
    for (unsigned i : order) {
        if (!m.inc())
            return;
        expr_ref new_def(m), tmp(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        (*rp)(defs[i], new_def, new_pr, new_dep);
        subst->insert(vars[i], new_def);
    }
    th_rewriter rw(m);
    for (unsigned i : indices()) {
        if (!m.inc())
            return;
        auto d = m_fmls[i];
        expr_ref new_f(m), tmp(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        (*rp)(d.fml(), new_f, new_pr, new_dep);
        rw(new_f, tmp);
        if (tmp == d.fml())
            continue;
        new_dep = m.mk_join(d.dep(), new_dep);
        m_fmls.update(i, dependent_expr(m, tmp, nullptr, new_dep));
    }
    m_eliminated += order.size();
    m_fmls.model_trail().push(subst.detach(), {}, false);
}

void ff_wire_simplifier::collect_statistics(statistics &st) const {
    st.update("ff wire definitions", m_eliminated);
    st.update("ff wire seconds", m_elapsed.get_seconds());
}

ff_simplify_simplifier::ff_simplify_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s)
    : dependent_expr_simplifier(m, s) {
    // propagate-values uses substitutivity: x=c permits G(x)->G(c).
    // ff_cond_solve_eqs_simplifier performs equisatisfiable elimination
    // with its own model reconstruction trail entries. Skipping it for
    // possible bit domains only preserves useful syntax; all skipped
    // constraints still reach solving.
    m_impl = alloc(then_simplifier, m, p, s);
    m_impl->add_simplifier(alloc(rewriter_simplifier, m, p, s));
    m_impl->add_simplifier(alloc(propagate_values, m, p, s));
    m_impl->add_simplifier(alloc(ff_disjunctive_simplifier, m, p, s));
    m_impl->add_simplifier(alloc(ff_zero_test_simplifier, m, s));
    m_impl->add_simplifier(alloc(ff_wire_simplifier, m, s));
    m_impl->add_simplifier(alloc(ff_cond_solve_eqs_simplifier, m, p, s));
    m_impl->add_simplifier(alloc(rewriter_simplifier, m, p, s));
    updt_params(p);
}

void ff_simplify_simplifier::updt_params(params_ref const &p) {
    m_params.append(p);
    m_impl->updt_params(p);
}

void ff_simplify_simplifier::collect_param_descrs(param_descrs &r) {
    m_impl->collect_param_descrs(r);
    r.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
    r.insert("ff.preprocess", CPK_BOOL, "simplify field circuits before modular algebra", "true");
}

void ff_simplify_simplifier::collect_statistics(statistics &st) const {
    m_impl->collect_statistics(st);
    st.update("ff preprocess seconds", m_elapsed.get_seconds());
    st.update("ff preprocess Boolean skips", m_boolean_skips);
}

void ff_simplify_simplifier::reset_statistics() {
    m_elapsed.reset();
    m_boolean_skips = 0;
    m_impl->reset_statistics();
}

bool ff_simplify_simplifier::skip_boolean_goal() {
    // Preserve compact theory atoms for lazy Boolean search. Expanding
    // wire definitions across Boolean input choices can turn a small
    // branch-local polynomial into a large shared Boolean/field term.
    // The algebraic strategy still performs its own normalization.
    // This is a cost heuristic: returning the unchanged goal neither
    // assumes a Boolean assignment nor drops any field constraint.
    ptr_vector<expr> todo;
    std::set<expr *> seen;
    for (unsigned i : indices())
        todo.push_back(m_fmls[i].fml());
    while (!todo.empty()) {
        if (!m.inc())
            return true;
        expr *e = todo.back();
        todo.pop_back();
        if (!seen.insert(e).second)
            continue;
        if (!is_app(e) || (is_uninterp_const(e) && m.is_bool(e)))
            return true;
        for (expr *arg : *to_app(e))
            todo.push_back(arg);
    }
    return false;
}

void ff_simplify_simplifier::reduce() {
    if (m_fmls.proofs_enabled())
        throw rewriter_exception("QF_FF certificates are not supported in v1");
    if (!m_params.get_bool("ff.preprocess", true))
        return;
    scoped_watch watch(m_elapsed);
    if (skip_boolean_goal()) {
        ++m_boolean_skips;
        return;
    }
    m_impl->reduce();
}
