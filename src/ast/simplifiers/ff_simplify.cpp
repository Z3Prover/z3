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
#include "ast/simplifiers/ff_domain_analysis.h"
#include "ast/ast_util.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "params/smt_params_helper.hpp"
#include "util/common_msgs.h"
#include <unordered_map>
#include <set>
#include <vector>

namespace {
    // cond(has_bits_probe, skip, solve-eqs): skip generic equality solving
    // when a formula looks like a Boolean domain candidate, for the same
    // reason ff_disjunctive_simplifier and ff_wire_simplifier preserve them.
    class ff_cond_solve_eqs_simplifier : public dependent_expr_simplifier {
        euf::solve_eqs m_solve_eqs;

        bool has_bits() {
            ff_domain_analysis domains(m);
            for (unsigned i : indices())
                if (domains.variable(m_fmls[i].fml()))
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
    ff_domain_analysis domains(m);
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
        if (domains.variable(eq))
            m_fmls.update(i, dependent_expr(m, eq, nullptr, m_fmls[i].dep()));
    }
}

// Recover a circuit zero-test from x*z=0 and z=1+c*x*u (c != 0).
// Both equations are retained. The derived definition removes the arbitrary
// inverse witness from z's dependencies, making duplicate tests congruent.
void ff_zero_test_simplifier::reduce() {
    ff_util ff(m);
    // Associativity changes grouping, not the multiset of factors. Do not
    // memoize this traversal: repeated factors must retain multiplicity.
    auto factors_of = [&](expr *e, ptr_vector<expr> &factors) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            if (!m.inc())
                throw rewriter_exception(Z3_CANCELED_MSG);
            expr *t = todo.back();
            todo.pop_back();
            if (ff.is_mul(t)) {
                for (expr *arg : *to_app(t))
                    todo.push_back(arg);
            }
            else
                factors.push_back(t);
        }
    };
    auto complement = [&](expr *e) -> expr * {
        // Recognize 1-z using -1=p-1. In characteristic two -z=z,
        // so 1+z is the same complement.
        expr *a = nullptr, *b = nullptr;
        if (!ff.is_add(e, a, b))
            return nullptr;
        rational c;
        if (!ff.is_numeral(a))
            std::swap(a, b);
        if (!ff.is_numeral(a, c) || !c.is_one())
            return nullptr;
        if (ff.modulus(e->get_sort()) == rational(2))
            return b;
        expr *v = nullptr;
        if (!ff.is_mul(b, a, v))
            return nullptr;
        if (!ff.is_numeral(a))
            std::swap(a, v);
        return ff.is_numeral(a, c) && c == ff.modulus(e->get_sort()) - rational(1) ? v : nullptr;
    };
    struct zero {
        expr_ref_vector factors;
        unsigned premise;
        bool nonzero;
        zero(ast_manager &m, unsigned i, bool nz) : factors(m), premise(i), nonzero(nz) {}
    };
    obj_map<expr, std::vector<zero>> zeros;
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
        ptr_vector<expr> factors;
        factors_of(a, factors);
        for (unsigned j = 0; j < factors.size(); ++j) {
            expr *z = factors[j];
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
            for (unsigned k = 0; k < factors.size(); ++k)
                if (k != j && !ff.is_numeral(factors[k]))
                    rec.factors.push_back(factors[k]);
            if (!rec.factors.empty())
                zeros.insert_if_not_there(z, std::vector<zero>()).push_back(std::move(rec));
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
        if (!zeros.contains(z))
            continue;
        for (auto const &rec : zeros.find(z)) {
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
            factors_of(term, factors);
            {
                ptr_vector<expr> non_numeral;
                for (expr *arg : factors)
                    if (!ff.is_numeral(arg))
                        non_numeral.push_back(arg);
                factors = non_numeral;
            }
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
    obj_map<expr, unsigned> ids;
    ptr_vector<expr> vars, defs;
    unsigned_vector defining_indices;
    std::set<expr *> bits;
    ff_domain_analysis domains(m);
    for (unsigned i : indices())
        if (expr *v = domains.variable(m_fmls[i].fml()))
            bits.insert(v);
    for (unsigned i : indices()) {
        if (!m.inc())
            return;
        expr *v = nullptr, *rhs = nullptr;
        if (!m.is_eq(m_fmls[i].fml(), v, rhs))
            continue;
        if (!is_uninterp_const(v))
            std::swap(v, rhs);
        // Keep one defining equality per variable; other equalities
        // remain constraints, so conflicting definitions cannot vanish.
        if (!is_uninterp_const(v) || !ff.is_ff(v) || bits.contains(v) || ids.contains(v) || occurs(v, rhs))
            continue;
        ids.insert(v, static_cast<unsigned>(vars.size()));
        vars.push_back(v);
        defs.push_back(rhs);
        defining_indices.push_back(i);
    }
    std::vector<std::vector<unsigned>> uses(vars.size());
    std::vector<unsigned> degree(vars.size(), 0), ready;
    for (unsigned i = 0; i < defs.size(); ++i) {
        expr_mark seen;
        ptr_vector<expr> todo;
        todo.push_back(defs[i]);
        while (!todo.empty()) {
            if (!m.inc())
                return;
            expr *e = todo.back();
            todo.pop_back();
            if (seen.is_marked(e))
                continue;
            seen.mark(e, true);
            if (!is_app(e))
                return;
            unsigned id;
            if (ids.find(e, id)) {
                uses[id].push_back(i);
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
    scoped_ptr<expr_substitution> subst = alloc(expr_substitution, m, true);
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    rp->set_substitution(subst.get());
    // Build the substitution bottom-up in dependency order, applying the
    // partial substitution built so far to each definition in turn, mirroring
    // euf::solve_eqs::normalize(). Because `order` only contains variables
    // whose definitions transitively depend on earlier entries, the fully
    // substituted definitions recomputed below coincide with what the final
    // substitution produces when later applied to every formula.
    th_rewriter rw(m);
    for (unsigned i : order) {
        if (!m.inc())
            return;
        expr_ref new_def(m), tmp(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        (*rp)(defs[i], new_def, new_pr, new_dep);
        // Normalize at each wire boundary, before another definition copies
        // the expanded DAG. This preserves the sharing and early cancellations
        // of the former tactic implementation.
        rw(new_def);
        new_dep = m.mk_join(new_dep, m_fmls[defining_indices[i]].dep());
        subst->insert(vars[i], new_def, new_dep);
        // The substitution has changed: cached rewrites of a newly defined
        // variable (or a containing term) must not survive this mutation.
        rp->reset();
    }
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
    m_eliminated += static_cast<unsigned>(order.size());
    m_fmls.model_trail().push(subst.detach(), {}, false);
}

void ff_wire_simplifier::collect_statistics(statistics &st) const {
    st.update("ff wire definitions", m_eliminated);
    st.update("ff wire seconds", m_elapsed.get_seconds());
}

ff_basic_simplifier::ff_basic_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s)
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

void ff_basic_simplifier::updt_params(params_ref const &p) {
    m_params.append(p);
    m_impl->updt_params(p);
}

void ff_basic_simplifier::collect_param_descrs(param_descrs &r) {
    m_impl->collect_param_descrs(r);
    r.insert("ff.disjunctive_bits", CPK_BOOL, "rewrite disjunctive Boolean field domains as polynomial equations", "true");
    r.insert("ff.preprocess", CPK_BOOL, "simplify field circuits before modular algebra", "true");
}

void ff_basic_simplifier::collect_statistics(statistics &st) const {
    m_impl->collect_statistics(st);
    st.update("ff preprocess seconds", m_elapsed.get_seconds());
    st.update("ff preprocess Boolean skips", m_boolean_skips);
}

void ff_basic_simplifier::reset_statistics() {
    m_elapsed.reset();
    m_boolean_skips = 0;
    m_impl->reset_statistics();
}

bool ff_basic_simplifier::skip_boolean_goal() {
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

void ff_basic_simplifier::reduce() {
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
