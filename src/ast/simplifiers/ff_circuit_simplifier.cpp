/*++
Copyright (c) 2026 Romain Soulat

Bounded arithmetic-to-Boolean circuit simplification. Each local identity is
proved by ITE case analysis, congruence and numerical field rewriting. Matching
never treats a wire name or an unasserted equation as evidence.
--*/
#include "ast/simplifiers/ff_simplify.h"
#include "ast/ff_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/th_rewriter.h"
#include <functional>

namespace {
// Shannon expansion of a finite-valued field atom. Memoization shares equal
// residual atoms: sums of bits have quadratically many residual sums, rather
// than one proof for every complete assignment. Every branch is exhaustive.
class atom_compiler {
    ast_manager& m;
    ff_util ff;
    th_rewriter rw;
    bool proofs;
    unsigned states = 0;
    obj_map<expr, expr*> memo;
    obj_map<expr, proof*> evidence;
    expr_ref_vector pins;
    proof_ref_vector proof_pins;

    bool selector(expr* root, expr_ref& condition) {
        ptr_vector<expr> todo;
        expr_mark seen;
        todo.push_back(root);
        unsigned nodes = 0;
        bool direct = m.is_eq(root) && ff.is_ff(to_app(root)->get_arg(0));
        if (direct) for (expr* arg : *to_app(root)) {
            expr *c, *a, *b;
            direct &= ff.is_numeral(arg) ||
                (m.is_ite(arg, c, a, b) && ff.is_numeral(a) && ff.is_numeral(b));
        }
        while (!todo.empty()) {
            if (!m.inc() || ++nodes > 2048) return false;
            expr* e = todo.back(); todo.pop_back();
            if (seen.is_marked(e)) continue;
            seen.mark(e, true);
            if (!is_app(e)) return false;
            if (ff.is_ff(e)) {
                expr *c, *a, *b;
                if (m.is_ite(e, c, a, b) && ff.is_numeral(a) && ff.is_numeral(b)) {
                    // Comparing numeric ITEs needs only their two selectors;
                    // expanding a compound condition here would undo sharing.
                    if (direct) {
                        if (!condition || c->get_id() < condition->get_id()) condition = c;
                        continue;
                    }
                    // Split underlying Boolean atoms, not a compound gate
                    // treated as a fresh independent selector. This retains
                    // correlations such as a AND b sharing the input a.
                    ptr_vector<expr> choices;
                    expr_mark visited;
                    choices.push_back(c);
                    while (!choices.empty()) {
                        if (!m.inc()) return false;
                        expr* q = choices.back(); choices.pop_back();
                        if (visited.is_marked(q)) continue;
                        visited.mark(q, true);
                        if (m.is_true(q) || m.is_false(q)) continue;
                        bool logical = is_app(q) && to_app(q)->get_family_id() == m.get_basic_family_id() &&
                            (m.is_not(q) || m.is_and(q) || m.is_or(q) || m.is_ite(q) ||
                             m.is_implies(q) || m.is_xor(q) || (m.is_eq(q) && m.is_bool(to_app(q)->get_arg(0))));
                        if (logical) for (expr* arg : *to_app(q)) choices.push_back(arg);
                        else if (!condition || q->get_id() < condition->get_id()) condition = q;
                    }
                    continue;
                }
                if (!(ff.is_numeral(e) || ff.is_add(e) || ff.is_mul(e) || ff.is_neg(e))) return false;
            }
            for (expr* a : *to_app(e)) todo.push_back(a);
        }
        return true;
    }

public:
    atom_compiler(ast_manager& m, bool proofs) : m(m), ff(m), rw(m), proofs(proofs), pins(m), proof_pins(m) {}
    bool compile(expr* source, expr_ref& target, proof_ref& pr, unsigned depth = 0) {
        expr* cached = nullptr;
        if (memo.find(source, cached)) { target = cached; pr = evidence[source]; return true; }
        if (++states > 256 || depth > 32 || !m.inc()) return false;
        expr_ref c(m);
        if (!selector(source, c)) return false;
        if (!c) { target = source; return true; }
        expr_ref_vector results(m);
        proof_ref_vector hypotheses(m), branch_proofs(m);
        for (unsigned value = 0; value < 2; ++value) {
            // Keep a syntactic NOT here: iff-false expects exactly not(c),
            // even if c is itself a negation. Its discharge must likewise
            // retain not(not(c)) when c is a disjunction.
            expr_ref assumption(value ? c.get() : m.mk_not(c), m);
            proof_ref h(proofs ? m.mk_hypothesis(assumption) : nullptr, m);
            expr_substitution sub(m, false, proofs);
            sub.insert(c, value ? m.mk_true() : m.mk_false(),
                proofs ? (value ? m.mk_iff_true(h) : m.mk_iff_false(h)) : nullptr);
            scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, proofs);
            replace->set_substitution(&sub);
            expr_ref replaced(m), reduced(m), result(m);
            proof_ref substitution(m), normalization(m), child(m);
            expr_dependency_ref dep(m);
            (*replace)(source, replaced, substitution, dep);
            rw(replaced, reduced, normalization);
            if (!compile(reduced, result, child, depth + 1)) return false;
            hypotheses.push_back(h);
            branch_proofs.push_back(m.mk_transitivity(substitution, normalization, child));
            results.push_back(result);
        }
        target = m.mk_ite(c, results.get(1), results.get(0));
        if (proofs) {
            expr_ref goal(m.mk_eq(source, target), m);
            proof_ref denied(m.mk_hypothesis(mk_not(m, goal)), m);
            proof_ref_vector sides(m);
            for (unsigned value = 0; value < 2; ++value) {
                proof* h = hypotheses.get(value);
                expr_substitution sub(m, false, true);
                sub.insert(c, value ? m.mk_true() : m.mk_false(), value ? m.mk_iff_true(h) : m.mk_iff_false(h));
                scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, true);
                replace->set_substitution(&sub);
                expr_ref replaced(m), reduced(m);
                proof_ref substitution(m), normalization(m);
                expr_dependency_ref dep(m);
                (*replace)(target, replaced, substitution, dep);
                rw(replaced, reduced, normalization);
                if (reduced != results.get(value)) return false;
                proof_ref reverse(m.mk_symmetry(m.mk_transitivity(substitution, normalization)), m);
                proof_ref equality(m.mk_transitivity(branch_proofs.get(value), reverse), m);
                if (!equality) equality = m.mk_reflexivity(source);
                proof_ref conflict(m.mk_unit_resolution({equality, denied}, m.mk_false()), m);
                expr_ref negated(m.mk_not(m.get_fact(h)), m);
                proof_ref lemma(m.mk_lemma(conflict, m.mk_or(negated, goal)), m);
                sides.push_back(m.mk_unit_resolution({lemma, denied}, negated));
            }
            proof_ref conflict(m.mk_unit_resolution(sides.size(), sides.data(), m.mk_false()), m);
            pr = m.mk_lemma(conflict, goal);
        }
        expr_ref normalized(m); proof_ref normalization(m);
        rw(target, normalized, normalization);
        pr = m.mk_transitivity(pr, normalization); target = normalized;
        pins.push_back(source); pins.push_back(target); proof_pins.push_back(pr);
        memo.insert(source, target); evidence.insert(source, pr);
        return true;
    }
};

class circuit_rewriter {
    ast_manager& m;
    ff_util ff;
    th_rewriter rw;
    bool proofs;
    unsigned work = 0;

    // Only three independent local selectors are expanded. Larger circuits
    // compose these small identities bottom-up, preserving shared ITE terms.
    bool selectors(expr* root, expr_ref_vector& conditions) {
        ptr_vector<expr> pending;
        expr_mark seen;
        pending.push_back(root);
        unsigned nodes = 0;
        while (!pending.empty()) {
            if (!m.inc() || ++work > 100000) return false;
            expr* e = pending.back(); pending.pop_back();
            if (seen.is_marked(e)) continue;
            seen.mark(e, true);
            if (++nodes > 32) return false;
            if (ff.is_numeral(e)) continue;
            expr *c, *a, *b;
            if (m.is_ite(e, c, a, b) && ff.is_numeral(a) && ff.is_numeral(b)) {
                if (!conditions.contains(c)) conditions.push_back(c);
                if (conditions.size() > 3) return false;
            }
            else if (ff.is_add(e) || ff.is_mul(e) || ff.is_neg(e))
                for (expr* arg : *to_app(e)) pending.push_back(arg);
            else return false;
        }
        return !conditions.empty();
    }

    // Substitute selector hypotheses with their iff-true/iff-false proofs.
    // Both sides then reduce numerically. All open assumptions are discharged
    // by ordinary lemma and unit-resolution steps, including the denied goal.
    proof_ref prove(expr* source, expr* target, expr_ref_vector const& cs) {
        expr_ref goal(m.mk_eq(source, target), m);
        proof_ref denied(m.mk_hypothesis(mk_not(m, goal)), m);
        proof_ref_vector hypotheses(m);
        std::function<proof_ref(unsigned)> visit = [&](unsigned depth) -> proof_ref {
            if (!m.inc()) return proof_ref(m);
            if (depth == cs.size()) {
                expr_substitution subst(m, false, true);
                for (unsigned i = 0; i < cs.size(); ++i) {
                    bool positive = m.get_fact(hypotheses.get(i)) == cs.get(i);
                    subst.insert(cs.get(i), positive ? m.mk_true() : m.mk_false(),
                        positive ? m.mk_iff_true(hypotheses.get(i)) : m.mk_iff_false(hypotheses.get(i)));
                }
                scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, true);
                replace->set_substitution(&subst);
                expr_ref l(m), r(m), ln(m), rn(m);
                proof_ref lp(m), rp(m), lr(m), rr(m);
                expr_dependency_ref dep(m);
                (*replace)(source, l, lp, dep); (*replace)(target, r, rp, dep);
                rw(l, ln, lr); rw(r, rn, rr);
                if (ln != rn) return proof_ref(m);
                lp = m.mk_transitivity(lp, lr);
                rp = m.mk_transitivity(rp, rr);
                proof_ref equality(m.mk_transitivity(lp, m.mk_symmetry(rp)), m);
                if (!equality) equality = m.mk_reflexivity(source);
                return proof_ref(m.mk_unit_resolution({equality, denied}, m.mk_false()), m);
            }
            proof_ref_vector sides(m);
            for (unsigned value = 0; value < 2; ++value) {
                expr_ref assumption(value ? cs[depth] : m.mk_not(cs[depth]), m);
                hypotheses.push_back(m.mk_hypothesis(assumption));
                proof_ref conflict = visit(depth + 1);
                hypotheses.pop_back();
                if (!conflict) return proof_ref(m);
                expr_ref_vector clause(m);
                for (proof* h : hypotheses) clause.push_back(m.mk_not(m.get_fact(h)));
                clause.push_back(m.mk_not(assumption)); clause.push_back(goal);
                proof_ref lemma(m.mk_lemma(conflict, mk_or(clause)), m);
                proof_ref_vector parents(m);
                parents.push_back(lemma); parents.append(hypotheses); parents.push_back(denied);
                sides.push_back(m.mk_unit_resolution(parents.size(), parents.data(), m.mk_not(assumption)));
            }
            return proof_ref(m.mk_unit_resolution(sides.size(), sides.data(), m.mk_false()), m);
        };
        proof_ref conflict = visit(0);
        return conflict ? proof_ref(m.mk_lemma(conflict, goal), m) : proof_ref(m);
    }

public:
    circuit_rewriter(ast_manager& m, bool proofs) : m(m), ff(m), rw(m), proofs(proofs) {}

    bool rewrite(expr* source, expr_ref& target, proof_ref& pr) {
        if (m.is_eq(source) && ff.is_ff(to_app(source)->get_arg(0))) {
            atom_compiler compiler(m, proofs);
            return compiler.compile(source, target, pr) && target != source;
        }
        if (!(ff.is_add(source) || ff.is_mul(source) || ff.is_neg(source))) return false;
        // N-ary products of bits are conjunctions. Compose binary four-case
        // proofs instead of enumerating all assignments to a wide product.
        ptr_vector<expr> factors, pending;
        if (ff.is_mul(source)) pending.push_back(source);
        while (!pending.empty() && factors.size() <= 64) {
            if (!m.inc()) return false;
            expr* e = pending.back(); pending.pop_back();
            if (ff.is_mul(e))
                for (unsigned i = to_app(e)->get_num_args(); i-- > 0;)
                    pending.push_back(to_app(e)->get_arg(i));
            else factors.push_back(e);
        }
        if (pending.empty() && factors.size() > 3 && factors.size() <= 64) {
            for (expr* a : factors) {
                expr *c, *t, *e; rational x, y;
                if (!m.is_ite(a, c, t, e) || !ff.is_numeral(t, x) || !ff.is_numeral(e, y) ||
                    (!x.is_zero() && !x.is_one()) || (!y.is_zero() && !y.is_one())) return false;
            }
            expr_ref original(factors[0], m), reduced(original, m);
            proof_ref prefix(m);
            for (unsigned i = 1; i < factors.size(); ++i) {
                expr* arg = factors[i];
                expr_ref old(ff.mk_mul(original, arg), m), next(ff.mk_mul(reduced, arg), m), out(m);
                proof_ref step(m), local(m);
                proof* parent = prefix;
                if (proofs && old != next) step = m.mk_congruence(to_app(old), to_app(next), 1, &parent);
                if (!rewrite(next, out, local)) return false;
                prefix = m.mk_transitivity(step, local);
                original = old; reduced = out;
            }
            target = reduced;
            if (proofs) {
                proof_ref association(m.mk_rewrite(source, original), m);
                pr = m.mk_transitivity(association, prefix);
            }
            return true;
        }
        expr_ref_vector cs(m);
        if (!selectors(source, cs)) return false;
        expr_ref_vector positive(m);
        for (unsigned assignment = 0; assignment < (1u << cs.size()); ++assignment) {
            expr_substitution subst(m);
            expr_ref_vector conjuncts(m);
            for (unsigned i = 0; i < cs.size(); ++i) {
                bool b = (assignment >> i) & 1;
                subst.insert(cs.get(i), b ? m.mk_true() : m.mk_false());
                conjuncts.push_back(b ? cs.get(i) : m.mk_not(cs.get(i)));
            }
            scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, false);
            replace->set_substitution(&subst);
            expr_ref value(source, m);
            (*replace)(value); rw(value);
            rational n;
            if (!ff.is_numeral(value, n) || (!n.is_zero() && !n.is_one())) return false;
            if (n.is_one()) positive.push_back(mk_and(conjuncts));
        }
        expr_ref condition(mk_or(positive), m);
        target = m.mk_ite(condition, ff.mk_numeral(rational(1), source->get_sort()),
                                   ff.mk_numeral(rational(0), source->get_sort()));
        if (proofs) {
            pr = prove(source, target, cs);
            if (!pr) return false;
        }
        // Simplify only after discharging the selector cases. Flattening a
        // compound selector beforehand would hide the substitution boundary.
        expr_ref normalized(m); proof_ref normalization(m);
        rw(target, normalized, normalization);
        pr = m.mk_transitivity(pr, normalization);
        target = normalized;
        return true;
    }
};
}

bool ff_simplify_circuit(ast_manager& m, expr* source, expr_ref& target, proof_ref& pr, bool proofs) {
    circuit_rewriter rewriter(m, proofs);
    return rewriter.rewrite(source, target, pr);
}

void ff_circuit_simplifier::reduce() {
    if (m_fmls.has_quantifiers()) return;
    circuit_rewriter rewriter(m, m_fmls.proofs_enabled());
    obj_map<expr, expr*> rewritten;
    obj_map<expr, proof*> evidence;
    expr_ref_vector pins(m);
    proof_ref_vector proof_pins(m);
    ptr_vector<expr> pending;
    for (unsigned i : indices()) {
        auto d = m_fmls[i];
        pending.push_back(d.fml());
        while (!pending.empty()) {
            if (!m.inc()) return;
            expr* e = pending.back();
            if (rewritten.contains(e)) { pending.pop_back(); continue; }
            if (!is_app(e)) return;
            bool ready = true;
            for (expr* a : *to_app(e))
                if (!rewritten.contains(a)) { pending.push_back(a); ready = false; }
            if (!ready) continue;
            expr_ref_vector args(m);
            proof_ref_vector parents(m);
            for (expr* a : *to_app(e)) {
                args.push_back(rewritten[a]);
                if (evidence[a]) parents.push_back(evidence[a]);
            }
            expr_ref next(m.mk_app(to_app(e)->get_decl(), args), m), result(m);
            proof_ref pr(m), local(m);
            if (m_fmls.proofs_enabled() && next != e)
                pr = m.mk_congruence(to_app(e), to_app(next), parents.size(), parents.data());
            if (rewriter.rewrite(next, result, local)) {
                pr = m.mk_transitivity(pr, local);
                next = result;
                ++m_rewritten;
            }
            pins.push_back(e); pins.push_back(next); proof_pins.push_back(pr);
            rewritten.insert(e, next); evidence.insert(e, pr);
            pending.pop_back();
        }
        if (rewritten[d.fml()] != d.fml())
            m_fmls.update(i, dependent_expr(m, rewritten[d.fml()],
                m.mk_modus_ponens(d.pr(), evidence[d.fml()]), d.dep()));
    }
}
