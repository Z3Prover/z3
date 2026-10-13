/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    theory_ff.cpp

Abstract:

    Theory solver for prime fields: ground combination with uninterpreted
    functions, arrays, and datatypes via modular algebra (Groebner bases),
    falling back to an exact bit-vector encoding when algebra is
    inconclusive. See theory_ff.h.

Author:

    Romain Soulat

--*/
#include "math/ff/ff_params.h"
#include "smt/theory_ff.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "model/ff_factory.h"
#include "math/ff/ff_polynomial.h"
#include "ast/ff/ff_solver.h"
#include "params/smt_params_helper.hpp"
#include <memory>

namespace smt {
    namespace {
        class ff_value_proc : public model_value_proc {
            ast_manager &m;
            sort_ref field;
            enode *encoded;

        public:
            ff_value_proc(ast_manager &m, sort *s, enode *n) : m(m), field(s, m), encoded(n) {}
            void get_dependencies(buffer<model_value_dependency> &out) override {
                out.push_back(model_value_dependency(encoded));
            }
            app *mk_value(model_generator &, expr_ref_vector const &values) override {
                rational n;
                unsigned width;
                VERIFY(bv_util(m).is_numeral(values.get(0), n, width));
                return ff_util(m).mk_numeral(n, field);
            }
        };
    }  // namespace

    theory_ff::theory_ff(context &ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("ff")), ff(m), bv(m), rw(m), operations(m, rw), helpers(m), root_norm_pins(m),
          model_values(m) {}

    theory_ff::~theory_ff() {}

    void theory_ff::ensure_helpers(sort *s) {
        if (wraps.contains(s))
            return;
        sort *encoded = bv.mk_sort(ff.width(s));
        func_decl *w = m.mk_fresh_func_decl("ff.encode", 1, &s, encoded);
        helpers.push_back(w);
        func_decl *u = m.mk_fresh_func_decl("ff.decode", 1, &encoded, s);
        helpers.push_back(u);
        wraps.insert(s, w);
        unwraps.insert(s, u);
        decoders.insert(u);
    }

    expr_ref theory_ff::wrap(expr *e) {
        // Decoder terms are only introduced as decode(encode(t)); avoid
        // recursively generating encode(decode(encode(...))).
        if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
            return expr_ref(to_app(e)->get_arg(0), m);
        ensure_helpers(e->get_sort());
        return expr_ref(m.mk_app(wraps.find(e->get_sort()), e), m);
    }

    void theory_ff::assert_axiom(expr *e, bool simplify) {
        expr_ref axiom(e, m);
        if (simplify)
            rw(axiom);
        if (!m.inc())
            throw default_exception(Z3_CANCELED_MSG);
        if (m.is_true(axiom))
            return;
        ctx.internalize(axiom, false);
        literal lit = ctx.get_literal(axiom);
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        ++axioms;
    }

    void theory_ff::constrain(expr *e) {
        if (m.proofs_enabled())
            throw default_exception("finite-field combination certificates are not supported in v1");
        if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
            return;
        if (constrained.contains(e))
            return;
        constrained.insert(e);
        sort *s = e->get_sort();
        expr_ref encoded = wrap(e);
        ctx.ensure_internalized(encoded);
        ctx.mark_as_relevant(ctx.get_enode(encoded));
        if (ff.modulus(s) != rational(2))
            assert_axiom(bv.mk_ult(encoded, bv.mk_numeral(ff.modulus(s), ff.width(s))));

        // encode(t)=encode(u) iff t=u by congruence; together with the range
        // bound this gives an injective canonical representation.
        expr_ref decoded(m.mk_app(unwraps.find(s), encoded), m);
        assert_axiom(m.mk_eq(decoded, e));

        if (!ff.is_interp(e))
            return;  // UF applications, array reads and datatype selectors.
        app *a = to_app(e);
        expr_ref_vector args(m);
        for (expr *arg : *a) args.push_back(wrap(arg));
        expr_ref value = operations.apply(a, args);
        assert_axiom(m.mk_eq(encoded, value));
    }

    bool theory_ff::internalize_term(app *e) {
        ctx.internalize(e->get_args(), e->get_num_args(), false);
        // Keep field operators out of the EUF congruence table (as arithmetic
        // internalizers do); foreign terms retain normal congruence closure.
        enode *n = ctx.e_internalized(e) ? ctx.get_enode(e) : ctx.mk_enode(e, false, false, false);
        apply_sort_cnstr(n, e->get_sort());
        return true;
    }

    void theory_ff::apply_sort_cnstr(enode *n, sort *) {
        if (!is_attached_to_var(n)) {
            ctx.attach_th_var(n, this, mk_var(n));
            if (bv_fields.contains(n->get_sort()) && !ctx.relevancy())
                constrain(n->get_expr());
        }
    }

    // Term ITEs (and other FF-sorted terms whose creation bypasses
    // apply_sort_cnstr, see context::internalize_term) can reach an equality
    // atom without ever owning a theory variable. Force one on both sides
    // here so new_eq_eh/new_diseq_eh still fire once this atom is (un)decided.
    void theory_ff::internalize_eq_eh(app *atom, bool_var) {
        expr *lhs = nullptr, *rhs = nullptr;
        VERIFY(m.is_eq(atom, lhs, rhs));
        apply_sort_cnstr(ctx.get_enode(lhs), lhs->get_sort());
        apply_sort_cnstr(ctx.get_enode(rhs), rhs->get_sort());
    }

    void theory_ff::new_eq_eh(theory_var v1, theory_var v2) {
        eqs.push_back({v1, v2});
        ctx.push_trail(push_back_vector<svector<std::pair<theory_var, theory_var>>>(eqs));
    }

    void theory_ff::new_diseq_eh(theory_var v1, theory_var v2) {
        diseqs.push_back({v1, v2});
        ctx.push_trail(push_back_vector<svector<std::pair<theory_var, theory_var>>>(diseqs));
    }   

    void theory_ff::relevant_eh(expr *e) {
        // Re-emit on relevancy propagation: axioms can be popped while the
        // term's enode remains internalized.
        if (ff.is_ff(e) && bv_fields.contains(e->get_sort()))
            constrain(e);
    }

    expr_ref theory_ff::square_root_term(expr *e) {
        expr_ref result = ff.square_root(e);
        if (result)
            rw(result);
        return result;
    }

    // Generalizes the literal top-level zero-product rule: flatten a-b into
    // monomials (coefficient x sorted atomic-factor multiset), then take the
    // multiset-intersection of every nonzero-coefficient monomial's factors
    // as a common factor. a-b = factor * remainder by construction (the
    // common multiset is a sub-multiset of every included monomial's
    // factors), so asserting factor=0 or remainder=0 is equivalent to a=b.
    // Count factor candidates even when splitting is disabled. Once a search
    // has emitted its split budget, skip the potentially expensive flattening
    // walk altogether; the candidate statistic then stops at that point.
    bool theory_ff::factor_split(expr *a, expr *b, expr_ref_vector &branches) {
        smt_params_helper params(ctx.get_params());
        if (params.ff_factor_split() && factor_split_clauses >= params.ff_max_factor_splits())
            return false;
        sort *s = a->get_sort();
        rational const &p = ff.modulus(s);
        vector<std::pair<rational, ptr_vector<expr>>> monomials;
        bool overflow = false;
        // Hard cap on total node visits, independent of the final monomial
        // count: shared sub-terms (e.g. from let-bound definitions) are
        // revisited once per occurrence, so a DAG with heavy internal sharing
        // could otherwise blow up this walk long before 200 monomials are
        // produced.
        unsigned steps = 0;
        const unsigned max_steps = 20000;
        auto flatten = [&](expr *root, rational sign) {
            ptr_vector<expr> todo_e;
            vector<rational> todo_s;
            todo_e.push_back(root);
            todo_s.push_back(sign);
            while (!todo_e.empty()) {
                if (overflow || monomials.size() > 200 || ++steps > max_steps) {
                    overflow = true;
                    return;
                }
                expr *e = todo_e.back();
                rational sg = todo_s.back();
                todo_e.pop_back();
                todo_s.pop_back();
                expr *x = nullptr;
                rational c;
                if (ff.is_add(e)) {
                    for (expr *arg : *to_app(e)) {
                        todo_e.push_back(arg);
                        todo_s.push_back(sg);
                    }
                }
                else if (ff.is_neg(e, x)) {
                    todo_e.push_back(x);
                    todo_s.push_back(-sg);
                }
                else if (ff.is_numeral(e, c)) {
                    rational coeff = (sg * c) % p;
                    if (coeff.is_neg())
                        coeff += p;
                    if (!coeff.is_zero())
                        monomials.push_back({coeff, ptr_vector<expr>()});
                }
                else {
                    ptr_vector<expr> factors;
                    rational coeff(1);
                    ptr_vector<expr> todo_f;
                    todo_f.push_back(e);
                    while (!todo_f.empty()) {
                        if (factors.size() > 8 || ++steps > max_steps) {
                            overflow = true;
                            return;
                        }
                        expr *f = todo_f.back();
                        todo_f.pop_back();
                        rational fc;
                        if (ff.is_mul(f)) {
                            for (expr *arg : *to_app(f))
                                todo_f.push_back(arg);
                        }
                        else if (ff.is_numeral(f, fc))
                            coeff *= fc;
                        else
                            factors.push_back(f);
                    }
                    std::sort(factors.begin(), factors.end(), [](expr *x, expr *y) { return x->get_id() < y->get_id(); });
                    coeff = (sg * coeff) % p;
                    if (coeff.is_neg())
                        coeff += p;
                    if (!coeff.is_zero())
                        monomials.push_back({coeff, factors});
                }
            }
        };
        flatten(a, rational(1));
        flatten(b, rational(-1));
        if (overflow || monomials.empty() || monomials.size() > 200)
            return false;
        ptr_vector<expr> common = monomials[0].second;
        for (unsigned i = 1; i < monomials.size() && !common.empty(); ++i) {
            ptr_vector<expr> const &factors = monomials[i].second;
            if (factors.empty()) {
                // A pure-constant monomial shares no factor with anything;
                // the running intersection collapses to empty, not "stale".
                common.reset();
                break;
            }
            ptr_vector<expr> remaining = factors, kept;
            for (expr *f : common) {
                auto it = std::find(remaining.begin(), remaining.end(), f);
                if (it != remaining.end()) {
                    kept.push_back(f);
                    remaining.erase(it);
                }
            }
            common = kept;
        }
        if (common.empty())
            return false;
        ++factor_split_candidates;
        TRACE(ff_root_split_miss,
              tout << "common factor " << mk_pp(common[0], m) << " in "
                   << mk_pp(a, m) << " = " << mk_pp(b, m) << "\n";);
        if (!params.ff_factor_split())
            return false;
        // Build factor = product(common) and remainder = sum over monomials
        // of coeff * product(factors with one copy of each common element
        // removed).
        auto build_term = [&](rational const &coeff, ptr_vector<expr> const &factors) -> expr_ref {
            expr_ref_vector args(m);
            if (!coeff.is_one() || factors.empty())
                args.push_back(ff.mk_numeral(coeff, s));
            for (expr *f : factors)
                args.push_back(f);
            return expr_ref(args.size() == 1 ? args.get(0) : ff.mk_mul(args), m);
        };
        expr_ref factor_expr(build_term(rational(1), common), m);
        expr_ref_vector remainder_terms(m);
        // The running intersection in `common` is a genuine sub-multiset of
        // every monomial's factors by construction; std::find should always
        // succeed. Guard anyway (bail out rather than erase end()) so a
        // future change to the intersection logic fails safe in Release
        // builds, where SASSERT is compiled out.
        for (auto &[coeff, factors] : monomials) {
            ptr_vector<expr> residual = factors;
            for (expr *f : common) {
                auto it = std::find(residual.begin(), residual.end(), f);
                if (it == residual.end())
                    return false;
                residual.erase(it);
            }
            remainder_terms.push_back(build_term(coeff, residual));
        }
        expr_ref remainder(m);
        remainder = remainder_terms.size() == 1 ? remainder_terms.get(0) : ff.mk_add(remainder_terms);
        expr_ref zero(ff.mk_numeral(rational(0), s), m);
        branches.push_back(m.mk_eq(factor_expr, zero));
        branches.push_back(m.mk_eq(remainder, zero));
        return true;
    }

    bool theory_ff::propagate_roots() {
        if (!smt_params_helper(ctx.get_params()).ff_root_split())
            return false;
        bool changed = false;
        // Optional: these valid clauses can substantially change SAT branching,
        // so keep the default conservative.
        bool boolean_split = smt_params_helper(ctx.get_params()).ff_boolean_split();
        // new_eq_eh only fires for relevant, merged (hence true) equalities;
        // snapshot the size so lemmas asserted here can't grow this pass.
        for (auto [v1, v2] : eqs) {
            if (!m.inc())
                return changed;
            expr *a = get_enode(v1)->get_expr(), *b = get_enode(v2)->get_expr();
            expr *ka = a, *kb = b;
            if (ka->get_id() > kb->get_id())
                std::swap(ka, kb);
            if (split_atoms.contains({ka, kb}))
                continue;
            auto square_of = [&](expr *square, expr *base) {
                expr *x = nullptr, *y = nullptr;
                return ff.is_mul(square, x, y) && x == base && y == base;
            };
            expr *digit = boolean_split ? (square_of(a, b) ? b : (square_of(b, a) ? a : nullptr)) : nullptr;
            // Avoid normalizing atoms whose operands aren't a syntactic square
            // or product; the complete algebra/fallback still sees any miss.
            if (!digit && (!ff.is_interp(a) || !ff.is_interp(b)))
                continue;
            split_atoms.insert({ka, kb});
            expr_ref atom_ref(m.mk_eq(a, b), m);
            expr *atom = atom_ref;
            // Rewriting an atom is pure; keep the result across backtracking.
            expr *cached = nullptr;
            expr_ref normalized(m);
            if (root_norm.find(atom, cached))
                normalized = cached;
            else {
                normalized = atom;
                rw(normalized);
                // Keep long incremental sessions bounded; rewriting is pure,
                // so eviction loses only reuse.
                if (root_norm_pins.size() >= 8192) {
                    root_norm.reset();
                    root_norm_pins.reset();
                }
                root_norm_pins.push_back(atom);
                root_norm_pins.push_back(normalized);
                root_norm.insert(atom, normalized);
            }
            if (!m.is_eq(normalized, a, b))
                continue;
            expr_ref_vector branches(m);
            bool factor_clause = false;
            rational c;
            if (!digit && ff.is_numeral(a, c) && c.is_zero())
                std::swap(a, b);
            if (digit) {
                // x*x=x iff x*(x-1)=0, so x=0 or x=1 in a field (no zero divisors).
                branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(0), digit->get_sort())));
                branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(1), digit->get_sort())));
            }
            else if (ff.is_numeral(b, c) && c.is_zero() && ff.is_mul(a) &&
                to_app(a)->get_num_args() <= 16) {
                // A field has no zero divisors: a product is zero iff some
                // factor is zero.
                for (expr *arg : *to_app(a))
                    if (!ff.is_numeral(arg))
                        branches.push_back(m.mk_eq(arg, b));
            }
            else {
                expr_ref lhs = square_root_term(a), rhs = square_root_term(b);
                if (!lhs || !rhs || (lhs == a && rhs == b)) {
                    if (!factor_split(a, b, branches))
                        continue;
                    factor_clause = true;
                }
                else {
                    // A^2=B^2 iff (A-B)*(A+B)=0, hence A=B or A=-B.
                    branches.push_back(m.mk_eq(lhs, rhs));
                    expr_ref neg(ff.mk_neg(rhs), m);
                    branches.push_back(m.mk_eq(lhs, neg));
                }
            }
            if (branches.empty())
                continue;
            expr_ref_vector clause(m);
            clause.push_back(m.mk_not(atom));
            expr_mark seen;
            bool satisfied = false;
            for (expr *branch : branches) {
                expr_ref root(branch, m);
                rw(root);
                if (m.is_true(root) || ctx.find_assignment(root) == l_true) {
                    satisfied = true;
                    break;
                }
                if (!m.is_false(root) && !seen.is_marked(root)) {
                    seen.mark(root);
                    clause.push_back(root);
                }
            }
            if (satisfied)
                continue;
            // Assert the original equality, not just the sampled roots.
            assert_axiom(m.mk_or(clause.size(), clause.data()), false);
            ++root_clauses;
            if (factor_clause)
                ++factor_split_clauses;
            changed = true;
        }
        return changed;
    }

    final_check_status theory_ff::check_native() {
        ++native_checks;
        native_values.reset();
        bool arranged = false;
        obj_map<sort, std::unique_ptr<ff::solver>> fields;
        obj_map<sort, ptr_vector<enode>> terms_by_sort;
        auto problem = [&](sort *s) -> ff::solver & {
            auto &p = fields.insert_if_not_there(s, std::unique_ptr<ff::solver>());
            if (!p)
            {
                auto &shared = encodings.insert_if_not_there(s, std::unique_ptr<ff::ff_encoding_cache>());
                if (!shared)
                    shared = std::make_unique<ff::ff_encoding_cache>(m, s);
                if (shared->size() > 200000)
                    shared->reset();
                p = std::make_unique<ff::solver>(m, s, ctx.get_params(), shared.get(), &memo);
            }
            return *p;
        };
        auto add = [&](sort *s, expr *a, expr *b, bool equality) {
            if (bv_fields.contains(s)) return;
            try { problem(s).add(a, b, equality); }
            catch (ff::exhausted const &) { bv_fields.insert(s); ++fallbacks; }
        };
        obj_hashtable<enode> model_terms;
        // Forward each relevant variable's equality to its current union-find
        // root (not just the pairs recorded by new_eq_eh/new_diseq_eh): this
        // surfaces ground simplifications - e.g. a variable merged to a
        // constant root - that the incremental eqs/diseqs log alone would
        // only pick up on a later call, which otherwise starves the Groebner
        // engine of resolved facts and causes it to exhaust its budget.
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            if (!ctx.is_relevant(n))
                continue;
            if (bv_fields.contains(n->get_sort()))
                continue;
            problem(n->get_sort());
            ptr_vector<enode> &terms = terms_by_sort.insert_if_not_there(n->get_sort(), ptr_vector<enode>());
            if (!model_terms.contains(n)) {
                model_terms.insert(n);
                terms.push_back(n);
            }
            enode *root = n->get_root();
            if (n != root && !bv_fields.contains(root->get_sort()))
                add(n->get_sort(), n->get_expr(), root->get_expr(), true);
        }

        for (auto [v1, v2] : diseqs) {
            enode *n1 = get_enode(v1), *n2 = get_enode(v2);
            if (bv_fields.contains(n1->get_sort()))
                continue;
            SASSERT(ctx.is_relevant(n1) && ctx.is_relevant(n2));
            add(n1->get_sort(), n1->get_expr(), n2->get_expr(), false);
        }

        for (auto &kv : fields) {
            sort *s = &kv.get_key();
            auto &pp = kv.m_value;
            if (bv_fields.contains(s)) continue;
            auto &p = *pp;
            try {
                lbool result = p.check();
                if (result == l_undef)
                    throw ff::exhausted();
                if (result == l_false) {
                    expr_ref_vector clause(m);
                    // These premises can't hold simultaneously, so their negated
                    // disjunction is field-valid; this is an explanation, not a
                    // v2 proof certificate.
                    for (unsigned d : p.conflict())
                        clause.push_back(m.mk_not(p.premise(d)));
                    // Preserve the exact SAT atoms; rewriting could produce an
                    // atom already assigned the opposite value, repeating this
                    // final check indefinitely.
                    assert_axiom(m.mk_or(clause), false);
                    ++native_conflicts;
                    return FC_CONTINUE;
                }
                std::map<rational, enode *> representatives;
                for (enode *n : terms_by_sort.insert_if_not_there(s, ptr_vector<enode>())) {
                    rational value = p.value(n->get_expr());
                    native_values.insert(n->get_expr(), value);
                    // Only roots shared with another theory need an arrangement;
                    // private terms are already checked by algebra, and arranging
                    // every wire would overwhelm linear DAG evaluation.
                    if (!ctx.is_shared(n))
                        continue;
                    auto [it, inserted] = representatives.emplace(value, n);
                    if (inserted || n->get_root() == it->second->get_root())
                        continue;
                    // Equal canonical values must agree in every other theory;
                    // ask SAT to choose the equality rather than asserting it.
                    if (ctx.assume_eq(n, it->second)) {
                        ++arrangements;
                        arranged = true;
                        continue;
                    }
                    // A previously assigned interface atom may already exclude
                    // this candidate; fall back rather than accept it.
                    throw ff::exhausted();
                }
            }
            catch (ff::exhausted const &) {
                // A local algebra limit shouldn't hide a conflict in another field.
                if (m.limit().is_canceled()) return FC_GIVEUP;
                bv_fields.insert(s);
                ++fallbacks;
            }
        }
        return arranged ? FC_CONTINUE : FC_DONE;
    }

    final_check_status theory_ff::final_check_eh(unsigned) {
        if (!get_num_vars())
            return FC_DONE;
        if (m.proofs_enabled())
            throw default_exception("finite-field combination certificates are not supported in v1");
        if (propagate_roots())
            return FC_CONTINUE;
        final_check_status status = check_native();
        if (status != FC_DONE) return status;
        if (!m.inc()) return FC_GIVEUP;
        if (!bv_fields.empty() && ctx.get_fparams().m_bv_mode == bv_solver_id::BS_NO_BV)
            return FC_GIVEUP;
        unsigned before = axioms;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            if (bv_fields.contains(n->get_sort()) && ctx.is_relevant(n))
                constrain(n->get_expr());
        }
        return axioms != before ? FC_CONTINUE : FC_DONE;
    }

    void theory_ff::refresh_bv_fields() {
        bv_fields.reset();
        // Decoder applications can survive a SAT backtrack; keep their entire
        // field encoded until those enodes disappear.
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr *e = get_enode(v)->get_expr();
            if (is_app(e) && decoders.contains(to_app(e)->get_decl()))
                bv_fields.insert(e->get_sort());
        }
    }

    void theory_ff::pop_scope_eh(unsigned n) {
        theory::pop_scope_eh(n);
        root_norm.reset();
        root_norm_pins.reset();
        refresh_bv_fields();
        native_values.reset();
        model_values.reset();
        // A term can survive a scope in which its defining axioms were emitted;
        // rebuild the emission cache so final_check repairs live definitions.
        constrained.reset();
        split_atoms.reset();
    }

    void theory_ff::reset_eh() {
        theory::reset_eh();
        encodings.reset();
        root_norm.reset();
        root_norm_pins.reset();
        memo.clear();
        native_values.reset();
        model_values.reset();
        constrained.reset();
        split_atoms.reset();
        bv_fields.reset();
        factor_split_clauses = 0;
    }

    void theory_ff::init_model(model_generator &mg) {
        model_values.reset();
        mg.register_factory(alloc(ff_factory, m));
        for (func_decl *f : helpers)
            mg.hide(f);
    }

    model_value_proc *theory_ff::mk_value(enode *n, model_generator &) {
        expr *e = n->get_expr();
        if (ff.is_numeral(e))
            return alloc(expr_wrapper_proc, to_app(e));
        if (!bv_fields.contains(e->get_sort())) {
            rational value;
            VERIFY(native_values.find(e, value));
            app *numeral = ff.mk_numeral(value, e->get_sort());
            model_values.push_back(numeral);
            return alloc(expr_wrapper_proc, numeral);
        }
        expr_ref encoded = wrap(e);
        SASSERT(ctx.e_internalized(encoded));
        return alloc(ff_value_proc, m, e->get_sort(), ctx.get_enode(encoded));
    }

    void theory_ff::finalize_model(model_generator &mg) {
        for (func_decl *f : helpers)
            mg.get_model().unregister_decl(f);
    }
}  // namespace smt
