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
                if (!lhs || !rhs || (lhs == a && rhs == b))
                    continue;
                // A^2=B^2 iff (A-B)*(A+B)=0, hence A=B or A=-B.
                branches.push_back(m.mk_eq(lhs, rhs));
                expr_ref neg(ff.mk_neg(rhs), m);
                branches.push_back(m.mk_eq(lhs, neg));
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
        // NSB review: this was previous updated to use eqs and diseqs instead of 
        // reproducing equalities from the E-graph.
        // Accessing get_num_b_internalized and get_assigment is not following
        // the conventions assumed for theory solvers to receive the solver state based
        // on the assign_eh, new_eq_eh and new_diseq_eh callbacks.

#if 0
        // NSB: can we do this instead?
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
        }

        for (auto [v1, v2] : eqs) {
            enode *n1 = get_enode(v1), *n2 = get_enode(v2);
            if (bv_fields.contains(n1->get_sort()))
                continue;
            SASSERT(ctx.is_relevant(n1) && ctx.is_relevant(n2));
            add(n1->get_sort(), n1->get_expr(), n2->get_expr(), true);
        }

        for (auto [v1, v2] : diseqs) {
            enode *n1 = get_enode(v1), *n2 = get_enode(v2);
            if (bv_fields.contains(n1->get_sort()))
                continue;
            SASSERT(ctx.is_relevant(n1) && ctx.is_relevant(n2));
            add(n1->get_sort(), n1->get_expr(), n2->get_expr(), false);
        }

#else

        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            enode *root = n->get_root();
            if (!ctx.is_relevant(n) && !ctx.is_relevant(root))
                continue;
            if (bv_fields.contains(n->get_sort())) 
                continue;
            problem(n->get_sort());
            ptr_vector<enode> &terms = terms_by_sort.insert_if_not_there(n->get_sort(), ptr_vector<enode>());
            // Record both the term and its root since either may be relevant.
            for (enode *term : {n, root})
                if (!model_terms.contains(term)) {
                    model_terms.insert(term);
                    terms.push_back(term);
                }
            // A class root may inherit its field variable from another member.
            if (n != root)
                add(n->get_sort(), n->get_expr(), root->get_expr(), true);
        }
        // Term ITEs need not own a field theory variable, so equality callbacks
        // alone miss their selected-branch equalities. Retain the assigned atoms
        // as premises, including disequalities chosen by the SAT search.

        // NSB code review: the above comment doesnt make sense.
        // The code below just looks for equality atoms that get assigned to true or false.
        // The new_eq_eh and new_diseq_eh callbacks should be used for this.
        for (unsigned i = 0; i < ctx.get_num_b_internalized(); ++i) {
            expr *e = ctx.get_b_internalized(i);
            expr *a, *b;
            if (!m.is_eq(e, a, b) || !ff.is_ff(a) || !ctx.is_relevant(e))
                continue;
            lbool value = ctx.get_assignment(e);
            if (value != l_undef)
                add(a->get_sort(), a, b, value == l_true);
        }
#endif
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
