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
#include "params/smt_params_helper.hpp"
#include <memory>

namespace smt {
    // Polynomial encodings of field terms, shared across final checks.
    // Encoding a term only depends on the term (and on the variable ids given
    // to foreign atoms), so it can be reused as long as the keys stay alive;
    // every key is pinned here. Not used with compact encodings, whose fresh
    // definitional variables belong to a single problem.
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

    namespace {
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
            ptr_vector<enode> terms;
            struct constraint {
                expr *a, *b;
                bool equality;
            };
            std::vector<constraint> inputs;
            obj_map<expr, expr *> normalized;
            obj_map<expr, std::set<unsigned>> normalization_deps;
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
                        // Foreign applications are opaque to this field. The
                        // SMT arrangement, not this substitution, handles their
                        // arguments (which may belong to entirely other sorts).
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
                    std::set<unsigned> deps;
                    for (expr *arg : *a) {
                        args.push_back(normalized.find(arg));
                        std::set<unsigned> const &used = normalization_deps.insert_if_not_there(arg, std::set<unsigned>());
                        deps.insert(used.begin(), used.end());
                    }
                    normalization_deps.insert(e, std::move(deps));
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
                // Acyclic x=t definitions admit a unique extension for x.
                // Substitute along the DAG without expanding its polynomials;
                // canonical rewriting can identify equivalent circuit outputs.
                // Cycles and competing definitions remain residual constraints.
                // Record the transitive support of each substitution. A
                // conflict needs only definitions actually used by its terms;
                // unrelated wire equalities must not weaken the learned clause.
                for (unsigned i : order) {
                    expr *value = normalize(defs[i]);
                    normalized.insert(vars[i], value);
                    std::set<unsigned> deps = normalization_deps.insert_if_not_there(defs[i], std::set<unsigned>());
                    deps.insert(chosen[i]);
                    normalization_deps.insert(vars[i], std::move(deps));
                    removed.insert(chosen[i]);
                }
                for (unsigned i = 0; i < inputs.size(); ++i) {
                    if (removed.contains(i))
                        continue;
                    auto [a, b, equality] = inputs[i];
                    expr *lhs_term = normalize(a), *rhs_term = normalize(b);
                    std::set<unsigned> dependencies = normalization_deps.insert_if_not_there(a, std::set<unsigned>());
                    std::set<unsigned> const &rhs_deps = normalization_deps.insert_if_not_there(b, std::set<unsigned>());
                    dependencies.insert(rhs_deps.begin(), rhs_deps.end());
                    a = lhs_term;
                    b = rhs_term;
                    // After justified substitution, t=t imposes no residual
                    // constraint. Do not duplicate the whole definition support
                    // on the many tautologies in a circuit equality class.
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
                    f.dependencies = dependencies;
                    f.dependencies.insert(i);
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
                        // equalities from their equality classes are added below.
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
        // Decoder terms are private and only introduced as decode(encode(t)).
        // Their representation is already bounded by t's range axiom. Avoid
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

        // encode is a function, hence t=u implies encode(t)=encode(u).
        // decode(encode(t))=t supplies the converse by congruence. Together
        // with the range bound this is an injective canonical representation,
        // including finite-domain cardinality. Ordinary stable-infiniteness
        // assumptions are not valid for fields and are not used here.
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
        // Field operators are interpreted through algebra or BV definitions. Keep
        // them out of the EUF congruence table (as arithmetic internalizers do);
        // congruent operands imply equal encodings, and decode then implies
        // equal field results. Foreign UF/array/datatype terms retain normal
        // congruence closure through their own internalizers.
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

    void theory_ff::relevant_eh(expr *e) {
        // Re-emit on relevancy propagation after backtracking: theory axioms
        // can be popped while the original term's enode remains internalized.
        if (ff.is_ff(e) && bv_fields.contains(e->get_sort()))
            constrain(e);
    }

    expr_ref theory_ff::square_root_term(expr *e) {
        rational value, root;
        if (ff.is_numeral(e, value)) {
            // An integer square representative is also a square modulo p.
            // Failure here is not a nonresidue test: leave other residues to
            // algebra. In particular, do not discard modular-only square roots.
            if (value.is_int_perfect_square(root))
                return expr_ref(ff.mk_numeral(root, e->get_sort()), m);
            return expr_ref(m);
        }
        if (!ff.is_mul(e) || to_app(e)->get_num_args() > 16)
            return expr_ref(m);
        obj_map<expr, unsigned> powers;
        rational coefficient(1);
        // Binary associative ASTs may hide repeated factors at different
        // depths. Flatten the product, retaining every occurrence: a visited
        // set would incorrectly turn x*x into x and invalidate the square test.
        ptr_vector<expr> pending;
        pending.push_back(e);
        unsigned factor_count = 0;
        while (!pending.empty()) {
            if (!m.inc())
                return expr_ref(m);
            expr *arg = pending.back();
            pending.pop_back();
            if (ff.is_mul(arg)) {
                for (expr *factor : *to_app(arg))
                    pending.push_back(factor);
            }
            else {
                if (++factor_count > 16)
                    return expr_ref(m);
                if (ff.is_numeral(arg, value))
                    coefficient = mod(coefficient * value, ff.modulus(e->get_sort()));
                else
                    ++powers.insert_if_not_there(arg, 0u);
            }
        }
        if (!coefficient.is_int_perfect_square(root))
            return expr_ref(m);
        expr_ref_vector factors(m);
        if (!root.is_one())
            factors.push_back(ff.mk_numeral(root, e->get_sort()));
        // Every symbolic factor must have even multiplicity. Halving these
        // multiplicities constructs A with e=A*A, without distributing products
        // of sums or assuming anything about the values of symbolic factors.
        for (auto const &kv : powers) {
            expr *arg = &kv.get_key();
            unsigned power = kv.get_value();
            if (power % 2)
                return expr_ref(m);
            for (unsigned i = 0; i < power / 2; ++i)
                factors.push_back(arg);
        }
        expr_ref result(m);
        if (factors.empty())
            result = ff.mk_numeral(rational(1), e->get_sort());
        else if (factors.size() == 1)
            result = factors.get(0);
        else
            result = ff.mk_mul(factors);
        rw(result);
        return result;
    }

    bool theory_ff::propagate_roots() {
        if (!smt_params_helper(ctx.get_params()).ff_root_split())
            return false;
        bool changed = false;
        // Optional: these valid clauses can substantially change SAT branching.
        // Keep the default conservative; caller-selected portfolios can enable them.
        bool boolean_split = smt_params_helper(ctx.get_params()).ff_boolean_split();
        // New branch atoms are considered at the next final check. Bounding
        // the snapshot and product arity keeps this pass from recursively
        // expanding a circuit or generating an unbounded SAT disjunction.
        unsigned end = ctx.get_num_b_internalized();
        for (unsigned i = 0; i < end; ++i) {
            if (!m.inc())
                return changed;
            expr *atom = ctx.get_b_internalized(i), *a, *b;
            if (!m.is_eq(atom, a, b) || !ff.is_ff(a) || !ctx.is_relevant(atom) || ctx.get_assignment(atom) != l_true ||
                split_atoms.contains(atom))
                continue;
            auto square_of = [&](expr *square, expr *base) {
                expr *x = nullptr, *y = nullptr;
                return ff.is_mul(square, x, y) && x == base && y == base;
            };
            expr *digit = boolean_split ? (square_of(a, b) ? b : (square_of(b, a) ? a : nullptr)) : nullptr;
            // Most circuit atoms are wire=expression. An opaque operand is not
            // a syntactic square or product, so avoid normalizing these atoms
            // just to discover that. This heuristic may miss a cancellation
            // exposing a square; the complete algebra/fallback still sees it.
            if (!digit && (!ff.is_interp(a) || !ff.is_interp(b)))
                continue;
            split_atoms.insert(atom);
            // Rewriting an atom is pure; keep the result across backtracking.
            expr *cached = nullptr;
            expr_ref normalized(m);
            if (root_norm.find(atom, cached))
                normalized = cached;
            else {
                normalized = atom;
                rw(normalized);
                // Keep long incremental sessions bounded, including scopes that
                // never pop. Rewriting is pure, so eviction loses only reuse.
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
                // x*x=x iff x*(x-1)=0. A field has no zero divisors, so
                // x=0 or x=1, including characteristic two. Expose this
                // finite domain to SAT for any field term x, not just wires.
                // The source equality remains the guard of the emitted clause.
                branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(0), digit->get_sort())));
                branches.push_back(m.mk_eq(digit, ff.mk_numeral(rational(1), digit->get_sort())));
            }
            else if (ff.is_numeral(b, c) && c.is_zero() && ff.is_mul(a) &&
                to_app(a)->get_num_args() <= 16) {
                // A field has no zero divisors: a product is zero iff some
                // factor is zero. Nonzero constant factors need no branch.
                for (expr *arg : *to_app(a))
                    if (!ff.is_numeral(arg))
                        branches.push_back(m.mk_eq(arg, b));
            }
            else {
                expr_ref lhs = square_root_term(a), rhs = square_root_term(b);
                if (!lhs || !rhs || (lhs == a && rhs == b))
                    continue;
                // A^2=B^2 iff (A-B)*(A+B)=0, hence A=B or A=-B.
                // No inverse of 2 is used. In characteristic two the branches
                // coincide and are deduplicated below; B=0 is likewise a unit.
                branches.push_back(m.mk_eq(lhs, rhs));
                expr_ref neg(ff.mk_neg(rhs), m);
                branches.push_back(m.mk_eq(lhs, neg));
            }
            if (branches.empty())
                continue;
            expr_ref_vector clause(m);
            clause.push_back(m.mk_not(atom));
            obj_hashtable<expr> seen;
            bool satisfied = false;
            for (expr *branch : branches) {
                expr_ref root(branch, m);
                rw(root);
                if (m.is_true(root) || ctx.find_assignment(root) == l_true) {
                    satisfied = true;
                    break;
                }
                if (!m.is_false(root) && !seen.contains(root)) {
                    seen.insert(root);
                    clause.push_back(root);
                }
            }
            if (satisfied)
                continue;
            // The original equality is the exact SAT premise, including when
            // recognition used its normalized form. Never assert sampled roots
            // as an exhaustive list or rewrite away this conditional guard.
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
        obj_map<sort, std::unique_ptr<field_problem>> fields;
        auto problem = [&](sort *s) -> field_problem & {
            auto &p = fields.insert_if_not_there(s, std::unique_ptr<field_problem>());
            if (!p)
            {
                auto &shared = encodings.insert_if_not_there(s, std::unique_ptr<ff_encoding_cache>());
                if (!shared)
                    shared = std::make_unique<ff_encoding_cache>(m);
                if (shared->cache.size() > 200000)
                    shared->reset();
                p = std::make_unique<field_problem>(m, s, ctx.get_params(), shared.get());
            }
            if (p->options.ff_basis_cache())
                p->algebra.set_basis_cache(&memo);
            return *p;
        };
        auto add = [&](sort *s, expr *a, expr *b, bool equality) {
            if (bv_fields.contains(s)) return;
            try { problem(s).add(a, b, equality); }
            catch (ff::exhausted const &) { bv_fields.insert(s); ++fallbacks; }
        };
        obj_hashtable<enode> model_terms;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            enode *root = n->get_root();
            if (!ctx.is_relevant(n) && !ctx.is_relevant(root))
                continue;
            if (bv_fields.contains(n->get_sort())) continue;
            auto &p = problem(n->get_sort());
            // Equality classes can inherit their field theory variable from a
            // non-root member. Model construction asks for the relevant root,
            // so record both values, even if only the root is marked relevant.
            // The retained equality premise justifies their common value.
            for (enode *term : {n, root})
                if (!model_terms.contains(term)) {
                    model_terms.insert(term);
                    p.terms.push_back(term);
                }
            if (n != root)
                add(n->get_sort(), n->get_expr(), root->get_expr(), true);
        }
        // Include assigned equality atoms, including interface decisions. An
        // equality-engine merge may have a foreign-theory justification; using
        // the equality itself as a premise yields a theory-valid conditional
        // lemma, which the SMT context resolves against that justification.
        for (unsigned i = 0; i < ctx.get_num_b_internalized(); ++i) {
            expr *e = ctx.get_b_internalized(i);
            expr *a, *b;
            if (!m.is_eq(e, a, b) || !ff.is_ff(a) || !ctx.is_relevant(e))
                continue;
            lbool value = ctx.get_assignment(e);
            if (value != l_undef)
                add(a->get_sort(), a, b, value == l_true);
        }
        for (auto &kv : fields) {
            sort *s = &kv.get_key();
            auto &pp = kv.m_value;
            if (bv_fields.contains(s)) continue;
            auto &p = *pp;
            try {
                p.prepare();
                std::vector<rational> values(p.num_variables);
                lbool result = p.algebra.solve(p.eqs, p.neqs, values);
                if (result == l_undef)
                    throw ff::exhausted();
                if (result == l_false) {
                    expr_ref_vector clause(m);
                    // Provenance follows every ideal operation and root branch.
                    // If these premises hold simultaneously, the polynomial system
                    // has no solution, so their negated disjunction is field-valid.
                    // This is a conflict explanation, not a v2 proof certificate.
                    for (unsigned d : p.algebra.conflict())
                        clause.push_back(m.mk_not(p.premises.get(d)));
                    // Preserve the exact SAT atoms. Algebraically rewriting an
                    // equality may create a different atom already assigned the
                    // opposite truth value, making the lemma satisfied instead of
                    // conflicting and repeating the same final check indefinitely.
                    assert_axiom(m.mk_or(clause.size(), clause.data()), false);
                    ++native_conflicts;
                    return FC_CONTINUE;
                }
                std::map<rational, enode *> representatives;
                // Check original inputs after DAG extension as well as the engine's
                // residual polynomial check. Sampling only supplies SAT witnesses.
                for (auto [a, b, equality] : p.inputs)
                    if ((p.evaluate(a, values) == p.evaluate(b, values)) != equality)
                        throw ff::exhausted();
                for (enode *n : p.terms) {
                    rational value = p.evaluate(n->get_expr(), values);
                    native_values.insert(n->get_expr(), value);
                    // Only roots observed by another theory need an arrangement.
                    // Private field terms may share a value without being merged;
                    // their equalities/disequalities are already checked by algebra.
                    // Arranging every intermediate circuit wire creates irrelevant
                    // SAT choices and can overwhelm otherwise linear DAG evaluation.
                    if (!ctx.is_shared(n))
                        continue;
                    auto [it, inserted] = representatives.emplace(value, n);
                    if (inserted || n->get_root() == it->second->get_root())
                        continue;
                    // Equal canonical values must agree in every other theory.
                    // Ask SAT to choose the equality, rather than asserting it as
                    // a consequence of one candidate model. Its false branch feeds
                    // a disequality into the next algebra check. Shared terms take
                    // their values from F_p itself, including finite cardinality;
                    // stable infiniteness is not assumed. One representative per
                    // value suffices by transitivity.
                    if (ctx.assume_eq(n, it->second)) {
                        ++arrangements;
                        arranged = true;
                        continue;
                    }
                    // A rewritten/previously assigned interface atom may already
                    // exclude this candidate without having appeared above. Falling
                    // back is conservative; never accept incompatible field models.
                    throw ff::exhausted();
                }
            }
            catch (ff::exhausted const &) {
                // A local algebra limit is not a reason to miss an immediate
                // conflict in another field. Shared cancellation is still global.
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
        // Decoder applications can survive a SAT backtrack. Keep their entire
        // field encoded until those enodes disappear; never expose them as free
        // algebraic variables. A user pop can remove the last such bridge.
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
        // A term can survive a scope in which its defining axioms were emitted.
        // Rebuild the emission cache, so final_check repairs all live definitions.
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
