#include "smt/theory_ff.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "model/ff_factory.h"
#include "math/polynomial/ff_polynomial.h"
#include "params/smt_params_helper.hpp"
#include <unordered_map>
#include <memory>

namespace smt {
    namespace {
        struct field_problem {
            ast_manager &m;
            ff_util ff;
            ff::engine algebra;
            std::unordered_map<expr *, ff::polynomial> cache;
            unsigned num_variables = 0;
            std::vector<ff::polynomial> eqs, neqs;
            expr_ref_vector premises;
            ptr_vector<enode> terms;
            struct constraint {
                expr *a, *b;
                bool equality;
            };
            std::vector<constraint> inputs;
            std::unordered_map<expr *, expr *> normalized;
            std::unordered_map<expr *, std::set<unsigned>> normalization_deps;
            std::unordered_map<expr *, unsigned> variable_ids;
            std::unordered_map<expr *, rational> evaluated;
            expr_ref_vector pins;
            th_rewriter rw;

            field_problem(ast_manager &m, sort *s, params_ref const &p)
                : m(m), ff(m), algebra(ff.modulus(s), m.limit(), p.get_uint("ff.max_steps", 2000000),
                                       p.get_uint("ff.max_terms", 4096), p.get_bool("ff.bit_propagation", true),
                                       smt_params_helper(p).ff_batch(), smt_params_helper(p).ff_sparse_witness()),
                  premises(m), pins(m), rw(m) {
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
                    if (a->get_family_id() != ff.get_fid()) {
                        // Foreign applications are opaque to this field. The
                        // SMT arrangement, not this substitution, handles their
                        // arguments (which may belong to entirely other sorts).
                        normalized[e] = e;
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
                    auto &deps = normalization_deps[e];
                    for (expr *arg : *a) {
                        args.push_back(normalized.at(arg));
                        auto const &used = normalization_deps[arg];
                        deps.insert(used.begin(), used.end());
                    }
                    expr_ref value = rw.mk_app(a->get_decl(), args);
                    pins.push_back(value);
                    normalized[e] = value;
                    todo.pop_back();
                }
                return normalized.at(root);
            }

            void prepare() {
                std::unordered_map<expr *, unsigned> definitions;
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
                    definitions[a] = vars.size();
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
                        if (auto it = definitions.find(e); it != definitions.end()) {
                            uses[it->second].push_back(i);
                            ++degree[i];
                        }
                        if (to_app(e)->get_family_id() == ff.get_fid())
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
                    normalized[vars[i]] = normalize(defs[i]);
                    normalization_deps[vars[i]] = normalization_deps[defs[i]];
                    normalization_deps[vars[i]].insert(chosen[i]);
                    removed.insert(chosen[i]);
                }
                for (unsigned i = 0; i < inputs.size(); ++i) {
                    if (removed.contains(i))
                        continue;
                    auto [a, b, equality] = inputs[i];
                    expr *lhs_term = normalize(a), *rhs_term = normalize(b);
                    auto dependencies = normalization_deps[a];
                    auto const &rhs_deps = normalization_deps[b];
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
                    else if (a->get_family_id() != ff.get_fid()) {
                        auto it = variable_ids.find(e);
                        value = it == variable_ids.end() ? rational(0) : values[it->second];
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
                        bool mul = a->get_decl_kind() == OP_FF_MUL;
                        value = rational(mul ? 1 : 0);
                        rational weight(1);
                        for (expr *arg : *a) {
                            rational const &v = evaluated.at(arg);
                            value = mod(mul ? value * v : value + weight * v, ff.modulus(e->get_sort()));
                            if (a->get_decl_kind() == OP_FF_BITSUM)
                                weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                        }
                        if (a->get_decl_kind() == OP_FF_NEG)
                            value = mod(-value, ff.modulus(e->get_sort()));
                    }
                    evaluated[e] = value;
                    todo.pop_back();
                }
                return evaluated.at(root);
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
                    bool interpreted = a->get_family_id() == ff.get_fid();
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
                        variable_ids[e] = num_variables;
                        f = algebra.variable(num_variables++);
                    }
                    else if (a->get_decl_kind() == OP_FF_NEG)
                        f = algebra.scale(cache.at(a->get_arg(0)), rational(-1));
                    else {
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
                    }
                    cache.emplace(e, std::move(f));
                    todo.pop_back();
                }
                return cache.at(root);
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
        : theory(ctx, ctx.get_manager().mk_family_id("ff")), ff(m), bv(m), rw(m), helpers(m), model_values(m) {}

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

    expr_ref theory_ff::reduce(expr *e, sort *s, unsigned width) {
        // Widened arithmetic has no BV overflow. Remainder is in [0,p-1],
        // so dropping high bits afterwards preserves the canonical residue.
        expr_ref modulus(bv.mk_numeral(ff.modulus(s), width), m);
        expr_ref result(bv.mk_bv_urem(e, modulus), m);
        if (width != ff.width(s))
            result = bv.mk_extract(ff.width(s) - 1, 0, result);
        rw(result);
        return result;
    }

    expr_ref theory_ff::binary(expr *a, expr *b, sort *s, bool mul) {
        unsigned width = ff.width(s), wide = mul ? 2 * width : width + 1;
        expr_ref x(bv.mk_zero_extend(wide - width, a), m);
        expr_ref y(bv.mk_zero_extend(wide - width, b), m);
        expr_ref result(mul ? bv.mk_bv_mul(x, y) : bv.mk_bv_add(x, y), m);
        return reduce(result, s, wide);
    }

    void theory_ff::assert_axiom(expr *e, bool simplify) {
        expr_ref axiom(e, m);
        if (simplify)
            rw(axiom);
        if (m.limit().is_canceled())
            throw default_exception(m.limit().get_cancel_msg());
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

        if (!is_app(e) || to_app(e)->get_family_id() != get_id())
            return;  // UF applications, array reads and datatype selectors.
        app *a = to_app(e);
        expr_ref value(m);
        rational numeral;
        if (ff.is_numeral(e, numeral))
            value = bv.mk_numeral(numeral, ff.width(s));
        else if (a->get_decl_kind() == OP_FF_NEG) {
            expr_ref arg = wrap(a->get_arg(0));
            expr_ref wide(bv.mk_zero_extend(1, arg), m);
            expr_ref p(bv.mk_numeral(ff.modulus(s), ff.width(s) + 1), m);
            expr_ref neg(bv.mk_bv_sub(p, wide), m);
            // 0<=p-x<=p for canonical x; reduction also sends -0 to 0.
            value = reduce(neg, s, ff.width(s) + 1);
        }
        else if (a->get_decl_kind() == OP_FF_BITSUM) {
            // Horner's identity sum(2^i*x_i)=x_0+2*(x_1+2*(...)) holds
            // modulo p without any Booleanity or no-wrap assumption.
            value = wrap(a->get_arg(a->get_num_args() - 1));
            for (unsigned i = a->get_num_args() - 1; i-- > 0;) {
                value = binary(value, value, s, false);
                expr_ref arg = wrap(a->get_arg(i));
                value = binary(value, arg, s, false);
            }
        }
        else {
            SASSERT(a->get_decl_kind() == OP_FF_ADD || a->get_decl_kind() == OP_FF_MUL);
            value = wrap(a->get_arg(0));
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                expr_ref arg = wrap(a->get_arg(i));
                value = binary(value, arg, s, a->get_decl_kind() == OP_FF_MUL);
            }
        }
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
            if (bv_mode && !ctx.relevancy())
                constrain(n->get_expr());
        }
    }

    void theory_ff::relevant_eh(expr *e) {
        // Re-emit on relevancy propagation after backtracking: theory axioms
        // can be popped while the original term's enode remains internalized.
        if (bv_mode && ff.is_ff(e))
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
        if (!is_app_of(e, get_id(), OP_FF_MUL) || to_app(e)->get_num_args() > 16)
            return expr_ref(m);
        std::map<expr *, unsigned> powers;
        rational coefficient(1);
        for (expr *arg : *to_app(e)) {
            if (ff.is_numeral(arg, value))
                coefficient = mod(coefficient * value, ff.modulus(e->get_sort()));
            else
                ++powers[arg];
        }
        if (!coefficient.is_int_perfect_square(root))
            return expr_ref(m);
        expr_ref_vector factors(m);
        if (!root.is_one())
            factors.push_back(ff.mk_numeral(root, e->get_sort()));
        // Every symbolic factor must have even multiplicity. Halving these
        // multiplicities constructs A with e=A*A, without distributing products
        // of sums or assuming anything about the values of symbolic factors.
        for (auto const &[arg, power] : powers) {
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
            result = ff.mk_app(OP_FF_MUL, factors.size(), factors.data());
        rw(result);
        return result;
    }

    bool theory_ff::propagate_roots() {
        if (!ctx.get_params().get_bool("ff.root_split", true))
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
                return is_app_of(square, get_id(), OP_FF_MUL) &&
                       to_app(square)->get_num_args() == 2 &&
                       to_app(square)->get_arg(0) == base && to_app(square)->get_arg(1) == base;
            };
            expr *digit = boolean_split ? (square_of(a, b) ? b : (square_of(b, a) ? a : nullptr)) : nullptr;
            // Most circuit atoms are wire=expression. An opaque operand is not
            // a syntactic square or product, so avoid normalizing these atoms
            // just to discover that. This heuristic may miss a cancellation
            // exposing a square; the complete algebra/fallback still sees it.
            if (!digit && (!is_app(a) || !is_app(b) || to_app(a)->get_family_id() != get_id() ||
                to_app(b)->get_family_id() != get_id()))
                continue;
            split_atoms.insert(atom);
            expr_ref normalized(atom, m);
            rw(normalized);
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
            else if (ff.is_numeral(b, c) && c.is_zero() && is_app_of(a, get_id(), OP_FF_MUL) &&
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
                expr *arg = rhs;
                expr_ref neg(ff.mk_app(OP_FF_NEG, 1, &arg), m);
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
        std::map<sort *, std::unique_ptr<field_problem>> fields;
        auto problem = [&](sort *s) -> field_problem & {
            auto &p = fields[s];
            if (!p)
                p = std::make_unique<field_problem>(m, s, ctx.get_params());
            if (ctx.get_params().get_bool("ff.basis_cache", true))
                p->algebra.set_basis_cache(&memo);
            return *p;
        };
        obj_hashtable<enode> model_terms;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode *n = get_enode(v);
            enode *root = n->get_root();
            if (!ctx.is_relevant(n) && !ctx.is_relevant(root))
                continue;
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
                p.add(n->get_expr(), root->get_expr(), true);
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
                problem(a->get_sort()).add(a, b, value == l_true);
        }
        for (auto &[s, pp] : fields) {
            auto &p = *pp;
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
        return arranged ? FC_CONTINUE : FC_DONE;
    }

    final_check_status theory_ff::final_check_eh(unsigned) {
        if (!get_num_vars())
            return FC_DONE;
        if (m.proofs_enabled())
            throw default_exception("finite-field combination certificates are not supported in v1");
        if (!bv_mode) {
            if (propagate_roots())
                return FC_CONTINUE;
            try {
                return check_native();
            } catch (ff::exhausted const &) {
                if (!m.inc())
                    return FC_GIVEUP;
                // Keep the bridge enabled for the remainder of this context:
                // helper applications can outlive the SAT scope that created
                // them, and must not later be treated as free native variables.
                bv_mode = true;
                ++fallbacks;
                native_values.reset();
            }
        }
        unsigned before = axioms;
        for (unsigned v = 0; v < get_num_vars(); ++v)
            if (ctx.is_relevant(get_enode(v)))
                constrain(get_enode(v)->get_expr());
        return axioms != before ? FC_CONTINUE : FC_DONE;
    }

    void theory_ff::pop_scope_eh(unsigned n) {
        theory::pop_scope_eh(n);
        native_values.reset();
        model_values.reset();
        // A term can survive a scope in which its defining axioms were emitted.
        // Rebuild the emission cache, so final_check repairs all live definitions.
        constrained.reset();
        split_atoms.reset();
    }

    void theory_ff::reset_eh() {
        theory::reset_eh();
        memo.clear();
        native_values.reset();
        model_values.reset();
        constrained.reset();
        split_atoms.reset();
        bv_mode = false;
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
        if (!bv_mode) {
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
