/*++
Copyright (c) 2026 Romain Soulat
--*/
#include "ast/ff/ff_evidence.h"
#include "ast/ff_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "math/ff/ff_certificate.h"
#include "math/ff/ff_params.h"

namespace ff {
    // A bounded propositional truth table discharges Boolean rearrangements
    // that are valid but do not share a rewriter normal form. Non-Boolean
    // equalities remain independent atoms, so this cannot assume field facts.
    // This is exhaustive checking, not a call back into the SMT solver.
    bool check_boolean_tautology(ast_manager& m, expr* formula) {
        ptr_vector<expr> pending, order;
        obj_map<expr, unsigned> indices, atoms;
        auto connective = [&](expr* e) {
            if (!is_app(e) || to_app(e)->get_family_id() != m.get_basic_family_id()) return false;
            auto* a = to_app(e);
            switch (a->get_decl_kind()) {
            case OP_TRUE: case OP_FALSE: case OP_NOT: case OP_AND: case OP_OR:
            case OP_IMPLIES: case OP_XOR: case OP_ITE: return true;
            case OP_EQ: return m.is_bool(a->get_arg(0));
            default: return false;
            }
        };
        pending.push_back(formula);
        while (!pending.empty()) {
            if (!m.inc() || order.size() >= 10000) return false;
            expr* e = pending.back();
            if (indices.contains(e)) { pending.pop_back(); continue; }
            if (connective(e)) {
                bool ready = true;
                for (expr* arg : *to_app(e))
                    if (!indices.contains(arg)) { pending.push_back(arg); ready = false; }
                if (!ready) continue;
            }
            else {
                if (atoms.size() >= 12) return false;
                atoms.insert(e, atoms.size());
            }
            indices.insert(e, order.size()); order.push_back(e); pending.pop_back();
        }
        svector<bool> values;
        values.resize(order.size(), false);
        for (unsigned assignment = 0; assignment < (1u << atoms.size()); ++assignment) {
            if (!m.inc()) return false;
            for (unsigned i = 0; i < order.size(); ++i) {
                expr* e = order[i];
                unsigned atom;
                if (atoms.find(e, atom)) { values[i] = (assignment >> atom) & 1; continue; }
                auto* a = to_app(e);
                auto v = [&](unsigned j) { return values[indices[a->get_arg(j)]]; };
                bool result = false;
                switch (a->get_decl_kind()) {
                case OP_TRUE: result = true; break;
                case OP_FALSE: break;
                case OP_NOT: result = !v(0); break;
                case OP_EQ: result = v(0) == v(1); break;
                case OP_XOR: result = v(0) != v(1); break;
                case OP_IMPLIES: result = !v(0) || v(1); break;
                case OP_ITE: result = v(0) ? v(1) : v(2); break;
                case OP_AND:
                    result = true;
                    for (unsigned j = 0; j < a->get_num_args(); ++j) result &= v(j);
                    break;
                case OP_OR:
                    for (unsigned j = 0; j < a->get_num_args(); ++j) result |= v(j);
                    break;
                default: return false;
                }
                values[i] = result;
            }
            if (!values.back()) return false;
        }
        return true;
    }

    // Replay a ring identity or an equality scaled by a nonzero field unit.
    // This performs polynomial normalization only: no ideal computation,
    // root search or assumption about an opaque field term is permitted.
    bool check_polynomial_rewrite(ast_manager& m, expr* formula) {
        ff_util ff(m);
        expr *a, *b, *c = nullptr, *d = nullptr;
        if (!m.is_eq(formula, a, b)) return false;
        bool relation = m.is_bool(a);
        if (relation) {
            expr* left = a; expr* right = b;
            if (!m.is_eq(left, a, b) || !m.is_eq(right, c, d)) return false;
        }
        if (!ff.is_ff(a) || (relation && a->get_sort() != c->get_sort())) return false;
        engine arithmetic(ff.modulus(a->get_sort()), m.limit(), 100000, 10000, false, false, false);
        obj_map<expr, polynomial> values;
        unsigned variables = 0;
        auto normalize = [&](expr* root) {
            ptr_vector<expr> pending;
            pending.push_back(root);
            while (!pending.empty()) {
                if (!m.inc() || values.size() >= 10000) throw exhausted();
                expr* e = pending.back();
                if (values.contains(e)) { pending.pop_back(); continue; }
                if (!is_app(e)) throw exhausted();
                auto* app = to_app(e);
                bool operation = ff.is_add(e) || ff.is_mul(e) || ff.is_neg(e) || ff.is_bitsum(e);
                if (operation) {
                    bool ready = true;
                    for (expr* arg : *app)
                        if (!values.contains(arg)) { pending.push_back(arg); ready = false; }
                    if (!ready) continue;
                }
                rational number;
                polynomial value;
                if (ff.is_numeral(e, number)) value = arithmetic.constant(number);
                else if (!operation) value = arithmetic.variable(variables++);
                else {
                    value = arithmetic.constant(rational(ff.is_mul(e) ? 1 : 0));
                    rational weight(1);
                    for (expr* arg : *app) {
                        if (ff.is_mul(e)) value = arithmetic.mul(value, values[arg]);
                        else value = arithmetic.add(std::move(value), values[arg], ff.is_neg(e) ? rational(-1) : weight);
                        if (ff.is_bitsum(e)) weight = mod(weight * rational(2), ff.modulus(e->get_sort()));
                    }
                }
                values.insert(e, std::move(value)); pending.pop_back();
            }
            return values[root];
        };
        try {
            auto left_a = normalize(a), left_b = normalize(b);
            auto left = arithmetic.add(std::move(left_a), left_b, rational(-1));
            if (!relation) return left.empty();
            auto right_a = normalize(c), right_b = normalize(d);
            auto right = arithmetic.add(std::move(right_a), right_b, rational(-1));
            if (left.empty() || right.empty()) return left.empty() && right.empty();
            left = arithmetic.scale(left, arithmetic.inverse(left.begin()->second));
            right = arithmetic.scale(right, arithmetic.inverse(right.begin()->second));
            return left.size() == right.size() && std::equal(left.begin(), left.end(), right.begin());
        }
        catch (exhausted const&) { return false; }
    }

    namespace {
        // A deterministic extension of the AST DAG. Every arithmetic term gets
        // a defining equation; foreign applications are opaque field variables.
        // We never descend into foreign arguments or assume their congruence.
        struct encoding {
            ast_manager &m;
            ff_util ff;
            engine &e;
            sort *field;
            unsigned variables = 0;
            obj_map<expr, polynomial> terms;
            std::vector<polynomial> equations;
            encoding(ast_manager &m, engine &e, sort *field) : m(m), ff(m), e(e), field(field) {}
            polynomial term(expr *root) {
                ptr_vector<expr> pending;
                pending.push_back(root);
                while (!pending.empty()) {
                    if (!m.inc())
                        throw exhausted();
                    expr *t = pending.back();
                    if (terms.contains(t)) {
                        pending.pop_back();
                        continue;
                    }
                    if (!is_app(t) || t->get_sort() != field)
                        throw exhausted();
                    auto a = to_app(t);
                    bool ready = true;
                    if (ff.is_interp(t))
                        for (expr *arg : *a)
                            if (!terms.contains(arg)) {
                                pending.push_back(arg);
                                ready = false;
                            }
                    if (!ready)
                        continue;
                    rational c;
                    polynomial f;
                    if (ff.is_numeral(t, c))
                        f = e.constant(c);
                    else if (!ff.is_interp(t))
                        f = e.variable(variables++);
                    else {
                        if (ff.is_neg(t))
                            f = e.scale(terms.find(a->get_arg(0)), rational(-1));
                        else if (ff.is_mul(t) || ff.is_add(t) || ff.is_bitsum(t)) {
                            bool mul = ff.is_mul(t);
                            f = e.constant(rational(mul ? 1 : 0));
                            rational weight(1);
                            for (expr *arg : *a) {
                                f = mul ? e.mul(f, terms.find(arg)) : e.add(std::move(f), terms.find(arg), weight);
                                if (ff.is_bitsum(t))
                                    weight = mod(weight * rational(2), ff.modulus(field));
                            }
                        }
                        else
                            throw exhausted();
                        auto v = e.variable(variables++);
                        equations.push_back(e.add(v, f, rational(-1)));
                        f = std::move(v);
                    }
                    if (variables > 4096 || equations.size() > 8192)
                        throw exhausted();
                    terms.insert(t, std::move(f));
                }
                return terms.find(root);
            }
            void bind(expr_ref_vector const &premises) {
                for (expr *literal : premises) {
                    bool positive = true;
                    if (m.is_not(literal, literal))
                        positive = false;
                    expr *a, *b;
                    if (!m.is_eq(literal, a, b) || a->get_sort() != field || b->get_sort() != field)
                        throw exhausted();
                    // Keep deterministic traversal order: function argument
                    // evaluation order is not part of the proof format.
                    auto left = term(a), right = term(b);
                    auto f = e.add(std::move(left), right, rational(-1));
                    if (!positive) {
                        // f != 0 iff there exists an inverse witness w with
                        // w*f-1=0. A refutation of this extension is sufficient.
                        f = e.add(e.mul(e.variable(variables++), f), e.constant(rational(-1)));
                    }
                    equations.push_back(std::move(f));
                }
                // These are actual field axioms, including extension variables,
                // not algebraic-closure assumptions. Large fields omit them to
                // avoid expanding degree p; absence can only reduce coverage.
                auto p = ff.modulus(field);
                if (p <= rational(31)) {
                    for (unsigned v = 0; v < variables; ++v) {
                        polynomial f;
                        e.add_term(f, monomial(p.get_unsigned(), v), rational(1));
                        equations.push_back(e.add(std::move(f), e.variable(v), rational(-1)));
                    }
                }
            }
        };
        sort *get_field(ast_manager &m, expr_ref_vector const &premises) {
            if (premises.empty() || premises.size() > 4096)
                return nullptr;
            expr *p = premises[0], *a, *b;
            m.is_not(p, p);
            return m.is_eq(p, a, b) && ff_util(m).is_ff(a) ? a->get_sort() : nullptr;
        }
        bool named(expr *e, char const *n, unsigned arity) {
            return is_app(e) && to_app(e)->get_name() == symbol(n) && to_app(e)->get_num_args() == arity;
        }
        bool get_index(arith_util &a, expr *e, unsigned &i) {
            rational r;
            if (!a.is_numeral(e, r) || !r.is_unsigned())
                return false;
            i = r.get_unsigned();
            return true;
        }
        bool unpack(ast_manager &m, app *proof, expr_ref_vector &premises) {
            if (!named(proof, "ff-pac", 2))
                return false;
            expr *ps = proof->get_arg(0);
            if (!is_app(ps) || to_app(ps)->get_name() != symbol("ff-premises"))
                return false;
            for (expr *p : *to_app(ps)) {
                if (!m.is_bool(p))
                    return false;
                premises.push_back(p);
            }
            return get_field(m, premises) != nullptr;
        }
    }  // namespace
    static app_ref pack_certificate(ast_manager &m, sort *field,
                                    expr_ref_vector const &premises, certificate const &cert) {
        arith_util arith(m);
        expr_ref_vector nodes(m);
        auto index = [&](unsigned i) { return arith.mk_int(i); };
        for (auto const &n : cert.nodes) {
            if (!m.inc())
                throw exhausted();
            expr_ref_vector args(m);
            char const *rule;
            if (n.kind == certificate::rule::input) {
                rule = "ff-input";
                args.push_back(index(n.left));
            }
            else if (n.kind == certificate::rule::add) {
                rule = "ff-add";
                args.push_back(nodes.get(n.left));
                args.push_back(nodes.get(n.right));
            }
            else {
                rule = "ff-mul";
                args.push_back(nodes.get(n.left));
                args.push_back(ff_util(m).mk_numeral(n.coefficient, field));
                for (auto v : n.factor)
                    args.push_back(index(v));
            }
            nodes.push_back(m.mk_app(symbol(rule), args.size(), args.data(), m.mk_proof_sort()));
        }
        expr_ref ps(m.mk_app(symbol("ff-premises"), premises.size(), premises.data(), m.mk_proof_sort()), m);
        expr *args[] = {ps, nodes.get(cert.root)};
        return app_ref(m.mk_app(symbol("ff-pac"), 2, args, m.mk_proof_sort()), m);
    }
    struct recorded_problem::imp {
        ast_manager &m;
        engine &algebra;
        sort_ref field;
        expr_ref_vector premises;
        encoding encoded;
        std::vector<rational> values;
        obj_map<expr, rational> evaluated;
        expr_ref_vector evaluated_pins;
        app_ref proof;
        bool checked = false;
        lbool result = l_undef;
        imp(ast_manager &m, sort *field, engine &e, expr_ref_vector const &ps)
            : m(m), algebra(e), field(field, m), premises(ps), encoded(m, e, field), evaluated_pins(m), proof(m) {}
        rational value(expr *root) {
            ptr_vector<expr> pending;
            pending.push_back(root);
            while (!pending.empty()) {
                if (!m.inc()) throw exhausted();
                expr *t = pending.back();
                if (evaluated.contains(t)) { pending.pop_back(); continue; }
                if (!is_app(t) || t->get_sort() != field) throw exhausted();
                rational v;
                if (encoded.ff.is_numeral(t, v)) {}
                else if (!encoded.ff.is_interp(t)) {
                    polynomial f;
                    // Unconstrained foreign values extend the candidate by 0.
                    v = encoded.terms.find(t, f) ? algebra.evaluate(f, values) : rational(0);
                }
                else {
                    bool ready = true;
                    for (expr *arg : *to_app(t))
                        if (!evaluated.contains(arg)) { pending.push_back(arg); ready = false; }
                    if (!ready) continue;
                    bool mul = encoded.ff.is_mul(t);
                    v = rational(mul ? 1 : 0);
                    rational weight(1);
                    for (expr *arg : *to_app(t)) {
                        auto const &a = evaluated.find(arg);
                        v = mod(mul ? v * a : v + weight * a, encoded.ff.modulus(field));
                        if (encoded.ff.is_bitsum(t)) weight = mod(weight * rational(2), encoded.ff.modulus(field));
                    }
                    if (encoded.ff.is_neg(t)) v = mod(-v, encoded.ff.modulus(field));
                }
                evaluated.insert(t, v);
                evaluated_pins.push_back(t);
                pending.pop_back();
            }
            return evaluated.find(root);
        }
    };
    recorded_problem::recorded_problem(ast_manager &m, sort *field, engine &e, expr_ref_vector const &ps)
        : m_imp(std::make_unique<imp>(m, field, e, ps)) {}
    recorded_problem::~recorded_problem() = default;
    lbool recorded_problem::check() {
        auto &p = *m_imp;
        if (p.checked) throw default_exception("recorded field problem already checked");
        p.checked = true;
        p.encoded.bind(p.premises);
        certificate cert;
        p.values.resize(p.encoded.variables);
        p.result = solve_with_certificate(p.algebra, p.encoded.equations, p.values, cert);
        if (p.result == l_false)
            p.proof = pack_certificate(p.m, p.field, p.premises, cert);
        if (p.result == l_true) {
            // Validate AST semantics independently of polynomial conversion and
            // after restoring all eliminated definitions, including witnesses.
            for (expr *lit : p.premises) {
                bool positive = !p.m.is_not(lit, lit);
                expr *a, *b;
                if (!p.m.is_eq(lit, a, b) || (p.value(a) == p.value(b)) != positive)
                    return p.result = l_undef;
            }
        }
        return p.result;
    }
    app *recorded_problem::evidence() const { return m_imp->proof; }
    rational recorded_problem::value(expr *term) {
        if (m_imp->result != l_true) throw default_exception("recorded field candidate unavailable");
        return m_imp->value(term);
    }
    app_ref record_refutation(ast_manager &m, expr_ref_vector const &premises, params_ref const &params) {
        sort *field = get_field(m, premises);
        if (!field) return app_ref(m);
        smt_params_helper opts(params);
        engine e(ff_util(m).modulus(field), m.limit(), opts.ff_max_steps(), opts.ff_max_terms(), false, false, false);
        configure_engine(e, opts);
        try {
            recorded_problem problem(m, field, e, premises);
            return problem.check() == l_false ? app_ref(problem.evidence(), m) : app_ref(m);
        }
        catch (exhausted const&) {
            // Encoding itself uses the algebra budget, before the solver's
            // bounded search handler. All inconclusive local proof attempts
            // obey this interface's null-evidence contract.
            return app_ref(m);
        }
    }
    expr_ref_vector refutation_clause(ast_manager &m, app *proof) {
        expr_ref_vector premises(m), clause(m);
        if (!unpack(m, proof, premises))
            return clause;
        for (expr *p : premises)
            clause.push_back(mk_not(m, p));
        return clause;
    }
    proof_ref mk_refutation_lemma(ast_manager &m, expr *fact, app *evidence) {
        parameter params[] = {parameter(symbol("pac")), parameter(evidence)};
        return proof_ref(m.mk_th_lemma(ff_util(m).get_fid(), fact, 0, nullptr, 2, params), m);
    }
    bool check_refutation_lemma(ast_manager &m, proof *lemma) {
        auto *decl = lemma->get_decl();
        if (decl->get_family_id() != m.get_basic_family_id() || decl->get_decl_kind() != PR_TH_LEMMA ||
            decl->get_num_parameters() != 3 || !decl->get_parameter(0).is_symbol() ||
            decl->get_parameter(0).get_symbol() != symbol("ff") ||
            !decl->get_parameter(1).is_symbol() || decl->get_parameter(1).get_symbol() != symbol("pac") ||
            !decl->get_parameter(2).is_ast() || !is_app(decl->get_parameter(2).get_ast()) ||
            m.get_num_parents(lemma) != 0 || !m.has_fact(lemma))
            return false;
        auto *evidence = to_app(decl->get_parameter(2).get_ast());
        if (!check_refutation(m, evidence)) return false;
        expr_ref_vector literals(m), todo(m);
        expr_mark present;
        todo.push_back(m.get_fact(lemma));
        while (!todo.empty()) {
            expr_ref lit(todo.back(), m);
            todo.pop_back();
            if (m.is_true(lit)) return true;
            if (m.is_or(lit)) {
                for (expr *arg : *to_app(lit)) todo.push_back(arg);
                continue;
            }
            bool negative = false;
            expr *atom = lit;
            while (m.is_not(atom, atom)) negative = !negative;
            literals.push_back(negative ? m.mk_not(atom) : atom);
            present.mark(literals.back(), true);
        }
        // Weakening is valid, but no certified literal may be removed here:
        // propositional discharge is represented by native proof parents above
        // this leaf, never silently assumed by the field checker.
        for (expr *lit : refutation_clause(m, evidence))
            if (!present.is_marked(lit)) return false;
        return true;
    }
    bool check_refutation(ast_manager &m, app *proof) {
        try {
            expr_ref_vector premises(m);
            if (!unpack(m, proof, premises))
                return false;
            auto field = get_field(m, premises);
            engine e(ff_util(m).modulus(field), m.limit(), 10000000, 16384, false, false, false);
            encoding encoded(m, e, field);
            encoded.bind(premises);
            obj_map<expr, polynomial> values;
            ptr_vector<expr> pending;
            pending.push_back(proof->get_arg(1));
            arith_util arith(m);
            while (!pending.empty()) {
                if (!m.inc())
                    throw exhausted();
                expr *t = pending.back();
                if (values.contains(t)) {
                    pending.pop_back();
                    continue;
                }
                if (!is_app(t) || values.size() > 100000)
                    return false;
                app *n = to_app(t);
                bool input = named(n, "ff-input", 1), add = named(n, "ff-add", 2);
                bool mul = n->get_name() == symbol("ff-mul") && n->get_num_args() >= 2;
                if (!input && !add && !mul)
                    return false;
                bool ready = true;
                if (!input) {
                    if (!values.contains(n->get_arg(0))) {
                        pending.push_back(n->get_arg(0));
                        ready = false;
                    }
                    if (add && !values.contains(n->get_arg(1))) {
                        pending.push_back(n->get_arg(1));
                        ready = false;
                    }
                }
                if (!ready)
                    continue;
                polynomial f;
                if (input) {
                    unsigned i;
                    if (!get_index(arith, n->get_arg(0), i) || i >= encoded.equations.size())
                        return false;
                    f = encoded.equations[i];
                }
                else if (add)
                    f = e.add(values.find(n->get_arg(0)), values.find(n->get_arg(1)));
                else {
                    rational c;
                    if (n->get_arg(1)->get_sort() != field || !ff_util(m).is_numeral(n->get_arg(1), c))
                        return false;
                    monomial factor;
                    for (unsigned j = 2; j < n->get_num_args(); ++j) {
                        unsigned v;
                        if (!get_index(arith, n->get_arg(j), v) || v >= encoded.variables)
                            return false;
                        factor.push_back(v);
                    }
                    if (!std::is_sorted(factor.begin(), factor.end()))
                        return false;
                    polynomial multiplier;
                    e.add_term(multiplier, factor, c);
                    f = e.mul(multiplier, values.find(n->get_arg(0)));
                }
                values.insert(t, std::move(f));
            }
            return values.find(proof->get_arg(1)) == e.constant(rational(1));
        } catch (exhausted const &) {
            return false;
        }
    }
}  // namespace ff
