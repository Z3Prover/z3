/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include "ast/proofs/lp_proof.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include <set>

namespace lp {
    namespace {
        using manager = evidence_manager;
        using rule = manager::rule;

        char const* name(rule r) {
            switch (r) {
            case rule::input: return "lp-input";
            case rule::linear: return "lp-linear";
            case rule::integer_tighten: return "lp-integer-tighten";
            case rule::integer_lattice: return "lp-integer-lattice";
            case rule::gomory: return "lp-gomory";
            case rule::monomial_substitute: return "lp-monomial-substitute";
            case rule::monomial_interval: return "lp-monomial-interval";
            case rule::discharge: return "lp-discharge";
            default: return "lp-unsupported";
            }
        }

        bool hint(proof const* p, char const* s) {
            auto* d = p->get_decl();
            return p->get_decl_kind() == PR_TH_LEMMA && d->get_num_parameters() >= 2 &&
                d->get_parameter(0).is_symbol() && d->get_parameter(0).get_symbol() == symbol("arith") &&
                d->get_parameter(1).is_symbol() && d->get_parameter(1).get_symbol() == symbol(s);
        }

        void put(vector<parameter>& ps, unsigned n) {
            ps.push_back(parameter(rational(n)));
        }

        void put(vector<parameter>& ps, manager::fact const& f) {
            put(ps, static_cast<unsigned>(static_cast<int>(f.kind) + 2));
            put(ps, f.contradiction ? 1 : 0);
            ps.push_back(parameter(f.rhs.x));
            ps.push_back(parameter(f.rhs.y));
            put(ps, f.lhs.size());
            for (auto const& [c, j] : f.lhs) {
                ps.push_back(parameter(c));
                put(ps, j);
            }
        }

        struct reader {
            func_decl* d;
            unsigned cursor = 2;
            bool get(unsigned& n) {
                if (cursor == d->get_num_parameters())
                    return false;
                auto const& p = d->get_parameter(cursor++);
                if (!p.is_rational() || !p.get_rational().is_unsigned())
                    return false;
                n = p.get_rational().get_unsigned();
                return true;
            }
            bool get(mpq& q) {
                if (cursor == d->get_num_parameters())
                    return false;
                auto const& p = d->get_parameter(cursor++);
                if (!p.is_rational())
                    return false;
                q = p.get_rational();
                return true;
            }
            bool get(expr*& e) {
                if (cursor == d->get_num_parameters())
                    return false;
                auto const& p = d->get_parameter(cursor++);
                if (!p.is_ast() || !is_expr(p.get_ast()))
                    return false;
                e = to_expr(p.get_ast());
                return true;
            }
            bool count(unsigned& n) {
                return get(n) && n <= d->get_num_parameters() - cursor;
            }
            bool get(manager::fact& f) {
                unsigned kind, contradiction, size;
                if (!get(kind) || !get(contradiction) || contradiction > 1 ||
                    !get(f.rhs.x) || !get(f.rhs.y) || !count(size))
                    return false;
                if (kind > 4)
                    return false;
                f.kind = static_cast<lconstraint_kind>(static_cast<int>(kind) - 2);
                f.contradiction = contradiction != 0;
                for (unsigned i = 0; i < size; ++i) {
                    mpq c;
                    unsigned j;
                    if (!get(c) || !get(j))
                        return false;
                    f.lhs.push_back({c, j});
                }
                return true;
            }
        };

        void encode(manager::proof_expression const& e, expr_ref_vector const& variables, vector<parameter>& ps) {
            ps.push_back(parameter(symbol("lp-context")));
            put(ps, 1); // Certificate format version.
            put(ps, e.variables.size());
            for (unsigned i = 0; i < e.variables.size(); ++i) {
                auto const& v = e.variables[i];
                ps.push_back(parameter(variables[i]));
                put(ps, v.is_int ? 1 : 0);
                put(ps, v.definition.size());
                for (auto const& [c, j] : v.definition) {
                    ps.push_back(parameter(c));
                    put(ps, j);
                }
            }
            put(ps, e.monomials.size());
            for (auto const& mon : e.monomials) {
                put(ps, mon.column);
                put(ps, mon.factors.size());
                for (auto j : mon.factors)
                    put(ps, j);
            }
            put(ps, e.steps.size());
            for (auto const& s : e.steps) {
                put(ps, static_cast<unsigned>(s.kind));
                put(ps, s.conclusion);
                put(ps, s.input);
                put(ps, s.assumption);
                put(ps, s.id);
                put(ps, s.equation);
                put(ps, s.pivot);
                put(ps, s.definition);
                put(ps, s.source);
                ps.push_back(parameter(s.divisor));
                put(ps, s.premises.size());
                for (unsigned i = 0; i < s.premises.size(); ++i) {
                    put(ps, s.premises[i]);
                    ps.push_back(parameter(s.coefficients[i]));
                }
                put(ps, s.bounds.size());
                for (auto const& b : s.bounds) {
                    put(ps, b.column);
                    put(ps, b.lower);
                    put(ps, b.upper);
                }
            }
            put(ps, e.root);
        }

        bool decode(proof* context, manager::proof_expression& e, expr_ref_vector& variables) {
            if (!hint(context, "lp-context"))
                return false;
            reader r{context->get_decl()};
            unsigned version, size;
            if (!r.get(version) || version != 1 || !r.count(size))
                return false;
            for (unsigned i = 0; i < size; ++i) {
                manager::variable v;
                expr* term;
                unsigned is_int, count;
                if (!r.get(term) || !r.get(is_int) || is_int > 1 || !r.count(count))
                    return false;
                v.is_int = is_int != 0;
                variables.push_back(term);
                for (unsigned k = 0; k < count; ++k) {
                    mpq c;
                    unsigned j;
                    if (!r.get(c) || !r.get(j))
                        return false;
                    v.definition.push_back({c, j});
                }
                e.variables.push_back(std::move(v));
            }
            if (!r.count(size))
                return false;
            for (unsigned i = 0; i < size; ++i) {
                manager::monomial mon;
                unsigned count;
                if (!r.get(mon.column) || !r.count(count))
                    return false;
                for (unsigned k = 0; k < count; ++k) {
                    unsigned j;
                    if (!r.get(j))
                        return false;
                    mon.factors.push_back(j);
                }
                e.monomials.push_back(std::move(mon));
            }
            if (!r.count(size))
                return false;
            for (unsigned i = 0; i < size; ++i) {
                manager::proof_step s;
                unsigned kind, count;
                if (!r.get(kind) || kind >= static_cast<unsigned>(rule::unsupported) || !r.get(s.conclusion) ||
                    !r.get(s.input) || !r.get(s.assumption) || !r.get(s.id) || !r.get(s.equation) ||
                    !r.get(s.pivot) || !r.get(s.definition) || !r.get(s.source) || !r.get(s.divisor) ||
                    !r.count(count))
                    return false;
                s.kind = static_cast<rule>(kind);
                for (unsigned k = 0; k < count; ++k) {
                    unsigned j;
                    mpq c;
                    if (!r.get(j) || !r.get(c))
                        return false;
                    s.premises.push_back(j);
                    s.coefficients.push_back(c);
                }
                if (!r.count(count))
                    return false;
                for (unsigned k = 0; k < count; ++k) {
                    manager::column_bounds b;
                    if (!r.get(b.column) || !r.get(b.lower) || !r.get(b.upper))
                        return false;
                    s.bounds.push_back(b);
                }
                e.steps.push_back(std::move(s));
            }
            return r.get(e.root) && r.cursor == r.d->get_num_parameters() && e.check();
        }

        expr_ref real_term(ast_manager& m, expr* e) {
            arith_util a(m);
            return expr_ref(a.is_int(e) ? a.mk_to_real(e) : e, m);
        }

        expr_ref polynomial(ast_manager& m, vector<std::pair<mpq, lpvar>> const& lhs,
                            expr_ref_vector const& variables, bool is_int = false,
                            rational const& scale = rational(1)) {
            arith_util a(m);
            expr_ref_vector terms(m);
            for (auto const& [c, j] : lhs) {
                if (j >= variables.size())
                    return expr_ref(m);
                expr_ref t(variables[j], m);
                if (!is_int)
                    t = real_term(m, t);
                terms.push_back(a.mk_mul(a.mk_numeral(scale * c, is_int), t));
            }
            return expr_ref(terms.empty() ? a.mk_numeral(rational(0), is_int) : a.mk_add(terms), m);
        }

        rational fact_scale(ast_manager& m, manager::fact const& f, expr_ref_vector const& variables) {
            if (f.contradiction)
                return rational(1);
            arith_util a(m);
            rational scale = denominator(f.rhs.x);
            for (auto const& [c, j] : f.lhs) {
                if (j >= variables.size() || !a.is_int(variables[j]))
                    return rational(1);
                scale = lcm(scale, denominator(c));
            }
            return scale;
        }

        vector<rational> weights(ast_manager& m, manager::proof_expression const& e,
                                 manager::proof_step const& s, expr_ref_vector const& variables) {
            vector<rational> result;
            for (unsigned i = 0; i < s.premises.size(); ++i)
                result.push_back(s.coefficients[i] / fact_scale(m, e.steps[s.premises[i]].conclusion, variables));
            if (!s.conclusion.contradiction)
                result.push_back(rational(1) / fact_scale(m, s.conclusion, variables));
            return result;
        }

    }

    expr_ref evidence_fact(ast_manager& m, manager::fact const& f, expr_ref_vector const& variables) {
        if (f.contradiction)
            return expr_ref(m.mk_false(), m);
        arith_util a(m);
        bool is_int = true;
        rational scale = denominator(f.rhs.x);
        for (auto const& [c, j] : f.lhs) {
            if (j >= variables.size())
                return expr_ref(m);
            is_int &= a.is_int(variables[j]);
            scale = lcm(scale, denominator(c));
        }
        if (!is_int)
            scale = rational(1);
        expr_ref lhs = polynomial(m, f.lhs, variables, is_int, scale);
        if (!lhs || !f.rhs.y.is_zero())
            return expr_ref(m);
        expr_ref rhs(a.mk_numeral(scale * f.rhs.x, is_int), m);
        switch (f.kind) {
        case EQ: return expr_ref(m.mk_eq(lhs, rhs), m);
        case LE: return expr_ref(a.mk_le(lhs, rhs), m);
        case LT: return expr_ref(a.mk_lt(lhs, rhs), m);
        case GE: return expr_ref(a.mk_ge(lhs, rhs), m);
        case GT: return expr_ref(a.mk_gt(lhs, rhs), m);
        default: return expr_ref(m);
        }
    }

    namespace {
        bool equivalent(ast_manager& m, expr* x, expr* y) {
            if (!x || !y)
                return false;
            expr_ref eq(m.mk_eq(x, y), m);
            params_ref params;
            params.set_bool("sort_sums", true);
            params.set_bool("som", true);
            th_rewriter rw(m, params);
            rw(eq);
            return m.is_true(eq);
        }

        bool check_bindings(ast_manager& m, manager::proof_expression const& e, expr_ref_vector const& variables) {
            arith_util a(m);
            for (unsigned i = 0; i < variables.size(); ++i) {
                auto const& v = e.variables[i];
                if (v.is_int ? !a.is_int(variables[i]) : !a.is_real(variables[i])) {
                    IF_VERBOSE(10, verbose_stream() << "LP proof: variable sort mismatch at " << i << "\n";);
                    return false;
                }
                if (!v.definition.empty()) {
                    expr_ref lhs = real_term(m, variables[i]);
                    expr_ref rhs = polynomial(m, v.definition, variables);
                    if (!equivalent(m, lhs, rhs)) {
                        IF_VERBOSE(10, verbose_stream() << "LP proof: definition mismatch " << mk_pp(lhs, m)
                                   << " := " << mk_pp(rhs, m) << "\n";);
                        return false;
                    }
                }
            }
            for (auto const& s : e.steps) {
                if (s.kind != rule::monomial_substitute && s.kind != rule::monomial_interval)
                    continue;
                if (s.definition >= e.monomials.size())
                    return false;
                auto const& mon = e.monomials[s.definition];
                if (mon.column >= variables.size())
                    return false;
                expr_ref_vector factors(m);
                for (auto j : mon.factors) {
                    if (j >= variables.size())
                        return false;
                    factors.push_back(real_term(m, variables[j]));
                }
                expr_ref lhs = real_term(m, variables[mon.column]);
                expr_ref rhs(factors.empty() ? a.mk_numeral(rational(1), false) : a.mk_mul(factors), m);
                if (!equivalent(m, lhs, rhs))
                    return false;
            }
            return true;
        }
    }

    bool is_evidence_proof(proof const* p) {
        if (hint(p, "lp-context"))
            return true;
        for (unsigned i = 0; i < static_cast<unsigned>(rule::unsupported); ++i)
            if (hint(p, name(static_cast<rule>(i))))
                return true;
        auto* d = p->get_decl();
        return p->get_decl_kind() == PR_TH_LEMMA && d->get_num_parameters() >= 2 &&
            d->get_parameter(0).is_symbol() && d->get_parameter(0).get_symbol() == symbol("arith") &&
            d->get_parameter(1).is_symbol() && d->get_parameter(1).get_symbol().str().starts_with("lp-");
    }

    class evidence_proof_checker::imp {
        struct certificate {
            proof_ref context;
            manager::proof_expression evidence;
            expr_ref_vector variables;
            certificate(ast_manager& m, proof* p): context(p, m), variables(m) {}
        };
        ast_manager& m;
        std::unordered_map<proof*, std::unique_ptr<certificate>> m_contexts;
    public:
        explicit imp(ast_manager& m): m(m) {}
        bool check(proof* p);
    };

    evidence_proof_checker::evidence_proof_checker(ast_manager& m): m_imp(std::make_unique<imp>(m)) {}
    evidence_proof_checker::~evidence_proof_checker() = default;
    bool evidence_proof_checker::check(proof* p) { return m_imp->check(p); }

    bool evidence_proof_checker::imp::check(proof* p) {
        if (!m.is_proof(p) || !m.has_fact(p))
            return false;
        bool context_rule = hint(p, "lp-context");
        if (!context_rule && m.get_num_parents(p) == 0)
            return false;
        proof* context = context_rule ? p : m.get_parent(p, 0);
        if (!m.is_proof(context) || !m.has_fact(context) ||
            m.get_num_parents(context) != 0 || !m.is_true(m.get_fact(context)))
            return false;
        auto found = m_contexts.find(context);
        if (found == m_contexts.end()) {
            auto c = std::make_unique<certificate>(m, context);
            if (!decode(context, c->evidence, c->variables) || !check_bindings(m, c->evidence, c->variables))
                return false;
            found = m_contexts.emplace(context, std::move(c)).first;
        }
        auto const& e = found->second->evidence;
        auto const& variables = found->second->variables;
        if (context_rule)
            return true;
        auto* d = p->get_decl();
        if (d->get_num_parameters() < 3 || !d->get_parameter(2).is_rational() ||
            !d->get_parameter(2).get_rational().is_unsigned())
            return false;
        unsigned index = d->get_parameter(2).get_rational().get_unsigned();
        if (index >= e.steps.size())
            return false;
        auto const& s = e.steps[index];
        vector<rational> expected_weights;
        if (s.kind == rule::linear)
            expected_weights = weights(m, e, s, variables);
        if (d->get_num_parameters() != 3 + expected_weights.size())
            return false;
        for (unsigned i = 0; i < expected_weights.size(); ++i)
            if (!d->get_parameter(i + 3).is_rational() ||
                d->get_parameter(i + 3).get_rational() != expected_weights[i])
                return false;
        expr_ref conclusion = evidence_fact(m, s.conclusion, variables);
        if (!hint(p, name(s.kind)) || !equivalent(m, m.get_fact(p), conclusion))
            return false;
        if (s.kind == rule::input) {
            if (m.get_num_parents(p) == 1)
                return equivalent(m, conclusion, m.mk_true());
            return m.get_num_parents(p) == 2 &&
                equivalent(m, m.get_fact(m.get_parent(p, 1)), conclusion);
        }
        if (s.kind == rule::discharge) {
            if (m.get_num_parents(p) != 2)
                return false;
            expr_ref assumption = evidence_fact(m, e.steps[s.assumption].conclusion, variables);
            return equivalent(m, m.get_fact(m.get_parent(p, 1)), m.mk_not(assumption));
        }
        if (m.get_num_parents(p) != s.premises.size() + 1)
            return false;
        for (unsigned i = 0; i < s.premises.size(); ++i) {
            expr_ref premise = evidence_fact(m, e.steps[s.premises[i]].conclusion, variables);
            if (!equivalent(m, m.get_fact(m.get_parent(p, i + 1)), premise))
                return false;
        }
        return true;
    }

    bool check_evidence_proof(ast_manager& m, proof* p) {
        evidence_proof_checker checker(m);
        return checker.check(p);
    }

    bool bind_evidence_inputs(ast_manager& m, manager::proof_expression const& e,
                              expr_ref_vector const& variables, proof_ref_vector const& premises,
                              proof_ref_vector& inputs) {
        if (variables.size() != e.variables.size() || !e.check())
            return false;
        inputs.reset();
        for (auto const& s : e.steps) {
            proof* input = nullptr;
            if (s.kind == rule::input) {
                expr_ref f = evidence_fact(m, s.conclusion, variables);
                for (auto* premise : premises)
                    if (equivalent(m, f, m.get_fact(premise))) {
                        input = premise;
                        break;
                    }
            }
            inputs.push_back(input);
        }
        return true;
    }

    proof_ref mk_evidence_proof(ast_manager& m, manager::proof_expression const& e,
                               expr_ref_vector const& variables, proof_ref_vector const& inputs) {
        proof_ref result(m);
        if (!m.proofs_enabled() || !e.check() || variables.size() != e.variables.size() ||
            inputs.size() != e.steps.size() || !check_bindings(m, e, variables))
            return result;
        vector<parameter> params;
        encode(e, variables, params);
        proof_ref context(m.mk_th_lemma(arith_util(m).get_family_id(), m.mk_true(), 0, nullptr,
                                       params.size(), params.data()), m);
        proof_ref_vector steps(m);
        std::vector<std::set<unsigned>> open(e.steps.size());
        for (unsigned i = 0; i < e.steps.size(); ++i) {
            auto const& s = e.steps[i];
            expr_ref conclusion = evidence_fact(m, s.conclusion, variables);
            proof_ref_vector parents(m);
            parents.push_back(context);
            if (s.kind == rule::input) {
                if (inputs[i]) {
                    if (!equivalent(m, m.get_fact(inputs[i]), conclusion))
                        return result;
                    parents.push_back(inputs[i]);
                }
                else if (!equivalent(m, conclusion, m.mk_true())) {
                    parents.push_back(m.mk_hypothesis(conclusion));
                    open[i].insert(i);
                }
            }
            else if (s.kind == rule::discharge) {
                expr_ref assumption = evidence_fact(m, e.steps[s.assumption].conclusion, variables);
                parents.push_back(m.mk_lemma(steps.get(s.premises[0]), m.mk_not(assumption)));
            }
            else
                for (auto j : s.premises)
                    parents.push_back(steps.get(j));
            for (auto j : s.premises)
                open[i].insert(open[j].begin(), open[j].end());
            if (s.kind == rule::discharge)
                open[i].erase(s.assumption);
            vector<parameter> ps;
            ps.push_back(parameter(symbol(name(s.kind))));
            ps.push_back(parameter(rational(i)));
            if (s.kind == rule::linear)
                for (auto const& c : weights(m, e, s, variables))
                    ps.push_back(parameter(c));
            proof_ref step(m.mk_th_lemma(arith_util(m).get_family_id(), conclusion, parents.size(), parents.data(),
                                        ps.size(), ps.data()), m);
            steps.push_back(step);
        }
        if (open[e.root].empty())
            result = steps.get(e.root);
        else {
            IF_VERBOSE(10, for (auto i : open[e.root])
                           verbose_stream() << "LP proof: unbound input " << i << ": "
                                            << mk_pp(m.get_fact(steps.get(i)), m) << "\n";);
        }
        return result;
    }
}
