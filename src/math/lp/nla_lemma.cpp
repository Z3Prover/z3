/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include <algorithm>
#include <iterator>
#include "math/lp/nla_lemma.h"
#include "math/lp/nla_core.h"

namespace nla {
    namespace {
        using certificate = lemma_certificate;
        using polynomial = certificate::polynomial;
        using monomial = certificate::monomial;
        using fact = certificate::fact;
        using step = certificate::step;
        using rule = certificate::rule;
        using lp::mpq;

        void add(polynomial &dst, polynomial const &src, mpq const &weight = mpq(1)) {
            for (auto const &[m, c] : src) {
                auto &value = dst[m];
                value += weight * c;
                if (value.is_zero())
                    dst.erase(m);
            }
        }

        bool multiply(polynomial const &a, polynomial const &b, polynomial &result) {
            polynomial product;
            for (auto const &[m, c] : a)
                for (auto const &[n, d] : b) {
                    monomial factors;
                    std::merge(m.begin(), m.end(), n.begin(), n.end(), std::back_inserter(factors));
                    polynomial term{{std::move(factors), c * d}};
                    add(product, term);
                    if (product.size() > 512)
                        return false;
                }
            result = std::move(product);
            return true;
        }

        bool integral(polynomial const &p) {
            for (auto const &[m, c] : p)
                if (!c.is_int() || c.is_zero() || !std::is_sorted(m.begin(), m.end()))
                    return false;
            return true;
        }

        bool expand(certificate const &cert, std::vector<fact> &inputs) {
            auto const &vars = cert.context.variables;
            std::vector<polynomial> expanded(vars.size());
            std::vector<unsigned> state(vars.size(), 0);
            std::map<unsigned, lp::evidence_manager::monomial const *> definitions;
            for (auto const &m : cert.context.monomials) {
                if (m.column >= vars.size() || !definitions.emplace(m.column, &m).second)
                    return false;
            }
            auto variable = [&](auto &&self, unsigned j) -> bool {
                if (j >= vars.size() || state[j] == 1)
                    return false;
                if (state[j] == 2)
                    return true;
                state[j] = 1;
                auto found = definitions.find(j);
                if (found != definitions.end()) {
                    expanded[j][{}] = mpq(1);
                    for (auto k : found->second->factors) {
                        if (!self(self, k))
                            return false;
                        if (!multiply(expanded[j], expanded[k], expanded[j]))
                            return false;
                    }
                }
                else if (!vars[j].definition.empty()) {
                    for (auto const &[c, k] : vars[j].definition) {
                        if (k >= j || !self(self, k))
                            return false;
                        add(expanded[j], expanded[k], c);
                    }
                }
                else
                    expanded[j][{j}] = mpq(1);
                state[j] = 2;
                return true;
            };
            for (auto const &f : cert.assumptions) {
                if (!f.rhs.y.is_zero() || f.contradiction ||
                    (f.kind != lp::EQ && f.kind != lp::NE && f.kind != lp::GE && f.kind != lp::GT && f.kind != lp::LE &&
                     f.kind != lp::LT))
                    return false;
                fact result;
                result.kind = f.kind;
                result.poly[{}] = -f.rhs.x;
                if (result.poly[{}].is_zero())
                    result.poly.clear();
                for (auto const &[c, j] : f.lhs) {
                    if (!variable(variable, j))
                        return false;
                    add(result.poly, expanded[j], c);
                }
                mpq scale(1);
                for (auto const &[m, c] : result.poly)
                    scale = lcm(scale, denominator(c));
                if (result.kind == lp::LE || result.kind == lp::LT) {
                    scale.neg();
                    result.kind = result.kind == lp::LE ? lp::GE : lp::GT;
                }
                for (auto &[m, c] : result.poly)
                    c *= scale;
                inputs.push_back(std::move(result));
            }
            return true;
        }

        bool nonzero(lp::lconstraint_kind k) {
            return k == lp::NE || k == lp::GT;
        }
        bool nonnegative(lp::lconstraint_kind k) {
            return k == lp::GE || k == lp::GT;
        }

        bool replay(step const &s, std::vector<fact> const &inputs, std::vector<fact> const &prior, fact &result) {
            switch (s.kind) {
            case rule::input:
                if (s.left >= inputs.size())
                    return false;
                result = inputs[s.left];
                return true;
            case rule::product: {
                if (s.left >= prior.size() || s.right >= prior.size())
                    return false;
                auto const &a = prior[s.left];
                auto const &b = prior[s.right];
                if (a.kind == lp::EQ || b.kind == lp::EQ)
                    result.kind = lp::EQ;
                else if (nonnegative(a.kind) && nonnegative(b.kind))
                    result.kind = a.kind == lp::GT && b.kind == lp::GT ? lp::GT : lp::GE;
                else if (nonzero(a.kind) && nonzero(b.kind))
                    result.kind = lp::NE;
                else
                    return false;
                return multiply(a.poly, b.poly, result.poly);
            }
            case rule::zero_product:
                if (s.left >= prior.size() || prior[s.left].kind != lp::EQ || !integral(s.argument))
                    return false;
                result.kind = lp::EQ;
                return multiply(prior[s.left].poly, s.argument, result.poly);
            case rule::square:
                if (!integral(s.argument))
                    return false;
                result.kind = lp::GE;
                return multiply(s.argument, s.argument, result.poly);
            case rule::linear: {
                if (!s.offset.is_int() || s.offset.is_neg())
                    return false;
                bool inequalities = false, strict = s.offset.is_pos();
                unsigned disequalities = 0;
                if (!s.offset.is_zero())
                    result.poly[{}] = s.offset;
                for (auto const &[i, c] : s.premises) {
                    if (i >= prior.size() || !c.is_int())
                        return false;
                    if (c.is_zero())
                        continue;
                    auto const &p = prior[i];
                    if (nonnegative(p.kind)) {
                        if (c.is_neg())
                            return false;
                        inequalities = true;
                        strict |= p.kind == lp::GT;
                    }
                    else if (p.kind == lp::NE)
                        ++disequalities;
                    else if (p.kind != lp::EQ)
                        return false;
                    add(result.poly, p.poly, c);
                    if (result.poly.size() > 512)
                        return false;
                }
                if (disequalities && (disequalities != 1 || inequalities || !s.offset.is_zero()))
                    return false;
                result.kind = disequalities ? lp::NE : strict ? lp::GT : inequalities ? lp::GE : lp::EQ;
                return true;
            }
            }
            return false;
        }

        bool contradiction(fact const &f) {
            if (f.poly.size() > 1 || (!f.poly.empty() && !f.poly.begin()->first.empty()))
                return false;
            mpq c = f.poly.empty() ? mpq(0) : f.poly.begin()->second;
            return f.kind == lp::EQ   ? !c.is_zero()
                   : f.kind == lp::NE ? c.is_zero()
                   : f.kind == lp::GT ? !c.is_pos()
                                      : f.kind == lp::GE && c.is_neg();
        }

        unsigned degree(polynomial const &p) {
            unsigned result = 0;
            for (auto const &[m, c] : p)
                result = std::max(result, static_cast<unsigned>(m.size()));
            return result;
        }

        bool linear_refutation(std::vector<fact> const &facts, step &result, lp::lp_settings &settings) {
            struct limit : lp::lp_resource_limit {
                lp::lp_settings &parent;
                unsigned ticks = 0;
                explicit limit(lp::lp_settings &p) : parent(p) {}
                bool get_cancel_flag() override {
                    return ++ticks > 20000 || parent.get_cancel_flag();
                }
            } resource(settings);
            lp::lar_solver solver(true);
            solver.settings().set_resource_limit(resource);
            std::map<monomial, unsigned> columns;
            std::map<unsigned, unsigned> sources;
            for (unsigned i = 0; i < facts.size(); ++i) {
                auto const &f = facts[i];
                if (f.kind == lp::NE || degree(f.poly) == 0)
                    continue;
                vector<std::pair<mpq, lp::lpvar>> term;
                mpq constant(0);
                for (auto const &[m, c] : f.poly) {
                    if (m.empty()) {
                        constant = c;
                        continue;
                    }
                    auto [entry, fresh] = columns.emplace(m, 0);
                    if (fresh)
                        entry->second = solver.add_var(static_cast<unsigned>(columns.size() - 1), false);
                    term.push_back({c, entry->second});
                }
                auto j = solver.add_term(term, UINT_MAX);
                auto ci = solver.add_var_bound(j, f.kind, -constant);
                sources.emplace(ci, i);
                solver.activate(ci);
            }
            if (solver.find_feasible_solution() != lp::lp_status::INFEASIBLE)
                return false;
            lp::explanation explanation;
            solver.get_infeasibility_explanation(explanation);
            vector<std::pair<lp::constraint_index, mpq>> coefficients;
            if (!solver.dep_manager().linearize_coefficients(explanation.evidence(), mpq(1), coefficients))
                return false;
            mpq scale(1);
            for (auto const &[ci, c] : coefficients)
                scale = lcm(scale, denominator(c));
            result.kind = rule::linear;
            for (auto const &[ci, c] : coefficients) {
                auto found = sources.find(ci);
                if (found == sources.end())
                    return false;
                auto i = found->second;
                result.premises.push_back({i, scale * (facts[i].kind == lp::EQ ? -c : c)});
            }
            return true;
        }

        bool prove(certificate &cert, lp::lp_settings &settings) {
            std::vector<fact> inputs, facts;
            if (!expand(cert, inputs) || inputs.size() > 64)
                return false;
            auto append = [&](step s) {
                fact f;
                if (facts.size() >= 384 || settings.get_cancel_flag() || !replay(s, inputs, facts, f) ||
                    f.poly.size() > 512)
                    return false;
                cert.steps.push_back(std::move(s));
                facts.push_back(std::move(f));
                if (contradiction(facts.back()))
                    cert.root = static_cast<unsigned>(facts.size() - 1);
                return true;
            };
            unsigned max_degree = 1;
            for (unsigned i = 0; i < inputs.size(); ++i) {
                step s;
                s.left = i;
                if (!append(std::move(s)))
                    return false;
                max_degree = std::max(max_degree, degree(inputs[i].poly));
            }
            std::map<unsigned, polynomial> variables;
            for (auto const &f : inputs)
                for (auto const &[m, c] : f.poly)
                    for (auto j : m)
                        variables[j] = {{{j}, mpq(1)}};
            for (auto const &[j, p] : variables) {
                step s;
                s.kind = rule::square;
                s.argument = p;
                if (!append(std::move(s)))
                    return false;
            }
            for (unsigned i = 0; i < inputs.size(); ++i) {
                auto const &f = inputs[i];
                auto constant = f.poly.find({});
                if (nonnegative(f.kind) && constant != f.poly.end() && constant->second.is_neg()) {
                    step s;
                    s.kind = rule::linear;
                    s.offset = -constant->second;
                    s.premises.push_back({i, mpq(1)});
                    if (!append(std::move(s)))
                        return false;
                }
                if (f.kind == lp::EQ)
                    for (auto const &[j, p] : variables) {
                        step s;
                        s.kind = rule::zero_product;
                        s.left = i;
                        s.argument = p;
                        if (!append(std::move(s)))
                            return false;
                    }
            }
            unsigned seed = static_cast<unsigned>(facts.size()), begin = 0;
            for (unsigned round = 0; round < max_degree && facts.size() < 384; ++round) {
                if (settings.get_cancel_flag())
                    return false;
                if (cert.root != UINT_MAX)
                    return true;
                for (unsigned i = 0; i < facts.size(); ++i)
                    if (facts[i].kind == lp::NE)
                        for (unsigned j = 0; j < facts.size(); ++j) {
                            if (settings.get_cancel_flag())
                                return false;
                            auto const &a = facts[i].poly;
                            auto const &b = facts[j].poly;
                            if (facts[j].kind != lp::EQ || a.empty() || a.size() != b.size() || b.empty())
                                continue;
                            mpq ratio = a.begin()->second / b.begin()->second;
                            polynomial difference = a;
                            add(difference, b, -ratio);
                            if (!difference.empty())
                                continue;
                            step s;
                            s.kind = rule::linear;
                            s.premises = {{i, mpq(denominator(ratio))}, {j, -numerator(ratio)}};
                            append(std::move(s));
                            return cert.root != UINT_MAX;
                        }
                step refutation;
                if (linear_refutation(facts, refutation, settings) && append(std::move(refutation)) &&
                    cert.root != UINT_MAX)
                    return true;
                unsigned end = static_cast<unsigned>(facts.size());
                for (unsigned i = begin; i < end && facts.size() < 384; ++i)
                    for (unsigned j = 0; j < seed && facts.size() < 384; ++j) {
                        if (settings.get_cancel_flag())
                            return false;
                        if (degree(facts[i].poly) + degree(facts[j].poly) > max_degree)
                            continue;
                        step s;
                        s.kind = rule::product;
                        s.left = i;
                        s.right = j;
                        fact candidate;
                        if (!replay(s, inputs, facts, candidate) ||
                            std::find(facts.begin(), facts.end(), candidate) != facts.end())
                            continue;
                        append(std::move(s));
                    }
                if (end == facts.size())
                    break;
                begin = end;
            }
            if (cert.root != UINT_MAX)
                return true;
            step refutation;
            return linear_refutation(facts, refutation, settings) && append(std::move(refutation)) &&
                   cert.root != UINT_MAX;
        }
    }  // namespace

    bool lemma_certificate::check() const {
        std::vector<fact> inputs, prior;
        if (root >= steps.size() || premise_count > assumptions.size() || !expand(*this, inputs))
            return false;
        for (auto const &s : steps) {
            fact result;
            if (!replay(s, inputs, prior, result))
                return false;
            prior.push_back(std::move(result));
        }
        return contradiction(prior[root]);
    }

    std::shared_ptr<lemma_certificate const> lemma_certificate::capture(lp::lar_solver &solver, lemma const &l) {
        if (!solver.dep_manager().proofs_enabled())
            return nullptr;
        auto cert = std::make_shared<lemma_certificate>();
        solver.dep_manager().snapshot_context(cert->context);
        auto add_fact = [&](lp::evidence_manager::fact f) {
            cert->assumptions.push_back(solver.dep_manager().snapshot_fact(std::move(f)));
        };
        for (auto const &ev : l.expl()) {
            auto const &c = solver.constraints()[ev.ci()];
            lp::evidence_manager::fact f;
            f.lhs = c.coeffs();
            f.kind = c.kind();
            f.rhs = c.rhs_impq();
            f.rhs.x -= c.get_free_coeff_of_left_side();
            add_fact(std::move(f));
        }
        cert->premise_count = cert->assumptions.size();
        for (auto const &ineq : l.ineqs()) {
            lp::evidence_manager::fact f;
            f.lhs = ineq.term().coeffs_as_vector();
            f.kind = ineq.cmp() == lp::EQ   ? lp::NE
                     : ineq.cmp() == lp::NE ? lp::EQ
                     : ineq.cmp() == lp::LE ? lp::GT
                     : ineq.cmp() == lp::LT ? lp::GE
                     : ineq.cmp() == lp::GE ? lp::LT
                                            : lp::LE;
            f.rhs = lp::impq(ineq.rs());
            add_fact(std::move(f));
        }
        return prove(*cert, solver.settings()) && cert->check() ? cert : nullptr;
    }

    void lemma_certificate::display(std::ostream &out) const {
        std::vector<fact> inputs;
        if (!expand(*this, inputs)) {
            out << "(invalid)";
            return;
        }
        out << "(polynomial-refutation (premises " << premise_count << ") (variables";
        for (unsigned i = 0; i < context.variables.size(); ++i) {
            auto const &v = context.variables[i];
            out << " (" << i << " " << (v.is_int ? "Int" : "Real") << " (";
            for (auto const &[c, j] : v.definition)
                out << "(" << c << " " << j << ")";
            out << "))";
        }
        out << ") (monomials";
        for (auto const &m : context.monomials) {
            out << " (" << m.column;
            for (auto j : m.factors)
                out << " " << j;
            out << ")";
        }
        out << ") (assumptions";
        for (auto const &f : assumptions) {
            out << " (" << lp::lconstraint_kind_string(f.kind) << " " << f.rhs.x << " (";
            for (auto const &[c, j] : f.lhs)
                out << "(" << c << " " << j << ")";
            out << "))";
        }
        out << ") (inputs";
        for (auto const &f : inputs) {
            out << " (" << lp::lconstraint_kind_string(f.kind);
            for (auto const &[m, c] : f.poly) {
                out << " (" << c;
                for (auto j : m)
                    out << " " << j;
                out << ")";
            }
            out << ")";
        }
        out << ") (steps";
        for (auto const &s : steps) {
            out << " (" << static_cast<unsigned>(s.kind) << " " << s.left << " " << s.right << " " << s.offset;
            out << " (";
            for (auto const &[m, c] : s.argument) {
                out << "(" << c;
                for (auto j : m)
                    out << " " << j;
                out << ")";
            }
            out << ") (";
            for (auto const &[i, c] : s.premises)
                out << "(" << i << " " << c << ")";
            out << "))";
        }
        out << ") (root " << root << "))";
    }
}  // namespace nla
