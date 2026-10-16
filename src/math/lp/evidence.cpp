/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include <map>
#include <vector>
#include "math/lp/evidence.h"

namespace lp {
    namespace {
        using polynomial = std::map<lpvar, mpq>;

        void add(polynomial &dst, polynomial const &src, mpq const &coefficient) {
            for (auto const &[j, c] : src) {
                auto &d = dst[j];
                d += coefficient * c;
                if (d.is_zero())
                    dst.erase(j);
            }
        }

        bool is_upper(lconstraint_kind kind) {
            return kind == LE || kind == LT;
        }
        bool is_lower(lconstraint_kind kind) {
            return kind == GE || kind == GT;
        }
        bool is_strict(lconstraint_kind kind) {
            return kind == LT || kind == GT;
        }

        struct normalized {
            polynomial lhs;
            mpq constant;
            lconstraint_kind kind = EQ;
        };

        bool normalize(evidence_manager::fact const &f, std::vector<polynomial> const &variables, normalized &p) {
            if (!f.rhs.y.is_zero() || (f.kind != EQ && !is_lower(f.kind) && !is_upper(f.kind)))
                return false;
            p.kind = f.kind;
            mpq sign(is_lower(f.kind) ? -1 : 1);
            p.constant = -sign * f.rhs.x;
            for (auto const &[c, j] : f.lhs) {
                if (j >= variables.size())
                    return false;
                add(p.lhs, variables[j], sign * c);
            }
            return true;
        }
    }  // namespace

    bool evidence_manager::proof_expression::check() const {
        if (!complete || root >= steps.size())
            return false;
        std::vector<polynomial> expanded;
        for (unsigned i = 0; i < variables.size(); ++i) {
            auto const &v = variables[i];
            polynomial p;
            if (v.definition.empty())
                p[i] = mpq(1);
            for (auto const &[c, j] : v.definition) {
                if (j >= i || (v.is_int && (!c.is_int() || !variables[j].is_int)))
                    return false;
                add(p, expanded[j], c);
            }
            expanded.push_back(std::move(p));
        }
        std::vector<normalized> facts;
        for (unsigned i = 0; i < steps.size(); ++i) {
            auto const &s = steps[i];
            if (s.kind < rule::input || s.kind > rule::unsupported ||
                (s.kind != rule::discharge && s.assumption != UINT_MAX))
                return false;
            normalized f;
            if (!normalize(s.conclusion, expanded, f))
                return false;
            if (s.premises.size() != s.coefficients.size())
                return false;
            for (auto j : s.premises)
                if (j >= i)
                    return false;
            switch (s.kind) {
            case rule::input:
                if (s.input == UINT_MAX || s.conclusion.contradiction || !s.premises.empty())
                    return false;
                break;
            case rule::linear: {
                polynomial lhs;
                mpq constant(0);
                bool strict = false, equality = true;
                for (unsigned k = 0; k < s.premises.size(); ++k) {
                    auto j = s.premises[k];
                    auto const &p = facts[j];
                    auto const &c = s.coefficients[k];
                    if (steps[j].conclusion.contradiction || (p.kind != EQ && c.is_neg()))
                        return false;
                    add(lhs, p.lhs, c);
                    constant += c * p.constant;
                    if (!c.is_zero()) {
                        strict |= is_strict(p.kind);
                        equality &= p.kind == EQ;
                    }
                }
                if (s.conclusion.contradiction) {
                    if (!lhs.empty() ||
                        !(constant.is_pos() || (strict && constant.is_zero()) || (equality && !constant.is_zero())))
                        return false;
                }
                else {
                    if (lhs != f.lhs)
                        return false;
                    mpq slack = constant - f.constant;
                    if (f.kind == EQ) {
                        if (!equality || !slack.is_zero())
                            return false;
                    }
                    else if (slack.is_neg() || (is_strict(f.kind) && !strict && slack.is_zero()))
                        return false;
                }
                break;
            }
            case rule::integer_tighten: {
                if (s.conclusion.contradiction || s.premises.size() != 1 || s.coefficients[0] != mpq(1))
                    return false;
                auto const &input = steps[s.premises[0]].conclusion;
                auto const &polynomial = facts[s.premises[0]].lhs;
                if (input.contradiction || polynomial != f.lhs || !input.rhs.y.is_zero())
                    return false;
                for (auto const &[j, c] : polynomial)
                    if (!c.is_int() || j >= variables.size() || !variables[j].is_int)
                        return false;
                mpq bound;
                if (is_upper(input.kind) && s.conclusion.kind == LE)
                    bound = input.kind == LT ? ceil(input.rhs.x) - mpq(1) : floor(input.rhs.x);
                else if (is_lower(input.kind) && s.conclusion.kind == GE)
                    bound = input.kind == GT ? floor(input.rhs.x) + mpq(1) : ceil(input.rhs.x);
                else
                    return false;
                if (s.conclusion.rhs.x != bound)
                    return false;
                break;
            }
            case rule::discharge: {
                if (s.conclusion.contradiction || s.premises.size() != 1 || s.coefficients[0] != mpq(1) ||
                    !steps[s.premises[0]].conclusion.contradiction || s.assumption >= i ||
                    steps[s.assumption].kind != rule::input)
                    return false;
                auto const &assumption = steps[s.assumption].conclusion;
                auto opposite = assumption.kind == LT   ? GE
                                : assumption.kind == LE ? GT
                                : assumption.kind == GT ? LE
                                : assumption.kind == GE ? LT
                                                        : NE;
                polynomial negated;
                add(negated, facts[s.assumption].lhs, mpq(-1));
                if (opposite != s.conclusion.kind || negated != f.lhs || facts[s.assumption].constant != -f.constant)
                    return false;
                break;
            }
            case rule::unsupported: return false;
            }
            facts.push_back(std::move(f));
        }
        return true;
    }
}  // namespace lp
