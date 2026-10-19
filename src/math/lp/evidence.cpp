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

        bool read_bound(evidence_manager::proof_step const &s, unsigned index, lpvar j, bool lower,
                        std::vector<polynomial> const &variables, vector<evidence_manager::proof_step> const &steps,
                        mpq &value, bool &open) {
            if (index >= s.premises.size() || j >= variables.size() || s.coefficients[index] != mpq(1))
                return false;
            auto const &f = steps[s.premises[index]].conclusion;
            if (f.contradiction || (f.kind != EQ && !(lower ? is_lower(f.kind) : is_upper(f.kind))))
                return false;
            normalized b;
            if (!normalize(f, variables, b))
                return false;
            polynomial expected;
            add(expected, variables[j], mpq(lower && f.kind != EQ ? -1 : 1));
            if (expected != b.lhs)
                return false;
            value = f.rhs.x;
            open = is_strict(f.kind);
            return true;
        }

        bool check_lattice(evidence_manager::proof_step const &s, std::vector<polynomial> const &variables,
                           vector<evidence_manager::variable> const &declarations,
                           vector<evidence_manager::proof_step> const &steps, normalized const &conclusion) {
            normalized identity;
            if (s.conclusion.contradiction || (s.conclusion.kind != LE && s.conclusion.kind != GE) ||
                s.pivot >= variables.size() || !s.divisor.is_pos() || s.equation.kind != EQ ||
                s.equation.contradiction || !normalize(s.equation, variables, identity) || !identity.lhs.empty() ||
                !identity.constant.is_zero())
                return false;
            polynomial row;
            for (auto const &[c, j] : s.equation.lhs)
                row[j] += c;
            if (row[s.pivot] != mpq(-1))
                return false;
            bool upper = s.conclusion.kind == LE, source_found = false, source_open = false;
            mpq source, constant(0);
            std::map<lpvar, mpq> fixed;
            for (auto const &b : s.bounds) {
                if (!row.contains(b.column))
                    return false;
                if (b.column == s.pivot) {
                    if (source_found || !read_bound(s, upper ? b.upper : b.lower, b.column, !upper, variables, steps,
                                                    source, source_open))
                        return false;
                    source_found = true;
                    continue;
                }
                mpq lo, hi;
                bool lo_open, hi_open;
                if (!read_bound(s, b.lower, b.column, true, variables, steps, lo, lo_open) ||
                    !read_bound(s, b.upper, b.column, false, variables, steps, hi, hi_open) || lo != hi || lo_open ||
                    hi_open || !fixed.emplace(b.column, lo).second)
                    return false;
            }
            if (!source_found)
                return false;
            polynomial integral;
            for (auto const &[j, c] : row) {
                if (j == s.pivot)
                    continue;
                auto value = fixed.find(j);
                if (value != fixed.end())
                    constant += c * value->second;
                else
                    add(integral, variables[j], c / s.divisor);
            }
            for (auto const &[j, c] : integral)
                if (!c.is_int() || !declarations[j].is_int)
                    return false;
            mpq quotient = (source - constant) / s.divisor;
            mpq rounded = upper ? (source_open ? ceil(quotient) - mpq(1) : floor(quotient))
                                : (source_open ? floor(quotient) + mpq(1) : ceil(quotient));
            polynomial lhs;
            add(lhs, variables[s.pivot], mpq(upper ? 1 : -1));
            return conclusion.lhs == lhs && s.conclusion.rhs.x == s.divisor * rounded + constant;
        }

        bool check_gomory(evidence_manager::proof_step const &s, std::vector<polynomial> const &variables,
                          vector<evidence_manager::variable> const &declarations,
                          vector<evidence_manager::proof_step> const &steps, normalized const &conclusion) {
            normalized equation;
            if (s.conclusion.contradiction || s.conclusion.kind != GE || s.equation.kind != EQ ||
                s.equation.contradiction || !normalize(s.equation, variables, equation) || !equation.lhs.empty() ||
                !equation.constant.is_zero() || s.pivot >= variables.size() || !declarations[s.pivot].is_int)
                return false;
            polynomial row;
            for (auto const &[c, j] : s.equation.lhs)
                row[j] += c;
            if (row[s.pivot] != mpq(1))
                return false;
            std::map<lpvar, evidence_manager::column_bounds> bounds;
            for (auto const &b : s.bounds)
                if (b.column == s.pivot || !row.contains(b.column) || !bounds.emplace(b.column, b).second)
                    return false;
            auto bound_value = [&](unsigned index, lpvar j, bool lower, mpq &value) {
                bool open;
                return read_bound(s, index, j, lower, variables, steps, value, open);
            };
            struct shifted_column {
                lpvar column;
                mpq coefficient, shift;
                bool lower;
            };
            std::vector<shifted_column> shifted;
            mpq offset(0);
            for (auto const &[j, c] : row) {
                if (j == s.pivot || c.is_zero())
                    continue;
                auto found = bounds.find(j);
                mpq lower, upper;
                bool has_lower = found != bounds.end() && found->second.lower != UINT_MAX;
                bool has_upper = found != bounds.end() && found->second.upper != UINT_MAX;
                if ((has_lower && !bound_value(found->second.lower, j, true, lower)) ||
                    (has_upper && !bound_value(found->second.upper, j, false, upper)))
                    return false;
                if (has_lower && has_upper) {
                    if (lower != upper)
                        return false;
                    offset -= c * lower;
                    continue;
                }
                if (declarations[j].is_int && c.is_int())
                    continue;
                if (!has_lower && !has_upper)
                    return false;
                mpq shift = has_lower ? lower : upper;
                if (declarations[j].is_int && !shift.is_int())
                    return false;
                offset -= c * shift;
                shifted.push_back({j, c, shift, has_lower});
            }
            mpq fraction = offset - floor(offset);
            if (!fraction.is_pos() || fraction >= mpq(1))
                return false;
            evidence_manager::fact expected;
            expected.kind = GE;
            expected.rhs = impq(mpq(1));
            for (auto const &b : shifted) {
                mpq direction = b.lower ? -b.coefficient : b.coefficient;
                mpq weight;
                if (declarations[b.column].is_int) {
                    mpq part = direction - floor(direction);
                    mpq left = part / (mpq(1) - fraction), right = (mpq(1) - part) / fraction;
                    weight = left < right ? left : right;
                }
                else
                    weight = direction.is_pos() ? direction / (mpq(1) - fraction) : -direction / fraction;
                if (!b.lower)
                    weight.neg();
                expected.lhs.push_back({weight, b.column});
                expected.rhs.x += weight * b.shift;
            }
            normalized result;
            return normalize(expected, variables, result) && result.lhs == conclusion.lhs &&
                   result.constant == conclusion.constant;
        }

        struct interval {
            mpq lo, hi;
            bool lo_open = false, hi_open = false;
            bool lo_inf = false, hi_inf = false;
        };

        bool contains_zero(interval const &a) {
            return (a.lo_inf || a.lo.is_neg() || (a.lo.is_zero() && !a.lo_open)) &&
                   (a.hi_inf || a.hi.is_pos() || (a.hi.is_zero() && !a.hi_open));
        }

        interval multiply(interval const &a, interval const &b) {
            struct endpoint {
                mpq value;
                int infinity;
                bool open;
                bool operator<(endpoint const &other) const {
                    return infinity != other.infinity ? infinity < other.infinity : !infinity && value < other.value;
                }
            };
            endpoint lo{mpq(0), 0, false}, hi = lo;
            bool first = true;
            for (unsigned i = 0; i < 2; ++i)
                for (unsigned j = 0; j < 2; ++j) {
                    mpq x = i ? a.hi : a.lo, y = j ? b.hi : b.lo;
                    int xi = (i ? a.hi_inf : a.lo_inf) ? (i ? 1 : -1) : 0;
                    int yi = (j ? b.hi_inf : b.lo_inf) ? (j ? 1 : -1) : 0;
                    endpoint p{mpq(0), 0, (i ? a.hi_open : a.lo_open) || (j ? b.hi_open : b.lo_open)};
                    if ((!xi && x.is_zero()) || (!yi && y.is_zero())) {
                        p.open = !(contains_zero(a) || contains_zero(b));
                    }
                    else if (xi || yi) {
                        int xs = xi ? xi : (x.is_pos() ? 1 : -1);
                        int ys = yi ? yi : (y.is_pos() ? 1 : -1);
                        p.infinity = xs * ys;
                        p.open = true;
                    }
                    else {
                        p.value = x * y;
                        if (p.value.is_zero() && (contains_zero(a) || contains_zero(b)))
                            p.open = false;
                    }
                    if (first || p < lo)
                        lo = p;
                    else if (!(lo < p))
                        lo.open &= p.open;
                    if (first || hi < p)
                        hi = p;
                    else if (!(p < hi))
                        hi.open &= p.open;
                    first = false;
                }
            return {lo.value, hi.value, lo.open, hi.open, lo.infinity != 0, hi.infinity != 0};
        }

        interval exponentiate(interval const &a, unsigned p) {
            mpq lo = power(a.lo, p), hi = power(a.hi, p);
            if (p % 2)
                return {lo, hi, a.lo_open, a.hi_open, a.lo_inf, a.hi_inf};
            interval result;
            result.hi_inf = a.lo_inf || a.hi_inf;
            result.hi = lo > hi ? lo : hi;
            result.hi_open = (lo != result.hi || a.lo_open) && (hi != result.hi || a.hi_open);
            if (!a.lo_inf && a.lo.is_pos()) {
                result.lo = lo;
                result.lo_open = a.lo_open;
            }
            else if (!a.hi_inf && a.hi.is_neg()) {
                result.lo = hi;
                result.lo_open = a.hi_open;
            }
            else {
                result.lo = mpq(0);
                result.lo_open = !contains_zero(a);
            }
            return result;
        }

        bool check_monomial(evidence_manager::proof_step const &s, std::vector<polynomial> const &variables,
                            vector<evidence_manager::proof_step> const &steps,
                            vector<evidence_manager::monomial> const &definitions, normalized const &conclusion) {
            if (s.conclusion.contradiction || s.definition >= definitions.size())
                return false;
            auto const &definition = definitions[s.definition];
            if (definition.column >= variables.size() || s.pivot >= variables.size())
                return false;
            std::map<lpvar, unsigned> powers;
            for (auto j : definition.factors) {
                if (j >= variables.size())
                    return false;
                ++powers[j];
            }
            lpvar source = s.source == UINT_MAX ? definition.column : s.source;
            mpq multiplier(1), shift(0);
            if (s.source != UINT_MAX) {
                normalized identity;
                if (s.kind != evidence_manager::rule::monomial_interval || source >= variables.size() ||
                    powers.size() != 2 || definition.factors.size() != 2 || !powers.contains(s.pivot) ||
                    source == definition.column || powers.contains(source) || s.equation.kind != EQ ||
                    s.equation.contradiction || !normalize(s.equation, variables, identity) || !identity.lhs.empty() ||
                    !identity.constant.is_zero())
                    return false;
                polynomial row;
                for (auto const &[c, j] : s.equation.lhs)
                    row[j] += c;
                lpvar other = definition.factors[0] == s.pivot ? definition.factors[1] : definition.factors[0];
                for (auto const &[j, c] : row)
                    if (j != source && j != definition.column && j != other && !c.is_zero())
                        return false;
                multiplier = -row[definition.column];
                shift = -row[other];
                if (row[source] != mpq(1) || multiplier.is_zero())
                    return false;
            }
            struct box {
                interval range{mpq(0), mpq(0), false, false, true, true};
                bool lower = false, upper = false;
            };
            std::map<lpvar, box> boxes;
            for (auto const &b : s.bounds) {
                if (b.column != definition.column && b.column != source && !powers.contains(b.column))
                    return false;
                auto [entry, fresh] = boxes.emplace(b.column, box());
                if (!fresh)
                    return false;
                auto &box = entry->second;
                box.lower = b.lower != UINT_MAX;
                box.upper = b.upper != UINT_MAX;
                box.range.lo_inf = !box.lower;
                box.range.hi_inf = !box.upper;
                if ((box.lower &&
                     !read_bound(s, b.lower, b.column, true, variables, steps, box.range.lo, box.range.lo_open)) ||
                    (box.upper &&
                     !read_bound(s, b.upper, b.column, false, variables, steps, box.range.hi, box.range.hi_open)) ||
                    (box.lower && box.upper &&
                     (box.range.lo > box.range.hi ||
                      (box.range.lo == box.range.hi && (box.range.lo_open || box.range.hi_open)))))
                    return false;
            }
            mpq fixed(1);
            unsigned unknowns = 0;
            lpvar unknown = UINT_MAX;
            for (auto const &[j, p] : powers) {
                auto const &b = boxes[j];
                if (b.lower && b.upper && b.range.lo == b.range.hi)
                    fixed *= power(b.range.lo, p);
                else {
                    unknowns += p;
                    unknown = j;
                }
            }
            if (s.kind == evidence_manager::rule::monomial_substitute) {
                if (s.conclusion.kind != EQ || (unknowns > 1 && !fixed.is_zero()))
                    return false;
                evidence_manager::fact expected;
                expected.lhs.push_back({mpq(1), definition.column});
                if (unknowns && !fixed.is_zero())
                    expected.lhs.push_back({-fixed, unknown});
                else
                    expected.rhs = impq(fixed);
                normalized result;
                return normalize(expected, variables, result) && result.lhs == conclusion.lhs &&
                       result.constant == conclusion.constant;
            }
            bool upper = is_upper(s.conclusion.kind);
            if (!upper && !is_lower(s.conclusion.kind))
                return false;
            polynomial expected_lhs;
            add(expected_lhs, variables[s.pivot], mpq(upper ? 1 : -1));
            if (conclusion.lhs != expected_lhs)
                return false;
            bool upward = s.pivot == definition.column;
            if (!upward && !powers.contains(s.pivot))
                return false;
            interval product{mpq(1), mpq(1)};
            for (auto const &[j, p] : powers) {
                if (!upward && j == s.pivot)
                    continue;
                auto found = boxes.find(j);
                interval range{mpq(0), mpq(0), false, false, true, true};
                if (found != boxes.end())
                    range = found->second.range;
                product = multiply(product, exponentiate(range, p));
            }
            unsigned exponent = 1;
            interval range = product;
            if (!upward) {
                auto const &b = boxes[source];
                bool positive = !product.lo_inf && (product.lo.is_pos() || (product.lo.is_zero() && product.lo_open));
                bool negative = !product.hi_inf && (product.hi.is_neg() || (product.hi.is_zero() && product.hi_open));
                if (!positive && !negative)
                    return false;
                interval inverse;
                inverse.lo_inf = !product.hi_inf && product.hi.is_zero();
                inverse.hi_inf = !product.lo_inf && product.lo.is_zero();
                if (!product.hi_inf && !inverse.lo_inf)
                    inverse.lo = mpq(1) / product.hi;
                if (!product.lo_inf && !inverse.hi_inf)
                    inverse.hi = mpq(1) / product.lo;
                inverse.lo_open = product.hi_inf || product.hi_open;
                inverse.hi_open = product.lo_inf || product.lo_open;
                auto numerator = b.range;
                numerator.lo_inf = !b.lower;
                numerator.hi_inf = !b.upper;
                range = multiply(numerator, inverse);
                if (s.source != UINT_MAX) {
                    range.lo -= shift;
                    range.hi -= shift;
                    mpq scale = mpq(1) / multiplier;
                    range = multiply(range, {scale, scale});
                }
                exponent = powers[s.pivot];
            }
            bool strict = is_strict(s.conclusion.kind);
            mpq q = s.conclusion.rhs.x, value = power(q, exponent);
            auto above = [&](mpq const &endpoint, bool open) {
                return value > endpoint || (value == endpoint && (!strict || open));
            };
            auto below = [&](mpq const &endpoint, bool open) {
                return value < endpoint || (value == endpoint && (!strict || open));
            };
            if (exponent % 2)
                return upper ? !range.hi_inf && above(range.hi, range.hi_open)
                             : !range.lo_inf && below(range.lo, range.lo_open);
            auto const &target = boxes[s.pivot];
            if (upper)
                return !q.is_neg() ? !range.hi_inf && above(range.hi, range.hi_open)
                                   : target.upper && !target.range.hi.is_pos() && !range.lo_inf &&
                                         below(range.lo, range.lo_open);
            return !q.is_pos()
                       ? !range.hi_inf && above(range.hi, range.hi_open)
                       : target.lower && !target.range.lo.is_neg() && !range.lo_inf && below(range.lo, range.lo_open);
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
            case rule::gomory:
                if (!check_gomory(s, expanded, variables, steps, f))
                    return false;
                break;
            case rule::integer_lattice:
                if (!check_lattice(s, expanded, variables, steps, f))
                    return false;
                break;
            case rule::monomial_substitute:
            case rule::monomial_interval:
                if (!check_monomial(s, expanded, steps, monomials, f))
                    return false;
                break;
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
