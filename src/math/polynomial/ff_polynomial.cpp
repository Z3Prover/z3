#include "math/polynomial/ff_polynomial.h"
#include <algorithm>
#include <iterator>
#include <set>
#include <queue>
#include <tuple>

namespace ff {
    void engine::collect_statistics(statistics &st) const {
        st.update("ff algebra steps", work);
        st.update("ff eliminations", m_eliminations);
        st.update("ff substitutions", m_substitutions);
        st.update("ff substituted terms", m_substituted_terms);
        st.update("ff basis calls", m_basis_calls);
        st.update("ff basis pairs", m_basis_pairs);
        st.update("ff chain skips", m_chain_skips);
        st.update("ff matrix batches", m_batches);
        st.update("ff matrix rows", m_matrix_rows);
        st.update("ff extra matrix reducers", m_extra_matrix_reducers);
        st.update("ff sparse trials", m_sparse_trials);
        st.update("ff sparse witnesses", m_sparse_witnesses);
        st.update("ff step exhaustions", m_step_exhaustions);
        st.update("ff term exhaustions", m_term_exhaustions);
        st.update("ff basis exhaustions", m_basis_exhaustions);
        st.update("ff matrix exhaustions", m_matrix_exhaustions);
        st.update("ff root calls", m_root_calls);
        st.update("ff propagated bit facts", m_bit_facts);
        st.update("ff bit rounds", m_bit_rounds);
        st.update("ff split facts", m_split_facts);
        st.update("ff minimal polynomials", m_minpolys);
        st.update("ff quotient probes", m_quotient_probes);
        st.update("ff quotient facts", m_quotient_facts);
        st.update("ff quotient exhaustions", m_quotient_exhaustions);
        st.update("ff model probes", m_model_probes);
        st.update("ff bound facts", m_bound_facts);
        st.update("ff deferred eliminations", m_deferred_eliminations);
        st.update("ff scalar fallbacks", m_scalar_fallbacks);
        st.update("ff gm skips", m_gm_skips);
        st.update("ff mask skips", m_mask_skips);
        st.update("ff bucket reductions", m_bucket_reductions);
        st.update("ff small products", m_small_products);
    }
    unsigned engine::propagate_bits(std::vector<polynomial> &eqs) {
        // Recognize the polynomial shape used by R1CS exporters as well as
        // ff.bitsum syntax. Each side must be an injective binary encoding;
        // Booleanity and the no-wrap bound are essential premises.
        std::set<unsigned> bits;
        std::map<unsigned, rational> constants;
        std::map<unsigned, std::set<unsigned>> bit_deps, constant_deps;
        rational const &prime = p;
        for (auto const &f : eqs) {
            tick();
            if (f.size() == 2) {
                // Stored coefficients are nonzero. Thus a*b^2-a*b=0
                // is equivalent to b*(b-1)=0, hence b in {0,1} in a
                // field. A merely quadratic equation is not sufficient.
                auto a = f.begin(), b = std::next(a);
                if (a->first.size() == 2 && b->first.size() == 1 && a->first[0] == a->first[1] &&
                    a->first[0] == b->first[0] && mod(a->second + b->second, prime).is_zero()) {
                    bits.insert(b->first[0]);
                    bit_deps[b->first[0]] = f.dependencies;
                }
            }
            // Direct constant equalities, including non-unit pivots. Keep
            // the original equations; contradictory pins remain conflicts.
            // c*v+k=0 fixes v=-k*c^{-1}, since the stored pivot c != 0.
            if (!f.empty() && f.size() <= 2 && f.begin()->first.size() == 1 &&
                (f.size() == 1 || std::next(f.begin())->first.empty())) {
                rational c = f.size() == 1 ? rational(0) : std::next(f.begin())->second;
                constants[f.begin()->first[0]] = mod(-c * inverse(f.begin()->second), prime);
                constant_deps[f.begin()->first[0]] = f.dependencies;
            }
        }
        unsigned before_bounds = eqs.size();
        if (bit_bounds) {
            std::vector<polynomial> facts;
            for (auto const &f : eqs) {
                tick();
                rational lo(0), hi(0), offset(0);
                std::vector<std::pair<unsigned, rational>> terms;
                auto deps = f.dependencies;
                bool valid = true;
                for (auto const &[mon, coeff] : f) {
                    tick();
                    if (mon.empty()) { offset += coeff; continue; }
                    if (mon.size() != 1) { valid = false; break; }
                    unsigned v = mon[0];
                    if (constants.contains(v)) {
                        offset += coeff * constants.at(v);
                        deps.insert(constant_deps.at(v).begin(), constant_deps.at(v).end());
                        continue;
                    }
                    if (!bits.contains(v)) { valid = false; break; }
                    deps.insert(bit_deps.at(v).begin(), bit_deps.at(v).end());
                    rational c = coeff > div(p, rational(2)) ? coeff - p : coeff;
                    terms.emplace_back(v, c);
                    if (c.is_neg()) lo += c; else hi += c;
                }
                if (!valid || terms.empty()) continue;
                offset = mod(offset, p);
                // Every Boolean assignment lies inside this signed integer
                // interval. A field zero requires an integer multiple of p.
                // Floor division works for negative endpoints too; intervals
                // spanning several multiples are allowed, with weaker inference.
                auto possible = [&](rational const &l, rational const &h) {
                    return -div(-l, p) <= div(h, p);
                };
                for (auto const &[v, c] : terms) {
                    rational l = lo - (c.is_neg() ? c : rational(0)) + offset;
                    rational h = hi - (c.is_neg() ? rational(0) : c) + offset;
                    bool zero = possible(l, h), one = possible(l + c, h + c);
                    if (zero && one) continue;
                    polynomial fact = !zero && !one ? constant(rational(1)) :
                        add(variable(v), constant(zero ? rational(0) : rational(-1)));
                    fact.dependencies = deps;
                    facts.push_back(std::move(fact));
                    ++m_bound_facts;
                }
            }
            eqs.insert(eqs.end(), facts.begin(), facts.end());
        }
        unsigned original = eqs.size();
        // If r + B = 0 and the same r + C = 0 occur, subtraction gives
        // B = C. Here B,C are linear combinations of known Boolean digits;
        // r may be a nonlinear circuit expression. Normalize by a nonzero
        // tail coefficient so scalar multiples match as well. Only emit
        // consequences that pass the existing no-wrap digit check below.
        using signature = std::vector<std::pair<monomial, rational>>;
        std::map<signature, polynomial> shared_tails;
        std::vector<polynomial> differences;
        if (bit_propagation)
            for (auto const &f : eqs) {
                polynomial tail, digits;
                for (auto const &[mon, c] : f) {
                    if (mon.empty() || (mon.size() == 1 && bits.contains(mon[0])))
                        add_term(digits, mon, c);
                    else
                        add_term(tail, mon, c);
                }
                if (tail.empty() || digits.empty())
                    continue;
                // The digit difference follows from precisely the two rows
                // with this common tail. Keep that support through scaling.
                digits.dependencies = f.dependencies;
                rational leading = tail.begin()->second;
                rational scale_by = inverse(leading);
                tail = scale(std::move(tail), scale_by);
                digits = scale(std::move(digits), scale_by);
                signature key(tail.begin(), tail.end());
                auto [it, fresh] = shared_tails.emplace(std::move(key), digits);
                if (!fresh)
                    differences.push_back(scale(add(std::move(digits), it->second, rational(-1)), leading));
            }
        for (unsigned j = 0; j < original + differences.size(); ++j) {
            tick();
            auto const &candidate = j < original ? eqs[j] : differences[j - original];
            auto premises = candidate.dependencies;
            std::map<unsigned, unsigned> positive, negative;
            rational offset(0);
            bool valid = true;
            for (auto const &[mon, coeff] : candidate) {
                if (mon.empty()) {
                    offset += coeff;
                    continue;
                }
                if (mon.size() != 1) {
                    valid = false;
                    break;
                }
                unsigned v = mon[0];
                if (auto it = constants.find(v); it != constants.end()) {
                    // Substitute a value justified by a retained equality;
                    // a pinned output may expose an otherwise hidden sum.
                    offset += coeff * it->second;
                    auto const &used = constant_deps.at(v);
                    premises.insert(used.begin(), used.end());
                    continue;
                }
                if (!bits.contains(v)) {
                    valid = false;
                    break;
                }
                auto const &used = bit_deps.at(v);
                premises.insert(used.begin(), used.end());
                bool neg = coeff > div(prime, rational(2));
                // c and -(p-c) denote the same field coefficient. Accept
                // only signed powers of two, with one bit per position on
                // each side, to obtain two ordinary binary encodings.
                rational weight = neg ? prime - coeff : coeff;
                unsigned position = 0;
                while (weight > rational(1) && mod(weight, rational(2)).is_zero()) {
                    weight = div(weight, rational(2));
                    ++position;
                }
                auto &side = neg ? negative : positive;
                if (!weight.is_one() || !side.emplace(position, v).second) {
                    valid = false;
                    break;
                }
            }
            auto contiguous = [&](auto const &side) {
                // For n Boolean digits at positions 0..n-1, the integer
                // sum lies in [0,2^n-1]. Requiring 2^n <= p keeps that
                // entire interval in [0,p-1], where reduction is injective.
                return side.empty() ||
                       (side.rbegin()->first + 1 == side.size() && rational::power_of_two(side.size()) <= prime);
            };
            if (!valid || !contiguous(positive) || !contiguous(negative))
                continue;
            offset = mod(offset, prime);
            if (positive.empty()) {
                // Multiply the whole equality by -1 to orient its sole
                // binary sum positively; negating the constant is essential.
                positive.swap(negative);
                offset = mod(-offset, prime);
            }
            if (positive.empty())
                continue;
            unsigned first = eqs.size();
            if (negative.empty()) {
                // The unique canonical target must lie in the n-bit range.
                // Outside it there is no solution; inside it uniqueness of
                // binary expansion fixes every bit to the target's digit.
                rational value = mod(-offset, prime);
                if (value >= rational::power_of_two(positive.size()))
                    eqs.push_back(constant(rational(1)));
                else
                    for (auto const &[position, v] : positive) {
                        eqs.push_back(add(variable(v), constant(-mod(value, rational(2)))));
                        value = div(value, rational(2));
                    }
            }
            // No-wrap sums equal in F_p are equal as integers. Binary
            // uniqueness identifies shared positions and forces unmatched
            // high digits to zero, even when the widths differ.
            else if (offset.is_zero() && (basis_bits || positive.size() == negative.size())) {
                for (auto const &[position, v] : positive)
                    eqs.push_back(negative.contains(position) ?
                        add(variable(v), variable(negative.at(position)), rational(-1)) : variable(v));
                for (auto const &[position, v] : negative)
                    if (!positive.contains(position)) eqs.push_back(variable(v));
            }
            // The equation, used pins and participating digit domains suffice
            // for the no-wrap deduction. Unrelated equations are not premises.
            for (unsigned i = first; i < eqs.size(); ++i)
                eqs[i].dependencies.insert(premises.begin(), premises.end());
        }
        unsigned added = eqs.size() - before_bounds;
        m_bit_facts += added;
        if (added)
            ++m_bit_rounds;
        return added;
    }

    void engine::split_consequences(std::vector<polynomial> &eqs) {
        if (work + 1 >= max_work) return;
        engine probe(p, limit, std::min(50000u, (max_work - work) / 16), std::min(max_terms, 512u),
                     false, batch_enabled, false);
        configure_probe(probe);
        std::vector<polynomial> linear, nonlinear, facts;
        for (auto const &f : eqs)
            (f.empty() || f.begin()->first.size() <= 1 ? linear : nonlinear).push_back(f);
        if (linear.empty() || nonlinear.empty()) return;
        try {
            // Each subsystem implies every member of its own ideal. Keep both
            // original subsystems and share their consequences: no independence
            // assumption is made about their variables or satisfiability.
            // Packing definitions stay in the linear subsystem during this phase.
            probe.basis(nonlinear);
            for (auto const &f : nonlinear)
                if (!f.empty() && f.begin()->first.size() <= 1) linear.push_back(f);
            probe.basis(linear);
            facts = linear;
            if (basis_bits) {
                std::set<unsigned> vars;
                for (auto const &f : linear)
                    for (auto const &[mon, c] : f) vars.insert(mon.begin(), mon.end());
                for (unsigned v : vars) {
                    auto x = probe.variable(v);
                    auto domain = probe.add(probe.mul(x, x), x, rational(-1));
                    auto reduced = probe.reduce(domain, nonlinear);
                    if (reduced.empty()) {
                        domain.dependencies = reduced.dependencies;
                        facts.push_back(std::move(domain));
                    }
                }
            }
        }
        catch (exhausted const &) { facts.clear(); }
        work += probe.steps();
        if (limit.is_canceled()) throw exhausted();
        for (auto const &f : facts)
            if (std::find(eqs.begin(), eqs.end(), f) == eqs.end()) {
                eqs.push_back(f);
                ++m_split_facts;
            }
    }

    polynomial engine::minimal_polynomial(unsigned v, std::vector<polynomial> const &bs) {
        // A zero-dimensional leading ideal contains a pure power of every
        // variable. This sufficient check avoids guessing that the quotient is
        // finite-dimensional from the absence of explicit univariate equations.
        std::set<unsigned> vars, bounded;
        for (auto const &f : bs) {
            tick();
            if (f.empty()) continue;
            auto const &lm = f.begin()->first;
            for (auto const &[mon, c] : f) {
                tick();
                vars.insert(mon.begin(), mon.end());
            }
            if (!lm.empty() && std::all_of(lm.begin(), lm.end(), [&](unsigned w) { return w == lm[0]; }))
                bounded.insert(lm[0]);
        }
        if (vars != bounded || vars.empty()) return {};
        struct row { polynomial normal, relation; };
        std::map<monomial, row, monomial_order> pivots;
        polynomial power = constant(rational(1));
        for (unsigned degree = 0; degree <= 32; ++degree) {
            polynomial r = power, relation;
            add_term(relation, monomial(degree, v), rational(1));
            while (!r.empty()) {
                auto it = pivots.find(r.begin()->first);
                if (it == pivots.end()) break;
                rational c = r.begin()->second;
                r = add(std::move(r), it->second.normal, -c);
                relation = add(std::move(relation), it->second.relation, -c);
            }
            relation.dependencies.insert(r.dependencies.begin(), r.dependencies.end());
            if (r.empty()) {
                // The same row operations act on normal forms of 1,x,... and
                // their formal powers. A zero row therefore witnesses an ideal
                // relation in x alone. It need not be the lexicographic GB.
                ++m_minpolys;
                return relation;
            }
            rational inv = inverse(r.begin()->second);
            auto lead = r.begin()->first;
            pivots.emplace(lead, row{scale(std::move(r), inv), scale(std::move(relation), inv)});
            power = reduce(mul(power, variable(v)), bs);
        }
        return {};
    }

    bool engine::small_quotient(std::vector<polynomial> const &bs, std::set<unsigned> &vars) {
        if (bs.size() > 128) return false;
        std::set<unsigned> bounded;
        unsigned terms = 0;
        for (auto const &f : bs) {
            tick();
            if (f.empty()) continue;
            terms += f.size();
            if (terms > 2048) return false;
            auto const &lm = f.begin()->first;
            if (lm.empty() || lm.size() > 64) return false;
            for (auto const &[mon, c] : f) {
                tick();
                vars.insert(mon.begin(), mon.end());
            }
            if (std::all_of(lm.begin(), lm.end(), [&](unsigned v) { return v == lm[0]; }))
                bounded.insert(lm[0]);
        }
        // Pure powers of every active variable in the leading ideal prove
        // finite dimension. A missing power is only a reason to skip this
        // heuristic, never evidence that the constraints are satisfiable.
        if (vars.empty() || vars.size() > 16 || vars != bounded) return false;
        std::vector<monomial> standard(1);
        for (unsigned i = 0; i < standard.size(); ++i) {
            for (unsigned v : vars) {
                tick();
                if (!standard[i].empty() && v < standard[i].back()) continue;
                monomial candidate = standard[i];
                candidate.push_back(v);
                bool reducible = false;
                for (auto const &f : bs) {
                    tick();
                    if (!f.empty() && std::includes(candidate.begin(), candidate.end(),
                                                    f.begin()->first.begin(), f.begin()->first.end())) {
                        reducible = true;
                        break;
                    }
                }
                // Standard monomials form an order ideal: a divisible monomial
                // has no standard descendants. Sorted extensions enumerate each
                // survivor once and bound the actual quotient dimension, rather
                // than the often much larger product of pure-power degrees.
                if (reducible) continue;
                if (standard.size() == 128) return false;
                standard.push_back(std::move(candidate));
            }
        }
        return true;
    }

    bool engine::quotient_field_basis(std::vector<polynomial> &bs) {
        std::set<unsigned> vars;
        if (!small_quotient(bs, vars)) return false;
        ++m_quotient_probes;
        std::vector<polynomial> facts;
        for (unsigned v : vars) {
            auto x = variable(v);
            polynomial power = reduce(x, bs), result = constant(rational(1));
            rational exponent = p;
            // Square and reduce modulo the original basis after each product.
            // Congruence is preserved by multiplication and reduction, so the
            // result is congruent to x^p without ever allocating degree p.
            while (!exponent.is_zero()) {
                tick();
                if (!mod(exponent, rational(2)).is_zero())
                    result = reduce(mul(result, power), bs);
                exponent = div(exponent, rational(2));
                if (!exponent.is_zero()) power = reduce(mul(power, power), bs);
            }
            auto fact = reduce(add(std::move(result), x, rational(-1)), bs);
            if (!fact.empty()) facts.push_back(std::move(fact));
        }
        if (facts.empty()) return false;
        // Every field element satisfies x^p-x=0. Each remainder differs from
        // that field axiom by an ideal combination of its recorded reducers.
        // Thus adjoining it preserves exactly the F_p solutions, including
        // nonradical ideals. Field axioms have no asserted premise; all reducer
        // dependencies are retained even when intermediate terms cancel.
        bs.insert(bs.end(), facts.begin(), facts.end());
        basis(bs);
        m_quotient_facts += facts.size();
        return true;
    }

    void engine::configure_probe(engine &probe) const {
        // Preserve representation/reduction choices without recursively enabling
        // additional search probes or giving them a new independent work budget.
        probe.bounded_elimination = bounded_elimination;
        probe.sugar_pairs = sugar_pairs;
        probe.gm_pairs = gm_pairs;
        probe.div_masks = div_masks;
        probe.geobucket = geobucket;
        probe.small_coefficients = small_coefficients;
        probe.compact_encoding = compact_encoding;
        probe.adaptive_reduction = adaptive_reduction;
        probe.adaptive_matrix = adaptive_matrix;
        probe.definition_variables = definition_variables;
        probe.root_completion = root_completion;
        probe.quotient_field = quotient_field;
    }
    void engine::tick() {
        if (++work > max_work || !limit.inc()) {
            ++m_step_exhaustions;
            throw exhausted();
        }
    }
    rational engine::coefficient_residue(rational const &a) {
        // All internal coefficients are integral. Canonical residues need no
        // division; signed and arbitrary-size intermediates keep exact mod.
        if (small_coefficients && !a.is_neg() && a < p) return a;
        return mod(a, p);
    }
    rational engine::coefficient_product(rational const &a, rational const &b) {
        if (small_coefficients && p.is_unsigned() && a.is_unsigned() && b.is_unsigned()) {
            // Here each operand and p fit in 32 bits. Their product fits in
            // uint64_t even at the largest 32-bit prime; no truncation occurs.
            ++m_small_products;
            return rational((a.get_uint64() * b.get_uint64()) % p.get_uint64(), rational::ui64());
        }
        return a * b;
    }
    void engine::add_term(polynomial &f, monomial const &mon, rational const &c) {
        // Coefficients are residues in F_p: c*t+d*t=(c+d mod p)*t.
        // A zero coefficient contributes nothing, including after cancellation.
        tick();
        rational value = coefficient_residue(c);
        if (value.is_zero())
            return;
        auto it = f.find(mon);
        if (it == f.end())
            f.emplace(mon, value);
        else {
            if (small_coefficients) {
                // Both summands are canonical residues: one subtraction is enough.
                it->second += value;
                if (it->second >= p) it->second -= p;
            }
            else it->second = mod(it->second + value, p);
            if (it->second.is_zero())
                f.erase(it);
        }
        f.sugar = std::max(f.sugar, static_cast<unsigned>(mon.size()));
        if (f.size() > max_terms || mon.size() > 1024) {
            ++m_term_exhaustions;
            throw exhausted();
        }
    }
    polynomial engine::constant(rational const &c) {
        polynomial f;
        add_term(f, {}, c);
        return f;
    }
    polynomial engine::variable(unsigned v) {
        polynomial f;
        add_term(f, {v}, rational(1));
        return f;
    }
    polynomial engine::add(polynomial a, polynomial const &b, rational const &c) {
        a.dependencies.insert(b.dependencies.begin(), b.dependencies.end());
        a.sugar = std::max(a.sugar, b.sugar);
        rational scalar = small_coefficients ? coefficient_residue(c) : c;
        for (auto const &[mon, coeff] : b)
            add_term(a, mon, coefficient_product(coeff, scalar));
        return a;
    }
    polynomial engine::scale(polynomial a, rational const &c) {
        polynomial out;
        out.dependencies = a.dependencies;
        out.sugar = a.sugar;
        rational scalar = small_coefficients ? coefficient_residue(c) : c;
        for (auto const &[mon, coeff] : a)
            add_term(out, mon, coefficient_product(coeff, scalar));
        return out;
    }
    polynomial engine::mul(polynomial const &a, polynomial const &b) {
        // Distribute over sums; a monomial is a sorted multiset of variables.
        // Merging preserves multiplicities, using commutativity but not x^2=x.
        polynomial out;
        out.dependencies = a.dependencies;
        out.dependencies.insert(b.dependencies.begin(), b.dependencies.end());
        out.sugar = a.sugar + b.sugar;
        for (auto const &[ma, ca] : a)
            for (auto const &[mb, cb] : b) {
                monomial mon;
                std::merge(ma.begin(), ma.end(), mb.begin(), mb.end(), std::back_inserter(mon));
                add_term(out, mon, coefficient_product(ca, cb));
            }
        return out;
    }
    rational engine::inverse(rational a) {
        // Extended Euclid yields t*a+k*p=gcd(a,p). Only gcd=1 permits
        // division; then t mod p is the inverse. Noninvertibility must not
        // silently become a rewrite (the field contract requires prime p).
        rational r = p, t(0), s(1);
        a = mod(a, p);
        if (small_coefficients && a.is_one()) return a;
        while (!a.is_zero()) {
            tick();
            rational q = div(r, a), next = r - q * a;
            r = a;
            a = next;
            next = t - q * s;
            t = s;
            s = next;
        }
        if (!r.is_one())
            throw exhausted();
        return mod(t, p);
    }
    rational engine::evaluate(polynomial const &a, std::vector<rational> const &values) {
        rational out(0);
        for (auto const &[mon, coeff] : a) {
            rational c = coeff;
            for (unsigned v : mon) {
                tick();
                c = mod(c * values[v], p);
            }
            out = mod(out + c, p);
        }
        return out;
    }
    polynomial engine::substitute(polynomial const &f, unsigned v, polynomial const &value) {
        // Replace each c*m*v^d by c*m*value^d. Under v=value this is
        // polynomial evaluation's substitution law, valid for both =0 and !=0.
        // The substituted definition carries its premise dependencies with it.
        ++m_substitutions;
        m_substituted_terms += f.size();
        polynomial out;
        out.dependencies = f.dependencies;
        for (auto const &[mon, coeff] : f) {
            monomial rest;
            unsigned degree = 0;
            for (unsigned w : mon)
                if (w == v)
                    ++degree;
                else
                    rest.push_back(w);
            polynomial term;
            add_term(term, rest, coeff);
            for (unsigned i = 0; i < degree; ++i)
                term = mul(term, value);
            out = add(std::move(out), term);
        }
        return out;
    }
    static bool quotient(monomial const &a, monomial const &b, monomial &out) {
        if (!std::includes(a.begin(), a.end(), b.begin(), b.end()))
            return false;
        out.clear();
        std::set_difference(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(out));
        return true;
    }
    // A support mask is a necessary condition for divisibility, even when
    // variable IDs collide modulo 64. Passing the filter still requires the
    // exact multiset test, including exponent multiplicities.
    static uint64_t support_mask(monomial const &m) {
        uint64_t mask = 0;
        for (unsigned v : m) mask |= uint64_t(1) << (v % 64);
        return mask;
    }
    polynomial engine::reduce(polynomial f, std::vector<polynomial> const &bs) {
        // Each subtraction f-q*b preserves f modulo the ideal of bs. Record
        // every used reducer's premises, including steps whose terms cancel.
        polynomial rem;
        rem.dependencies = f.dependencies;
        rem.sugar = f.sugar;
        std::vector<uint64_t> masks;
        if (div_masks)
            for (auto const &b : bs) masks.push_back(b.empty() ? 0 : support_mask(b.begin()->first));
        auto find_reducer = [&](monomial const &mon, monomial &q) {
            uint64_t mask = div_masks ? support_mask(mon) : 0;
            for (unsigned j = 0; j < bs.size(); ++j) {
                if (bs[j].empty()) continue;
                if (div_masks && (mask & masks[j]) != masks[j]) { ++m_mask_skips; continue; }
                if (quotient(mon, bs[j].begin()->first, q)) return j;
            }
            return static_cast<unsigned>(bs.size());
        };
        if (geobucket) {
            ++m_bucket_reductions;
            std::vector<polynomial> buckets;
            auto put = [&](polynomial row) {
                // A bucket of level k holds at most 4*2^k terms. Merge only
                // on a capacity collision, avoiding a full accumulator merge
                // for every short multiple. Their sum is the active polynomial.
                if (row.empty()) return;
                size_t level = 0, capacity = 4;
                while (row.size() > capacity) { ++level; capacity *= 2; }
                for (;;) {
                    if (buckets.size() <= level) buckets.resize(level + 1);
                    if (buckets[level].empty()) { buckets[level] = std::move(row); return; }
                    row = add(std::move(row), buckets[level]);
                    buckets[level].clear();
                    if (row.empty()) return;
                    ++level;
                }
            };
            put(std::move(f));
            for (;;) {
                tick();
                monomial mon;
                bool found = false;
                for (auto const &b : buckets)
                    if (!b.empty() && (!found || monomial_order{}(b.begin()->first, mon))) {
                        mon = b.begin()->first; found = true;
                    }
                if (!found) break;
                rational coeff(0);
                for (auto &b : buckets)
                    if (!b.empty() && b.begin()->first == mon) {
                        coeff += b.begin()->second;
                        b.erase(b.begin());
                    }
                coeff = coefficient_residue(coeff);
                if (coeff.is_zero()) continue;
                monomial q;
                unsigned j = find_reducer(mon, q);
                if (j == bs.size()) { add_term(rem, mon, coeff); continue; }
                auto const &b = bs[j];
                rem.dependencies.insert(b.dependencies.begin(), b.dependencies.end());
                rem.sugar = std::max(rem.sugar, b.sugar + static_cast<unsigned>(q.size()));
                rational factor = coefficient_residue(-coeff * inverse(b.begin()->second));
                polynomial tail;
                // The leading term has already been removed. Add only the
                // negative multiple of the tail: exactly the same reduction.
                for (auto it = std::next(b.begin()); it != b.end(); ++it) {
                    monomial product;
                    std::merge(q.begin(), q.end(), it->first.begin(), it->first.end(), std::back_inserter(product));
                    add_term(tail, product, coefficient_product(factor, it->second));
                }
                put(std::move(tail));
            }
            return rem;
        }
        while (!f.empty()) {
            tick();
            auto [mon, coeff] = *f.begin();
            monomial q;
            unsigned j = find_reducer(mon, q);
            if (j == bs.size()) {
                add_term(rem, mon, coeff);
                f.erase(f.begin());
            }
            else {
                auto const &b = bs[j];
                polynomial factor;
                add_term(factor, q, -coeff * inverse(b.begin()->second));
                rem.dependencies.insert(b.dependencies.begin(), b.dependencies.end());
                rem.sugar = std::max(rem.sugar, b.sugar + static_cast<unsigned>(q.size()));
                f = add(std::move(f), mul(factor, b));
            }
        }
        return rem;
    }
    std::vector<polynomial> engine::batch_reduce(std::vector<polynomial> const &rows,
                                                 std::vector<polynomial> const &bs) {
        ++m_batches;
        SASSERT(p.is_unsigned());
        uint64_t prime = p.get_uint64();
        std::set<monomial, monomial_order> columns, pending;
        std::vector<polynomial> reducers;
        size_t symbolic_bytes = 0;
        constexpr size_t symbolic_limit = 16 * 1024 * 1024;
        auto charge = [&](size_t count, size_t bytes) {
            // Saturating admission check avoids multiplication overflow. This
            // is a conservative storage allowance, not an allocator measurement.
            if (count > (symbolic_limit - symbolic_bytes) / bytes) {
                ++m_matrix_exhaustions;
                throw exhausted();
            }
            symbolic_bytes += count * bytes;
        };
        auto charge_header = [&](polynomial const &f) {
            // Include old plus new vector capacity during reallocation,
            // tree-node links/alignment and
            // premise nodes. Coefficients are canonical <2^32 here; the term
            // allowance includes rational and small-integer backing storage.
            charge(3, sizeof(polynomial));
            charge(f.dependencies.size(), 64);
        };
        auto charge_term = [&](monomial const &mon) {
            charge(1, 128);
            charge(mon.capacity(), sizeof(unsigned));
        };
        if (adaptive_matrix)
            for (auto const &f : rows) {
                charge_header(f);
                for (auto const &[mon, c] : f) charge_term(mon);
            }
        std::vector<uint64_t> masks;
        if (div_masks)
            for (auto const &b : bs) masks.push_back(b.empty() ? 0 : support_mask(b.begin()->first));
        auto discover = [&](polynomial const &f) {
            for (auto const &[mon, coefficient] : f) {
                tick();
                if (adaptive_matrix) {
                    if (!columns.contains(mon)) {
                        // Reserve four copies: columns, pending, the later
                        // column-index tree and indexed monomial vector. Keep
                        // charging erased pending entries; this overestimates
                        // live storage and never weakens the bound.
                        charge(4, 64 + sizeof(monomial));
                        charge(mon.capacity(), 4 * sizeof(unsigned));
                        columns.insert(mon);
                        pending.insert(mon);
                    }
                }
                else if (columns.insert(mon).second) pending.insert(mon);
                if (columns.size() > static_cast<size_t>(max_terms) * 4) {
                    ++m_matrix_exhaustions;
                    throw exhausted();
                }
            }
        };
        for (auto const &f : rows)
            discover(f);
        // F4 symbolic preprocessing: for every reducible matrix monomial M,
        // add one row (M/lm(g))*g from the existing basis and discover its tail.
        // These rows belong to the old ideal. A monomial is processed once;
        // generated tails decrease in the admissible monomial order.
        while (!pending.empty()) {
            tick();
            monomial mon = *pending.begin();
            pending.erase(pending.begin());
            uint64_t mask = div_masks ? support_mask(mon) : 0;
            for (unsigned j = 0; j < bs.size(); ++j) {
                auto const &b = bs[j];
                if (b.empty()) continue;
                if (div_masks && (mask & masks[j]) != masks[j]) { ++m_mask_skips; continue; }
                monomial factor;
                if (!quotient(mon, b.begin()->first, factor))
                    continue;
                if (adaptive_matrix) charge_header(b);
                polynomial row;
                row.dependencies = b.dependencies;
                row.sugar = b.sugar + static_cast<unsigned>(factor.size());
                for (auto const &[tail, coefficient] : b) {
                    monomial product;
                    std::merge(factor.begin(), factor.end(), tail.begin(), tail.end(), std::back_inserter(product));
                    if (adaptive_matrix) charge_term(product);
                    add_term(row, product, coefficient);
                }
                discover(row);
                reducers.push_back(std::move(row));
                if (reducers.size() > 1024) {
                    if (!adaptive_matrix) {
                        ++m_matrix_exhaustions;
                        throw exhausted();
                    }
                    // Only the admission bound changes: the same reducer is
                    // selected in the same order and denotes the same ideal
                    // multiple. Existing column, row, work and cancellation
                    // guards remain active, including matrix elimination caps.
                    ++m_extra_matrix_reducers;
                }
                break;
            }
        }
        std::map<monomial, unsigned, monomial_order> indices;
        std::vector<monomial> monomials;
        for (auto const &mon : columns) {
            indices.emplace(mon, monomials.size());
            monomials.push_back(mon);
        }
        if (compact_matrix) {
            struct packed_row {
                std::vector<std::pair<unsigned, uint64_t>> coefficients;
                std::set<unsigned> dependencies;
                unsigned sugar = 0;
            };
            std::map<unsigned, packed_row> pivots;
            std::vector<polynomial> out;
            size_t stored = 0;
            auto eliminate = [&](polynomial const &f, bool emit) {
                ++m_matrix_rows;
                packed_row row;
                row.dependencies = f.dependencies;
                row.sugar = f.sugar;
                for (auto const &[mon, c] : f) row.coefficients.emplace_back(indices.at(mon), c.get_uint64());
                while (!row.coefficients.empty()) {
                    tick();
                    auto [lead, factor] = row.coefficients.front();
                    auto it = pivots.find(lead);
                    if (it == pivots.end()) break;
                    auto const &pivot = it->second;
                    row.dependencies.insert(pivot.dependencies.begin(), pivot.dependencies.end());
                    row.sugar = std::max(row.sugar, pivot.sugar);
                    std::vector<std::pair<unsigned, uint64_t>> next;
                    next.reserve(row.coefficients.size() + pivot.coefficients.size());
                    unsigned i = 0, j = 0;
                    while (i < row.coefficients.size() || j < pivot.coefficients.size()) {
                        tick();
                        if (j == pivot.coefficients.size() || (i < row.coefficients.size() &&
                            row.coefficients[i].first < pivot.coefficients[j].first)) {
                            next.push_back(row.coefficients[i++]); continue;
                        }
                        auto [column, value] = pivot.coefficients[j++];
                        uint64_t old = i < row.coefficients.size() && row.coefficients[i].first == column ?
                            row.coefficients[i++].second : 0;
                        // Ordered merge computes exactly row-factor*pivot over
                        // F_p. p<2^32 bounds every product by uint64 capacity.
                        uint64_t c = (old + prime - factor * value % prime) % prime;
                        if (c) next.emplace_back(column, c);
                    }
                    row.coefficients = std::move(next);
                    if (row.coefficients.size() > max_terms) {
                        ++m_matrix_exhaustions; throw exhausted();
                    }
                }
                if (row.coefficients.empty()) return;
                uint64_t inv = inverse(rational(row.coefficients.front().second)).get_uint64();
                for (auto &[column, c] : row.coefficients) { tick(); c = c * inv % prime; }
                if (emit) {
                    polynomial f;
                    f.dependencies = row.dependencies;
                    f.sugar = row.sugar;
                    for (auto const &[column, c] : row.coefficients) add_term(f, monomials[column], rational(c));
                    out.push_back(std::move(f));
                }
                // Bound allocated row capacity, not just live terms. A packed
                // coefficient pair uses 16 bytes rather than an allocated tree
                // node; provenance still uses tree nodes and is charged at 48.
                stored += 16 * row.coefficients.capacity() + 48 * row.dependencies.size();
                if (stored > static_cast<size_t>(max_terms) * 64 * 48) {
                    ++m_matrix_exhaustions; throw exhausted();
                }
                unsigned column = row.coefficients.front().first;
                pivots.emplace(column, std::move(row));
            };
            for (auto const &f : reducers) eliminate(f, false);
            for (auto const &f : rows) eliminate(f, true);
            return out;
        }
        struct sparse_row {
            std::map<unsigned, uint64_t> coefficients;
            std::set<unsigned> dependencies;
            unsigned sugar = 0;
        };
        std::map<unsigned, sparse_row> pivots;
        std::vector<polynomial> out;
        size_t stored = 0;
        auto eliminate = [&](polynomial const &f, bool emit) {
            ++m_matrix_rows;
            sparse_row row;
            row.dependencies = f.dependencies;
            row.sugar = f.sugar;
            for (auto const &[mon, coefficient] : f)
                row.coefficients.emplace(indices.at(mon), coefficient.get_uint64());
            while (!row.coefficients.empty()) {
                tick();
                auto [column, factor] = *row.coefficients.begin();
                auto it = pivots.find(column);
                if (it == pivots.end())
                    break;
                auto const &pivot = it->second;
                row.dependencies.insert(pivot.dependencies.begin(), pivot.dependencies.end());
                row.sugar = std::max(row.sugar, pivot.sugar);
                for (auto const &[c, value] : pivot.coefficients) {
                    tick();
                    // Both operands are <p<2^32, so their product fits uint64.
                    // Subtract modulo p without signed arithmetic or overflow.
                    uint64_t reduced = (factor * value) % prime;
                    uint64_t next = row.coefficients[c] + prime - reduced;
                    if (next >= prime)
                        next -= prime;
                    if (next)
                        row.coefficients[c] = next;
                    else
                        row.coefficients.erase(c);
                }
                if (row.coefficients.size() > max_terms) {
                    ++m_matrix_exhaustions;
                    throw exhausted();
                }
            }
            if (row.coefficients.empty())
                return;
            uint64_t inv = inverse(rational(row.coefficients.begin()->second)).get_uint64();
            for (auto &[column, value] : row.coefficients) {
                tick();
                value = value * inv % prime;
            }
            // Row addition and nonzero scaling preserve the ideal generated
            // together with the retained old basis. Track exactly the rows used
            // in each reduction; certificates can record their multipliers in v2.
            if (emit) {
                polynomial result;
                result.dependencies = row.dependencies;
                result.sugar = row.sugar;
                for (auto const &[column, value] : row.coefficients)
                    add_term(result, monomials[column], rational(value));
                out.push_back(std::move(result));
            }
            stored += row.coefficients.size() + row.dependencies.size();
            if (stored > static_cast<size_t>(max_terms) * 64) {
                ++m_matrix_exhaustions;
                throw exhausted();
            }
            unsigned column = row.coefficients.begin()->first;
            pivots.emplace(column, std::move(row));
        };
        for (auto const &f : reducers)
            eliminate(f, false);
        for (auto const &f : rows)
            eliminate(f, true);
        return out;
    }

    void engine::basis(std::vector<polynomial> &eqs) {
        ++m_basis_calls;
        std::vector<polynomial> cache_input;
        auto cacheable = [](std::vector<polynomial> const &polys) {
            size_t terms = 0, storage = 0;
            for (auto const &f : polys) {
                terms += f.size();
                storage += f.size() + f.dependencies.size();
                for (auto const &[mon, coefficient] : f)
                    storage += mon.size();
                // Bound provenance and monomial storage as well as term count;
                // a small number of terms can carry many input dependencies.
                if (terms > 2048 || storage > 16384)
                    return false;
            }
            return true;
        };
        if (memo) {
            for (auto const &entry : memo->entries) {
                if (entry.prime != p || entry.input.size() != eqs.size())
                    continue;
                bool same = true;
                for (unsigned i = 0; i < eqs.size() && same; ++i)
                    same = entry.input[i] == eqs[i] && entry.input[i].dependencies == eqs[i].dependencies;
                // Exact polynomial equality, field modulus and premise-index
                // equality make the cached ideal and its provenance reusable.
                // No approximate fingerprint can establish a cache hit.
                if (same) {
                    eqs = entry.output;
                    ++memo->hits;
                    return;
                }
            }
            ++memo->misses;
            if (cacheable(eqs))
                cache_input = eqs;
        }
        std::vector<polynomial> bs;
        std::vector<std::pair<unsigned, unsigned>> pairs;
        bool batched = batch_enabled && p.is_unsigned();
        bool ordered = batched || sugar_pairs;
        // GM installation keeps basis rows stable. Removing a basis row would
        // invalidate deferred syzygy witnesses unless their representation were
        // transferred too; the existing autoreduction is used only without GM.
        std::map<std::pair<unsigned, unsigned>, monomial> live_pairs;
        using critical_pair = std::tuple<unsigned, unsigned, unsigned>;
        std::priority_queue<critical_pair, std::vector<critical_pair>, std::greater<critical_pair>> ranked;
        std::set<std::pair<unsigned, unsigned>> completed;
        auto pair_key = [](unsigned a, unsigned b) {
            return std::make_pair(std::min(a, b), std::max(a, b));
        };

        unsigned active_basis = 0;
        auto insert = [&](polynomial input) {
            std::vector<polynomial> pending;
            pending.push_back(std::move(input));
            for (unsigned next = 0; next < pending.size(); ++next) {
                polynomial f = reduce(std::move(pending[next]), bs);
                if (f.empty())
                    continue;
                rational c = inverse(f.begin()->second);
                f = scale(std::move(f), c);
                struct new_pair { unsigned j; monomial lcm; bool coprime; };
                std::vector<new_pair> fresh;
                auto const &right = f.begin()->first;
                for (unsigned j = 0; j < bs.size(); ++j) {
                    if (bs[j].empty()) continue;
                    auto const &left = bs[j].begin()->first;
                    monomial lcm;
                    std::set_union(left.begin(), left.end(), right.begin(), right.end(), std::back_inserter(lcm));
                    bool coprime = lcm.size() == left.size() + right.size();
                    fresh.push_back({j, std::move(lcm), coprime});
                }
                if (gm_pairs) {
                    for (auto it = live_pairs.begin(); it != live_pairs.end();) {
                        tick();
                        auto [a, b] = it->first;
                        auto const &lcm = it->second;
                        monomial la, lb;
                        std::set_union(right.begin(), right.end(), bs[a].begin()->first.begin(), bs[a].begin()->first.end(), std::back_inserter(la));
                        std::set_union(right.begin(), right.end(), bs[b].begin()->first.begin(), bs[b].begin()->first.end(), std::back_inserter(lb));
                        // Strict chain criterion: if lm(h)|lcm(a,b) and both
                        // replacement lcms are proper divisors, S(a,b) is a
                        // combination of lower-lcm pairs. Strict decrease makes
                        // deferred elimination well-founded, not circular.
                        if (la != lcm && lb != lcm && std::includes(lcm.begin(), lcm.end(), right.begin(), right.end())) {
                            it = live_pairs.erase(it); ++m_gm_skips;
                        }
                        else ++it;
                    }
                }
                for (auto const &candidate : fresh) {
                    unsigned j = candidate.j;
                    auto const &lcm = candidate.lcm;
                    bool skip = false;
                    if (gm_pairs) {
                        for (auto const &other : fresh) {
                            tick();
                            if (j == other.j) continue;
                            // Gebauer-Moeller installation retains minimal lcms
                            // among pairs with the new row. Equal lcms retain one
                            // representative, preferring a coprime (zero) pair.
                            // The chain identity uses this representative and an
                            // old-old pair. Product pairs must participate in
                            // this minimization before they are discarded.
                            bool preferred = other.lcm != lcm ||
                                (other.coprime != candidate.coprime ? other.coprime : other.j < j);
                            if (preferred && std::includes(lcm.begin(), lcm.end(), other.lcm.begin(), other.lcm.end())) {
                                skip = true; break;
                            }
                        }
                        skip |= candidate.coprime;
                    }
                    if (skip) { ++m_gm_skips; continue; }
                    if (gm_pairs) live_pairs.emplace(pair_key(j, bs.size()), lcm);
                    if (ordered) {
                        unsigned rank = sugar_pairs ? std::max(
                            bs[j].sugar + static_cast<unsigned>(lcm.size() - bs[j].begin()->first.size()),
                            f.sugar + static_cast<unsigned>(lcm.size() - right.size())) : lcm.size();
                        ranked.emplace(rank, j, bs.size());
                    }
                    else pairs.emplace_back(j, bs.size());
                }
                bs.push_back(std::move(f));
                ++active_basis;
                if (batched && !gm_pairs) {
                    // If a new leading monomial divides an old one, replace
                    // the old row by its remainder using the other rows. This
                    // preserves the ideal: old = remainder + sum(q_i*b_i).
                    // Keep stable indices for queued pairs, but discard retired
                    // row storage and ignore their stale pairs. Never simply
                    // drop a row because its leading monomial is redundant.
                    for (unsigned j = 0; j + 1 < bs.size(); ++j) {
                        if (bs[j].empty()) continue;
                        monomial factor;
                        if (!quotient(bs[j].begin()->first, bs.back().begin()->first, factor))
                            continue;
                        polynomial old = std::move(bs[j]);
                        bs[j].clear();
                        bs[j].dependencies.clear();
                        --active_basis;
                        pending.push_back(reduce(std::move(old), bs));
                    }
                }
                if (active_basis > 256 || bs.size() > 4096) {
                    ++m_basis_exhaustions;
                    throw exhausted();
                }
            }
        };
        for (auto const &f : eqs)
            insert(f);
        unsigned next_pair = 0;
        while (ordered ? !ranked.empty() : next_pair < pairs.size()) {
            if (!bs.empty() && bs.back().begin()->first.empty())
                break;
            std::vector<polynomial> rows;
            std::vector<std::pair<unsigned, unsigned>> reduced_pairs;
            unsigned degree = ordered ? std::get<0>(ranked.top()) : 0;
            do {
                ++m_basis_pairs;
                tick();
                unsigned a, b;
                if (ordered) {
                    std::tie(std::ignore, a, b) = ranked.top();
                    ranked.pop();
                }
                else std::tie(a, b) = pairs[next_pair++];
                if (gm_pairs && !live_pairs.erase(pair_key(a, b))) continue;
                if (bs[a].empty() || bs[b].empty()) continue;
                auto const &ma = bs[a].begin()->first;
                auto const &mb = bs[b].begin()->first;
                monomial common, lcm;
                std::set_intersection(ma.begin(), ma.end(), mb.begin(), mb.end(), std::back_inserter(common));
                // Relatively-prime leading monomials have commuting reductions;
                // their S-polynomial reduces to zero (the product criterion).
                if (common.empty()) {
                    completed.insert(pair_key(a, b));
                    continue;
                }
                std::set_union(ma.begin(), ma.end(), mb.begin(), mb.end(), std::back_inserter(lcm));
                bool chained = false;
                for (unsigned k = 0; k < bs.size(); ++k) {
                    if (bs[k].empty() || k == a || k == b || !completed.contains(pair_key(a, k)) ||
                        !completed.contains(pair_key(b, k)))
                        continue;
                    auto const &mk = bs[k].begin()->first;
                    if (std::includes(lcm.begin(), lcm.end(), mk.begin(), mk.end())) {
                        // The chain identity expresses S(a,b) using S(a,k)
                        // and S(k,b). Both reductions must already be represented
                        // in the basis: pending rows in this batch do not qualify.
                        chained = true;
                        break;
                    }
                }
                if (chained) {
                    ++m_chain_skips;
                    completed.insert(pair_key(a, b));
                    continue;
                }
                monomial qa, qb;
                quotient(lcm, ma, qa);
                quotient(lcm, mb, qb);
                polynomial fa, fb;
                // Each monic S-polynomial is an ideal consequence. Batching
                // changes its reduction algorithm, never the input constraints.
                add_term(fa, qa, rational(1));
                add_term(fb, qb, rational(-1));
                rows.push_back(add(mul(fa, bs[a]), mul(fb, bs[b])));
                reduced_pairs.push_back(pair_key(a, b));
            } while (batched && !ranked.empty() && std::get<0>(ranked.top()) == degree && rows.size() < (compact_matrix ? 16u : 64u));
            if (batched && !rows.empty()) {
                unsigned matrix_failures = m_matrix_exhaustions;
                try { rows = batch_reduce(rows, bs); }
                catch (exhausted const &) {
                    if (!adaptive_reduction || m_matrix_exhaustions == matrix_failures || work >= max_work || limit.is_canceled())
                        throw;
                    // batch_reduce has not mutated rows or bs on failure. The
                    // original S-polynomials can therefore be reduced one by
                    // one below, preserving both the ideal and provenance. Keep
                    // all spent work charged; never suppress cancellation or a
                    // polynomial/work limit. Subsequent pairs use scalar steps.
                    ++m_scalar_fallbacks;
                    batched = false;
                }
            }
            for (auto &row : rows)
                insert(std::move(row));
            // Only completed batch outputs justify subsequent chain skips.
            completed.insert(reduced_pairs.begin(), reduced_pairs.end());
        }
        std::erase_if(bs, [](auto const &f) { return f.empty(); });
        if (memo && !cache_input.empty()) {
            if (cacheable(bs)) {
                if (memo->entries.size() == 4)
                    memo->entries.erase(memo->entries.begin());
                memo->entries.push_back({p, std::move(cache_input), bs});
            }
        }
        eqs = std::move(bs);
    }
    polynomial engine::remainder(polynomial f, polynomial const &divisor) {
        return reduce(std::move(f), {divisor});
    }
    polynomial engine::gcd(polynomial a, polynomial b) {
        // Euclid preserves the common univariate roots because a=q*b+r;
        // scaling the last nonzero remainder to monic preserves its roots.
        while (!b.empty()) {
            polynomial r = remainder(a, b);
            a = std::move(b);
            b = std::move(r);
        }
        if (a.empty())
            return a;
        rational c = inverse(a.begin()->second);
        return scale(std::move(a), c);
    }
    polynomial engine::power_mod(polynomial a, rational n, polynomial const &modulus) {
        polynomial r = constant(rational(1));
        a = remainder(std::move(a), modulus);
        while (!n.is_zero()) {
            tick();
            if (!mod(n, rational(2)).is_zero())
                r = remainder(mul(r, a), modulus);
            n = div(n, rational(2));
            if (!n.is_zero())
                a = remainder(mul(a, a), modulus);
        }
        return r;
    }
    rational engine::random_value() {
        rational r(0);
        for (unsigned i = 0; i <= p.get_num_bits() / 32; ++i) {
            random_state ^= random_state << 13;
            random_state ^= random_state >> 17;
            random_state ^= random_state << 5;
            r = mod(r * rational::power_of_two(32) + rational(random_state), p);
        }
        return r;
    }
    void engine::split_roots(polynomial const &f, unsigned v, std::vector<rational> &out) {
        unsigned degree = f.begin()->first.size();
        if (degree == 0)
            return;
        if (degree == 1) {
            auto it = f.find({});
            out.push_back(mod(-(it == f.end() ? rational(0) : it->second) * inverse(f.begin()->second), p));
            return;
        }
        // f divides X^p-X, so is square-free and splits into linear factors.
        if (p == rational(2)) {
            out.push_back(rational(0));
            out.push_back(rational(1));
            return;
        }
        for (unsigned trial = 0; trial < 64; ++trial) {
            polynomial a = add(variable(v), constant(random_value()));
            polynomial h = add(power_mod(a, div(p - rational(1), rational(2)), f), constant(rational(-1)));
            polynomial d = gcd(f, h);
            if (d.empty() || d.begin()->first.empty() || d.begin()->first.size() == degree)
                continue;
            // Exact univariate polynomial division.
            polynomial q, rem = f;
            while (!rem.empty() && rem.begin()->first.size() >= d.begin()->first.size()) {
                monomial mon(rem.begin()->first.size() - d.begin()->first.size(), v);
                rational c = mod(rem.begin()->second * inverse(d.begin()->second), p);
                polynomial term;
                add_term(term, mon, c);
                q = add(std::move(q), term);
                rem = add(std::move(rem), mul(term, d), rational(-1));
            }
            if (!rem.empty())
                throw exhausted();
            split_roots(d, v, out);
            split_roots(q, v, out);
            return;
        }
        throw exhausted();
    }

    lbool engine::solve_core(std::vector<polynomial> eqs, std::vector<polynomial> neqs, std::vector<rational> &values,
                             unsigned depth) {
        if (depth > 32)
            return l_undef;
        if (linear_split && depth == 0) split_consequences(eqs);
        std::vector<std::pair<unsigned, polynomial>> defs;
        // Sparse occurrence indices avoid rescanning every circuit equation after
        // each wire elimination. Requeue only constraints whose polynomial changed.
        using uses = std::map<unsigned, std::set<unsigned>>;
        uses eq_uses, neq_uses;
        auto variables = [](polynomial const &f) {
            std::set<unsigned> out;
            for (auto const &[mon, c] : f)
                out.insert(mon.begin(), mon.end());
            return out;
        };
        auto index = [&](uses &table, polynomial const &f, unsigned i, bool add) {
            for (unsigned v : variables(f)) {
                if (add)
                    table[v].insert(i);
                else
                    table[v].erase(i);
            }
        };
        using candidate = std::tuple<size_t, unsigned, unsigned>;
        std::priority_queue<candidate, std::vector<candidate>, std::greater<candidate>> pending;
        std::vector<unsigned> revision(eqs.size(), 0);
        for (unsigned i = 0; i < eqs.size(); ++i) {
            index(eq_uses, eqs[i], i, true);
            pending.emplace(eqs[i].size(), i, 0);
        }
        for (unsigned i = 0; i < neqs.size(); ++i)
            index(neq_uses, neqs[i], i, true);
        for (;;) {
            std::set<unsigned> bit_variables;
            if (bit_propagation)
                for (auto const &f : eqs) {
                    if (f.size() != 2)
                        continue;
                    auto a = f.begin(), b = std::next(a);
                    if (a->first.size() == 2 && b->first.size() == 1 && a->first[0] == a->first[1] &&
                        a->first[0] == b->first[0] && mod(a->second + b->second, p).is_zero())
                        bit_variables.insert(b->first[0]);
                }
            while (!pending.empty()) {
                tick();
                auto [size, i, version] = pending.top();
                pending.pop();
                if (version != revision[i])
                    continue;
                auto const &f = eqs[i];
                // The zero polynomial imposes no equality constraint. A nonzero
                // constant polynomial cannot equal zero in a field.
                if (f.empty())
                    continue;
                if (f.begin()->first.empty()) {
                    m_conflict = f.dependencies;
                    return l_false;
                }
                for (auto const &[mon, coeff] : f) {
                    if (mon.size() != 1)
                        continue;
                    unsigned v = mon[0];
                    // Keep nonlinear circuit definitions compact. Retaining an
                    // equation is always sound; eliminating this auxiliary here
                    // would immediately undo the exact definitional extension.
                    // Constants and affine aliases may still eliminate it.
                    if (compact_encoding && definition_variables.contains(v) && f.begin()->first.size() > 1)
                        continue;
                    // Keep digits explicit in wide packs and nonlinear definitions.
                    // Eliminating a digit there hides its Boolean domain before the
                    // next layer's no-wrap equality can be recognized. Constants
                    // and direct affine aliases remain safe elimination candidates.
                    if (bit_variables.contains(v) &&
                        (f.size() > 2 ||
                         std::any_of(f.begin(), f.end(), [](auto const &t) { return t.first.size() > 1; })))
                        continue;
                    bool alone = true;
                    for (auto const &[other, c] : f)
                        if (other != mon && std::binary_search(other.begin(), other.end(), v))
                            alone = false;
                    if (!alone)
                        continue;
                    // f=c*v+r with c!=0 and v absent from r is equivalent to
                    // v=-r/c. Substitute this definition everywhere and remove f:
                    // each residual model extends uniquely by the saved definition.
                    polynomial def = f;
                    def.erase(mon);
                    def = scale(std::move(def), -inverse(coeff));
                    if (bounded_elimination && !def.empty() && def.begin()->first.size() > 1) {
                        // For a monomial containing v^k, substituting an s-term
                        // degree-d definition creates at most s^k terms and
                        // raises its degree by k*(d-1). Estimate before expanding.
                        // Retaining the original equation changes no semantics;
                        // this merely delegates an expensive elimination to GB.
                        auto grows = [&](polynomial const &g) {
                            size_t terms = 0, cap = 2 * g.size() + 8;
                            size_t degree_cap = std::max(size_t(8), 2 * g.begin()->first.size());
                            for (auto const &[m, c] : g) {
                                tick();
                                unsigned power = std::count(m.begin(), m.end(), v);
                                size_t expansion = 1;
                                if (m.size() + power * (def.begin()->first.size() - 1) > degree_cap) return true;
                                for (unsigned k = 0; k < power; ++k) {
                                    if (expansion > cap / def.size()) return true;
                                    expansion *= def.size();
                                }
                                terms += expansion;
                                if (terms > cap) return true;
                            }
                            return false;
                        };
                        bool costly = false;
                        for (unsigned j : eq_uses[v])
                            if (j != i && grows(eqs[j])) { costly = true; break; }
                        if (!costly)
                            for (unsigned j : neq_uses[v])
                                if (grows(neqs[j])) { costly = true; break; }
                        if (costly) { ++m_deferred_eliminations; continue; }
                    }
                    defs.emplace_back(v, def);
                    ++m_eliminations;
                    index(eq_uses, f, i, false);
                    eqs[i].clear();
                    auto affected = eq_uses[v];
                    for (unsigned j : affected) {
                        index(eq_uses, eqs[j], j, false);
                        eqs[j] = substitute(eqs[j], v, def);
                        index(eq_uses, eqs[j], j, true);
                        pending.emplace(eqs[j].size(), j, ++revision[j]);
                    }
                    affected = neq_uses[v];
                    for (unsigned j : affected) {
                        index(neq_uses, neqs[j], j, false);
                        neqs[j] = substitute(neqs[j], v, def);
                        index(neq_uses, neqs[j], j, true);
                        if (neqs[j].empty()) {
                            m_conflict = neqs[j].dependencies;
                            return l_false;
                        }
                    }
                    break;
                }
            }
            // Elimination can expose a new equality between two packed bit vectors.
            // Alternate exact substitution and injective bit decomposition until no
            // new facts arise; never infer digit equality without Boolean domains
            // and an interval smaller than the field. The original tactic did this
            // only before elimination, missing later circuit layers.
            unsigned first = eqs.size();
            if (!bit_propagation || !propagate_bits(eqs))
                break;
            revision.resize(eqs.size(), 0);
            for (unsigned i = first; i < eqs.size(); ++i) {
                index(eq_uses, eqs[i], i, true);
                pending.emplace(eqs[i].size(), i, 0);
            }
        }
        // 0=0 is true, but a disequality simplified to 0!=0 is a conflict.
        std::erase_if(eqs, [](auto const &f) { return f.empty(); });
        for (auto const &f : neqs)
            if (f.empty()) {
                m_conflict = f.dependencies;
                return l_false;
            }
        auto restore = [&]() {
            // Earlier definitions can mention variables eliminated later;
            // reverse order ensures their values have already been restored.
            for (auto i = defs.rbegin(); i != defs.rend(); ++i)
                values[i->first] = evaluate(i->second, values);
        };
        if (eqs.empty()) {
            // A verified witness is sufficient; failed sampling never means UNSAT.
            for (unsigned trial = 0; trial < 32; ++trial) {
                for (auto &v : values)
                    v = trial < 2 ? rational(trial) : random_value();
                bool ok = true;
                for (auto const &f : neqs)
                    if (evaluate(f, values).is_zero()) {
                        ok = false;
                        break;
                    }
                if (ok) {
                    restore();
                    return l_true;
                }
            }
            return l_undef;
        }
        if ((sparse_enabled || model_search) && depth == 0) {
            std::set<unsigned> active;
            for (auto const &f : eqs)
                for (auto const &[mon, coefficient] : f)
                    active.insert(mon.begin(), mon.end());
            for (auto const &f : neqs)
                for (auto const &[mon, coefficient] : f)
                    active.insert(mon.begin(), mon.end());
            // Underdetermined systems often admit sparse witnesses. Try exact
            // univariate slices before an expensive basis: one coordinate is
            // free, a second is 1, and the rest are 0. These are SAT candidates
            // only; failed slices never justify UNSAT or a conflict dependency.
            // Bound the whole phase to a fraction of the caller's work budget.
            if (active.size() > eqs.size() && active.size() <= (model_search ? 64u : 12u) && work < max_work) {
                unsigned stop = work + (max_work - work) / 16;
                for (unsigned pivot : active) {
                    for (unsigned anchor : active) {
                        if (anchor == pivot || work + 1 >= stop)
                            continue;
                        ++m_sparse_trials;
                        auto slice = [&](std::vector<polynomial> const &polys) {
                            std::vector<polynomial> out;
                            for (auto const &f : polys) {
                                polynomial r;
                                for (auto const &[mon, coefficient] : f) {
                                    tick();
                                    if (std::any_of(mon.begin(), mon.end(), [&](unsigned v) { return v != pivot && v != anchor; }))
                                        continue;
                                    monomial powers(std::count(mon.begin(), mon.end(), pivot), pivot);
                                    add_term(r, powers, coefficient);
                                }
                                out.push_back(std::move(r));
                            }
                            return out;
                        };
                        auto sliced_eqs = slice(eqs), sliced_neqs = slice(neqs);
                        if (work + 1 >= stop)
                            break;
                        engine probe(p, limit, std::min(8192u, stop - work - 1), max_terms, bit_propagation, batch_enabled, false);
                        configure_probe(probe);
                        std::vector<rational> trial(values.size());
                        lbool status = l_undef;
                        try { status = probe.solve(sliced_eqs, sliced_neqs, trial); }
                        catch (exhausted const &) {}
                        work += probe.steps();
                        if (limit.is_canceled())
                            throw exhausted();
                        if (status != l_true)
                            continue;
                        rational root = trial[pivot];
                        std::fill(trial.begin(), trial.end(), rational(0));
                        trial[pivot] = root;
                        trial[anchor] = rational(1);
                        bool valid = true;
                        for (auto const &f : eqs)
                            valid &= evaluate(f, trial).is_zero();
                        for (auto const &f : neqs)
                            valid &= !evaluate(f, trial).is_zero();
                        if (valid) {
                            ++m_sparse_witnesses;
                            values = std::move(trial);
                            restore();
                            return l_true;
                        }
                    }
                }
            }
        }
        basis(eqs);
        if (quotient_field && depth == 0 && work < max_work) {
            engine probe(p, limit, std::min(50000u, (max_work - work) / 16),
                         std::min(max_terms, 512u), false, batch_enabled, false);
            configure_probe(probe);
            auto completed = eqs;
            bool changed = false;
            try { changed = probe.quotient_field_basis(completed); }
            catch (exhausted const &) { ++m_quotient_exhaustions; }
            work += probe.steps();
            m_quotient_probes += probe.m_quotient_probes;
            if (limit.is_canceled()) throw exhausted();
            // Commit only a completed basis. Local resource exhaustion leaves
            // the original equations intact; shared cancellation still escapes.
            if (changed) {
                eqs = std::move(completed);
                m_quotient_facts += probe.m_quotient_facts;
            }
        }
        for (auto const &f : eqs)
            if (!f.empty() && f.begin()->first.empty()) {
                m_conflict = f.dependencies;
                return l_false;
            }
        if (basis_bits) {
            auto augmented = eqs;
            if (propagate_bits(augmented)) {
                bool fresh = false;
                for (unsigned i = eqs.size(); i < augmented.size(); ++i)
                    fresh |= std::find(eqs.begin(), eqs.end(), augmented[i]) == eqs.end();
                if (fresh) {
                    lbool result = solve_core(std::move(augmented), neqs, values, depth + 1);
                    if (result == l_true) restore();
                    return result;
                }
            }
        }
        if (model_search || root_completion) {
            bool has_univariate = false;
            for (auto const &f : eqs) {
                if (f.empty()) continue;
                unsigned v = f.begin()->first[0];
                has_univariate |= std::all_of(f.begin(), f.end(), [&](auto const &t) {
                    return std::all_of(t.first.begin(), t.first.end(), [&](unsigned w) { return w == v; });
                });
            }
            if (!has_univariate) {
                engine probe(p, limit, std::min(30000u, (max_work - std::min(work, max_work)) / 16), max_terms,
                             false, batch_enabled, false);
                configure_probe(probe);
                polynomial relation;
                try { relation = probe.minimal_polynomial(eqs.front().begin()->first[0], eqs); }
                catch (exhausted const &) {}
                work += probe.steps();
                if (limit.is_canceled()) throw exhausted();
                if (!relation.empty()) {
                    eqs.push_back(std::move(relation));
                    ++m_minpolys;
                }
            }
        }
        for (auto const &f : neqs) {
            // A zero remainder means the equalities imply f=0, contradicting
            // the asserted f!=0. The basis and disequality premises are joined.
            auto reduced = reduce(f, eqs);
            if (reduced.empty()) {
                m_conflict = reduced.dependencies;
                return l_false;
            }
        }
        for (auto const &f : eqs) {
            if (f.empty())
                continue;
            unsigned v = f.begin()->first[0];
            bool univariate = true;
            for (auto const &[mon, c] : f)
                for (unsigned w : mon)
                    if (v != w)
                        univariate = false;
            if (!univariate)
                continue;
            ++m_root_calls;
            std::vector<rational> candidates;
            bool simple = false;
            if (f.begin()->first.size() == 2 && (f.size() == 1 || (f.size() == 2 && f.rbegin()->first.empty()))) {
                rational constant = f.size() == 1 ? rational(0) : f.rbegin()->second;
                rational square = mod(-constant * inverse(f.begin()->second), p), root;
                // For nonzero a, a*X^2+c=0 iff X^2=-c/a. If that
                // residue is an integer square r^2, (X-r)*(X+r)=0
                // gives the complete field root set {r,-r}. Deduplicate
                // zero and characteristic two. An integer nonsquare says
                // nothing about modular square roots: use the general path.
                if (square.is_int_perfect_square(root)) {
                    candidates.push_back(root);
                    rational negative = mod(-root, p);
                    if (negative != root)
                        candidates.push_back(negative);
                    simple = true;
                }
            }
            // X^p-X has exactly the elements of F_p as its simple roots.
            // gcd(f,X^p-X) therefore retains precisely f's field roots; a
            // nonzero constant gcd rules out f=0 even if it has extension-field
            // roots. Exhausting all retained roots is required to conclude UNSAT.
            if (!simple) {
                polynomial roots = gcd(f, add(power_mod(variable(v), p, f), variable(v), rational(-1)));
                if (roots.empty())
                    throw exhausted();
                if (roots.begin()->first.empty()) {
                    m_conflict = f.dependencies;
                    return l_false;
                }
                split_roots(roots, v, candidates);
            }
            bool unknown = false;
            auto core = f.dependencies;
            for (auto const &r : candidates) {
                auto branch = eqs;
                branch.push_back(add(variable(v), constant(-r)));
                lbool status = solve_core(std::move(branch), neqs, values, depth + 1);
                if (status == l_true) {
                    restore();
                    return l_true;
                }
                unknown |= status == l_undef;
                if (status == l_false)
                    core.insert(m_conflict.begin(), m_conflict.end());
            }
            m_conflict = std::move(core);
            return unknown ? l_undef : l_false;
        }
        if (!neqs.empty()) {
            // Rabinowitsch witnesses turn f != 0 into f*t - 1 = 0. A unit
            // ideal proves inconsistency even without constructing witnesses:
            // f!=0 permits t=f^{-1}, and f*t=1 implies f!=0. Deriving 1=0
            // is consequently a contradiction. V1 tracks premise dependencies,
            // but does not emit the polynomial identity as a checkable certificate.
            // Keep this conflict check separate from model search: these fresh
            // variables do not belong to the caller's assignment vector.
            auto augmented = eqs;
            unsigned fresh = values.size();
            for (auto const &f : neqs) {
                if (f.begin()->first.empty())
                    continue;
                augmented.push_back(add(mul(f, variable(fresh++)), constant(rational(-1))));
            }
            basis(augmented);
            for (auto const &f : augmented)
                if (!f.empty() && f.begin()->first.empty()) {
                    m_conflict = f.dependencies;
                    return l_false;
                }
        }
        if (model_search && depth == 0) {
            std::set<unsigned> vars;
            for (auto const &f : eqs)
                for (auto const &[mon, c] : f) vars.insert(mon.begin(), mon.end());
            unsigned stop = work + (max_work - std::min(work, max_work)) / 4;
            // No dimension claim is needed for witness probes. Rotate variables
            // before values, giving each slice its own budget; a hard first
            // coordinate cannot consume all work meant for the other slices.
            // Failed or incomplete probes never justify an UNSAT answer.
            for (unsigned trial = 0; trial < 3; ++trial)
                for (unsigned v : vars) {
                    if (work + 1 >= stop) break;
                    engine probe(p, limit, std::min(12000u, stop - work - 1), max_terms,
                                 bit_propagation, batch_enabled, false);
                    configure_probe(probe);
                    auto branch = eqs;
                    branch.push_back(add(variable(v), constant(trial < 2 ? -rational(trial) : -random_value())));
                    std::vector<rational> assignment(values.size());
                    lbool status = l_undef;
                    ++m_model_probes;
                    try { status = probe.solve(branch, neqs, assignment); }
                    catch (exhausted const &) {}
                    work += probe.steps();
                    if (limit.is_canceled()) throw exhausted();
                    if (status == l_true) {
                        values = std::move(assignment);
                        restore();
                        return l_true;
                    }
                }
        }
        // Without an explicit univariate relation, try a few assignments. This
        // does not establish positive dimension. Failed guesses say nothing
        // about satisfiability; the complete fallback handles the remainder.
        unsigned v = eqs.front().begin()->first.front();
        for (unsigned trial = 0; trial < 3; ++trial) {
            auto branch = eqs;
            rational value = trial < 2 ? rational(trial) : random_value();
            branch.push_back(add(variable(v), constant(-value)));
            if (solve_core(std::move(branch), neqs, values, depth + 1) == l_true) {
                restore();
                return l_true;
            }
        }
        return l_undef;
    }
    lbool engine::solve(std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                        std::vector<rational> &values) {
        lbool r = solve_core(eqs, neqs, values, 0);
        if (r == l_true) {
            // Independently evaluate the input polynomials after reconstruction.
            for (auto const &f : eqs)
                if (!evaluate(f, values).is_zero())
                    return l_undef;
            for (auto const &f : neqs)
                if (evaluate(f, values).is_zero())
                    return l_undef;
        }
        return r;
    }
}  // namespace ff
