/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

Notes:

    TODO: from test_ineq_basic5:    (mod 2^4)
        Lemma: -0 \/ -1 \/ 2 \/ 3
           -0: -4 > v1 + v0         [ bvalue=l_false @0 pwatched=1  ]
           -1: v1 > 2               [ bvalue=l_false @0 pwatched=1  ]
            2: -3 <= -1*v0 + -7     [ bvalue=l_undef pwatched=0  ]
            3: -4 <= v0             [ bvalue=l_undef pwatched=0  ]

        2  ==>  v0 \not\in [0;12[
        3  ==>  v0 \not\in [13;10[
        A value is "truly" forbidden if neither branch works:
            v0 \not\in [0;12[ intersect [13;10[  ==  [0;10[
        ==> replace 2, 3 by single constraint 10 <= v0


    TODO: from bench1:
        Lemma: 12 \/ -26 \/ 292 \/ 294 \/ 295
             12: v11 <= v10 + v0                 [ l_false assert@0 pwatched active ]
            -26: v12 + -1*v11 != 0               [ l_false assert@0 pwatched active ]
            292: v10 + v0 + 1 == 0               [ l_false eval@6 pwatched active ]
            294: v12 + -1*v10 + -1*v0 + -1 == 0  [ l_undef ]
            295: v10 + v0 + 1 <= v12             [ l_undef ]

        292: v10 + v0 + 1 == 0
        294: v10 + v0 + 1 == v12
        295: v10 + v0 + 1 <= v12

        ==> drop 294 because it implies 295
        ==> drop 292 because it implies 295


    TODO from bench0:
	-43 \/ 3 \/ 4 \/ -0 \/ -44 \/ -52
		-43: v3 + -1 != 0
		3: v3 == 0
		4: v3 <= v5
		-0: v5 + v4*v3 + -1*v2*v1 != 0
		-44: v4 + -1 != 0
		-52: v2 != 0

        Drop v3 == 0 because it implies v3 - 1 != 0

    The try_recognize_bailout returns true, but fails to simplify any other literal.
    Overall, why return true immediately if there are other literals that subsume each-other?



    TODO: connect disjoint intervals
        For example, rewrite:
            p < a  \/  b <= p
            <=>  ~ (a <= p < b)
            <=>  ~ (p - a < b - a)
            <=>  p - a >= b - a
        (similar for other combinations of <, <=)

--*/
#include "math/polysat/solver.h"
#include "math/polysat/simplify_clause.h"

namespace polysat {

    simplify_clause::simplify_clause(solver& s):
        s(s)
    {}

    bool simplify_clause::apply(clause& cl) {
        LOG_H1("Simplifying clause: " << cl);
        bool simplified = false;
        if (try_remove_equations(cl))
            simplified = true;
#if 0
        if (try_recognize_bailout(cl))
            simplified = true;
#endif
        if (try_equal_body_subsumptions(cl))
            simplified = true;
#if 0 
        if (try_bit_subsumptions(cl))
            simplified = true;
#endif
        return simplified;
    }

    /**
     *  If we have:
     *      p <= q
     *      p - q == 0
     *  Then remove the equality.
     *
     *  If we have:
     *      p < q
     *      p - q == 0
     *  Then merge into p <= q.
     */
    bool simplify_clause::try_remove_equations(clause& cl) {
        LOG_H2("Remove superfluous equations from: " << cl);
        bool const has_eqn = any_of(cl, [&](sat::literal lit) { return s.lit2cnstr(lit).is_eq(); });
        if (!has_eqn)
            return false;
        bool any_removed = false;
        bool_vector& should_remove = m_bools;
        should_remove.fill(cl.size(), false);
        for (unsigned i = cl.size(); i-- > 0; ) {
            sat::literal const lit = cl[i];
            signed_constraint const c = s.lit2cnstr(lit);
            if (!c->is_ule())
                continue;
            if (c->is_eq())
                continue;
#if 1
            // Disable the case p<q && p=q for now.
            // The merging of less-than and equality may remove premises from the lemma.
            // See test_band5.
            // TODO: fix and re-enable
            if (c.is_negative())
                continue;
#endif
            LOG_V(10, "Examine: " << lit_pp(s, lit));
            pdd const p = c->to_ule().lhs();
            pdd const q = c->to_ule().rhs();
            signed_constraint const eq = s.m_constraints.find_eq(p - q);
            if (!eq)
                continue;
            auto const eq_it = std::find(cl.begin(), cl.end(), eq.blit());
            if (eq_it == cl.end())
                continue;
            unsigned eq_idx = (unsigned)std::distance(cl.begin(), eq_it);
            any_removed = true;
            should_remove[eq_idx] = true;
            if (c.is_positive()) {
                // c:  p <= q
                // eq: p == q
                LOG("Removing " << eq.blit() << ": " << eq << " because it subsumes " << cl[i] << ": " << s.lit2cnstr(cl[i]));
            }
            else {
                // c:  p > q
                // eq: p == q
                cl[i] = s.ule(q, p).blit();
                LOG("Merge " << eq.blit() << ": " << eq << " and " << lit << ": " << c << " to obtain " << cl[i] << ": " << s.lit2cnstr(cl[i]));
            }
        }
        // Remove superfluous equations
        if (!any_removed)
            return false;
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i)
            if (!should_remove[i])
                cl[j++] = cl[i];
        cl.m_literals.shrink(j);
        return true;
    }

    // If x != k appears among the new literals, all others are superfluous.
    // TODO: this seems to work for lemmas coming from forbidden intervals, but in general it's too naive (esp. for side lemmas).
    bool simplify_clause::try_recognize_bailout(clause& cl) {
        LOG_H2("Try to find bailout literal");
        pvar v = null_var;
        sat::literal eq = sat::null_literal;
        rational k;
        for (sat::literal lit : cl) {
            LOG_V(10, "Examine " << lit_pp(s, lit));
            lbool status = s.m_bvars.value(lit);
            // skip premise literals
            if (status == l_false)
                continue;
            SASSERT(status != l_true);  // would be an invalid lemma
            SASSERT_EQ(status, l_undef);  // new literal
            auto c = s.lit2cnstr(lit);
            // For now we only handle the case where exactly one variable is
            // unassigned among the new constraints
            for (pvar w : c->vars()) {
                if (s.is_assigned(w))
                    continue;
                if (v == null_var)
                    v = w;
                else if (v != w)
                    return false;
            }
            SASSERT(v != null_var);  // constraints without unassigned variables would be evaluated at this point
            if (c.is_diseq() && c.diseq().is_unilinear()) {
                pdd const& p = c.diseq();
                if (p.hi().is_one()) {
                    eq = lit;
                    k = (-p.lo()).val();
                }
            }
        }
        if (eq == sat::null_literal)
            return false;
        LOG("Found bailout literal: " << lit_pp(s, eq));
        // Keep all premise literals and the equation
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i) {
            sat::literal const lit = cl[i];
            lbool const status = s.m_bvars.value(lit);
            if (status == l_false || lit == eq)
                cl[j++] = cl[i];
            else {
                DEBUG_CODE({
                    auto a = s.get_assignment().clone();
                    a.push(v, k);
                    SASSERT(s.lit2cnstr(lit).is_currently_false(a));
                });
            }
        }
        if (j == cl.size())
            return false;
        cl.m_literals.shrink(j);
        return true;
    }

    /**
     * Abstract body of the polynomial (i.e., the variable terms without constant term)
     * by a single variable.
     *
     * abstract(2*x*y + x + 7)
     * -> v = 2*x*y + x
     *    r = x + 7
     *
     * \return Abstracted polynomial
     * \param[out] v Body
     */
    pdd simplify_clause::abstract(pdd const& p, pdd& v) {
        if (p.is_val()) {
            SASSERT(v.is_zero());
            return p;
        }
        if (p.is_unilinear()) {
            // we need an interval with coeff == 1 to be able to compare intervals easily
            auto const& coeff = p.hi().val();
            if (coeff.is_one() || coeff == p.manager().max_value()) {
                v = p.manager().mk_var(p.var());
                return p;
            }
        }
        unsigned max_var = p.var();
        auto& m = p.manager();
        pdd r(m);
        v = p - p.offset();
        r = p - v;
        auto const& lc = p.leading_coefficient();
        if (mod(-lc, m.two_to_N()) < lc) {
            v = -v;
            r -= m.mk_var(max_var);
        }
        else
            r += m.mk_var(max_var);
        return r;
    }

    void simplify_clause::prepare_subs_entry(subs_entry& entry, signed_constraint c) {
        entry.valid = false;
        if (!c->is_ule())
            return;
        forbidden_intervals fi(s);

        auto const& ule = c->to_ule();
        auto& m = ule.lhs().manager();
        signed_constraint sc = c;
        pdd v_lhs(m), v_rhs(m);
        pdd lhs = abstract(ule.lhs(), v_lhs);
        pdd rhs = abstract(ule.rhs(), v_rhs);
        if (lhs.is_val() && rhs.is_val())
            return;
        if (!lhs.is_val() && !rhs.is_val() && v_lhs != v_rhs)
            return;
        if (lhs != ule.lhs() || rhs != ule.rhs()) {
            sc = s.ule(lhs, rhs);
            if (c.is_negative())
                sc.negate();
        }
        pvar v = rhs.is_val() ? lhs.var() : rhs.var();
        VERIFY(fi.get_interval(sc, v, entry));
        if (entry.coeff != 1)
            return;
        entry.var = lhs.is_val() ? v_rhs : v_lhs;
        entry.subsuming = false;
        entry.valid = true;
    }


    /**
     * Test simple subsumption between inequalities over equal polynomials (up to the constant term),
     * i.e., subsumption between literals of the form:
     *
     *      p + n_1 <= n_2
     *      n_3 <= p + n_4
     *      p + n_5 <= p + n_6
     *
     * (p polynomial, n_i constant numbers)
     *
     * A literal C subsumes literal D (i.e, C ==> D),
     * if the forbidden interval of C is a superset of the forbidden interval of D.
     * fi(D) subset fi(C)  ==>  C subsumes D
     * If C subsumes D, remove C from the lemma.
     */
    bool simplify_clause::try_equal_body_subsumptions(clause& cl) {
        LOG_H2("Equal-body-subsumption for: " << cl);

        m_entries.reserve(cl.size());
        for (unsigned i = 0; i < cl.size(); ++i) {
            subs_entry& entry = m_entries[i];
            sat::literal lit = cl[i];
            LOG_V(10, "Literal " << lit_pp(s, lit));
            signed_constraint c = s.lit2cnstr(lit);
            prepare_subs_entry(entry, c);
        }

        // Check subsumption between intervals for the same variable
        bool any_subsumed = false;
        for (unsigned i = 0; i < cl.size(); ++i) {
            subs_entry& e = m_entries[i];
            if (e.subsuming || !e.valid)
                continue;
            for (unsigned j = 0; j < cl.size(); ++j) {
                subs_entry& f = m_entries[j];
                if (f.subsuming || !f.valid || i == j || *e.var != *f.var)
                    continue;
                if (e.interval.currently_contains(f.interval)) {
                    // f subset of e  ==>  f.src subsumed by e.src
                    LOG("Removing " << cl[i] << ": " << s.lit2cnstr(cl[i]) << " because it subsumes " << cl[j] << ": " << s.lit2cnstr(cl[j]));
                    e.subsuming = true;
                    any_subsumed = true;
                    break;
                }
            }
        }
        // Remove subsuming literals
        if (!any_subsumed)
            return false;
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i)
            if (!m_entries[i].subsuming)
                cl[j++] = cl[i];
        cl.m_literals.shrink(j);
        return true;
    }

    // decomposes into a plain constant and a part containing variables. e.g., 2*x*y + 3*z - 2 gets { 2*x*y + 3*z, -2 }
    static std::pair<pdd, pdd> decouple_constant(const pdd& p) {
        for (const auto& m : p) {
            if (m.vars.empty())
                return { p - m.coeff, p.manager().mk_val(m.coeff) };
        }
        return { p, p.manager().mk_val(0) };
    }
    
    // 2^(k - d) * x = m * 2^(k - d)
    bool simplify_clause::get_trailing_mask(pdd lhs, pdd rhs, pdd& p, trailing_bits& mask, bool pos) {
        auto lhs_decomp = decouple_constant(lhs);
        auto rhs_decomp = decouple_constant(rhs);
        
        lhs = lhs_decomp.first - rhs_decomp.first;
        rhs = rhs_decomp.second - lhs_decomp.second;
        
        SASSERT(rhs.is_val());
        
        unsigned k = lhs.manager().power_of_2(); 
        unsigned d = lhs.max_pow2_divisor();
        unsigned span = k - d;
        if (span == 0 || lhs.is_val())
            return false;
        
        p = lhs.div(rational::power_of_two(d));
        rational rhs_val = rhs.val();
        mask.bits = rhs_val / rational::power_of_two(d);
        if (!mask.bits.is_int())
            return false;
        
        auto it = p.begin();
        auto first = *it;
        it++;
        if (it == p.end()) {
            // if the lhs contains only one monomial it is of the form: odd * x = mask. We can multiply by the inverse to get the mask for x
            SASSERT(first.coeff.is_odd());
            rational inv;
            VERIFY(first.coeff.mult_inverse(lhs.power_of_2(), inv));
            p *= inv;
            mask.bits = mod2k(mask.bits * inv, span);
        }
        
        mask.length = span;
        mask.positive = pos;
        return true;
    }
    
    // 2^(k - 1) <= 2^(k - i - 1) * x (original definition) // TODO: Have this as well
    // 2^(k - i - 1) * x + 2^(k - 1) <= 2^(k - 1) - 1 (currently we test only for this form) 
    bool simplify_clause::get_bit(const pdd& lhs, const pdd& rhs, pdd& p, single_bit& bit, bool pos) {
        if (!rhs.is_val())
            return false;
        
        rational rhs_val = rhs.val() + 1;
        unsigned k = rhs.power_of_2();
        
        if (rhs_val != rational::power_of_two(k - 1))
            return false;
        
        pdd rest = lhs - rhs_val;
        unsigned d = rest.max_pow2_divisor();
        bit.position = k - d - 1;
        bit.positive = pos;
        p = rest.div(rational::power_of_two(d));
        return true;
    }

    // Compares with respect to "subsumption"
    // -1: mask1 < mask2 (e.g., 101 < 0101)
    //  0: incomparable
    //  1: mask1 > mask2
    // failure mask1 == mask2
    static int compare(const trailing_bits& mask1, const trailing_bits& mask2) {
        if (mask1.length == mask2.length) {
            SASSERT(mask1.bits != mask2.bits); // otw. we would have already eliminated the duplicate constraint
            return 0;
        }
        if (mask1.length < mask2.length) {
            for (unsigned i = 0; i < mask1.length; i++)
              if (mask1.bits.get_bit(i) != mask2.bits.get_bit(i))
                  return 0;
            return -1;
        }
        SASSERT(mask1.length > mask2.length);
        for (unsigned i = 0; i < mask2.length; i++)
            if (mask1.bits.get_bit(i) != mask2.bits.get_bit(i))
                return 0;
        return 1;
    }
    
    /**
     * Test simple subsumption between bit and parity constraints.
     *
     *   let lsb(t, d) = m := 2^(k - d)*t = m * 2^(k - d) denotes that the last (least significant) d bits of t are the binary representation of m
     *   let bit(t, i) :=  2^(k - 1) <= 2^(k - i - 1)*t
     *   TODO: 2^(k - 1 - d) <= 2^(k - i - 1)*t denotes that bits i-d...i are set to 0
     *   
     *   lsb(t, d) = m with log2(m) >= d => false
     *   
     *   parity(t) >= d denotes lsb(t, d)      = 0
     *   parity(t) <= d denotes lsb(t, d + 1) != 0
     *   
     *   parity(t) >= d1 || parity(t) >= d2 with d1 < d2 implies parity(t) >= d1
     *   parity(t) <= d1 || parity(t) <= d2 with d1 < d2 implies parity(t) <= d2
     *   
     *   parity(t) >= d1 || !bit(t, d2) with d2 < d1 implies bit(t, d2)
     *   parity(t) <= d1 ||  bit(t, d2) with d2 < d1 implies parity(t) <= d1
     *   
     *   parity(t) >= d1 || parity(t) <= d2 with d1 <= d2 implies true
     *   
     *   More generally: parity can be replaced by lsb in case we check for subsumption between the bit-masks rather than comparing the parities (special case)
     */
    bool simplify_clause::try_bit_subsumptions(clause& cl) {
        
        struct pdd_info {
            unsigned sz;
            vector<trailing_bits> leading;
            vector<single_bit> fixed_bits;
        };
        
        struct optional_pdd_hash {
            unsigned operator()(optional<pdd> const& args) const {
                return args->hash();
            }
        };
        
        ptr_vector<pdd_info> info_list;
        map<optional<pdd>, pdd_info*, optional_pdd_hash, default_eq<optional<pdd>>> info_table;
        bool is_valid = false;
        
        auto get_info = [&info_table, &info_list](const pdd& p) -> pdd_info& {
            auto it = info_table.find_iterator(optional(p));
            if (it != info_table.end())
                return *it->m_value;
            auto* info = alloc(pdd_info);
            info->sz = p.manager().power_of_2();
            info_list.push_back(info);
            info_table.insert(optional(p), info);
            return *info;
        };
        
        bool changed = false;
        bool_vector removed(cl.size(), false);
        
        for (unsigned i = 0; i < cl.size(); i++) {
            signed_constraint c = s.lit2cnstr(cl[i]);
            if (!c->is_ule())
                continue;
            trailing_bits mask;
            single_bit bit;
            pdd p = c->to_ule().lhs();
            if ((c.is_eq() || c.is_diseq()) && get_trailing_mask(c->to_ule().lhs(), c->to_ule().rhs(), p, mask, c.is_positive())) {
                if (mask.bits.bitsize() > mask.length) {
                    removed[i] = true; // skip this constraint. e.g., 2^(k-3)*x = 9*2^(k-3) is false as 9 >= 2^3
                    continue;
                }
                    
                mask.src_idx = i;
                get_info(p).leading.push_back(mask);
            }
            else if (c->is_ule() && get_bit(c->to_ule().lhs(), c->to_ule().rhs(), p, bit, c.is_positive())) {
                bit.src_idx = i;
                get_info(p).fixed_bits.push_back(bit);
            }
        }
        
        for (const auto& entry : info_list) {
            for (unsigned i = 0; i < entry->leading.size(); i++) {
                auto& p1 = entry->leading[i];
                // trailing vs. positive 
                for (unsigned j = i + 1; !removed[p1.src_idx] && j < entry->leading.size(); j++) {
                    auto& p2 = entry->leading[j];
                    if (!removed[p2.src_idx])
                        continue;
                    
                    if (p1.positive == p2.positive) {
                        int cmp = compare(p1, p2);
                        if (cmp != 0) {
                            if ((cmp == -1) == p1.positive) {
                                LOG("Removed: " << s.lit2cnstr(cl[p2.src_idx]) << " because of " << s.lit2cnstr(cl[p1.src_idx]) << "\n");
                                removed[p2.src_idx] = true;
                                changed = true;
                            }
                            else if ((cmp == 1) == p1.positive) {
                                LOG("Removed: " << s.lit2cnstr(cl[p1.src_idx]) << " because of " << s.lit2cnstr(cl[p2.src_idx]) << "\n");
                                removed[p1.src_idx] = true;
                                changed = true;
                            }
                        }
                    }
                    else {
                        auto& pos = p1.positive ? p1 : p2; 
                        auto& neg = p1.positive ? p2 : p1;
                        
                        int cmp = compare(pos, neg);
                        if (cmp == -1) {
                            is_valid = true;
                            changed = true;
                            LOG("Tautology: " << s.lit2cnstr(cl[pos.src_idx]) << " and " << s.lit2cnstr(cl[neg.src_idx]) << "\n");
                            goto done;
                        }
                    }
                }
                // trailing vs. bit
                for (unsigned j = 0; !removed[p1.src_idx] && j < entry->fixed_bits.size(); j++) {
                    auto& p2 = entry->fixed_bits[j];
                    if (removed[p2.src_idx])
                        continue;
                    
                    if (p2.position >= p1.length)
                        continue;
                    
                    if (p1.positive) {
                        if (p1.bits.get_bit(p2.position) == p2.positive) {
                            LOG("Removed: " << s.lit2cnstr(cl[p1.src_idx]) << " because of " << s.lit2cnstr(cl[p2.src_idx]) << " (bit)\n");
                            removed[p1.src_idx] = true;
                            changed = true;
                        }
                    }
                    else {
                        if (p1.bits.get_bit(p2.position) != p2.positive) {
                            LOG("Removed: " << s.lit2cnstr(cl[p2.src_idx]) << " (bit) because of " << s.lit2cnstr(cl[p1.src_idx]) << "\n");
                            removed[p2.src_idx] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        
        done:
        for (auto entry : info_list)
            dealloc(entry);
        if (is_valid) {
            SASSERT(!cl.empty());
            cl.literals().clear();
            cl.literals().push_back(s.eq(s.value(rational::zero(), 1)).blit()); // an obvious tautology
            return true;
        }
        // Remove subsuming literals
        if (!changed)
            return false;
        verbose_stream() << "Bit simplified\n";
        unsigned cli = 0;
        for (unsigned i = 0; i < cl.size(); ++i)
            if (!removed[i])
                cl[cli++] = cl[i];
        cl.m_literals.shrink(cli);
        return true;
    }

#if 0
    // All variables of clause 'cl' except 'z' are assigned.
    // Goal: a possibly weaker clause that implies a restriction on z around z_val
    clause_ref simplify_clause::make_asserting(clause& cl, pvar z, rational z_val) {
        signed_constraints cz;  // constraints of 'cl' that contain 'z'
        sat::literal_vector lits;  // literals of the new clause
        for (sat::literal lit : cl) {
            signed_constraint c = s.lit2cnstr(lit);
            if (c.contains_var(z))
                cz.push_back(c);
            else
                lits.push_back(lit);
        }
        SASSERT(!cz.empty());
        if (cz.size() == 1) {
            // TODO: even in this case, if the constraint is non-linear in z, we might want to extract a maximal forbidden interval around z_val.
            return nullptr;
        }
        else {
            // multiple constraints that contain z
            find_implied_constraint(cz, z, z_val, lits);
            return clause::from_literals(std::move(lits));
        }
    }

    // Each constraint in 'cz' is univariate in 'z' under the current assignment.
    // Goal: a literal that is implied by the disjunction of cz and ensures z != z_val in viable.
    //       (plus side conditions that do not depend on z)
    void simplify_clause::find_implied_constraint(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits)
    {
        unsigned const out_lits_original_size = out_lits.size();

        forbidden_intervals fi(s);
        fi_record entry;

        auto intersection = eval_interval::full();
        bool all_unit = true;

        for (signed_constraint const& c : cz) {
            if (fi.get_interval(c, z, entry) && entry.coeff == 1) {
                intersection = intersection.intersect(entry.interval);
                for (auto const& sc : entry.side_cond)
                    out_lits.push_back(sc.blit());
            } else {
                all_unit = false;
                break;
            }
        }

        if (all_unit) {
            SASSERT(!intersection.is_currently_empty());
            // Unit intervals from all constraints
            // => build constraint from intersection of forbidden intervals
            //    z \not\in [l;u[  <=>  z - l >= u - l
            if (intersection.is_proper()) {
                auto c_new = s.ule(intersection.hi() - intersection.lo(), z - intersection.lo());
                out_lits.push_back(c_new.blit());
            }
        } else {
            out_lits.shrink(out_lits_original_size);
            find_implied_constraint_sat(cz, z, z_val, out_lits);
        }
    }

    void simplify_clause::find_implied_constraint_sat(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits)
    {
        unsigned bit_width = s.size(z);
        auto p_factory = mk_univariate_bitblast_factory();
        auto p_us = (*p_factory)(bit_width);
        auto& us = *p_us;

        // Find max z1 such that z1 < z_val and all cz true under z := z1 (and current assignment)
        rational z1 = z_val;

        for (signed_constraint const& c : cz)
            c.add_to_univariate_solver(s, us, 0);
        us.add_ult_const(z_val, false, 0);  // z1 < z_val

        // First check if any such z1 exists
        switch (us.check()) {
        case l_false:
            // No such z1 exists
            z1 = s.m_pdd[z]->max_value();  // -1
            break;
        case l_true:
            // z1 exists. Try to make it as small as possible by setting bits to 0

            for (unsigned j = bit_width; j-- > 0; ) {
                switch (us.check()) {
                case l_true:
                    // TODO
                    break;
                case l_false:
                    // TODO
                    break;
                default:
                    UNREACHABLE();  // TODO: see below
                }
            }

            break;
        default:
            UNREACHABLE();  // TODO: should we link the child solver's resources to polysat's resource counter?
        }

        // Find min z2 such that z2 > z_val and all cz true under z := z2 (and current assignment)
        // TODO
    }
#endif

}
