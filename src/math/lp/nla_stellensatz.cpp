/*++
  Copyright (c) 2025 Microsoft Corporation



  */

#include "util/heap.h"
#include "math/dd/pdd_eval.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_coi.h"
#include "math/lp/nla_stellensatz.h"

namespace nla {

    lp::lconstraint_kind join(lp::lconstraint_kind k1, lp::lconstraint_kind k2) {
        if (k1 == k2)
            return k1;
        if (k1 == lp::lconstraint_kind::EQ)
            return k2;
        if (k2 == lp::lconstraint_kind::EQ)
            return k1;
        if ((k1 == lp::lconstraint_kind::LE && k2 == lp::lconstraint_kind::LT) ||
            (k1 == lp::lconstraint_kind::LT && k2 == lp::lconstraint_kind::LE))
            return lp::lconstraint_kind::LT;
        if ((k1 == lp::lconstraint_kind::GE && k2 == lp::lconstraint_kind::GT) ||
            (k1 == lp::lconstraint_kind::GT && k2 == lp::lconstraint_kind::GE))
            return lp::lconstraint_kind::GT;
        UNREACHABLE();
        return k1;
    }

    lp::lconstraint_kind meet(lp::lconstraint_kind k1, lp::lconstraint_kind k2) {
        if (k1 == k2)
            return k1;
        if (k1 == lp::lconstraint_kind::EQ)
            return k1;
        if (k2 == lp::lconstraint_kind::EQ)
            return k2;
        if ((k1 == lp::lconstraint_kind::LE && k2 == lp::lconstraint_kind::LT) ||
            (k1 == lp::lconstraint_kind::LT && k2 == lp::lconstraint_kind::LE))
            return lp::lconstraint_kind::LE;
        if ((k1 == lp::lconstraint_kind::GE && k2 == lp::lconstraint_kind::GT) ||
            (k1 == lp::lconstraint_kind::GT && k2 == lp::lconstraint_kind::GE))
            return lp::lconstraint_kind::GE;
        UNREACHABLE();
        return k1;
    }
    
    lpvar stellensatz::monomial_factory::mk_monomial(lp::lar_solver &lra, svector<lpvar> const &vars) {
        lpvar v = lp::null_lpvar;
        if (vars.empty())
            return v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;
        auto is_int = all_of(vars, [&](lpvar v) { return lra.var_is_int(v); });
        auto nv = lra.number_of_vars();
        v = lra.add_var(nv, is_int);
        m_vars2mon.insert(_vars, v);
        m_mon2vars.insert(v, _vars);
        return v;
    }

    lpvar stellensatz::monomial_factory::get_monomial(svector<lpvar> const &vars) {
        lpvar v = lp::null_lpvar;
        if (vars.empty())
            return v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;
        NOT_IMPLEMENTED_YET();
        return lp::null_lpvar;
    }

    void stellensatz::monomial_factory::init(lpvar v, svector<lpvar> const &_vars) {
        svector<lpvar> vars(_vars);
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, v);
        m_mon2vars.insert(v, vars);
    }

    stellensatz::stellensatz(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core), 
        pddm(core->lra_solver().number_of_vars())
    {}

    lbool stellensatz::saturate() {
        init_solver();
        TRACE(arith, display(tout << "stellensatz before saturation\n"));
        auto r = eliminate_variables();
        if (r == l_false)
            return r;
        // TODO: populate solver
        TRACE(arith, display(tout << "stellensatz after saturation\n"));
        r = m_solver.solve();
        // IF_VERBOSE(0, verbose_stream() << "stellensatz " << r << "\n");
        return r;
    }

    void stellensatz::init_solver() {
        m_constraints.reset();
        m_monomial_factory.reset();
        m_coi.init();
        m_constraint_index.reset();
        init_vars();
        init_occurs();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto sz = src.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            if (!m_coi.vars().contains(v))
                continue;
            if (c().is_monic_var(v))
                init_monomial(v);
            // assert bounds on v in the new solver.
            if (src.column_has_lower_bound(v)) {
                auto lo_bound = src.get_lower_bound(v);
                SASSERT(lo_bound.y >= 0);
                auto k   = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = src.get_column_lower_bound_witness(v);
                add_var_bound(v, k, rhs, external_justification(dep));
            }
            if (src.column_has_upper_bound(v)) {
                auto hi_bound = src.get_upper_bound(v);
                SASSERT(hi_bound.y <= 0);
                auto k   = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = src.get_column_upper_bound_witness(v);
                add_var_bound(v, k, rhs, external_justification(dep));
            }
        }
        m_occurs.reserve(sz);
    }

    dd::pdd stellensatz::to_pdd(lpvar v) {
        if (m_coi.mons().contains(v)) {
            auto& mon = c().emons()[v];
            dd::pdd prod(pddm);
            prod = 1;
            for (auto w : mon.vars())
                prod *= to_pdd(w);
            return prod;
        }
        if (m_coi.terms().contains(v)) {
            auto const& t = c().lra_solver().get_term(v);
            dd::pdd sum(pddm);
            sum = 0;
            for (auto cv : t) 
                sum += to_pdd(cv.j())*cv.coeff();
            return sum;
        }
        return pddm.mk_var(v);
    }

    stellensatz::term_offset stellensatz::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.get_monomial(vars));                
        }        
        return to;
    }

    void stellensatz::init_monomial(unsigned mon_var) {
        auto &mon = c().emons()[mon_var];
        m_monomial_factory.init(mon_var, mon.vars());
    }

    lp::constraint_index stellensatz::add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const& rhs, justification j) {
        auto p = to_pdd(v) - rhs;
        rational d(1);
        for (auto const& [c, is_constant] : p.coefficients()) 
            d = lcm(d, denominator(c));
        if (d != 1)
            p *= d;        
        return gcd_normalize(add_constraint(p, k, j));
    }

    lp::constraint_index stellensatz::add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j) {
        if (k == lp::lconstraint_kind::LE) {
            k = lp::lconstraint_kind::GE;
            p = -p;
        }
        if (k == lp::lconstraint_kind::LT) {
            k = lp::lconstraint_kind::GT;
            p = -p;
        }
        if (k == lp::lconstraint_kind::GT && is_int(p)) {
            k = lp::lconstraint_kind::GE;
            p += rational(1);
        }
        lp::constraint_index ci = lp::null_ci;
        if (m_constraint_index.find({p.index(), k}, ci))
            return ci;
        ci = m_constraints.size();
        m_constraints.push_back({p, k, j });
        m_constraint_index.insert({p.index(), k}, ci);
        return ci;
    }

    void stellensatz::add_active(lp::constraint_index ci, uint_set const &tabu) {
        if (m_active.contains(ci))
            return;
        m_active.insert(ci);
        m_tabu.reserve(ci + 1);
        m_tabu[ci] = tabu;
    }

    // initialize active set of constraints that evaluate to false in the current model
    // loop over active set to eliminate variables.
    lbool stellensatz::eliminate_variables() {
        m_active.reset();
        m_tabu.reset();
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {
            if (!constraint_is_true(ci))
                add_active(ci, uint_set());
        } 
        while (!m_active.empty()) {
            // factor ci into x*p + q <= rhs, where degree(x, q) < degree(x, p) + 1
            // if p is vanishing (evaluates to 0), then add p = 0 as assumption and reduce to q.
            // otherwise
            // find complementary constraints that contain x^k for k = 0 .. degree -1
            // eliminate x (and other variables) by combining ci with complementary constraints. 
            auto ci = m_active.elem_at(0);   
            m_active.remove(ci);     

            switch (factor(ci)) {
            case l_undef: break; 
            case l_false: return l_false;
            case l_true: continue;
            }

            auto x = select_variable_to_eliminate(ci);
            if (x == lp::null_lpvar)
                continue;
            auto f = factor(x, ci);
            TRACE(arith, tout << "factor " << m_constraints[ci].p << " -> j" << x << "^" << f.degree << " * " << f.p << "  +  "
                              << f.q << "\n");
            auto p_value = cvalue(f.p);
            if (vanishing(x, f, ci))
                continue;
            unsigned num_x = m_occurs[x].size();
            for (unsigned i = 0; i < f.degree; ++i)
                f.p *= to_pdd(x);
            auto [_m1, _f_p] = f.p.var_factors();

            for (unsigned cx = 0; cx < num_x; ++cx) {
                auto other_ci = m_occurs[x][cx]; 
                if (other_ci == ci)
                    continue;
                auto const &other_ineq = m_constraints[other_ci];
                auto g = factor(x, other_ci);
                auto p_value2 = cvalue(g.p);
                // check that p_value and p_value2 have different signs
                // check that other_ineq.lhs() is disjoint from tabu
                // compute overlaps extending x
                // 
                SASSERT(g.degree > 0);
                if (g.degree > f.degree) // future: could handle this too by considering tabu to be a map into degrees.
                    continue;
                if (p_value2 == 0)
                    continue;
                if (p_value > 0 && p_value2 > 0)
                    continue;
                if (p_value < 0 && p_value2 < 0)
                    continue;
                if (any_of(other_ineq.p.free_vars(), [&](unsigned j) { return m_tabu[ci].contains(j); }))
                    continue;

                TRACE(arith, tout << "factor (" << other_ci << ") " << other_ineq.p << " -> j" << x << "^" << g.degree
                                  << " * " << g.p
                                  << "  +  " << g.q << "\n");


                for (unsigned i = 0; i < g.degree; ++i)
                    g.p *= to_pdd(x);


                auto [m2, g_p] = g.p.var_factors();
                unsigned_vector m1m2;
                auto m1(_m1);
                auto f_p(_f_p);
                dd::pdd::merge(m1, m2, m1m2);
                SASSERT(m1m2.contains(x));
                f_p = f_p.mul(m1);
                g_p = g_p.mul(m2);

                if (!f_p.is_linear())
                    continue;
                if (!g_p.is_linear())
                    continue;

                TRACE(arith, tout << "m1 " << m1 << " m2 " << m2 << " m1m2: " << m1m2 << "\n");
                
                auto sign_f = cvalue(f_p) < 0;
                SASSERT(sign_f != cvalue(g_p) < 0);
                SASSERT(cvalue(f_p) != 0);
                SASSERT(cvalue(g_p) != 0);

                // m1m2 * f_p + f.q >= 0
                // m1m2 * g_p + g.q >= 0
                // 
                lp::constraint_index ci_a, ci_b;
                auto aj = assumption_justification();

                if (g_p.is_val())
                    ci_a = multiply(ci, pddm.mk_val(g_p.val()));
                else if (!sign_f)
                    ci_a = multiply(ci, add_constraint(g_p, lp::lconstraint_kind::LT, aj));
                else
                    ci_a = multiply(ci, add_constraint(g_p, lp::lconstraint_kind::GT, aj));

                if (f_p.is_val())
                    ci_b = multiply(other_ci, pddm.mk_val(f_p.val()));
                else if (sign_f)
                    ci_b = multiply(other_ci, add_constraint(f_p, lp::lconstraint_kind::LT, aj));
                else
                    ci_b = multiply(other_ci, add_constraint(f_p, lp::lconstraint_kind::GT, aj));
                
                auto new_ci = add(ci_a, ci_b);
                CTRACE(arith, !is_new_constraint(new_ci), display_constraint(tout << "not new ", new_ci) << "\n");
                if (!is_new_constraint(new_ci))
                    continue;
                if (m_constraints[new_ci].p.degree() <= 3)
                    init_occurs(new_ci);        
                TRACE(arith, tout << "eliminate j" << x << ":\n"; 
                    display_constraint(tout << "ci: ", ci) << "\n";
                      display_constraint(tout << "other_ci: ", other_ci) << "\n";
                      display_constraint(tout << "ci_a: ", ci_a) << "\n"; 
                      display_constraint(tout << "ci_b: ", ci_b) << "\n";
                      display_constraint(tout << "new_ci: ", new_ci) << "\n");

                if (conflict(new_ci))
                    return l_false;

                if (!constraint_is_true(new_ci)) {
                    auto const &p = m_constraints[ci].p;
                    auto const &[new_p, new_k, new_j] = m_constraints[new_ci];
                    if (new_p.degree() <= 3 && !new_p.free_vars().contains(x)) {
                        uint_set new_tabu(m_tabu[ci]), fv;
                        for (auto v : new_p.free_vars())
                            fv.insert(v);
                        for (auto v : p.free_vars())
                            if (!fv.contains(v))
                                new_tabu.insert(v);
                        add_active(new_ci, new_tabu);
                    }
                }                
            }          
        }
        return l_undef;
    }

    bool stellensatz::conflict(lp::constraint_index ci) {
        auto const &[new_p, new_k, new_j] = m_constraints[ci];
        if (new_p.is_val() && ((new_p.val() < 0 && new_k == lp::lconstraint_kind::GE) || (new_p.val() <= 0 && new_k == lp::lconstraint_kind::GT))) {
            lp::explanation ex;
            lemma_builder new_lemma(c(), "stellensatz");
            m_constraints_in_conflict.reset();
            explain_constraint(new_lemma, ci, ex);
            new_lemma &= ex;
            IF_VERBOSE(2, verbose_stream() << "stellensatz unsat \n" << new_lemma << "\n");
            TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
            c().lra_solver().settings().stats().m_nla_stellensatz++;
            return true;
        }
        return false;
    }

    bool stellensatz::vanishing(lpvar x, factorization const &f, lp::constraint_index ci) {
        if (f.q.is_zero())
            return false;
        if (f.p.is_zero())
            return false;
        auto p_value = cvalue(f.p);
        if (p_value != 0)
            return false;

        // add p = 0 as assumption and reduce to q.
        auto p_is_0 = assume(f.p, lp::lconstraint_kind::EQ);
        // ci & -p_is_0*x^f.degree  => new_ci
        dd::pdd r = pddm.mk_val(rational(-1));
        for (unsigned i = 0; i < f.degree; ++i)
            r = r * pddm.mk_var(x);
        p_is_0 = multiply(p_is_0, r);
        auto new_ci = add(ci, p_is_0);
        TRACE(arith, display_constraint(tout << "reduced", new_ci) << "\n");
        if (!is_new_constraint(new_ci))
            return false;
        init_occurs(new_ci);
        uint_set new_tabu(m_tabu[ci]);
        uint_set q_vars;
        for (auto j : f.q.free_vars())
            q_vars.insert(j);
        for (auto j : f.p.free_vars())
            if (!q_vars.contains(j))
                new_tabu.insert(j);
        add_active(new_ci, new_tabu);
        return true;
    }

    lbool stellensatz::factor(lp::constraint_index ci) {
        auto const &[p, k, j] = m_constraints[ci];
        auto [vars, q] = p.var_factors();

        auto add_new = [&](lp::constraint_index new_ci) {
            SASSERT(!constraint_is_true(new_ci));
            TRACE(arith, display_constraint(tout << "factor ", new_ci) << "\n");
            if (conflict(new_ci))
                return l_false;
            init_occurs(new_ci);
            auto new_tabu(m_tabu[ci]);
            add_active(new_ci, new_tabu);
            return l_true;
        };

        auto subst = [&](lpvar v, dd::pdd p) { 
            auto q = pddm.mk_var(v) - p;
            auto new_ci = substitute(ci, assume(q, lp::lconstraint_kind::EQ), v, p);
            return add_new(new_ci);
        };

        TRACE(arith, tout << "factor (" << ci << ") " << p << " q: " << q << " vars: " << vars << "\n");
        if (vars.empty()) {
            for (auto v : p.free_vars()) {
                if (c().val(v) == 0)
                    return subst(v, pddm.mk_val(0));
                if (c().val(v) == 1)
                    return subst(v, pddm.mk_val(1));
                if (c().val(v) == -1)
                    return subst(v, pddm.mk_val(-1));
            }
            return l_undef;
        }
        for (auto v : vars) {
            if (c().val(v) == 0)
                return subst(v, pddm.mk_val(0));
        }
        vector<dd::pdd> muls;
        muls.push_back(q);
        for (auto v : vars)
            muls.push_back(muls.back() * pddm.mk_var(v));
        auto new_ci = ci;
        SASSERT(muls.back() == p);
        for (unsigned i = vars.size(); i-- > 0;) {
            auto pv = pddm.mk_var(vars[i]);
            auto k = c().val(vars[i]) > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::LT;
            new_ci = divide(new_ci, assume(pv, k), muls[i]);
        }
        return add_new(new_ci);
    }

    bool stellensatz::is_new_constraint(lp::constraint_index ci) const {
        return ci == m_constraints.size() - 1;
    }

    lp::lpvar stellensatz::select_variable_to_eliminate(lp::constraint_index ci) {
        auto const& [p, k, j] = m_constraints[ci];
        lpvar best_var = lp::null_lpvar;
        for (auto v : p.free_vars())
            if (best_var > v)
                best_var = v;
        return best_var;
    }

    unsigned stellensatz::degree_of_var_in_constraint(lpvar var, lp::constraint_index ci) const {
        return m_constraints[ci].p.degree(var);
    }

    stellensatz::factorization stellensatz::factor(lpvar v, lp::constraint_index ci) {
        auto const& [p, k, j] = m_constraints[ci];
        auto degree = degree_of_var_in_constraint(v, ci);
        dd::pdd lc(pddm), rest(pddm);
        p.factor(v, degree, lc, rest);
        return {degree, lc, rest};
    }



    //
    // a constraint can be explained by a set of bounds used as justifications
    // and by an original constraint.
    // 
    void stellensatz::explain_constraint(lemma_builder &new_lemma, lp::constraint_index ci, lp::explanation &ex) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);
        auto &[p, k, b] = m_constraints[ci];
        if (std::holds_alternative<external_justification>(b)) {
            auto dep = std::get<external_justification>(b);
            c().lra_solver().push_explanation(dep.dep, ex);
        } 
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto& m = std::get<multiplication_justification>(b);
            explain_constraint(new_lemma, m.left, ex);
            explain_constraint(new_lemma, m.right, ex);
        } 
        else if (std::holds_alternative<division_justification>(b)) {
            auto &m = std::get<division_justification>(b);
            explain_constraint(new_lemma, m.ci, ex);
            explain_constraint(new_lemma, m.divisor, ex);
        } 
        else if (std::holds_alternative<substitute_justification>(b)) {
            auto &m = std::get<substitute_justification>(b);
            explain_constraint(new_lemma, m.ci, ex);
            explain_constraint(new_lemma, m.ci_eq, ex);
        } 
        else if (std::holds_alternative<addition_justification>(b)) {
            auto& m = std::get<addition_justification>(b);
            explain_constraint(new_lemma, m.left, ex);
            explain_constraint(new_lemma, m.right, ex);
        } 
        else if (std::holds_alternative<multiplication_poly_justification>(b)) {
            auto& m = std::get<multiplication_poly_justification>(b);
            explain_constraint(new_lemma, m.ci, ex);
        } 
        else if (std::holds_alternative<assumption_justification>(b)) {
            auto [t, coeff] = to_term_offset(p);
            new_lemma |= ineq(t, negate(k), -coeff);
        }
        else if (std::holds_alternative<gcd_justification>(b)) {
            auto& m = std::get<gcd_justification>(b);
            explain_constraint(new_lemma, m.ci, ex);
        }
        else
            UNREACHABLE();
    }
 
    rational stellensatz::cvalue(dd::pdd const& p) const {
        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned v) -> rational { return c().val(v); };
        return eval(p);
    }

    lp::constraint_index stellensatz::gcd_normalize(lp::constraint_index ci) {
        auto [p, k, j] = m_constraints[ci];
        rational g(0);
        bool _is_int = is_int(p);
        for (auto const& [c, is_constant] : p.coefficients()) 
            if (!is_constant || !_is_int)
                g = gcd(g, c);
        if (g == 0 || g == 1)
            return ci;
        switch (k) {
        case lp::lconstraint_kind::GE: {
            auto q = p * (1/ g);
            q += (ceil(q.offset()) - q.offset());
            return add_constraint(q, k, gcd_justification(ci));
        }
        case lp::lconstraint_kind::GT: {
            auto q = p;
            if (_is_int) {
                q += rational(1);
                k = lp::lconstraint_kind::GE;                
            }
            q *= (1 / g);
            q += (ceil(q.offset()) - q.offset());
            return add_constraint(q, k, gcd_justification(ci));
        }
        case lp::lconstraint_kind::LT:
        case lp::lconstraint_kind::LE:            
            UNREACHABLE();
        case lp::lconstraint_kind::EQ:
        case lp::lconstraint_kind::NE:
            if (!divides(g, p.offset()))
                return ci;
            return add_constraint(p * (1/g), k, gcd_justification(ci));
        default:
            UNREACHABLE(); 
            return ci;
        }        
    }
    
    lp::constraint_index stellensatz::assume(dd::pdd const& p, lp::lconstraint_kind k) {
        return add_constraint(p, k, assumption_justification());
    }
    
    // p1 >= lo1, p2 >= lo2 => p1 + p2 >= lo1 + lo2
    lp::constraint_index stellensatz::add(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1, j1] = m_constraints[left];
        auto const &[q, k2, j2] = m_constraints[right];
        lp::lconstraint_kind k = join(k1, k2);
        return gcd_normalize(add_constraint(p + q, k, addition_justification{left, right}));
    }

    // p >= 0  =>  a * p >= 0 if a > 0,
    // p = 0   => p * q = 0  no matter what q
    lp::constraint_index stellensatz::multiply(lp::constraint_index ci, dd::pdd q) {        
        auto const& [p, k, j] = m_constraints[ci];
        auto k1 = k;
        if (q.is_val() && q.val() < 0)
            k1 = swap_side(k1);
        SASSERT(q.is_val() || k1 == lp::lconstraint_kind::EQ);
        return add_constraint(p * q, k1, multiplication_poly_justification{ci, q});
    }

    lp::constraint_index stellensatz::multiply(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1, j1] = m_constraints[left];
        auto const &[q, k2, j2] = m_constraints[right];
        lp::lconstraint_kind k = meet(k1, k2);
        return add_constraint(p*q, k, multiplication_justification{left, right});
    }

    // p k 0, d > 0 -> p/d k 0, where q := d / d
    // q is the quotient obtained by dividing the divisor constraint, which is of the form d - 1 >= 0 or d > 0
    lp::constraint_index stellensatz::divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd q) {
        auto const &[p, k, j] = m_constraints[ci];
        return add_constraint(q, k, division_justification{ci, divisor});
    }

    lp::constraint_index stellensatz::substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v,
                                                 dd::pdd p) {
        auto const &[p1, k1, j1] = m_constraints[ci];
        auto const &[p2, k2, j2] = m_constraints[ci_eq];    
        SASSERT(k2 == lp::lconstraint_kind::EQ);
        auto q = p1.subst_pdd(v, p);
        return add_constraint(q, k1, substitute_justification{ci, ci_eq, v, p});        
    }

    void stellensatz::init_occurs() {
        m_occurs.reset();
        m_occurs.reserve(c().lra_solver().number_of_vars());
        for (lp::constraint_index ci = 0; ci < m_constraints.size(); ++ci) 
            init_occurs(ci);        
    }

    void stellensatz::init_occurs(lp::constraint_index ci) {
        if (ci == lp::null_ci)
            return;
        auto const &con = m_constraints[ci];
        for (auto v : con.p.free_vars())
            m_occurs[v].push_back(ci);
        
    }

    bool stellensatz::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return c().lra_solver().var_is_int(v); });
    }

    bool stellensatz::is_int(dd::pdd const &p) const {
        return is_int(p.free_vars());
    }

    bool stellensatz::constraint_is_true(lp::constraint_index ci) const {
        auto const& [p, k, j] = m_constraints[ci];
        auto lhs = cvalue(p);
        switch (k) {
        case lp::lconstraint_kind::GT: return lhs > 0;
        case lp::lconstraint_kind::GE: return lhs >= 0;
        case lp::lconstraint_kind::LE: return lhs <= 0;
        case lp::lconstraint_kind::LT: return lhs < 0;
        case lp::lconstraint_kind::EQ: return lhs == 0;
        case lp::lconstraint_kind::NE: return lhs != 0;
        default: UNREACHABLE();  return false;
        }
    }

    std::ostream& stellensatz::display(std::ostream& out) const {
        #if 0
//        m_solver.lra().display(out);
        for (auto const& [vars, v] : m_vars2mon) {
            out << "j" << v << " := ";
            display_product(out, vars);
            out << "\n";
        }
        #endif
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {      
            out << "(" << ci << ") ";
            display_constraint(out, ci);
            bool is_true = constraint_is_true(ci);
            out << (is_true ? " [true]" : " [false]") << "\n";
            out << "\t<- ";
            display(out, m_constraints[ci].j);
            out << "\n";
        }
        return out;
    }

    std::ostream& stellensatz::display_product(std::ostream& out, svector<lpvar> const& vars) const {
        bool first = true;
        for (auto v : vars) {
            if (first)
                first = false;
            else
                out << " * ";
            out << "j" << v;
        }
        return out;
    }

    std::ostream& stellensatz::display(std::ostream& out, term_offset const& t) const {
        bool first = true;
        for (auto [v, coeff] : t.first) {
            c().display_coeff(out, first, coeff);
            first = false;
            out << pp_j(*this, v);
        }
        if (t.second != 0)
            out << " + " << t.second;
        return out;
    }

    std::ostream& stellensatz::display_var(std::ostream& out, lpvar j) const {
        if (c().is_monic_var(j)) 
            return display_product(out, c().emon(j).vars());        
        else 
            return out << "j" << j;
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, lp::constraint_index ci) const {
        return display_constraint(out, m_constraints[ci]);
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, constraint const &c) const {
        auto const &[p, k, j] = c;
        p.display(out);
        return out << " " << k << " 0";
    }

    std::ostream &stellensatz::display(std::ostream &out, justification const &j) const {
        if (std::holds_alternative<external_justification>(j)) {
            auto dep = std::get<external_justification>(j).dep;
            unsigned_vector cs;
            c().lra_solver().dep_manager().linearize(dep, cs);
            for (auto c : cs)
                out << "[o " << c << "] ";  // constraint index from c().lra_solver.
        }
        else if (std::holds_alternative<addition_justification>(j)) {
            auto m = std::get<addition_justification>(j);
            out << "(" << m.left << ") + (" << m.right << ")";
        }
        else if (std::holds_alternative<substitute_justification>(j)) {
            auto m = std::get<substitute_justification>(j);
            out << "(" << m.ci << ") (" << m.ci_eq << ") by j" << m.v << " := " << m.p;
        }
        else if (std::holds_alternative<multiplication_justification>(j)) {
            auto m = std::get<multiplication_justification>(j);
            out << "(" << m.left << ") * (" << m.right << ")";
        }
        else if (std::holds_alternative<multiplication_poly_justification>(j)) {
            auto m = std::get<multiplication_poly_justification>(j);
            out << m.p << " * (" << m.ci << ")";
        }
        else if (std::holds_alternative<division_justification>(j)) {
            auto &m = std::get<division_justification>(j);
            out << "(" << m.ci << ") / (" << m.divisor << ")";
        } 
        else if (std::holds_alternative<assumption_justification>(j)) {
            out << "assumption";
        }
        else if (std::holds_alternative<gcd_justification>(j)) {
            auto m = std::get<gcd_justification>(j);
            out << " gcd (" << m.ci << ")";
        }
        else
            UNREACHABLE();
        return out;
    }

    std::ostream &stellensatz::display_lemma(std::ostream &out, lp::explanation const &ex) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> todo;
        for (auto c : ex) 
            todo.push_back(c.ci());
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto ci = todo[i];
            if (m_constraints_in_conflict.contains(ci))
                continue;
            m_constraints_in_conflict.insert(ci);
            out << "(" << ci << ") ";
            display_constraint(out, ci) << " ";
            auto const& j = m_constraints[ci].j;

            display(out, j) << "\n";
            if (std::holds_alternative<multiplication_justification>(j)) {
                auto m = std::get<multiplication_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<substitute_justification>(j)) {
                auto m = std::get<substitute_justification>(j);
                todo.push_back(m.ci);
                todo.push_back(m.ci_eq);
            }
            else if (std::holds_alternative<division_justification>(j)) {
                auto m = std::get<division_justification>(j);
                todo.push_back(m.ci);
                todo.push_back(m.divisor);
            }
            else if (std::holds_alternative<addition_justification>(j)) {
                auto m = std::get<addition_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<multiplication_poly_justification>(j)) {
                auto m = std::get<multiplication_poly_justification>(j);
                todo.push_back(m.ci);
            }
            else if (std::holds_alternative<external_justification>(j)) {
                // do nothing
            }
            else if (std::holds_alternative<assumption_justification>(j)) {                                
                // do nothing
            }
            else if (std::holds_alternative<gcd_justification>(j)) {
                auto m = std::get<gcd_justification>(j);
                todo.push_back(m.ci);
            }
            else 
                NOT_IMPLEMENTED_YET();

        }
        return out;
    }


    // Solver component
    // check LRA feasibilty
    // (partial) check LIA feasibility
    // try patch LIA model
    // option: iterate by continuing saturation based on partial results
    // option: add incremental linearization axioms
    // option: detect squares and add axioms for violated squares
    // option: add NIA filters (non-linear divisbility axioms)    


    void stellensatz::solver::init() {
        lra_solver = alloc(lp::lar_solver);
        int_solver = alloc(lp::int_solver, *lra_solver);
        m_ex.clear();
        m_internal2external_constraints.reset();
        m_monomial_factory.reset();
        auto &src = s.c().lra_solver();
        auto &dst = *lra_solver;
        for (unsigned v = 0; v < src.number_of_vars(); ++v)
            dst.add_var(v, src.var_is_int(v));                   
        
        for (lp::constraint_index ci = 0; ci < s.m_constraints.size(); ++ci) {
            auto const &[p, k, j] = s.m_constraints[ci];
            auto [t, offset] = to_term_offset(p);
            auto coeffs = t.coeffs_as_vector();
            if (coeffs.empty())
                continue;
            SASSERT(!coeffs.empty());
            auto ti = dst.add_term(coeffs, dst.number_of_vars());
            auto new_ci = dst.add_var_bound(ti, k, -offset);
            m_internal2external_constraints.setx(new_ci, ci, ci);
        }
    }

    stellensatz::term_offset stellensatz::solver::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.mk_monomial(*lra_solver, vars));
        }
        return to;
    }


    //
    // convert a conflict from m_solver.lra()/lia() into
    // a conflict for c().lra_solver()
    //
    void stellensatz::solver::add_lemma() {
        TRACE(arith, s.display(tout); s.display_lemma(tout, m_ex));
        auto &src = s.c().lra_solver();
        lp::explanation ex2;
        lemma_builder new_lemma(s.c(), "stellensatz");
        s.m_constraints_in_conflict.reset();
        for (auto p : m_ex)
            s.explain_constraint(new_lemma, m_internal2external_constraints[p.ci()], ex2);
        new_lemma &= ex2;
        IF_VERBOSE(2, verbose_stream() << "stellensatz unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        s.c().lra_solver().settings().stats().m_nla_stellensatz++;
    }

    lbool stellensatz::solver::solve() {
        init();
        lbool r = solve_lra();
        // IF_VERBOSE(0, verbose_stream() << "solve lra " << r << "\n");
        if (r != l_true)
            return r;
        r = solve_lia();
        // IF_VERBOSE(0, verbose_stream() << "solve lia " << r << "\n");
        if (r != l_true)
            return r;
        return l_undef;
        if (update_values())
            return l_true;

        return l_undef;
    }

    lbool stellensatz::solver::solve_lra() {
        auto status = lra_solver->find_feasible_solution();;
        if (lra_solver->is_feasible())
            return l_true;
        if (status == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(m_ex);
            add_lemma();
            return l_false;
        }
        return l_undef;
    }

    lbool stellensatz::solver::solve_lia() {
        switch (int_solver->check(&m_ex)) {
        case lp::lia_move::sat: 
            return l_true;
        case lp::lia_move::conflict: 
            add_lemma();
            return l_false;
        default:  // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }

    // update m_values
    // return true if the new assignment satisfies the products.
    // return false if value constraints are not satisfied on monomials and there is a false constaint.
    bool stellensatz::solver::update_values() {
        return false;
        #if 0
        std::unordered_map<lpvar, rational> values;
        lra_solver->get_model(values);
        unsigned sz = lra_solver->number_of_vars();
        for (unsigned i = 0; i < sz; ++i) {
            auto const &value = values[i];
            bool is_int = lra_solver->var_is_int(i); 
            SASSERT(!is_int || value.is_int());
            if (!s.is_mon_var(i))
                continue;
            rational val(1);
            for (auto w : s.c().emons()[i])
                val *= values[w];
            values[i] = val;
        }
        auto indices = lra_solver->constraints().indices();
        bool satisfies_products = all_of(indices, [&](auto ci) {
            NOT_IMPLEMENTED_YET();
            // todo: wrong, needs to be at level of lra constraint evaluation
            return s.constraint_is_true(ci);});
        if (satisfies_products) {
            TRACE(arith, tout << "found satisfying model\n");
            for (auto v : s.m_coi.vars()) 
                s.c().lra_solver().set_column_value(v, lp::impq(values[v], rational(0)));            
        }
        return satisfies_products;
        #endif
    }
}
