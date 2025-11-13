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

    stellensatz::stellensatz(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core),
        pddm(m_solver.lra().number_of_vars())
    {}

    lbool stellensatz::saturate() {
        init_solver();
        TRACE(arith, display(tout << "stellensatz before saturation\n"));
        eliminate_variables();
        // TODO: populate solver
        TRACE(arith, display(tout << "stellensatz after saturation\n"));
        return l_undef;
        lbool r = m_solver.solve();
        // IF_VERBOSE(0, verbose_stream() << "stellensatz " << r << "\n");
        if (r == l_false)
            add_lemma();
        return r;
    }

    void stellensatz::init_solver() {
        m_solver.init();
        m_vars2mon.reset();
        m_mon2vars.reset();
        m_constraints.reset();
        m_coi.init();
        init_vars();
        init_occurs();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto sz = src.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            if (m_coi.mons().contains(v))
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
                sum *= to_pdd(cv.j())*cv.coeff();
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
                to.first.add_monomial(coeff, mk_monomial(vars));                
        }        
        return to;
    }

    lpvar stellensatz::mk_monomial(svector<lpvar> const &vars) {
        lpvar v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;

        v = add_var(is_int(vars));
        m_vars2mon.insert(_vars, v);
        m_mon2vars.insert(v, _vars);
        SASSERT(m_values.size() == v);
        return v;
    }

    void stellensatz::init_monomial(unsigned mon_var) {
        auto &mon = c().emons()[mon_var];
        svector<lpvar> vars(mon.vars());
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, mon_var);
        m_mon2vars.insert(mon_var, vars);
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
        m_constraints.push_back({p, k, j });
        return m_constraints.size() - 1;
    }

    // initialize active set of constraints that evaluate to false in the current model
    // loop over active set to eliminate variables.
    void stellensatz::eliminate_variables() {
        vector<std::pair<lp::constraint_index, uint_set>> active;
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {
            if (!constraint_is_true(ci))
                active.push_back({ci, uint_set()});
        } 
        while (!active.empty()) {
            // factor ci into x*p + q <= rhs, where degree(x, q) < degree(x, p) + 1
            // if p is vanishing (evaluates to 0), then add p = 0 as assumption and reduce to q.
            // otherwise
            // find complementary constraints that contain x^k for k = 0 .. degree -1
            // eliminate x (and other variables) by combining ci with complementary constraints. 
            auto [ci, tabu] = active.back();               
            active.pop_back();           
            auto x = select_variable_to_eliminate(ci);
            auto f = factor(x, ci);
            auto p_value = cvalue(f.p);
            if (!f.p.is_zero() && p_value == 0) {
                // add p = 0 as assumption and reduce to q.
                auto p_is_0 = assume(f.p, lp::lconstraint_kind::EQ);
                if (!f.q.is_zero()) {
                    // ci & -p_is_0*x^f.degree  => new_ci
                    p_is_0 = multiply(p_is_0, rational(-1));             
                    for (unsigned i = 0; i < f.degree; ++i)
                        p_is_0 = multiply_var(p_is_0, x);                  
                    auto new_ci = add(ci, p_is_0);
                    init_occurs(new_ci);
                    uint_set new_tabu(tabu);
                    uint_set q_vars;
                    for (auto j : f.q.free_vars())
                        q_vars.insert(j);
                    for (auto j : f.p.free_vars())
                        if (!q_vars.contains(j))
                            new_tabu.insert(j);
                    active.push_back({new_ci, new_tabu});
                }
                continue;
            }
            for (auto other_ci : m_occurs[x]) {
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
                if (p_value > 0 && p_value2 > 0)
                    continue;
                if (p_value < 0 && p_value2 < 0)
                    continue;
                if (any_of(other_ineq.p.free_vars(), [&](unsigned j) { return tabu.contains(j); }))
                    continue;

                for (unsigned i = 0; i < f.degree; ++i)
                    f.p *= to_pdd(x);
                for (unsigned i = 0; i < g.degree; ++i)
                    g.p *= to_pdd(x);

                auto [m1, f_p] = f.p.var_factors();
                auto [m2, g_p] = g.p.var_factors();
                unsigned_vector m1m2;
                dd::pdd::merge(m1, m2, m1m2);
                SASSERT(m1m2.contains(x));
                f_p = f_p.mul(m1);
                g_p = g_p.mul(m2);
                
                auto sign_f = cvalue(f_p) < 0;
                SASSERT(sign_f != cvalue(g_p) < 0);
                SASSERT(cvalue(f_p) != 0);
                SASSERT(cvalue(g_p) != 0);

                // m1m2 * f_p + f.q >= 0
                // m1m2 * g_p + g.q >= 0
                // 
                auto ci_a = ci;
                auto ci_b = other_ci;
                auto aj = assumption_justification();
                if (f_p.is_val())
                    ci_a = multiply(other_ci, f_p.val());
                else if (sign_f)
                    ci_a = multiply(other_ci, add_constraint(f_p, lp::lconstraint_kind::LT, aj));
                else
                    ci_a = multiply(other_ci, add_constraint(f_p, lp::lconstraint_kind::GT, aj));
                
                if (g_p.is_val())
                    ci_b = multiply(ci, g_p.val());
                else if (!sign_f)
                    ci_b = multiply(ci, add_constraint(g_p, lp::lconstraint_kind::LT, aj));
                else
                    ci_b = multiply(ci, add_constraint(g_p, lp::lconstraint_kind::GT, aj));

                auto new_ci = add(ci_a, ci_b);
                init_occurs(new_ci);
                if (!constraint_is_true(new_ci)) {
                    auto const &p = m_constraints[ci].p;
                    auto const &[new_p, new_k, new_j] = m_constraints[new_ci];
                    uint_set new_tabu(tabu), fv;                 
                    for (auto v : new_p.free_vars())
                        fv.insert(v);
                    for (auto v : p.free_vars())
                        if (!fv.contains(v))
                            new_tabu.insert(v);
                    active.push_back({new_ci, new_tabu});
                }                
            }          
        }
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
    // convert a conflict from m_solver.lra()/lia() into
    // a conflict for c().lra_solver()
    // 1. constraints that are obtained by multiplication are explained from the original constraint
    // 2. bounds justifications are added as justifications to the lemma.
    // 
    void stellensatz::add_lemma() {
        lp::explanation const &ex1 = m_solver.ex();
        vector<ineq> const &ineqs = m_solver.ineqs();
        TRACE(arith, display(tout); display_lemma(tout, ex1, ineqs));
        auto& lra = c().lra_solver();
        lp::explanation ex2;
        lemma_builder new_lemma(c(), "stellensatz");
        m_constraints_in_conflict.reset();
        for (auto p : ex1) 
            explain_constraint(new_lemma, p.ci(), ex2);        
        new_lemma &= ex2;
        for (auto const &ineq : ineqs)
            new_lemma |= ineq;
        IF_VERBOSE(2, verbose_stream() << "stellensatz unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        c().lra_solver().settings().stats().m_nla_stellensatz++;
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
            m_solver.lra().push_explanation(dep.dep, ex);
        } 
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto& m = std::get<multiplication_justification>(b);
            explain_constraint(new_lemma, m.left, ex);
            explain_constraint(new_lemma, m.right, ex);
        } 
        else if (std::holds_alternative<addition_justification>(b)) {
            auto& m = std::get<addition_justification>(b);
            explain_constraint(new_lemma, m.left, ex);
            explain_constraint(new_lemma, m.right, ex);
        } 
        else if (std::holds_alternative<multiplication_const_justification>(b)) {
            auto& m = std::get<multiplication_const_justification>(b);
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
        // eval.var2val() = [&](unsigned v) -> void { return c().val(v); };
        return eval(p);
    }

    lp::constraint_index stellensatz::gcd_normalize(lp::constraint_index ci) {
        auto [p, k, j] = m_constraints[ci];
        rational g(0);
        bool is_int = all_of(p.free_vars(), [&](unsigned v) { return c().lra_solver().var_is_int(v); });
        for (auto const& [c, is_constant] : p.coefficients()) 
            if (!is_constant || !is_int)
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
            if (is_int) {
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

    // p >= lo  =>  a * p >= a * lo if a > 0
    lp::constraint_index stellensatz::multiply(lp::constraint_index ci, rational const& mul) {
        SASSERT(mul != 0);
        auto const& [p, k, j] = m_constraints[ci];
        return add_constraint(p * mul, mul > 0 ? k : swap_side(k), multiplication_const_justification{ci, mul});
    }

    lp::constraint_index stellensatz::multiply(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1, j1] = m_constraints[left];
        auto const &[q, k2, j2] = m_constraints[right];
        lp::lconstraint_kind k = meet(k1, k2);
        return add_constraint(p*q, k, multiplication_justification{left, right});
    }

    lp::constraint_index stellensatz::multiply_var(lp::constraint_index ci, lpvar x) {
        auto const& [p, k, j] = m_constraints[ci];
        SASSERT(k == lp::lconstriant_kind::EQ);        
        SASSERT(p.offset() == 0);
        return add_constraint(to_pdd(x) * p, k, multiplication_var_justification{ci, x});          
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
        return all_of(vars, [&](lpvar v) { return m_solver.lra().var_is_int(v); });
    }

    lpvar stellensatz::add_var(bool is_int) {
        auto v = m_solver.lra().number_of_vars();
        auto w = m_solver.lra().add_var(v, is_int);
        SASSERT(v == w);
        m_occurs.reserve(m_solver.lra().number_of_vars());
        return w;
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
        m_solver.lra().display(out);
        for (auto const& [vars, v] : m_vars2mon) {
            out << "j" << v << " := ";
            display_product(out, vars);
            out << "\n";
        }
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
        if (is_mon_var(j)) {
//            display_product(out, c().emons()[j]);
        }
        else {
            out << "j" << j;
        }

        return out;
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
        else if (std::holds_alternative<multiplication_justification>(j)) {
            auto m = std::get<multiplication_justification>(j);
            out << "(" << m.left << ") * (" << m.right << ")";
        }
        else if (std::holds_alternative<addition_justification>(j)) {
            auto m = std::get<addition_justification>(j);
            out << "(" << m.left << ") + (" << m.right << ")";
        }
        else if (std::holds_alternative<multiplication_const_justification>(j)) {
            auto m = std::get<multiplication_const_justification>(j);
            out << m.mul << " * (" << m.ci << ")";
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

    std::ostream& stellensatz::display_lemma(std::ostream& out, lp::explanation const& ex,
        vector<ineq> const& ineqs) {
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
            else if (std::holds_alternative<addition_justification>(j)) {
                auto m = std::get<addition_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<multiplication_const_justification>(j)) {
                auto m = std::get<multiplication_const_justification>(j);
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
        for (auto ineq : ineqs) {
            term_offset t(ineq.term(), rational(0));
            display(out, t) << " " << ineq.cmp() << " " << ineq.rs() << "\n";
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
        m_ineqs.reset();
    }

    lbool stellensatz::solver::solve() {
        lbool r = solve_lra();
        // IF_VERBOSE(0, verbose_stream() << "solve lra " << r << "\n");
        if (r != l_true)
            return r;
        r = solve_lia();
        // IF_VERBOSE(0, verbose_stream() << "solve lia " << r << "\n");
        if (r != l_true)
            return r;
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
            return l_false;
        }
        return l_undef;
    }

    lbool stellensatz::solver::solve_lia() {
        switch (int_solver->check(&m_ex)) {
        case lp::lia_move::sat: return l_true;
        case lp::lia_move::conflict: return l_false;
        default:  // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }

    // update m_values
    // return true if the new assignment satisfies the products.
    // return false if value constraints are not satisfied on monomials and there is a false constaint.
    bool stellensatz::solver::update_values() {
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
    }
}
