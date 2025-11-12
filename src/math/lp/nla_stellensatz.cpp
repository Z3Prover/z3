/*++
  Copyright (c) 2025 Microsoft Corporation



  */

#include "util/heap.h"
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

    stellensatz::stellensatz(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core) 
    {}

    lbool stellensatz::saturate() {
        init_solver();
        TRACE(arith, display(tout << "stellensatz after saturation\n"));
        eliminate_variables();
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
        m_values.reset();
        m_justifications.reset();
        m_max_monomial_degree = 0;
        m_coi.init();
        init_vars();
        init_occurs();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto &dst = m_solver.lra();
        auto sz = src.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            // Declare v into m_solver.lra()
            unsigned w;
            if (m_coi.mons().contains(v))
                init_monomial(v);
            else 
                m_values.push_back(c().val(v));
            if (m_coi.terms().contains(v)) {
                auto const& t = src.get_term(v);
                // justification: variables in coefficients are always declared before term variable.
                SASSERT(all_of(t, [&](auto p) { return p.j() < v; }));
                w = dst.add_term(t.coeffs_as_vector(), v);
            } 
            else
                w = dst.add_var(v, src.var_is_int(v));

            // assert bounds on v in the new solver.
            VERIFY(w == v);
            if (src.column_has_lower_bound(v)) {
                auto lo_bound = src.get_lower_bound(v);
                SASSERT(lo_bound.y >= 0);
                auto k   = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = src.get_column_lower_bound_witness(v);
                auto ci  = dst.add_var_bound(v, k, rhs);
                add_justification(ci, external_justification(dep));
            }
            if (src.column_has_upper_bound(v)) {
                auto hi_bound = src.get_upper_bound(v);
                SASSERT(hi_bound.y <= 0);
                auto k   = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = src.get_column_upper_bound_witness(v);
                auto ci  = dst.add_var_bound(v, k, rhs);
                add_justification(ci, external_justification(dep));
            }
        }
        m_occurs.reserve(sz);
        for (auto const &[v, vars] : m_mon2vars) 
            m_max_monomial_degree = std::max(m_max_monomial_degree, vars.size());        
    }

    void stellensatz::init_monomial(unsigned mon_var) {
        auto& mon = c().emons()[mon_var];
        svector<lpvar> vars(mon.vars());
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, mon_var);
        m_mon2vars.insert(mon_var, vars);
        m_values.push_back(cvalue(vars));
    }

    // initialize active set of constraints that evaluate to false in the current model
    // loop over active set to eliminate variables.
    void stellensatz::eliminate_variables() {
        vector<std::pair<lp::constraint_index, uint_set>> active;
        for (auto ci : m_solver.lra().constraints().indices()) {
            if (constraint_is_true(ci))
                continue;
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
            if (!f.p.is_empty() && p_value == 0) {
                // add p = 0 as assumption and reduce to q.
                auto p_is_0 = assume(f.p, lp::lconstraint_kind::EQ, rational(0));
                if (!f.q.is_empty()) {
                    auto const &con = m_solver.lra().constraints()[ci];
                    // ci & -p_is_0*f.coeff*x^f.degree  => new_ci
              
                    if (f.coeff != -1)
                        p_is_0 = multiply(p_is_0, rational(-f.coeff));
                    for (unsigned i = 0; i < f.degree; ++i)
                        p_is_0 = multiply_var(p_is_0, x);                    
                    auto new_ci = add(ci, p_is_0);
                    uint_set new_tabu(tabu);
                    uint_set q_vars;
                    for (auto cv : f.q)
                        q_vars.insert(cv.j());
                    for (auto cv : f.p)
                        if (!q_vars.contains(cv.j()))
                            new_tabu.insert(cv.j());
                    active.push_back({new_ci, new_tabu});
                }
                continue;
            }
            for (auto other_ci : m_occurs[x]) {
            
            }

            // 
        }
    }

    lp::lpvar stellensatz::select_variable_to_eliminate(lp::constraint_index ci) {
        auto &ineq = m_solver.lra().constraints()[ci];
        lpvar best_var = lp::null_lpvar;
        for (auto cv : ineq.lhs()) {
            auto v = cv.j();
            if (best_var == lp::null_lpvar) {
                best_var = v;
                continue;
            }
            if (is_mon_var(v)) {
                for (auto w : m_mon2vars[v]) {
                    if (best_var > v) {
                        best_var = v;                     
                    }
                }
            }
            else if (best_var > v) {
                best_var = v;
            }
        }
        return best_var;
    }

    unsigned stellensatz::degree_of_var_in_constraint(lpvar var, lp::constraint_index ci) const {
        auto &ineq = m_solver.lra().constraints()[ci];
        unsigned max_degree = 0;
        for (auto cv : ineq.lhs()) {            
            auto degree = degree_of_var_in_monomial(var, cv.j());
            if (degree > max_degree)
                max_degree = degree;
        }
        return max_degree;
    }

    unsigned stellensatz::degree_of_var_in_monomial(lpvar v, lpvar mi) const {
        unsigned degree = 0;
        if (is_mon_var(mi)) {
            for (auto w : m_mon2vars[mi]) 
                if (v == w)
                    degree++;            
        }
        else if (mi == v)
            ++degree; 
        return degree;
    }

    stellensatz::factorization stellensatz::factor(lpvar v, lp::constraint_index ci) {
        auto &ineq = m_solver.lra().constraints()[ci];
        auto degree = degree_of_var_in_constraint(v, ci);
        rational coeff(0);
        lp::lar_term p, q;
        for (auto cv : ineq.lhs()) {
            auto d = degree_of_var_in_monomial(v, cv.j());
            if (d < degree) 
                q.add_monomial(cv.coeff(), cv.j());
            else {
                auto w = divide(v, degree, cv.j());
                if (w == lp::null_lpvar)
                    coeff += cv.coeff();
                else
                    p.add_monomial(cv.coeff(), w);               
            }
                
        }
        return {coeff, degree, p, q};
    }

    lp::lpvar stellensatz::divide(lpvar v, unsigned degree, lpvar mi) {
        SASSERT(degree_of_var(v, mi) >= degree);
        if (is_mon_var(mi)) {
            auto const &vars = m_mon2vars[mi];
            if (degree == vars.size())
                return lp::null_lpvar;
            svector<lpvar> _vars;
            for (auto w : vars) {
                if (w == v && degree > 0) 
                    --degree;                
                else
                    _vars.push_back(w);
            }
            return mk_monomial(_vars);
        }
        SASSERT(degree == 1 && mi == v);
        return lp::null_lpvar;
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
        auto just = m_justifications.get(ci);
        if (just == nullptr)
            return;
        auto &b = *just;
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
            auto &con = m_solver.lra().constraints()[ci];
            new_lemma |= ineq(con.lhs(), negate(con.kind()), con.rhs());
        }
        else if (std::holds_alternative<gcd_justification>(b)) {
            auto& m = std::get<gcd_justification>(b);
            explain_constraint(new_lemma, m.ci, ex);
        }
        else
            UNREACHABLE();
    }
 
    rational stellensatz::cvalue(lp::lar_term const &t) const {
        rational r(0);
        for (auto cv : t)
            r += c().val(cv.j()) * cv.coeff();
        return r;
    }

    rational stellensatz::mvalue(lp::lar_term const &t) const {
        rational r(0);
        for (auto cv : t)
            r += m_values[cv.j()] * cv.coeff();
        return r;
    }

    rational stellensatz::cvalue(svector<lpvar> const &prod) const {
        rational p(1);
        for (auto v : prod)
            p *= c().val(v);
        return p;
    }

    rational stellensatz::mvalue(svector<lpvar> const &prod) const {
        rational p(1);
            for (auto v : prod)
                p *= m_values[v];
        return p;
    }

    void stellensatz::gcd_normalize(vector<std::pair<rational, lpvar>> &t, lp::lconstraint_kind k, rational &rhs) {
        rational d(1);
        for (auto &[c,v] : t)
            d = lcm(d, denominator(c));
        d = lcm(d, denominator(rhs));
        if (d != 1) {
            for (auto &[c, v] : t)
                c *= d;
            rhs *= d;
        }
        rational g(0);
        for (auto &[c, v] : t)
            g = gcd(g, c);
        bool is_int = true;
        for (auto &[c, v] : t)
            is_int &= m_solver.lra().var_is_int(v);
        if (!is_int)
            g = gcd(g, rhs);
        if (g == 1 || g == 0)
            return;
        switch (k) {
        case lp::lconstraint_kind::GE:
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            rhs = ceil(rhs);
            break;
        case lp::lconstraint_kind::GT:
            for (auto &[c, v] : t)
                c /= g;
            if (is_int)
                rhs += 1;
            rhs /= g;
            rhs = ceil(rhs);
            break;
        case lp::lconstraint_kind::LE:
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            rhs = floor(rhs);
            break;
        case lp::lconstraint_kind::LT:
            for (auto &[c, v] : t)
                c /= g;
            if (is_int)
                rhs -= 1;
            rhs /= g;
            rhs = floor(rhs);
            break;
        case lp::lconstraint_kind::EQ:
        case lp::lconstraint_kind::NE:
            if (!divides(g, rhs))
                break;
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            break;
        }    
    }

    lp::constraint_index stellensatz::normalize_ineq(lp::constraint_index ci) {
        auto const &con = m_solver.lra().constraints()[ci];
        auto k = con.kind();
        if (k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::LT) {
            auto mjust = multiplication_const_justification({ci, rational(-1)});
            k = swap_side(k);
            rational value(0);
            auto coeffs = con.coeffs();
            for (auto &[c, v] : coeffs) {
                c = -c;
                value += c * m_values[v];
            }
            auto ti = m_solver.lra().add_term(coeffs, m_solver.lra().number_of_vars());
            m_occurs.reserve(m_solver.lra().number_of_vars());
            m_values.push_back(value);
            ci = m_solver.lra().add_var_bound(ti, k, -con.rhs());
        }
        return ci;
    }

    lp::constraint_index stellensatz::add_ineq( 
        justification const& just, lp::lar_term & t, lp::lconstraint_kind k,
        rational const & rhs_) {
        auto coeffs = t.coeffs_as_vector();
        SASSERT(!coeffs.empty());
        auto add = [&](justification const& just, vector<std::pair<rational, lpvar>> const& coeffs, rational const& rhs) {
            auto ti = m_solver.lra().add_term(coeffs, m_solver.lra().number_of_vars());
            m_occurs.reserve(m_solver.lra().number_of_vars());
            m_values.push_back(mvalue(t));
            auto new_ci = m_solver.lra().add_var_bound(ti, k, rhs);
            TRACE(arith, display(tout, just) << "\n");
            SASSERT(m_values.size() - 1 == ti);
            add_justification(new_ci, just);
            return new_ci;
        };
        auto new_ci = add(just, coeffs, rhs_);  
        rational rhs(rhs_);
        gcd_normalize(coeffs, k, rhs);
        if (rhs != rhs_) 
            new_ci = add(gcd_justification(new_ci), coeffs, rhs);        
        init_occurs(new_ci);
        return new_ci;
    }

    lp::constraint_index stellensatz::add_ineq(justification const& just, lpvar j, lp::lconstraint_kind k,
        rational const& rhs) {
        auto new_ci = m_solver.lra().add_var_bound(j, k, rhs);
        add_justification(new_ci, just);
        init_occurs(new_ci);
        return new_ci;
    }

    lp::constraint_index stellensatz::assume(lp::lar_term &t, lp::lconstraint_kind k, rational const &rhs) {
        return add_ineq(assumption_justification(), t, k, rhs);
    }
    // p1 >= lo1, p2 >= lo2 => p1 + p2 >= lo1 + lo2
    lp::constraint_index stellensatz::add(lp::constraint_index left, lp::constraint_index right) {
        auto const &lcon = m_solver.lra().constraints()[left];
        auto const &rcon = m_solver.lra().constraints()[right];
        SASSERT(lcon.kind() == lp::lconstraint_kind::GE || lcon.kind() == lp::lconstraint_kind::GT);
        SASSERT(rcon.kind() == lp::lconstraint_kind::GE || rcon.kind() == lp::lconstraint_kind::GT);
        lp::lar_term t;
        for (auto const &[v, c] : lcon.lhs())
            t.add_monomial(c, v);
        for (auto const &[v, c] : rcon.lhs())
            t.add_monomial(c, v);
        lp::lconstraint_kind k = join(lcon.kind(), rcon.kind());
        rational rhs = lcon.rhs() + rcon.rhs();
        auto just = addition_justification{left, right};
        return add_ineq(just, t, k, rhs);
    }

    // p >= lo  =>  a * p >= a * lo if a > 0
    lp::constraint_index stellensatz::multiply(lp::constraint_index ci, rational const& mul) {
        SASSERT(mul != 0);
        auto const &con = m_solver.lra().constraints()[ci];
        lp::lar_term t;
        for (auto const &[v, c] : con.lhs())
            t.add_monomial(c * mul, v);
        lp::lconstraint_kind k = con.kind();
        if (mul < 0)
            k = swap_side(k);
        rational rhs = con.rhs() * mul;
        auto just = multiplication_const_justification{ci, mul};
        return add_ineq(just, t, k, rhs);        
    }

    lp::constraint_index stellensatz::multiply(lp::constraint_index left, lp::constraint_index right) {
        auto const &lcon = m_solver.lra().constraints()[left];
        auto const &rcon = m_solver.lra().constraints()[right];
        SASSERT(lcon.kind() == lp::lconstraint_kind::GE || lcon.kind() == lp::lconstraint_kind::GT);
        SASSERT(rcon.kind() == lp::lconstraint_kind::GE || rcon.kind() == lp::lconstraint_kind::GT);
        lp::lar_term t;
        for (auto const &[v1, c1] : lcon.lhs()) {
            for (auto const &[v2, c2] : rcon.lhs()) {
                auto j = mk_monomial(expand_monomial({v1, v2}));
                t.add_monomial(c1 * c2, j);
            }
        }
        if (rcon.rhs() != 0)
            for (auto const &[v, c] : lcon.lhs()) 
                t.add_monomial(-c * rcon.rhs(), v);
        if (lcon.rhs() != 0)
            for (auto const &[v, c] : rcon.lhs()) 
                t.add_monomial(-c * lcon.rhs(), v);
        lp::lconstraint_kind k = join(lcon.kind(), rcon.kind());
        rational rhs{0};
        return add_ineq(multiplication_justification{left, right}, t, k, rhs);
    }

    lp::constraint_index stellensatz::multiply_var(lp::constraint_index ci, lpvar x) {
        auto const &con = m_solver.lra().constraints()[ci];
        lp::lconstraint_kind k = con.kind();
        SASSERT(k == lp::lconstriant_kind::EQ);
        SASSERT(con.rhs() == 0);
        lp::lar_term t;
        for (auto const &[v, c] : con.lhs())
            t.add_monomial(c, mk_monomial(expand_monomial({x, v})));        
        auto just = multiplication_const_justification{ci, rational(1)}; // multiply var
        return add_ineq(just, t, k, rational(0));  
    }

    void stellensatz::init_occurs() {
        m_occurs.reset();
        m_occurs.reserve(c().lra_solver().number_of_vars());
        for (auto ci : m_solver.lra().constraints().indices())
            init_occurs(ci);        
    }

    void stellensatz::init_occurs(lp::constraint_index ci) {
        if (ci == lp::null_ci)
            return;
        ci = normalize_ineq(ci);
        auto const &con = m_solver.lra().constraints()[ci];
        for (auto cv : con.lhs()) {
            auto v = cv.j();
            if (is_mon_var(v)) {
                for (auto w : m_mon2vars[v]) 
                    m_occurs[w].push_back(ci);                
            }
            else 
                m_occurs[v].push_back(ci);
        }
    }

    // Insert a (new) monomial representing product of vars.
    // if the length of vars is 1 then the new monomial is vars[0]
    // if the same monomial was previous defined, return the previously defined monomial.
    // otherwise create a fresh variable representing the monomial.
    // todo: if _vars is a square, then add bound axiom.
    lpvar stellensatz::mk_monomial(svector<lpvar> const& vars) {
        lpvar v;
        if (vars.empty())
            return lp::null_lpvar;
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
        m_values.push_back(cvalue(vars));
        return v;
    }

    lpvar stellensatz::mk_monomial(svector<lp::lpvar> const &_vars, lp::lpvar j) {
        svector<lpvar> vars(_vars);
        if (is_mon_var(j))
            vars.append(m_mon2vars[j]);
        else
            vars.push_back(j);
        return mk_monomial(vars);
    }

    svector<lp::lpvar> stellensatz::expand_monomial(svector<lp::lpvar> const& vars) {
        svector<lp::lpvar> result;
        for (auto v : vars) {
            if (is_mon_var(v)) 
                result.append(m_mon2vars[v]);            
            else 
                result.push_back(v);            
        }
        return result;
    }

    lpvar stellensatz::mk_term(term_offset& t) {
        if (t.second != 0) {            
            auto w = add_var(t.second.is_int()); // or reuse the constant 1 that is already there.
            m_values.push_back(t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::GE, t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::LE, t.second);
            m_justifications.push_back(nullptr);
            m_justifications.push_back(nullptr);
            t.first.add_monomial(rational(1), w);
            t.second = 0;
        }
        auto ti = m_solver.lra().add_term(t.first.coeffs_as_vector(), m_solver.lra().number_of_vars());
        m_values.push_back(cvalue(t.first));
        m_occurs.reserve(m_solver.lra().number_of_vars());
        return ti;
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
        auto const& con = m_solver.lra().constraints()[ci];
        auto lhs = -con.rhs();
        for (auto const& cv : con.lhs())
            lhs += cv.coeff() * m_values[cv.j()];
        switch (con.kind()) {
        case lp::lconstraint_kind::GT: return lhs > 0;
        case lp::lconstraint_kind::GE: return lhs >= 0;
        case lp::lconstraint_kind::LE: return lhs <= 0;
        case lp::lconstraint_kind::LT: return lhs < 0;
        case lp::lconstraint_kind::EQ: return lhs == 0;
        case lp::lconstraint_kind::NE: return lhs != 0;
        default: UNREACHABLE(); return false;
        }
    }

    std::ostream& stellensatz::display(std::ostream& out) const {
        m_solver.lra().display(out);
        for (auto const& [vars, v] : m_vars2mon) {
            out << "j" << v << " := ";
            display_product(out, vars);
            out << "\n";
        }
        for (auto ci : m_solver.lra().constraints().indices()) {
            out << "(" << ci << ") ";
            display_constraint(out, ci);
            bool is_true = constraint_is_true(ci);
            out << (is_true ? " [true]" : " [false]") << "\n";
            auto j = m_justifications.get(ci);
            if (!j)
                continue;
            out << "\t<- ";
            display(out, *j);
            out << "\n";
        }
        return out;
    }

    std::ostream& stellensatz::display(std::ostream& out, justification const& b) const {
        if (std::holds_alternative<external_justification>(b)) {
            auto &dep = std::get<external_justification>(b);
            unsigned_vector cs;
            c().lra_solver().dep_manager().linearize(dep.dep, cs);
            for (auto c : cs)
                out << "[o " << c << "] ";  // constraint index from c().lra_solver.
        } 
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto &m = std::get<multiplication_justification>(b);
            out << "mult (" << m.left << ") (" << m.right << ")";
        }
        else if (std::holds_alternative<addition_justification>(b)) {
            auto &m = std::get<addition_justification>(b);
            out << "(" << m.left << ") (" << m.right << ")";
        }
        else if (std::holds_alternative<gcd_justification>(b)) {
            auto &m = std::get<gcd_justification>(b);
            out << "gcd(" << m.ci << ")";
        }
        else if (std::holds_alternative<assumption_justification>(b)) {
            out << "assumption";
        }
        else if (std::holds_alternative<multiplication_const_justification>(b)) {
            auto &m = std::get<multiplication_const_justification>(b);
            out << m.mul << " * (" << m.ci << ")";
        }
        else
            UNREACHABLE();
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
        if (is_mon_var(j))
            display_product(out, m_mon2vars[j]);
        else
            out << "j" << j;
        return out;
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, lp::constraint_index ci) const {
        auto const& con = m_solver.lra().constraints()[ci];
        return display_constraint(out, con.lhs(), con.kind(), con.rhs());
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, 
        lp::lar_term const& lhs,
        lp::lconstraint_kind k, rational const& rhs) const {
        bool first = true;
        for (auto cv : lhs) {
            auto v = cv.j();
            c().display_coeff(out, first, cv.coeff());
            first = false;
            if (is_mon_var(v))
                display_product(out, m_mon2vars[v]);
            else
                out << "j" << v;
        }
        return out << " " << k << " " << rhs;
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
            auto j = m_justifications.get(ci);
            if (!j)
                continue;
            display(out, *j) << "\n";
            if (std::holds_alternative<multiplication_justification>(*j)) {
                auto m = std::get<multiplication_justification>(*j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<addition_justification>(*j)) {
                auto m = std::get<addition_justification>(*j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<multiplication_const_justification>(*j)) {
                auto m = std::get<multiplication_const_justification>(*j);
                todo.push_back(m.ci);
            }
            else if (std::holds_alternative<external_justification>(*j)) {
                // do nothing
            }
            else if (std::holds_alternative<assumption_justification>(*j)) {
                // do nothing
            }
            else if (std::holds_alternative<gcd_justification>(*j)) {
                auto m = std::get<gcd_justification>(*j);
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
            if (s.is_mon_var(i)) 
                s.m_values[i] = s.mvalue(s.m_mon2vars[i]);             
            else
                s.m_values[i] = value;
        }
        auto indices = lra_solver->constraints().indices();
        bool satisfies_products = all_of(indices, [&](auto ci) {
            return s.constraint_is_true(ci);});
        if (satisfies_products) {
            TRACE(arith, tout << "found satisfying model\n");
            for (auto v : s.m_coi.vars()) 
                s.c().lra_solver().set_column_value(v, lp::impq(s.m_values[v], rational(0)));            
        }
        return satisfies_products;
    }
}
