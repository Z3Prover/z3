/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/

#include "util/heap.h"
#include "params/smt_params_helper.hpp"
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
        pddm(core->lra_solver().number_of_vars()) {
    }

    lbool stellensatz::saturate() {
        unsigned num_constraints = 0, num_conflicts = 0;
        init_solver();
        TRACE(arith, display(tout << "stellensatz before saturation\n"));
    start_saturate:
        num_constraints = m_constraints.size();
        lbool r;
        if (m_config.strategy == 0)
            r = conflict_saturation();
        else
            r = model_repair();
        
        if (m_constraints.size() == num_constraints)
            return l_undef;
        
        if (r == l_undef)
            r = m_solver.solve(m_core);
        TRACE(arith, display(tout << "stellensatz after saturation " << r << "\n"));
        if (r == l_false) {
            ++num_conflicts;            
            IF_VERBOSE(2, verbose_stream() << "(nla.stellensatz :conflicts " << num_conflicts << ":constraints " << m_constraints.size() << ")\n");
            if (num_conflicts >= m_config.max_conflicts)
                return l_undef;
            while (backtrack(m_core)) {
                ++c().lp_settings().stats().m_stellensatz.m_num_backtracks;               
                lbool rb = m_solver.solve(m_core);
                if (rb == l_false)
                    continue;
                if (rb == l_undef) 
                    return rb;                
                m_solver.update_values(m_values);
                goto start_saturate;
            }
            ++c().lp_settings().stats().m_stellensatz.m_num_conflicts;
            conflict(m_core);
        }
        if (r == l_true && !set_model())
            r = l_undef;
        return r;
    }

    void stellensatz::pop_constraint() {
        auto const &[p, k, j] = m_constraints.back();
        m_constraint_index.erase({p.index(), k});             
        m_constraints.pop_back();       
    }

    void stellensatz::init_solver() {
        m_trail.reset();
        m_monomial_factory.reset();
        m_coi.init();
        m_values.reset();
        init_vars();
        init_occurs();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto sz = src.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            m_values.push_back(c().val(v));
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

    // set the model based on m_values computed by the solver
    bool stellensatz::set_model() {
        if (any_of(m_constraints, [&](auto const &c) { return !constraint_is_true(c); }))
            return false;
        auto &src = c().lra_solver();
        c().m_use_nra_model = true;
        m_values.reserve(src.number_of_vars());
        for (unsigned v = 0; v < src.number_of_vars(); ++v) {
            if (c().is_monic_var(v)) {
                auto& mon = c().emons()[v];
                rational val(1);
                for (auto w : mon.vars())
                    val *= m_values[w];
                m_values[v] = val;
            }
            else if (src.column_has_term(v)) {
                auto const& t = src.get_term(v);
                rational val(0);
                for (auto cv : t) 
                    val += m_values[cv.j()] * cv.coeff();
                m_values[v] = val;
            }
            else if (m_coi.vars().contains(v)) {
                // variable is in coi, m_values[v] is set.
            }
            else {
                m_values[v] = c().val(v);
            }
            c().m_nra.set_value(v, m_values[v]);
        }          
        return true;
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

    bool stellensatz::has_term_offset(dd::pdd const &p) {
        for (auto const &[coeff, vars] : p) 
            if (!vars.empty() && lp::null_lpvar == m_monomial_factory.get_monomial(vars))
                return false;
        return true;
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
            p -= rational(1);
        }
        lp::constraint_index ci = lp::null_ci;
        if (m_constraint_index.find({p.index(), k}, ci))
            return ci;
        ci = m_constraints.size();
        m_constraints.push_back({p, k, j });
        m_constraint_index.insert({p.index(), k}, ci);
        ++c().lp_settings().stats().m_stellensatz.m_num_constraints;
        
        m_tabu.reserve(ci + 1);
        m_tabu[ci].reset();
        m_has_occurs.reserve(ci + 1);
        struct undo_constraint : public trail {
            stellensatz &s;
            undo_constraint(stellensatz& s): s(s) {}
            void undo() override {
                s.pop_constraint();
            }
        };
        m_trail.push_scope();
        m_trail.push(undo_constraint(*this));
        return ci;
    }

    void stellensatz::add_active(lp::constraint_index ci, uint_set const &tabu) {
        if (m_active.contains(ci))
            return;
        m_active.insert(ci);
        m_tabu[ci] = tabu;
    }

    // initialize active set of constraints that evaluate to false in the current model
    // loop over active set to eliminate variables.
    lbool stellensatz::conflict_saturation() {
        m_active.reset();
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {
            if (!constraint_is_true(ci))
                add_active(ci, uint_set());
        } 
        while (!m_active.empty() && c().reslim().inc()) {
            if (m_constraints.size() >= m_config.max_constraints)
                break;
            // factor ci into x*p + q <= rhs, where degree(x, q) < degree(x, p) + 1
            // if p is vanishing (evaluates to 0), then add p = 0 as assumption and reduce to q.
            // otherwise
            // find complementary constraints that contain x^k for k = 0 .. degree -1
            // eliminate x (and other variables) by combining ci with complementary constraints. 
            auto ci = m_active.elem_at(0);   
            m_active.remove(ci);   
            if (constraint_is_true(ci))
                continue;
            

            TRACE(arith, display_constraint(tout << "process (" << ci << ") ", ci) << " " << m_tabu[ci] << "\n");

            switch (factor(ci)) {
            case l_undef: break; 
            case l_false: return l_false;
            case l_true: continue;
            }

            auto x = select_variable_to_eliminate(ci);
            if (x == lp::null_lpvar)
                continue;
            if (!resolve_variable(x, ci))
                return l_false;         
        }
        return l_undef;
    }

    bool stellensatz::resolve_variable(lpvar x, lp::constraint_index ci) {
        auto f = factor(x, ci);
        TRACE(arith, tout << "factor " << m_constraints[ci].p << " -> j" << x << "^" << f.degree << " * " << f.p
                          << "  +  " << f.q << "\n");
        auto p_value = value(f.p);
        if (vanishing(x, f, ci))
            return true;
        if (p_value == 0)
            return true;
        if (m_tabu[ci].contains(x))
            return true;
        unsigned num_x = m_occurs[x].size();
        for (unsigned i = 0; i < f.degree; ++i)
            f.p *= to_pdd(x);
        auto [_m1, _f_p] = f.p.var_factors();

        for (unsigned cx = 0; cx < num_x; ++cx) {
            auto other_ci = m_occurs[x][cx];
            if (m_tabu[other_ci].contains(x))
                continue;
            if (!resolve_variable(x, ci, other_ci, p_value, f, _m1, _f_p))
                return false;
        } 
        return true;
    }

    bool stellensatz::resolve_variable(lpvar x, lp::constraint_index ci, lp::constraint_index other_ci,
                                       rational const &p_value, factorization const &f, unsigned_vector const &_m1,
                                       dd::pdd _f_p) {
        if (ci == other_ci)
            return true;
        if (f.degree != 1)
            return true; // future - could handle this
        auto const &[other_p, other_k, other_j] = m_constraints[other_ci];
        auto const &[p, k, j] = m_constraints[ci];
        auto g = factor(x, other_ci);
        if (g.degree != 1)
            return true; // not handling degree > 1
        auto p_value2 = value(g.p);
        //
        // check that p_value and p_value2 have different signs
        // check that other_p is disjoint from tabu
        // compute overlaps extending x
        //
        TRACE(arith, display_constraint(tout << "(" << other_ci << ") resolve with x" << x << " " << p_value << " " << p_value2 << " ", other_ci)
                         << "\n");
        SASSERT(g.degree > 0);
        SASSERT(p_value != 0);
        if (g.degree > f.degree)  // future: could handle this too by considering tabu to be a map into degrees.
            return true;
        if (p_value > 0 && p_value2 > 0)
            return true;
        if (p_value < 0 && p_value2 < 0)
            return true;
        if (any_of(other_p.free_vars(), [&](unsigned j) { return m_tabu[ci].contains(j); }))
            return true;

        TRACE(arith, tout << "factor (" << other_ci << ") " << other_p << " -> j" << x << "^" << g.degree << " * "
                          << g.p << "  +  " << g.q << "\n");

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

        TRACE(arith, tout << "m1 " << m1 << " m2 " << m2 << " m1m2: " << m1m2 << "\n");

        auto sign_f = value(f_p) < 0;
        SASSERT(value(f_p) != 0);

        // m1m2 * f_p + f.q >= 0
        // m1m2 * g_p + g.q >= 0
        //
        lp::constraint_index ci_a, ci_b;
        auto aj = assumption_justification();

        bool g_strict = other_k == lp::lconstraint_kind::GT;
        bool f_strict = k == lp::lconstraint_kind::LT;
        if (g_p.is_val())
            ci_a = multiply(ci, pddm.mk_val(g_p.val()));
        else if (!sign_f)
            ci_a =
                multiply(ci, add_constraint(g_p, f_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE, aj));
        else
            ci_a =
                multiply(ci, add_constraint(g_p, f_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE, aj));

        if (f_p.is_val())
            ci_b = multiply(other_ci, pddm.mk_val(f_p.val()));
        else if (sign_f)
            ci_b = multiply(other_ci,
                            add_constraint(f_p, g_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE, aj));
        else
            ci_b = multiply(other_ci,
                            add_constraint(f_p, g_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE, aj));

        auto new_ci = add(ci_a, ci_b);
        CTRACE(arith, !is_new_constraint(new_ci), display_constraint(tout << "not new ", new_ci) << "\n");
        ++c().lp_settings().stats().m_stellensatz.m_num_resolutions;
        if (!is_new_constraint(new_ci))
            return true;
        if (m_constraints[new_ci].p.degree() <= m_config.max_degree)
            init_occurs(new_ci);
        TRACE(arith, tout << "eliminate j" << x << ":\n"; 
              display_constraint(tout << "ci: ", ci) << "\n";
              display_constraint(tout << "other_ci: ", other_ci) << "\n";
              display_constraint(tout << "ci_a: ", ci_a) << "\n"; 
              display_constraint(tout << "ci_b: ", ci_b) << "\n";
              display_constraint(tout << "new_ci: ", new_ci) << "\n");

        if (conflict(new_ci))
            return false;

        uint_set new_tabu(m_tabu[ci]);
        new_tabu.insert(x);
        add_active(new_ci, new_tabu);
        return factor(new_ci) != l_false;  
    }

    bool stellensatz::conflict(lp::constraint_index ci) {
        auto const &[new_p, new_k, new_j] = m_constraints[ci];
        if (new_p.is_val() && ((new_p.val() < 0 && new_k == lp::lconstraint_kind::GE) || (new_p.val() <= 0 && new_k == lp::lconstraint_kind::GT))) {
            m_core.reset();
            m_core.push_back(ci);
            return true;
        }
        return false;
    }

    void stellensatz::conflict(svector<lp::constraint_index> const& core) {
        lp::explanation ex;
        lemma_builder new_lemma(c(), "stellensatz");
        m_constraints_in_conflict.reset();
        for (auto ci : core)
            explain_constraint(new_lemma, ci, ex);
        new_lemma &= ex;
        IF_VERBOSE(2, verbose_stream() << "stellensatz unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        c().lra_solver().settings().stats().m_nla_stellensatz++;
    }

    lbool stellensatz::model_repair() {
        for (lp::constraint_index ci = 0; ci < m_constraints.size(); ++ci)
            m_active.insert(ci);
        svector<lpvar> vars;
        for (unsigned v = 0; v < m_values.size(); ++v)
            vars.push_back(v);
        random_gen rand(c().random());
        shuffle(vars.size(), vars.begin(), rand);
        for (auto v : vars)
            if (!model_repair(v))
                return l_false;    
        for (unsigned i = vars.size(); i-- > 0;)
            set_value(vars[i]);      
        return all_of(m_constraints, [&](constraint const& c) { return constraint_is_true(c); }) ? l_true : l_undef;
    }

    bool stellensatz::model_repair(lp::lpvar v) {
        m_sup_inf.reserve(v + 1);
        auto bounds = find_bounds(v);
        auto const &[lo, inf, infs] = bounds.first;
        auto const &[hi, sup, sups] = bounds.second;
        auto has_false = any_of(infs, [&](lp::constraint_index ci) { return !constraint_is_true(ci); }) ||
                         any_of(sups, [&](lp::constraint_index ci) { return !constraint_is_true(ci); });
        TRACE(arith, tout << "j" << v << " " << infs.size() << " " << sups.size() << "\n");
        if (!has_false)
            return true;
        m_sup_inf[v] = {inf, sup};
        SASSERT(!infs.empty() || !sups.empty());
        if (infs.empty()) {
            SASSERT(!sups.empty());
            // repair v by setting it below sup
            auto f = factor(v, sup);
            m_values[v] = floor(-value(f.q) / value(f.p));
            return true;            
        }
        if (sups.empty()) {
            SASSERT(!infs.empty());
            // repair v by setting it above inf
            auto f = factor(v, inf);
            m_values[v] = ceil(-value(f.q) / value(f.p));
            return true;
        }
        if (lo <= hi && (!is_int(v) || ceil(lo) <= floor(hi))) {            
            // repair v by setting it between lo and hi assuming it is integral when v is integer
            m_values[v] = is_int(v) ? ceil(lo) : lo;
            return true;
        }

        auto resolve = [&](unsigned inf, unsigned_vector const &sups) {
            auto f = factor(v, inf);
            SASSERT(f.degree == 1);
            auto p_value = value(f.p);
            f.p *= pddm.mk_var(v);
            auto [m, f_p] = f.p.var_factors();
            return all_of(sups, [&](auto s) { return resolve_variable(v, inf, s, p_value, f, m, f_p); });
        };
        // lo > hi - pick a side and assume inf or sup and enforce order between sup and inf.
        // maybe just add constraints that are false and skip the rest?
        // remove sups and infs from active because we computed resolvents
        if (infs.size() <= 3 && sups.size() <= 3 && (infs.size() <= 2 || sups.size() <= 2)) {
            for (auto inf : infs) 
                if (!resolve(inf, sups))
                    return false;            
        }
        else if (infs.size() < sups.size()) {
            if (!resolve(inf, sups))
                return false;
            for (auto i : infs)
                if (!assume_ge(v, i, inf))
                    return false;
        }
        else {
            if (!resolve(sup, infs))
                return false;
            for (auto s : sups)
                if (!assume_ge(v, sup, s))
                    return false;
        }
        for (auto ci : infs)
            if (m_active.contains(ci))
                m_active.remove(ci);
        for (auto ci : sups)
            if (m_active.contains(ci))
                m_active.remove(ci);
        return true;
    }

    void stellensatz::set_value(lp::lpvar v) {
        auto [inf, sup] = m_sup_inf[v];
        if (inf == lp::null_ci && sup == lp::null_ci)
            return;
        else if (inf != lp::null_ci) {
            auto f = factor(v, inf);
            SASSERT(f.degree == 1);
            auto quot = -value(f.q) / value(f.p);
            bool is_strict = m_constraints[inf].k == lp::lconstraint_kind::GT;
            if (is_strict) {
                if (sup != lp::null_ci) {
                    auto g = factor(v, sup);
                    SASSERT(g.degree == 1);
                    auto quot2 = -value(g.q) / value(g.p);
                    quot = (quot + quot2) / rational(2);
                }
                else {
                    quot += rational(1);
                }
            }
            m_values[v] = is_int(v) ? ceil(quot) : quot;
        }
        else if (sup != lp::null_ci) {
            auto f = factor(v, sup);
            SASSERT(f.degree == 1);
            auto quot = -value(f.q) / value(f.p);
            bool is_strict = m_constraints[sup].k == lp::lconstraint_kind::GT;
            if (is_strict)
                quot -= rational(1);
            m_values[v] = is_int(v) ? floor(quot) : quot;
        }
    }

    // lo <= hi
    bool stellensatz::assume_ge(lpvar v, lp::constraint_index lo, lp::constraint_index hi) {
        if (lo == hi)
            return true;
        auto const &[plo, klo, jlo] = m_constraints[lo];
        auto const &[phi, khi, jhi] = m_constraints[hi];
        auto f = factor(v, lo);
        auto g = factor(v, hi);
        SASSERT(f.degree == 1);
        SASSERT(g.degree == 1);
        auto fp_value = value(f.p);
        auto gp_value = value(g.p);
        SASSERT(fp_value != 0);
        SASSERT(gp_value != 0);
        SASSERT((fp_value > 0) == (gp_value > 0));
        //
        // f.p x + f.q >= 0 <=> f.p x >= - f.q <=> x <= - f.q / f.p
        // - f.q / f.p <= - g.q / g.p
        // f.p x + f.q >= 0
        // <=>
        // x >= - f.q / f.p
        //
        // - f.q / f.p <= - g.q / g.p
        // <=>
        //    f.q / f.p >= g.q / g.p
        // <=>
        //    f.q * g.p >= g.q * f.p
        //
        auto r = (f.q * g.p) - (g.q * f.p);
        SASSERT(value(r) >= 0);
        auto new_ci = assume(r, join(klo, khi));
        m_active.insert(new_ci);
        return factor(new_ci) != l_false;   
    }

    std::pair<stellensatz::bound_info, stellensatz::bound_info> stellensatz::find_bounds(lpvar v) {
        std::pair<bound_info, bound_info> result;
        auto &[lo, inf, infs] = result.first;
        auto &[hi, sup, sups] = result.second;
        for (auto ci : m_occurs[v]) {
            if (!m_active.contains(ci))
                continue;
            auto f = factor(v, ci);
            if (vanishing(v, f, ci))  
                continue;
           
            if (f.degree > 1)
                continue;
            SASSERT(f.degree == 1);
            auto p_value = value(f.p);
            auto q_value = value(f.q);
            auto quot = -q_value / p_value;
            if (p_value < 0) {
                // p*x + q >= 0  =>  x <= -q / p if p < 0
                if (sups.empty() || hi > quot) {
                    hi = quot;
                    sup = ci;
                }
                else if (hi == quot && m_constraints[ci].k == lp::lconstraint_kind::GT) {
                    sup = ci;
                }
                sups.push_back(ci);
            }
            else {
                // p*x + q >= 0  =>  x >= -q / p if p > 0
                if (infs.empty() || lo < quot) {
                    lo = quot;
                    inf = ci;
                }
                else if (lo == quot && m_constraints[ci].k == lp::lconstraint_kind::GT) {
                    inf = ci;
                }
                infs.push_back(ci);
            }
        }
        return result;
    }

    bool stellensatz::vanishing(lpvar x, factorization const &f, lp::constraint_index ci) {
        if (f.p.is_zero())
            return false;
        auto p_value = value(f.p);
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
        if (is_new_constraint(new_ci)) {
            init_occurs(new_ci);
            uint_set new_tabu(m_tabu[ci]);
            new_tabu.insert(x);
            add_active(new_ci, new_tabu);
        }
        ++c().lp_settings().stats().m_stellensatz.m_num_vanishings;
        return true;
    }

    lbool stellensatz::factor(lp::constraint_index ci) {
        auto const &[p, k, j] = m_constraints[ci];
        auto [vars, q] = p.var_factors(); // p = vars * q

        auto add_new = [&](lp::constraint_index new_ci) {
            TRACE(arith, display_constraint(tout << "factor ", new_ci) << "\n");
            if (conflict(new_ci))
                return l_false;
            init_occurs(new_ci);
            auto new_tabu(m_tabu[ci]);
            add_active(new_ci, new_tabu);
            return l_true;
        };

        TRACE(arith, tout << "factor (" << ci << ") " << p << " q: " << q << " vars: " << vars << "\n");     
        if (vars.empty())
            return l_undef;
        for (auto v : vars) {
            if (value(v) == 0)
                return l_undef;
        }
        vector<dd::pdd> muls;
        muls.push_back(q);
        for (auto v : vars)
            muls.push_back(muls.back() * pddm.mk_var(v));
        auto new_ci = ci;
        SASSERT(muls.back() == p);
        for (unsigned i = vars.size(); i-- > 0;) {
            auto pv = pddm.mk_var(vars[i]);
            auto k = value(vars[i]) > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::LT;
            new_ci = divide(new_ci, assume(pv, k), muls[i]);
        }
        if (m_active.contains(ci))
            m_active.remove(ci);
        return add_new(new_ci);
    }

    bool stellensatz::is_new_constraint(lp::constraint_index ci) const {
        return ci + 1 == m_constraints.size();
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
    // check if core depends on an assumption
    // identify the maximal assumption
    // undo m_constraints down to max_ci.
    // negate max_ci
    // propagate it using remaining external and assumptions.
    // find a new satisfying assignment (if any) before continuing.
    // 
    bool stellensatz::backtrack(svector<lp::constraint_index> const &core) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        if (assumptions.empty())
            return false;
        lp::constraint_index max_ci = 0;
        for (auto ci : assumptions)
            max_ci = std::max(ci, max_ci);
        TRACE(arith, tout << "max " << max_ci << " external " << external << " assumptions " << assumptions << "\n";
              display_constraint(tout, max_ci) << "\n";);
        // TODO, we can in reality replay all constraints that don't depend on max_ci
        vector<constraint> replay;
        unsigned i = 0;
        for (auto ci : external) {
            if (ci > max_ci)
                replay.push_back(m_constraints[ci]);
            else
                external[i++] = ci;
        }
        external.shrink(i);
        auto [p, k, j] = m_constraints[max_ci];
        while (m_constraints.size() > max_ci)
            m_trail.pop_scope(1);
        
        for (auto const &[_p, _k, _j] : replay) {
            auto ci = add_constraint(_p, _k, _j);
            init_occurs(ci);
            external.push_back(ci);
        }
        assumptions.erase(max_ci);
        external.append(assumptions);
        propagation_justification prop{external};
        auto new_ci = add_constraint(p, negate(k), prop);
        TRACE(arith, display_constraint(tout << "backtrack ", new_ci) << "\n");
        init_occurs(new_ci);
        return true;
    }

    bool stellensatz::core_is_linear(svector<lp::constraint_index> const &core) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        return all_of(assumptions, [&](auto ci) { return has_term_offset(m_constraints[ci].p); });
    }

    void stellensatz::explain_constraint(lp::constraint_index ci, svector<lp::constraint_index> &external,
                                         svector<lp::constraint_index> &assumptions) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);
        auto &[p, k, b] = m_constraints[ci];
        if (std::holds_alternative<external_justification>(b)) {
            external.push_back(ci);
        }
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto &m = std::get<multiplication_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<eq_justification>(b)) {
            auto &m = std::get<eq_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<division_justification>(b)) {
            auto &m = std::get<division_justification>(b);
            explain_constraint(m.ci, external, assumptions);
            explain_constraint(m.divisor, external, assumptions);
        }
        else if (std::holds_alternative<substitute_justification>(b)) {
            auto &m = std::get<substitute_justification>(b);
            explain_constraint(m.ci, external, assumptions);
            explain_constraint(m.ci_eq, external, assumptions);
        }
        else if (std::holds_alternative<propagation_justification>(b)) {
            auto &m = std::get<propagation_justification>(b);
            for (auto c : m.cs)
                explain_constraint(c, external, assumptions);
        }
        else if (std::holds_alternative<addition_justification>(b)) {
            auto &m = std::get<addition_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<multiplication_poly_justification>(b)) {
            auto &m = std::get<multiplication_poly_justification>(b);
            explain_constraint(m.ci, external, assumptions);
        }
        else if (std::holds_alternative<assumption_justification>(b)) {
            assumptions.push_back(ci);
        }
        else if (std::holds_alternative<gcd_justification>(b)) {
            auto &m = std::get<gcd_justification>(b);
            explain_constraint(m.ci, external, assumptions);
        }
        else
            UNREACHABLE();
    }

    //
    // a constraint can be explained by a set of bounds used as justifications
    // and by an original constraint.
    // 
    void stellensatz::explain_constraint(lemma_builder &new_lemma, lp::constraint_index ci, lp::explanation &ex) {
        svector<lp::constraint_index> external, assumptions;
        explain_constraint(ci, external, assumptions);
        for (auto ci : external) {
            auto &[p, k, b] = m_constraints[ci];
            auto dep = std::get<external_justification>(b);
            c().lra_solver().push_explanation(dep.dep, ex);
        }
        for (auto ci : assumptions) {
            auto &[p, k, b] = m_constraints[ci];
            auto [t, coeff] = to_term_offset(p);
            new_lemma |= ineq(t, negate(k), -coeff);
        }
    }
 
    rational stellensatz::value(dd::pdd const& p) const {
        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned v) -> rational { return value(v); };
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
        if (k == lp::lconstraint_kind::EQ) {
            auto left = assume(p, lp::lconstraint_kind::GE);
            auto right = assume(-p, lp::lconstraint_kind::GE);
            return add_constraint(p, k, eq_justification{left, right});
        }
        u_dependency *d = nullptr;
        auto has_bound = [&](rational const& a, lpvar x, rational const& b) {
            rational bound;
            bool is_strict = false;
            if (a == 1 && k == lp::lconstraint_kind::GE && c().lra_solver().has_lower_bound(x, d, bound, is_strict) &&
                bound >= -b) {
                return true;
            }
            if (a == 1 && k == lp::lconstraint_kind::GT && c().lra_solver().has_lower_bound(x, d, bound, is_strict) &&
                (bound > -b || (is_strict && bound >= -b))) {
                return true;
            }
            if (a == -1 && k == lp::lconstraint_kind::GE && c().lra_solver().has_upper_bound(x, d, bound, is_strict) &&
                bound <= -b) {
                return true;
            }
            if (a == -1 && k == lp::lconstraint_kind::GT && c().lra_solver().has_upper_bound(x, d, bound, is_strict) &&
                (bound < -b || (is_strict && bound <= -b))) {
                return true;
            }
            return false;
        };

        if (p.is_unilinear() && has_bound(p.hi().val(), p.var(), p.lo().val()))
            // ax + b ~k~ 0
            return add_constraint(p, k, external_justification(d));        
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
        if (m_has_occurs[ci])
            return;
        struct undo_occurs : public trail {
            stellensatz & s;
            lp::constraint_index ci;
            undo_occurs(stellensatz & s, lp::constraint_index ci) : s(s), ci(ci) {}
            void undo() override {
                s.remove_occurs(ci);
            }
        };
        m_trail.push(undo_occurs(*this, ci));
        m_has_occurs[ci] = true;
        auto const &con = m_constraints[ci];
        for (auto v : con.p.free_vars())
            m_occurs[v].push_back(ci);
        
    }

    void stellensatz::remove_occurs(lp::constraint_index ci) {
        SASSERT(m_has_occurs[ci]);
        m_has_occurs[ci] = false;            
        auto const &con = m_constraints[ci];
        for (auto v : con.p.free_vars())
            m_occurs[v].pop_back();
    }

    bool stellensatz::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return c().lra_solver().var_is_int(v); });
    }

    bool stellensatz::is_int(dd::pdd const &p) const {
        return is_int(p.free_vars());
    }

    bool stellensatz::constraint_is_true(lp::constraint_index ci) const {
        return constraint_is_true(m_constraints[ci]);
    }

    bool stellensatz::constraint_is_true(constraint const &c) const {
        auto const& [p, k, j] = c;
        auto lhs = value(p);
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
        else if (std::holds_alternative<eq_justification>(j)) {
            auto &m = std::get<eq_justification>(j);
            out << "(" << m.left << ") & (" << m.right << ")";
        } 
        else if (std::holds_alternative<substitute_justification>(j)) {
            auto m = std::get<substitute_justification>(j);
            out << "(" << m.ci << ") (" << m.ci_eq << ") by j" << m.v << " := " << m.p;
        }
        else if (std::holds_alternative<propagation_justification>(j)) {
            auto &m = std::get<propagation_justification>(j);
            out << "propagate ";
            for (auto c : m.cs)
                out << "(" << c << ") ";
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
            if (std::holds_alternative<eq_justification>(j)) {
                auto m = std::get<eq_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            if (std::holds_alternative<propagation_justification>(j)) {
                auto m = std::get<propagation_justification>(j);
                todo.append(m.cs);
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

    void stellensatz::updt_params(params_ref const& p) {
        smt_params_helper sp(p);
        m_config.max_degree = sp.arith_nl_stellensatz_max_degree();
        m_config.max_conflicts = sp.arith_nl_stellensatz_max_conflicts();
        m_config.max_constraints = sp.arith_nl_stellensatz_max_constraints();
        m_config.strategy = sp.arith_nl_stellensatz_strategy();
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

    lbool stellensatz::solver::solve(svector<lp::constraint_index>& core) {
        init();
        lbool r = solve_lra();
        if (r == l_true) 
            r = solve_lia();
        
        if (r == l_false) { 
            core.reset();
            for (auto p : m_ex)
                core.push_back(m_internal2external_constraints[p.ci()]);
        }
        return r;
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
        case lp::lia_move::sat: 
            return l_true;
        case lp::lia_move::conflict: 
            return l_false;
        default:  // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }

    // update values using the model
    void stellensatz::solver::update_values(vector<rational>& values) {
        std::unordered_map<lpvar, rational> _values;
        lra_solver->get_model(_values);
        unsigned sz = values.size();
        for (unsigned i = 0; i < sz; ++i) 
            values[i] = _values[i];
        TRACE(arith, for (unsigned i = 0; i < sz; ++i) tout << "j" << i << " := " << values[i] << "\n";);
    }
}
