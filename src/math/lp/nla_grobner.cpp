 /*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    nla_grobner.cpp

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#include "util/uint_set.h"
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
#include "math/grobner/pdd_solver.h"
#include "math/dd/pdd_interval.h"
#include "math/dd/pdd_eval.h"

namespace nla {

    grobner::grobner(core* c):
        common(c),
        m_pdd_manager(m_core.lra.number_of_vars()),
        m_solver(m_core.m_reslim, m_core.lra.dep_manager(), m_pdd_manager),
        lra(m_core.lra),
        m_quota(m_core.params().arith_nl_gr_q())
    {}

    lp::lp_settings& grobner::lp_settings() {
        return c().lp_settings();
    }

    void grobner::operator()() {

        if (lra.column_count() > 5000)
            return;

        if (m_quota == 0)
            m_quota = c().params().arith_nl_gr_q();                    

        if (m_quota == 1) {
            m_delay_base++;
            m_delay = m_delay_base;
            m_quota = c().params().arith_nl_gr_q();
        }

        if (m_delay > 0) {
            --m_delay;
            return;
        }
        
        lp_settings().stats().m_grobner_calls++;
        find_nl_cluster();        
        if (!configure())
            return;
        m_solver.saturate();

        if (m_delay_base > 0)
            --m_delay_base;
        
        try {

            if (is_conflicting())
                return;

            if (propagate_eqs())
                return;
            
            if (propagate_factorization())
                return;
            
            if (propagate_linear_equations())
                return;
            
        }
        catch (...) {
            
        }

        // DEBUG_CODE(for (auto e : m_solver.equations()) check_missing_propagation(*e););

        // for (auto e : m_solver.equations()) check_missing_propagation(*e);
        
        ++m_delay_base;
        if (m_quota > 0)
           --m_quota;

        IF_VERBOSE(3, verbose_stream() << "grobner miss, quota " << m_quota << "\n");
        IF_VERBOSE(4, diagnose_pdd_miss(verbose_stream()));
    }

    dd::solver::equation_vector const& grobner::core_equations(bool all_eqs) {
        flet<bool> _add_all(m_add_all_eqs, all_eqs);
        find_nl_cluster();        
        if (!configure()) 
            throw dd::pdd_manager::mem_out();
        return m_solver.equations();
    }

    bool grobner::is_conflicting() {
        for (auto eq : m_solver.equations()) {
            if (is_conflicting(*eq)) {
                lp_settings().stats().m_grobner_conflicts++;
                TRACE("grobner", m_solver.display(tout));
                IF_VERBOSE(3, verbose_stream() << "grobner conflict\n");
                return true;
            }
        }
        return false;
    }

    bool grobner::propagate_eqs() {
        unsigned changed = 0;
        for (auto eq : m_solver.equations()) 
            if (propagate_fixed(*eq) && ++changed >= m_solver.number_of_conflicts_to_report())
                return true;
        return changed > 0;
    }

    bool grobner::propagate_factorization() {
        unsigned changed = 0;
        for (auto eq : m_solver.equations()) 
            if (propagate_factorization(*eq) && ++changed >= m_solver.number_of_conflicts_to_report())
                return true;
        return changed > 0;
    }

    /**
       \brief detect equalities 
       - k*x = 0, that is x = 0
       - ax + b = 0
    */
    typedef lp::lar_term term;
    bool grobner::propagate_fixed(const dd::solver::equation& eq) {        
        dd::pdd const& p = eq.poly();
        if (p.is_unary()) {
            unsigned v = p.var();
            if (c().var_is_fixed(v))
                return false;

            ineq new_eq(v, llc::EQ, rational::zero());
            if (c().ineq_holds(new_eq))
                return false;
            new_lemma lemma(c(), "pdd-eq");
            add_dependencies(lemma, eq);
            lemma |= new_eq;
            return true;
        }
        if (p.is_offset()) {
            unsigned v = p.var();
            if (c().var_is_fixed(v))
                return false;
            rational a = p.hi().val();
            rational b = -p.lo().val();
            rational d = lcm(denominator(a), denominator(b));
            a *= d;
            b *= d;
            ineq new_eq(term(a, v), llc::EQ, b);
            if (c().ineq_holds(new_eq))
                return false;
            new_lemma lemma(c(), "pdd-eq");
            add_dependencies(lemma, eq);
            lemma |= new_eq;
            return true;
        }

        return false;
    }

    /**
       \brief detect simple factors
       x*q = 0 => x = 0 or q = 0
     */

    bool grobner::propagate_factorization(const dd::solver::equation& eq) {
        dd::pdd const& p = eq.poly();
        auto [vars, q] = p.var_factors();
        if (vars.empty() || !q.is_linear())
            return false;

        // IF_VERBOSE(0, verbose_stream() << "factored " << q << " : " << vars << "\n");

        term t;
        rational lc(1);
        auto ql = q;
        while (!ql.is_val()) {
            lc = lcm(lc, denominator(ql.hi().val()));
            ql = ql.lo();
        }
        lc = lcm(denominator(ql.val()), lc);

        while (!q.is_val()) {
            t.add_monomial(lc*q.hi().val(), q.var());
            q = q.lo();
        }
        vector<ineq> ineqs;
        for (auto v : vars)
            ineqs.push_back(ineq(v, llc::EQ, rational::zero()));
        ineqs.push_back(ineq(t, llc::EQ, -lc*q.val()));
        for (auto const& i : ineqs)
            if (c().ineq_holds(i))
                return false;

        new_lemma lemma(c(), "pdd-factored");
        add_dependencies(lemma, eq);
        for (auto const& i : ineqs)
            lemma |= i;
        //lemma.display(verbose_stream());
        return true;
    }

    void grobner::explain(dd::solver::equation const& eq, lp::explanation& exp) {
        u_dependency_manager dm;
        vector<unsigned, false> lv;
        dm.linearize(eq.dep(), lv);
        for (unsigned ci : lv)
            exp.push_back(ci);
    }


    void grobner::add_dependencies(new_lemma& lemma, const dd::solver::equation& eq) {
        lp::explanation exp;
        explain(eq, exp);
        lemma &= exp;
    }

    bool grobner::configure() {
        m_solver.reset();
        try {
            set_level2var();
            TRACE("grobner",
                  tout << "base vars: ";
                  for (lpvar j : c().active_var_set())
                      if (lra.is_base(j))
                          tout << "j" << j << " ";
                  tout << "\n");
            for (lpvar j : c().active_var_set()) {
                if (lra.is_base(j))
                    add_row(lra.basic2row(j));
                
                if (c().is_monic_var(j) && c().var_is_fixed(j))
                    add_fixed_monic(j);
            }
        }
        catch (dd::pdd_manager::mem_out) {
            IF_VERBOSE(2, verbose_stream() << "pdd throw\n");
            return false;
        }
        TRACE("grobner", m_solver.display(tout));

#if 0
        IF_VERBOSE(2, m_pdd_grobner.display(verbose_stream()));
        dd::pdd_eval eval(m_pdd_manager);
        eval.var2val() = [&](unsigned j){ return val(j); };
        for (auto* e : m_pdd_grobner.equations()) {
            dd::pdd p = e->poly();
            rational v = eval(p);
            if (p.is_linear() && !eval(p).is_zero()) {
                IF_VERBOSE(0, verbose_stream() << "violated linear constraint " << p << "\n");
            }
        }
#endif
   
        struct dd::solver::config cfg;
        cfg.m_max_steps = m_solver.equations().size();
        cfg.m_max_simplified = c().params().arith_nl_grobner_max_simplified();
        cfg.m_eqs_growth = c().params().arith_nl_grobner_eqs_growth();
        cfg.m_expr_size_growth = c().params().arith_nl_grobner_expr_size_growth();
        cfg.m_expr_degree_growth = c().params().arith_nl_grobner_expr_degree_growth();
        cfg.m_number_of_conflicts_to_report = c().params().arith_nl_grobner_cnfl_to_report();
        m_solver.set(cfg);
        m_solver.adjust_cfg();
        m_pdd_manager.set_max_num_nodes(10000); // or something proportional to the number of initial nodes.

        return true;
    }

    std::ostream& grobner::diagnose_pdd_miss(std::ostream& out) {

        // m_pdd_grobner.display(out);

        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned j){ return val(j); };
        for (auto* e : m_solver.equations()) {
            dd::pdd p = e->poly();
            rational v = eval(p);
            if (!v.is_zero()) {
                out << p << " := " << v << "\n";
            }
        }  
  
        for (unsigned j = 0; j < lra.number_of_vars(); ++j) {
            if (lra.column_has_lower_bound(j) || lra.column_has_upper_bound(j)) {
                out << j << ": [";
                if (lra.column_has_lower_bound(j)) out << lra.get_lower_bound(j);
                out << "..";
                if (lra.column_has_upper_bound(j)) out << lra.get_upper_bound(j);
                out << "]\n";
            }
        }              
        return out;
    }

    bool grobner::equation_is_true(dd::solver::equation const& eq) {
        if (any_of(eq.poly().free_vars(), [&](unsigned j) { return lra.column_is_free(j); }))
            return true;
        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned j){ return val(j); };
        return eval(eq.poly()) == 0;
    }
    

    bool grobner::is_conflicting(const dd::solver::equation& e) {
        if (equation_is_true(e))
            return false;
        auto& di = c().m_intervals.get_dep_intervals();
        dd::pdd_interval evali(di);
        evali.var2interval() = [this](lpvar j, bool deps, scoped_dep_interval& a) {
            if (deps) c().m_intervals.set_var_interval<dd::w_dep::with_deps>(j, a);
            else c().m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
        };
        scoped_dep_interval i(di), i_wd(di);
        evali.get_interval<dd::w_dep::without_deps>(e.poly(), i);    
        if (!di.separated_from_zero(i)) {
            TRACE("grobner", m_solver.display(tout << "not separated from 0 ", e) << "\n";
                  evali.get_interval_distributed<dd::w_dep::without_deps>(e.poly(), i);
                  tout << "separated from 0: " << di.separated_from_zero(i) << "\n";
                  for (auto j : e.poly().free_vars()) {
                      scoped_dep_interval a(di);
                      c().m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
                      c().m_intervals.display(tout << "j" << j << " ", a); tout << " ";
                  }
                  tout << "\n");

            
            if (add_horner_conflict(e))
                return true;
#if 0
            if (add_nla_conflict(e)) 
                return true;
#endif
            return false;
        }
        evali.get_interval<dd::w_dep::with_deps>(e.poly(), i_wd);  
        std::function<void (const lp::explanation&)> f = [this](const lp::explanation& e) {
            new_lemma lemma(m_core, "pdd");
            lemma &= e;
        };
        if (di.check_interval_for_conflict_on_zero(i_wd, e.dep(), f)) {
            TRACE("grobner", m_solver.display(tout << "conflict ", e) << "\n");
            return true;
        }
        else {
#if 0
            if (add_nla_conflict(e)) 
                return true;
#endif
            TRACE("grobner", m_solver.display(tout << "no conflict ", e) << "\n");
            return false;
        }
    }

    bool grobner::propagate_linear_equations() {
        unsigned changed = 0;
        m_mon2var.clear();
        for (auto const& m : c().emons()) 
            m_mon2var[m.vars()] = m.var();
        
        for (auto eq : m_solver.equations()) 
            if (propagate_linear_equations(*eq))
                ++changed;
        return changed > 0;
    }
        
    bool grobner::propagate_linear_equations(dd::solver::equation const& e) {
        if (equation_is_true(e))
            return false;
        rational value(0);
        for (auto const& [coeff, vars] : e.poly()) {
            if (vars.empty())
                value += coeff;
            else if (vars.size() == 1)
                value += coeff*val(vars[0]);
            else if (m_mon2var.find(vars) == m_mon2var.end())
                return false;
            else
                value += coeff*val(m_mon2var.find(vars)->second);
        }
        if (value == 0)
            return false;

        rational lc(1);
        for (auto const& [coeff, vars] : e.poly()) 
            lc = lcm(denominator(coeff), lc);
        
        vector<std::pair<lp::mpq, unsigned>> coeffs;
        rational offset(0);

        for (auto const& [coeff, vars] : e.poly()) {
            if (vars.size() == 0)
                offset -= lc*coeff;
            else if (vars.size() == 1)
                coeffs.push_back({lc*coeff, vars[0]});
            else
                coeffs.push_back({lc*coeff, m_mon2var.find(vars)->second});
        }                    

        lp::lpvar j = c().lra.add_term(coeffs, UINT_MAX);
        c().lra.update_column_type_and_bound(j, lp::lconstraint_kind::EQ, offset, e.dep());
        c().m_check_feasible = true; 
        return true;
    }


    void grobner::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, svector<lpvar> & q) {
        if (c().active_var_set_contains(j))
            return;
        c().insert_to_active_var_set(j);
        if (c().is_monic_var(j)) {
            const monic& m = c().emons()[j];
            for (auto fcn : factorization_factory_imp(m, m_core)) 
                for (const factor& fc: fcn) 
                    q.push_back(var(fc));        
        }

        if (c().var_is_fixed(j))
            return;
        const auto& matrix = lra.A_r();
        for (auto & s : matrix.m_columns[j]) {
            unsigned row = s.var();
            if (m_rows.contains(row))
                continue;
            m_rows.insert(row);
            unsigned k = lra.get_base_column_in_row(row);
            // grobner bassis does not know about integer constraints
            if (lra.column_is_free(k) && !m_add_all_eqs && k != j)
                continue;
            // a free column over the reals can be assigned
            if (lra.column_is_free(k) && k != j && !lra.var_is_int(k)) 
                continue;
            CTRACE("grobner", matrix.m_rows[row].size() > c().params().arith_nl_grobner_row_length_limit(),
                   tout << "ignore the row " << row << " with the size " << matrix.m_rows[row].size() << "\n";);
            // limits overhead of grobner equations, unless this is for extracting a complete COI of the non-satisfied subset.
            if (!m_add_all_eqs && matrix.m_rows[row].size() > c().params().arith_nl_horner_row_length_limit())
                continue;
            for (auto& rc : matrix.m_rows[row]) 
                add_var_and_its_factors_to_q_and_collect_new_rows(rc.var(), q);
        }
    }

    const rational& grobner::val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep) {
        auto* d = lra.get_bound_constraint_witnesses_for_column(j);
        if (d)
            dep = c().m_intervals.mk_join(dep, d);
        return lra.column_lower_bound(j).x;
    }

    dd::pdd grobner::pdd_expr(const rational& coeff, lpvar j, u_dependency*& dep) {
        dd::pdd r = m_pdd_manager.mk_val(coeff);
        sbuffer<lpvar> vars;
        vars.push_back(j);
        u_dependency* zero_dep = dep;
        while (!vars.empty()) {
            j = vars.back();
            vars.pop_back();
            if (c().params().arith_nl_grobner_subs_fixed() > 0 && c().var_is_fixed_to_zero(j)) {
                r = m_pdd_manager.mk_val(val_of_fixed_var_with_deps(j, zero_dep));
                dep = zero_dep;
                return r;
            }
            if (c().params().arith_nl_grobner_subs_fixed() == 1 && c().var_is_fixed(j))
                r *= val_of_fixed_var_with_deps(j, dep);
            else if (!c().is_monic_var(j))
                r *= m_pdd_manager.mk_var(j);
            else
                for (lpvar k : c().emons()[j].vars())
                    vars.push_back(k);        
        }
        return r;
    }

    /**
       \brief convert p == 0 into a solved form v == r, such that
       v has bounds [lo, oo) iff r has bounds [lo', oo)
       v has bounds (oo,hi]  iff r has bounds (oo,hi']

       The solved form allows the Grobner solver identify more bounds conflicts.
       A bad leading term can miss bounds conflicts.
       For example for x + y + z == 0 where x, y : [0, oo) and z : (oo,0]
       we prefer to solve z == -x - y instead of x == -z - y
       because the solution -z - y has neither an upper, nor a lower bound.
    */
    bool grobner::is_solved(dd::pdd const& p, unsigned& v, dd::pdd& r) {
        if (!p.is_linear())
            return false;
        r = p;
        unsigned num_lo = 0, num_hi = 0;
        unsigned lo = 0, hi = 0;
        rational lc, hc, c;
        while (!r.is_val()) {
            SASSERT(r.hi().is_val());
            v = r.var();
            rational val = r.hi().val();
            switch (lra.get_column_type(v)) {
            case lp::column_type::lower_bound:
                if (val > 0) num_lo++, lo = v, lc = val; else num_hi++, hi = v, hc = val;
                break;
            case lp::column_type::upper_bound:
                if (val < 0) num_lo++, lo = v, lc = val; else num_hi++, hi = v, hc = val;
                break;
            case lp::column_type::fixed:
            case lp::column_type::boxed:
                break;
            default:
                return false;
            }
            if (num_lo > 1 && num_hi > 1)
                return false;
            r = r.lo();
        }
        if (num_lo == 1 && num_hi > 1) {
            v = lo;
            c = lc;
        }
        else if (num_hi == 1 && num_lo > 1) {
            v = hi;
            c = hc;
        }
        else
            return false;
    
        r = c*m_pdd_manager.mk_var(v) - p;
        if (c != 1)
            r = r * (1/c);
        return true;
    }

    /**
       \brief add an equality to grobner solver, convert it to solved form if available.
    */    
    void grobner::add_eq(dd::pdd& p, u_dependency* dep) {
        unsigned v;
        dd::pdd q(m_pdd_manager);
        m_solver.simplify(p, dep);
        if (is_solved(p, v, q)) 
            m_solver.add_subst(v, q, dep);
        else         
            m_solver.add(p, dep);
    }

    void grobner::add_fixed_monic(unsigned j) {
        u_dependency* dep = nullptr;
        dd::pdd r = m_pdd_manager.mk_val(rational(1));
        for (lpvar k : c().emons()[j].vars())
            r *= pdd_expr(rational::one(), k, dep);
        r -= val_of_fixed_var_with_deps(j, dep);
        add_eq(r, dep);
    }

    void grobner::add_row(const std_vector<lp::row_cell<rational>> & row) {
        u_dependency *dep = nullptr;
        rational val;
        dd::pdd sum = m_pdd_manager.mk_val(rational(0));
        for (const auto &p : row) 
            sum += pdd_expr(p.coeff(), p.var(), dep);
        TRACE("grobner", c().print_row(row, tout) << " " << sum << "\n");
        add_eq(sum, dep);
    }

    void grobner::find_nl_cluster() {        
        prepare_rows_and_active_vars();
        svector<lpvar> q;
        TRACE("grobner", for (lpvar j : c().m_to_refine) print_monic(c().emons()[j], tout) << "\n";);
          
        for (lpvar j : c().m_to_refine)
            q.push_back(j);
    
        while (!q.empty()) {
            lpvar j = q.back();        
            q.pop_back();
            add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
        }
        TRACE("grobner", tout << "vars in cluster: ";
              for (lpvar j : c().active_var_set()) tout << "j" << j << " "; tout << "\n";
              display_matrix_of_m_rows(tout);
              );
    }

    void grobner::prepare_rows_and_active_vars() {
        m_rows.reset();
        c().clear_active_var_set();
    }


    void grobner::display_matrix_of_m_rows(std::ostream & out) const {
        const auto& matrix = lra.A_r();
        out << m_rows.size() << " rows" << "\n";
        out << "the matrix\n";          
        for (const auto & r : matrix.m_rows) 
            c().print_row(r, out) << std::endl;
    }
    
    void grobner::set_level2var() {
        unsigned n = lra.column_count();
        unsigned_vector sorted_vars(n), weighted_vars(n);
        for (unsigned j = 0; j < n; j++) {
            sorted_vars[j] = j;
            weighted_vars[j] = c().get_var_weight(j);
        }
#if 1
        // potential update to weights
        for (unsigned j = 0; j < n; j++) {
            if (c().is_monic_var(j) && c().m_to_refine.contains(j)) {
                for (lpvar k : c().m_emons[j].vars()) {
                    weighted_vars[k] += 6;
                }
            }
        }
#endif

        std::sort(sorted_vars.begin(), sorted_vars.end(), [&](unsigned a, unsigned b) {
            unsigned wa = weighted_vars[a];
            unsigned wb = weighted_vars[b];
            return wa < wb || (wa == wb && a < b); });

        unsigned_vector l2v(n);
        for (unsigned j = 0; j < n; j++)
            l2v[j] = sorted_vars[j];

        m_pdd_manager.reset(l2v);

        TRACE("grobner",
            for (auto v : sorted_vars)
                tout << "j" << v << " w:" << weighted_vars[v] << " ";
        tout << "\n");
    }

    bool grobner::is_nla_conflict(const dd::solver::equation& eq) {
        vector<dd::pdd> eqs;
        eqs.push_back(eq.poly());
        return l_false == c().m_nra.check(eqs);
    }

    bool grobner::add_horner_conflict(const dd::solver::equation& eq) {
        nex_creator& nc = m_nex_creator;
        nc.pop(0);
        nex_creator::sum_factory sum(nc);
        u_map<nex_var*> var2nex;
        for (auto v : eq.poly().free_vars()) 
            var2nex.insert(v, nc.mk_var(v));
        unsigned mx = 0;
        for (auto v : eq.poly().free_vars())
            mx = std::max(v, mx);
        nc.set_number_of_vars(mx + 1);
        for (auto const& [coeff, vars] : eq.poly()) {
            switch (vars.size()) {
            case 0:
                sum += nc.mk_scalar(coeff);
                break;
            case 1:
                sum += nc.mk_mul(coeff, var2nex[vars[0]]);
                break;
            default:
                nc.m_mk_mul.reset();
                nc.m_mk_mul *= coeff;
                for (auto v : vars)
                    nc.m_mk_mul *= var2nex[v];
                sum += nc.m_mk_mul.mk();
                break;
            }
        }
        nex* e = nc.simplify(sum.mk());
        if (e->get_degree() < 2 || !e->is_sum())
            return false;

        auto dep = eq.dep();
        cross_nested cn(
            [this, dep](const nex* n) { return c().m_intervals.check_nex(n, dep);  },
            [this](unsigned j)   { return c().var_is_fixed(j); },
            [this]() { return c().random(); }, nc);
        cn.run(to_sum(e));
        bool ret = cn.done();
        return ret;
    }

    bool grobner::add_nla_conflict(const dd::solver::equation& eq) {
        if (is_nla_conflict(eq)) {
            new_lemma lemma(m_core,"nla-conflict");
            lp::explanation exp;
            explain(eq, exp);
            lemma &= exp;
            return true;
        }
        return false;
    }


    void grobner::check_missing_propagation(const dd::solver::equation& e) { 
        bool is_confl = is_nla_conflict(e);
        CTRACE("grobner", is_confl, m_solver.display(tout << "missed conflict ", e););
        if (is_confl) {
            IF_VERBOSE(2, verbose_stream() << "missed conflict\n");
            return;
        }
        //lbool r = c().m_nra.check_tight(e.poly());
        //CTRACE("grobner", r == l_false, m_solver.display(tout << "tight equality ", e););
    }


}
