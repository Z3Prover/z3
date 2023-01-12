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
#include "math/lp/nex.h"
#include "math/grobner/pdd_solver.h"
#include "math/dd/pdd_interval.h"
#include "math/dd/pdd_eval.h"

namespace nla {

    grobner::grobner(core* c):
        common(c),
        m_pdd_manager(m_core.m_lar_solver.number_of_vars()),
        m_solver(m_core.m_reslim, m_pdd_manager),
        m_lar_solver(m_core.m_lar_solver)

    {}

    lp::lp_settings& grobner::lp_settings() {
        return c().lp_settings();
    }

    void grobner::operator()() {
        unsigned& quota = c().m_nla_settings.grobner_quota;
        if (quota == 1)
            return;

        lp_settings().stats().m_grobner_calls++;
        find_nl_cluster();        
        configure();
        m_solver.saturate();

        if (is_conflicting())
            return;

        try {
            if (propagate_bounds())
                return;

            if (propagate_eqs())
                return;

            if (propagate_factorization())
                return;
        }
        catch (...) {
            
        }

        if (quota > 1)
            quota--;

        IF_VERBOSE(2, verbose_stream() << "grobner miss, quota " << quota << "\n");
        IF_VERBOSE(4, diagnose_pdd_miss(verbose_stream()));

#if 0
        // diagnostics: did we miss something
        vector<dd::pdd> eqs;
        for (auto eq : m_solver.equations())
            eqs.push_back(eq->poly());
        c().m_nra.check(eqs);
#endif
    }

    bool grobner::is_conflicting() {
        unsigned conflicts = 0;
        for (auto eq : m_solver.equations()) 
            if (is_conflicting(*eq) && ++conflicts >= m_solver.number_of_conflicts_to_report())
                break;

        if (conflicts > 0) 
            lp_settings().stats().m_grobner_conflicts++;

        TRACE("grobner", m_solver.display(tout));
        IF_VERBOSE(2, if (conflicts > 0) verbose_stream() << "grobner conflict\n");

        return conflicts > 0;
    }

    bool grobner::propagate_bounds() {
        unsigned changed = 0;
        for (auto eq : m_solver.equations()) 
            if (propagate_bounds(*eq) && ++changed >= m_solver.number_of_conflicts_to_report())
                return true;
        return changed > 0;
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
        //IF_VERBOSE(0, verbose_stream() << p << "\n");
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
        while (!q.is_val()) {
            t.add_monomial(q.hi().val(), q.var());
            q = q.lo();
        }
        vector<ineq> ineqs;
        for (auto v : vars)
            ineqs.push_back(ineq(v, llc::EQ, rational::zero()));
        ineqs.push_back(ineq(t, llc::EQ, -q.val()));
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


    void grobner::add_dependencies(new_lemma& lemma, const dd::solver::equation& eq) {
        lp::explanation ex;
        u_dependency_manager dm;
        vector<unsigned, false> lv;
        dm.linearize(eq.dep(), lv);
        for (unsigned ci : lv)
            ex.push_back(ci);
        lemma &= ex;
    }

    void grobner::configure() {
        m_solver.reset();
        try {
            set_level2var();
            TRACE("grobner",
                  tout << "base vars: ";
                  for (lpvar j : c().active_var_set())
                      if (m_lar_solver.is_base(j))
                          tout << "j" << j << " ";
                  tout << "\n");
            for (lpvar j : c().active_var_set()) {
                if (m_lar_solver.is_base(j))
                    add_row(m_lar_solver.basic2row(j));
                
                if (c().is_monic_var(j) && c().var_is_fixed(j))
                    add_fixed_monic(j);
            }
        }
        catch (...) {
            IF_VERBOSE(2, verbose_stream() << "pdd throw\n");
            return;
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
        cfg.m_max_simplified = c().m_nla_settings.grobner_max_simplified;
        cfg.m_eqs_growth = c().m_nla_settings.grobner_eqs_growth;
        cfg.m_expr_size_growth = c().m_nla_settings.grobner_expr_size_growth;
        cfg.m_expr_degree_growth = c().m_nla_settings.grobner_expr_degree_growth;
        cfg.m_number_of_conflicts_to_report = c().m_nla_settings.grobner_number_of_conflicts_to_report;
        m_solver.set(cfg);
        m_solver.adjust_cfg();
        m_pdd_manager.set_max_num_nodes(10000); // or something proportional to the number of initial nodes.
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
  
        for (unsigned j = 0; j < m_lar_solver.number_of_vars(); ++j) {
            if (m_lar_solver.column_has_lower_bound(j) || m_lar_solver.column_has_upper_bound(j)) {
                out << j << ": [";
                if (m_lar_solver.column_has_lower_bound(j)) out << m_lar_solver.get_lower_bound(j);
                out << "..";
                if (m_lar_solver.column_has_upper_bound(j)) out << m_lar_solver.get_upper_bound(j);
                out << "]\n";
            }
        }              
        return out;
    }

    bool grobner::is_conflicting(const dd::solver::equation& e) {
        auto& di = c().m_intervals.get_dep_intervals();
        dd::pdd_interval eval(di);
        eval.var2interval() = [this](lpvar j, bool deps, scoped_dep_interval& a) {
            if (deps) c().m_intervals.set_var_interval<dd::w_dep::with_deps>(j, a);
            else c().m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
        };
        scoped_dep_interval i(di), i_wd(di);
        eval.get_interval<dd::w_dep::without_deps>(e.poly(), i);    
        if (!di.separated_from_zero(i)) {
            TRACE("grobner", m_solver.display(tout << "not separated from 0 ", e) << "\n";
                  eval.get_interval_distributed<dd::w_dep::without_deps>(e.poly(), i);
                  tout << "separated from 0: " << di.separated_from_zero(i) << "\n";
                  for (auto j : e.poly().free_vars()) {
                      scoped_dep_interval a(di);
                      c().m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
                      c().m_intervals.display(tout << "j" << j << " ", a); tout << " ";
                  }
                  tout << "\n");
        
            return false;
        }
        eval.get_interval<dd::w_dep::with_deps>(e.poly(), i_wd);  
        std::function<void (const lp::explanation&)> f = [this](const lp::explanation& e) {
            new_lemma lemma(m_core, "pdd");
            lemma &= e;
        };
        if (di.check_interval_for_conflict_on_zero(i_wd, e.dep(), f)) {
            TRACE("grobner", m_solver.display(tout << "conflict ", e) << "\n");
            return true;
        }
        else {
            TRACE("grobner", m_solver.display(tout << "no conflict ", e) << "\n");
            return false;
        }
    }

    bool grobner::propagate_bounds(const dd::solver::equation& e) {
        return false;
        // TODO
        auto& di = c().m_intervals.get_dep_intervals();
        dd::pdd_interval eval(di);
        eval.var2interval() = [this](lpvar j, bool deps, scoped_dep_interval& a) {
            if (deps) c().m_intervals.set_var_interval<dd::w_dep::with_deps>(j, a);
            else c().m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
        };
        scoped_dep_interval i(di), i_wd(di);
        eval.get_interval<dd::w_dep::without_deps>(e.poly(), i);
        return false;
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
        const auto& matrix = m_lar_solver.A_r();
        for (auto & s : matrix.m_columns[j]) {
            unsigned row = s.var();
            if (m_rows.contains(row))
                continue;
            m_rows.insert(row);
            unsigned k = m_lar_solver.get_base_column_in_row(row);
            if (m_lar_solver.column_is_free(k) && k != j)
                continue;
            CTRACE("grobner", matrix.m_rows[row].size() > c().m_nla_settings.grobner_row_length_limit,
                   tout << "ignore the row " << row << " with the size " << matrix.m_rows[row].size() << "\n";); 
            if (matrix.m_rows[row].size() > c().m_nla_settings.grobner_row_length_limit)
                continue;
            for (auto& rc : matrix.m_rows[row]) 
                add_var_and_its_factors_to_q_and_collect_new_rows(rc.var(), q);
        }
    }

    const rational& grobner::val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep) {
        unsigned lc, uc;
        m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
        dep = c().m_intervals.mk_join(dep, c().m_intervals.mk_leaf(lc));
        dep = c().m_intervals.mk_join(dep, c().m_intervals.mk_leaf(uc));
        return m_lar_solver.column_lower_bound(j).x;
    }

    dd::pdd grobner::pdd_expr(const rational& coeff, lpvar j, u_dependency*& dep) {
        dd::pdd r = m_pdd_manager.mk_val(coeff);
        sbuffer<lpvar> vars;
        vars.push_back(j);
        u_dependency* zero_dep = dep;
        while (!vars.empty()) {
            j = vars.back();
            vars.pop_back();
            if (c().m_nla_settings.grobner_subs_fixed > 0 && c().var_is_fixed_to_zero(j)) {
                r = m_pdd_manager.mk_val(val_of_fixed_var_with_deps(j, zero_dep));
                dep = zero_dep;
                return r;
            }
            if (c().m_nla_settings.grobner_subs_fixed == 1 && c().var_is_fixed(j))
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
            switch (m_lar_solver.get_column_type(v)) {
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

    void grobner::add_row(const vector<lp::row_cell<rational>> & row) {
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
        m_rows.clear();
        m_rows.resize(m_lar_solver.row_count());
        c().clear_and_resize_active_var_set();
    }


    void grobner::display_matrix_of_m_rows(std::ostream & out) const {
        const auto& matrix = m_lar_solver.A_r();
        out << m_rows.size() << " rows" << "\n";
        out << "the matrix\n";          
        for (const auto & r : matrix.m_rows) 
            c().print_row(r, out) << std::endl;
    }
    
    void grobner::set_level2var() {
        unsigned n = m_lar_solver.column_count();
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

}
