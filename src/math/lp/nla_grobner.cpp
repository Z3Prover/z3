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

    void core::run_grobner() {
        unsigned& quota = m_nla_settings.grobner_quota;
        if (quota == 1) {
            return;
        }
        clear_and_resize_active_var_set(); 
        find_nl_cluster();

        lp_settings().stats().m_grobner_calls++;
        configure_grobner();
        m_pdd_grobner.saturate();
        bool conflict = false;
        unsigned n = m_pdd_grobner.number_of_conflicts_to_report();
        SASSERT(n > 0);
        for (auto eq : m_pdd_grobner.equations()) {        
            if (check_pdd_eq(eq)) {
                conflict = true;
                if (--n == 0)
                    break;
            }
        }
        TRACE("grobner", m_pdd_grobner.display(tout));
        if (conflict) {
            IF_VERBOSE(2, verbose_stream() << "grobner conflict\n");
            return;
        }

#if 0
        // diagnostics: did we miss something
        vector<dd::pdd> eqs;
        for (auto eq : m_pdd_grobner.equations())
            eqs.push_back(eq->poly());
        m_nra.check(eqs);
#endif
    
#if 0
        bool propagated = false;
        for (auto eq : m_pdd_grobner.equations()) {
            auto const& p = eq->poly();
            if (p.is_offset()) {
                lpvar v = p.var();
                if (m_lar_solver.column_has_lower_bound(v) &&
                    m_lar_solver.column_has_upper_bound(v))
                    continue;
                rational fixed_val = -p.lo().val();
                lp::explanation ex;
                u_dependency_manager dm;
                vector<unsigned, false> lv;
                dm.linearize(eq->dep(), lv);
                for (unsigned ci : lv)
                    ex.push_back(ci);
                new_lemma lemma(*this, "pdd-eq");
                lemma &= ex;
                lemma |= ineq(v, llc::EQ, fixed_val);
                propagated = true;
            }
        }
        if (propagated) 
            return;
#endif

        if (quota > 1)
            quota--;
        IF_VERBOSE(2, verbose_stream() << "grobner miss, quota " << quota <<  "\n");
        IF_VERBOSE(4, diagnose_pdd_miss(verbose_stream()));
    
    }

    void core::configure_grobner() {
        m_pdd_grobner.reset();
        try {
            set_level2var_for_grobner();
            TRACE("grobner",
                  tout << "base vars: ";
                  for (lpvar j : active_var_set())
                      if (m_lar_solver.is_base(j))
                          tout << "j" << j << " ";
                  tout << "\n");
            for (lpvar j : active_var_set()) {
                if (m_lar_solver.is_base(j))
                    add_row_to_grobner(m_lar_solver.basic2row(j));
                
                if (is_monic_var(j) && var_is_fixed(j))
                    add_fixed_monic_to_grobner(j);
            }
        }
        catch (...) {
            IF_VERBOSE(2, verbose_stream() << "pdd throw\n");
            return;
        }
        TRACE("grobner", m_pdd_grobner.display(tout));
    
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
        cfg.m_max_steps = m_pdd_grobner.equations().size();
        cfg.m_max_simplified = m_nla_settings.grobner_max_simplified;
        cfg.m_eqs_growth = m_nla_settings.grobner_eqs_growth;
        cfg.m_expr_size_growth = m_nla_settings.grobner_expr_size_growth;
        cfg.m_expr_degree_growth = m_nla_settings.grobner_expr_degree_growth;
        cfg.m_number_of_conflicts_to_report = m_nla_settings.grobner_number_of_conflicts_to_report;
        m_pdd_grobner.set(cfg);
        m_pdd_grobner.adjust_cfg();
        m_pdd_manager.set_max_num_nodes(10000); // or something proportional to the number of initial nodes.
    }

    std::ostream& core::diagnose_pdd_miss(std::ostream& out) {

        // m_pdd_grobner.display(out);

        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned j){ return val(j); };
        for (auto* e : m_pdd_grobner.equations()) {
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

    bool core::check_pdd_eq(const dd::solver::equation* e) {
        auto& di = m_intervals.get_dep_intervals();
        dd::pdd_interval eval(di);
        eval.var2interval() = [this](lpvar j, bool deps, scoped_dep_interval& a) {
            if (deps) m_intervals.set_var_interval<dd::w_dep::with_deps>(j, a);
            else m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
        };
        scoped_dep_interval i(di), i_wd(di);
        eval.get_interval<dd::w_dep::without_deps>(e->poly(), i);    
        if (!di.separated_from_zero(i)) {
            TRACE("grobner", m_pdd_grobner.display(tout << "not separated from 0 ", *e) << "\n";
                  eval.get_interval_distributed<dd::w_dep::without_deps>(e->poly(), i);
                  tout << "separated from 0: " << di.separated_from_zero(i) << "\n";
                  for (auto j : e->poly().free_vars()) {
                      scoped_dep_interval a(di);
                      m_intervals.set_var_interval<dd::w_dep::without_deps>(j, a);
                      m_intervals.display(tout << "j" << j << " ", a); tout << " ";
                  }
                  tout << "\n");
        
            return false;
        }
        eval.get_interval<dd::w_dep::with_deps>(e->poly(), i_wd);  
        std::function<void (const lp::explanation&)> f = [this](const lp::explanation& e) {
            new_lemma lemma(*this, "pdd");
            lemma &= e;
        };
        if (di.check_interval_for_conflict_on_zero(i_wd, e->dep(), f)) {
            TRACE("grobner", m_pdd_grobner.display(tout << "conflict ", *e) << "\n");
            lp_settings().stats().m_grobner_conflicts++;
            return true;
        }
        else {
            TRACE("grobner", m_pdd_grobner.display(tout << "no conflict ", *e) << "\n");
            return false;
        }
    }

    void core::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, svector<lpvar> & q) {
        if (active_var_set_contains(j))
            return;
        insert_to_active_var_set(j);
        if (is_monic_var(j)) {
            const monic& m = emons()[j];
            for (auto fcn : factorization_factory_imp(m, *this)) 
                for (const factor& fc: fcn) 
                    q.push_back(var(fc));        
        }

        if (var_is_fixed(j))
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
            CTRACE("grobner", matrix.m_rows[row].size() > m_nla_settings.grobner_row_length_limit,
                   tout << "ignore the row " << row << " with the size " << matrix.m_rows[row].size() << "\n";); 
            if (matrix.m_rows[row].size() > m_nla_settings.grobner_row_length_limit) 
                continue;
            for (auto& rc : matrix.m_rows[row]) 
                add_var_and_its_factors_to_q_and_collect_new_rows(rc.var(), q);
        }


    }

    const rational& core::val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep) {
        unsigned lc, uc;
        m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
        dep = m_intervals.mk_join(dep, m_intervals.mk_leaf(lc));
        dep = m_intervals.mk_join(dep, m_intervals.mk_leaf(uc));
        return m_lar_solver.column_lower_bound(j).x;
    }

    dd::pdd core::pdd_expr(const rational& c, lpvar j, u_dependency*& dep) {
        dd::pdd r = m_pdd_manager.mk_val(c);
        sbuffer<lpvar> vars;
        vars.push_back(j);
        u_dependency* zero_dep = dep;
        while (!vars.empty()) {
            j = vars.back();
            vars.pop_back();
            if (m_nla_settings.grobner_subs_fixed > 0 && var_is_fixed_to_zero(j)) {
                r = m_pdd_manager.mk_val(val_of_fixed_var_with_deps(j, zero_dep));
                dep = zero_dep;
                return r;
            }
            if (m_nla_settings.grobner_subs_fixed == 1 && var_is_fixed(j))
                r *= val_of_fixed_var_with_deps(j, dep);
            else if (!is_monic_var(j))
                r *= m_pdd_manager.mk_var(j);
            else
                for (lpvar k : emons()[j].vars())
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
    bool core::is_solved(dd::pdd const& p, unsigned& v, dd::pdd& r) {
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
    void core::add_eq_to_grobner(dd::pdd& p, u_dependency* dep) {
        unsigned v;
        dd::pdd q(m_pdd_manager);
        m_pdd_grobner.simplify(p, dep);
        if (is_solved(p, v, q)) 
            m_pdd_grobner.add_subst(v, q, dep);
        else         
            m_pdd_grobner.add(p, dep);    
    }

    void core::add_fixed_monic_to_grobner(unsigned j) {
        u_dependency* dep = nullptr;
        dd::pdd r = m_pdd_manager.mk_val(rational(1));
        for (lpvar k : emons()[j].vars()) 
            r *= pdd_expr(rational::one(), k, dep);
        r -= val_of_fixed_var_with_deps(j, dep);
        add_eq_to_grobner(r, dep);
    }

    void core::add_row_to_grobner(const vector<lp::row_cell<rational>> & row) {
        u_dependency *dep = nullptr;
        rational val;
        dd::pdd sum = m_pdd_manager.mk_val(rational(0));
        for (const auto &p : row) 
            sum += pdd_expr(p.coeff(), p.var(), dep);
        TRACE("grobner", print_row(row, tout) << " " << sum << "\n");
        add_eq_to_grobner(sum, dep);
    }


    void core::find_nl_cluster() {
        prepare_rows_and_active_vars();
        svector<lpvar> q;
        TRACE("grobner", for (lpvar j : m_to_refine) print_monic(emons()[j], tout) << "\n";);
          
        for (lpvar j : m_to_refine) 
            q.push_back(j);
    
        while (!q.empty()) {
            lpvar j = q.back();        
            q.pop_back();
            add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
        }
        TRACE("grobner", tout << "vars in cluster: ";
              for (lpvar j : active_var_set()) tout << "j" << j << " "; tout << "\n";
              display_matrix_of_m_rows(tout);
              );
    }

    void core::prepare_rows_and_active_vars() {
        m_rows.clear();
        m_rows.resize(m_lar_solver.row_count());
        clear_and_resize_active_var_set();
    }


    void core::display_matrix_of_m_rows(std::ostream & out) const {
        const auto& matrix = m_lar_solver.A_r();
        out << m_rows.size() << " rows" << "\n";
        out << "the matrix\n";          
        for (const auto & r : matrix.m_rows) 
            print_row(r, out) << std::endl;
    }
    

}
