/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxsres.cpp

Abstract:
   
    MaxRes (weighted) max-sat algorithms:

    - mus:     max-sat algorithm by Nina and Bacchus, AAAI 2014.
    - mus-mss: based on dual refinement of bounds.
    - mss:     based on maximal satisfying sets (only).

    MaxRes is a core-guided approach to maxsat.
    MusMssMaxRes extends the core-guided approach by
    leveraging both cores and satisfying assignments
    to make progress towards a maximal satisfying assignment.

    Given a (minimal) unsatisfiable core for the soft
    constraints the approach works like max-res.
    Given a (maximal) satisfying subset of the soft constraints
    the approach updates the upper bound if the current assignment
    improves the current best assignmet.
    Furthermore, take the soft constraints that are complements
    to the current satisfying subset. 
    E.g, if F are the hard constraints and 
    s1,...,sn, t1,..., tm are the soft clauses and 
    F & s1 & ... & sn is satisfiable, then the complement 
    of of the current satisfying subset is t1, .., tm.
    Update the hard constraint:
         F := F & (t1 or ... or tm)
    Replace t1, .., tm by m-1 new soft clauses:
         t1 & t2, t3 & (t1 or t2), t4 & (t1 or t2 or t3), ..., tn & (t1 or ... t_{n-1})
    Claim: 
       If k of these soft clauses are satisfied, then k+1 of 
       the previous soft clauses are satisfied.
       If k of these soft clauses are false in the satisfying assignment 
       for the updated F, then k of the original soft clauses are also false 
       under the assignment.
       In summary: any assignment to the new clauses that satsfies F has the
       same cost.
    Claim:
       If there are no satisfying assignments to F, then the current best assignment
       is the optimum.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/

#include "solver.h"
#include "maxsmt.h"
#include "maxres.h"
#include "ast_pp.h"
#include "mus.h"
#include "mss.h"
#include "inc_sat_solver.h"
#include "opt_context.h"


using namespace opt;

class maxres : public maxsmt_solver_base {
public:
    enum strategy_t {
        s_mus,
        s_mus_mss,
        s_mss
    };
private:
    expr_ref_vector  m_B;
    expr_ref_vector  m_asms;    
    obj_map<expr, rational> m_asm2weight;
    ptr_vector<expr> m_new_core;
    mus              m_mus;
    mss              m_mss;
    expr_ref_vector  m_trail;
    strategy_t       m_st;
    rational         m_max_upper;

public:
    maxres(context& c,
           vector<rational> const& ws, expr_ref_vector const& soft, 
           strategy_t st):
        maxsmt_solver_base(c, ws, soft),
        m_B(m), m_asms(m),
        m_mus(m_s, m),
        m_mss(m_s, m),
        m_trail(m),
        m_st(st)
    {
    }

    virtual ~maxres() {}

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }

    void add_soft(expr* e, rational const& w) {
        TRACE("opt", tout << mk_pp(e, m) << "\n";);
        expr_ref asum(m), fml(m);
        app_ref cls(m);
        rational weight(0);
        if (m_asm2weight.find(e, weight)) {
            weight += w;
            m_asm2weight.insert(e, weight);
            return;
        }
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = mk_fresh_bool("soft");
            fml = m.mk_iff(asum, e);
            s().assert_expr(fml);
        }
        new_assumption(asum, w);
        m_upper += w;
    }

    void new_assumption(expr* e, rational const& w) {
        TRACE("opt", tout << "insert: " << mk_pp(e, m) << " : " << w << "\n";);
        m_asm2weight.insert(e, w);
        m_asms.push_back(e);
        m_trail.push_back(e);        
    }

    lbool mus_solver() {
        init();
        init_local();
        while (true) {
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  s().display(tout);
                  tout << "\n";
                  display(tout);
                  );
            lbool is_sat = s().check_sat(m_asms.size(), m_asms.c_ptr());
            if (m_cancel) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true: {
                s().get_model(m_model);
                expr_ref tmp(m);
                DEBUG_CODE(
                    for (unsigned i = 0; i < m_asms.size(); ++i) {
                        VERIFY(m_model->eval(m_asms[i].get(), tmp));                        
                        SASSERT(m.is_true(tmp));
                    });
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    VERIFY(m_model->eval(m_soft[i].get(), tmp));
                    m_assignment[i] = m.is_true(tmp);
                }
                m_upper = m_lower;
                return l_true;
            }
            case l_false:
                is_sat = process_unsat();
                if (is_sat != l_true) return is_sat;
                break;
            case l_undef:
                return l_undef;
            default:
                break;
            }
        }
        return l_true;
    }

    lbool mus_mss_solver() {
        init();
        init_local();
        enable_sls(m_asms);
        ptr_vector<expr> mcs;
        vector<ptr_vector<expr> > cores;
        while (m_lower < m_upper) {            
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  s().display(tout);
                  tout << "\n";
                  display(tout);
                  );
            lbool is_sat = try_improve_bound(cores, mcs);
            if (m_cancel) {
                return l_undef;
            }
            switch (is_sat) {
            case l_undef:
                return l_undef;
            case l_false:
                SASSERT(cores.empty() && mcs.empty());
                m_lower = m_upper;
                return l_true;
            case l_true:
                SASSERT(cores.empty() || mcs.empty());
                for (unsigned i = 0; is_sat == l_true && i < cores.size(); ++i) {
                    is_sat = process_unsat(cores[i]);
                }
                if (is_sat == l_true && cores.empty()) {
                    is_sat = process_sat(mcs);
                }
                if (is_sat != l_true) {
                    return is_sat;
                }
                break;
            }
        }
        m_lower = m_upper;
        return l_true;
    }

    lbool mss_solver() {
        init();
        init_local();
        enable_sls(m_asms);
        set_mus(false);
        ptr_vector<expr> mcs;
        while (m_lower < m_upper) {            
            IF_VERBOSE(1, verbose_stream() << "(opt.maxres [" << m_lower << ":" << m_upper << "])\n";);

            lbool is_sat = s().check_sat(0, 0);
            if (is_sat == l_true) {
                vector<ptr_vector<expr> > cores;
                ptr_vector<expr> mss;       
                model_ref mdl;
                expr_ref tmp(m);
                mcs.reset();
                s().get_model(mdl);
                update_assignment(mdl.get());
                for (unsigned i = 0; i < m_asms.size(); ++i) {
                    VERIFY(mdl->eval(m_asms[i].get(), tmp));
                    if (m.is_true(tmp)) {
                        mss.push_back(m_asms[i].get());
                    }
                }
                is_sat = m_mss(cores, mss, mcs);
                std::cout << mcs.size() << " " << is_sat << "\n";
            }
            switch (is_sat) {
            case l_undef:
                return l_undef;
            case l_false:
                m_lower = m_upper;
                break;
            case l_true: {
                
                is_sat = process_sat(mcs);
                if (is_sat != l_true) {
                    return is_sat;
                }
                model_ref mdl;
                m_mss.get_model(mdl);
                update_assignment(mdl.get());
                break;
            }
            }
        }
        m_lower = m_upper;
        return l_true;
    }

    lbool operator()() {
        switch(m_st) {
        case s_mus:
            return mus_solver();
        case s_mus_mss:
            return mus_mss_solver();
        case s_mss:
            return mss_solver();
        }
        return l_undef;
    }

    lbool get_cores(vector<ptr_vector<expr> >& cores) {
        // assume m_s is unsat.
        lbool is_sat = l_false;
        expr_ref_vector asms(m_asms);
        cores.reset();
        ptr_vector<expr> core;
        while (is_sat == l_false) {
            core.reset();
            s().get_unsat_core(core);
            is_sat = minimize_core(core);
            if (is_sat != l_true) {
                break;
            }
            cores.push_back(core);
            // TBD: ad hoc to avoid searching for large cores..
            if (core.size() >= 3) {
                break;
            }
            remove_soft(core, asms);
            TRACE("opt",
                  display_vec(tout << "core: ", core.size(), core.c_ptr());
                  display_vec(tout << "assumptions: ", asms.size(), asms.c_ptr()););
            is_sat = s().check_sat(asms.size(), asms.c_ptr());            
        }
        TRACE("opt", 
              tout << "num cores: " << cores.size() << "\n";
              for (unsigned i = 0; i < cores.size(); ++i) {
                  for (unsigned j = 0; j < cores[i].size(); ++j) {
                      tout << mk_pp(cores[i][j], m) << " ";
                  }
                  tout << "\n";
              }
              tout << "num satisfying: " << asms.size() << "\n";);
        
        return is_sat;
    }


    lbool process_sat(ptr_vector<expr>& corr_set) {
        expr_ref fml(m), tmp(m);
        TRACE("opt", display_vec(tout << "corr_set: ", corr_set.size(), corr_set.c_ptr()););
        if (corr_set.empty()) {
            return l_true;
        }
        
        remove_core(corr_set);
        rational w = split_core(corr_set);
        TRACE("opt", display_vec(tout << " corr_set: ", corr_set.size(), corr_set.c_ptr()););
        cs_max_resolve(corr_set, w);
        return l_true;
    }

    lbool process_unsat() {
        vector<ptr_vector<expr> > cores;
        lbool is_sat = get_cores(cores);
        if (is_sat != l_true) {
            return is_sat;
        }
        if (cores.empty()) {
            return l_false;
        }
        for (unsigned i = 0; is_sat == l_true && i < cores.size(); ++i) {
            is_sat = process_unsat(cores[i]);
        }
        return is_sat;
    }
    
    lbool process_unsat(ptr_vector<expr>& core) {
        expr_ref fml(m);
        remove_core(core);
        rational w = split_core(core);
        TRACE("opt", display_vec(tout << "minimized core: ", core.size(), core.c_ptr()););
        max_resolve(core, w);
        fml = m.mk_not(m.mk_and(m_B.size(), m_B.c_ptr()));
        s().assert_expr(fml);
        m_lower += w;
        IF_VERBOSE(1, verbose_stream() << "(opt.maxres [" << m_lower << ":" << m_upper << "])\n";);
        return l_true;
    }

    lbool minimize_core(ptr_vector<expr>& core) {
        if (m_c.sat_enabled()) {
            return l_true;
        }
        m_mus.reset();
        for (unsigned i = 0; i < core.size(); ++i) {
            m_mus.add_soft(core[i]);
        }
        unsigned_vector mus_idx;
        lbool is_sat = m_mus.get_mus(mus_idx);
        if (is_sat != l_true) {
            return is_sat;
        }
        m_new_core.reset();
        for (unsigned i = 0; i < mus_idx.size(); ++i) {
            m_new_core.push_back(core[mus_idx[i]]);
        }
        core.reset();
        core.append(m_new_core);
        return l_true;
    }

    rational get_weight(expr* e) {
        return m_asm2weight.find(e);
    }

    rational split_core(ptr_vector<expr> const& core) {

        // find the minimal weight:
        SASSERT(!core.empty());
        rational w = get_weight(core[0]);
        for (unsigned i = 1; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 < w) {
                w = w2;
            }
        }
        // add fresh soft clauses for weights that are above w.
        for (unsigned i = 0; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 > w) {
                rational w3 = w2 - w;
                new_assumption(core[i], w3);
            }
        }
        return w;
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " : " << get_weight(args[i]) << " ";
        }
        out << "\n";
    }

    void display(std::ostream& out) {
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            expr* a = m_asms[i].get();
            out << mk_pp(a, m) << " : " << get_weight(a) << "\n";
        }
    }

    void max_resolve(ptr_vector<expr>& core, rational const& w) {
        SASSERT(!core.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(core.size(), core.c_ptr());
        d = m.mk_true();
        //
        // d_0 := true
        // d_i := b_{i-1} and d_{i-1}    for i = 1...sz-1
        // soft (b_i or !d_i) 
        //   == (b_i or !(!b_{i-1} or d_{i-1}))
        //   == (b_i or b_0 & b_1 & ... & b_{i-1})
        // 
        // Soft constraint is satisfied if previous soft constraint
        // holds or if it is the first soft constraint to fail.
        // 
        // Soundness of this rule can be established using MaxRes
        // 
        for (unsigned i = 1; i < core.size(); ++i) {
            expr* b_i = m_B[i-1].get();
            expr* b_i1 = m_B[i].get();
            if (i > 2) {
                dd = mk_fresh_bool("d");
                fml = m.mk_implies(dd, d);
                s().assert_expr(fml);
                fml = m.mk_implies(dd, b_i);
                s().assert_expr(fml);
                d = dd;
            }
            else {
                d = m.mk_and(b_i, d);
            }
            asum = mk_fresh_bool("a");
            cls = m.mk_or(b_i1, d);
            fml = m.mk_implies(asum, cls);
            new_assumption(asum, w);
            s().assert_expr(fml);
        }
    }

    // cs is a correction set (a complement of a (maximal) satisfying assignment).
    void cs_max_resolve(ptr_vector<expr>& cs, rational const& w) {
        TRACE("opt", display_vec(tout << "correction set: ", cs.size(), cs.c_ptr()););
        SASSERT(!cs.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(cs.size(), cs.c_ptr());
        d = m.mk_false();
        //
        // d_0 := false
        // d_i := b_{i-1} or d_{i-1}    for i = 1...sz-1
        // soft (b_i and d_i) 
        //   == (b_i and (b_0 or b_1 or ... or b_{i-1}))
        //
        // asm => b_i
        // asm => d_{i-1} or b_{i-1}
        // d_i => d_{i-1} or b_{i-1}
        //
        for (unsigned i = 1; i < cs.size(); ++i) {
            expr* b_i = m_B[i-1].get();
            expr* b_i1 = m_B[i].get();
            cls = m.mk_or(b_i, d);
            if (i > 2) {
                d = mk_fresh_bool("d");
                fml = m.mk_implies(d, cls);
                s().assert_expr(fml);
            }
            else {
                d = cls;
            }
            asum = mk_fresh_bool("a");
            fml = m.mk_implies(asum, b_i1);
            s().assert_expr(fml);
            fml = m.mk_implies(asum, cls);
            s().assert_expr(fml);
            new_assumption(asum, w);
        }
        fml = m.mk_or(m_B.size(), m_B.c_ptr());
        s().assert_expr(fml);
    }

    lbool try_improve_bound(vector<ptr_vector<expr> >& cores, ptr_vector<expr>& mcs) {
        cores.reset();
        mcs.reset();
        ptr_vector<expr> core;
        expr_ref_vector asms(m_asms);
        while (true) {
            rational upper = m_max_upper;
            unsigned sz = 0;
            for (unsigned i = 0; m_upper <= rational(2)*upper && i < asms.size(); ++i, ++sz) {
                upper -= get_weight(asms[i].get());
            }
            lbool is_sat = s().check_sat(sz, asms.c_ptr());
            switch (is_sat) {
            case l_true: {
                model_ref mdl;
                s().get_model(mdl); // last model is best way to reduce search space.
                update_assignment(mdl.get());
                ptr_vector<expr> mss;
                mss.append(asms.size(), asms.c_ptr());
                set_mus(false);
                is_sat = m_mss(cores, mss, mcs);
                set_mus(true);
                if (is_sat != l_true) {
                    return is_sat;
                }
                m_mss.get_model(mdl); // last model is best way to reduce search space.
                update_assignment(mdl.get());
                if (!cores.empty() && mcs.size() > cores.back().size()) {
                    mcs.reset();
                }
                else {
                    cores.reset();
                }
                return l_true;
            }
            case l_undef:
                return l_undef;
            case l_false:
                core.reset();
                s().get_unsat_core(core);
                is_sat = minimize_core(core);
                if (is_sat != l_true) {
                    break;
                }
                if (core.empty()) {
                    cores.reset();
                    mcs.reset();
                    return l_false;
                }
                cores.push_back(core);
                if (core.size() >= 3) {
                    return l_true;
                }
                //
                // check arithmetic: cannot improve upper bound
                //
                if (m_upper <= upper) {
                    return l_true;
                }
                
                remove_soft(core, asms);
                break;
            }
        }
        
        return l_undef;
    }


    void update_assignment(model* mdl) {
        rational upper(0);
        expr_ref tmp(m);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            expr* n = m_soft[i].get();
            VERIFY(mdl->eval(n, tmp));
            if (!m.is_true(tmp)) {
                upper += m_weights[i];
            }
            CTRACE("opt", !m.is_true(tmp) && !m.is_false(tmp), 
                   tout << mk_pp(n, m) << " |-> " << mk_pp(tmp, m) << "\n";);
        }
        if (upper >= m_upper) {
            return;
        }
        m_model = mdl;

        for (unsigned i = 0; i < m_soft.size(); ++i) {
            expr* n = m_soft[i].get();
            VERIFY(m_model->eval(n, tmp));
            m_assignment[i] = m.is_true(tmp);
        }
        m_upper = upper;
        // verify_assignment();
        IF_VERBOSE(1, verbose_stream() << 
                   "(opt.maxres [" << m_lower << ":" << m_upper << "])\n";);
    }

    void remove_soft(ptr_vector<expr> const& core, expr_ref_vector& asms) {
        for (unsigned i = 0; i < asms.size(); ++i) {
            if (core.contains(asms[i].get())) {
                asms[i] = asms.back();
                asms.pop_back();
                --i;
            }
        }
    }

    void remove_core(ptr_vector<expr> const& core) {
        remove_soft(core, m_asms);
    }

    virtual void set_cancel(bool f) {
        maxsmt_solver_base::set_cancel(f);
        m_mus.set_cancel(f);
    }

    void init_local() {
        m_upper.reset();
        m_lower.reset();
        m_trail.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            add_soft(m_soft[i].get(), m_weights[i]);
        }
        m_max_upper = m_upper;
    }

    void verify_assignment() {
        IF_VERBOSE(0, verbose_stream() << "verify assignment\n";);        
        ref<solver> sat_solver = mk_inc_sat_solver(m, m_params);
        for (unsigned i = 0; i < s().get_num_assertions(); ++i) {
            sat_solver->assert_expr(s().get_assertion(i));
        }
        expr_ref n(m);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            n = m_soft[i].get();
            if (!m_assignment[i]) {
                n = m.mk_not(n);
            }
            sat_solver->assert_expr(n);
        }
        lbool is_sat = sat_solver->check_sat(0, 0);
        if (is_sat == l_false) {
            IF_VERBOSE(0, verbose_stream() << "assignment is infeasible\n";);
        }
    }

};

opt::maxsmt_solver_base* opt::mk_maxres(context& c,
                                        vector<rational> const& ws, expr_ref_vector const& soft) {
    return alloc(maxres, c, ws, soft, maxres::s_mus);
}

opt::maxsmt_solver_base* opt::mk_mus_mss_maxres(context& c,
                                        vector<rational> const& ws, expr_ref_vector const& soft) {
    return alloc(maxres, c, ws, soft, maxres::s_mus_mss);
}

opt::maxsmt_solver_base* opt::mk_mss_maxres(context& c,
                                        vector<rational> const& ws, expr_ref_vector const& soft) {
    return alloc(maxres, c, ws, soft, maxres::s_mss);
}

