/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    dual_maxsres.cpp

Abstract:
   
    MaxRes (weighted) max-sat algorithm 
    based on dual refinement of bounds.

    MaxRes is a core-guided approach to maxsat.
    DualMaxRes extends the core-guided approach by
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

    Nikolaj Bjorner (nbjorner) 2014-27-7

Notes:

--*/

#include "solver.h"
#include "maxsmt.h"
#include "dual_maxres.h"
#include "ast_pp.h"
#include "mus.h"

using namespace opt;


class dual_maxres : public maxsmt_solver_base {
    expr_ref_vector  m_B;
    expr_ref_vector  m_asms;    
    obj_map<expr, rational> m_asm2weight;
    obj_map<expr, expr*>    m_soft2asm;
    ptr_vector<expr> m_new_core;
    mus              m_mus;
    expr_ref_vector  m_trail;

public:
    dual_maxres(ast_manager& m, opt_solver* s, params_ref& p, 
           vector<rational> const& ws, expr_ref_vector const& soft):
        maxsmt_solver_base(s, m, p, ws, soft),
        m_B(m), m_asms(m),
        m_mus(m_s, m),
        m_trail(m)
    {
    }

    virtual ~dual_maxres() {}

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }

    void add_soft(expr* e, rational const& w) {
        TRACE("opt", tout << mk_pp(e, m) << "\n";);
        expr_ref asum(m), fml(m);
        expr* f;
        if (m_soft2asm.find(e, f)) {
            m_asm2weight.find(f) += w;
            return;
        }
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = mk_fresh_bool("soft");
            fml = m.mk_iff(asum, e);
            m_s->assert_expr(fml);
        }
        m_soft2asm.insert(e, asum);
        new_assumption(asum, w);
        m_upper += w;
    }

    void new_assumption(expr* e, rational const& w) {
        m_asm2weight.insert(e, w);
        m_asms.push_back(e);
        m_trail.push_back(e);        
    }

    lbool operator()() {
        solver::scoped_push _sc(*m_s.get());
        init();
        init_local();
        enable_bvsat();
        enable_sls();
        lbool was_sat = l_false;
        ptr_vector<expr> soft_compl;
        vector<ptr_vector<expr> > cores;
        while (m_lower < m_upper) {            
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  m_s->display(tout);
                  tout << "\n";
                  display(tout);
                  );
            lbool is_sat = m_s->check_sat(0, 0);
            if (m_cancel) {
                return l_undef;
            }
            if (is_sat == l_true) {
                was_sat = l_true;
                is_sat = extend_model(soft_compl);
                switch (is_sat) {
                case l_undef:
                    break;
                case l_false:
                    is_sat = get_cores(cores);
                    for (unsigned i = 0; is_sat == l_true && i < cores.size(); ++i) {
                        is_sat = process_unsat(cores[i]);
                    }
                    break;
                case l_true:
                    is_sat = process_sat(soft_compl);
                    break;
                }
            }
            switch (is_sat) {
            case l_undef:
                return l_undef;
            case l_false:
                m_lower = m_upper;
                return was_sat;
            case l_true: 
                break;
            }
        }
        return was_sat;
    }

    lbool process_sat(ptr_vector<expr>& softc) {
        expr_ref fml(m), tmp(m);
        TRACE("opt", display_vec(tout << "softc: ", softc.size(), softc.c_ptr()););
        SASSERT(!softc.empty()); // we should somehow stop if all soft are satisfied.
        if (softc.empty()) {
            return l_false;
        }
        
        remove_soft(softc);
        rational w = split_soft(softc);
        TRACE("opt", display_vec(tout << " softc: ", softc.size(), softc.c_ptr()););
        dual_max_resolve(softc, w);
        return l_true;
    }

    // 
    // Retrieve a set of disjoint cores over the current assumptions.
    // TBD: when the remaining are satisfiable, then extend the
    // satisfying model to improve upper bound.
    // 
    lbool get_cores(vector<ptr_vector<expr> >& cores) {
        // assume m_s is unsat.
        lbool is_sat = l_false;
        expr_ref_vector asms(m);
        asms.append(m_asms.size(), m_asms.c_ptr());
        cores.reset();
        ptr_vector<expr> core;
        while (is_sat == l_false) {
            core.reset();
            m_s->get_unsat_core(core);
            is_sat = minimize_core(core);
            if (is_sat != l_true) {
                break;
            }
            cores.push_back(core);
            break;
            // 
            // TBD: multiple core refinement 
            // produces unsound results.
            // what is a sound variant?
            // 
            remove_soft(core, asms);
            is_sat = m_s->check_sat(asms.size(), asms.c_ptr());
            
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

    lbool process_unsat(ptr_vector<expr>& core) {
        expr_ref fml(m);
        SASSERT(!core.empty());
        if (core.empty()) {
            return l_false;
        }
        remove_soft(core);
        rational w = split_soft(core);
        TRACE("opt", display_vec(tout << "core: ", core.size(), core.c_ptr());
              for (unsigned i = 0; i < core.size(); ++i) {
                  tout << get_weight(core[i]) << " ";
              }
              tout << "min-weight: " << w << "\n";);
        max_resolve(core, w);
        m_lower += w;        
        IF_VERBOSE(1, verbose_stream() << 
                   "(opt.dual_max_res [" << m_lower << ":" << m_upper << "])\n";);
        return l_true;
    }

    //
    // The hard constraints are satisfiable.
    // Extend the current model to satisfy as many
    // soft constraints as possible until either
    // hitting an unsatisfiable subset of size < 1/2*#assumptions,
    // or producing a maximal satisfying assignment exceeding 
    // number of soft constraints >= 1/2*#assumptions.
    // In both cases, soft constraints that are not satisfied 
    // is <= 1/2*#assumptions. In this way, the new modified assumptions
    // account for at most 1/2 of the current assumptions.
    // The core reduction algorithms also need to take into account
    // at most 1/2 of the assumptions for minimization.
    // 

    lbool extend_model(ptr_vector<expr>& soft_compl) {
        ptr_vector<expr> asms;
        model_ref mdl;
        expr_ref tmp(m);
        m_s->get_model(mdl);
        unsigned num_true = update_model(mdl, asms, soft_compl);
        for (unsigned j = 0; j < m_asms.size(); ++j) {
            expr* fml = m_asms[j].get();
            VERIFY(mdl->eval(fml, tmp));
            if (m.is_false(tmp)) {
                asms.push_back(fml);
                lbool is_sat = m_s->check_sat(asms.size(), asms.c_ptr());
                asms.pop_back();
                switch (is_sat) {
                case l_false:
                    if (num_true*2 < m_asms.size()) {
                        return l_false;
                    }
                    break;
                case l_true:
                    m_s->get_model(mdl);
                    num_true = update_model(mdl, asms, soft_compl);
                    break;
                case l_undef:
                    return l_undef;
                }
            }
        }
        return l_true;
    }

    unsigned update_model(model_ref& mdl, ptr_vector<expr>& asms, ptr_vector<expr>& soft_compl) {
        expr_ref tmp(m);
        asms.reset();
        soft_compl.reset();
        rational weight = m_lower;
        unsigned num_true = 0;
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            expr* fml = m_asms[i].get();
            VERIFY(mdl->eval(fml, tmp));
            SASSERT(m.is_false(tmp) || m.is_true(tmp));            
            if (m.is_false(tmp)) {
                weight += get_weight(fml);
                soft_compl.push_back(fml);
            }
            else {
                ++num_true;
                asms.push_back(fml);
            }
        }
        if (weight < m_upper) {
            m_upper = weight;
            m_model = mdl;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                expr_ref tmp(m);
                VERIFY(m_model->eval(m_soft[i].get(), tmp));
                m_assignment[i] = m.is_true(tmp);
            }
            IF_VERBOSE(1, verbose_stream() << 
                       "(opt.dual_max_res [" << m_lower << ":" << m_upper << "])\n";);
        }
        return num_true;
    }

    lbool minimize_core(ptr_vector<expr>& core) {
        if (m_sat_enabled) {
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


    // 
    // find the minimal weight.
    // soft clauses with weight larger than the minimal weight
    // are (re)added as soft clauses where the weight is updated
    // to subtract the minimal weight.
    //
    rational split_soft(ptr_vector<expr> const& soft) {

        SASSERT(!soft.empty());
        rational w = get_weight(soft[0]);
        for (unsigned i = 1; i < soft.size(); ++i) {
            rational w2 = get_weight(soft[i]);
            if (w2 < w) {
                w = w2;
            }
        }
        // add fresh soft clauses for weights that are above w.
        for (unsigned i = 0; i < soft.size(); ++i) {
            rational w2 = get_weight(soft[i]);
            if (w2 > w) {
                new_assumption(soft[i], w2 - w);
            }
        }
        return w;
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " ";
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
        app_ref cls(m), d(m);
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
            d = m.mk_and(b_i, d);
            asum = mk_fresh_bool("a");
            cls = m.mk_or(b_i1, d);
            fml = m.mk_iff(asum, cls);
            new_assumption(asum, w);
            m_s->assert_expr(fml);
        }
        fml = m.mk_not(m.mk_and(m_B.size(), m_B.c_ptr()));
        m_s->assert_expr(fml);
    }

    // satc are the complements of a (maximal) satisfying assignment.
    void dual_max_resolve(ptr_vector<expr>& satc, rational const& w) {
        SASSERT(!satc.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m);
        m_B.reset();
        m_B.append(satc.size(), satc.c_ptr());
        d = m.mk_false();
        //
        // d_0 := false
        // d_i := b_{i-1} or d_{i-1}    for i = 1...sz-1
        // soft (b_i and d_i) 
        //   == (b_i and (b_0 or b_1 or ... or b_{i-1}))
        // 
        for (unsigned i = 1; i < satc.size(); ++i) {
            expr* b_i = m_B[i-1].get();
            expr* b_i1 = m_B[i].get();
            d = m.mk_or(b_i, d);
            asum = mk_fresh_bool("a");
            cls = m.mk_and(b_i1, d);
            fml = m.mk_iff(asum, cls);
            new_assumption(asum, w);
            m_s->assert_expr(fml);
        }
        fml = m.mk_or(m_B.size(), m_B.c_ptr());
        m_s->assert_expr(fml);
    }

    void remove_soft(ptr_vector<expr> const& soft, expr_ref_vector& asms) {
        for (unsigned i = 0; i < asms.size(); ++i) {
            if (soft.contains(asms[i].get())) {
                asms[i] = asms.back();
                asms.pop_back();
                --i;
            }
        }
    }

    void remove_soft(ptr_vector<expr> const& soft) {
        remove_soft(soft, m_asms);
    }

    virtual void set_cancel(bool f) {
        maxsmt_solver_base::set_cancel(f);
        m_mus.set_cancel(f);
    }

    void init_local() {
        m_upper.reset();
        m_lower.reset();
        m_asm2weight.reset();
        m_soft2asm.reset();
        m_trail.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            add_soft(m_soft[i].get(), m_weights[i]);
        }
    }

};

opt::maxsmt_solver_base* opt::mk_dual_maxres(
    ast_manager& m, opt_solver* s, params_ref& p, 
    vector<rational> const& ws, expr_ref_vector const& soft) {
    return alloc(dual_maxres, m, s, p, ws, soft);
}

