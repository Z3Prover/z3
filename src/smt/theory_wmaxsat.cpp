/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_wmaxsat.h

Abstract:

    Weighted Max-SAT theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

--*/

#include <typeinfo>
#include "smt/smt_context.h"
#include "ast/ast_pp.h"
#include "smt/theory_wmaxsat.h"
#include "smt/smt_justification.h"

namespace smt {

    theory_wmaxsat::theory_wmaxsat(ast_manager& m, generic_model_converter& mc):
        theory(m.mk_family_id("weighted_maxsat")),
        m_mc(mc),
        m_vars(m),
        m_fmls(m),
        m_zweights(m_mpz),
        m_old_values(m_mpz),
        m_zcost(m_mpz),
        m_zmin_cost(m_mpz),
        m_found_optimal(false),
        m_propagate(false),
        m_normalize(false),
        m_den(1)
    {}
    
    theory_wmaxsat::~theory_wmaxsat() { 
        m_old_values.reset();
    }
    
    /**
       \brief return the complement of variables that are currently assigned.
    */
    void theory_wmaxsat::get_assignment(svector<bool>& result) {
        result.reset();
        
        if (!m_found_optimal) {
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                result.push_back(false);
            }
        }
        else {
            std::sort(m_cost_save.begin(), m_cost_save.end());
            for (unsigned i = 0,j = 0; i < m_vars.size(); ++i) {
                if (j < m_cost_save.size() && m_cost_save[j] == static_cast<theory_var>(i)) {
                    result.push_back(false);
                    ++j;
                }
                else {
                    result.push_back(true);
                }
            }
        }
        TRACE("opt",
              tout << "cost save: ";
              for (unsigned i = 0; i < m_cost_save.size(); ++i) {
                  tout << m_cost_save[i] << " ";
              }
              tout << "\nvars: ";
              for (unsigned i = 0; i < m_vars.size(); ++i) {
                  tout << mk_pp(m_vars[i].get(), get_manager()) << " ";
              }
              tout << "\nassignment: ";
              for (unsigned i = 0; i < result.size(); ++i) {
                  tout << result[i] << " ";
              }
              tout << "\n";);                          
    }
    
    void theory_wmaxsat::init_search_eh() {
        m_propagate = true;
    }
    
    expr* theory_wmaxsat::assert_weighted(expr* fml, rational const& w) {
        context & ctx = get_context();
        ast_manager& m = get_manager();
        app_ref var(m), wfml(m);
        var = m.mk_fresh_const("w", m.mk_bool_sort());
        m_mc.hide(var);
        wfml = m.mk_or(var, fml);
        ctx.assert_expr(wfml);
        m_rweights.push_back(w);
        m_vars.push_back(var);
        m_fmls.push_back(fml);
        m_assigned.push_back(false);
        m_enabled.push_back(true);
        m_normalize = true;
        bool_var bv = register_var(var, true);
        (void)bv;
        TRACE("opt", tout << "inc: " << ctx.inconsistent() << " enable: v" << m_bool2var[bv] 
              << " b" << bv << " " << mk_pp(var, get_manager()) << "\n" << wfml << "\n";);
        return var;
    }

    void theory_wmaxsat::disable_var(expr* var) {
        context& ctx = get_context();
        SASSERT(ctx.b_internalized(var));
        bool_var bv = ctx.get_bool_var(var);
        theory_var tv = m_bool2var[bv];
        m_enabled[tv] = false;
        TRACE("opt", tout << "disable: v" << tv << " b" << bv << " " << mk_pp(var, get_manager()) << "\n";);
    }
    
    bool_var theory_wmaxsat::register_var(app* var, bool attach) {
        context & ctx = get_context();
        bool_var bv;
        SASSERT(!ctx.e_internalized(var));
        enode* x = ctx.mk_enode(var, false, true, true);
        if (ctx.b_internalized(var)) {
            bv = ctx.get_bool_var(var);
        }
        else {
            bv = ctx.mk_bool_var(var);
        }
        ctx.set_enode_flag(bv, true);
        if (attach) {
            ctx.set_var_theory(bv, get_id());                    
            theory_var v = mk_var(x);
            ctx.attach_th_var(x, this, v);
            m_bool2var.insert(bv, v);
            while (m_var2bool.size() <= static_cast<unsigned>(v)) {
                m_var2bool.push_back(null_bool_var);
            }
            m_var2bool[v] = bv;
            SASSERT(ctx.bool_var2enode(bv));
        }
        return bv;
    }
    
    rational theory_wmaxsat::get_cost() { 
        unsynch_mpq_manager mgr;
        scoped_mpq q(mgr);
        mgr.set(q, m_zcost, m_den.to_mpq().numerator());
        return rational(q);
    }

    void theory_wmaxsat::init_min_cost(rational const& r) {
        m_rmin_cost = r;
        m_zmin_cost = (m_rmin_cost * m_den).to_mpq().numerator();
    }


    void theory_wmaxsat::assign_eh(bool_var v, bool is_true) {
        if (is_true) {
            if (m_normalize) normalize();
            context& ctx = get_context();
            theory_var tv = m_bool2var[v];
            if (m_assigned[tv] || !m_enabled[tv]) return;
            scoped_mpz w(m_mpz);
            w = m_zweights[tv];
            ctx.push_trail(numeral_trail(m_zcost, m_old_values));
            ctx.push_trail(push_back_vector<context, svector<theory_var> >(m_costs));
            ctx.push_trail(value_trail<context, bool>(m_assigned[tv]));
            m_zcost += w;
            TRACE("opt", tout << "Assign v" << tv << " weight: " << w << " cost: " << m_zcost << " " << mk_pp(m_vars[m_bool2var[v]].get(), get_manager()) << "\n";);
            m_costs.push_back(tv);
            m_assigned[tv] = true;
            if (m_zcost >= m_zmin_cost) {
                block();
            }            
            else {
                m_can_propagate = true;
            }
        }
    }

    final_check_status theory_wmaxsat::final_check_eh() {
        if (m_normalize) normalize();
        TRACE("opt", tout << "cost: " << m_zcost << " min cost: " << m_zmin_cost << "\n";);
        return FC_DONE;
    }


    void theory_wmaxsat::reset_eh() {
        theory::reset_eh();
        reset_local();
    }

    void theory_wmaxsat::reset_local() {
        m_vars.reset();
        m_fmls.reset();
        m_rweights.reset();
        m_rmin_cost.reset();
        m_zweights.reset();
        m_zcost.reset();
        m_zmin_cost.reset();
        m_cost_save.reset();
        m_bool2var.reset();
        m_var2bool.reset();
        m_propagate = false;
        m_can_propagate = false;
        m_found_optimal = false;
        m_assigned.reset();
        m_enabled.reset();
    }


    void theory_wmaxsat::propagate() {
        context& ctx = get_context();
        for (unsigned i = 0; m_propagate && i < m_vars.size(); ++i) {
            bool_var bv = m_var2bool[i];
            lbool asgn = ctx.get_assignment(bv);
            if (asgn == l_true) {
                assign_eh(bv, true);
            }
        }
        m_propagate = false;
        //while (m_found_optimal && max_unassigned_is_blocked() && !ctx.inconsistent()) { }

        m_can_propagate = false;
    }       
    
    bool theory_wmaxsat::is_optimal() const {
        return !m_found_optimal || m_zcost < m_zmin_cost;
    }

    expr_ref theory_wmaxsat::mk_block() {
        ++m_stats.m_num_blocks;
        ast_manager& m = get_manager();
        expr_ref_vector disj(m);
        compare_cost compare_cost(*this);
        svector<theory_var> costs(m_costs);
        std::sort(costs.begin(), costs.end(), compare_cost);
        scoped_mpz weight(m_mpz);
        m_mpz.reset(weight);
        for (unsigned i = 0; i < costs.size() && m_mpz.lt(weight, m_zmin_cost); ++i) {
            theory_var tv = costs[i];
            if (m_enabled[tv]) {
                weight += m_zweights[tv];
                disj.push_back(m.mk_not(m_vars[tv].get()));
            }
        }
        if (is_optimal()) {
            m_found_optimal = true;
            m_cost_save.reset();
            m_cost_save.append(m_costs);
            TRACE("opt",
                  tout << "costs: ";
                  for (unsigned i = 0; i < m_costs.size(); ++i) {
                      tout << mk_pp(get_enode(m_costs[i])->get_owner(), get_manager()) << " ";
                  }
                  tout << "\n";
                  //get_context().display(tout);                      
                  );
        }
        expr_ref result(m.mk_or(disj.size(), disj.c_ptr()), m);
        TRACE("opt",
              tout << result << " weight: " << weight << "\n";
              tout << "cost: " << m_zcost << " min-cost: " << m_zmin_cost << "\n";);
        return result;
    }

    void theory_wmaxsat::restart_eh() {}

    void theory_wmaxsat::block() {
        if (m_vars.empty()) {
            return;
        }
        ++m_stats.m_num_blocks;
        context& ctx = get_context();
        literal_vector lits;
        compare_cost compare_cost(*this);
        svector<theory_var> costs(m_costs);
        std::sort(costs.begin(), costs.end(), compare_cost);
        
        scoped_mpz weight(m_mpz);
        m_mpz.reset(weight);
        for (unsigned i = 0; i < costs.size() && weight < m_zmin_cost; ++i) {
            weight += m_zweights[costs[i]];
            lits.push_back(literal(m_var2bool[costs[i]]));
        }
        TRACE("opt", ctx.display_literals_verbose(tout, lits); tout << "\n";);
        
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), 0, nullptr, 0, nullptr)));
    }     

    bool theory_wmaxsat::max_unassigned_is_blocked() {
        context& ctx = get_context();
        unsigned max_unassigned = m_max_unassigned_index;
        if (max_unassigned < m_sorted_vars.size() && 
            m_zcost + m_zweights[m_sorted_vars[max_unassigned]] < m_zmin_cost) {
            return false;
        }
        // update value of max-unassigned
        while (max_unassigned < m_sorted_vars.size() &&
               ctx.get_assignment(m_var2bool[m_sorted_vars[max_unassigned]]) != l_undef) {
            ++max_unassigned;
        }
        // 
        if (max_unassigned > m_max_unassigned_index) {
            ctx.push_trail(value_trail<context, unsigned>(m_max_unassigned_index));
            m_max_unassigned_index = max_unassigned;
        }
        if (max_unassigned < m_sorted_vars.size() && 
            m_zcost + m_zweights[m_sorted_vars[max_unassigned]] >= m_zmin_cost) {
            theory_var tv = m_sorted_vars[max_unassigned];
            propagate(m_var2bool[tv]);
            m_max_unassigned_index++;
            return true;
        }

        return false;
    }
    
    void theory_wmaxsat::propagate(bool_var v) {
        ++m_stats.m_num_propagations;
        context& ctx = get_context();
        literal_vector lits;
        literal lit(v, true);
        
        SASSERT(ctx.get_assignment(lit) == l_undef);
        
        for (unsigned i = 0; i < m_costs.size(); ++i) {
            bool_var w = m_var2bool[m_costs[i]];
            lits.push_back(literal(w));        
        }
        TRACE("opt", 
              ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); 
              ctx.display_literal_verbose(tout << " --> ", lit););
        
        region& r = ctx.get_region();
        ctx.assign(lit, ctx.mk_justification(
                       ext_theory_propagation_justification(
                           get_id(), r, lits.size(), lits.c_ptr(), 0, nullptr, lit, 0, nullptr)));
    }                


    void theory_wmaxsat::normalize() {
        m_den = rational::one();
        for (unsigned i = 0; i < m_rweights.size(); ++i) {
            if (m_enabled[i]) {
                m_den = lcm(m_den, denominator(m_rweights[i]));
            }
        }
        m_den = lcm(m_den, denominator(m_rmin_cost));
        SASSERT(!m_den.is_zero());
        m_zweights.reset();
        m_sorted_vars.reset();
        for (unsigned i = 0; i < m_rweights.size(); ++i) {            
            rational r = m_rweights[i]*m_den;
            SASSERT(r.is_int());
            mpq const& q = r.to_mpq();
            m_zweights.push_back(q.numerator());
            m_sorted_vars.push_back(i);
        }
        compare_cost compare_cost(*this);
        std::sort(m_sorted_vars.begin(), m_sorted_vars.end(), compare_cost);
        m_max_unassigned_index = 0;
        
        m_zcost.reset();
        rational r = m_rmin_cost * m_den;
        m_zmin_cost = r.to_mpq().numerator();
        m_normalize = false;
    }

};
