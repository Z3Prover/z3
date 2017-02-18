/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsmt.cpp

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/

#include <typeinfo>
#include "maxsmt.h"
#include "maxres.h"
#include "wmax.h"
#include "ast_pp.h"
#include "uint_set.h"
#include "opt_context.h"
#include "theory_wmaxsat.h"
#include "theory_pb.h"
#include "ast_util.h"
#include "pb_decl_plugin.h"


namespace opt {

    maxsmt_solver_base::maxsmt_solver_base(
        maxsat_context& c, vector<rational> const& ws, expr_ref_vector const& soft):
        m(c.get_manager()), 
        m_c(c),
        m_soft(soft),
        m_weights(ws),
        m_assertions(m),
        m_trail(m) {
        c.get_base_model(m_model);
        SASSERT(m_model);
        updt_params(c.params());
    }
    
    void maxsmt_solver_base::updt_params(params_ref& p) {
        m_params.copy(p);
    }       

    solver& maxsmt_solver_base::s() {
        return m_c.get_solver(); 
    }

    void maxsmt_solver_base::commit_assignment() {
        expr_ref tmp(m);
        rational k(0), cost(0);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            if (get_assignment(i)) {
                k += m_weights[i];
            }
            else {
                cost += m_weights[i];
            }
        }       
        pb_util pb(m);
        tmp = pb.mk_ge(m_weights.size(), m_weights.c_ptr(), m_soft.c_ptr(), k);
        TRACE("opt", tout << "cost: " << cost << "\n" << tmp << "\n";);
        s().assert_expr(tmp);
    }

    bool maxsmt_solver_base::init() {
        m_lower.reset();
        m_upper.reset();
        m_assignment.reset();
        for (unsigned i = 0; i < m_weights.size(); ++i) {
            expr_ref val(m);
            if (!m_model->eval(m_soft[i], val)) return false;
            m_assignment.push_back(m.is_true(val));
            if (!m_assignment.back()) {
                m_upper += m_weights[i];
            }
        }
        
        TRACE("opt", 
              tout << "upper: " << m_upper << " assignments: ";
              for (unsigned i = 0; i < m_weights.size(); ++i) {
                  tout << (m_assignment[i]?"T":"F");
              }
              tout << "\n";);
        return true;
    }

    void maxsmt_solver_base::set_mus(bool f) {
        params_ref p;
        p.set_bool("minimize_core", f);
        // p.set_bool("minimize_core_partial", f);
        s().updt_params(p);
    }

    void maxsmt_solver_base::enable_sls(bool force) {
        m_c.enable_sls(force);
    }

    app* maxsmt_solver_base::mk_fresh_bool(char const* name) {
        app* result = m.mk_fresh_const(name, m.mk_bool_sort());
        m_c.fm().insert(result->get_decl());
        return result;
    }

    smt::theory_wmaxsat* maxsmt_solver_base::get_wmax_theory() const {
        smt::theory_id th_id = m.get_family_id("weighted_maxsat");
        smt::theory* th = m_c.smt_context().get_theory(th_id);               
        if (th) {
            return dynamic_cast<smt::theory_wmaxsat*>(th);
        }
        else {
            return 0;
        }
    }

    smt::theory_wmaxsat* maxsmt_solver_base::ensure_wmax_theory() {
        smt::theory_wmaxsat* wth = get_wmax_theory();
        if (wth) {
            wth->reset_local();
        }
        else {
            wth = alloc(smt::theory_wmaxsat, m, m_c.fm());
            m_c.smt_context().register_plugin(wth);
        }
        smt::theory_id th_pb = m.get_family_id("pb");
        smt::theory_pb* pb = dynamic_cast<smt::theory_pb*>(m_c.smt_context().get_theory(th_pb));
        if (!pb) {
            theory_pb_params params;
            pb = alloc(smt::theory_pb, m, params);
            m_c.smt_context().register_plugin(pb);
        }
        return wth;
    }

    maxsmt_solver_base::scoped_ensure_theory::scoped_ensure_theory(maxsmt_solver_base& s) {
        m_wth = s.ensure_wmax_theory();
    }
    maxsmt_solver_base::scoped_ensure_theory::~scoped_ensure_theory() {
        if (m_wth) {
            m_wth->reset_local();
        }
    }
    smt::theory_wmaxsat& maxsmt_solver_base::scoped_ensure_theory::operator()() { return *m_wth; }


    void maxsmt_solver_base::trace_bounds(char const * solver) {
        IF_VERBOSE(1, 
                   rational l = m_adjust_value(m_lower);
                   rational u = m_adjust_value(m_upper);
                   if (l > u) std::swap(l, u);
                   verbose_stream() << "(opt." << solver << " [" << l << ":" << u << "])\n";);        
    }

    lbool maxsmt_solver_base::find_mutexes(obj_map<expr, rational>& new_soft) {
        m_lower.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            new_soft.insert(m_soft[i], m_weights[i]);
        }
        vector<expr_ref_vector> mutexes;
        lbool is_sat = s().find_mutexes(m_soft, mutexes);
        if (is_sat != l_true) {
            return is_sat;
        }
        for (unsigned i = 0; i < mutexes.size(); ++i) {
            process_mutex(mutexes[i], new_soft);
        }
        return l_true;
    }

    struct maxsmt_compare_soft {
        obj_map<expr, rational> const& m_soft;
        maxsmt_compare_soft(obj_map<expr, rational> const& soft): m_soft(soft) {}
        bool operator()(expr* a, expr* b) const {
            return m_soft.find(a) > m_soft.find(b);
        }
    };

    void maxsmt_solver_base::process_mutex(expr_ref_vector& mutex, obj_map<expr, rational>& new_soft) {
        TRACE("opt", 
              for (unsigned i = 0; i < mutex.size(); ++i) {
                  tout << mk_pp(mutex[i].get(), m) << " |-> " << new_soft.find(mutex[i].get()) << "\n";
              });
        if (mutex.size() <= 1) {
            return;
        }
        maxsmt_compare_soft cmp(new_soft);
        ptr_vector<expr> _mutex(mutex.size(), mutex.c_ptr());
        std::sort(_mutex.begin(), _mutex.end(), cmp);
        mutex.reset();
        mutex.append(_mutex.size(), _mutex.c_ptr());

        rational weight(0), sum1(0), sum2(0);
        vector<rational> weights;
        for (unsigned i = 0; i < mutex.size(); ++i) {
            rational w = new_soft.find(mutex[i].get());
            weights.push_back(w);
            sum1 += w;
            new_soft.remove(mutex[i].get());
        }
        for (unsigned i = mutex.size(); i > 0; ) {
            --i;
            expr_ref soft(m.mk_or(i+1, mutex.c_ptr()), m);
            m_trail.push_back(soft);
            rational w = weights[i];
            weight = w - weight;
            m_lower += weight*rational(i);
            IF_VERBOSE(1, verbose_stream() << "(opt.maxsat mutex size: " << i + 1 << " weight: " << weight << ")\n";);
            sum2 += weight*rational(i+1);
            new_soft.insert(soft, weight);
            for (; i > 0 && weights[i-1] == w; --i) {} 
            weight = w;
        }        
        SASSERT(sum1 == sum2);        
    }



    maxsmt::maxsmt(maxsat_context& c, unsigned index):
        m(c.get_manager()), m_c(c), m_index(index), 
        m_soft_constraints(m), m_answer(m) {}

    lbool maxsmt::operator()() {
        lbool is_sat = l_undef;
        m_msolver = 0;
        symbol const& maxsat_engine = m_c.maxsat_engine();
        IF_VERBOSE(1, verbose_stream() << "(maxsmt)\n";);
        TRACE("opt", tout << "maxsmt\n";
              s().display(tout); tout << "\n";
              );
        if (m_soft_constraints.empty() || maxsat_engine == symbol("maxres") || maxsat_engine == symbol::null) {            
            m_msolver = mk_maxres(m_c, m_index, m_weights, m_soft_constraints);
        }
        else if (maxsat_engine == symbol("pd-maxres")) {            
            m_msolver = mk_primal_dual_maxres(m_c, m_index, m_weights, m_soft_constraints);
        }
        else if (maxsat_engine == symbol("wmax")) {
            m_msolver = mk_wmax(m_c, m_weights, m_soft_constraints);
        }
        else if (maxsat_engine == symbol("sortmax")) {
            m_msolver = mk_sortmax(m_c, m_weights, m_soft_constraints);
        }
        else {
            warning_msg("solver %s is not recognized, using default 'maxres'", maxsat_engine.str().c_str());
            m_msolver = mk_maxres(m_c, m_index, m_weights, m_soft_constraints);
        }

        if (m_msolver) {
            m_msolver->updt_params(m_params);
            m_msolver->set_adjust_value(m_adjust_value);
            is_sat = l_undef;
            try {
                is_sat = (*m_msolver)();
            }
            catch (z3_exception&) {
                is_sat = l_undef;
            }
            if (is_sat != l_false) {
                m_msolver->get_model(m_model, m_labels);
            }
        }

        IF_VERBOSE(1, verbose_stream() << "is-sat: " << is_sat << "\n";
                   if (is_sat == l_true) {
                       verbose_stream() << "Satisfying soft constraints\n";
                       display_answer(verbose_stream());
                   });

        DEBUG_CODE(if (is_sat == l_true) verify_assignment(););
        
        return is_sat;
    }

    void maxsmt::set_adjust_value(adjust_value& adj) { 
        m_adjust_value = adj; 
        if (m_msolver) {
            m_msolver->set_adjust_value(m_adjust_value);
        }
    }


    void maxsmt::verify_assignment() {
        // TBD: have to use a different solver 
        // because we don't push local scope any longer.
        return;
    }

    bool maxsmt::get_assignment(unsigned idx) const {
        if (m_msolver) {
            return m_msolver->get_assignment(idx);
        }
        else {
            return true;
        }
    } 

    rational maxsmt::get_lower() const {
        rational r = m_lower;
        if (m_msolver) {
            rational q = m_msolver->get_lower();
            if (q > r) r = q;
        }
        return m_adjust_value(r);
    }

    rational maxsmt::get_upper() const {
        rational r = m_upper;
        if (m_msolver) {
            rational q = m_msolver->get_upper();
            if (q < r) r = q; 
        }
        return m_adjust_value(r);
    }

    void maxsmt::update_lower(rational const& r) {
        m_lower = r;
    }

    void maxsmt::update_upper(rational const& r) {
        m_upper = r;
    }    

    void maxsmt::get_model(model_ref& mdl, svector<symbol>& labels) {
        mdl = m_model.get();
        labels = m_labels;
    }

    void maxsmt::commit_assignment() {
        if (m_msolver) {
            m_msolver->commit_assignment();
        }
    }

    void maxsmt::add(expr* f, rational const& w) {
        TRACE("opt", tout << mk_pp(f, m) << " weight: " << w << "\n";);
        SASSERT(m.is_bool(f));
        SASSERT(w.is_pos());
        unsigned index = 0;
        if (m_soft_constraint_index.find(f, index)) {
            m_weights[index] += w;
        }
        else {
            m_soft_constraint_index.insert(f, m_weights.size());
            m_soft_constraints.push_back(f);
            m_weights.push_back(w);
        }
        m_upper += w;
    }

    void maxsmt::display_answer(std::ostream& out) const {
        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            expr* e = m_soft_constraints[i];
            bool is_not = m.is_not(e, e);
            out << m_weights[i] << ": " << mk_pp(e, m)
                << ((is_not != get_assignment(i))?" |-> true ":" |-> false ")
                << "\n";
            
        }
    }
    
    
    bool maxsmt::is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

    void maxsmt::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_msolver) {
            m_msolver->updt_params(p);
        }
    }

    void maxsmt::collect_statistics(statistics& st) const {
        if (m_msolver) {
            m_msolver->collect_statistics(st);
        }
    }

    solver& maxsmt::s() {
        return m_c.get_solver(); 
    }



};
