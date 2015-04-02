/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.cpp

Abstract:

    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/

#include "opt_context.h"
#include "ast_pp.h"
#include "opt_solver.h"
#include "opt_params.hpp"
#include "for_each_expr.h"
#include "goal.h"
#include "tactic.h"
#include "lia2card_tactic.h"
#include "elim01_tactic.h"
#include "solve_eqs_tactic.h"
#include "simplify_tactic.h"
#include "propagate_values_tactic.h"
#include "solve_eqs_tactic.h"
#include "elim_uncnstr_tactic.h"
#include "tactical.h"
#include "model_smt2_pp.h"
#include "card2bv_tactic.h"
#include "nnf_tactic.h"
#include "inc_sat_solver.h"
#include "bv_decl_plugin.h"
#include "pb_decl_plugin.h"
#include "ast_smt_pp.h"
#include "filter_model_converter.h"

namespace opt {

    void context::scoped_state::push() {
        m_hard_lim.push_back(m_hard.size());
        m_objectives_lim.push_back(m_objectives.size());        
        m_objectives_term_trail_lim.push_back(m_objectives_term_trail.size());
    }

    void context::scoped_state::pop() {
        m_hard.resize(m_hard_lim.back());
        unsigned k = m_objectives_term_trail_lim.back();
        while (m_objectives_term_trail.size() > k) {
            unsigned idx = m_objectives_term_trail.back();
            m_objectives[idx].m_terms.pop_back();
            m_objectives[idx].m_weights.pop_back();
            m_objectives_term_trail.pop_back();
        }
        m_objectives_term_trail_lim.pop_back();
        k = m_objectives_lim.back();
        while (m_objectives.size() > k) {
            objective& obj = m_objectives.back();
            if (obj.m_type == O_MAXSMT) {
                m_indices.erase(obj.m_id);
            }
            m_objectives.pop_back();
        }
        m_objectives_lim.pop_back();            
        m_hard_lim.pop_back();   
    }
    
    void context::scoped_state::add(expr* hard) {
        m_hard.push_back(hard);
    }

    bool context::scoped_state::set(ptr_vector<expr> & hard) {
        bool eq = hard.size() == m_hard.size();
        for (unsigned i = 0; eq && i < hard.size(); ++i) {
            eq = hard[i] == m_hard[i].get();
        }
        m_hard.reset();
        m_hard.append(hard.size(), hard.c_ptr());
        return !eq;
    }

    unsigned context::scoped_state::add(expr* f, rational const& w, symbol const& id) {
        if (w.is_neg()) {
            throw default_exception("Negative weight supplied. Weight should be positive");
        }
        if (w.is_zero()) {
            throw default_exception("Zero weight supplied. Weight should be positive");
        }
        if (!m.is_bool(f)) {
            throw default_exception("Soft constraint should be Boolean");
        }
        if (!m_indices.contains(id)) {
            m_objectives.push_back(objective(m, id));
            m_indices.insert(id, m_objectives.size() - 1);
        }
        SASSERT(m_indices.contains(id));        
        unsigned idx = m_indices[id];
        m_objectives[idx].m_terms.push_back(f);
        m_objectives[idx].m_weights.push_back(w);
        m_objectives_term_trail.push_back(idx);
        return idx;
    }

    unsigned context::scoped_state::add(app* t, bool is_max) {
        app_ref tr(t, m);
        if (!m_bv.is_bv(t) && !m_arith.is_int_real(t)) {
            throw default_exception("Objective must be bit-vector, integer or real");   
        }
        unsigned index = m_objectives.size();
        m_objectives.push_back(objective(is_max, tr, index));
        return index;
    }

    context::context(ast_manager& m):
        m(m),
        m_arith(m),
        m_bv(m),
        m_hard_constraints(m),
        m_solver(0),
        m_box_index(UINT_MAX),
        m_optsmt(m),
        m_scoped_state(m),
        m_fm(m),
        m_objective_refs(m),
        m_enable_sat(false),
        m_enable_sls(false),
        m_is_clausal(false),
        m_pp_neat(false)
    {
        params_ref p;
        p.set_bool("model", true);
        p.set_bool("unsat_core", true);
        updt_params(p);
    }

    context::~context() {
        reset_maxsmts();
    }

    void context::reset_maxsmts() {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_maxsmts.reset();
    }

    void context::push() {
        m_scoped_state.push();
    }

    void context::pop(unsigned n) {
        for (unsigned i = 0; i < n; ++i) {
            m_scoped_state.pop();
        }
        clear_state();
        reset_maxsmts();
        m_optsmt.reset();        
        m_hard_constraints.reset();
    }

    void context::set_hard_constraints(ptr_vector<expr>& fmls) {
        if (m_scoped_state.set(fmls)) {
            clear_state();
        }
    }

    void context::add_hard_constraint(expr* f) { 
        m_scoped_state.add(f);
        clear_state();
    }

    unsigned context::add_soft_constraint(expr* f, rational const& w, symbol const& id) { 
        clear_state();
        return m_scoped_state.add(f, w, id);
    }

    unsigned context::add_objective(app* t, bool is_max) {
        clear_state();
        return m_scoped_state.add(t, is_max);
    }

    void context::import_scoped_state() {
        m_optsmt.reset();        
        reset_maxsmts();
        m_objectives.reset();
        m_hard_constraints.reset();
        scoped_state& s = m_scoped_state;        
        for (unsigned i = 0; i < s.m_objectives.size(); ++i) {
            objective& obj = s.m_objectives[i];
            m_objectives.push_back(obj);
            if (obj.m_type == O_MAXSMT) {
                add_maxsmt(obj.m_id);
            }
        }
        m_hard_constraints.append(s.m_hard);
    }

    lbool context::optimize() {
        if (m_pareto) {
            return execute_pareto();
        }
        if (m_box_index != UINT_MAX) {
            return execute_box();
        }
        clear_state();
        init_solver(); 
        import_scoped_state(); 
        normalize();
        internalize();
        update_solver();
        solver& s = get_solver();
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            TRACE("opt", tout << "Hard constraint: " << mk_ismt2_pp(m_hard_constraints[i].get(), m) << std::endl;);
            s.assert_expr(m_hard_constraints[i].get());
        }

        IF_VERBOSE(1, verbose_stream() << "(optimize:check-sat)\n";);
        lbool is_sat = s.check_sat(0,0);
        TRACE("opt", tout << "initial search result: " << is_sat << "\n";);
        if (is_sat != l_true) {
            m_model = 0;
            return is_sat;
        }
        IF_VERBOSE(1, verbose_stream() << "(optimize:sat)\n";);
        s.get_model(m_model);
        TRACE("opt", model_smt2_pp(tout, m, *m_model, 0););
        m_optsmt.setup(*m_opt_solver.get());
        update_lower();
        switch (m_objectives.size()) {
        case 0:
            return is_sat;
        case 1:
            return execute(m_objectives[0], true, false);
        default: {
            opt_params optp(m_params);
            symbol pri = optp.priority();
            if (pri == symbol("pareto")) {
                return execute_pareto();
            }
            else if (pri == symbol("box")) {
                return execute_box();
            }
            else {
                return execute_lex();
            }
        }
        }
    }

    void context::get_base_model(model_ref& mdl) {
        mdl = m_model;
    }

    void context::fix_model(model_ref& mdl) {
        if (mdl) {
            if (m_model_converter) {
                (*m_model_converter)(mdl, 0);
            }
            m_fm(mdl, 0);
        }
    }

    void context::set_model(model_ref& mdl) {
        m_model = mdl;
        fix_model(mdl);
    }

    void context::get_model(model_ref& mdl) {
        mdl = m_model;
        fix_model(mdl);
    }

    lbool context::execute_min_max(unsigned index, bool committed, bool scoped, bool is_max) {
        if (scoped) get_solver().push();            
        lbool result = m_optsmt.lex(index, is_max);
        if (result == l_true) m_optsmt.get_model(m_model);
        if (scoped) get_solver().pop(1);        
        if (result == l_true && committed) m_optsmt.commit_assignment(index);
        return result;
    }
    
    lbool context::execute_maxsat(symbol const& id, bool committed, bool scoped) {
        model_ref tmp;
        maxsmt& ms = *m_maxsmts.find(id);
        if (scoped) get_solver().push();            
        lbool result = ms();
        if (result != l_false && (ms.get_model(tmp), tmp.get())) ms.get_model(m_model);
        if (scoped) get_solver().pop(1);
        if (result == l_true && committed) ms.commit_assignment();
        return result;
    }

    lbool context::execute(objective const& obj, bool committed, bool scoped) {
        switch(obj.m_type) {
        case O_MAXIMIZE: return execute_min_max(obj.m_index, committed, scoped, true);
        case O_MINIMIZE: return execute_min_max(obj.m_index, committed, scoped, false);
        case O_MAXSMT: return execute_maxsat(obj.m_id, committed, scoped);
        default: UNREACHABLE(); return l_undef;
        }
    }
    
    lbool context::execute_lex() {
        lbool r = l_true;
        IF_VERBOSE(1, verbose_stream() << "(optsmt:lex)\n";);
        for (unsigned i = 0; r == l_true && i < m_objectives.size(); ++i) {
            bool is_last = i + 1 == m_objectives.size();
            r = execute(m_objectives[i], i + 1 < m_objectives.size(), !is_last);
            if (r == l_true && !get_lower_as_num(i).is_finite()) {
                return r;
            }
            if (r == l_true && i + 1 < m_objectives.size()) {
                update_lower();
            }
        }
        DEBUG_CODE(if (r == l_true) validate_lex(););
        return r;
    }    

    lbool context::execute_box() {
        if (m_box_index < m_objectives.size()) {
            m_model = m_box_models[m_box_index];
            ++m_box_index;           
            return l_true;
        }
        if (m_box_index != UINT_MAX && m_box_index >= m_objectives.size()) {
            m_box_index = UINT_MAX;
            return l_false;
        }
        m_box_index = 1;
        m_box_models.reset();
        lbool r = m_optsmt.box();
        for (unsigned i = 0, j = 0; r == l_true && i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            if (obj.m_type == O_MAXSMT) {
                solver::scoped_push _sp(get_solver());
                r = execute(obj, false, false);
                if (r == l_true) m_box_models.push_back(m_model.get());
            }
            else {
                m_box_models.push_back(m_optsmt.get_model(j));
                ++j;
            }
        }
        if (r == l_true && m_objectives.size() > 0) {
            m_model = m_box_models[0];
        }
        return r;
    }


    expr_ref context::mk_le(unsigned i, model_ref& mdl) {
        objective const& obj = m_objectives[i];
        return mk_cmp(false, mdl, obj);
    }
    
    expr_ref context::mk_ge(unsigned i, model_ref& mdl) {
        objective const& obj = m_objectives[i];
        return mk_cmp(true, mdl, obj);
    }
    
    
    expr_ref context::mk_gt(unsigned i, model_ref& mdl) {
        expr_ref result = mk_le(i, mdl);
        result = m.mk_not(result);
        return result;
    }

    expr_ref context::mk_cmp(bool is_ge, model_ref& mdl, objective const& obj) {
        rational k(0);
        expr_ref val(m), result(m);
        switch (obj.m_type) {
        case O_MINIMIZE:
            is_ge = !is_ge;
        case O_MAXIMIZE:
            VERIFY(mdl->eval(obj.m_term, val) && is_numeral(val, k));
            if (is_ge) {
                result = mk_ge(obj.m_term, val);
            }
            else {
                result = mk_ge(val, obj.m_term);
            }
            break;
        case O_MAXSMT: {
            m_opt_solver->ensure_pb();
            pb_util      pb(m);
            unsigned sz = obj.m_terms.size();
            ptr_vector<expr> terms;
            vector<rational> coeffs;
            for (unsigned i = 0; i < sz; ++i) {
                terms.push_back(obj.m_terms[i]);
                coeffs.push_back(obj.m_weights[i]);
                VERIFY(mdl->eval(obj.m_terms[i], val));
                if (m.is_true(val)) {
                    k += obj.m_weights[i];
                }
            }
            if (is_ge) {
                result = pb.mk_ge(sz, coeffs.c_ptr(), terms.c_ptr(), k);
            }
            else {
                result = pb.mk_le(sz, coeffs.c_ptr(), terms.c_ptr(), k);
            }
            break;
        }
        }
        TRACE("opt", 
              tout << (is_ge?">= ":"<= ") << k << "\n";
              display_objective(tout, obj);
              tout << "\n";
              tout << result << "\n";);
        return result;
    }    

    expr_ref context::mk_ge(expr* t, expr* s) {
        expr_ref result(m);
        if (m_bv.is_bv(t)) {
            result = m_bv.mk_ule(s, t);
        }
        else {
            result = m_arith.mk_ge(t, s);
        }
        return result;
    }

    void context::yield() {
        m_pareto->get_model(m_model);
        update_bound(true);
        update_bound(false);
    }

    lbool context::execute_pareto() {
        
        if (!m_pareto) {
            set_pareto(alloc(gia_pareto, m, *this, m_solver.get(), m_params));
        }
        lbool is_sat = (*(m_pareto.get()))();
        if (is_sat != l_true) {
            set_pareto(0);
        }
        if (is_sat == l_true) {
            yield();
        }
        return is_sat;
    }

    void context::display_bounds(std::ostream& out, bounds_t const& b) const {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            display_objective(out, obj);
            if (obj.m_type == O_MAXIMIZE) {
                out << " |-> [" << b[i].first << ":" << b[i].second << "]\n";
            }
            else {
                out << " |-> [" << -b[i].second << ":" << -b[i].first << "]\n";
            }
        }        
    }

    solver& context::get_solver() { 
        return *m_solver.get(); 
    }

    void context::init_solver() {
        setup_arith_solver();
        #pragma omp critical (opt_context)
        {
            m_opt_solver = alloc(opt_solver, m, m_params, m_fm);
            m_opt_solver->set_logic(m_logic);
            m_solver = m_opt_solver.get();
        }
    }

    void context::setup_arith_solver() {
        opt_params p(m_params);        
        if (p.optsmt_engine() == symbol("symba") ||
            p.optsmt_engine() == symbol("farkas")) {
            std::stringstream strm;
            strm << AS_OPTINF;
            gparams::set("smt.arith.solver", strm.str().c_str());
        }
    }

    void context::update_solver() {
        if (!m_enable_sat || !probe_bv()) {
            return;
        }
        if (m_maxsat_engine != symbol("maxres") &&
            m_maxsat_engine != symbol("pd-maxres") &&
            m_maxsat_engine != symbol("bcd2") &&
            m_maxsat_engine != symbol("sls")) {
            return;
        }
        m_params.set_bool("minimize_core_partial", true); // false);
        m_params.set_bool("minimize_core", true);
        m_sat_solver = mk_inc_sat_solver(m, m_params);
        unsigned sz = get_solver().get_num_assertions();
        for (unsigned i = 0; i < sz; ++i) {
            m_sat_solver->assert_expr(get_solver().get_assertion(i));
        }   
        #pragma omp critical (opt_context)
        {
            m_solver = m_sat_solver.get();
        }
    }

    void context::set_soft_assumptions() {
        if (m_sat_solver.get()) {
            m_params.set_bool("soft_assumptions", true);
            m_sat_solver->updt_params(m_params);
        }
    }

    void context::enable_sls(expr_ref_vector const& soft, vector<rational> const& weights) {
        SASSERT(soft.size() == weights.size());
        if (m_sat_solver.get()) {
            set_soft_inc_sat(m_sat_solver.get(), soft.size(), soft.c_ptr(), weights.c_ptr());
        }
        if (m_enable_sls && m_sat_solver.get()) {
            m_params.set_bool("optimize_model", true);
            m_sat_solver->updt_params(m_params);
        }
    }

    struct context::is_bv {
        struct found {};
        ast_manager& m;
        pb_util      pb;
        bv_util      bv;
        is_bv(ast_manager& m): m(m), pb(m), bv(m) {}
        void operator()(var *) { throw found(); }
        void operator()(quantifier *) { throw found(); }
        void operator()(app *n) {
            family_id fid = n->get_family_id();
            if (fid != m.get_basic_family_id() &&
                fid != pb.get_family_id() &&
                fid != bv.get_family_id() &&
                !is_uninterp_const(n)) {
                throw found();
            }
        }        
    };

    bool context::probe_bv() {
        expr_fast_mark1 visited;
        is_bv proc(m);
        try {
            for (unsigned i = 0; i < m_objectives.size(); ++i) {
                objective & obj = m_objectives[i];
                if (obj.m_type != O_MAXSMT) return false;
                maxsmt& ms = *m_maxsmts.find(obj.m_id);
                for (unsigned j = 0; j < ms.size(); ++j) {
                    quick_for_each_expr(proc, visited, ms[j]);
                }
            }
            unsigned sz = get_solver().get_num_assertions();
            for (unsigned i = 0; i < sz; i++) {
                quick_for_each_expr(proc, visited, get_solver().get_assertion(i));
            }
            for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
                quick_for_each_expr(proc, visited, m_hard_constraints[i].get());
            }
        }
        catch (is_bv::found) {
            return false;
        }
        return true;
    }

    struct context::is_propositional_fn {
        struct found {};
        ast_manager& m;
        is_propositional_fn(ast_manager& m): m(m) {}
        void operator()(var *) { throw found(); }
        void operator()(quantifier *) { throw found(); }
        void operator()(app *n) {
            family_id fid = n->get_family_id();
            if (fid != m.get_basic_family_id() &&
                !is_uninterp_const(n)) {
                throw found();
            }
        }        
    };

    bool context::is_propositional(expr* p) {
        expr* np;
        if (is_uninterp_const(p) || (m.is_not(p, np) && is_uninterp_const(np))) {
            return true;
        }
        is_propositional_fn proc(m);
        expr_fast_mark1 visited;
        try {
            quick_for_each_expr(proc, visited, p);
        }
        catch (is_propositional_fn::found) {
            return false;
        }
        return true;
    }


    void context::add_maxsmt(symbol const& id) {
        maxsmt* ms = alloc(maxsmt, *this);
        ms->updt_params(m_params);
        #pragma omp critical (opt_context)
        {
            m_maxsmts.insert(id, ms);
        }
    }

    bool context::is_numeral(expr* e, rational & n) const {
        unsigned sz;
        return m_arith.is_numeral(e, n) || m_bv.is_numeral(e, n, sz);
    }

    void context::normalize() {
        expr_ref_vector fmls(m);
        to_fmls(fmls);
        simplify_fmls(fmls);
        from_fmls(fmls);
    }

    void context::simplify_fmls(expr_ref_vector& fmls) {
        if (m_is_clausal) {
            return;
        }

        goal_ref g(alloc(goal, m, true, false));
        for (unsigned i = 0; i < fmls.size(); ++i) {
            g->assert_expr(fmls[i].get());
        }
        tactic_ref tac0 = 
            and_then(mk_simplify_tactic(m), 
                     mk_propagate_values_tactic(m),
                     mk_solve_eqs_tactic(m),
                     // NB: mk_elim_uncstr_tactic(m) is not sound with soft constraints
                     mk_simplify_tactic(m));   
        opt_params optp(m_params);
        tactic_ref tac2, tac3;
        if (optp.elim_01()) {
            tac2 = mk_elim01_tactic(m);
            tac3 = mk_lia2card_tactic(m);
            params_ref lia_p;
            lia_p.set_bool("compile_equality", optp.pb_compile_equality());
            tac3->updt_params(lia_p);
            set_simplify(and_then(tac0.get(), tac2.get(), tac3.get()));
        }
        else {
            set_simplify(tac0.get());
        }
        proof_converter_ref pc;
        expr_dependency_ref core(m);
        goal_ref_buffer result;
        (*m_simplify)(g, result, m_model_converter, pc, core); 
        SASSERT(result.size() == 1);
        goal* r = result[0];
        fmls.reset();
        expr_ref tmp(m);
        for (unsigned i = 0; i < r->size(); ++i) {
            fmls.push_back(r->form(i));
        }        
    }

    bool context::is_maximize(expr* fml, app_ref& term, expr*& orig_term, unsigned& index) {
        if (is_app(fml) && m_objective_fns.find(to_app(fml)->get_decl(), index) && 
            m_objectives[index].m_type == O_MAXIMIZE) {
            term = to_app(to_app(fml)->get_arg(0));
            orig_term = m_objective_orig.find(to_app(fml)->get_decl());
            return true;
        }
        return false;
    }

    bool context::is_minimize(expr* fml, app_ref& term, expr*& orig_term, unsigned& index) {
        if (is_app(fml) && m_objective_fns.find(to_app(fml)->get_decl(), index) && 
            m_objectives[index].m_type == O_MINIMIZE) {
            term = to_app(to_app(fml)->get_arg(0));
            orig_term = m_objective_orig.find(to_app(fml)->get_decl());
            return true;
        }
        return false;
    }

    bool context::is_maxsat(expr* fml, expr_ref_vector& terms, 
                            vector<rational>& weights, rational& offset, 
                            bool& neg, symbol& id, unsigned& index) {
        if (!is_app(fml)) return false;
        neg = false;
        app* a = to_app(fml);
        if (m_objective_fns.find(a->get_decl(), index) && m_objectives[index].m_type == O_MAXSMT) {
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* arg = a->get_arg(i);
                if (m.is_true(arg)) {
                    // skip
                }
                else if (m.is_false(arg)) {
                    offset += m_objectives[index].m_weights[i];
                }
                else {
                    terms.push_back(arg);
                    weights.push_back(m_objectives[index].m_weights[i]);
                }
            } 
            id = m_objectives[index].m_id;
            return true;
        }
        app_ref term(m);
        expr* orig_term;
        offset = rational::zero();
        bool is_max = is_maximize(fml, term, orig_term, index);
        bool is_min = !is_max && is_minimize(fml, term, orig_term, index);
        if (is_min && get_pb_sum(term, terms, weights, offset)) {
            TRACE("opt", tout << "try to convert minimization" << mk_pp(term, m) << "\n";);
            // minimize 2*x + 3*y 
            // <=>
            // (assert-soft (not x) 2)
            // (assert-soft (not y) 3)
            //
            for (unsigned i = 0; i < weights.size(); ++i) {
                if (weights[i].is_neg()) {
                    offset += weights[i];
                    weights[i].neg();
                }
                else {
                    terms[i] = m.mk_not(terms[i].get());
                }
            }
            TRACE("opt", 
                  tout << "Convert minimization " << mk_pp(orig_term, m) << "\n";
                  tout << "to maxsat: " << term << "\n";
                  for (unsigned i = 0; i < weights.size(); ++i) {
                      tout << mk_pp(terms[i].get(), m) << ": " << weights[i] << "\n";
                  }
                  tout << "offset: " << offset << "\n";
                  );
            std::ostringstream out;
            out << mk_pp(orig_term, m);
            id = symbol(out.str().c_str());
            return true;
        }
        if (is_max && get_pb_sum(term, terms, weights, offset)) {
            TRACE("opt", tout << "try to convert maximization" << mk_pp(term, m) << "\n";);
            // maximize 2*x + 3*y - z 
            // <=>
            // (assert-soft x 2)
            // (assert-soft y 3)
            // (assert-soft (not z) 1)
            // offset := 6
            // maximize = offset - penalty
            // 
            for (unsigned i = 0; i < weights.size(); ++i) {
                if (weights[i].is_neg()) {
                    weights[i].neg();
                    terms[i] = m.mk_not(terms[i].get());
                }
                offset += weights[i];
            }
            neg = true;
            std::ostringstream out;
            out << mk_pp(orig_term, m);
            id = symbol(out.str().c_str());
            return true;
        }
        if ((is_max || is_min) && m_bv.is_bv(term)) {
            offset.reset();
            unsigned bv_size = m_bv.get_bv_size(term);
            expr_ref val(m);
            val = m_bv.mk_numeral(is_max, 1);
            for (unsigned i = 0; i < bv_size; ++i) {
                rational w = power(rational(2),i);
                weights.push_back(w);
                terms.push_back(m.mk_eq(val, m_bv.mk_extract(i, i, term)));
                if (is_max) {
                    offset += w;
                }
            }
            neg = is_max;
            std::ostringstream out;
            out << mk_pp(orig_term, m);
            id = symbol(out.str().c_str());
            return true;            
        }
        return false;
    }

    expr* context::mk_objective_fn(unsigned index, objective_t ty, unsigned sz, expr*const* args) {
        ptr_vector<sort> domain;
        for (unsigned i = 0; i < sz; ++i) {
            domain.push_back(m.get_sort(args[i]));
        }
        char const* name = "";
        switch(ty) {
        case O_MAXIMIZE: name = "maximize"; break;
        case O_MINIMIZE: name = "minimize"; break;
        case O_MAXSMT: name = "maxsat"; break;
        default: break;
        }
        func_decl* f = m.mk_fresh_func_decl(name,"", domain.size(), domain.c_ptr(), m.mk_bool_sort());
        m_objective_fns.insert(f, index);
        m_objective_refs.push_back(f);
        if (sz > 0) {
            m_objective_orig.insert(f, args[0]);
        }
        return m.mk_app(f, sz, args);
    }

    expr* context::mk_maximize(unsigned index, app* t) {
        expr* t_ = t;
        return mk_objective_fn(index, O_MAXIMIZE, 1, &t_);
    }

    expr* context::mk_minimize(unsigned index, app* t) {
        expr* t_ = t;
        return mk_objective_fn(index, O_MINIMIZE, 1, &t_);
    }

    expr* context::mk_maxsat(unsigned index, unsigned num_fmls, expr* const* fmls) {
        return mk_objective_fn(index, O_MAXSMT, num_fmls, fmls);
    }

    void context::from_fmls(expr_ref_vector const& fmls) {
        TRACE("opt",
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i], m) << "\n";
              });
        m_hard_constraints.reset();
        expr* orig_term;
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls[i];
            app_ref tr(m);
            expr_ref_vector terms(m);
            vector<rational> weights;
            rational offset(0);
            unsigned index;
            symbol id;
            bool neg;
            if (is_maxsat(fml, terms, weights, offset, neg, id, index)) {
                objective& obj = m_objectives[index];
                if (obj.m_type != O_MAXSMT) {
                    // change from maximize/minimize.
                    obj.m_id = id;
                    obj.m_type = O_MAXSMT;
                    obj.m_weights.append(weights);
                    SASSERT(!m_maxsmts.contains(id));
                    add_maxsmt(id);
                }
                mk_atomic(terms);
                SASSERT(obj.m_id == id);
                obj.m_terms.reset();
                obj.m_terms.append(terms);
                obj.m_adjust_value.set_offset(offset);
                obj.m_adjust_value.set_negate(neg);
                m_maxsmts.find(id)->set_adjust_value(obj.m_adjust_value);
                TRACE("opt", tout << "maxsat: " << id << " offset:" << offset << "\n";);
            }
            else if (is_maximize(fml, tr, orig_term, index)) {
                m_objectives[index].m_term = tr;
            }
            else if (is_minimize(fml, tr, orig_term, index)) {
                m_objectives[index].m_term = tr;
                m_objectives[index].m_adjust_value.set_negate(true);
            }
            else {
                m_hard_constraints.push_back(fml);
            }
        }
    }

    /**
       To select the proper theory solver we have to ensure that all theory 
       symbols from soft constraints are reflected in the hard constraints.

       - filter "obj" from generated model.
     */
    void context::mk_atomic(expr_ref_vector& terms) {
        ref<filter_model_converter> fm;
        for (unsigned i = 0; i < terms.size(); ++i) {
            expr_ref p(terms[i].get(), m);
            app_ref q(m);
            if (is_propositional(p)) {
                terms[i] = p;
            }
            else {
                q = m.mk_fresh_const("obj", m.mk_bool_sort()); 
                terms[i] = q;
                m_hard_constraints.push_back(m.mk_iff(p, q));
                if (!fm) fm = alloc(filter_model_converter, m);
                fm->insert(q->get_decl());
            }
        }
        if (fm) {
            m_model_converter = concat(m_model_converter.get(), fm.get());
        }
    }

    void context::to_fmls(expr_ref_vector& fmls) {
        m_objective_fns.reset();
        fmls.append(m_hard_constraints);
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE:
                fmls.push_back(mk_minimize(i, obj.m_term));
                break;
            case O_MAXIMIZE:
                fmls.push_back(mk_maximize(i, obj.m_term));
                break;
            case O_MAXSMT: 
                fmls.push_back(mk_maxsat(i, obj.m_terms.size(), obj.m_terms.c_ptr()));
                break;
            }
        }
        TRACE("opt",
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i].get(), m) << "\n";
              });
    }

    void context::internalize() {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective & obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE: {
                app_ref tmp(m);
                tmp = m_arith.mk_uminus(obj.m_term);
                obj.m_index = m_optsmt.add(tmp);
                break;
            }
            case O_MAXIMIZE:
                obj.m_index = m_optsmt.add(obj.m_term);
                break;
            case O_MAXSMT: {
                maxsmt& ms = *m_maxsmts.find(obj.m_id);
                for (unsigned j = 0; j < obj.m_terms.size(); ++j) {
                    ms.add(obj.m_terms[j].get(), obj.m_weights[j]);        
                }
                break;
            }
            }
        }
    }

    void context::update_bound(bool is_lower) {
        expr_ref val(m);
        if (!m_model.get()) return;
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            rational r;
            switch(obj.m_type) {
            case O_MINIMIZE: {
                bool evaluated = m_model->eval(obj.m_term, val);
                TRACE("opt", tout << obj.m_term << " " << val << " " << evaluated << " " << is_numeral(val, r) << "\n";);
                if (evaluated && is_numeral(val, r)) {
                    inf_eps val = inf_eps(obj.m_adjust_value(r));
                    TRACE("opt", tout << "adjusted value: " << val << "\n";);
                    if (is_lower) {
                        m_optsmt.update_lower(obj.m_index, val);
                    }
                    else {
                        m_optsmt.update_upper(obj.m_index, val);
                    }
                }
                break;
            }
            case O_MAXIMIZE: {
                bool evaluated = m_model->eval(obj.m_term, val);
                TRACE("opt", tout << obj.m_term << " " << val << "\n";);
                if (evaluated && is_numeral(val, r)) {
                    inf_eps val = inf_eps(obj.m_adjust_value(r));
                    TRACE("opt", tout << "adjusted value: " << val << "\n";);
                    if (is_lower) {
                        m_optsmt.update_lower(obj.m_index, val);
                    }
                    else {
                        m_optsmt.update_upper(obj.m_index, val);
                    }
                }
                break;
            }
            case O_MAXSMT: {
                bool ok = true;
                for (unsigned j = 0; ok && j < obj.m_terms.size(); ++j) {
                    bool evaluated = m_model->eval(obj.m_terms[j], val);
                    TRACE("opt", tout << mk_pp(obj.m_terms[j], m) << " " << val << "\n";);
                    if (evaluated) {
                        if (!m.is_true(val)) {
                            r += obj.m_weights[j];
                        }
                    }
                    else {
                        ok = false;
                    }
                }
                if (ok) {
                    maxsmt& ms = *m_maxsmts.find(obj.m_id);
                    if (is_lower) {
                        ms.update_upper(r);
                        TRACE("opt", tout << r << " " << ms.get_upper() << "\n";);                        
                    }
                    else {
                        ms.update_lower(r);
                        TRACE("opt", tout << r << " " << ms.get_lower() << "\n";);                        
                    }
                }
                break;
            }
            }
        }
    }

    void context::display(std::ostream& out) {
        display_assignment(out);
    }

    void context::display_assignment(std::ostream& out) {
        for (unsigned i = 0; i < m_scoped_state.m_objectives.size(); ++i) {
            objective const& obj = m_scoped_state.m_objectives[i];
            display_objective(out, obj);
            if (get_lower_as_num(i) != get_upper_as_num(i)) {
                out << " |-> [" << get_lower(i) << ":" << get_upper(i) << "]\n";
            }
            else {
                out << " |-> " << get_lower(i) << "\n";
            }
        }
    }

    void context::display_objective(std::ostream& out, objective const& obj) const {
        switch(obj.m_type) {
        case O_MAXSMT: {
            symbol s = obj.m_id;
            if (s != symbol::null) {
                out << s;
            }
            break;
        }
        default:
            out << obj.m_term;
            break;
        }
    }

    inf_eps context::get_lower_as_num(unsigned idx) {
        if (idx > m_objectives.size()) {
            throw default_exception("index out of bounds"); 
        }
        objective const& obj = m_objectives[idx];
        switch(obj.m_type) {
        case O_MAXSMT: 
            return inf_eps(m_maxsmts.find(obj.m_id)->get_lower());
        case O_MINIMIZE:
            return obj.m_adjust_value(m_optsmt.get_upper(obj.m_index));
        case O_MAXIMIZE: 
            return obj.m_adjust_value(m_optsmt.get_lower(obj.m_index));
        default:
            UNREACHABLE();
            return inf_eps();
        }        
    }

    inf_eps context::get_upper_as_num(unsigned idx) {
        if (idx > m_objectives.size()) {
            throw default_exception("index out of bounds"); 
        }
        objective const& obj = m_objectives[idx];
        switch(obj.m_type) {
        case O_MAXSMT: 
            return inf_eps(m_maxsmts.find(obj.m_id)->get_upper());
        case O_MINIMIZE:
            return obj.m_adjust_value(m_optsmt.get_lower(obj.m_index));
        case O_MAXIMIZE: 
            return obj.m_adjust_value(m_optsmt.get_upper(obj.m_index));
        default:
            UNREACHABLE();
            return inf_eps();
        }
    }

    expr_ref context::get_lower(unsigned idx) {
        return to_expr(get_lower_as_num(idx));
    }

    expr_ref context::get_upper(unsigned idx) {
        return to_expr(get_upper_as_num(idx));
    }

    expr_ref context::to_expr(inf_eps const& n) {
        rational inf = n.get_infinity();
        rational r   = n.get_rational();
        rational eps = n.get_infinitesimal();
        expr_ref_vector args(m);
        if (!inf.is_zero()) {
            expr* oo = m.mk_const(symbol("oo"), m_arith.mk_int());
            if (inf.is_one()) {
                args.push_back(oo);
            }
            else {
                args.push_back(m_arith.mk_mul(m_arith.mk_numeral(inf, inf.is_int()), oo));
            }
        }
        if (!r.is_zero()) {
            args.push_back(m_arith.mk_numeral(r, r.is_int()));
        }
        if (!eps.is_zero()) {
            expr* ep = m.mk_const(symbol("epsilon"), m_arith.mk_real());
            if (eps.is_one()) {
                args.push_back(ep);
            }
            else {
                args.push_back(m_arith.mk_mul(m_arith.mk_numeral(eps, eps.is_int()), ep));
            }
        }
        switch(args.size()) {
        case 0: return expr_ref(m_arith.mk_numeral(rational(0), true), m);
        case 1: return expr_ref(args[0].get(), m);
        default: return expr_ref(m_arith.mk_add(args.size(), args.c_ptr()), m);
        }
    }
       
    void context::set_simplify(tactic* tac) {
        #pragma omp critical (opt_context)
        {
            m_simplify = tac;
        }
    }

    void context::clear_state() {
        set_pareto(0);
        m_box_index = UINT_MAX;
        m_model.reset();
    }

    void context::set_pareto(pareto_base* p) {
        #pragma omp critical (opt_context)
        {
            m_pareto = p;
        }
    }

    void context::set_cancel(bool f) {
        #pragma omp critical (opt_context)
        {
            if (m_solver) {
                if (f) m_solver->cancel(); else m_solver->reset_cancel();
            }
            if (m_pareto) {
                m_pareto->set_cancel(f);
            }
            if (m_simplify) {
                if (f) m_simplify->cancel(); else m_solver->reset_cancel();
            }
            map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
            for (; it != end; ++it) {
                it->m_value->set_cancel(f);
            }            
        }
        m_optsmt.set_cancel(f);
    }

    void context::collect_statistics(statistics& stats) const {
        if (m_solver) {
            m_solver->collect_statistics(stats);
        }
        if (m_simplify) {
            m_simplify->collect_statistics(stats);
        }
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            it->m_value->collect_statistics(stats);
        }        
    }

    void context::collect_param_descrs(param_descrs & r) {
        opt_params::collect_param_descrs(r);
    }
    
    void context::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_solver) {
            m_solver->updt_params(m_params);
        }
        m_optsmt.updt_params(m_params);
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            it->m_value->updt_params(m_params);
        }
        opt_params _p(p);
        m_enable_sat = _p.enable_sat();
        m_enable_sls = _p.enable_sls();
        m_maxsat_engine = _p.maxsat_engine();
        m_pp_neat = _p.pp_neat();
    }

    typedef obj_hashtable<func_decl> func_decl_set;

    struct context::free_func_visitor {
        ast_manager& m;
        func_decl_set m_funcs;
        obj_hashtable<sort> m_sorts;
        expr_mark m_visited;
    public:
        free_func_visitor(ast_manager& m): m(m) {}
        void operator()(var * n)        { }
        void operator()(app * n)        { 
            if (n->get_family_id() == null_family_id) {
                m_funcs.insert(n->get_decl()); 
            }
            sort* s = m.get_sort(n);
            if (s->get_family_id() == null_family_id) {
                m_sorts.insert(s);
            }
        }
        void operator()(quantifier * n) { }
        func_decl_set& funcs() { return m_funcs; }
        obj_hashtable<sort>& sorts() { return m_sorts; }

        void collect(expr* e) {
            for_each_expr(*this, m_visited, e);
        }
    };

    std::string context::to_string() const {
        smt2_pp_environment_dbg env(m);
        ast_smt_pp ll_smt2_pp(m);
        free_func_visitor visitor(m);
        std::ostringstream out;
#define PP(_e_) ast_smt2_pp(out, _e_, env);
#define PPE(_e_) if (m_pp_neat) ast_smt2_pp(out, _e_, env); else ll_smt2_pp.display_expr_smt2(out, _e_);
        for (unsigned i = 0; i < m_scoped_state.m_hard.size(); ++i) {
            visitor.collect(m_scoped_state.m_hard[i]);
        }
        for (unsigned i = 0; i < m_scoped_state.m_objectives.size(); ++i) {
            objective const& obj = m_scoped_state.m_objectives[i];
            switch(obj.m_type) {
            case O_MAXIMIZE: 
            case O_MINIMIZE:
                visitor.collect(obj.m_term);
                break;
            case O_MAXSMT: 
                for (unsigned j = 0; j < obj.m_terms.size(); ++j) {
                    visitor.collect(obj.m_terms[j]);
                }
                break;
            default: 
                UNREACHABLE();
                break;
            }
        }

        obj_hashtable<sort>::iterator sit = visitor.sorts().begin();
        obj_hashtable<sort>::iterator send = visitor.sorts().end();
        for (; sit != send; ++sit) {
            PP(*sit);
        }
        func_decl_set::iterator it  = visitor.funcs().begin();
        func_decl_set::iterator end = visitor.funcs().end();
        for (; it != end; ++it) {
            PP(*it);
            out << "\n";
        }
        for (unsigned i = 0; i < m_scoped_state.m_hard.size(); ++i) {
            out << "(assert ";
            PPE(m_scoped_state.m_hard[i]);
            out << ")\n";
        }
        for (unsigned i = 0; i < m_scoped_state.m_objectives.size(); ++i) {
            objective const& obj = m_scoped_state.m_objectives[i];
            switch(obj.m_type) {
            case O_MAXIMIZE: 
                out << "(maximize ";
                PP(obj.m_term);
                out << ")\n";
                break;
            case O_MINIMIZE:
                out << "(minimize ";
                PP(obj.m_term);
                out << ")\n";
                break;
            case O_MAXSMT: 
                for (unsigned j = 0; j < obj.m_terms.size(); ++j) {
                    out << "(assert-soft ";
                    PP(obj.m_terms[j]);
                    rational w = obj.m_weights[j];
                    if (w.is_int()) {
                        out << " :weight " << w;
                    }
                    else {
                        out << " :dweight " << w;
                    }
                    if (obj.m_id != symbol::null) {
                        out << " :id " << obj.m_id;
                    }
                    out << ")\n";
                }
                break;
            default: 
                UNREACHABLE();
                break;
            }
        }        
        
        param_descrs descrs;
        collect_param_descrs(descrs);
        m_params.display_smt2(out, "opt", descrs);
        
        out << "(check-sat)\n"; 
        return out.str();
    }

    void context::validate_lex() {
        rational r1;
        expr_ref val(m);
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE:
            case O_MAXIMIZE: {
                inf_eps n = m_optsmt.get_lower(obj.m_index);
                if (m_optsmt.objective_is_model_valid(obj.m_index) && 
                    n.get_infinity().is_zero() &&
                    n.get_infinitesimal().is_zero() &&
                    m_model->eval(obj.m_term, val) &&
                    is_numeral(val, r1)) {
                    rational r2 = n.get_rational();
                    if (obj.m_type == O_MINIMIZE) {
                        r1.neg();
                    }
                    CTRACE("opt", r1 != r2, tout << obj.m_term << " evaluates to " << r1 << " but has objective " << r2 << "\n";);
                    CTRACE("opt", r1 != r2, model_smt2_pp(tout, m, *m_model, 0););
                    SASSERT(r1 == r2);
                }
                break;
            }
            case O_MAXSMT: {
                maxsmt& ms = *m_maxsmts.find(obj.m_id);
                rational value(0);
                for (unsigned i = 0; i < obj.m_terms.size(); ++i) {
                    VERIFY(m_model->eval(obj.m_terms[i], val));
                    if (!m.is_true(val)) {
                        value += obj.m_weights[i];
                    }
                    // TBD: check that optimal was not changed.
                }
                TRACE("opt", tout << "value " << value << "\n";);
                break;
            }
            }       
        } 
    }
}
