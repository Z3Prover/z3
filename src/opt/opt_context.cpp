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

#include "util/gparams.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/bv_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/ast_smt_pp.h"
#include "ast/ast_pp_util.h"
#include "model/model_smt2_pp.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/arith/lia2card_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/tactical.h"
#include "tactic/arith/card2bv_tactic.h"
#include "tactic/arith/eq2bv_tactic.h"
#include "tactic/bv/dt2bv_tactic.h"
#include "tactic/generic_model_converter.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "qe/qsat.h"
#include "opt/opt_context.h"
#include "opt/opt_solver.h"
#include "opt/opt_params.hpp"


namespace opt {

    void context::scoped_state::push() {
        m_asms_lim.push_back(m_asms.size());
        m_hard_lim.push_back(m_hard.size());
        m_objectives_lim.push_back(m_objectives.size());        
        m_objectives_term_trail_lim.push_back(m_objectives_term_trail.size());
    }

    void context::scoped_state::pop() {
        m_hard.resize(m_hard_lim.back());
        m_asms.resize(m_asms_lim.back());
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
        m_asms_lim.pop_back();
    }
    
    void context::scoped_state::add(expr* hard) {
        m_hard.push_back(hard);
    }

    bool context::scoped_state::set(expr_ref_vector const & hard) {
        bool eq = hard.size() == m_hard.size();
        for (unsigned i = 0; eq && i < hard.size(); ++i) {
            eq = hard.get(i) == m_hard.get(i);
        }
        m_hard.reset();
        m_hard.append(hard);
        return !eq;
    }

    unsigned context::scoped_state::add(expr* f, rational const& w, symbol const& id) {
        if (!m.is_bool(f)) {
            throw default_exception("Soft constraint should be Boolean");
        }
        if (!m_indices.contains(id)) {
            m_objectives.push_back(objective(m, id));
            m_indices.insert(id, m_objectives.size() - 1);
        }
        SASSERT(m_indices.contains(id));        
        unsigned idx = m_indices[id];
        if (!w.is_zero()) {
            m_objectives[idx].m_terms.push_back(f);
            m_objectives[idx].m_weights.push_back(w);
            m_objectives_term_trail.push_back(idx);
        }
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
        m_solver(nullptr),
        m_pareto1(false),
        m_box_index(UINT_MAX),
        m_optsmt(m, *this),
        m_scoped_state(m),
        m_fm(alloc(generic_model_converter, m, "opt")),
        m_model_fixed(),
        m_objective_refs(m),
        m_core(m),
        m_enable_sat(false),
        m_is_clausal(false),
        m_pp_neat(false),
        m_unknown("unknown")
    {
        params_ref p;
        p.set_bool("model", true);
        p.set_bool("unsat_core", true);
        p.set_bool("elim_to_real", true);
        updt_params(p);
        m_model_counter = 0;
    }

    context::~context() {
        reset_maxsmts();
    }

    void context::reset_maxsmts() {
        for (auto& kv : m_maxsmts) {
            dealloc(kv.m_value);
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

    void context::get_labels(svector<symbol> & r) {
        r.append(m_labels);
    }

    void context::get_unsat_core(expr_ref_vector & r) { 
        r.append(m_core);
    }

    void context::set_hard_constraints(expr_ref_vector const& fmls) {
        if (m_scoped_state.set(fmls)) {
            clear_state();
        }
    }

    void context::add_hard_constraint(expr* f) { 
        m_scoped_state.add(f);
        clear_state();
    }

    void context::add_hard_constraint(expr* f, expr* t) {
        m_scoped_state.m_asms.push_back(t);
        m_scoped_state.add(m.mk_implies(t, f));
        clear_state();
    }

    void context::get_hard_constraints(expr_ref_vector& hard) {
        hard.append(m_scoped_state.m_hard);
    }

    expr_ref context::get_objective(unsigned i) {
        SASSERT(i < num_objectives());
        objective const& o = m_scoped_state.m_objectives[i];
        expr_ref result(m), zero(m);
        expr_ref_vector args(m);
        switch (o.m_type) {
        case O_MAXSMT:
            zero = m_arith.mk_numeral(rational(0), false);
            for (unsigned i = 0; i < o.m_terms.size(); ++i) {
                args.push_back(m.mk_ite(o.m_terms[i], zero, m_arith.mk_numeral(o.m_weights[i], false)));
            }
            result = m_arith.mk_add(args.size(), args.c_ptr());
            break;
        case O_MAXIMIZE:
            result = o.m_term;
            if (m_arith.is_arith_expr(result)) {
                result = m_arith.mk_uminus(result);
            }
            else if (m_bv.is_bv(result)) {
                result = m_bv.mk_bv_neg(result);
            }
            else {
                UNREACHABLE();
            }
            break;
        case O_MINIMIZE:
            result = o.m_term;
            break;
        }
        return result;
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
                add_maxsmt(obj.m_id, i);
            }
        }
        m_hard_constraints.append(s.m_hard);
    }

    lbool context::optimize(expr_ref_vector const& _asms) {
        if (m_pareto) {
            return execute_pareto();
        }
        if (m_box_index != UINT_MAX) {
            return execute_box();
        }
        clear_state();
        init_solver(); 
        import_scoped_state(); 
        expr_ref_vector asms(_asms);
        asms.append(m_scoped_state.m_asms);
        normalize(asms);
        if (m_hard_constraints.size() == 1 && m.is_false(m_hard_constraints.get(0))) {
            return l_false;
        }
        internalize();
        update_solver();
        if (contains_quantifiers()) {
            warning_msg("optimization with quantified constraints is not supported");
        }
#if 0
        if (is_qsat_opt()) {
            return run_qsat_opt();
        }
#endif
        solver& s = get_solver();
        s.assert_expr(m_hard_constraints);
        
        opt_params optp(m_params);
        symbol pri = optp.priority();

        IF_VERBOSE(1, verbose_stream() << "(optimize:check-sat)\n");
        
        lbool is_sat = s.check_sat(asms.size(),asms.c_ptr());

        TRACE("opt", s.display(tout << "initial search result: " << is_sat << "\n");); 
        if (is_sat != l_false) {
            s.get_model(m_model);
            s.get_labels(m_labels);
            model_updated(m_model.get());
        }
        if (is_sat != l_true) {
            TRACE("opt", tout << m_hard_constraints << " " << asms << "\n";);            
            if (!asms.empty()) {
                s.get_unsat_core(m_core);
            }
            return is_sat;
        }
        s.assert_expr(asms);
        IF_VERBOSE(1, verbose_stream() << "(optimize:sat)\n");
        TRACE("opt", model_smt2_pp(tout, m, *m_model, 0););
        m_optsmt.setup(*m_opt_solver.get());
        update_lower();
        
        switch (m_objectives.size()) {
        case 0:
            break;
        case 1:
            if (m_pareto1) {
                is_sat = l_false;
                m_pareto1 = false;
            }
            else {
                m_pareto1 = (pri == symbol("pareto"));
                is_sat = execute(m_objectives[0], true, false);
            }
            break;
        default: {
            opt_params optp(m_params);
            symbol pri = optp.priority();
            if (pri == symbol("pareto")) {
                is_sat = execute_pareto();
            }
            else if (pri == symbol("box")) {
                is_sat = execute_box();
            }
            else {
                is_sat = execute_lex();
            }
        }
        }
        if (is_sat == l_true) validate_model();
        return adjust_unknown(is_sat);
    }

    lbool context::adjust_unknown(lbool r) {
        if (r == l_true && m_opt_solver.get() && m_opt_solver->was_unknown()) {
            r = l_undef;
        }
        return r;
    }

    void context::get_base_model(model_ref& mdl) {
        mdl = m_model;
    }

    void context::fix_model(model_ref& mdl) {
        if (mdl && !m_model_fixed.contains(mdl.get())) {
            TRACE("opt", m_fm->display(tout << "fix-model\n");
                  if (m_model_converter) m_model_converter->display(tout););
            (*m_fm)(mdl);
            apply(m_model_converter, mdl);
            m_model_fixed.push_back(mdl.get());
        }
    }

    void context::set_model(model_ref& m) { 
        m_model = m; 
        opt_params optp(m_params);
        if (optp.dump_models()) {
            model_ref md = m->copy();
            fix_model(md);
            std::cout << *md << "\n";
        }
    }


    void context::get_model_core(model_ref& mdl) {
        mdl = m_model;
        fix_model(mdl);
        if (mdl) mdl->set_model_completion(true);
        CTRACE("opt", mdl, tout << *mdl;);
    }

    void context::get_box_model(model_ref& mdl, unsigned index) {
        if (index >= m_box_models.size()) {
            throw default_exception("index into models is out of bounds");
        }
        mdl = m_box_models[index];
        fix_model(mdl);
    }

    bool context::contains_quantifiers() const {
        for (expr* f : m_hard_constraints) {
            if (has_quantifiers(f)) return true;
        }
        return false;
    }


    lbool context::execute_min_max(unsigned index, bool committed, bool scoped, bool is_max) {
        if (scoped) get_solver().push();            
        lbool result = m_optsmt.lex(index, is_max);
        if (result == l_true) { m_optsmt.get_model(m_model, m_labels); SASSERT(m_model); }
        if (scoped) get_solver().pop(1);        
        if (result == l_true && committed) m_optsmt.commit_assignment(index);
        if (result == l_true && m_optsmt.is_unbounded(index, is_max) && contains_quantifiers()) {
            throw default_exception("unbounded objectives on quantified constraints is not supported");
        }
        return result;
    }
    
    lbool context::execute_maxsat(symbol const& id, bool committed, bool scoped) {
        model_ref tmp;
        maxsmt& ms = *m_maxsmts.find(id);
        if (scoped) get_solver().push();            
        lbool result = ms();
        if (result != l_false && (ms.get_model(tmp, m_labels), tmp.get())) {
            ms.get_model(m_model, m_labels);
        }
        if (scoped) get_solver().pop(1);
        if (result == l_true && committed) ms.commit_assignment();
        DEBUG_CODE(if (result == l_true) validate_maxsat(id););
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
    
    /**
       \brief there is no need to use push/pop when all objectives are maxsat and engine
       is maxres.
    */
    bool context::scoped_lex() {
        if (m_maxsat_engine == symbol("maxres")) {
            for (auto const& o : m_objectives) {
                if (o.m_type != O_MAXSMT) return true;
            }
            return false;
        }
        return true;
    }

    lbool context::execute_lex() {
        lbool r = l_true;
        bool sc = scoped_lex();
        IF_VERBOSE(1, verbose_stream() << "(opt :lex)\n";);
        unsigned sz = m_objectives.size();
        for (unsigned i = 0; r == l_true && i < sz; ++i) {
            objective const& o = m_objectives[i];
            bool is_last = i + 1 == sz;            
            r = execute(o, i + 1 < sz, sc && !is_last);
            if (r == l_true && o.m_type == O_MINIMIZE && !get_lower_as_num(i).is_finite()) {
                return r;
            }
            if (r == l_true && o.m_type == O_MAXIMIZE && !get_upper_as_num(i).is_finite()) {
                return r;
            }
            if (r == l_true && i + 1 < sz) {
                update_lower();
            }
        }
        DEBUG_CODE(if (r == l_true) validate_lex(););
        return r;
    }    

    lbool context::execute_box() {
        if (m_box_index < m_box_models.size()) {
            m_model = m_box_models[m_box_index];
            ++m_box_index;           
            return l_true;
        }
        if (m_box_index < m_objectives.size()) {
            m_model = nullptr;
            ++m_box_index;
            return l_undef;
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
                m_box_models.push_back(m_model.get());
            }
            else {
                m_box_models.push_back(m_optsmt.get_model(j));
                ++j;
            }
        }
        if (r == l_true && !m_box_models.empty()) {
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
        result = mk_not(m, result);
        return result;
    }

    expr_ref context::mk_cmp(bool is_ge, model_ref& mdl, objective const& obj) {
        rational k(0);
        expr_ref val(m), result(m);
        switch (obj.m_type) {
        case O_MINIMIZE:
            is_ge = !is_ge;
        case O_MAXIMIZE:
            val = (*mdl)(obj.m_term);
            if (is_numeral(val, k)) {
                if (is_ge) {
                    result = mk_ge(obj.m_term, val);
                }
                else {
                    result = mk_ge(val, obj.m_term);
                }
            }
            else {
                result = m.mk_true();
            }
            break;
        case O_MAXSMT: {
            pb_util      pb(m);
            unsigned sz = obj.m_terms.size();
            ptr_vector<expr> terms;
            vector<rational> coeffs;
            for (unsigned i = 0; i < sz; ++i) {
                terms.push_back(obj.m_terms[i]);
                coeffs.push_back(obj.m_weights[i]);
                if (mdl->is_true(obj.m_terms[i])) {
                    k += obj.m_weights[i];
                }
                else {
                    TRACE("opt", tout << (*mdl)(obj.m_terms[i]) << "\n";);
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
        SASSERT (m_pareto);
        m_pareto->get_model(m_model, m_labels);
        update_bound(true);
        update_bound(false);
        TRACE("opt", model_smt2_pp(tout, m, *m_model.get(), 0););
    }

    lbool context::execute_pareto() {        
        if (!m_pareto) {
            set_pareto(alloc(gia_pareto, m, *this, m_solver.get(), m_params));
        }
        lbool is_sat = (*(m_pareto.get()))();
        if (is_sat != l_true) {
            set_pareto(nullptr);
        }
        if (is_sat == l_true) {
            yield();
        }
        return is_sat;
    }


    std::string context::reason_unknown() const { 
        if (m.canceled()) {
            return Z3_CANCELED_MSG;
        }
        if (m_solver.get()) {
            return m_solver->reason_unknown();
        }
        return m_unknown;
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
        m_opt_solver = alloc(opt_solver, m, m_params, *m_fm);
        m_opt_solver->set_logic(m_logic);
        m_solver = m_opt_solver.get();
        m_opt_solver->ensure_pb();
    
        //if (opt_params(m_params).priority() == symbol("pareto") ||
        //    (opt_params(m_params).priority() == symbol("lex") && m_objectives.size() > 1)) {
        //}        
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
        if (opt_params(m_params).priority() == symbol("pareto")) {
            return;
        }
        if (m.proofs_enabled()) {
            return;
        }
        m_params.set_bool("minimize_core_partial", true);
        m_params.set_bool("minimize_core", true);
        m_sat_solver = mk_inc_sat_solver(m, m_params);
        expr_ref_vector fmls(m);
        get_solver().get_assertions(fmls);
        m_sat_solver->assert_expr(fmls);
        m_solver = m_sat_solver.get();        
    }

    void context::enable_sls(bool force) {
        if ((force || m_enable_sls) && m_sat_solver.get()) {
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
            for (objective& obj : m_objectives) {
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
            for (expr* f : m_hard_constraints) {
                quick_for_each_expr(proc, visited, f);
            }
        }
        catch (const is_bv::found &) {
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
        catch (const is_propositional_fn::found &) {
            return false;
        }
        return true;
    }


    void context::add_maxsmt(symbol const& id, unsigned index) {
        maxsmt* ms = alloc(maxsmt, *this, index);
        ms->updt_params(m_params);
        m_maxsmts.insert(id, ms);        
    }

    bool context::is_numeral(expr* e, rational & n) const {
        unsigned sz;
        return m_arith.is_numeral(e, n) || m_bv.is_numeral(e, n, sz);
    }

    void context::normalize(expr_ref_vector const& asms) {
        expr_ref_vector fmls(m);
        to_fmls(fmls);
        simplify_fmls(fmls, asms);
        from_fmls(fmls);
    }

    void context::simplify_fmls(expr_ref_vector& fmls, expr_ref_vector const& asms) {
        if (m_is_clausal) {
            return;
        }

        goal_ref g(alloc(goal, m, true, !asms.empty()));
        for (expr* fml : fmls) {
            g->assert_expr(fml);
        }
        for (expr * a : asms) {
            g->assert_expr(a, a);
        }
        tactic_ref tac0 = 
            and_then(mk_simplify_tactic(m, m_params), 
                     mk_propagate_values_tactic(m),
                     mk_solve_eqs_tactic(m),
                     // NB: cannot ackermannize because max/min objectives would disappear
                     // mk_ackermannize_bv_tactic(m, m_params), 
                     // NB: mk_elim_uncstr_tactic(m) is not sound with soft constraints
                     mk_simplify_tactic(m));   
        opt_params optp(m_params);
        tactic_ref tac1, tac2, tac3, tac4;
        if (optp.elim_01()) {
            tac1 = mk_dt2bv_tactic(m);
            tac2 = mk_lia2card_tactic(m);
            tac3 = mk_eq2bv_tactic(m);
            params_ref lia_p;
            lia_p.set_bool("compile_equality", optp.pb_compile_equality());
            tac2->updt_params(lia_p);
            set_simplify(and_then(tac0.get(), tac1.get(), tac2.get(), tac3.get(), mk_simplify_tactic(m)));
        }
        else {
            set_simplify(tac0.get());
        }
        goal_ref_buffer result;
        TRACE("opt", g->display(tout););
        (*m_simplify)(g, result); 
        SASSERT(result.size() == 1);
        goal* r = result[0];
        m_model_converter = r->mc();
        fmls.reset();
        expr_ref tmp(m);
        for (unsigned i = 0; i < r->size(); ++i) {
            if (asms.empty()) {
                fmls.push_back(r->form(i));
                continue;
            }

            ptr_vector<expr> deps;
            expr_dependency_ref core(r->dep(i), m);
            m.linearize(core, deps);
            if (!deps.empty()) {
                fmls.push_back(m.mk_implies(m.mk_and(deps.size(), deps.c_ptr()), r->form(i)));
            }
            else {
                fmls.push_back(r->form(i));
            }
        }        
        if (r->inconsistent()) {
            ptr_vector<expr> core_elems;
            expr_dependency_ref core(r->dep(0), m);
            m.linearize(core, core_elems);
            m_core.append(core_elems.size(), core_elems.c_ptr());
        }
    }

    bool context::is_maximize(expr* fml, app_ref& term, expr_ref& orig_term, unsigned& index) {
        if (is_app(fml) && m_objective_fns.find(to_app(fml)->get_decl(), index) && 
            m_objectives[index].m_type == O_MAXIMIZE) {
            term = to_app(to_app(fml)->get_arg(0));
            orig_term = m_objective_orig.find(to_app(fml)->get_decl());
            return true;
        }
        return false;
    }

    bool context::is_minimize(expr* fml, app_ref& term, expr_ref& orig_term, unsigned& index) {
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
                            bool& neg, symbol& id, expr_ref& orig_term, unsigned& index) {
        if (!is_app(fml)) return false;
        neg = false;
        orig_term = nullptr;
        index = 0;
        app* a = to_app(fml);
        
        if (m_objective_fns.find(a->get_decl(), index) && m_objectives[index].m_type == O_MAXSMT) {
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr_ref arg(a->get_arg(i), m);
                rational weight = m_objectives[index].m_weights[i];
                if (weight.is_neg()) {
                    weight.neg();
                    arg = mk_not(m, arg);
                    offset -= weight;
                }
                if (m.is_true(arg)) {
                    IF_VERBOSE(5, verbose_stream() << weight << ": " << mk_pp(m_objectives[index].m_terms[i].get(), m) << " |-> true\n";);
                }
                else if (weight.is_zero()) {
                    // skip
                }
                else if (m.is_false(arg)) {
                    IF_VERBOSE(5, verbose_stream() << weight << ": " << mk_pp(m_objectives[index].m_terms[i].get(), m) << " |-> false\n";);
                    offset += weight;
                }
                else {
                    terms.push_back(arg);
                    weights.push_back(weight);
                }
            } 
            id = m_objectives[index].m_id;
            return true;
        }
        app_ref term(m);
        offset = rational::zero();
        bool is_max = is_maximize(fml, term, orig_term, index);
        bool is_min = !is_max && is_minimize(fml, term, orig_term, index);
        if (is_min && get_pb_sum(term, terms, weights, offset)) {
            TRACE("opt", tout << "try to convert minimization\n" << mk_pp(term, m) << "\n";);
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
                    terms[i] = mk_not(m, terms[i].get());
                }
            }
            TRACE("opt", 
                  tout << "Convert minimization " << orig_term << "\n";
                  tout << "to maxsat: " << term << "\n";
                  for (unsigned i = 0; i < weights.size(); ++i) {
                      tout << mk_pp(terms[i].get(), m) << ": " << weights[i] << "\n";
                  }
                  tout << "offset: " << offset << "\n";
                  );
            std::ostringstream out;
            out << orig_term << ":" << index;
            id = symbol(out.str().c_str());
            return true;
        }
        if (is_max && get_pb_sum(term, terms, weights, offset)) {
            TRACE("opt", tout << "try to convert maximization " << mk_pp(term, m) << "\n";);
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
                    terms[i] = mk_not(m, terms[i].get());
                }
                offset += weights[i];
            }
            neg = true;
            std::ostringstream out;
            out << orig_term << ":" << index;
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
            out << orig_term << ":" << index;
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
        m_objective_orig.insert(f, sz > 0 ? args[0] : nullptr);
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
        TRACE("opt", tout << fmls << "\n";);
        m_hard_constraints.reset();
        for (expr * fml : fmls) {
            app_ref tr(m);
            expr_ref orig_term(m);
            expr_ref_vector terms(m);
            vector<rational> weights;
            rational offset(0);
            unsigned index = 0;
            symbol id;
            bool neg;
            if (is_maxsat(fml, terms, weights, offset, neg, id, orig_term, index)) {
                objective& obj = m_objectives[index];

                if (obj.m_type != O_MAXSMT) {
                    // change from maximize/minimize.
                    obj.m_id = id;
                    obj.m_type = O_MAXSMT;
                    SASSERT(!m_maxsmts.contains(id));
                    add_maxsmt(id, index);
                }
                mk_atomic(terms);
                SASSERT(obj.m_id == id);
                obj.m_term = orig_term?to_app(orig_term):nullptr;
                obj.m_terms.reset();
                obj.m_terms.append(terms);
                obj.m_weights.reset();
                obj.m_weights.append(weights);
                obj.m_adjust_value.set_offset(offset);
                obj.m_adjust_value.set_negate(neg);
                m_maxsmts.find(id)->set_adjust_value(obj.m_adjust_value);
                TRACE("opt", tout << "maxsat: " << id << " offset:" << offset << "\n";
                      tout << terms << "\n";);
            }
            else if (is_maximize(fml, tr, orig_term, index)) {
                purify(tr);
                m_objectives[index].m_term = tr;
            }
            else if (is_minimize(fml, tr, orig_term, index)) {
                purify(tr);
                m_objectives[index].m_term = tr;
                m_objectives[index].m_adjust_value.set_negate(true);
            }
            else {
                m_hard_constraints.push_back(fml);
            }
        }
        // fix types of objectives:
        for (objective & obj : m_objectives) {
            expr* t = obj.m_term;
            switch(obj.m_type) {
            case O_MINIMIZE:
            case O_MAXIMIZE:
                if (!m_arith.is_int(t) && !m_arith.is_real(t)) {
                    obj.m_term = m_arith.mk_numeral(rational(0), true);
                }
                break;
            default:
                break;
            }
        }
    }


    void context::model_updated(model* md) {
        model_ref mdl = md;
        set_model(mdl);
#if 0
        opt_params optp(m_params);
        symbol prefix = optp.solution_prefix();
        if (prefix == symbol::null || prefix == symbol("")) return;        
        model_ref mdl = md->copy();
        fix_model(mdl);
        std::ostringstream buffer;
        buffer << prefix << (m_model_counter++) << ".smt2";
        std::ofstream out(buffer.str());        
        if (out) {
            out << *mdl;
            out.close();
        }
#endif
    }


    bool context::verify_model(unsigned index, model* md, rational const& _v) {
        rational r;
        app_ref term = m_objectives[index].m_term;
        if (!term) {
            return true;
        }
        rational v = m_objectives[index].m_adjust_value(_v);
        expr_ref val(m);
        model_ref mdl = md->copy();
        fix_model(mdl);
        val = (*mdl)(term);
        unsigned bvsz;
        if (!m_arith.is_numeral(val, r) && !m_bv.is_numeral(val, r, bvsz)) {
            TRACE("opt", tout << "model does not evaluate objective to a value but instead " << val << "\n";
                  tout << *mdl << "\n";
                  );
            return false;
        }
        if (r != v) {
            TRACE("opt", tout << "Out of bounds: " << term << " " << val << " != " << v << "\n";);
            return false;
        }
        else {
            TRACE("opt", tout << "validated: " << term << " = " << val << "\n";);
        }
        return true;
    }

    void context::purify(app_ref& term) {
        generic_model_converter_ref fm;
        if (m_arith.is_add(term)) {
            expr_ref_vector args(m);
            for (expr* arg : *term) {
                if (is_mul_const(arg)) {
                    args.push_back(arg);
                }
                else {
                    args.push_back(purify(fm, arg));
                }
            }
            term = m_arith.mk_add(args.size(), args.c_ptr());
        }
        else if (m.is_ite(term) || !is_mul_const(term)) {
            TRACE("opt", tout << "Purifying " << term << "\n";);
            term = purify(fm, term);
        }
        if (fm) {
            m_model_converter = concat(m_model_converter.get(), fm.get());
        }
    }

    bool context::is_mul_const(expr* e) {
        expr* e1, *e2;
        return 
            is_uninterp_const(e) ||
            m_arith.is_numeral(e) ||
            (m_arith.is_mul(e, e1, e2) && m_arith.is_numeral(e1) && is_uninterp_const(e2)) ||
            (m_arith.is_mul(e, e2, e1) && m_arith.is_numeral(e1) && is_uninterp_const(e2));
    }

    app* context::purify(generic_model_converter_ref& fm, expr* term) {
       std::ostringstream out;
       out << mk_pp(term, m);
       app* q = m.mk_fresh_const(out.str(), m.get_sort(term));
       if (!fm) fm = alloc(generic_model_converter, m, "opt");
       if (m_arith.is_int_real(term)) {
           m_hard_constraints.push_back(m_arith.mk_ge(q, term));
           m_hard_constraints.push_back(m_arith.mk_le(q, term));
       }
       else {
           m_hard_constraints.push_back(m.mk_eq(q, term));
       }
       fm->hide(q);
       return q;
    }

    /**
       To select the proper theory solver we have to ensure that all theory 
       symbols from soft constraints are reflected in the hard constraints.

       - filter "obj" from generated model.
     */
    void context::mk_atomic(expr_ref_vector& terms) {
        generic_model_converter_ref fm;
        for (unsigned i = 0; i < terms.size(); ++i) {
            expr_ref p(terms[i].get(), m);
            app_ref q(m);
            if (is_propositional(p)) {
                terms[i] = p;
            }
            else {
                terms[i] = purify(fm, p);
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
        TRACE("opt", tout << fmls << "\n";);
    }

    void context::internalize() {
        for (objective & obj : m_objectives) {
            switch(obj.m_type) {
            case O_MINIMIZE: {
                app_ref tmp(m);
                tmp = obj.m_term;
                if (m_arith.is_int(tmp) || m_arith.is_real(tmp)) {
                    tmp = m_arith.mk_uminus(obj.m_term);
                }
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
        for (objective const& obj : m_objectives) {
            rational r;
            switch(obj.m_type) {
            case O_MINIMIZE: {
                val = (*m_model)(obj.m_term);
                TRACE("opt", tout << obj.m_term << " " << val << "\n";);
                if (is_numeral(val, r)) {
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
                val = (*m_model)(obj.m_term);
                TRACE("opt", tout << obj.m_term << " " << val << "\n";);
                if (is_numeral(val, r)) {
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
                    val = (*m_model)(obj.m_terms[j]);
                    TRACE("opt", tout << mk_pp(obj.m_terms[j], m) << " " << val << "\n";);
                    if (!m.is_true(val)) {
                        r += obj.m_weights[j];
                    }
                }
                if (ok) {
                    maxsmt& ms = *m_maxsmts.find(obj.m_id);
                    if (is_lower) {
                        ms.update_upper(r);
                        TRACE("opt", tout << "update upper from " << r << " to " << ms.get_upper() << "\n";);                        
                    }
                    else {
                        ms.update_lower(r);
                        TRACE("opt", tout << "update lower from " << r << " to " << ms.get_lower() << "\n";);                        
                    }
                }
                break;
            }
            }
        }
    }

    void context::display_benchmark() {
        display(verbose_stream());
        return;

        if (opt_params(m_params).dump_benchmarks() && 
            sat_enabled() && 
            m_objectives.size() == 1 &&
            m_objectives[0].m_type == O_MAXSMT
            ) {
            objective& o = m_objectives[0];
            unsigned sz = o.m_terms.size();
            inc_sat_display(verbose_stream(), get_solver(), sz, o.m_terms.c_ptr(), o.m_weights.c_ptr());
        }

        
    }

    void context::display(std::ostream& out) {
        display_assignment(out);
    }

    void context::display_assignment(std::ostream& out) {
        if (m_scoped_state.m_objectives.size() != m_objectives.size()) {
            throw default_exception("check-sat has not been called with latest objectives");
        }
        out << "(objectives\n";
        for (unsigned i = 0; i < m_scoped_state.m_objectives.size(); ++i) {
            objective const& obj = m_scoped_state.m_objectives[i];
            out << " (";
            display_objective(out, obj);
            if (get_lower_as_num(i) != get_upper_as_num(i)) {
                out << "  (interval " << get_lower(i) << " " << get_upper(i) << ")";
            }
            else {
                out << " " << get_lower(i);
            }
            out << ")\n";
        }
        out << ")\n";
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
        if (idx >= m_objectives.size()) {
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
        if (idx >= m_objectives.size()) {
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

    void context::to_exprs(inf_eps const& n, expr_ref_vector& es) {
        rational inf = n.get_infinity();
        rational r   = n.get_rational();
        rational eps = n.get_infinitesimal();
        es.push_back(m_arith.mk_numeral(inf, inf.is_int()));
        es.push_back(m_arith.mk_numeral(r, r.is_int()));
        es.push_back(m_arith.mk_numeral(eps, eps.is_int()));
    }

    expr_ref context::to_expr(inf_eps const& n) {
        rational inf = n.get_infinity();
        rational r   = n.get_rational();
        rational eps = n.get_infinitesimal();
        expr_ref_vector args(m);
        bool is_int = eps.is_zero() && r.is_int();
        if (!inf.is_zero()) {
            expr* oo = m.mk_const(symbol("oo"), is_int ? m_arith.mk_int() : m_arith.mk_real());
            if (inf.is_one()) {
                args.push_back(oo);
            }
            else {
                args.push_back(m_arith.mk_mul(m_arith.mk_numeral(inf, is_int), oo));
            }
        }
        if (!r.is_zero()) {
            args.push_back(m_arith.mk_numeral(r, is_int));
        }
        if (!eps.is_zero()) {
            expr* ep = m.mk_const(symbol("epsilon"), m_arith.mk_real());
            if (eps.is_one()) {
                args.push_back(ep);
            }
            else {
                args.push_back(m_arith.mk_mul(m_arith.mk_numeral(eps, is_int), ep));
            }
        }
        switch(args.size()) {
        case 0: return expr_ref(m_arith.mk_numeral(rational(0), true), m);
        case 1: return expr_ref(args[0].get(), m);
        default: return expr_ref(m_arith.mk_add(args.size(), args.c_ptr()), m);
        }
    }
       
    void context::set_simplify(tactic* tac) {
        m_simplify = tac;        
    }

    void context::clear_state() {
        m_pareto = nullptr;
        m_box_index = UINT_MAX;
        m_model.reset();
        m_model_fixed.reset();
        m_core.reset();
    }

    void context::set_pareto(pareto_base* p) {
        m_pareto = p;        
        m_pareto1 = p != nullptr;
    }

    void context::collect_statistics(statistics& stats) const {
        if (m_solver) {
            m_solver->collect_statistics(stats);
        }
        if (m_simplify) {
            m_simplify->collect_statistics(stats);
        }
        for (auto const& kv : m_maxsmts) {
            kv.m_value->collect_statistics(stats);
        }        
        get_memory_statistics(stats);
        get_rlimit_statistics(m.limit(), stats);
        if (m_qmax) {
            m_qmax->collect_statistics(stats);
        }
    }

    void context::collect_param_descrs(param_descrs & r) {
        opt_params::collect_param_descrs(r);
        insert_timeout(r);
        insert_ctrl_c(r);
    }
    
    void context::updt_params(params_ref const& p) {
        m_params.append(p);
        if (m_solver) {
            m_solver->updt_params(m_params);
        }
        if (m_sat_solver) {
            m_sat_solver->updt_params(m_params);
        }
        m_optsmt.updt_params(m_params);
        for (auto & kv : m_maxsmts) {
            kv.m_value->updt_params(m_params);
        }
        opt_params _p(p);
        m_enable_sat = _p.enable_sat();
        m_enable_sls = _p.enable_sls();
        m_maxsat_engine = _p.maxsat_engine();
        m_pp_neat = _p.pp_neat();
    }

    std::string context::to_string() const {
        return to_string(false, m_scoped_state.m_hard, m_scoped_state.m_objectives);
    }

    std::string context::to_string_internal() const {
        return to_string(true, m_hard_constraints, m_objectives);
    }

    std::string context::to_string(bool is_internal, expr_ref_vector const& hard, vector<objective> const& objectives) const {
        smt2_pp_environment_dbg env(m);
        ast_pp_util visitor(m);
        std::ostringstream out;
        visitor.collect(hard);
        model_converter_ref mc = concat(m_model_converter.get(), m_fm.get());
                
        for (objective const& obj : objectives) {
            switch(obj.m_type) {
            case O_MAXIMIZE: 
            case O_MINIMIZE:
                visitor.collect(obj.m_term);
                break;
            case O_MAXSMT: 
                visitor.collect(obj.m_terms);
                break;
            default: 
                UNREACHABLE();
                break;
            }
        }

        if (is_internal && mc) { 
            mc->set_env(&visitor); 
        }

        param_descrs descrs;
        collect_param_descrs(descrs);
        m_params.display_smt2(out, "opt", descrs);
        visitor.display_decls(out);
        visitor.display_asserts(out, hard, m_pp_neat);
        for (objective const& obj : objectives) {
            switch(obj.m_type) {
            case O_MAXIMIZE: 
                out << "(maximize ";
                ast_smt2_pp(out, obj.m_term, env);
                out << ")\n";
                break;
            case O_MINIMIZE:
                out << "(minimize ";
                ast_smt2_pp(out, obj.m_term, env);
                out << ")\n";
                break;
            case O_MAXSMT: 
                for (unsigned j = 0; j < obj.m_terms.size(); ++j) {
                    out << "(assert-soft ";
                    ast_smt2_pp(out, obj.m_terms[j], env);
                    rational w = obj.m_weights[j];
                    
                    w.display_decimal(out << " :weight ", 3, true);
                    if (obj.m_id != symbol::null) {
                        if (is_smt2_quoted_symbol(obj.m_id)) {
                            out << " :id " << mk_smt2_quoted_symbol(obj.m_id);
                        }
                        else {
                            out << " :id " << obj.m_id;
                        }
                    }
                    out << ")\n";
                }
                break;
            default: 
                UNREACHABLE();
                break;
            }
        }        
        if (is_internal && mc) {
            mc->display(out);
        }
        if (is_internal && mc) { 
            mc->set_env(nullptr);
        }       
        out << "(check-sat)\n"; 
        return out.str();
    }

    void context::validate_model() {
        return;
        if (!gparams::get_ref().get_bool("model_validate", false)) return;
        expr_ref_vector fmls(m);
        get_hard_constraints(fmls);
        expr_ref tmp(m);
        model_ref mdl;
        get_model(mdl);
        mdl->set_model_completion(true);
        for (expr * f : fmls) {
            if (!mdl->is_true(f)) {
                IF_VERBOSE(0, 
                           verbose_stream() << "Failed to validate " << mk_pp(f, m) << "\n" << tmp << "\n";
                           m_fm->display(verbose_stream() << "fm\n");
                           m_model_converter->display(verbose_stream() << "mc\n");
                           model_smt2_pp(verbose_stream(), m, *mdl, 0);
                           verbose_stream() << to_string_internal() << "\n");
            }
        }
    }

    void context::validate_maxsat(symbol const& id) {
        maxsmt& ms = *m_maxsmts.find(id);
        TRACE("opt", tout << "Validate: " << id << "\n";);
        for (objective const& obj : m_objectives) {
            if (obj.m_id == id && obj.m_type == O_MAXSMT) {        
                SASSERT(obj.m_type == O_MAXSMT);
                rational value(0);
                expr_ref val(m);
                for (unsigned i = 0; i < obj.m_terms.size(); ++i) {
                    auto const& t = obj.m_terms[i];
                    if (!m_model->is_true(t)) {
                        value += obj.m_weights[i];
                    }
                    // TBD: check that optimal was not changed.
                }
                value = obj.m_adjust_value(value);
                rational value0 = ms.get_lower();
                TRACE("opt", tout << "value " << value << " " << value0 << "\n";);
                // TBD is this correct? SASSERT(value == value0);
            }
        }
    }

    void context::validate_lex() {
        rational r1;
        expr_ref val(m);
        SASSERT(m_model);
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE:
            case O_MAXIMIZE: {
                inf_eps n = m_optsmt.get_lower(obj.m_index);
                if (m_optsmt.objective_is_model_valid(obj.m_index) && 
                    n.get_infinity().is_zero() &&
                    n.get_infinitesimal().is_zero() &&
                    is_numeral((*m_model)(obj.m_term), r1)) {
                    rational r2 = n.get_rational();
                    if (obj.m_type == O_MINIMIZE) {
                        r1.neg();
                    }
                    CTRACE("opt", r1 != r2, tout << obj.m_term << " evaluates to " << r1 << " but has objective " << r2 << "\n";);
                    CTRACE("opt", r1 != r2, tout << *m_model;);
                    SASSERT(r1 == r2);
                }
                break;
            }
            case O_MAXSMT: {
                rational value(0);
                for (unsigned i = 0; i < obj.m_terms.size(); ++i) {
                    if (!m_model->is_true(obj.m_terms[i])) {
                        value += obj.m_weights[i];
                    }
                    // TBD: check that optimal was not changed.
                }
                maxsmt& ms = *m_maxsmts.find(obj.m_id);
                rational value0 = ms.get_lower();
                TRACE("opt", tout << "value " << value << " other " << value0 << "\n";);
                // TBD SASSERT(value0 == value);
                break;
            }
            }       
        } 
    }

    bool context::is_qsat_opt() {
        if (m_objectives.size() != 1) {
            return false;
        }
        if (m_objectives[0].m_type != O_MAXIMIZE && 
            m_objectives[0].m_type != O_MINIMIZE) {
            return false;
        }
        if (!m_arith.is_real(m_objectives[0].m_term)) {
            return false;
        }
        for (expr* fml : m_hard_constraints) {
            if (has_quantifiers(fml)) {
                return true;
            }
        }
        return false;
    }

    lbool context::run_qsat_opt() {
        SASSERT(is_qsat_opt());
        objective const& obj = m_objectives[0];
        app_ref term(obj.m_term);
        if (obj.m_type == O_MINIMIZE) {
            term = m_arith.mk_uminus(term);
        }
        inf_eps value;
        m_qmax = alloc(qe::qmax, m, m_params);
        lbool result = (*m_qmax)(m_hard_constraints, term, value, m_model);
        if (result != l_undef && obj.m_type == O_MINIMIZE) {
            value.neg();
        }
        m_optsmt.setup(*m_opt_solver.get());
        if (result == l_undef) {
            if (obj.m_type == O_MINIMIZE) {
                m_optsmt.update_upper(obj.m_index, value);
            }
            else {
                m_optsmt.update_lower(obj.m_index, value);
            }
        }
        else {
            m_optsmt.update_lower(obj.m_index, value);
            m_optsmt.update_upper(obj.m_index, value);
        }
        return result;
    }
}
