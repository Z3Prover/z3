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
#include "arith_decl_plugin.h"
#include "for_each_expr.h"
#include "goal.h"
#include "tactic.h"
#include "lia2card_tactic.h"
#include "elim01_tactic.h"
#include "tactical.h"

namespace opt {

    context::context(ast_manager& m):
        m(m),
        m_hard_constraints(m),
        m_optsmt(m)
    {
        m_params.set_bool("model", true);
        m_params.set_bool("unsat_core", true);
        m_solver = alloc(opt_solver, m, m_params, symbol());
    }

    context::~context() {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
    }

    unsigned context::add_soft_constraint(expr* f, rational const& w, symbol const& id) { 
        maxsmt* ms;
        if (!m_maxsmts.find(id, ms)) {
            ms = alloc(maxsmt, m);
            m_maxsmts.insert(id, ms);
            m_objectives.push_back(objective(m, id));
            m_indices.insert(id, m_objectives.size() - 1);
        }
        SASSERT(m_indices.contains(id));        
        unsigned idx = m_indices[id];
        m_objectives[idx].m_terms.push_back(f);
        m_objectives[idx].m_weights.push_back(w);
        return idx;
    }

    unsigned context::add_objective(app* t, bool is_max) {
        app_ref tr(t, m);
        unsigned index = m_objectives.size();
        m_objectives.push_back(objective(is_max, tr, index));
        return index;
    }

    lbool context::optimize() {
        opt_solver& s = get_solver();        
        normalize();
        internalize();
        solver::scoped_push _sp(s);
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }

        lbool is_sat = s.check_sat_core(0,0);
        if (is_sat != l_true) {
            m_model = 0;
            return is_sat;
        }
        s.get_model(m_model);
        update_lower();
        switch (m_objectives.size()) {
        case 0:
            return is_sat;
        case 1:
            return execute(m_objectives[0], false);
        default: {
            symbol pri = m_params.get_sym("priority", symbol("lex"));
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

    void context::get_model(model_ref& mdl) {
        mdl = m_model;
    }

    lbool context::execute_min_max(unsigned index, bool committed, bool is_max) {
        // HACK: reuse m_optsmt without regard for box reuse and not considering
        // use-case of lex.
        lbool result = m_optsmt(get_solver());
        if (committed) m_optsmt.commit_assignment(index);
        return result;
    }


    lbool context::execute_maxsat(symbol const& id, bool committed) {
        maxsmt& ms = *m_maxsmts.find(id);
        lbool result = ms(get_solver());
        if (committed) ms.commit_assignment();
        return result;
    }

    lbool context::execute(objective const& obj, bool committed) {
        switch(obj.m_type) {
        case O_MAXIMIZE: return execute_min_max(obj.m_index, committed, true);
        case O_MINIMIZE: return execute_min_max(obj.m_index, committed, false);
        case O_MAXSMT: return execute_maxsat(obj.m_id, committed);
        default: UNREACHABLE(); return l_undef;
        }
    }
    
    lbool context::execute_lex() {
        lbool r = l_true;
        for (unsigned i = 0; r == l_true && i < m_objectives.size(); ++i) {
            r = execute(m_objectives[i], i + 1 < m_objectives.size());
        }
        return r;
    }    

    lbool context::execute_box() {
        lbool r = l_true;
        for (unsigned i = 0; r == l_true && i < m_objectives.size(); ++i) {
            get_solver().push();
            r = execute(m_objectives[i], false);
            get_solver().pop(1);
        }
        return r;
    }

    lbool context::execute_pareto() {
        // TODO: record a stream of results from pareto front
        return execute_lex();
    }

    opt_solver& context::get_solver() { 
        return *m_solver.get(); 
    }

    void context::normalize() {
        expr_ref_vector fmls(m);
        to_fmls(fmls);
        simplify_fmls(fmls);
        from_fmls(fmls);
    }

    void context::simplify_fmls(expr_ref_vector& fmls) {
        goal_ref g(alloc(goal, m, true, false));
        for (unsigned i = 0; i < fmls.size(); ++i) {
            g->assert_expr(fmls[i].get());
        }
        tactic_ref tac1 = mk_elim01_tactic(m);
        tactic_ref tac2 = mk_lia2card_tactic(m);
        tactic_ref tac  = and_then(tac1.get(), tac2.get());
        model_converter_ref mc;  // TBD: expose model converter upwards and apply to returned model.
        proof_converter_ref pc;
        expr_dependency_ref core(m);
        goal_ref_buffer result;
        (*tac)(g, result, mc, pc, core);   // TBD: have this an attribute so we can cancel.
        SASSERT(result.size() == 1);
        goal* r = result[0];
        fmls.reset();
        for (unsigned i = 0; i < r->size(); ++i) {
            fmls.push_back(r->form(i));
        }        
    }

    bool context::is_maximize(expr* fml, app_ref& term, unsigned& index) {
        if (is_app(fml) && m_objective_fns.find(to_app(fml)->get_decl(), index) && 
            m_objectives[index].m_type == O_MAXIMIZE) {
            term = to_app(to_app(fml)->get_arg(0));
            return true;
        }
        return false;
    }

    bool context::is_minimize(expr* fml, app_ref& term, unsigned& index) {
        if (is_app(fml) && m_objective_fns.find(to_app(fml)->get_decl(), index) && 
            m_objectives[index].m_type == O_MINIMIZE) {
            term = to_app(to_app(fml)->get_arg(0));
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
            terms.append(a->get_num_args(), a->get_args());
            weights.append(m_objectives[index].m_weights);
            id = m_objectives[index].m_id;
            return true;
        }
        app_ref term(m);
        offset = rational::zero();
        if (is_minimize(fml, term, index) &&
            get_pb_sum(term, terms, weights, offset)) {
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
            return true;
        }
        if (is_maximize(fml, term, index) &&
            get_pb_sum(term, terms, weights, offset)) {
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
        m_hard_constraints.reset();
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls[i];
            app_ref tr(m);
            expr_ref_vector terms(m);
            vector<rational> weights;
            rational offset;
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
                    maxsmt* ms = alloc(maxsmt, m);
                    m_maxsmts.insert(id, ms);
                    m_indices.insert(id, index);
                }
                SASSERT(obj.m_id == id);
                obj.m_terms.reset();
                obj.m_terms.append(terms);
                obj.m_offset = offset;
                obj.m_neg = neg;
                TRACE("opt", tout << "maxsat: " << id << " offset:" << offset << "\n";);
            }
            else if (is_maximize(fml, tr, index)) {
                m_objectives[index].m_term = tr;
            }
            else if (is_minimize(fml, tr, index)) {
                m_objectives[index].m_term = tr;
            }
            else {
                m_hard_constraints.push_back(fml);
            }
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
    }

    void context::internalize() {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective & obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE:
                obj.m_index = m_optsmt.get_num_objectives();
                m_optsmt.add(obj.m_term, false);
                break;
            case O_MAXIMIZE:
                obj.m_index = m_optsmt.get_num_objectives();
                m_optsmt.add(obj.m_term, true);
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

    void context::update_lower() {
        arith_util a(m);
        expr_ref val(m);
        rational r(0);
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MINIMIZE:
            case O_MAXIMIZE:
                if (m_model->eval(obj.m_term, val) && a.is_numeral(val, r)) {
                    m_optsmt.update_lower(obj.m_index, r);
                }
                break;
            case O_MAXSMT: {
                bool ok = true;
                for (unsigned j = 0; ok && j < obj.m_terms.size(); ++j) {
                    if (m_model->eval(obj.m_terms[j], val)) {
                        if (!m.is_true(val)) {
                            r += obj.m_weights[j];
                        }
                    }
                    else {
                        ok = false;
                    }
                }
                if (ok) {
                    m_maxsmts.find(obj.m_id)->update_lower(r);
                }
                break;
            }
            }
        }
    }

    void context::display_assignment(std::ostream& out) {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            display_objective(out, obj);
            out << get_upper(i) << "\n";
        }
    }

    void context::display_range_assignment(std::ostream& out) {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {            
            objective const& obj = m_objectives[i];
            display_objective(out, obj);
            out << " [" << get_lower(i) << ":" << get_upper(i) << "]\n";
        }
    }

    void context::display_objective(std::ostream& out, objective const& obj) const {
        switch(obj.m_type) {
        case O_MAXSMT: {
            symbol s = obj.m_id;
            if (s != symbol::null) {
                out << s << " : ";
            }
            break;
        }
        default:
            out << obj.m_term << " ";
            break;
        }
    }


    expr_ref context::get_lower(unsigned idx) {
        if (idx > m_objectives.size()) {
            throw default_exception("index out of bounds"); 
        }
        objective const& obj = m_objectives[idx];
        switch(obj.m_type) {
        case O_MAXSMT: {
            rational r = m_maxsmts.find(obj.m_id)->get_lower();
            if (obj.m_neg) r.neg();
            r += obj.m_offset;
            return to_expr(inf_eps(r));
        }
        case O_MINIMIZE:
        case O_MAXIMIZE: 
            return to_expr(m_optsmt.get_lower(obj.m_index));
        default:
            UNREACHABLE();
            return expr_ref(m);
        }
    }

    expr_ref context::get_upper(unsigned idx) {
        if (idx > m_objectives.size()) {
            throw default_exception("index out of bounds"); 
        }
        objective const& obj = m_objectives[idx];
        switch(obj.m_type) {
        case O_MAXSMT: {
            rational r = m_maxsmts.find(obj.m_id)->get_upper();
            if (obj.m_neg) r.neg();
            r += obj.m_offset;
            return to_expr(inf_eps(r));
        }
        case O_MINIMIZE:
        case O_MAXIMIZE: 
            return to_expr(m_optsmt.get_upper(obj.m_index));
        default:
            UNREACHABLE();
            return expr_ref(m);
        }
    }

    expr_ref context::to_expr(inf_eps const& n) {
        rational inf = n.get_infinity();
        rational r   = n.get_rational();
        rational eps = n.get_infinitesimal();
        expr_ref_vector args(m);
        arith_util a(m);
        if (!inf.is_zero()) {
            args.push_back(a.mk_mul(a.mk_numeral(inf, inf.is_int()), m.mk_const(symbol("oo"), a.mk_int())));
        }
        if (!r.is_zero()) {
            args.push_back(a.mk_numeral(r, r.is_int()));
        }
        if (!eps.is_zero()) {
            args.push_back(a.mk_mul(a.mk_numeral(eps, eps.is_int()), m.mk_const(symbol("epsilon"), a.mk_int())));
        }
        switch(args.size()) {
        case 0: return expr_ref(a.mk_numeral(rational(0), true), m);
        case 1: return expr_ref(args[0].get(), m);
        default: return expr_ref(a.mk_add(args.size(), args.c_ptr()), m);
        }
    }
        
    void context::set_cancel(bool f) {
        if (m_solver) {
            m_solver->set_cancel(f);
        }
        m_optsmt.set_cancel(f);
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            it->m_value->set_cancel(f);
        }
    }

    void context::collect_statistics(statistics& stats) const {
        if (m_solver) {
            m_solver->collect_statistics(stats);
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
        free_func_visitor visitor(m);
        std::ostringstream out;
#define PP(_e_) ast_smt2_pp(out, _e_, env);
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            visitor.collect(m_hard_constraints[i]);
        }
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
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
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            out << "(assert ";
            PP(m_hard_constraints[i]);
            out << ")\n";
        }
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
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
        out << "(optimize)\n"; 
        return out.str();
    }

}
