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

    void context::add_soft_constraint(expr* f, rational const& w, symbol const& id) { 
        maxsmt* ms;
        if (!m_maxsmts.find(id, ms)) {
            ms = alloc(maxsmt, m);
            m_maxsmts.insert(id, ms);
            m_objectives.push_back(objective(m, id));
        }
        ms->add(f, w);
    }

    void context::add_objective(app* t, bool is_max) {
        app_ref tr(t, m);
        unsigned index = m_optsmt.get_num_objectives();
        m_optsmt.add(t, is_max);
        m_objectives.push_back(objective(is_max, tr, index));
    }

    lbool context::optimize() {
        opt_solver& s = get_solver();
        solver::scoped_push _sp(s);
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }

        if (m_objectives.size() == 1) {
            return execute(m_objectives[0], false);
        }

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
            push();
            r = execute(m_objectives[i], false);
            pop(1);
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

    void context::push() {
        get_solver().push();
    }

    void context::pop(unsigned sz) {
        get_solver().pop(sz);
    }

    void context::display_assignment(std::ostream& out) {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MAXSMT: {
                symbol s = obj.m_id;
                if (s != symbol::null) {
                    out << s << " : ";
                }
                maxsmt* ms = m_maxsmts.find(s);
                out << ms->get_value() << "\n";
                break;
            }
            default:
                break;
            }
        }
        m_optsmt.display_assignment(out);
    }

    void context::display_range_assignment(std::ostream& out) {
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            switch(obj.m_type) {
            case O_MAXSMT: {
                symbol s = obj.m_id;
                if (s != symbol::null) {
                    out << s << " : ";
                }
                maxsmt* ms = m_maxsmts.find(s);
                out << "[" << ms->get_lower() << ":" << ms->get_upper() << "]\n";
                break;
            }
            default:
                break;
            }
        }
        m_optsmt.display_range_assignment(out);
    }

    expr_ref context::get_lower(unsigned idx) {
        if (idx > m_objectives.size()) {
            throw default_exception("index out of bounds"); 
        }
        objective const& obj = m_objectives[idx];
        switch(obj.m_type) {
        case O_MAXSMT: 
            return to_expr(m_maxsmts.find(obj.m_id)->get_lower());
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
        case O_MAXSMT: 
            return to_expr(m_maxsmts.find(obj.m_id)->get_upper());
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

}
