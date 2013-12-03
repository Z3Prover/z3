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

namespace opt {

    context::context(ast_manager& m):
        m(m),
        m_hard_constraints(m),
        m_optsmt(m),
        m_objs(m),
        m_obj_util(m)
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
        }
        ms->add(f, w);
    }

    lbool context::execute(expr* _obj, bool committed) {
        SASSERT(is_app(_obj));
        app* obj = to_app(_obj);

        if (obj->get_family_id() == null_family_id) {
            return execute_maxsat(obj, committed);
        }
        if (obj->get_family_id() != m_obj_util.get_family_id()) {
            return execute_min_max(obj, committed, true);
        }

        switch (obj->get_decl_kind()) {
        case OP_MINIMIZE:
            return execute_min_max(to_app(obj->get_arg(0)), committed, false);
        case OP_MAXIMIZE: 
            return execute_min_max(to_app(obj->get_arg(0)), committed, true);
        case OP_LEX:
            return execute_lex(obj);
        case OP_BOX:
            return execute_box(obj);
        case OP_PARETO:
            return execute_pareto(obj);
        default:
            UNREACHABLE();
            return l_undef;
        }
    }

    lbool context::execute_min_max(app* obj, bool committed, bool is_max) {
        // HACK: reuse m_optsmt but add only a single objective each round
        m_optsmt.add(obj, is_max);
        lbool result = m_optsmt(get_solver());
        if (committed) m_optsmt.commit_assignment(0);
        return result;
    }


    lbool context::execute_maxsat(app* obj, bool committed) {
        maxsmt* ms;
        VERIFY(m_maxsmts.find(obj->get_decl()->get_name(), ms));
        lbool result = (*ms)(get_solver());
        if (committed) ms->commit_assignment();
        return result;
    }
    
    lbool context::execute_lex(app* obj) {
        lbool r = l_true;
        for (unsigned i = 0; r == l_true && i < obj->get_num_args(); ++i) {
            r = execute(obj->get_arg(i), true);
        }
        return r;
    }    

    lbool context::execute_box(app* obj) {
        lbool r = l_true;
        for (unsigned i = 0; r == l_true && i < obj->get_num_args(); ++i) {
            push();
            r = execute(obj->get_arg(i), false);
            pop(1);
        }
        return r;
    }

    lbool context::execute_pareto(app* obj) {
        // TODO: record a stream of results from pareto front
        return execute_lex(obj);
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

    lbool context::optimize(expr* objective) {
        if (!objective) {
            return optimize();
        }
        opt_solver& s = get_solver();
        solver::scoped_push _sp(s);
        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }
        return execute(objective, false);
    }

    lbool context::optimize() {
        // Construct objectives
        expr_ref_vector objectives(m);
        expr_ref objective(m);
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            objectives.push_back(m_obj_util.mk_maxsat(it->m_key));
        }
        for (unsigned i = 0; i < m_objs.size(); ++i) {
            expr_ref e(m_objs[i].get(), m);
            app * o = m_ismaxs[i] ? m_obj_util.mk_max(e) : m_obj_util.mk_min(e);
            objectives.push_back(o);
        }
        if (m_params.get_bool("pareto", false)) {            
            objective = m_obj_util.mk_pareto(objectives.size(), objectives.c_ptr());
        }
        else {
            objective = m_obj_util.mk_box(objectives.size(), objectives.c_ptr());
        }
        return optimize(objective);
    }

    void context::display_assignment(std::ostream& out) {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            maxsmt* ms = it->m_value;
            if (it->m_key != symbol::null) {
                out << it->m_key << " : ";
            }
            out << ms->get_value() << "\n";
        }
        m_optsmt.display_assignment(out);
    }

    void context::display_range_assignment(std::ostream& out) {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            maxsmt* ms = it->m_value;
            if (it->m_key != symbol::null) {
                out << it->m_key << " : ";
            }
            out << "[" << ms->get_lower() << ":" << ms->get_upper() << "]\n";
        }
        m_optsmt.display_range_assignment(out);
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
