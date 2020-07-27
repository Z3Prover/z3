/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_pareto.h

Abstract:

    Pareto front utilities

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-24

Notes:

   
--*/
#pragma once

#include "solver/solver.h"
#include "model/model.h"

namespace opt {
   
    class pareto_callback {
    public:
        virtual unsigned num_objectives() = 0;
        virtual expr_ref mk_gt(unsigned i, model_ref& model) = 0;
        virtual expr_ref mk_ge(unsigned i, model_ref& model) = 0;
        virtual expr_ref mk_le(unsigned i, model_ref& model) = 0;
        virtual void fix_model(model_ref& m) = 0;
    };
    class pareto_base {
    protected:
        ast_manager&     m;
        pareto_callback& cb;
        ref<solver>      m_solver;
        params_ref       m_params;
        model_ref        m_model;
        svector<symbol>  m_labels;
    public:
        pareto_base(
            ast_manager & m, 
            pareto_callback& cb, 
            solver* s, 
            params_ref & p):
            m(m),
            cb(cb),            
            m_solver(s),
            m_params(p) {
        }
        virtual ~pareto_base() {}
        virtual void updt_params(params_ref & p) {
            m_solver->updt_params(p);
            m_params.copy(p);
        }
        virtual void collect_param_descrs(param_descrs & r) {
            m_solver->collect_param_descrs(r);
        }
        virtual void collect_statistics(statistics & st) const {
            m_solver->collect_statistics(st);
        }
        virtual void display(std::ostream & out) const {
            m_solver->display(out);
        }
        virtual lbool operator()() = 0;

        virtual void get_model(model_ref& mdl, svector<symbol>& labels) {
            mdl = m_model;
            labels = m_labels;
        }

    protected:

        void mk_dominates();

        void mk_not_dominated_by();            
    };
    class gia_pareto : public pareto_base {
    public:
        gia_pareto(ast_manager & m, 
                   pareto_callback& cb, 
                   solver* s, 
                   params_ref & p):
            pareto_base(m, cb, s, p) {            
        }
        ~gia_pareto() override {}

        lbool operator()() override;
    };

    // opportunistic improvement algorithm.
    class oia_pareto : public pareto_base {
    public:
        oia_pareto(ast_manager & m, 
                   pareto_callback& cb, 
                   solver* s, 
                   params_ref & p):
            pareto_base(m, cb, s, p) {            
        }
        ~oia_pareto() override {}

        lbool operator()() override;
    };
}

