/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    opt_lns.h

Abstract:

    Large neighborhood seearch

Author:

    Nikolaj Bjorner (nbjorner) 2018-3-13

Notes:

   
--*/
#ifndef OPT_LNS_H_
#define OPT_LNS_H_

#include "solver/solver.h"
#include "model/model.h"

namespace opt {

    class context;

    class lns {
        struct queue_elem {
            expr_ref_vector m_assignment;
            unsigned        m_index;
            queue_elem(expr_ref_vector& assign):
                m_assignment(assign),
                m_index(0)
            {}
        };
        ast_manager&        m;
        context&            m_ctx;
        ref<solver>         m_solver;
        model_ref           m_model;
        svector<symbol>     m_labels;
        vector<queue_elem>  m_queue;
        unsigned            m_qhead;
        expr_ref_vector     m_models_trail;
        expr_ref_vector     m_atoms;
        obj_hashtable<expr> m_models;
        obj_hashtable<expr> m_fixed;

        bool add_assignment();
    public:
        lns(context& ctx, solver* s);

        ~lns();

        void display(std::ostream & out) const;

        lbool operator()();

        void get_model(model_ref& mdl, svector<symbol>& labels) {
            mdl = m_model;
            labels = m_labels;
        }
    };
}

#endif
