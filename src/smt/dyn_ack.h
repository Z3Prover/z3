/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dyn_ack.h

Abstract:

    Support code for implementing Dynamic Ackermann's reduction

Author:

    Leonardo de Moura (leonardo) 2007-04-12.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "params/dyn_ack_params.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"
#include "util/obj_triple_hashtable.h"
#include "smt/smt_clause.h"

namespace smt {

    class context;

    class dyn_ack_manager {
        typedef std::pair<app *, app *>           app_pair;
        typedef obj_pair_map<app, app, unsigned>  app_pair2num_occs;
        typedef svector<app_pair>                 app_pair_vector;
        typedef obj_pair_hashtable<app, app>      app_pair_set;
        typedef obj_map<clause, app_pair>         clause2app_pair;

        typedef triple<expr *, expr *,expr *>        expr_triple;
        typedef obj_triple_map<expr, expr, expr, unsigned>  expr_triple2num_occs;
        typedef svector<expr_triple>                 expr_triple_vector;
        typedef obj_triple_hashtable<expr, expr, expr>      expr_triple_set;
        typedef obj_map<clause, expr_triple>         clause2expr_triple;

        context &                                  m_context;
        ast_manager &                              m;
        dyn_ack_params &                           m_params;
        app_pair2num_occs                          m_app_pair2num_occs;
        app_pair_vector                            m_app_pairs;
        app_pair_vector                            m_to_instantiate;
        unsigned                                   m_qhead;
        unsigned                                   m_num_instances;
        unsigned                                   m_num_propagations_since_last_gc;
        app_pair_set                               m_instantiated;
        clause2app_pair                            m_clause2app_pair;

        struct _triple {
            expr_triple2num_occs                   m_app2num_occs;
            expr_triple_vector                     m_apps;
            expr_triple_vector                     m_to_instantiate;
            unsigned                               m_qhead;
            unsigned                               m_num_instances;
            unsigned                               m_num_propagations_since_last_gc;
            expr_triple_set                        m_instantiated;
            clause2expr_triple                     m_clause2apps;
        };
        _triple                                    m_triple;
        


        void gc();
        void reset_app_pairs();
        friend class dyn_ack_clause_del_eh;
        void del_clause_eh(clause * cls);
        void instantiate(app * n1, app * n2);
        literal mk_eq(expr * n1, expr * n2);
        void cg_eh(app * n1, app * n2);

        void eq_eh(expr * n1, expr * n2, expr* r);
        void instantiate(expr * n1, expr * n2, expr* r);
        void reset_expr_triples();
        void gc_triples();
        
    public:
        dyn_ack_manager(context & ctx, dyn_ack_params & p);
        ~dyn_ack_manager();

        void setup() {
        }

        /**
           \brief This method is invoked before the beginning of the search.
        */
        void init_search_eh();

        /**
           \brief This method is invoked when the congruence rule was used during conflict resolution.
        */
        void used_cg_eh(app * n1, app * n2) {
            if (m_params.m_dack == dyn_ack_strategy::DACK_CR)
                cg_eh(n1, n2);
        }

        /**
           \brief This method is invoked when the congruence rule is the root of a conflict.
        */
        void cg_conflict_eh(app * n1, app * n2) {
            if (m_params.m_dack == dyn_ack_strategy::DACK_ROOT)
                cg_eh(n1, n2);
        }

        /**
           \brief This method is invoked when equalities are used during conflict resolution.
        */
        void used_eq_eh(expr * n1, expr * n2, expr* r) {
            if (m_params.m_dack_eq)
                eq_eh(n1, n2, r);
        }

        
        /**
           \brief This method is invoked when it is safe to expand the new ackermann rule entries.
        */
        void propagate_eh();

        void reset();

#ifdef Z3DEBUG
        bool check_invariant() const;
#endif
    };

};


