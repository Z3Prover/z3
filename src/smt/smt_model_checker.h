/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_checker.h

Abstract:

    Model checker
    AND
    Model-based quantifier instantiation.

Author:

    Leonardo de Moura (leonardo) 2010-12-03.

Revision History:

--*/
#ifndef SMT_MODEL_CHECKER_H_
#define SMT_MODEL_CHECKER_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"qi_params.h"
#include"smt_params.h"
#include"region.h"

class proto_model;
class model;

namespace smt {
    class context;
    class enode;
    class model_finder;
    class quantifier_manager;

    class model_checker {
        ast_manager &                               m_manager;
        qi_params const &                           m_params;
        // copy of smt_params for auxiliary context. 
        // the idea is to use a different configuration for the aux context (e.g., disable relevancy)
        scoped_ptr<smt_params>                      m_fparams;
        quantifier_manager *                        m_qm;
        context *                                   m_context; // owner of the model checker
        obj_map<enode, app *> const *               m_root2value; // temp field to store mapping received in the check method.
        model_finder &                              m_model_finder;
        scoped_ptr<context>                         m_aux_context; // Auxiliary context used for model checking quantifiers.
        unsigned                                    m_max_cexs;
        unsigned                                    m_iteration_idx;
        proto_model *                               m_curr_model;
        obj_map<expr, expr *>                       m_value2expr;
        friend class instantiation_set;

        void init_aux_context();
        expr * get_term_from_ctx(expr * val);
        void restrict_to_universe(expr * sk, obj_hashtable<expr> const & universe);
        void assert_neg_q_m(quantifier * q, expr_ref_vector & sks);
        bool add_blocking_clause(model * cex, expr_ref_vector & sks);
        bool check(quantifier * q);
        
        struct instance {
            quantifier * m_q;
            unsigned     m_generation;
            expr *       m_bindings[0];
            static unsigned get_obj_size(unsigned num_bindings) { return sizeof(instance) + num_bindings * sizeof(expr*); }
            instance(quantifier * q, expr * const * bindings, unsigned gen):m_q(q), m_generation(gen) {
                memcpy(m_bindings, bindings, q->get_num_decls() * sizeof(expr*));
            }
        };

        region                                     m_new_instances_region;
        expr_ref_vector                            m_new_instances_bindings;
        ptr_vector<instance>                       m_new_instances;
        bool add_instance(quantifier * q, model * cex, expr_ref_vector & sks, bool use_inv);
        void reset_new_instances();
        void assert_new_instances();

        quantifier * get_flat_quantifier(quantifier * q);

    public:
        model_checker(ast_manager & m, qi_params const & p, model_finder & mf);
        ~model_checker();
        void set_qm(quantifier_manager & qm);
        context * get_context() const { return m_context; }

        bool check(proto_model * md, obj_map<enode, app *> const & root2value);
        bool has_new_instances();

        void init_search_eh();
        void restart_eh();

        void reset();
    };
};

#endif // _SMT_MODEL_CHECKER_H_
