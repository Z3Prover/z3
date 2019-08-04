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

#include "util/obj_hashtable.h"
#include "ast/ast.h"
#include "ast/array_decl_plugin.h"
#include "ast/normal_forms/defined_names.h"
#include "smt/params/qi_params.h"
#include "smt/params/smt_params.h"

class proto_model;
class model;

namespace smt {
    class context;
    class enode;
    class model_finder;
    class quantifier_manager;

    class model_checker {
        ast_manager &                               m; // _manager;
        qi_params const &                           m_params;
        array_util                                  m_autil;
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
        bool                                        m_has_rec_fun;
        proto_model *                               m_curr_model;
        obj_map<expr, expr *>                       m_value2expr;
        expr_ref_vector                             m_fresh_exprs;

        friend class instantiation_set;

        void init_aux_context();
        void init_value2expr();
        expr * get_term_from_ctx(expr * val);
        expr * get_type_compatible_term(expr * val);
        expr_ref replace_value_from_ctx(expr * e);
        void restrict_to_universe(expr * sk, obj_hashtable<expr> const & universe);
        void assert_neg_q_m(quantifier * q, expr_ref_vector & sks);
        bool add_blocking_clause(model * cex, expr_ref_vector & sks);
        bool check(quantifier * q);
        bool check_rec_fun(quantifier* q, bool strict_rec_fun);
        bool has_rec_under_quantifiers();
        void check_quantifiers(bool strict_rec_fun, bool& found_relevant, unsigned& num_failures);

        struct instance {
            quantifier * m_q;
            unsigned     m_generation;
            expr *       m_def;
            unsigned     m_bindings_offset;
            instance(quantifier * q, unsigned offset, expr* def, unsigned gen):m_q(q), m_generation(gen), m_def(def), m_bindings_offset(offset) {}
        };

        svector<instance>                          m_new_instances;
        expr_ref_vector                            m_pinned_exprs;
        bool add_instance(quantifier * q, model * cex, expr_ref_vector & sks, bool use_inv);
        void reset_new_instances();
        void assert_new_instances();

        quantifier * get_flat_quantifier(quantifier * q);

        struct is_model_value {};
        expr_mark m_visited;
        bool contains_model_value(expr * e);
        void add_instance(quantifier * q, expr_ref_vector const & bindings, unsigned max_generation, expr * def);

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

        void operator()(expr* e);

    };
};

#endif // _SMT_MODEL_CHECKER_H_
