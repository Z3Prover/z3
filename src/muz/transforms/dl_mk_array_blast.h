/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast.h

Abstract:

    Remove array variables from rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:

--*/
#ifndef DL_MK_ARRAY_BLAST_H_
#define DL_MK_ARRAY_BLAST_H_

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_set.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/transforms/dl_mk_interp_tail_simplifier.h"
#include "tactic/equiv_proof_converter.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/expr_safe_replace.h"

namespace datalog {

    /**
       \brief Blast occurrences of arrays in rules
    */
    class mk_array_blast : public rule_transformer::plugin {
        typedef obj_map<app, var*> defs_t;

        context&        m_ctx;
        ast_manager&    m;
        array_util      a;
        rule_manager&   rm;
        params_ref      m_params;
        th_rewriter     m_rewriter;
        mk_interp_tail_simplifier m_simplifier;

        defs_t            m_defs;
        unsigned          m_next_var;

        bool blast(rule& r, rule_set& new_rules);

        bool is_store_def(expr* e, expr*& x, expr*& y);

        bool ackermanize(rule const& r, expr_ref& body, expr_ref& head);

        expr* get_select(expr* e) const;

        void get_select_args(expr* e, ptr_vector<expr>& args) const;

        bool insert_def(rule const& r, app* e, var* v);

        bool is_select_eq_var(expr* e, app*& s, var*& v) const;

    public:
        /**
           \brief Create rule transformer that removes array stores and selects by ackermannization.
        */
        mk_array_blast(context & ctx, unsigned priority);

        ~mk_array_blast() override;
        
        rule_set * operator()(rule_set const & source) override;

    };

};

#endif /* DL_MK_ARRAY_BLAST_H_ */

