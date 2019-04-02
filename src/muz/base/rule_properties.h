/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    rule_properties.h

Abstract:

    Collect properties of rules.

Author:

    Nikolaj Bjorner (nbjorner) 9-25-2014

Notes:
    

--*/

#ifndef RULE_PROPERTIES_H_
#define RULE_PROPERTIES_H_

#include "ast/ast.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "muz/base/dl_rule.h"

namespace datalog {
    class rule_properties {
        ast_manager&  m;
        rule_manager& rm;
        context&      m_ctx;
        i_expr_pred&  m_is_predicate;
        datatype_util m_dt;
        dl_decl_util  m_dl;
        bv_util       m_bv;
        bool          m_generate_proof;
        rule*         m_rule;
        obj_map<quantifier, rule*> m_quantifiers;
        obj_map<func_decl, rule*>  m_uninterp_funs;
        vector<rule*>           m_interp_pred;
        vector<rule*>           m_negative_rules;
        vector<rule*>           m_inf_sort;

        void insert(vector<rule*>& rules, rule* r);
    public:
        rule_properties(ast_manager & m, rule_manager& rm, context& ctx, i_expr_pred& is_predicate);
        ~rule_properties();    
        void set_generate_proof(bool generate_proof) { m_generate_proof = generate_proof; } 
        void collect(rule_set const& r);
        void check_quantifier_free();
        void check_uninterpreted_free();
        void check_existential_tail();
        void check_for_negated_predicates();
        void check_nested_free();
        void check_infinite_sorts();
        void operator()(var* n);
        void operator()(quantifier* n);
        void operator()(app* n);
        void reset();
    };
}

#endif /* RULE_PROPERTIES_H_ */
