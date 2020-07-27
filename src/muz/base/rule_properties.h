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

#pragma once

#include "ast/ast.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/recfun_decl_plugin.h"
#include "muz/base/dl_rule.h"
#include "ast/expr_functors.h"

namespace datalog {
    class rule_properties {
        ast_manager&  m;
        rule_manager& rm;
        context&      m_ctx;
        i_expr_pred&  m_is_predicate;
        datatype_util m_dt;
        dl_decl_util  m_dl;
        arith_util    m_a;
        bv_util       m_bv;
        array_util    m_ar;
        recfun::util  m_rec;
        bool          m_generate_proof;
        rule*         m_rule;
        obj_map<quantifier, rule*> m_quantifiers;
        obj_map<func_decl, rule*>  m_uninterp_funs;
        ptr_vector<rule>           m_interp_pred;
        ptr_vector<rule>           m_negative_rules;
        ptr_vector<rule>           m_inf_sort;
        bool                       m_collected;
        bool                       m_is_monotone;

        void insert(ptr_vector<rule>& rules, rule* r);
        void check_sort(sort* s);
        void visit_rules(expr_sparse_mark& visited, rule_set const& rules);
        bool evaluates_to_numeral(expr * n, rational& val);
    public:
        rule_properties(ast_manager & m, rule_manager& rm, context& ctx, i_expr_pred& is_predicate);
        ~rule_properties();    
        void set_generate_proof(bool generate_proof) { m_generate_proof = generate_proof; } 
        void collect(rule_set const& r);
        void check_quantifier_free();
        void check_quantifier_free(quantifier_kind qkind);
        void check_uninterpreted_free();
        void check_existential_tail();
        void check_for_negated_predicates();
        void check_nested_free();
        void check_infinite_sorts();
        bool is_monotone() { return m_is_monotone; }
        void operator()(var* n);
        void operator()(quantifier* n);
        void operator()(app* n);
        void reset();
    };
}

