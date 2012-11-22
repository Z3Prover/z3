/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pdr_quantifiers.h

Abstract:

    Module for handling quantifiers in rule bodies.

Author:

    Nikolaj Bjorner (nbjorner) 2012-05-19.

Revision History:

--*/

#ifndef _PDR_QUANTIFIERS_H_
#define _PDR_QUANTIFIERS_H_
 
#include "ast.h"
#include "dl_rule.h"
#include "obj_pair_hashtable.h"

namespace datalog {
    class rule_set;
};

namespace pdr {

    class model_node;
    class pred_transformer;
    class context;
    
    
    class quantifier_model_checker {
        context&                      m_ctx;
        ast_manager&                  m;
        obj_map<datalog::rule const, quantifier_ref_vector*>& m_quantifiers;
        datalog::rule_set&            m_rules;
        expr_ref_vector               m_trail;
        expr_ref                      m_A;
        expr_ref_vector               m_Bs;
        pred_transformer*             m_current_pt;
        datalog::rule const*          m_current_rule;
        model_node*                   m_current_node;
        app_ref_vector                  m_instantiations;
        ptr_vector<datalog::rule const> m_instantiated_rules;

        void model_check_node(model_node& node);

        bool find_instantiations(quantifier_ref_vector const& qs, unsigned level); 

        bool find_instantiations_model_based(quantifier_ref_vector const& qs, unsigned level);

        bool find_instantiations_proof_based(quantifier_ref_vector const& qs, unsigned level);

        bool find_instantiations_qe_based(quantifier_ref_vector const& qs, unsigned level);

        void add_binding(quantifier* q, expr_ref_vector& binding);

        void apply_binding(quantifier* q, expr_ref_vector& binding);

        void generalize_binding(expr_ref_vector const& binding, vector<expr_ref_vector>& bindings);

        void generalize_binding(expr_ref_vector const& binding, unsigned idx, expr_ref_vector& new_binding, vector<expr_ref_vector>& bindings);

        void refine();


        /**
           \brief model check a potential model against quantifiers in bodies of rules.
           
           \return true if the model rooted in 'root' is checks with the quantifiers, otherwise
           'false' and a set of instantiations that contradict the current model.
        */
        
        bool model_check(model_node& root);

    public:
        quantifier_model_checker(
            context& ctx, 
            ast_manager& m, 
            obj_map<datalog::rule const, quantifier_ref_vector*>& quantifiers, 
            datalog::rule_set& rules) : 
            m_ctx(ctx),
            m(m),
            m_quantifiers(quantifiers),
            m_rules(rules),
            m_trail(m), m_A(m), m_Bs(m),             
            m_current_pt(0), m_current_rule(0), 
            m_current_node(0), m_instantiations(m) {}

        bool check();
    };

};
#endif
