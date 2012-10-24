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

    struct qinst {
        quantifier_ref_vector  quantifiers; // quantifiers in rule body.
        func_decl_ref_vector   predicates;  // predicates in order of bindings.
        expr_ref_vector        bindings;    // the actual instantiations of the predicates
        qinst(ast_manager& m): quantifiers(m), predicates(m), bindings(m) {}
    };

    class qi {
        ptr_vector<datalog::rule const>     m_rules;
        app_ref_vector                     m_apps;
    public:
        qi(ast_manager& m) : m_apps(m) {}
        void add(datalog::rule const* r, app* a) {
            m_rules.push_back(r);
            m_apps.push_back(a);
        }
        unsigned size() const { return m_rules.size(); }
        datalog::rule const* get_rule(unsigned i) const { return m_rules[i]; }
        app*           get_app(unsigned i) const { return m_apps[i]; }
    };
    
    
    class quantifier_model_checker {
        context&                      m_ctx;
        ast_manager&                  m;
        obj_pair_map<datalog::rule const, expr, expr*> m_bound;
        expr_ref_vector               m_trail;
        expr_ref                      m_A;
        expr_ref_vector               m_Bs;
        pred_transformer*             m_current_pt;
        datalog::rule const*          m_current_rule;
        model_node*                   m_current_node;

        ptr_vector<datalog::rule const>     m_rules;
        app_ref_vector                      m_apps;

        void model_check_node(model_node& node);

        bool find_instantiations(qinst& qi, unsigned level); 

        bool find_instantiations_model_based(qinst& qi, unsigned level);

        bool find_instantiations_proof_based(qinst& qi, unsigned level);

        bool find_instantiations_qe_based(qinst& qi, unsigned level);

        void add_binding(quantifier* q, expr_ref_vector& binding);

        void apply_binding(quantifier* q, expr_ref_vector& binding);

        void generalize_binding(expr_ref_vector const& binding, vector<expr_ref_vector>& bindings);

        void generalize_binding(expr_ref_vector const& binding, unsigned idx, expr_ref_vector& new_binding, vector<expr_ref_vector>& bindings);

    public:
        quantifier_model_checker(context& ctx, ast_manager& m): 
            m_ctx(ctx),
            m(m), m_trail(m), m_A(m), m_Bs(m),             
            m_current_pt(0), m_current_rule(0), 
            m_current_node(0), m_apps(m) {}

        /**
           \brief model check a potential model against quantifiers in bodies of rules.
           
           \return true if the model rooted in 'root' is checks with the quantifiers, otherwise
           'false' and a set of instantiations that contradict the current model.
        */
        
        void model_check(model_node& root);

        void refine(qi& q, datalog::rule_set& rules);
    };

};
#endif
