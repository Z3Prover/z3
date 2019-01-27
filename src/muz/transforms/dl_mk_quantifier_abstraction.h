/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_quantifier_abstraction.h

Abstract:

    Convert clauses with array arguments to predicates 
    into Quantified Horn clauses.

Author:

    Ken McMillan 
    Andrey Rybalchenko
    Nikolaj Bjorner (nbjorner) 2013-04-02

Revision History:

    Based on approach suggested in SAS 2013 paper 
    "On Solving Universally Quantified Horn Clauses"    

--*/
#ifndef DL_MK_QUANTIFIER_ABSTRACTION_H_
#define DL_MK_QUANTIFIER_ABSTRACTION_H_


#include "muz/base/dl_rule_transformer.h"
#include "ast/array_decl_plugin.h"

namespace datalog {

    class context;

    class mk_quantifier_abstraction : public rule_transformer::plugin {
        class qa_model_converter;
        ast_manager& m;
        context&     m_ctx;
        array_util   a;
        func_decl_ref_vector           m_refs;
        obj_map<func_decl, func_decl*> m_new2old;
        obj_map<func_decl, func_decl*> m_old2new;
        qa_model_converter*            m_mc;

        func_decl* declare_pred(rule_set const& rules, rule_set& dst, func_decl* old_p);
        app_ref mk_head(rule_set const& rules, rule_set& dst, app* p, unsigned idx);
        app_ref mk_tail(rule_set const& rules, rule_set& dst, app* p);
        expr*   mk_select(expr* a, unsigned num_args, expr* const* args);

    public:
        mk_quantifier_abstraction(context & ctx, unsigned priority);

        ~mk_quantifier_abstraction() override;
        
        rule_set * operator()(rule_set const & source) override;
    };



};

#endif /* DL_MK_QUANTIFIER_ABSTRACTION_H_ */

