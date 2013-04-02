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
#ifndef _DL_MK_QUANTIFIER_ABSTRACTION_H_
#define _DL_MK_QUANTIFIER_ABSTRACTION_H_


#include"dl_rule_transformer.h"
#include"array_decl_plugin.h"

namespace datalog {

    class context;

    class mk_quantifier_abstraction : public rule_transformer::plugin {
        ast_manager& m;
        context&     m_ctx;
        array_util   a;
        func_decl_ref_vector m_refs;
        obj_map<func_decl, func_decl*> m_new2old;
        obj_map<func_decl, func_decl*> m_old2new;

        func_decl* declare_pred(func_decl* old_p);
        app_ref mk_head(app* p, unsigned idx);
        app_ref mk_tail(app* p);

    public:
        mk_quantifier_abstraction(context & ctx, unsigned priority);

        virtual ~mk_quantifier_abstraction();
        
        rule_set * operator()(rule_set const & source);
    };



};

#endif /* _DL_MK_QUANTIFIER_ABSTRACTION_H_ */

