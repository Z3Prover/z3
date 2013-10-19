/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_scale.h

Abstract:

    Add scale factor to linear (Real) arithemetic Horn clauses.
    The transformation replaces occurrences of isolated constants by
    a scale multiplied to each constant. 

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-19

Revision History:

--*/
#ifndef _DL_MK_SCALE_H_
#define _DL_MK_SCALE_H_

#include"dl_rule_transformer.h"
#include"arith_decl_plugin.h"

namespace datalog {

    class mk_scale : public rule_transformer::plugin {

        class scale_model_converter;

        ast_manager& m;
        context&     m_ctx;
        arith_util   a;
        expr_ref_vector m_trail;
        app_ref_vector m_eqs;
        obj_map<expr, expr*> m_cache;
        scale_model_converter* m_mc;

        expr*   linearize(unsigned num_vars, expr* e);
        app_ref mk_pred(unsigned num_vars, app* q);
        app_ref mk_constraint(unsigned num_vars, app* q);
    public:
        mk_scale(context & ctx, unsigned priority = 33039);
        virtual ~mk_scale();        
        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_SCALE_H_ */

