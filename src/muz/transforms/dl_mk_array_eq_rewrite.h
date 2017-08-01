/*++

Module Name:

    dl_mk_array_eq_rewrite.h

Abstract:
    Selects a representative for array equivalence classes.

Author:

    Julien Braine

Revision History:   

--*/

#ifndef DL_MK_ARRAY_EQ_REWRITE_H_
#define DL_MK_ARRAY_EQ_REWRITE_H_


#include "dl_rule_transformer.h"
#include "../spacer/obj_equiv_class.h"

namespace datalog {

    class context;
    class mk_array_eq_rewrite : public rule_transformer::plugin {
       //Context objects
       ast_manager&      m;
       context&          m_ctx;
       array_util   m_a;
    
       //Rule set context
       const rule_set*src_set;
       rule_set*dst;
       rule_manager* src_manager;
       unsigned cnt;//Index for new variables

       expr* replace(expr* e, expr* new_val, expr* old_val);
       void instantiate_rule(const rule& r, rule_set & dest);

     public:
        mk_array_eq_rewrite(context & ctx, unsigned priority);
        rule_set * operator()(rule_set const & source);
        virtual ~mk_array_eq_rewrite(){}
    };



};

#endif /* DL_MK_ARRAY_EQ_REWRITE_H_ */

