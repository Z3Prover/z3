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

#include "muz/base/dl_rule_transformer.h"

namespace datalog {

    class context;
    class mk_array_eq_rewrite : public rule_transformer::plugin {
       //Context objects
       ast_manager&      m;
       context&          m_ctx;
       array_util        m_a;

       //Rule set context
       const rule_set*   m_src_set;
       rule_set*         m_dst;
       rule_manager*     m_src_manager;
       unsigned          m_cnt;//Index for new variables

       expr* replace(expr* e, expr* new_val, expr* old_val);
       void instantiate_rule(const rule& r, rule_set & dest);

     public:
        mk_array_eq_rewrite(context & ctx, unsigned priority);
        rule_set * operator()(rule_set const & source) override;
        ~mk_array_eq_rewrite() override{}
    };



};

#endif /* DL_MK_ARRAY_EQ_REWRITE_H_ */
