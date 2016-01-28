 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_helper.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef ACKR_HELPER_H_6475
#define ACKR_HELPER_H_6475
#include"bv_decl_plugin.h"
class ackr_helper {
    public:
        ackr_helper(ast_manager& m) : m_bvutil(m) {}
        inline bool should_ackermannize(app const * a) const {
            if (a->get_family_id() == m_bvutil.get_family_id()) {
                switch (a->get_decl_kind()) {
                    case OP_BSDIV0:
                    case OP_BUDIV0:
                    case OP_BSREM0:
                    case OP_BUREM0:
                    case OP_BSMOD0:
                        return true;
                    default:
                        return is_uninterp(a);
                }
            }
            return (is_uninterp(a));
        }

        bv_util& bvutil() { return m_bvutil; }
    private:
        bv_util                              m_bvutil;
};
#endif /* ACKR_HELPER_H_6475 */
