/*++

  Module Name:

    mbp_qel.h

Abstract:

    Model Based Projection based on term graph

Author:

    Hari Govind V K (hgvk94) 2022-07-12

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "model/model.h"
#include "util/params.h"

namespace mbp {
class mbp_qel {
    class impl;
    impl *m_impl;

  public:
    mbp_qel(ast_manager &m, params_ref const &p);

    ~mbp_qel();

    /**
       Do model based projection
    */
    void operator()(app_ref_vector &vars, expr_ref &fml, model &mdl);
};
} // namespace mbp
