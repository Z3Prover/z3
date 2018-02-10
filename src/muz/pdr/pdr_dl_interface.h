/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_dl_interface.h

Abstract:

    SMT2 interface for the datalog PDR

Author:

    Krystof Hoder (t-khoder) 2011-9-22.

Revision History:

--*/

#ifndef PDR_DL_INTERFACE_H_
#define PDR_DL_INTERFACE_H_

#include "util/lbool.h"
#include "muz/base/dl_rule.h"
#include "muz/base/dl_rule_set.h"
#include "muz/base/dl_util.h"
#include "muz/base/dl_engine_base.h"
#include "util/statistics.h"

namespace datalog {
    class context;
}

namespace pdr {

    class context;

    class dl_interface : public datalog::engine_base {
        datalog::context& m_ctx;
        datalog::rule_set m_pdr_rules;
        datalog::rule_set m_old_rules;
        context*          m_context;
        obj_map<func_decl, func_decl*> m_pred2slice;
        ast_ref_vector    m_refs;

        void check_reset();

    public:
        dl_interface(datalog::context& ctx); 
        ~dl_interface() override;
        
        lbool query(expr* query) override;

        void display_certificate(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;

        void reset_statistics() override;

        expr_ref get_answer() override;

        unsigned get_num_levels(func_decl* pred) override;

        expr_ref get_cover_delta(int level, func_decl* pred) override;
       
        void add_cover(int level, func_decl* pred, expr* property) override;
               
        void updt_params() override;

        model_ref get_model() override;

        proof_ref get_proof() override;
        
    };
}


#endif
