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

#ifndef _PDR_DL_INTERFACE_H_
#define _PDR_DL_INTERFACE_H_

#include "lbool.h"
#include "dl_rule.h"
#include "dl_rule_set.h"
#include "statistics.h"

namespace datalog {
    class context;
}

namespace pdr {

    class context;

    class dl_interface {
        datalog::context& m_ctx;
        datalog::rule_set m_pdr_rules;
        datalog::rule_set m_old_rules;
        context*          m_context;
        obj_map<func_decl, func_decl*> m_pred2slice;
        ast_ref_vector    m_refs;

        void check_reset();

    public:
        dl_interface(datalog::context& ctx); 
        ~dl_interface();
        
        lbool query(expr* query);

        void cancel();

        void cleanup();

        void display_certificate(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        expr_ref get_answer();

        unsigned get_num_levels(func_decl* pred);

        expr_ref get_cover_delta(int level, func_decl* pred);
       
        void add_cover(int level, func_decl* pred, expr* property);

        static void collect_params(param_descrs& p);

        void updt_params();
        
    };
}


#endif
