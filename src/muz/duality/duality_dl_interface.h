/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  duality_dl_interface.h

  Abstract:

  SMT2 interface for Duality

  Author:

  Krystof Hoder (t-khoder) 2011-9-22.
  Modified by Ken McMIllan (kenmcmil) 2013-4-18.

  Revision History:

  --*/

#ifndef DUALITY_DL_INTERFACE_H_
#define DUALITY_DL_INTERFACE_H_

#include "util/lbool.h"
#include "muz/base/dl_rule.h"
#include "muz/base/dl_rule_set.h"
#include "muz/base/dl_engine_base.h"
#include "util/statistics.h"

namespace datalog {
    class context;
}

namespace Duality {

    class duality_data;

    class dl_interface : public datalog::engine_base {
        duality_data *_d;
        datalog::context &m_ctx;

    public:
        dl_interface(datalog::context& ctx); 
        ~dl_interface() override;
        
        lbool query(expr* query) override;

        void cancel() override;

        void cleanup() override;

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
        
        duality_data *dd(){return _d;}

    private:
        void display_certificate_non_const(std::ostream& out);
    };
}


#endif
