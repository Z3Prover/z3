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

#include "lbool.h"
#include "dl_rule.h"
#include "dl_rule_set.h"
#include "dl_engine_base.h"
#include "statistics.h"

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
        ~dl_interface();
        
        lbool query(expr* query);

        void cancel();

        void cleanup();

        void display_certificate(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        void reset_statistics();

        expr_ref get_answer();

        unsigned get_num_levels(func_decl* pred);

        expr_ref get_cover_delta(int level, func_decl* pred);
       
        void add_cover(int level, func_decl* pred, expr* property);
               
        void updt_params();

        model_ref get_model();

        proof_ref get_proof();
        
	duality_data *dd(){return _d;}

    private:
        void display_certificate_non_const(std::ostream& out);
    };
}


#endif
