/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_datatype_plugin.h

Abstract:

    Algebraic Datatypes for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-14
    
--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/datatype_decl_plugin.h"

namespace sls {
    
    class datatype_plugin : public plugin {
        struct stats {
            unsigned m_num_axioms = 0;
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        obj_map<sort, ptr_vector<expr>> m_dts;

        datatype_util m_dt;
        stats m_stats;

        void add_axioms();

    public:
        datatype_plugin(context& c);
        ~datatype_plugin() override;
        family_id fid() { return m_fid; }
        expr_ref get_value(expr* e) override;
        void initialize() override;
        void start_propagation() override;
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;       
        bool is_sat() override;
        void register_term(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override;
        bool set_value(expr* e, expr* v) override { return false; }

        void repair_up(app* e) override {}
        bool repair_down(app* e) override { return false; }
        void repair_literal(sat::literal lit) override {}

        void collect_statistics(statistics& st) const override;
        void reset_statistics() override;
    };
    
}
