/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    ddnf.h

Abstract:

    DDNF based engine.

Author:

    Nikolaj Bjorner (nbjorner) 2014-08-21

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "muz/base/dl_engine_base.h"

class tbv;
class tbv_manager;

namespace datalog {
    class context;

    class ddnf : public engine_base {
        class imp;
        imp* m_imp;
    public:
        ddnf(context& ctx);
        ~ddnf() override;
        lbool query(expr* query) override;
        void reset_statistics() override;
        void collect_statistics(statistics& st) const override;
        void display_certificate(std::ostream& out) const override;
        expr_ref get_answer() override;
    };

    class ddnf_node;
    class ddnf_mgr;
    class ddnf_core {
        ddnf_mgr* m_imp;
    public:
        ddnf_core(unsigned n);
        ~ddnf_core();
        ddnf_node* insert(tbv const& t);
        tbv_manager& get_tbv_manager();
        unsigned size() const;
        bool contains(tbv const& t);
        bool well_formed();

        //
        // accumulate labels covered by the stream of tbvs, 
        // such that labels that are covered by the current 
        // tbv but not the previous tbvs are included.
        // 
        void reset_accumulate();
        void accumulate(tbv const& t, unsigned_vector& labels);
        void display(std::ostream& out) const;
        void display_statistics(std::ostream& out) const;
    };
};

