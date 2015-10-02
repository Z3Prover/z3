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
#ifndef DDNF_H_
#define DDNF_H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"
#include "dl_engine_base.h"

class tbv;
class tbv_manager;

namespace datalog {
    class context;

    class ddnf : public engine_base {
        class imp;
        imp* m_imp;
    public:
        ddnf(context& ctx);
        ~ddnf();
        virtual lbool query(expr* query);
        virtual void cancel();
        virtual void cleanup();
        virtual void reset_statistics();
        virtual void collect_statistics(statistics& st) const;
        virtual void display_certificate(std::ostream& out) const;        
        virtual expr_ref get_answer();
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

#endif
