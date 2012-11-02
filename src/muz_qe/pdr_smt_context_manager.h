/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_smt_context_manager.h

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.

Revision History:

--*/

#ifndef _PDR_SMT_CONTEXT_MANAGER_H_
#define _PDR_SMT_CONTEXT_MANAGER_H_

#include "smt_kernel.h"
#include "sat_solver.h"
#include "func_decl_dependencies.h"

namespace pdr {
    
    class smt_context_manager;

    class smt_context {
    protected:
        app_ref              m_pred;
        smt_context_manager& m_parent;
        bool          m_in_delay_scope;
        bool          m_pushed;
    public:
        smt_context(smt_context_manager& p, ast_manager& m, app* pred);
        virtual ~smt_context() {}
        virtual void assert_expr(expr* e) = 0;
        virtual lbool check(expr_ref_vector& assumptions) = 0;
        virtual void get_model(model_ref& model) = 0;
        virtual proof* get_proof() = 0;
        virtual unsigned get_unsat_core_size() = 0;
        virtual expr* get_unsat_core_expr(unsigned i) = 0;
        virtual void push() = 0;
        virtual void pop() = 0;
        bool is_aux_predicate(func_decl* p);
        bool is_aux_predicate(expr* p) { return is_app(p) && is_aux_predicate(to_app(p)->get_decl()); }
        class scoped {
            smt_context& m_ctx;
        public:
            scoped(smt_context& ctx);
            ~scoped();
        };
    };

    class _smt_context : public smt_context {
        smt::kernel & m_context;
    public:
        _smt_context(smt::kernel & ctx, smt_context_manager& p, app* pred); 
        virtual ~_smt_context() {}
        virtual void assert_expr(expr* e);
        virtual lbool check(expr_ref_vector& assumptions);
        virtual void get_model(model_ref& model);
        virtual proof* get_proof();
        virtual void push() { m_context.push(); }
        virtual void pop() { m_context.pop(1); }
        virtual unsigned get_unsat_core_size() { return m_context.get_unsat_core_size(); }
        virtual expr* get_unsat_core_expr(unsigned i) { return m_context.get_unsat_core_expr(i); }
    };

    // TBD: 
    class sat_context : public smt_context {
        sat::solver m_solver;
    public:
        sat_context(smt::kernel & ctx, smt_context_manager& p, app* pred); 
        virtual ~sat_context() {}
        virtual void assert_expr(expr* e);
        virtual lbool check(expr_ref_vector& assumptions);
        virtual void get_model(model_ref& model);
        virtual proof* get_proof();
        virtual void pop() { m_solver.pop(1); }
        virtual void push() { m_solver.push(); }
        // TBD: add unsat core extraction with sat::solver.
        virtual unsigned get_unsat_core_size();
        virtual expr* get_unsat_core_expr(unsigned i);
    };

    class smt_context_manager {
        front_end_params&        m_fparams;
        ast_manager&             m;
        unsigned                 m_max_num_contexts;
        ptr_vector<smt::kernel>  m_contexts;
        unsigned                 m_num_contexts;
        app_ref_vector           m_predicate_list;
        func_decl_set            m_predicate_set;        
    public:
        smt_context_manager(front_end_params& fp, params_ref const& p, ast_manager& m);
        ~smt_context_manager();
        smt_context* mk_fresh();                
        void collect_statistics(statistics& st) const;
        bool is_aux_predicate(func_decl* p) const { return m_predicate_set.contains(p); }
    };

};

#endif
