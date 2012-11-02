/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_datalog.h

Abstract:
    Datalog API
    old external_relation_context_impl

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#ifndef _API_DATALOG_H_
#define _API_DATALOG_H_

#include"z3.h"
#include"ast.h"
#include"front_end_params.h"
#include"dl_external_relation.h"
#include"dl_decl_plugin.h"
#include"smt_kernel.h"
#include"api_util.h"
#include"dl_context.h"

typedef void (*reduce_app_callback_fptr)(void*, func_decl*, unsigned, expr*const*, expr**);
typedef void (*reduce_assign_callback_fptr)(void*, func_decl*, unsigned, expr*const*, unsigned, expr*const*);

namespace api {
    
    class fixedpoint_context : public datalog::external_relation_context {
        void *                       m_state;
        reduce_app_callback_fptr     m_reduce_app;
        reduce_assign_callback_fptr  m_reduce_assign;
        datalog::context             m_context;    
        ast_ref_vector               m_trail;        
    public:
        fixedpoint_context(ast_manager& m, front_end_params& p);
        virtual ~fixedpoint_context() {}
        family_id get_family_id() const { return const_cast<datalog::context&>(m_context).get_decl_util().get_family_id(); }
        void set_state(void* state);
        void set_reduce_app(reduce_app_callback_fptr f) { m_reduce_app = f; }
        void set_reduce_assign(reduce_assign_callback_fptr f) { m_reduce_assign = f; }
        virtual void reduce(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result);
        virtual void reduce_assign(func_decl* f, unsigned num_args, expr * const* args, unsigned num_out, expr* const* outs);
        datalog::context& ctx() { return m_context; }
        void add_rule(expr* rule, symbol const& name);
        void update_rule(expr* rule, symbol const& name);
        void add_table_fact(func_decl* r, unsigned num_args, unsigned args[]);
        std::string get_last_status();
        std::string to_string(unsigned num_queries, expr*const* queries);
        void cancel() { m_context.cancel(); }

        unsigned get_num_levels(func_decl* pred);
        expr_ref get_cover_delta(int level, func_decl* pred);
        void add_cover(int level, func_decl* pred, expr* predicate);
        void collect_param_descrs(param_descrs & p) { m_context.collect_params(p); }
        void updt_params(params_ref const& p) { m_context.updt_params(p); }

        void simplify_rules(
            unsigned num_rules, expr* const* rules, 
            unsigned num_outputs,  func_decl* const* outputs, expr_ref_vector& result);
    };
};


struct Z3_fixedpoint_ref : public api::object {
    api::fixedpoint_context *   m_datalog;
    params_ref               m_params;
    Z3_fixedpoint_ref():m_datalog(0) {}
    virtual ~Z3_fixedpoint_ref() { dealloc(m_datalog); }
};

inline Z3_fixedpoint_ref * to_fixedpoint(Z3_fixedpoint s) { return reinterpret_cast<Z3_fixedpoint_ref *>(s); }
inline Z3_fixedpoint of_datalog(Z3_fixedpoint_ref * s) { return reinterpret_cast<Z3_fixedpoint>(s); }
inline api::fixedpoint_context * to_fixedpoint_ref(Z3_fixedpoint s) { return to_fixedpoint(s)->m_datalog; }


#endif
