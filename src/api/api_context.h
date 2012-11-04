/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_context.h

Abstract:
    Interface of Z3 with "external world".

    It was called _Z3_context

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#ifndef _API_CONTEXT_H_
#define _API_CONTEXT_H_

#include"z3.h"
#include"ast.h"
#include"api_util.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"smt_kernel.h"
#include"front_end_params.h"
#include"event_handler.h"
#include"tactic_manager.h"

namespace smtlib {
    class parser;
};

namespace api {
    class config_params;

    Z3_search_failure mk_Z3_search_failure(smt::failure f);
       

    class context : public tactic_manager {
        class param_ini {
            front_end_params & m_params;
        public:
            param_ini(front_end_params & p);
            ~param_ini();
        };
        
        struct add_plugins {  add_plugins(ast_manager & m); };
        
        front_end_params           m_params;
        param_ini                  m_param_ini;
        bool                       m_user_ref_count; //!< if true, the user is responsible for managing referenc counters.
        ast_manager                m_manager;
        add_plugins                m_plugins;

        arith_util                 m_arith_util;
        bv_util                    m_bv_util;
        datalog::dl_decl_util      m_datalog_util;

        smt::kernel *              m_solver;     // General purpose solver for backward compatibility
        
        ast_ref_vector             m_last_result; //!< used when m_user_ref_count == true
        ast_ref_vector             m_ast_trail;   //!< used when m_user_ref_count == false
        unsigned_vector            m_ast_lim;
        ptr_vector<ast_ref_vector> m_replay_stack;

        ref<api::object>           m_last_obj; //!< reference to the last API object returned by the APIs

        family_id                  m_basic_fid;
        family_id                  m_array_fid;
        family_id                  m_arith_fid;
        family_id                  m_bv_fid;
        family_id                  m_dt_fid;
        family_id                  m_datalog_fid;
        datatype_decl_plugin *     m_dt_plugin;
        
        std::string                m_string_buffer; // temporary buffer used to cache strings sent to the "external" world.

        Z3_error_code              m_error_code;
        Z3_error_handler *         m_error_handler;
        std::string                m_exception_msg; // catch the message associated with a Z3 exception
        bool                       m_searching;
        Z3_ast_print_mode          m_print_mode;

        event_handler *            m_interruptable; // Reference to an object that can be interrupted by Z3_interrupt
    public:
        // Scoped obj for setting m_interruptable
        class set_interruptable {
            context & m_ctx;
        public:
            set_interruptable(context & ctx, event_handler & i);
            ~set_interruptable();
        };

        // ------------------------
        //
        // Core
        //
        // ------------------------
        
        context(config_params * p, bool user_ref_count = false);
        ~context();

        front_end_params & fparams() { return m_params; }
        ast_manager & m() { return m_manager; }
        arith_util & autil() { return m_arith_util; }
        bv_util & bvutil() { return m_bv_util; }
        datalog::dl_decl_util & datalog_util() { return m_datalog_util; }
        family_id get_basic_fid() const { return m_basic_fid; }
        family_id get_array_fid() const { return m_array_fid; }
        family_id get_arith_fid() const { return m_arith_fid; }
        family_id get_bv_fid() const { return m_bv_fid; }
        family_id get_dt_fid() const { return m_dt_fid; }
        family_id get_datalog_fid() const { return m_datalog_fid; }
        datatype_decl_plugin * get_dt_plugin() const { return m_dt_plugin; }

        Z3_error_code get_error_code() const { return m_error_code; }
        void reset_error_code() { m_error_code = Z3_OK; }
        void set_error_code(Z3_error_code err);
        void set_error_handler(Z3_error_handler h) { m_error_handler = h; }
        // Sign an error if solver is searching
        void check_searching();

        Z3_ast_print_mode get_print_mode() const { return m_print_mode; }
        void set_print_mode(Z3_ast_print_mode m) { m_print_mode = m; }

        // Store a copy of str in m_string_buffer, and return a reference to it.
        // This method is used to communicate local/internal strings with the "external world"
        char * mk_external_string(char const * str);
        char * mk_external_string(std::string const & str);

        // Create a numeral of the given sort
        expr * mk_numeral_core(rational const & n, sort * s);
        
        // Return a conjuction that will be exposed to the "external" world.
        expr * mk_and(unsigned num_exprs, expr * const * exprs);

        // Hack for preventing an AST for being GC when ref-count is not used
        void persist_ast(ast * n, unsigned num_scopes);

        // "Save" an AST that will exposed to the "external" world.
        void save_ast_trail(ast * n);
        
        // Similar to previous method, but it "adds" n to the result.
        void save_multiple_ast_trail(ast * n);
        
        // Reset the cache that stores the ASTs exposed in the previous call.
        // This is a NOOP if ref-count is disabled.
        void reset_last_result();
        
        // "Save" a reference to an object that is exposed by the API
        void save_object(object * r);

        // Process exception: save message and set error code.
        void handle_exception(z3_exception & ex);
        char const * get_exception_msg() const { return m_exception_msg.c_str(); }

        // Interrupt the current interruptable object
        void interrupt();

        void invoke_error_handler(Z3_error_code c);
        
        static void out_of_memory_handler(void * _ctx);

        void check_sorts(ast * n);
        // ------------------------
        //
        // Solver interface for backward compatibility 
        //
        // ------------------------
        
        bool has_solver() const { return m_solver != 0; }
        smt::kernel & get_smt_kernel();
        void assert_cnstr(expr * a);
        lbool check(model_ref & m);
        void push();
        void pop(unsigned num_scopes);
        unsigned get_num_scopes() const { return m_ast_lim.size(); }

        // ------------------------
        //
        // Parser interface for backward compatibility 
        //
        // ------------------------

        // TODO: move to a "parser" object visible to the external world.
        std::string                m_smtlib_error_buffer;
        smtlib::parser *           m_smtlib_parser;
        bool                       m_smtlib_parser_has_decls;
        ptr_vector<func_decl>      m_smtlib_parser_decls;
        ptr_vector<sort>           m_smtlib_parser_sorts;
        
        void reset_parser();
        void extract_smtlib_parser_decls();
        
    };
    
};

inline api::context * mk_c(Z3_context c) { return reinterpret_cast<api::context*>(c); }
#define RESET_ERROR_CODE() { mk_c(c)->reset_error_code(); }
#define SET_ERROR_CODE(ERR) { mk_c(c)->set_error_code(ERR); }
#define CHECK_NON_NULL(_p_,_ret_) { if (_p_ == 0) { SET_ERROR_CODE(Z3_INVALID_ARG); return _ret_; } }
#define CHECK_VALID_AST(_a_, _ret_) { if (_a_ == 0 || !CHECK_REF_COUNT(_a_)) { SET_ERROR_CODE(Z3_INVALID_ARG); return _ret_; } }
#define CHECK_SEARCHING(c) mk_c(c)->check_searching();
inline bool is_expr(Z3_ast a) { return is_expr(to_ast(a)); }
inline bool is_bool_expr(Z3_context c, Z3_ast a) { return is_expr(a) && mk_c(c)->m().is_bool(to_expr(a)); }
#define CHECK_FORMULA(_a_, _ret_) { if (_a_ == 0 || !CHECK_REF_COUNT(_a_) || !is_bool_expr(c, _a_)) { SET_ERROR_CODE(Z3_INVALID_ARG); return _ret_; } }
inline void check_sorts(Z3_context c, ast * n) { mk_c(c)->check_sorts(n); }

#endif
