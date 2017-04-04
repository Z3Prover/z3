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
#ifndef API_CONTEXT_H_
#define API_CONTEXT_H_

#include"z3.h"
#include"ast.h"
#include"api_util.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"seq_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"fpa_decl_plugin.h"
#include"smt_kernel.h"
#include"smt_params.h"
#include"event_handler.h"
#include"tactic_manager.h"
#include"context_params.h"
#include"api_polynomial.h"
#include"hashtable.h"

namespace smtlib {
    class parser;
};

namespace realclosure {
    class manager;
};

namespace api {
       

    class context : public tactic_manager {
        struct add_plugins {  add_plugins(ast_manager & m); };
        context_params             m_params;
        bool                       m_user_ref_count; //!< if true, the user is responsible for managing referenc counters.
        scoped_ptr<ast_manager>    m_manager;
        add_plugins                m_plugins;

        arith_util                 m_arith_util;
        bv_util                    m_bv_util;
        datalog::dl_decl_util      m_datalog_util;
        fpa_util                   m_fpa_util;
        datatype_util              m_dtutil;
        seq_util                   m_sutil;

        // Support for old solver API
        smt_params                 m_fparams;
        // -------------------------------

        ast_ref_vector             m_last_result; //!< used when m_user_ref_count == true
        ast_ref_vector             m_ast_trail;   //!< used when m_user_ref_count == false

        ref<api::object>           m_last_obj; //!< reference to the last API object returned by the APIs
        u_map<api::object*>        m_allocated_objects; // !< table containing current set of allocated API objects
        unsigned_vector            m_free_object_ids;   // !< free list of identifiers available for allocated objects.

        family_id                  m_basic_fid;
        family_id                  m_array_fid;
        family_id                  m_arith_fid;
        family_id                  m_bv_fid;
        family_id                  m_dt_fid;
        family_id                  m_datalog_fid;
        family_id                  m_pb_fid;
        family_id                  m_fpa_fid;
        family_id                  m_seq_fid;
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
        
        context(context_params * p, bool user_ref_count = false);
        ~context();
        ast_manager & m() const { return *(m_manager.get()); }

        context_params & params() { return m_params; }
        bool produce_proofs() const { return m().proofs_enabled(); }
        bool produce_models() const { return m_params.m_model; }
        bool produce_unsat_cores() const { return m_params.m_unsat_core; }
        bool use_auto_config() const { return m_params.m_auto_config; }
        unsigned get_timeout() const { return m_params.m_timeout; }
        unsigned get_rlimit() const { return m_params.m_rlimit; }
        arith_util & autil() { return m_arith_util; }
        bv_util & bvutil() { return m_bv_util; }
        datalog::dl_decl_util & datalog_util() { return m_datalog_util; }
        fpa_util & fpautil() { return m_fpa_util; }
        datatype_util& dtutil() { return m_dtutil; }
        seq_util& sutil() { return m_sutil; }
        family_id get_basic_fid() const { return m_basic_fid; }
        family_id get_array_fid() const { return m_array_fid; }
        family_id get_arith_fid() const { return m_arith_fid; }
        family_id get_bv_fid() const { return m_bv_fid; }
        family_id get_dt_fid() const { return m_dt_fid; }
        family_id get_datalog_fid() const { return m_datalog_fid; }
        family_id get_pb_fid() const { return m_pb_fid; }
        family_id get_fpa_fid() const { return m_fpa_fid; }
        family_id get_seq_fid() const { return m_seq_fid; }
        datatype_decl_plugin * get_dt_plugin() const { return m_dt_plugin; }

        Z3_error_code get_error_code() const { return m_error_code; }
        void reset_error_code() { m_error_code = Z3_OK; }
        void set_error_code(Z3_error_code err);
        void set_error_handler(Z3_error_handler h) { m_error_handler = h; }
        // Sign an error if solver is searching
        void check_searching();

        unsigned add_object(api::object* o);
        void del_object(api::object* o);

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
        // void persist_ast(ast * n, unsigned num_scopes);

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

        void check_sorts(ast * n);

        // ------------------------
        //
        // Polynomial manager & caches
        //
        // -----------------------
    private:
        reslimit                   m_limit;
        pmanager                   m_pmanager;
    public:
        polynomial::manager & pm() { return m_pmanager.pm(); }
        reslimit & poly_limit() { return m_limit; }
        
        // ------------------------
        //
        // RCF manager
        //
        // -----------------------
    private:
        unsynch_mpq_manager              m_rcf_qm;
        scoped_ptr<realclosure::manager> m_rcf_manager;
    public:
        realclosure::manager & rcfm();

        // ------------------------
        //
        // Solver interface for backward compatibility 
        //
        // ------------------------
        smt_params & fparams() { return m_fparams; }

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
#define CHECK_IS_EXPR(_p_, _ret_) { if (_p_ == 0 || !is_expr(_p_)) { SET_ERROR_CODE(Z3_INVALID_ARG); return _ret_; } }
inline bool is_bool_expr(Z3_context c, Z3_ast a) { return is_expr(a) && mk_c(c)->m().is_bool(to_expr(a)); }
#define CHECK_FORMULA(_a_, _ret_) { if (_a_ == 0 || !CHECK_REF_COUNT(_a_) || !is_bool_expr(c, _a_)) { SET_ERROR_CODE(Z3_INVALID_ARG); return _ret_; } }
inline void check_sorts(Z3_context c, ast * n) { mk_c(c)->check_sorts(n); }

#endif
