/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_context.cpp

Abstract:
    Interface of Z3 with "external world".

    It was called _Z3_context

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<typeinfo>
#include "api/api_context.h"
#include "util/z3_version.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "api/api_log_macros.h"
#include "api/api_util.h"
#include "ast/reg_decl_plugins.h"
#include "math/realclosure/realclosure.h"

// The install_tactics procedure is automatically generated
void install_tactics(tactic_manager & ctx);

namespace api {

    object::object(context& c): m_ref_count(0), m_context(c) { this->m_id = m_context.add_object(this); }

    void object::inc_ref() { m_ref_count++; }

    void object::dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) m_context.del_object(this); }
    
    unsigned context::add_object(api::object* o) {
        unsigned id = m_allocated_objects.size();
        if (!m_free_object_ids.empty()) {
            id = m_free_object_ids.back();
            m_free_object_ids.pop_back();
        }
        m_allocated_objects.insert(id, o);
        return id;
    }

    void context::del_object(api::object* o) {
        m_free_object_ids.push_back(o->id());
        m_allocated_objects.remove(o->id());
        dealloc(o);
    }

    static void default_error_handler(Z3_context ctx, Z3_error_code c) {
        printf("Error: %s\n", Z3_get_error_msg(ctx, c));
        exit(1);
    }

    context::add_plugins::add_plugins(ast_manager & m) {
        reg_decl_plugins(m);
    }

    // ------------------------
    //
    // Core
    //
    // ------------------------

    context::context(context_params * p, bool user_ref_count):
        m_params(p != nullptr ? *p : context_params()),
        m_user_ref_count(user_ref_count),
        m_manager(m_params.mk_ast_manager()),
        m_plugins(m()),
        m_arith_util(m()),
        m_bv_util(m()),
        m_datalog_util(m()),
        m_fpa_util(m()),
        m_sutil(m()),
        m_last_result(m()),
        m_ast_trail(m()),
        m_pmanager(m_limit) {

        m_error_code = Z3_OK;
        m_print_mode = Z3_PRINT_SMTLIB_FULL;
        m_searching  = false;
        

        m_interruptable = nullptr;
        m_error_handler = &default_error_handler;

        m_basic_fid = m().get_basic_family_id();
        m_arith_fid = m().mk_family_id("arith");
        m_bv_fid    = m().mk_family_id("bv");
        m_pb_fid    = m().mk_family_id("pb");
        m_array_fid = m().mk_family_id("array");
        m_dt_fid    = m().mk_family_id("datatype");
        m_datalog_fid = m().mk_family_id("datalog_relation");
        m_fpa_fid   = m().mk_family_id("fpa");
        m_seq_fid   = m().mk_family_id("seq");
        m_dt_plugin = static_cast<datatype_decl_plugin*>(m().get_plugin(m_dt_fid));
    
        install_tactics(*this);
    }


    context::~context() {
        m_last_obj = nullptr;
        u_map<api::object*>::iterator it = m_allocated_objects.begin();
        while (it != m_allocated_objects.end()) {
            api::object* val = it->m_value;
            DEBUG_CODE(warning_msg("Uncollected memory: %d: %s", it->m_key, typeid(*val).name()););
            m_allocated_objects.remove(it->m_key);
            dealloc(val);
            it = m_allocated_objects.begin();
        }
    }

    context::set_interruptable::set_interruptable(context & ctx, event_handler & i):
        m_ctx(ctx) {
        #pragma omp critical (set_interruptable) 
        {
            SASSERT(m_ctx.m_interruptable == 0);
            m_ctx.m_interruptable = &i;
        }
    }

    context::set_interruptable::~set_interruptable() {
        #pragma omp critical (set_interruptable) 
        {
            m_ctx.m_interruptable = nullptr;
        }
    }

    void context::interrupt() {
        #pragma omp critical (set_interruptable)
        {
            if (m_interruptable)
                (*m_interruptable)(API_INTERRUPT_EH_CALLER);
            m_limit.cancel();
            m().limit().cancel();
        }
    }
    
    void context::set_error_code(Z3_error_code err, char const* opt_msg) {
        m_error_code = err; 
        if (err != Z3_OK) {
            m_exception_msg.clear();
            if (opt_msg) m_exception_msg = opt_msg;
            invoke_error_handler(err); 
        }
    }

    void context::reset_error_code() { 
        m_error_code = Z3_OK; 
    }



    void context::check_searching() {
        if (m_searching) { 
            set_error_code(Z3_INVALID_USAGE, "cannot use function while searching"); // TBD: error code could be fixed.
        } 
    }

    char * context::mk_external_string(char const * str) {
        m_string_buffer = str?str:"";
        return const_cast<char *>(m_string_buffer.c_str());
    }
    
    char * context::mk_external_string(std::string const & str) {
        m_string_buffer = str;
        return const_cast<char *>(m_string_buffer.c_str());
    }

    expr * context::mk_numeral_core(rational const & n, sort * s) {
        expr* e = nullptr;
        family_id fid  = s->get_family_id();
        if (fid == m_arith_fid) {
            e = m_arith_util.mk_numeral(n, s);
        }
        else if (fid == m_bv_fid) {
            e = m_bv_util.mk_numeral(n, s);
        }
        else if (fid == get_datalog_fid() && n.is_uint64()) {
            uint64_t sz;
            if (m_datalog_util.try_get_size(s, sz) && 
                sz <= n.get_uint64()) {
                invoke_error_handler(Z3_INVALID_ARG);
            }
            e = m_datalog_util.mk_numeral(n.get_uint64(), s);
        }
        else {
            invoke_error_handler(Z3_INVALID_ARG);
        }
        save_ast_trail(e);
        return e;    
    }
        
    expr * context::mk_and(unsigned num_exprs, expr * const * exprs) {
        switch(num_exprs) {
        case 0: 
            return m().mk_true(); 
        case 1: 
            save_ast_trail(exprs[0]);
            return exprs[0];
        default: {
            expr * a = m().mk_and(num_exprs, exprs);
            save_ast_trail(a);
            return a;
        } }
    }


    void context::save_ast_trail(ast * n) {
        SASSERT(m().contains(n));
        if (m_user_ref_count) {
            // Corner case bug: n may be in m_last_result, and this is the only reference to n.
            // When, we execute reset() it is deleted
            // To avoid this bug, I bump the reference counter before reseting m_last_result
            ast_ref node(n, m());
            m_last_result.reset();
            m_last_result.push_back(std::move(node));
        }
        else {
            m_ast_trail.push_back(n);
        }
    }

    void context::save_multiple_ast_trail(ast * n) {
        if (m_user_ref_count)
            m_last_result.push_back(n);
        else
            m_ast_trail.push_back(n);
    }

    void context::reset_last_result() {
        if (m_user_ref_count)
            m_last_result.reset();
        m_last_obj = nullptr;
    }

    void context::save_object(object * r) {
        m_last_obj = r;
    }

    void context::handle_exception(z3_exception & ex) {
        if (ex.has_error_code()) {
            switch(ex.error_code()) {
            case ERR_MEMOUT: 
                set_error_code(Z3_MEMOUT_FAIL, nullptr);
            break;
            case ERR_PARSER: 
                set_error_code(Z3_PARSER_ERROR, ex.msg());
                break;
            case ERR_INI_FILE: 
                set_error_code(Z3_INVALID_ARG, nullptr);
                break;
            case ERR_OPEN_FILE:
                set_error_code(Z3_FILE_ACCESS_ERROR, nullptr);
                break;
            default:
                set_error_code(Z3_INTERNAL_FATAL, nullptr);
                break;
            }
        }
        else {
            set_error_code(Z3_EXCEPTION, ex.msg()); 
        }
    }
    
    void context::invoke_error_handler(Z3_error_code c) {
        if (m_error_handler) {
            if (g_z3_log) {
                // error handler can do crazy stuff such as longjmp
                g_z3_log_enabled = true;
            }
            m_error_handler(reinterpret_cast<Z3_context>(this), c);
        }
    }

    void context::check_sorts(ast * n) {
        if (!m().check_sorts(n)) {
            switch(n->get_kind()) {
            case AST_APP: {
                std::ostringstream buffer;
                app * a = to_app(n);
                buffer << mk_pp(a->get_decl(), m()) << " applied to: ";
                if (a->get_num_args() > 1) buffer << "\n";
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    buffer << mk_bounded_pp(a->get_arg(i), m(), 3) << " of sort ";
                    buffer << mk_pp(m().get_sort(a->get_arg(i)), m()) << "\n";
                }
                warning_msg("%s",buffer.str().c_str());
                break;
            }
            case AST_VAR:
            case AST_QUANTIFIER:
            case AST_SORT:
            case AST_FUNC_DECL:
                break;
            }
            set_error_code(Z3_SORT_ERROR, nullptr);
        }
    }

    // ------------------------
    //
    // RCF manager
    //
    // -----------------------
    realclosure::manager & context::rcfm() {
        if (m_rcf_manager.get() == nullptr) {
            m_rcf_manager = alloc(realclosure::manager, m_limit, m_rcf_qm);
        }
        return *(m_rcf_manager.get());
    }

};


// ------------------------
//
// Context creation API
//
// ------------------------

extern "C" {
    
    Z3_context Z3_API Z3_mk_context(Z3_config c) {
        Z3_TRY;
        LOG_Z3_mk_context(c);
        memory::initialize(UINT_MAX);
        Z3_context r = reinterpret_cast<Z3_context>(alloc(api::context, reinterpret_cast<context_params*>(c), false));
        RETURN_Z3(r);
        Z3_CATCH_RETURN_NO_HANDLE(nullptr);
    }

    Z3_context Z3_API Z3_mk_context_rc(Z3_config c) {
        Z3_TRY;
        LOG_Z3_mk_context_rc(c);
        memory::initialize(UINT_MAX);
        Z3_context r = reinterpret_cast<Z3_context>(alloc(api::context, reinterpret_cast<context_params*>(c), true));
        RETURN_Z3(r);
        Z3_CATCH_RETURN_NO_HANDLE(nullptr);
    }

    void Z3_API Z3_del_context(Z3_context c) {
        Z3_TRY;
        LOG_Z3_del_context(c);
        RESET_ERROR_CODE();
        dealloc(mk_c(c));
        Z3_CATCH;
    }

    void Z3_API Z3_interrupt(Z3_context c) {
        Z3_TRY;
        LOG_Z3_interrupt(c);
        mk_c(c)->interrupt();
        Z3_CATCH;
    }

    void Z3_API Z3_toggle_warning_messages(Z3_bool enabled) {
        LOG_Z3_toggle_warning_messages(enabled);
        enable_warning_messages(enabled != 0);
    }

    void Z3_API Z3_inc_ref(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_inc_ref(c, a);
        RESET_ERROR_CODE();
        mk_c(c)->m().inc_ref(to_ast(a));
        Z3_CATCH;
    }

    void Z3_API Z3_dec_ref(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_dec_ref(c, a);
        RESET_ERROR_CODE();
        if (a && to_ast(a)->get_ref_count() == 0) {
            SET_ERROR_CODE(Z3_DEC_REF_ERROR, nullptr);
            return;
        }
        if (a) {
            mk_c(c)->m().dec_ref(to_ast(a));
        }

        Z3_CATCH;
    }


    void Z3_API Z3_get_version(unsigned * major, 
                               unsigned * minor, 
                               unsigned * build_number, 
                               unsigned * revision_number) {
        LOG_Z3_get_version(major, minor, build_number, revision_number);
        *major           = Z3_MAJOR_VERSION;
        *minor           = Z3_MINOR_VERSION;
        *build_number    = Z3_BUILD_NUMBER;
        *revision_number = Z3_REVISION_NUMBER;
    }

    Z3_string Z3_API Z3_get_full_version(void) {
        LOG_Z3_get_full_version();
        return Z3_FULL_VERSION;
    }

    void Z3_API Z3_enable_trace(Z3_string tag) {
        memory::initialize(UINT_MAX);
        LOG_Z3_enable_trace(tag);
        // Tag is a string that was probably not allocated by Z3. Create a copy using symbol.
        symbol tag_sym(tag);
        enable_trace(tag_sym.bare_str());
    }

    void Z3_API Z3_disable_trace(Z3_string tag) {
        LOG_Z3_disable_trace(tag);
        disable_trace(tag);
    }

    void Z3_API Z3_reset_memory(void) {
        LOG_Z3_reset_memory();
        memory::finalize();
        memory::initialize(0);
    }

    void Z3_API Z3_finalize_memory(void) {
        LOG_Z3_finalize_memory();
        memory::finalize();
    }

    Z3_error_code Z3_API Z3_get_error_code(Z3_context c) {
        LOG_Z3_get_error_code(c);
        return mk_c(c)->get_error_code();
    }

    void Z3_API Z3_set_error_handler(Z3_context c, Z3_error_handler h) {
        RESET_ERROR_CODE();    
        mk_c(c)->set_error_handler(h);
        // [Leo]: using exception handling, we don't need global error handlers anymore
    }

    void Z3_API Z3_set_error(Z3_context c, Z3_error_code e) {
        SET_ERROR_CODE(e, nullptr);
    }

    static char const * _get_error_msg(Z3_context c, Z3_error_code err) {
        if (c) {
            char const* msg = mk_c(c)->get_exception_msg();
            if (msg && *msg) return msg;
        }
        switch(err) {
        case Z3_OK:                return "ok";
        case Z3_SORT_ERROR:        return "type error";
        case Z3_IOB:               return "index out of bounds";
        case Z3_INVALID_ARG:       return "invalid argument";
        case Z3_PARSER_ERROR:      return "parser error";
        case Z3_NO_PARSER:         return "parser (data) is not available";
        case Z3_INVALID_PATTERN:   return "invalid pattern";
        case Z3_MEMOUT_FAIL:       return "out of memory";
        case Z3_FILE_ACCESS_ERROR: return "file access error";
        case Z3_INTERNAL_FATAL:    return "internal error";
        case Z3_INVALID_USAGE:     return "invalid usage";
        case Z3_DEC_REF_ERROR:     return "invalid dec_ref command";
        case Z3_EXCEPTION:         return "Z3 exception";
        default:                   return "unknown";
        }
    }


    Z3_API char const * Z3_get_error_msg(Z3_context c, Z3_error_code err) {
        LOG_Z3_get_error_msg(c, err);
        return _get_error_msg(c, err);
    }

    Z3_API char const * Z3_get_error_msg_ex(Z3_context c, Z3_error_code err) {
        return Z3_get_error_msg(c, err);
    }


    void Z3_API Z3_set_ast_print_mode(Z3_context c, Z3_ast_print_mode mode) {
        Z3_TRY;
        LOG_Z3_set_ast_print_mode(c, mode);
        RESET_ERROR_CODE();
        mk_c(c)->set_print_mode(mode);
        Z3_CATCH;
    }
    
};

Z3_API ast_manager& Z3_get_manager(Z3_context c) {
    return mk_c(c)->m();
}


