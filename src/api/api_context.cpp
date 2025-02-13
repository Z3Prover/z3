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
#include "util/debug.h"
#include "util/z3_version.h"
#include "api/api_context.h"
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

    void object::inc_ref() { ++m_ref_count; }

    void object::dec_ref() { SASSERT(m_ref_count > 0); if (--m_ref_count == 0) m_context.del_object(this); }
    
    unsigned context::add_object(api::object* o) {
        flush_objects();
        unsigned id = m_allocated_objects.size();
        if (!m_free_object_ids.empty()) {
            id = m_free_object_ids.back();
            m_free_object_ids.pop_back();
        }
        m_allocated_objects.insert(id, o);
        return id;
    }

    void context::del_object(api::object* o) {
        if (!o)
            return;
#ifndef SINGLE_THREAD
        if (m_concurrent_dec_ref) {
            lock_guard lock(m_mux);
            m_objects_to_flush.push_back(o);
        }
        else
#endif
        {
            m_free_object_ids.push_back(o->id());
            m_allocated_objects.remove(o->id());
            dealloc(o);
        }
    }

    void context::dec_ref(ast* a) {
#ifndef SINGLE_THREAD
        if (m_concurrent_dec_ref) {
            lock_guard lock(m_mux);
            m_asts_to_flush.push_back(a);
        }
        else
#endif
            m().dec_ref(a);
    }

    // flush_objects can only be called in the main thread.
    // This ensures that the calls to m().dec_ref() and dealloc(o)
    // only happens in the main thread.
    // Calls to dec_ref are allowed in other threads when m_concurrent_dec_ref is
    // set to true.
    void context::flush_objects() {
#ifndef SINGLE_THREAD
        if (!m_concurrent_dec_ref)
            return;        
        {
            lock_guard lock(m_mux);
            if (m_asts_to_flush.empty() && m_objects_to_flush.empty())
                return;
            m_asts_to_flush2.swap(m_asts_to_flush);
            m_objects_to_flush2.swap(m_objects_to_flush);
        }
        for (ast* a : m_asts_to_flush2)
            m().dec_ref(a);
        for (auto* o : m_objects_to_flush2) {
            m_free_object_ids.push_back(o->id());
            m_allocated_objects.remove(o->id());
            dealloc(o);
        }
        m_objects_to_flush2.reset();
        m_asts_to_flush2.reset();
#endif
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

    context::context(ast_context_params * p, bool user_ref_count):
        m_params(p != nullptr ? *p : ast_context_params()),
        m_user_ref_count(user_ref_count),
        m_manager(m_params.mk_ast_manager()),
        m_plugins(m()),
        m_arith_util(m()),
        m_bv_util(m()),
        m_datalog_util(m()),
        m_fpa_util(m()),
        m_sutil(m()),
        m_recfun(m()),
        m_ast_trail(m()),
        m_pmanager(m_limit) {

        m_error_code = Z3_OK;
        m_print_mode = Z3_PRINT_SMTLIB_FULL;
        
        m_error_handler = &default_error_handler;

        m_bv_fid    = m().mk_family_id("bv");
        m_pb_fid    = m().mk_family_id("pb");
        m_array_fid = m().mk_family_id("array");
        m_dt_fid    = m().mk_family_id("datatype");
        m_datalog_fid = m().mk_family_id("datalog_relation");
        m_fpa_fid   = m().mk_family_id("fpa");
        m_seq_fid   = m().mk_family_id("seq");
	    m_char_fid   = m().mk_family_id("char");
        m_special_relations_fid   = m().mk_family_id("specrels");
        m_dt_plugin = static_cast<datatype_decl_plugin*>(m().get_plugin(m_dt_fid));
    
        install_tactics(*this);
    }


    context::~context() {
        if (m_parser)
            smt2::free_parser(m_parser);
        m_last_obj = nullptr;
        flush_objects();
        for (auto& kv : m_allocated_objects) {
            api::object* val = kv.m_value;
#ifdef SINGLE_THREAD
# define m_concurrent_dec_ref false
#endif
            DEBUG_CODE(if (!m_concurrent_dec_ref) warning_msg("Uncollected memory: %d: %s", kv.m_key, typeid(*val).name()););
            dealloc(val);
        }
        if (m_params.owns_manager())
            m_manager.detach();

    }

    context::set_interruptable::set_interruptable(context & ctx, event_handler & i):
        m_ctx(ctx) {
        lock_guard lock(ctx.m_mux);
        m_ctx.m_interruptable.push_back(& i);
    }

    context::set_interruptable::~set_interruptable() {
        lock_guard lock(m_ctx.m_mux);
        m_ctx.m_interruptable.pop_back();
    }

    void context::interrupt() {
        lock_guard lock(m_mux);
        for (auto * eh : m_interruptable)
            (*eh)(API_INTERRUPT_EH_CALLER);
        m_limit.cancel();
        m().limit().cancel();        
    }
    
    void context::set_error_code(Z3_error_code err, char const* opt_msg) {
        m_error_code = err; 
        if (err != Z3_OK) {
            m_exception_msg.clear();
            if (opt_msg) m_exception_msg = opt_msg;
            invoke_error_handler(err); 
        }
    }

    void context::set_error_code(Z3_error_code err, std::string &&opt_msg) {
        m_error_code = err;
        if (err != Z3_OK) {
            m_exception_msg = std::move(opt_msg);
            invoke_error_handler(err);
        }
    }
    
    const char * context::mk_external_string(std::string && str) {
        m_string_buffer = std::move(str);
        return m_string_buffer.c_str();
    }

    expr * context::mk_numeral_core(rational const & n, sort * s) {
        expr* e = nullptr;
        family_id fid  = s->get_family_id();
        if (fid == arith_family_id) {
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
        else if (fid == m_fpa_fid) {
            scoped_mpf tmp(fpautil().fm());
            fpautil().fm().set(tmp, fpautil().get_ebits(s), fpautil().get_sbits(s), n.get_double());
            e = fpautil().mk_value(tmp);
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
            // Corner case bug: n may be in m_ast_trail, and this is the only reference to n.
            // When, we execute reset() it is deleted
            // To avoid this bug, I bump the reference counter before resetting m_ast_trail
            ast_ref node(n, m());
            m_ast_trail.reset();
            m_ast_trail.push_back(std::move(node));
        }
        else {
            m_ast_trail.push_back(n);
        }
    }

    void context::save_multiple_ast_trail(ast * n) {
        m_ast_trail.push_back(n);
    }

    void context::reset_last_result() {
        if (m_user_ref_count)
            m_ast_trail.reset();
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
                set_error_code(Z3_PARSER_ERROR, ex.what());
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
            set_error_code(Z3_EXCEPTION, ex.what()); 
        }
    }
    
    void context::invoke_error_handler(Z3_error_code c) {
        if (m_error_handler) {
            // error handler can do crazy stuff such as longjmp
            ctx_enable_logging();
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
                if (a->get_num_args() > 1) buffer << '\n';
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    buffer << mk_bounded_pp(a->get_arg(i), m(), 3) << " of sort ";
                    buffer << mk_pp(a->get_arg(i)->get_sort(), m()) << '\n';
                }
                auto str = std::move(buffer).str();
                warning_msg("%s", str.c_str());
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
        Z3_context r = reinterpret_cast<Z3_context>(alloc(api::context, reinterpret_cast<ast_context_params*>(c), false));
        RETURN_Z3(r);
        Z3_CATCH_RETURN_NO_HANDLE(nullptr);
    }

    Z3_context Z3_API Z3_mk_context_rc(Z3_config c) {
        Z3_TRY;
        LOG_Z3_mk_context_rc(c);
        memory::initialize(UINT_MAX);
        set_default_exit_action(exit_action::throw_exception);
        Z3_context r = reinterpret_cast<Z3_context>(alloc(api::context, reinterpret_cast<ast_context_params*>(c), true));
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

    void Z3_API Z3_enable_concurrent_dec_ref(Z3_context c) {
        Z3_TRY;
        LOG_Z3_enable_concurrent_dec_ref(c);
        mk_c(c)->enable_concurrent_dec_ref();
        Z3_CATCH;
    }    

    void Z3_API Z3_toggle_warning_messages(bool enabled) {
        LOG_Z3_toggle_warning_messages(enabled);
        enable_warning_messages(enabled != 0);
    }

    void Z3_API Z3_inc_ref(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_inc_ref(c, a);
        RESET_ERROR_CODE();
        mk_c(c)->flush_objects();
        mk_c(c)->m().inc_ref(to_ast(a));
        Z3_CATCH;
    }

    void Z3_API Z3_dec_ref(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_dec_ref(c, a);
        if (a && to_ast(a)->get_ref_count() == 0) {
            // the error is unchecked (but should not happen) in GC'ed wrappers
            RESET_ERROR_CODE();
            SET_ERROR_CODE(Z3_DEC_REF_ERROR, nullptr);
            return;
        }
        if (a) {
            mk_c(c)->dec_ref(to_ast(a));
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
        memory::finalize(false);
        memory::initialize(0);
    }

    void Z3_API Z3_finalize_memory(void) {
        LOG_Z3_finalize_memory();
        memory::finalize(true);
    }

    Z3_error_code Z3_API Z3_get_error_code(Z3_context c) {
        LOG_Z3_get_error_code(c);
        return mk_c(c)->get_error_code();
    }

    void Z3_API Z3_set_error_handler(Z3_context c, Z3_error_handler h) {
        RESET_ERROR_CODE();    
        mk_c(c)->set_error_handler(h);
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

    Z3_string Z3_API Z3_get_error_msg(Z3_context c, Z3_error_code err) {
        LOG_Z3_get_error_msg(c, err);
        return _get_error_msg(c, err);
    }

    void Z3_API Z3_set_ast_print_mode(Z3_context c, Z3_ast_print_mode mode) {
        Z3_TRY;
        LOG_Z3_set_ast_print_mode(c, mode);
        RESET_ERROR_CODE();
        mk_c(c)->set_print_mode(mode);
        Z3_CATCH;
    }
    
};
