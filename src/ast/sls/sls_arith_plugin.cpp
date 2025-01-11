
/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    sls_arith_plugin.cpp

Abstract:

    Local search dispatch for NIA

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/

#include "ast/sls/sls_arith_plugin.h"
#include "ast/ast_ll_pp.h"

namespace sls {

#define WITH_FALLBACK(_fn_) \
    if (m_arith64) { \
        try {\
            return m_arith64->_fn_;\
        }\
        catch (overflow_exception&) {\
            IF_VERBOSE(1, verbose_stream() << "revert to bignum solver " << #_fn_ << "\n");\
            init_backup();\
        }\
    }\
    return m_arith->_fn_; \

#define APPLY_BOTH(_fn_) \
    if (m_arith64) { \
        try {\
            m_arith64->_fn_;\
        }\
        catch (overflow_exception&) {\
            IF_VERBOSE(1, verbose_stream() << "revert to bignum solver " << #_fn_ << "\n");\
            init_backup();\
        }\
    }\
    m_arith->_fn_; \

    arith_plugin::arith_plugin(context& ctx) :
        plugin(ctx), m_shared(ctx.get_manager()) {
        m_arith64 = alloc(arith_base<checked_int64<true>>, ctx);
        m_arith = alloc(arith_base<rational>, ctx);
        m_fid = m_arith->fid();
    }

    void arith_plugin::init_backup() {
        m_arith64 = nullptr;
    }

    void arith_plugin::register_term(expr* e) {
        APPLY_BOTH(register_term(e));
    }

    expr_ref arith_plugin::get_value(expr* e) {
        WITH_FALLBACK(get_value(e));
    }

    bool arith_plugin::is_fixed(expr* e, expr_ref& value) {
        WITH_FALLBACK(is_fixed(e, value));
    }

    void arith_plugin::initialize() {
        APPLY_BOTH(initialize());
    }

    void arith_plugin::start_propagation() {
        WITH_FALLBACK(start_propagation());
    }

    void arith_plugin::propagate_literal(sat::literal lit) {
        WITH_FALLBACK(propagate_literal(lit));
    }

    bool arith_plugin::propagate() {
        WITH_FALLBACK(propagate());
    }

    bool arith_plugin::is_sat() {
        WITH_FALLBACK(is_sat());
    }

    void arith_plugin::on_rescale() {
        APPLY_BOTH(on_rescale());
    }

    void arith_plugin::on_restart() {
        WITH_FALLBACK(on_restart());       
    }

    std::ostream& arith_plugin::display(std::ostream& out) const {     
        if (m_arith64) 
            return m_arith64->display(out);
        else
            return m_arith->display(out);                
    }

    bool arith_plugin::repair_down(app* e) {
        WITH_FALLBACK(repair_down(e));
    }

    void arith_plugin::repair_up(app* e) {
        WITH_FALLBACK(repair_up(e));
    }

    void arith_plugin::repair_literal(sat::literal lit) {
        WITH_FALLBACK(repair_literal(lit));
    }

    bool arith_plugin::set_value(expr* e, expr* v) {
        WITH_FALLBACK(set_value(e, v));
    }

    void arith_plugin::collect_statistics(statistics& st) const {
        if (m_arith64) 
            m_arith64->collect_statistics(st);
        else 
            m_arith->collect_statistics(st);
    }

    void arith_plugin::reset_statistics() {
        if (m_arith) 
            m_arith->reset_statistics();
        if (m_arith64)
            m_arith64->reset_statistics();
    }
}
