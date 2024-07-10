
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

    void arith_plugin::init_bool_var(sat::bool_var v) {
        if (!m_arith) {
            try {
                m_arith64->init_bool_var(v);
                return;
            }
            catch (overflow_exception&) {
                m_arith = alloc(arith_base<rational>, ctx);
                for (auto e : m_shared)
                    m_arith->set_shared(e);
                return; // initialization happens on check-sat calls
            }
        }
        m_arith->init_bool_var(v);

    }

    void arith_plugin::register_term(expr* e) {
        if (!m_arith) {
            try {
                m_arith64->register_term(e);
                return;
            }
            catch (overflow_exception&) {
                m_arith = alloc(arith_base<rational>, ctx);
                for (auto e : m_shared)
                    m_arith->set_shared(e);
            }
        }
        m_arith->register_term(e);
    }

    expr_ref arith_plugin::get_value(expr* e) {
        if (!m_arith) {
            try {
                return m_arith64->get_value(e);
            }
            catch (overflow_exception&) {
                m_arith = alloc(arith_base<rational>, ctx);
                for (auto e : m_shared)
                    m_arith->set_shared(e);
            }
        }
        return m_arith->get_value(e);
    }

    lbool arith_plugin::check() {
        if (!m_arith) {
            try {
                return m_arith64->check();
            }
            catch (overflow_exception&) {
                m_arith = alloc(arith_base<rational>, ctx);
                for (auto e : m_shared)
                    m_arith->set_shared(e);
            }
        }            
        return m_arith->check();
    }

    bool arith_plugin::is_sat() {
        if (!m_arith) 
            return m_arith64->is_sat();
        return m_arith->is_sat();
    }

    void arith_plugin::on_rescale() {
        if (m_arith) 
            m_arith->on_rescale();
        else 
            m_arith64->on_rescale();
    }

    void arith_plugin::on_restart() {
        if (m_arith) 
            m_arith->on_restart();
        else 
            m_arith64->on_restart();        
    }

    std::ostream& arith_plugin::display(std::ostream& out) const {
        if (m_arith) 
            return m_arith->display(out);
        else
            return m_arith64->display(out);                
    }

    void arith_plugin::mk_model(model& mdl) {
        if (m_arith) 
            m_arith->mk_model(mdl);        
        else 
            m_arith64->mk_model(mdl);        
    }

    void arith_plugin::set_shared(expr* e) {
        if (m_arith)
            m_arith->set_shared(e);
        else {
            m_arith64->set_shared(e);
            m_shared.push_back(e);
        }
    }

    void arith_plugin::set_value(expr* e, expr* v) {
        if (m_arith)
            m_arith->set_value(e, v);
        else 
            m_arith->set_value(e, v);
    }
}
