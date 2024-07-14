
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

    void arith_plugin::init_backup() {
        m_arith = alloc(arith_base<rational>, ctx);
        m_arith->initialize();
    }

    void arith_plugin::register_term(expr* e) {
        if (!m_arith) {
            try {
                m_arith64->register_term(e);
                return;
            }
            catch (overflow_exception&) {
                init_backup();
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
                init_backup();
            }
        }
        return m_arith->get_value(e);
    }

    void arith_plugin::initialize() {
        if (m_arith) 
            m_arith->initialize();
        else 
            m_arith64->initialize();
    }

    void arith_plugin::propagate_literal(sat::literal lit) {
        if (!m_arith) {
            try {
                m_arith64->propagate_literal(lit);
                return;
            }
            catch (overflow_exception&) {
                init_backup();
            }
        }
        m_arith->propagate_literal(lit);
    }

    bool arith_plugin::propagate() {
        if (!m_arith) {
            try {
                return m_arith64->propagate();
            }
            catch (overflow_exception&) {
                init_backup();
            }
        }
        return m_arith->propagate();
    }

    bool arith_plugin::is_sat() {
        if (m_arith) 
            return m_arith->is_sat();
        else
            return m_arith64->is_sat();
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

    void arith_plugin::repair_down(app* e) {
        if (m_arith) 
            m_arith->repair_down(e);
        else 
            m_arith64->repair_down(e);
    }

    void arith_plugin::repair_up(app* e) {
        if (m_arith)
            m_arith->repair_up(e);
        else
            m_arith64->repair_up(e);
    }

    void arith_plugin::set_value(expr* e, expr* v) {
        if (!m_arith) {
            try {
                m_arith64->set_value(e, v);
                return;
            }
            catch (overflow_exception&) {
                init_backup();
            }
        }
        m_arith->set_value(e, v);
    }
}
