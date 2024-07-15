
#include "ast/sls/sls_bv.h"

namespace sls {

    bv_plugin::bv_plugin(context& ctx): 
        plugin(ctx),
        bv(m),
        m_terms(m),
        m_eval(m)
    {}

    void bv_plugin::init_bool_var(sat::bool_var v) {
    }
    
    void bv_plugin::register_term(expr* e) {
    }
    
    expr_ref bv_plugin::get_value(expr* e) {
        return expr_ref(m);
    }
    
    lbool bv_plugin::check() {
        return l_undef;
    }
    
    bool bv_plugin::is_sat() {
        return false;
    }
    
    void bv_plugin::reset() {
    }
    
    void bv_plugin::on_rescale() {

    }
    
    void bv_plugin::on_restart() {
    }
    
    std::ostream& bv_plugin::display(std::ostream& out) const {
        return out;
    }
    
    void bv_plugin::mk_model(model& mdl) {

    }
    
    void bv_plugin::set_shared(expr* e) {

    }
    
    void bv_plugin::set_value(expr* e, expr* v) {

    }

    std::pair<bool, app*> bv_plugin::next_to_repair() {
        app* e = nullptr;
        if (m_repair_down != UINT_MAX) {
            e = m_terms.term(m_repair_down);
            m_repair_down = UINT_MAX;
            return { true, e };
        }

        if (!m_repair_up.empty()) {
            unsigned index = m_repair_up.elem_at(ctx.rand(m_repair_up.size()));
            m_repair_up.remove(index);
            e = m_terms.term(index);
            return { false, e };
        }

        while (!m_repair_roots.empty()) {
            unsigned index = m_repair_roots.elem_at(ctx.rand(m_repair_roots.size()));
            e = m_terms.term(index);
            if (m_terms.is_assertion(e) && !m_eval.bval1(e)) {
                SASSERT(m_eval.bval0(e));
                return { true, e };
            }
            if (!m_eval.re_eval_is_correct(e)) {
                init_repair_goal(e);
                return { true, e };
            }
            m_repair_roots.remove(index);
        }

        return { false, nullptr };
    }

    void bv_plugin::init_repair_goal(app* e) {
        m_eval.init_eval(e);
    }

}
