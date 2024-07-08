
#include "ast/sls/sls_bv.h"

namespace sls {

    bv_plugin::bv_plugin(context& ctx): 
        plugin(ctx),
        bv(m),
        m_terms(ctx),
        m_eval(m_terms, ctx)
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


        return { false, nullptr };
    }

}
