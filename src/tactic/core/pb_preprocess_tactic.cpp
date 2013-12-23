/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_preprocess_tactic.cpp

Abstract:

    Pre-process pseudo-Boolean inequalities using 
    generalized Davis Putnam (resolution) to eliminate variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-23

Notes:

--*/
#include "pb_preprocess_tactic.h"
#include "tactical.h"
#include "for_each_expr.h"
#include "pb_decl_plugin.h"

class pb_preprocess_tactic : public tactic {
    struct rec { unsigned pos, neg; rec() { pos = neg = 0; } };
    typedef obj_map<expr, rec> var_map;
    ast_manager&     m;
    pb_util          pb;
    var_map          m_vars;    
    ptr_vector<app>  m_ge;
    ptr_vector<expr> m_other;

    struct declassifier {
        obj_map<expr, rec>& m_vars;        
        declassifier(obj_map<expr, rec>& v): m_vars(v) {}

        void operator()(app* e) {
            if (m_vars.contains(e)) {
                m_vars.remove(e);
            }
        }
        void operator()(var* e) {}
        void operator()(quantifier* q) {}
    };

public:
    pb_preprocess_tactic(ast_manager& m, params_ref const& p = params_ref()): 
        m(m), pb(m) {}

    virtual ~pb_preprocess_tactic() {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(pb_preprocess_tactic, m);
    }
    
    virtual void operator()(
        goal_ref const & g, 
        goal_ref_buffer & result, 
        model_converter_ref & mc, 
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;

        reset();
        for (unsigned i = 0; i < g->size(); i++) {
            process_vars(g->form(i));
        }

        if (m_ge.empty()) {
            result.push_back(g.get());       
            return;
        }

        for (unsigned i = 0; i < m_ge.size(); ++i) {
            classify_vars(m_ge[i]);
        }

        declassifier dcl(m_vars);
        expr_mark visited;        
        for (unsigned i = 0; !m_vars.empty() && i < m_other.size(); ++i) {
            for_each_expr(dcl, visited, m_other[i]);
        }

        if (m_vars.empty()) {
            result.push_back(g.get());       
            return;
        }
        
        var_map::iterator it = next_resolvent(m_vars.begin()); 
        while (it != m_vars.end()) {
            expr * e = it->m_key;
            it->m_value.pos;
            it->m_value.neg;
            
            it = next_resolvent(it);
        }        

        g->inc_depth();
        result.push_back(g.get());       
    }

    virtual void set_cancel(bool f) {
    }

    virtual void updt_params(params_ref const & p) {
    }

    virtual void cleanup() {
    }

private:

    void reset() {
        m_ge.reset();
        m_other.reset();
        m_vars.reset();
    }

    void process_vars(expr* e) {
        if (pb.is_ge(e) && pure_args(to_app(e))) {
            m_ge.push_back(to_app(e));
        }
        else if (m.is_or(e) && pure_args(to_app(e))) {
            m_ge.push_back(to_app(e));
        }
        else {
            m_other.push_back(e);
        }
    }

    void classify_vars(app* e) {
        expr* r;
        for (unsigned i = 0; i < e->get_num_args(); ++i) {
            if (m.is_true(e) || m.is_false(e)) {
                // no-op
            }
            else if (m.is_not(e, r)) {
                insert(r, false);
            }
            else {
                insert(e, true);
            }
        }
    }

    void insert(expr* e, bool pos) {
        if (!m_vars.contains(e)) {
            m_vars.insert(e, rec());
        }
        if (pos) {
            m_vars.find(e).pos++;
        }
        else {
            m_vars.find(e).neg++;
        }
    }

    bool pure_args(app* a) const {
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr* e = a->get_arg(i);
            m.is_not(e, e);
            if (!is_uninterp_const(e) && !m.is_true(e) && !m.is_false(e)) {
                return false;
            }
        }
        return true;
    }

    var_map::iterator next_resolvent(var_map::iterator it) {
        if (it == m_vars.end()) {
            return it;
        }
        while (it != m_vars.end() && it->m_value.pos != 1 && it->m_value.neg != 1) {
            ++it;
        }
        return it;        
    }
};


tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p) {
    return alloc(pb_preprocess_tactic, m);
}
