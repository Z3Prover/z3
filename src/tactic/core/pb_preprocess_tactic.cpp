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
#include "th_rewriter.h"
#include "expr_substitution.h"
#include "ast_pp.h"

class pb_preprocess_tactic : public tactic {
    struct rec { unsigned_vector pos, neg; rec() { } };
    typedef obj_map<expr, rec> var_map;
    ast_manager&     m;
    pb_util          pb;
    var_map          m_vars;    
    app_ref_vector   m_ge;
    expr_ref_vector  m_other;
    th_rewriter      m_r;
    

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
        m(m), pb(m), m_ge(m), m_other(m), m_r(m) {}

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
        for (unsigned i = 0; i < g->size(); ++i) {
            process_vars(g->form(i));
        }

        if (m_ge.empty()) {
            result.push_back(g.get());       
            return;
        }


        for (unsigned i = 0; i < m_ge.size(); ++i) {
            classify_vars(i, m_ge[i].get());
        }

        declassifier dcl(m_vars);
        expr_mark visited;        
        for (unsigned i = 0; !m_vars.empty() && i < m_other.size(); ++i) {
            for_each_expr(dcl, visited, m_other[i].get());
        }

        if (m_vars.empty()) {
            result.push_back(g.get());       
            return;
        }

        g->inc_depth();        
        var_map::iterator it = next_resolvent(m_vars.begin()); 
        while (it != m_vars.end()) {
            expr * e = it->m_key;
            if (it->m_value.pos.empty()) {                
                replace(it->m_value.neg, e, m.mk_false());
            }
            else if (it->m_value.neg.empty()) {
                replace(it->m_value.pos, e, m.mk_true());
            }
            else if (it->m_value.pos.size() == 1) {
                resolve(it->m_value.pos[0], it->m_value.neg, e, true);
            }
            else if (it->m_value.neg.size() == 1) {
                resolve(it->m_value.neg[0], it->m_value.pos, e, false);                
            }
            else {
                
            }
            ++it;
            it = next_resolvent(it);
            // FIXME: some but not all indices are invalidated.
        }        

        g->reset();
        for (unsigned i = 0; i < m_ge.size(); ++i) {
            g->assert_expr(m_ge[i].get());
        }

        for (unsigned i = 0; i < m_other.size(); ++i) {
            g->assert_expr(m_other[i].get());
        }


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
        expr* r;
        if (is_uninterp_const(e)) {
            m_ge.push_back(to_app(e));
        }
        else if (pb.is_ge(e) && pure_args(to_app(e))) {
            m_ge.push_back(to_app(e));
        }
        else if (m.is_or(e) && pure_args(to_app(e))) {
            m_ge.push_back(to_app(e));
        }
        else if (m.is_not(e, r) && is_uninterp_const(r)) {
            m_ge.push_back(to_app(e));
        }
        else {
            m_other.push_back(e);
        }
    }

    void classify_vars(unsigned idx, app* e) {
        expr* r;
        if (m.is_not(e, r)) {
            insert(idx, r, false);
            return;
        }
        if (is_uninterp_const(e)) {
            insert(idx, e, true);
            return;
        }
        for (unsigned i = 0; i < e->get_num_args(); ++i) {
            expr* arg = e->get_arg(i);
            if (m.is_true(arg) || m.is_false(arg)) {
                // no-op
            }
            else if (m.is_not(arg, r)) {
                insert(idx, r, false);
            }
            else {
                insert(idx, arg, true);
            }
        }
    }

    void insert(unsigned i, expr* e, bool pos) {
        if (!m_vars.contains(e)) {
            m_vars.insert(e, rec());
        }
        if (pos) {
            m_vars.find(e).pos.push_back(i);
        }
        else {
            m_vars.find(e).neg.push_back(i);
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
        while (it != m_vars.end() && it->m_value.pos.size() > 1 && it->m_value.neg.size() > 1) {
            ++it;
        }
        return it;        
    }

    rational get_coeff(unsigned num_args, expr* const* args, rational const* coeffs, expr* e) {
        for (unsigned i = 0; i < num_args; ++i) {
            if (args[i] == e) return coeffs[i];
        }
        return rational::zero();
    }

    void resolve(unsigned idx, unsigned_vector const& positions, expr* e, bool pos) {
        app* fml = m_ge[idx].get();
        if (m.is_true(fml)) {
            return;
        }
        m_r.set_substitution(0);
        expr_ref tmp1(m), tmp2(m), e1(m), e2(m);
        ptr_vector<expr> args;
        vector<rational> coeffs;        
        rational k1, k2, c1, c2;
        if (pos) {
            e1 = e;
            e2 = m.mk_not(e);
        }
        else {
            e1 = m.mk_not(e);
            e2 = e;
        }
        VERIFY(to_ge(fml, args, coeffs, k1));
        c1 = get_coeff(args.size(), args.c_ptr(), coeffs.c_ptr(), e1);
        unsigned sz = coeffs.size();
        for (unsigned i = 0; i < positions.size(); ++i) {
            SASSERT(positions[i] != idx); // rely on simplification
            app* fml2 = m_ge[positions[i]].get();
            if (m.is_true(fml2)) continue;
            VERIFY(to_ge(fml2, args, coeffs, k2));
            c2 = get_coeff(args.size()-sz, args.c_ptr()+sz, coeffs.c_ptr()+sz, e2);
            std::cout << "coeffs: " << c1 << " " << c2 << "\n";
            tmp1 = pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), k1 + k2);
            m_r(tmp1, tmp2);
            TRACE("pb", tout << mk_pp(fml2, m) << " -> " << tmp2 << "\n";);
            IF_VERBOSE(1, verbose_stream() << mk_pp(fml2, m) << " -> " << tmp2 << "\n";);
#if 0
            m_ge[positions[i]] = tmp2;
#endif
            args.resize(sz);
            coeffs.resize(sz);
        }
        
        // m_ge[idx] = m.mk_true();
    }

    bool to_ge(app* e, ptr_vector<expr>& args, vector<rational>& coeffs, rational& k) {
        expr* r;
        if (is_uninterp_const(e)) {
            args.push_back(e);
            coeffs.push_back(rational::one());
            k = rational::one();
        }
        else if (m.is_not(e, r) && is_uninterp_const(r)) {
            args.push_back(e);
            coeffs.push_back(rational::one());
            k = rational::one();
        }
        else if (pb.is_ge(e)) {
            SASSERT(pure_args(e));
            for (unsigned i = 0; i < e->get_num_args(); ++i) {
                args.push_back(e->get_arg(i));
                coeffs.push_back(pb.get_coeff(e, i));
            }
            k = pb.get_k(e);
        }
        else if (m.is_or(e)) {
            SASSERT(pure_args(e));
            for (unsigned i = 0; i < e->get_num_args(); ++i) {
                args.push_back(e->get_arg(i));
                coeffs.push_back(rational::one());
            }
            k = rational::one();
        }
        else {
            return false;
        }
        return true;
    }

    void replace(unsigned_vector const& positions, expr* e, expr* v) {
        expr_substitution sub(m);
        sub.insert(e, v);
        expr_ref tmp(m);
        m_r.set_substitution(&sub);
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx = positions[i];
            if (!m.is_true(m_ge[idx].get())) {
                m_r(m_ge[idx].get(), tmp);
                TRACE("pb", tout << mk_pp(m_ge[idx].get(), m) << " -> " << tmp 
                      << " by " << mk_pp(e, m) << " |-> " << mk_pp(v, m) << "\n";);
                m_ge[idx] = to_app(tmp);
            }
        }
    }
};


tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p) {
    return alloc(pb_preprocess_tactic, m);
}
