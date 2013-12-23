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
    unsigned_vector  m_ge;
    unsigned_vector  m_other;
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
        m(m), pb(m), m_r(m) {}

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
            process_vars(i, g->form(i));
        }

        if (m_ge.empty()) {
            result.push_back(g.get());       
            return;
        }

        for (unsigned i = 0; i < m_ge.size(); ++i) {
            classify_vars(i, to_app(g->form(m_ge[i])));
        }

        declassifier dcl(m_vars);
        expr_mark visited;        
        for (unsigned i = 0; !m_vars.empty() && i < m_other.size(); ++i) {
            for_each_expr(dcl, visited, g->form(m_other[i]));
        }

        if (m_vars.empty()) {
            result.push_back(g.get());       
            return;
        }

        g->inc_depth();        
        // first eliminate variables
        var_map::iterator it = next_resolvent(m_vars.begin()); 
        while (it != m_vars.end()) {
            expr * e = it->m_key;
            rec const& r = it->m_value;
            if (r.pos.empty()) {                
                replace(r.neg, e, m.mk_false(), g);
            }
            else if (r.neg.empty()) {
                replace(r.pos, e, m.mk_true(), g);
            }
            ++it;
            it = next_resolvent(it);
        }        
        // now resolve clauses.
        it = next_resolvent(m_vars.begin());
        while (it != m_vars.end()) {
            expr * e = it->m_key;
            rec const& r = it->m_value;
            if (r.pos.size() == 1) {
                resolve(r.pos[0], r.neg, e, true, g);
            }
            else if (r.neg.size() == 1) {
                resolve(r.neg[0], r.pos, e, false, g);                
            }
            ++it;
            it = next_resolvent(it);
        }


        g->elim_true();

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


    void process_vars(unsigned i, expr* e) {
        expr* r;
        if (is_uninterp_const(e)) {
            m_ge.push_back(i);
        }
        else if (pb.is_ge(e) && pure_args(to_app(e))) {
            m_ge.push_back(i);
        }
        else if (m.is_or(e) && pure_args(to_app(e))) {
            m_ge.push_back(i);
        }
        else if (m.is_not(e, r) && is_uninterp_const(r)) {
            m_ge.push_back(i);
        }
        else {
            m_other.push_back(i);
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

    //
    // one of the formulas are replaced by T after resolution
    // so if there is a pointer into that formula, we can no
    // longer assume variables have unique occurrences.
    //
    bool is_valid(unsigned_vector const& positions, goal_ref const& g) const {
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx = positions[i];
            if (m.is_true(g->form(idx))) return false;
        }
        return true;
    }

    bool is_reduction(unsigned_vector const& pos, app* fml, goal_ref const& g) {
        unsigned sz = fml->get_num_args();
        for (unsigned i = 0; i < pos.size(); ++i) {
            if (!is_app(g->form(pos[i]))) return false;
            if (to_app(g->form(pos[i]))->get_num_args() < sz) return false;
        }
        return true;
    }

    void resolve(unsigned idx1, unsigned_vector const& positions, expr* e, bool pos, goal_ref const& g) {
        if (!is_app(g->form(idx1))) {
            return;
        }
        app* fml = to_app(g->form(idx1));
        if (m.is_true(fml)) {
            return;
        }
        if (!is_valid(positions, g)) {
            return;
        }
        if (positions.size() > 1 && !is_reduction(positions, fml, g)) {
            return;
        }
        IF_VERBOSE(1, verbose_stream() << "resolving: " << mk_pp(fml, m) << "\n";);
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
        if (c1.is_zero()) {
            return;
        }
        unsigned sz = coeffs.size();
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx2 = positions[i];
            if (idx2 == idx1) {
                continue;
            }
            app* fml2 = to_app(g->form(idx2));
            if (m.is_true(fml2)) continue;
            VERIFY(to_ge(fml2, args, coeffs, k2));
            c2 = get_coeff(args.size()-sz, args.c_ptr()+sz, coeffs.c_ptr()+sz, e2);
            if (!c2.is_zero()) {
                rational m1(1), m2(1);
                if (c1 != c2) {
                    rational lc = lcm(c1, c2);
                    m1 = lc/c1;
                    m2 = lc/c2;
                    for (unsigned j = 0; j < sz; ++j) {
                        coeffs[j] *= m1;
                    }
                    for (unsigned j = sz; j < args.size(); ++j) {
                        coeffs[j] *= m2;
                    }
                }
                tmp1 = pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), m1*k1 + m2*k2);
                m_r(tmp1, tmp2);
                TRACE("pb", tout << "to\n" << mk_pp(fml2, m) << " -> " << tmp2 << "\n";);
                IF_VERBOSE(1, verbose_stream() << mk_pp(fml2, m) << " -> " << tmp2 << "\n";);

                g->update(idx2, tmp2); // proof & dependencies

                if (!m1.is_one()) {
                    for (unsigned j = 0; j < sz; ++j) {
                        coeffs[j] /= m1;
                    }
                }
            }
            args.resize(sz);
            coeffs.resize(sz);
        }
        g->update(idx1, m.mk_true()); // proof & dependencies
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

    void replace(unsigned_vector const& positions, expr* e, expr* v, goal_ref const& g) {
        if (!is_valid(positions, g)) return;
        expr_substitution sub(m);
        sub.insert(e, v);
        expr_ref tmp(m);
        m_r.set_substitution(&sub);        
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx = positions[i];
            expr* f = g->form(idx);
            if (!m.is_true(f)) {
                m_r(f, tmp);
                TRACE("pb", tout << mk_pp(f, m) << " -> " << tmp 
                      << " by " << mk_pp(e, m) << " |-> " << mk_pp(v, m) << "\n";);
                g->update(idx, tmp); // proof & dependencies.
            }
        }
    }
};


tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p) {
    return alloc(pb_preprocess_tactic, m);
}
