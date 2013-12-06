/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    lia2card_tactic.cpp

Abstract:

    Convert 0-1 integer variables cardinality constraints to built-in cardinality operator.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-11-5

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"ast_pp.h"
#include"expr_safe_replace.h" // NB: should use proof-producing expr_substitute in polished version.
#include"pb_decl_plugin.h"
#include"arith_decl_plugin.h"

class lia2card_tactic : public tactic {
public:
    typedef obj_hashtable<expr> expr_set;
    ast_manager &                    m;
    arith_util                       a;
    params_ref                       m_params;
    pb_util                          m_pb;
    mutable ptr_vector<expr>         m_todo;
    expr_set                         m_01s;

    
    lia2card_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        a(m),
        m_pb(m) {
    }

    virtual ~lia2card_tactic() {
    }
        
    void set_cancel(bool f) {
    }
        
    void updt_params(params_ref const & p) {
        m_params = p;
    }
    
    virtual void operator()(goal_ref const & g, 
                    goal_ref_buffer & result, 
                    model_converter_ref & mc, 
                    proof_converter_ref & pc,
                    expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        m_01s.reset();
        
        tactic_report report("cardinality-intro", *g);
        
        bound_manager bounds(m);
        bounds(*g);
        
        bound_manager::iterator bit = bounds.begin(), bend = bounds.end();
        for (; bit != bend; ++bit) {
            expr* x = *bit;
            bool s1, s2;
            rational lo, hi;
            if (a.is_int(x) && 
                bounds.has_lower(x, lo, s1) && !s1 && lo.is_zero() &&
                bounds.has_upper(x, hi, s2) && !s2 && hi.is_one()) {
                m_01s.insert(x);
                TRACE("pb", tout << "add bound " << mk_pp(x, m) << "\n";);
            }
        }
        
        expr_safe_replace sub(m);
        extract_pb_substitution(g, sub);
        
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        
        for (unsigned i = 0; i < g->size(); i++) {
            expr * curr = g->form(i);
            sub(curr, new_curr);                
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());
        
        // TBD: convert models for 0-1 variables.
        // TBD: support proof conversion (or not..)
    }

    void extract_pb_substitution(goal_ref const& g, expr_safe_replace& sub) {
        ast_mark mark;
        for (unsigned i = 0; i < g->size(); i++) {
            extract_pb_substitution(mark, g->form(i), sub);
        }
    }
    
    void extract_pb_substitution(ast_mark& mark, expr* fml, expr_safe_replace& sub) {
        expr_ref tmp(m);
        m_todo.reset();
        m_todo.push_back(fml);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            m_todo.pop_back();
            if (mark.is_marked(e) || !is_app(e)) {
                continue;
            }
            mark.mark(e, true);
            if (get_pb_relation(sub, e, tmp)) {
                sub.insert(e, tmp);
                continue;
            }
            app* ap = to_app(e);
            m_todo.append(ap->get_num_args(), ap->get_args());
        }
    }


    bool is_01var(expr* x) const {
        return m_01s.contains(x);
    }
    
    expr_ref mk_01(expr* x) {
        expr* r = m.mk_eq(x, a.mk_numeral(rational(1), m.get_sort(x)));
        return expr_ref(r, m);
    }        
    
    bool get_pb_relation(expr_safe_replace& sub, expr* fml, expr_ref& result) {
        expr* x, *y;
        expr_ref_vector args(m);
        vector<rational> coeffs;
        rational coeff;
        if ((a.is_le(fml, x, y) || a.is_ge(fml, y, x)) &&
            get_pb_sum(x, rational::one(), args, coeffs, coeff) &&
            get_pb_sum(y, -rational::one(), args, coeffs, coeff)) {
            result = m_pb.mk_le(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff);
            return true;
        }
        else if ((a.is_lt(fml, y, x) || a.is_gt(fml, x, y)) &&
                 get_pb_sum(x, rational::one(), args, coeffs, coeff) &&
                 get_pb_sum(y, -rational::one(), args, coeffs, coeff)) {
            result = m.mk_not(m_pb.mk_le(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff));
            return true;
        }
        else if (m.is_eq(fml, x, y) &&
                 get_pb_sum(x, rational::one(), args, coeffs, coeff) &&
                 get_pb_sum(y, -rational::one(), args, coeffs, coeff)) {
            result = m.mk_and(m_pb.mk_le(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff), 
                              m_pb.mk_ge(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff));
            return true;
        }                
        return false;
    }
    
    bool get_pb_sum(expr* x, rational const& mul, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
        expr *y, *z, *u;
        rational r, q;
        app* f = to_app(x);
        bool ok = true;
        if (a.is_add(x)) {
            for (unsigned i = 0; ok && i < f->get_num_args(); ++i) {
                ok = get_pb_sum(f->get_arg(i), mul, args, coeffs, coeff);
            }
        }
        else if (a.is_sub(x, y, z)) {
            ok = get_pb_sum(y, mul, args, coeffs, coeff);
            ok = ok && get_pb_sum(z, -mul, args, coeffs, coeff);
        }
        else if (a.is_uminus(x, y)) {
            ok = get_pb_sum(y, -mul, args, coeffs, coeff);
        }
        else if (a.is_mul(x, y, z) && a.is_numeral(y, r)) {
            ok = get_pb_sum(z, r*mul, args, coeffs, coeff);
        }                
        else if (a.is_mul(x, z, y) && a.is_numeral(y, r)) {
            ok = get_pb_sum(z, r*mul, args, coeffs, coeff);
        }
        else if (m.is_ite(x, y, z, u) && a.is_numeral(z, r) && a.is_numeral(u, q)) {
            args.push_back(y);
            coeffs.push_back(r*mul);
            args.push_back(m.mk_not(y));
            coeffs.push_back(q*mul);
        }
        else if (is_01var(x)) {
            args.push_back(mk_01(x));
            coeffs.push_back(mul);
        }
        else if (a.is_numeral(x, r)) {
            coeff += mul*r;
        }
        else {
            ok = false;
        }
        return ok;
    }
    
    virtual tactic * translate(ast_manager & m) {
        return alloc(lia2card_tactic, m, m_params);
    }
        
    virtual void collect_param_descrs(param_descrs & r) {
    }
        
    virtual void cleanup() {
        #pragma omp critical (tactic_cancel)
        {
            m_01s.reset();
            m_todo.reset();
        }
    }
};

tactic * mk_lia2card_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(lia2card_tactic, m, p));
}

void convert_objectives() {
    
}
