/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    propagate_ineqs_tactic.h

Abstract:

    This tactic performs the following tasks:

     - Propagate bounds using the bound_propagator.
     - Eliminate subsumed inequalities.  
       For example:
          x - y >= 3
          can be replaced with true if we know that
          x >= 3 and y <= 0
            
     - Convert inequalities of the form p <= k and p >= k into p = k,
       where p is a polynomial and k is a constant.

    This strategy assumes the input is in arith LHS mode.
    This can be achieved by using option :arith-lhs true in the
    simplifier.
     
Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"tactical.h"
#include"bound_propagator.h"
#include"arith_decl_plugin.h"
#include"simplify_tactic.h"
#include"ast_smt2_pp.h"

class propagate_ineqs_tactic : public tactic {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    propagate_ineqs_tactic(ast_manager & m, params_ref const & p);

    virtual tactic * translate(ast_manager & m) {
        return alloc(propagate_ineqs_tactic, m, m_params);
    }

    virtual ~propagate_ineqs_tactic();

    virtual void updt_params(params_ref const & p);
    virtual void collect_param_descrs(param_descrs & r) {}

    virtual void operator()(goal_ref const & g, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);
    
    virtual void cleanup();
};

tactic * mk_propagate_ineqs_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(propagate_ineqs_tactic, m, p));
}

struct propagate_ineqs_tactic::imp {
    ast_manager &          m;
    unsynch_mpq_manager    nm;
    small_object_allocator m_allocator;
    bound_propagator       bp;
    arith_util             m_util;
    typedef bound_propagator::var a_var;
    obj_map<expr, a_var>   m_expr2var;
    expr_ref_vector        m_var2expr;

    typedef numeral_buffer<mpq, unsynch_mpq_manager> mpq_buffer;
    typedef svector<a_var> var_buffer;                          
    
    mpq_buffer             m_num_buffer;
    var_buffer             m_var_buffer;
    goal_ref               m_new_goal;
    
    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_allocator("ineq-simplifier"),
        bp(nm, m_allocator, p),
        m_util(m),
        m_var2expr(m),
        m_num_buffer(nm) {
        updt_params_core(p);
    }

    void updt_params_core(params_ref const & p) {
    }

    void updt_params(params_ref const & p) {
        updt_params_core(p);
        bp.updt_params(p);
    }

    void display_bounds(std::ostream & out) {
        unsigned sz = m_var2expr.size();
        mpq  k;
        bool strict;
        unsigned ts;
        for (unsigned x = 0; x < sz; x++) {
            if (bp.lower(x, k, strict, ts)) 
                out << nm.to_string(k) << " " << (strict ? "<" : "<=");
            else
                out << "-oo <";
            out << " " << mk_ismt2_pp(m_var2expr.get(x), m) << " ";
            if (bp.upper(x, k, strict, ts)) 
                out << (strict ? "<" : "<=") << " " << nm.to_string(k);
            else
                out << "< oo";
            out << "\n";
        }
        nm.del(k);
    }

    a_var mk_var(expr * t) {
        if (m_util.is_to_real(t))
            t = to_app(t)->get_arg(0);
        a_var x;
        if (m_expr2var.find(t, x))
            return x;
        x = m_var2expr.size();
        bp.mk_var(x, m_util.is_int(t));
        m_var2expr.push_back(t);
        m_expr2var.insert(t, x);
        return x;
    }

    void expr2linear_pol(expr * t, mpq_buffer & as, var_buffer & xs) {
        mpq c_mpq_val;
        if (m_util.is_add(t)) {
            rational c_val;
            unsigned num = to_app(t)->get_num_args();
            for (unsigned i = 0; i < num; i++) {
                expr * mon = to_app(t)->get_arg(i);
                expr * c, * x;
                if (m_util.is_mul(mon, c, x) && m_util.is_numeral(c, c_val)) {
                    nm.set(c_mpq_val, c_val.to_mpq());
                    as.push_back(c_mpq_val);
                    xs.push_back(mk_var(x));
                }
                else {
                    as.push_back(mpq(1));
                    xs.push_back(mk_var(mon));
                }
            }
        }
        else {
            as.push_back(mpq(1));
            xs.push_back(mk_var(t));
        }
        nm.del(c_mpq_val);
    }

    a_var mk_linear_pol(expr * t) {
        a_var x;
        if (m_expr2var.find(t, x))
            return x;
        x = mk_var(t);
        if (m_util.is_add(t)) {
            m_num_buffer.reset();
            m_var_buffer.reset();
            expr2linear_pol(t, m_num_buffer, m_var_buffer);
            m_num_buffer.push_back(mpq(-1));
            m_var_buffer.push_back(x);
            bp.mk_eq(m_num_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr());
        }
        return x;
    }

    enum kind { EQ, LE, GE };
    
    bool process(expr * t) {
        bool sign = false;
        while (m.is_not(t, t))
            sign = !sign;
        bool strict = false;
        kind k;
        if (m.is_eq(t)) {
            if (sign)
                return false;
            k = EQ;
        } 
        else if (m_util.is_le(t)) {
            if (sign) {
                k = GE;
                strict = true;
            }
            else {
                k = LE;
            }
        }
        else if (m_util.is_ge(t)) {
            if (sign) {
                k = LE;
                strict = true;
            }
            else {
                k = GE;
            }
        }
        else {
            return false;
        }
        expr * lhs = to_app(t)->get_arg(0);
        expr * rhs = to_app(t)->get_arg(1);
        if (m_util.is_numeral(lhs)) {
            std::swap(lhs, rhs); 
            if (k == LE)
                k = GE;
            else if (k == GE)
                k = LE;
        }

        rational c;
        if (!m_util.is_numeral(rhs, c))
            return false;
        a_var x = mk_linear_pol(lhs);
        mpq c_prime;
        nm.set(c_prime, c.to_mpq());
        if (k == EQ) {
            SASSERT(!strict);
            bp.assert_lower(x, c_prime, false);
            bp.assert_upper(x, c_prime, false);
        }
        else if (k == LE) {
            bp.assert_upper(x, c_prime, strict);
        }
        else {
            SASSERT(k == GE);
            bp.assert_lower(x, c_prime, strict);
        }
        nm.del(c_prime);
        return true;
    }

    bool collect_bounds(goal const & g) {
        bool found = false;
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * t = g.form(i);
            if (process(t))
                found = true;
            else
                m_new_goal->assert_expr(t); // save non-bounds here
        }
        return found;
    }

    bool lower_subsumed(expr * p, mpq const & k, bool strict) {
        if (!m_util.is_add(p))
            return false;
        m_num_buffer.reset();
        m_var_buffer.reset();
        expr2linear_pol(p, m_num_buffer, m_var_buffer);
        mpq  implied_k;
        bool implied_strict;
        bool result = 
            bp.lower(m_var_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr(), implied_k, implied_strict) &&
            (nm.gt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
        nm.del(implied_k);
        return result;
    }

    bool upper_subsumed(expr * p, mpq const & k, bool strict) {
        if (!m_util.is_add(p))
            return false;
        m_num_buffer.reset();
        m_var_buffer.reset();
        expr2linear_pol(p, m_num_buffer, m_var_buffer);
        mpq  implied_k;
        bool implied_strict;
        bool result = 
            bp.upper(m_var_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr(), implied_k, implied_strict) &&
            (nm.lt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
        nm.del(implied_k);
        return result;
    }
    
    void restore_bounds() {
        mpq l, u;
        bool strict_l, strict_u, has_l, has_u;
        unsigned ts;
        unsigned sz = m_var2expr.size();
        for (unsigned x = 0; x < sz; x++) {
            expr * p = m_var2expr.get(x);
            has_l = bp.lower(x, l, strict_l, ts);
            has_u = bp.upper(x, u, strict_u, ts);
            if (!has_l && !has_u)
                continue;
            if (has_l && has_u && nm.eq(l, u) && !strict_l && !strict_u) {
                // l <= p <= l -->  p = l
                m_new_goal->assert_expr(m.mk_eq(p, m_util.mk_numeral(rational(l), m_util.is_int(p))));
                continue;
            }
            if (has_l && !lower_subsumed(p, l, strict_l)) {
                if (strict_l)
                    m_new_goal->assert_expr(m.mk_not(m_util.mk_le(p, m_util.mk_numeral(rational(l), m_util.is_int(p)))));
                else
                    m_new_goal->assert_expr(m_util.mk_ge(p, m_util.mk_numeral(rational(l), m_util.is_int(p))));
            }
            if (has_u && !upper_subsumed(p, u, strict_u)) {
                if (strict_u)
                    m_new_goal->assert_expr(m.mk_not(m_util.mk_ge(p, m_util.mk_numeral(rational(u), m_util.is_int(p)))));
                else
                    m_new_goal->assert_expr(m_util.mk_le(p, m_util.mk_numeral(rational(u), m_util.is_int(p))));
            }
        }
        nm.del(l);
        nm.del(u);
    }
    
    bool is_x_minus_y_eq_0(expr * t, expr * & x, expr * & y) {
        expr * lhs, * rhs, * m1, * m2;
        if (m.is_eq(t, lhs, rhs) && m_util.is_zero(rhs) && m_util.is_add(lhs, m1, m2)) {
            if (m_util.is_times_minus_one(m2, y) && is_uninterp_const(m1)) {
                x = m1;
                return true;
            }
            if (m_util.is_times_minus_one(m1, y) && is_uninterp_const(m2)) {
                x = m2;
                return true;
            }
        }
        return false;
    }

    bool is_unbounded(expr * t) {
        a_var x;
        if (m_expr2var.find(t, x))
            return !bp.has_lower(x) && !bp.has_upper(x);
        return true;
    }

    bool lower(expr * t, mpq & k, bool & strict) {
        unsigned ts;
        a_var x;
        if (m_expr2var.find(t, x))
            return bp.lower(x, k, strict, ts);
        return false;
    }

    bool upper(expr * t, mpq & k, bool & strict) {
        unsigned ts;
        a_var x;
        if (m_expr2var.find(t, x))
            return bp.upper(x, k, strict, ts);
        return false;
    }

    void find_ite_bounds(expr * root) {
        TRACE("find_ite_bounds_bug", display_bounds(tout););
        expr * n = root;
        expr * target = 0;
        expr * c, * t, * e;
        expr * x, * y;
        bool has_l, has_u;
        mpq l_min, u_max;
        bool l_strict, u_strict;
        mpq curr;
        bool curr_strict;
        while (true) {
            TRACE("find_ite_bounds_bug", tout << mk_ismt2_pp(n, m) << "\n";);

            if (m.is_ite(n, c, t, e)) {
                if (is_x_minus_y_eq_0(t, x, y))
                    n = e;
                else if (is_x_minus_y_eq_0(e, x, y))
                    n = t;
                else
                    break;
            }
            else if (is_x_minus_y_eq_0(n, x, y)) {
                n = 0;
            }
            else {
                break;
            }

            TRACE("find_ite_bounds_bug", tout << "x: " << mk_ismt2_pp(x, m) << ", y: " << mk_ismt2_pp(y, m) << "\n";
                  if (target) { 
                      tout << "target: " << mk_ismt2_pp(target, m) << "\n";
                      tout << "has_l: " << has_l << " " << nm.to_string(l_min) << " has_u: " << has_u << " " << nm.to_string(u_max) << "\n";
                  });

            if (is_unbounded(y))
                std::swap(x, y);
            
            if (!is_unbounded(x)) {
                TRACE("find_ite_bounds_bug", tout << "x is already bounded\n";);
                break;
            }
            
            if (target == 0) {
                target = x;
                if (lower(y, curr, curr_strict)) {
                    has_l = true;
                    nm.set(l_min, curr);
                    l_strict = curr_strict;
                }
                else {
                    has_l = false;
                    TRACE("find_ite_bounds_bug", tout << "y does not have lower\n";);
                }
                if (upper(y, curr, curr_strict)) {
                    has_u = true;
                    nm.set(u_max, curr);
                    u_strict = curr_strict;
                }
                else {
                    has_u = false;
                    TRACE("find_ite_bounds_bug", tout << "y does not have upper\n";);
                }
            }
            else if (target == x) {
                if (has_l) {
                    if (lower(y, curr, curr_strict)) {
                        if (nm.lt(curr, l_min) || (!curr_strict && l_strict && nm.eq(curr, l_min))) {
                            nm.set(l_min, curr);
                            l_strict = curr_strict;
                        }
                    }
                    else {
                        has_l = false;
                        TRACE("find_ite_bounds_bug", tout << "y does not have lower\n";);
                    }
                }
                if (has_u) {
                    if (upper(y, curr, curr_strict)) {
                        if (nm.gt(curr, u_max) || (curr_strict && !u_strict && nm.eq(curr, u_max))) {
                            nm.set(u_max, curr);
                            u_strict = curr_strict;
                        }
                    }
                    else {
                        has_u = false;
                        TRACE("find_ite_bounds_bug", tout << "y does not have upper\n";);
                    }
                }
            }
            else { 
                break;
            }
            
            if (!has_l && !has_u)
                break;

            if (n == 0) {
                TRACE("find_ite_bounds", tout << "found bounds for: " << mk_ismt2_pp(target, m) << "\n";
                      tout << "has_l: " << has_l << " " << nm.to_string(l_min) << " l_strict: " << l_strict << "\n";
                      tout << "has_u: " << has_u << " " << nm.to_string(u_max) << " u_strict: " << u_strict << "\n";
                      tout << "root:\n" << mk_ismt2_pp(root, m) << "\n";);
                a_var x = mk_var(target);
                if (has_l)
                    bp.assert_lower(x, l_min, l_strict);
                if (has_u)
                    bp.assert_upper(x, u_max, u_strict);
                break;
            }
        }
        nm.del(l_min);
        nm.del(u_max);
        nm.del(curr);
    }

    void find_ite_bounds() {
        unsigned sz = m_new_goal->size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = m_new_goal->form(i);
            if (m.is_ite(f)) 
                find_ite_bounds(to_app(f));
        }
        bp.propagate();
        TRACE("find_ite_bounds", display_bounds(tout););
    }

    void operator()(goal * g, goal_ref & r) {
        tactic_report report("propagate-ineqs", *g);

        m_new_goal = alloc(goal, *g, true);
        m_new_goal->inc_depth();
        r = m_new_goal.get();
        if (!collect_bounds(*g)) {
            m_new_goal = 0;
            r = g;
            return; // nothing to be done
        }
        
        TRACE("propagate_ineqs_tactic", g->display(tout); display_bounds(tout); tout << "bound propagator:\n"; bp.display(tout););

        bp.propagate();

        report_tactic_progress(":bound-propagations", bp.get_num_propagations());
        report_tactic_progress(":bound-false-alarms", bp.get_num_false_alarms());

        if (bp.inconsistent()) {
            r->reset();
            r->assert_expr(m.mk_false());
            return;
        }

        // find_ite_bounds(); // did not help

        restore_bounds();
        
        TRACE("propagate_ineqs_tactic", tout << "after propagation:\n"; display_bounds(tout); bp.display(tout););
        TRACE("propagate_ineqs_tactic", r->display(tout););
    }

};

propagate_ineqs_tactic::propagate_ineqs_tactic(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

propagate_ineqs_tactic::~propagate_ineqs_tactic() {
    dealloc(m_imp);
}

void propagate_ineqs_tactic::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void propagate_ineqs_tactic::operator()(goal_ref const & g, 
                                        goal_ref_buffer & result, 
                                        model_converter_ref & mc, 
                                        proof_converter_ref & pc,
                                        expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("propagate-ineqs", g);
    fail_if_unsat_core_generation("propagate-ineqs", g);
    mc = 0; pc = 0; core = 0; result.reset();
    goal_ref r;
    (*m_imp)(g.get(), r);
    result.push_back(r.get());
    SASSERT(r->is_well_sorted());
}

 
void propagate_ineqs_tactic::cleanup() {
    imp * d = alloc(imp, m_imp->m, m_params);
    std::swap(d, m_imp);    
    dealloc(d);
}
