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
#include "util/cooperate.h"
#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_util.h"
#include "ast/ast_pp_util.h"
#include "tactic/tactical.h"
#include "tactic/arith/bound_manager.h"
#include "tactic/generic_model_converter.h"

class lia2card_tactic : public tactic {

    struct bound {
        unsigned m_lo;
        unsigned m_hi;
        expr*    m_expr;
        bound(unsigned lo, unsigned hi, expr* b):
            m_lo(lo), m_hi(hi), m_expr(b) {}
        bound(): m_lo(0), m_hi(0), m_expr(nullptr) {}
    };

    struct lia_rewriter_cfg : public default_rewriter_cfg {
        ast_manager&     m;
        lia2card_tactic& t;
        arith_util       a;
        expr_ref_vector  args;
        vector<rational> coeffs;
        rational         coeff;

        bool is_pb(expr* x, expr* y, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
            args.reset();
            coeffs.reset();
            coeff.reset();
            return 
                t.get_pb_sum(x,  rational::one(), args, coeffs, coeff) &&
                t.get_pb_sum(y, -rational::one(), args, coeffs, coeff);
        }

        bool is_le(expr* x, expr* y, expr_ref& result) {
            if (is_pb(x, y, args, coeffs, coeff)) {
                result = t.mk_le(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff);
                return true;
            }
            else {
                return false;
            }
        }

        br_status mk_app_core(func_decl* f, unsigned sz, expr*const* es, expr_ref& result) {
            if (is_decl_of(f, a.get_family_id(), OP_LE) && is_le(es[0], es[1], result)) {
            }
            else if (is_decl_of(f, a.get_family_id(), OP_GE) && is_le(es[1], es[0], result)) {
            }
            else if (is_decl_of(f, a.get_family_id(), OP_LT) && is_le(es[1], es[0], result)) {
                result = m.mk_not(result);
            }
            else if (is_decl_of(f, a.get_family_id(), OP_GT) && is_le(es[0], es[1], result)) {
                result = m.mk_not(result);
            }
            else if (m.is_eq(f) && is_pb(es[0], es[1], args, coeffs, coeff)) {
                result = t.mk_eq(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), -coeff); 
            }    
            else {
                return BR_FAILED;
            }
            TRACE("pbsum", tout << expr_ref(m.mk_app(f, sz, es), m) << " ==>\n" <<  result << "\n";);

            return BR_DONE;
        }

        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = nullptr;
            return mk_app_core(f, num, args, result);
        }
        lia_rewriter_cfg(lia2card_tactic& t):m(t.m), t(t), a(m), args(m) {}
    };        

    class lia_rewriter : public rewriter_tpl<lia_rewriter_cfg> {
        lia_rewriter_cfg m_cfg;
    public:
        lia_rewriter(lia2card_tactic& t):
            rewriter_tpl<lia_rewriter_cfg>(t.m, false, m_cfg),
            m_cfg(t)
        {}
    };

public:
    typedef obj_map<expr, bound> bounds_map;
    ast_manager &                    m;
    arith_util                       a;
    lia_rewriter                     m_rw;
    params_ref                       m_params;
    pb_util                          m_pb;
    mutable ptr_vector<expr>*        m_todo;
    bounds_map                       m_bounds;
    bool                             m_compile_equality;
    unsigned                         m_max_ub;
    ref<generic_model_converter>     m_mc;
        
    lia2card_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        a(m),
        m_rw(*this),
        m_pb(m),
        m_todo(alloc(ptr_vector<expr>)),
        m_compile_equality(true) {
        m_max_ub = 100;
    }

    ~lia2card_tactic() override {
        dealloc(m_todo);
    }
                
    void updt_params(params_ref const & p) override {
        m_params = p;
        m_compile_equality = p.get_bool("compile_equality", true);
    }
    
    expr_ref mk_bounded(expr_ref_vector& axioms, app* x, unsigned lo, unsigned hi) {
        expr_ref_vector xs(m);
        expr_ref last_v(m);
        if (!m_mc) m_mc = alloc(generic_model_converter, m, "lia2card");
        if (hi == 0) {
            expr* r = a.mk_int(0);
            m_mc->add(x->get_decl(), r);
            return expr_ref(r, m);
        }
        if (lo > 0) {
            xs.push_back(a.mk_int(lo));
        }
        for (unsigned i = lo; i < hi; ++i) {     
            std::string name(x->get_decl()->get_name().str());
            expr_ref v(m.mk_fresh_const(name.c_str(), m.mk_bool_sort()), m);
            if (last_v) axioms.push_back(m.mk_implies(v, last_v));
            xs.push_back(m.mk_ite(v, a.mk_int(1), a.mk_int(0)));
            m_mc->hide(v);            
            last_v = v;
        }
        expr* r = a.mk_add(xs.size(), xs.c_ptr());
        m_mc->add(x->get_decl(), r);
        return expr_ref(r, m);        
    }    

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        SASSERT(g->is_well_sorted());
        m_bounds.reset();
        m_mc.reset();
        expr_ref_vector axioms(m);
        expr_safe_replace rep(m);

        TRACE("pb", g->display(tout););        
        tactic_report report("lia2card", *g);
        
        bound_manager bounds(m);
        bounds(*g);
        
        for (expr* x : bounds) {
            bool s1 = false, s2 = false;
            rational lo, hi;
            if (a.is_int(x) && 
                is_uninterp_const(x) && 
                bounds.has_lower(x, lo, s1) && !s1 && lo.is_unsigned() &&
                bounds.has_upper(x, hi, s2) && !s2 && hi.is_unsigned() && hi.get_unsigned() - lo.get_unsigned() <= m_max_ub) {
                expr_ref b = mk_bounded(axioms, to_app(x), lo.get_unsigned(), hi.get_unsigned());
                rep.insert(x, b);
                m_bounds.insert(x, bound(lo.get_unsigned(), hi.get_unsigned(), b));
                TRACE("pb", tout << "add bound " << mk_pp(x, m) << "\n";);
            }
        }
        for (unsigned i = 0; i < g->size(); i++) {            
            expr_ref   new_curr(m), tmp(m);
            proof_ref  new_pr(m);        
            rep(g->form(i), tmp);
            m_rw(tmp, new_curr, new_pr);
            if (m.proofs_enabled() && !new_pr) {
                new_pr = m.mk_rewrite(g->form(i), new_curr);
                new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
            }
            // IF_VERBOSE(0, verbose_stream() << mk_pp(g->form(i), m) << "\n--->\n" << new_curr << "\n";);
            g->update(i, new_curr, new_pr, g->dep(i));

        }
        for (expr* a : axioms) {
            g->assert_expr(a);
        }
        if (m_mc) g->add(m_mc.get());
        g->inc_depth();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());
        m_bounds.reset();   
    }
    
    expr* mk_le(unsigned sz, rational const* weights, expr* const* args, rational const& w) {
        if (sz == 0) {
            return w.is_neg()?m.mk_false():m.mk_true();
        }
        if (sz == 1 && weights[0].is_one() && w >= rational::one()) {
            return m.mk_true();
        }
        if (sz == 1 && weights[0].is_one() && w.is_zero()) {
            return m.mk_not(args[0]);
        }
        if (w.is_neg()) {
            DEBUG_CODE(for (unsigned i = 0; i < sz; ++i) SASSERT(weights[i].is_nonneg()); );
            return m.mk_false();
        }
        return m_pb.mk_le(sz, weights, args, w);
    }

    expr* mk_eq(unsigned sz, rational const* weights, expr* const* args, rational const& w) {
        if (w.is_neg()) {
            DEBUG_CODE(for (unsigned i = 0; i < sz; ++i) SASSERT(weights[i].is_nonneg()); );
            return m.mk_false();
        }
        if (m_compile_equality) {
            return m_pb.mk_eq(sz, weights, args, w);
        }
        else {
            return m.mk_and(mk_ge(sz, weights, args, w), mk_le(sz, weights, args, w));
        }
    }
    
    expr* mk_ge(unsigned sz, rational const* weights, expr* const* args, rational const& w) {
        if (sz == 0) {
            return w.is_pos()?m.mk_false():m.mk_true();
        }
        if (sz == 1 && weights[0].is_one() && w.is_one()) {
            return args[0];
        }
        if (sz == 1 && weights[0].is_one() && w.is_zero()) {
            return m.mk_not(args[0]);
        }
        if (w.is_neg()) {
            DEBUG_CODE(for (unsigned i = 0; i < sz; ++i) SASSERT(weights[i].is_nonneg()); );
            return m.mk_true();
        }
        return m_pb.mk_ge(sz, weights, args, w);
    }
    
    bool get_pb_sum(expr* x, rational const& mul, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
        expr_ref_vector conds(m);
        return get_sum(x, mul, conds, args, coeffs, coeff);
    }

    bool get_sum(expr* x, rational const& mul, expr_ref_vector& conds, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
        expr *y, *z, *u;
        rational r, q;
        if (!is_app(x)) return false;
        app* f = to_app(x);
        bool ok = true;
        if (a.is_add(x)) {
            for (unsigned i = 0; ok && i < f->get_num_args(); ++i) {
                ok = get_sum(f->get_arg(i), mul, conds, args, coeffs, coeff);
            }
        }
        else if (a.is_sub(x, y, z)) {
            ok = get_sum(y, mul, conds, args, coeffs, coeff);
            ok = ok && get_sum(z, -mul, conds, args, coeffs, coeff);
        }
        else if (a.is_uminus(x, y)) {
            ok = get_sum(y, -mul, conds, args, coeffs, coeff);
        }
        else if (a.is_mul(x, y, z) && is_numeral(y, r)) {
            ok = get_sum(z, r*mul, conds, args, coeffs, coeff);
        }                
        else if (a.is_mul(x, z, y) && is_numeral(y, r)) {
            ok = get_sum(z, r*mul, conds, args, coeffs, coeff);
        }
        else if (a.is_to_real(x, y)) {
            ok = get_sum(y, mul, conds, args, coeffs, coeff);
        }
        else if (m.is_ite(x, y, z, u)) {
            conds.push_back(y);
            ok = get_sum(z, mul, conds, args, coeffs, coeff);
            conds.pop_back();
            conds.push_back(m.mk_not(y));
            ok &= get_sum(u, mul, conds, args, coeffs, coeff);
            conds.pop_back();            
        }
        else if (is_numeral(x, r)) {
            insert_arg(mul*r, conds, m.mk_true(), args, coeffs, coeff);
        }
        else {
            TRACE("pb", tout << "Can't handle " << mk_pp(x, m) << "\n";);
            ok = false;
        }
        return ok;
    }

    expr_ref add_conds(expr_ref_vector& es, expr* e) {
        expr_ref result(m);
        if (!m.is_true(e)) {
            es.push_back(e);
        }
        result = mk_and(m, es.size(), es.c_ptr());
        if (!m.is_true(e)) {
            es.pop_back();
        }
        return result;
    }

    bool is_numeral(expr* e, rational& r) {
        if (a.is_uminus(e, e) && is_numeral(e, r)) {
            r.neg();
            return true;
        }
        if (a.is_to_real(e, e)) {
            return is_numeral(e, r);
        }
        return a.is_numeral(e, r);
    }
    
    void insert_arg(
        rational const& p, 
        expr_ref_vector& conds,
        expr* x, 
        expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
        expr_ref cond = add_conds(conds, x);
        if (m.is_true(cond)) {
            coeff += p;
        }
        else if (p.is_neg()) {
            // -p*x = p*(1-x) - p
            args.push_back(m.mk_not(cond));
            coeffs.push_back(-p);
            coeff += p;
        }
        else if (p.is_pos()) {
            args.push_back(cond);
            coeffs.push_back(p);
        }
    }

    tactic * translate(ast_manager & m) override {
        return alloc(lia2card_tactic, m, m_params);
    }
        
    void collect_param_descrs(param_descrs & r) override {
        r.insert("compile_equality", CPK_BOOL, 
                 "(default:false) compile equalities into pseudo-Boolean equality");
    }
        
    void cleanup() override {        
        ptr_vector<expr>* todo = alloc(ptr_vector<expr>);
        std::swap(m_todo, todo);        
        dealloc(todo);
        m_bounds.reset();
    }
};

tactic * mk_lia2card_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(lia2card_tactic, m, p));
}

bool get_pb_sum(expr* term, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff) {
    params_ref p;
    ast_manager& m = args.get_manager();
    lia2card_tactic tac(m, p);
    return tac.get_pb_sum(term, rational::one(), args, coeffs, coeff);
}
