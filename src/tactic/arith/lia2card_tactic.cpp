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
#include"pb_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"rewriter_def.h"
#include"ast_util.h"
#include"ast_pp_util.h"

class lia2card_tactic : public tactic {
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
                t.get_pb_sum(x, rational::one(), args, coeffs, coeff) &&
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

#if 0
            expr_ref vc(m);
            vc = m.mk_not(m.mk_eq(m.mk_app(f, sz, es), result));
            ast_pp_util pp(m);
            pp.collect(vc);
            std::cout 
                << "(push)\n"
                << "(echo \"" << result << "\")\n"
                ;
            pp.display_decls(std::cout);
            std::cout
                << "(assert " << vc << ")\n"
                << "(check-sat)\n"
                << "(pop)\n";
#endif
            return BR_DONE;
        }

        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
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
    typedef obj_hashtable<expr> expr_set;
    ast_manager &                    m;
    arith_util                       a;
    lia_rewriter                     m_rw;
    params_ref                       m_params;
    pb_util                          m_pb;
    mutable ptr_vector<expr>*        m_todo;
    expr_set*                        m_01s;
    bool                             m_compile_equality;
        
    lia2card_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        a(m),
        m_rw(*this),
        m_pb(m),
        m_todo(alloc(ptr_vector<expr>)),
        m_01s(alloc(expr_set)),
        m_compile_equality(false) {
    }

    virtual ~lia2card_tactic() {
        dealloc(m_todo);
        dealloc(m_01s);
    }
                
    void updt_params(params_ref const & p) {
        m_params = p;
        m_compile_equality = p.get_bool("compile_equality", false);
    }
    
    virtual void operator()(goal_ref const & g, 
                    goal_ref_buffer & result, 
                    model_converter_ref & mc, 
                    proof_converter_ref & pc,
                    expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        m_01s->reset();
        
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
                m_01s->insert(x);
                TRACE("pb", tout << "add bound " << mk_pp(x, m) << "\n";);
            }
        }
        expr_mark subfmls;
        for (unsigned i = 0; i < g->size(); i++) {            
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);        
            m_rw(g->form(i), new_curr, new_pr);
            if (m.proofs_enabled() && !new_pr) {
                new_pr = m.mk_rewrite(g->form(i), new_curr);
                new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
            }
            g->update(i, new_curr, new_pr, g->dep(i));
            mark_rec(subfmls, new_curr);
        }
        expr_set::iterator it = m_01s->begin(), end = m_01s->end();
        for (; it != end; ++it) {
            expr* v = *it;
            if (subfmls.is_marked(v)) {
                g->assert_expr(a.mk_le(v, a.mk_numeral(rational(1), true)));
                g->assert_expr(a.mk_le(a.mk_numeral(rational(0), true), v));
            }
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());
        
        // TBD: convert models for 0-1 variables.
        // TBD: support proof conversion (or not..)
    }
    
    void mark_rec(expr_mark& mark, expr* e) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            e = todo.back();
            todo.pop_back();
            if (!mark.is_marked(e)) {
                mark.mark(e);
                if (is_app(e)) {
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
                        todo.push_back(to_app(e)->get_arg(i));
                    }
                }
                else if (is_quantifier(e)) {
                    todo.push_back(to_quantifier(e)->get_expr());
                }
            }
        }
    }


    bool is_01var(expr* x) const {
        return m_01s->contains(x);
    }
    
    expr_ref mk_01(expr* x) {
        expr* r = m.mk_eq(x, a.mk_numeral(rational(1), m.get_sort(x)));
        return expr_ref(r, m);
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
        else if (is_01var(x)) {
            insert_arg(mul, conds, mk_01(x), args, coeffs, coeff);
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

    virtual tactic * translate(ast_manager & m) {
        return alloc(lia2card_tactic, m, m_params);
    }
        
    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("compile_equality", CPK_BOOL, 
                 "(default:false) compile equalities into pseudo-Boolean equality");
    }
        
    virtual void cleanup() {        
        expr_set* d = alloc(expr_set);
        ptr_vector<expr>* todo = alloc(ptr_vector<expr>);
        std::swap(m_01s, d);
        std::swap(m_todo, todo);        
        dealloc(d);
        dealloc(todo);
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
