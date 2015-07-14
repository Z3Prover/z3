/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ctx_solver_simplify_tactic.cpp

Abstract:

    Context simplifier for propagating solver assignments.

Author:

    Nikolaj (nbjorner) 2012-3-6

Notes:

--*/

#include"ctx_solver_simplify_tactic.h"
#include"arith_decl_plugin.h"
#include"smt_params.h"
#include"smt_kernel.h"
#include"ast_pp.h"
#include"mk_simplified_app.h"
#include"ast_util.h"

class ctx_solver_simplify_tactic : public tactic {
    ast_manager&          m;
    params_ref            m_params;
    smt_params            m_front_p;
    smt::kernel           m_solver;
    arith_util            m_arith;
    mk_simplified_app     m_mk_app;
    func_decl_ref         m_fn;
    obj_map<sort, func_decl*> m_fns;
    unsigned              m_num_steps;
    volatile bool         m_cancel;
public:
    ctx_solver_simplify_tactic(ast_manager & m, params_ref const & p = params_ref()):
        m(m), m_params(p), m_solver(m, m_front_p),  
        m_arith(m), m_mk_app(m), m_fn(m), m_num_steps(0), 
        m_cancel(false) {
        sort* i_sort = m_arith.mk_int();
        m_fn = m.mk_func_decl(symbol(0xbeef101), i_sort, m.mk_bool_sort());
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(ctx_solver_simplify_tactic, m, m_params);
    }

    virtual ~ctx_solver_simplify_tactic() {
        obj_map<sort, func_decl*>::iterator it = m_fns.begin(), end = m_fns.end();
        for (; it != end; ++it) {
            m.dec_ref(it->m_value);
        }
        m_fns.reset();
    }

    virtual void updt_params(params_ref const & p) {
        m_solver.updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        m_solver.collect_param_descrs(r); 
    }
    
    virtual void collect_statistics(statistics & st) const {
        st.update("solver-simplify-steps", m_num_steps);
    }

    virtual void reset_statistics() { m_num_steps = 0; }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        
        mc = 0; pc = 0; core = 0;
        reduce(*(in.get()));
        in->inc_depth();
        result.push_back(in.get());
    }

    virtual void cleanup() {
        reset_statistics();
        m_solver.reset();
        m_cancel = false;
    }

protected:

    virtual void set_cancel(bool f) {
        m_solver.set_cancel(f);
        m_cancel = false;
    }

    void reduce(goal& g) {
        SASSERT(g.is_well_sorted());
        expr_ref fml(m);
        tactic_report report("ctx-solver-simplify", g);
        if (g.inconsistent())
            return;
        ptr_vector<expr> fmls;
        g.get_formulas(fmls);
        fml = mk_and(m, fmls.size(), fmls.c_ptr());
        m_solver.push();
        reduce(fml);
        m_solver.pop(1);
        SASSERT(m_solver.get_scope_level() == 0);
        TRACE("ctx_solver_simplify_tactic",
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i], m) << "\n";
              }
              tout << "=>\n";
              tout << mk_pp(fml, m) << "\n";);
        DEBUG_CODE(
        {
            m_solver.push();
            expr_ref fml1(m);
            fml1 = mk_and(m, fmls.size(), fmls.c_ptr());
            fml1 = m.mk_iff(fml, fml1);
            fml1 = m.mk_not(fml1);
            m_solver.assert_expr(fml1);
            lbool is_sat = m_solver.check();
            TRACE("ctx_solver_simplify_tactic", tout << "is non-equivalence sat?: " << is_sat << "\n";);
            if (is_sat == l_true) {
                TRACE("ctx_solver_simplify_tactic", 
                      tout << "result is not equivalent to input\n";
                      tout << mk_pp(fml1, m) << "\n";);
                UNREACHABLE();
            }
            m_solver.pop(1);
        });
        g.reset();
        g.assert_expr(fml, 0, 0); 
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(ctx-solver-simplify :num-steps " << m_num_steps << ")\n";);
        SASSERT(g.is_well_sorted());        
    }

    struct expr_pos {
        unsigned m_parent;
        unsigned m_self;
        unsigned m_idx;
        expr*    m_expr;
        expr_pos(unsigned p, unsigned s, unsigned i, expr* e):
            m_parent(p), m_self(s), m_idx(i), m_expr(e)
        {}
        expr_pos():
            m_parent(0), m_self(0), m_idx(0), m_expr(0)
        {}
    };

    void reduce(expr_ref& result){
        SASSERT(m.is_bool(result));
        ptr_vector<expr> names;
        svector<expr_pos> todo;
        expr_ref_vector fresh_vars(m), trail(m);
        expr_ref res(m), tmp(m);
        obj_map<expr, expr_pos> cache;        
        unsigned id = 1, child_id = 0;
        expr_ref n2(m), fml(m);
        unsigned parent_pos = 0, self_pos = 0, self_idx = 0;
        app * a;
        unsigned sz;
        expr_pos path_r;
        expr_ref_vector args(m);
        expr_ref n = mk_fresh(id, m.mk_bool_sort());
        trail.push_back(n);        

        fml = result.get();
        tmp = m.mk_not(m.mk_iff(fml, n));
        m_solver.assert_expr(tmp);

        todo.push_back(expr_pos(0,0,0,fml));
        names.push_back(n);
        m_solver.push();

        while (!todo.empty() && !m_cancel) {            
            expr_ref res(m);
            args.reset();
            expr* e    = todo.back().m_expr;
            self_pos   = todo.back().m_self;
            parent_pos = todo.back().m_parent;
            self_idx   = todo.back().m_idx;
            n = names.back();
            
            if (cache.contains(e)) {
                goto done;
            }
            if (m.is_bool(e) && simplify_bool(n, res)) {
                TRACE("ctx_solver_simplify_tactic", 
                      tout << "simplified: " << mk_pp(e, m) << " |-> " << mk_pp(res, m) << "\n";);
                goto done;
            }
            if (!is_app(e)) {
                res = e;
                goto done;
            }
            
            a = to_app(e);
            sz = a->get_num_args();            
            n2 = 0;

            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = a->get_arg(i);
                if (cache.find(arg, path_r)) {
                    //
                    // This is a single traversal version of the context
                    // simplifier. It simplifies only the first occurrence of 
                    // a sub-term with respect to the context.
                    //
                                        
                    if (path_r.m_parent == self_pos && path_r.m_idx == i) {
                        args.push_back(path_r.m_expr);
                    }
                    else {
                        args.push_back(arg);
                    }
                }
                else if (!n2) {
                    n2 = mk_fresh(id, m.get_sort(arg));
                    trail.push_back(n2);
                    todo.push_back(expr_pos(self_pos, child_id++, i, arg));
                    names.push_back(n2);
                    args.push_back(n2);
                }
                else {
                    args.push_back(arg);
                }
            }
            m_mk_app(a->get_decl(), args.size(), args.c_ptr(), res);
            trail.push_back(res);
            // child needs to be visited.
            if (n2) {
                m_solver.push();
                tmp = m.mk_eq(res, n);
                m_solver.assert_expr(tmp);
                continue;
            }
        
        done:
            if (res) {
                cache.insert(e, expr_pos(parent_pos, self_pos, self_idx, res));
            }            
            
            todo.pop_back();
            names.pop_back();
            m_solver.pop(1);
        }
        if (!m_cancel) {
            VERIFY(cache.find(fml, path_r));
            result = path_r.m_expr;
        }
    }

    bool simplify_bool(expr* n, expr_ref& res) {
        expr_ref tmp(m);
        m_solver.push();
        m_solver.assert_expr(n);
        lbool is_sat = m_solver.check();
        m_solver.pop(1);
        if (is_sat == l_false) {
            res = m.mk_true();
            return true;
        }

        m_solver.push();
        tmp = m.mk_not(n);
        m_solver.assert_expr(tmp);
        is_sat = m_solver.check();
        m_solver.pop(1);
        if (is_sat == l_false) {
            res = m.mk_false();
            return true;
        }

        return false;
    }

    expr_ref mk_fresh(unsigned& id, sort* s) {
        func_decl* fn;
        if (m.is_bool(s)) {
            fn = m_fn;
        }
        else if (!m_fns.find(s, fn)) {
            fn = m.mk_func_decl(symbol(0xbeef101 + id), m_arith.mk_int(), s);
            m.inc_ref(fn);
            m_fns.insert(s, fn);
        }
        return expr_ref(m.mk_app(fn, m_arith.mk_numeral(rational(id++), true)), m);
    }
    
};

tactic * mk_ctx_solver_simplify_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ctx_solver_simplify_tactic, m, p));
}
