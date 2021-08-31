/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    fix_dl_var_tactic.cpp

Abstract:

    Fix a difference logic variable to 0.
    If the problem is in the difference logic fragment, that is, all arithmetic terms
    are of the form (x + k), and the arithmetic atoms are of the 
    form x - y <= k or x - y = k. Then, we can set one variable to 0.

    This is useful because, many bounds can be exposed after this operation is performed.

Author:

    Leonardo de Moura (leonardo) 2011-12-19

Revision History:

--*/
#include "tactic/tactical.h"
#include "ast/rewriter/th_rewriter.h"
#include "tactic/generic_model_converter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/expr_substitution.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"

class fix_dl_var_tactic : public tactic {

    struct is_target {
        struct failed {};
        ast_manager &          m;
        arith_util &           m_util;
        expr_fast_mark1 *      m_visited;
        ptr_vector<expr>       m_todo;
        obj_map<app, unsigned> m_occs;
        obj_map<app, unsigned> m_non_nested_occs;

        is_target(arith_util & u):
            m(u.get_manager()),
            m_util(u) {
        }
        
        void throw_failed(expr * ctx1, expr * ctx2 = nullptr) {
            TRACE("fix_dl_var", tout << mk_ismt2_pp(ctx1, m) << "\n"; if (ctx2) tout << mk_ismt2_pp(ctx2, m) << "\n";);
            throw failed();
        }
        
        bool is_arith(expr * n) {
            sort * s = n->get_sort();
            return s->get_family_id() == m_util.get_family_id();
        }

        // Remark: we say an expression is nested, if it occurs inside the boolean structure of the formula.
        // That is, the expression is not part of an unit clause comprising of a single inequality/equality.
        
        void inc_occ(expr * n, bool nested) {
            if (is_uninterp_const(n) && is_arith(n)) {
                m_occs.insert_if_not_there(to_app(n), 0)++;

                if (!nested) {
                    m_non_nested_occs.insert_if_not_there(to_app(n), 0)++;
                }
            }
        }

        void visit(expr * n, bool nested) {
            inc_occ(n, nested);
            if (!m_visited->is_marked(n)) {
                m_visited->mark(n);
                m_todo.push_back(n);
            }
        }
        
        void process_app(app * t) {
            if (!is_uninterp(t) && !is_arith(t)) {
                throw_failed(t);
            }
            for (expr* arg : *t) 
                visit(arg, false);
        }

        void process_arith_atom(expr * lhs, expr * rhs, bool nested) {
            if (is_uninterp(lhs) && is_uninterp(rhs)) {
                visit(lhs, nested);
                visit(rhs, nested);
                return;
            }

            if (m_util.is_numeral(lhs))
                std::swap(lhs, rhs);
            
            if (!m_util.is_numeral(rhs))
                throw_failed(lhs, rhs);
            
            expr * t, * ms, * s;
            // check if lhs is of the form: (+ t (* (- 1) s))
            if (m_util.is_add(lhs, t, ms) && m_util.is_times_minus_one(ms, s) && is_uninterp(t) && is_uninterp(s)) {
                visit(t, nested);
                visit(s, nested);
            }
            else {
                CTRACE("fix_dl_var", m_util.is_add(lhs, t, ms),
                       s = 0;
                       tout << "is_times_minus_one: " << m_util.is_times_minus_one(ms, s) << "\n";
                       tout << "is_uninterp(t):     " << is_uninterp(t) << "\n";
                       tout << "t.family_id():      " << (is_app(t) ? to_app(t)->get_family_id() : -1) << "\n";
                       tout << "util.family_id:     " << m_util.get_family_id() << "\n";
                       if (s) {
                       tout << "is_uninterp(s):     " << is_uninterp(s) << "\n";
                       tout << "s.family_id():      " << (is_app(s) ? to_app(s)->get_family_id() : -1) << "\n";
                       });
                throw_failed(lhs, rhs);
            }
        }

        void process_eq(app * t, bool nested) {
            if (!is_arith(t->get_arg(0))) {
                process_app(t);
            }
            else {
                process_arith_atom(t->get_arg(0), t->get_arg(1), nested);
            }
        }

        void process_arith(app * t, bool nested) {
            if (m.is_bool(t) && t->get_num_args() == 2) {
                process_arith_atom(t->get_arg(0), t->get_arg(1), nested);
                return;
            }
            // check if t is of the form c + k
            expr * c, * k;
            if (m_util.is_add(t, k, c) && is_uninterp(c) && m_util.is_numeral(k)) {
                visit(c, nested);
            }
            else {
                throw_failed(t);
            }
        }

        void process(expr * n) {
            if (m_visited->is_marked(n))
                return;
            
            while (m.is_not(n, n))
                ;

            if (is_app(n) && to_app(n)->get_family_id() ==  m_util.get_family_id()) {
                process_arith(to_app(n), false);
                return;
            }
            
            m_todo.push_back(n);
            m_visited->mark(n);

            while (!m_todo.empty()) {
                expr * n = m_todo.back();
                m_todo.pop_back();
                
                if (!is_app(n))
                    throw_failed(n);
                
                app * t = to_app(n);
                
                if (m.is_eq(t))
                    process_eq(t, true);
                else if (t->get_family_id() ==  m_util.get_family_id())
                    process_arith(t, true);
                else
                    process_app(t);
            }
        }

        app * most_occs(obj_map<app, unsigned> & occs, unsigned & best) {
            app * r = nullptr;
            best = 0;
            for (auto const& kv : occs) {
                if (kv.m_value > best) {
                    best = kv.m_value;
                    r    = kv.m_key;
                }
            }
            return r;
        }

        // TODO make it a parameter
#define NESTED_PENALTY 10

        app * most_occs() {
            // We try to choose a variable that when set to 0 will generate many bounded variables.
            // That is why we give preference to variables occurring in non-nested inequalities.
            unsigned best1, best2;
            app * r1, * r2;
            r1 = most_occs(m_non_nested_occs, best1);
            r2 = most_occs(m_occs, best2);
            TRACE("fix_dl_var", 
                  if (r1) {
                      tout << "r1 occs: " << best1 << "\n";
                      tout << mk_ismt2_pp(r1, m) << "\n";
                  }
                  if (r2) {
                      tout << "r2 occs: " << best2 << "\n";
                      tout << mk_ismt2_pp(r2, m) << "\n";
                  });
            if (best2 > NESTED_PENALTY * best1)
                return r2;
            else
                return r1;
        }

        app * operator()(goal const & g) {
            try {
                expr_fast_mark1 visited;
                m_visited = &visited;
                unsigned sz = g.size();
                for (unsigned i = 0; i < sz; i++) {
                    process(g.form(i));
                }
                return most_occs();
            }
            catch (const failed &) {
                return nullptr;
            }
        }
    };

    struct imp {
        ast_manager & m;
        arith_util    u;
        th_rewriter   m_rw;
        bool          m_produce_models;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            u(m),
            m_rw(m, p) {
        }
        
        void updt_params(params_ref const & p) {
            m_rw.updt_params(p);
        }
                
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) {
            tactic_report report("fix-dl-var", *g);
            bool produce_proofs = g->proofs_enabled();
            m_produce_models    = g->models_enabled();
            TRACE("fix_dl_var", g->display(tout););

            app * var = is_target(u)(*g);
            if (var != nullptr) {
                IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(fixing-at-zero " << var->get_decl()->get_name() << ")\n";);
                
                expr_substitution subst(m);
                app * zero = u.mk_numeral(rational(0), u.is_int(var));
                subst.insert(var, zero);
                m_rw.set_substitution(&subst);
            
                if (m_produce_models) {
                    generic_model_converter * mc = alloc(generic_model_converter, m, "fix_dl");
                    mc->add(var, zero);
                    g->add(mc);
                }
                
                expr_ref   new_curr(m);
                proof_ref  new_pr(m);
                unsigned size = g->size();
                for (unsigned idx = 0; !g->inconsistent() && idx < size; idx++) {
                    expr * curr = g->form(idx);
                    m_rw(curr, new_curr, new_pr);
                    if (produce_proofs) {
                        proof * pr = g->pr(idx);
                        new_pr     = m.mk_modus_ponens(pr, new_pr);
                    }
                    g->update(idx, new_curr, new_pr, g->dep(idx));
                }
                g->inc_depth();
            }
            result.push_back(g.get());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    fix_dl_var_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(fix_dl_var_tactic, m, m_params);
    }
        
    ~fix_dl_var_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        th_rewriter::get_param_descrs(r);
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
    
    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
};

tactic * mk_fix_dl_var_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(fix_dl_var_tactic, m, p));
}
