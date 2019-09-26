/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solve_eqs_tactic.cpp

Abstract:

    Tactic for solving equations and performing gaussian elimination.

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/
#include "ast/rewriter/expr_replacer.h"
#include "ast/occurs.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/hoist_rewriter.h"
#include "tactic/goal_shared_occs.h"
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "tactic/tactic_params.hpp"

class solve_eqs_tactic : public tactic {
    struct imp {
        typedef generic_model_converter gmc;
        
        ast_manager &                 m_manager;
        expr_replacer *               m_r;
        bool                          m_r_owner;
        arith_util                    m_a_util;
        obj_map<expr, unsigned>       m_num_occs;
        unsigned                      m_num_steps;
        unsigned                      m_num_eliminated_vars;
        bool                          m_theory_solver;
        bool                          m_ite_solver;
        unsigned                      m_max_occs;
        bool                          m_context_solve;
        scoped_ptr<expr_substitution> m_subst;
        scoped_ptr<expr_substitution> m_norm_subst;
        expr_sparse_mark              m_candidate_vars;
        expr_sparse_mark              m_candidate_set;
        ptr_vector<expr>              m_candidates;
        ptr_vector<app>               m_vars;
        expr_sparse_mark              m_nonzero;
        ptr_vector<app>               m_ordered_vars;
        bool                          m_produce_proofs;
        bool                          m_produce_unsat_cores;
        bool                          m_produce_models;
        
        imp(ast_manager & m, params_ref const & p, expr_replacer * r, bool owner):
            m_manager(m),
            m_r(r),
            m_r_owner(r == nullptr || owner),
            m_a_util(m),
            m_num_steps(0),
            m_num_eliminated_vars(0) {
            updt_params(p);
            if (m_r == nullptr)
                m_r       = mk_default_expr_replacer(m);
        }
        
        ~imp() {
            if (m_r_owner)
                dealloc(m_r);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void updt_params(params_ref const & p) {
            tactic_params tp(p);
            m_ite_solver     = p.get_bool("ite_solver", tp.solve_eqs_ite_solver());
            m_theory_solver  = p.get_bool("theory_solver", tp.solve_eqs_theory_solver());
            m_max_occs       = p.get_uint("solve_eqs_max_occs", tp.solve_eqs_max_occs());
            m_context_solve  = p.get_bool("context_solve", tp.solve_eqs_context_solve());
        }
                
        void checkpoint() {
            if (m().canceled())
                throw tactic_exception(m().limit().get_cancel_msg());
        }
        
        // Check if the number of occurrences of t is below the specified threshold :solve-eqs-max-occs
        bool check_occs(expr * t) const {
            if (m_max_occs == UINT_MAX)
                return true;
            unsigned num = 0;
            m_num_occs.find(t, num);
            TRACE("solve_eqs_check_occs", tout << mk_ismt2_pp(t, m_manager) << " num_occs: " << num << " max: " << m_max_occs << "\n";);
            return num <= m_max_occs;
        }
        
        // Use: (= x def) and (= def x)

        bool trivial_solve1(expr * lhs, expr * rhs, app_ref & var, expr_ref & def, proof_ref & pr) { 

            if (is_uninterp_const(lhs) && !m_candidate_vars.is_marked(lhs) && !occurs(lhs, rhs) && check_occs(lhs)) {
                var = to_app(lhs); 
                def = rhs;
                pr  = nullptr;
                return true;
            }
            else {
                return false;
            }
        }
        bool trivial_solve(expr * lhs, expr * rhs, app_ref & var, expr_ref & def, proof_ref & pr) {
            if (trivial_solve1(lhs, rhs, var, def, pr)) 
                return true;
            if (trivial_solve1(rhs, lhs, var, def, pr)) {
                if (m_produce_proofs) {
                    pr = m().mk_commutativity(m().mk_eq(lhs, rhs));
                }
                return true;
            }
            return false;
        }
        
        // (ite c (= x t1) (= x t2)) --> (= x (ite c t1 t2))
        bool solve_ite_core(app * ite, expr * lhs1, expr * rhs1, expr * lhs2, expr * rhs2, app_ref & var, expr_ref & def, proof_ref & pr) {
            if (lhs1 != lhs2)
                return false;
            if (!is_uninterp_const(lhs1) || m_candidate_vars.is_marked(lhs1))
                return false;
            if (occurs(lhs1, ite->get_arg(0)) || occurs(lhs1, rhs1) || occurs(lhs1, rhs2))
                return false;
            if (!check_occs(lhs1))
                return false;
            var = to_app(lhs1);
            def = m().mk_ite(ite->get_arg(0), rhs1, rhs2);
            
            if (m_produce_proofs)
                pr = m().mk_rewrite(ite, m().mk_eq(var, def));
            return true;
        }
        
        // (ite c (= x t1) (= x t2)) --> (= x (ite c t1 t2))
        bool solve_ite(app * ite, app_ref & var, expr_ref & def, proof_ref & pr) {
            expr * t = ite->get_arg(1);
            expr * e = ite->get_arg(2);
            
            if (!m().is_eq(t) || !m().is_eq(e))
                return false;
            
            expr * lhs1 = to_app(t)->get_arg(0);
            expr * rhs1 = to_app(t)->get_arg(1);
            expr * lhs2 = to_app(e)->get_arg(0);
            expr * rhs2 = to_app(e)->get_arg(1);
            
            return 
                solve_ite_core(ite, lhs1, rhs1, lhs2, rhs2, var, def, pr) ||
                solve_ite_core(ite, rhs1, lhs1, lhs2, rhs2, var, def, pr) ||
                solve_ite_core(ite, lhs1, rhs1, rhs2, lhs2, var, def, pr) ||
                solve_ite_core(ite, rhs1, lhs1, rhs2, lhs2, var, def, pr);
        }
        
        bool is_pos_literal(expr * n) {
            return is_app(n) && to_app(n)->get_num_args() == 0 && to_app(n)->get_family_id() == null_family_id;
        }
        
        bool is_neg_literal(expr * n) {
            if (m_manager.is_not(n))
                return is_pos_literal(to_app(n)->get_arg(0));
            return false;
        }
        
#if 0
        bool not_bool_eq(expr * f, app_ref & var, expr_ref & def, proof_ref & pr) {
            if (!m().is_not(f))
                return false;
            expr * eq = to_app(f)->get_arg(0);
            if (!m().is_eq(f))
                return false;
            
        }
#endif
        
        /**
           \brief Given t of the form (f s_0 ... s_n), 
           return true if x occurs in some s_j for j != i 
        */
        bool occurs_except(expr * x, app * t, unsigned i) {
            unsigned num = t->get_num_args();
            for (unsigned j = 0; j < num; j++) {
                if (i != j && occurs(x, t->get_arg(j)))
                    return true;
            }
            return false;
        }

        void add_pos(expr* f) {
            expr* lhs = nullptr, *rhs = nullptr;
            rational val;
            if (m_a_util.is_le(f, lhs, rhs) && m_a_util.is_numeral(rhs, val) && val.is_neg()) {
                m_nonzero.mark(lhs);
            }
            else if (m_a_util.is_ge(f, lhs, rhs) && m_a_util.is_numeral(rhs, val) && val.is_pos()) {
                m_nonzero.mark(lhs);
            }
            else if (m().is_not(f, f)) {
                if (m_a_util.is_le(f, lhs, rhs) && m_a_util.is_numeral(rhs, val) && !val.is_neg()) {
                    m_nonzero.mark(lhs);
                }
                else if (m_a_util.is_ge(f, lhs, rhs) && m_a_util.is_numeral(rhs, val) && !val.is_pos()) {
                    m_nonzero.mark(lhs);
                }
                else if (m().is_eq(f, lhs, rhs) && m_a_util.is_numeral(rhs, val) && val.is_zero()) {
                    m_nonzero.mark(lhs);                    
                }
            }            
        }

        bool is_nonzero(expr* e) {
            return m_nonzero.is_marked(e);
        }

        bool isolate_var(app* arg, app_ref& var, expr_ref& div, unsigned i, app* lhs, expr* rhs) {
            if (!m_a_util.is_mul(arg)) return false;
            unsigned n = arg->get_num_args();
            for (unsigned j = 0; j < n; ++j) {
                expr* e = arg->get_arg(j);
                bool ok = is_uninterp_const(e) && check_occs(e) && !occurs(e, rhs) && !occurs_except(e, lhs, i);
                if (!ok) continue;
                var = to_app(e);
                for (unsigned k = 0; ok && k < n; ++k) {
                    expr* arg_k = arg->get_arg(k);
                    ok = k == j || (!occurs(var, arg_k) && is_nonzero(arg_k));
                }
                if (!ok) continue;
                ptr_vector<expr> args;
                for (unsigned k = 0; k < n; ++k) {
                    if (k != j) args.push_back(arg->get_arg(k));
                }
                div = m_a_util.mk_mul(args.size(), args.c_ptr());
                return true;
            }
            return false;
        }

        bool solve_nl(app * lhs, expr * rhs, expr* eq, app_ref& var, expr_ref & def, proof_ref & pr) {
            SASSERT(m_a_util.is_add(lhs));
            if (m_a_util.is_int(lhs)) return false;
            unsigned num = lhs->get_num_args();
            expr_ref div(m());
            for (unsigned i = 0; i < num; i++) {
                expr * arg = lhs->get_arg(i);
                if (is_app(arg) && isolate_var(to_app(arg), var, div, i, lhs, rhs)) {
                    ptr_vector<expr> args;
                    for (unsigned k = 0; k < num; ++k) {
                        if (k != i) args.push_back(lhs->get_arg(k));
                    }
                    def = m_a_util.mk_sub(rhs, m_a_util.mk_add(args.size(), args.c_ptr()));
                    def = m_a_util.mk_div(def, div);
                    if (m_produce_proofs)
                        pr = m().mk_rewrite(eq, m().mk_eq(var, def));
                    return true;
                }
            }
            return false;
        }
        
        bool solve_arith_core(app * lhs, expr * rhs, expr * eq, app_ref & var, expr_ref & def, proof_ref & pr) {
            SASSERT(m_a_util.is_add(lhs));
            bool is_int  = m_a_util.is_int(lhs);
            expr * a = nullptr; 
            expr * v = nullptr;
            rational a_val;
            unsigned num = lhs->get_num_args();
            unsigned i;
            for (i = 0; i < num; i++) {
                expr * arg = lhs->get_arg(i);
                if (is_uninterp_const(arg) && !m_candidate_vars.is_marked(arg) && check_occs(arg) && !occurs(arg, rhs) && !occurs_except(arg, lhs, i)) {
                    a_val = rational(1); 
                    v     = arg;
                    break;
                }
                else if (m_a_util.is_mul(arg, a, v) && 
                         is_uninterp_const(v) && 
                         !m_candidate_vars.is_marked(v) &&
                         m_a_util.is_numeral(a, a_val) &&
                         !a_val.is_zero() &&
                         (!is_int || a_val.is_minus_one()) &&
                         check_occs(v) &&
                         !occurs(v, rhs) && 
                         !occurs_except(v, lhs, i)) {
                    break;
                }
            }
            if (i == num)
                return false;
            var = to_app(v);
            expr_ref inv_a(m());
            if (!a_val.is_one()) {
                inv_a = m_a_util.mk_numeral(rational(1)/a_val, is_int);
                rhs   = m_a_util.mk_mul(inv_a, rhs);
            }
            
            ptr_buffer<expr> other_args;
            for (unsigned j = 0; j < num; j++) {
                if (i != j) {
                    if (inv_a)
                        other_args.push_back(m_a_util.mk_mul(inv_a, lhs->get_arg(j)));
                    else
                        other_args.push_back(lhs->get_arg(j));
                }
            }
            switch (other_args.size()) {
            case 0:
                def = rhs;
                break;
            case 1:
                def = m_a_util.mk_sub(rhs, other_args[0]);
                break;
            default:
                def = m_a_util.mk_sub(rhs, m_a_util.mk_add(other_args.size(), other_args.c_ptr()));
                break;
            }
            if (m_produce_proofs)
                pr = m().mk_rewrite(eq, m().mk_eq(var, def));
            return true;
        }
        
        bool solve_arith(expr * lhs, expr * rhs, expr * eq, app_ref & var, expr_ref & def, proof_ref & pr) {
            return 
                (m_a_util.is_add(lhs) && solve_arith_core(to_app(lhs), rhs, eq, var, def, pr)) ||
                (m_a_util.is_add(rhs) && solve_arith_core(to_app(rhs), lhs, eq, var, def, pr));
#if 0
            // better done inside of nlsat
                (m_a_util.is_add(lhs) && solve_nl(to_app(lhs), rhs, eq, var, def, pr)) ||
                (m_a_util.is_add(rhs) && solve_nl(to_app(rhs), lhs, eq, var, def, pr));
#endif
        }
        
        bool solve(expr * f, app_ref & var, expr_ref & def, proof_ref & pr) {
            expr* arg1 = nullptr, *arg2 = nullptr;
            if (m().is_eq(f, arg1, arg2)) {
                if (trivial_solve(arg1, arg2, var, def, pr))
                    return true;
                if (m_theory_solver) {
                    if (solve_arith(arg1, arg2, f, var, def, pr))
                        return true;
                }
                return false;
            }
                        
#if 0
            if (not_bool_eq(f, var, def, pr))
                return true;
#endif
            
            if (m_ite_solver && m().is_ite(f))
                return solve_ite(to_app(f), var, def, pr);
            
            if (is_pos_literal(f)) {
                if (m_candidate_vars.is_marked(f))
                    return false;
                var = to_app(f);
                def = m().mk_true();
                if (m_produce_proofs) {
                    // [rewrite]: (iff (iff l true) l)
                    // [symmetry T1]: (iff l (iff l true))
                    pr = m().mk_rewrite(m().mk_eq(var, def), var);
                    pr = m().mk_symmetry(pr);
                }
                TRACE("solve_eqs_bug2", tout << "eliminating: " << mk_ismt2_pp(f, m()) << "\n";);
                return true;
            }
            
            if (is_neg_literal(f)) {
                var = to_app(to_app(f)->get_arg(0));
                if (m_candidate_vars.is_marked(var))
                    return false;
                def = m().mk_false();
                if (m_produce_proofs) {
                    // [rewrite]: (iff (iff l false) ~l)
                    // [symmetry T1]: (iff ~l (iff l false))
                    pr = m().mk_rewrite(m().mk_eq(var, def), f);
                    pr = m().mk_symmetry(pr);
                }
                return true;
            }
            
            return false;
        }

        void insert_solution(goal const& g, unsigned idx, expr* f, app* var, expr* def, proof* pr) {
            m_vars.push_back(var);
            m_candidates.push_back(f);
            m_candidate_set.mark(f);
            m_candidate_vars.mark(var);
            if (m_produce_proofs) {
                if (!pr)
                    pr = g.pr(idx);
                else
                    pr = m().mk_modus_ponens(g.pr(idx), pr);
            }
            m_subst->insert(var, def, pr, g.dep(idx));
        }
        
        /**
           \brief Start collecting candidates
        */
        void collect(goal const & g) {
            m_subst->reset();
            m_norm_subst->reset();
            m_r->set_substitution(nullptr);
            m_candidate_vars.reset();
            m_candidate_set.reset();
            m_candidates.reset();
            m_vars.reset();
            m_nonzero.reset();
            app_ref  var(m());
            expr_ref  def(m());
            proof_ref pr(m());
            unsigned size = g.size();
            for (unsigned idx = 0; idx < size; idx++) {
                add_pos(g.form(idx));
            }
            for (unsigned idx = 0; idx < size; idx++) {
                checkpoint();
                expr * f = g.form(idx);
                if (solve(f, var, def, pr)) {
                    insert_solution(g, idx, f, var, def, pr);
                }
                m_num_steps++;
            }
            
            TRACE("solve_eqs", 
                  tout << "candidate vars:\n";
                  for (app* v : m_vars) {
                      tout << mk_ismt2_pp(v, m()) << " ";
                  }
                  tout << "\n";);
        }

        struct nnf_context {
            bool m_is_and;
            expr_ref_vector m_args;
            unsigned m_index;
            nnf_context(bool is_and, expr_ref_vector const& args, unsigned idx):
                m_is_and(is_and),
                m_args(args),
                m_index(idx)
            {}
        };

        ptr_vector<expr> m_todo;       
        void mark_occurs(expr_mark& occ, goal const& g, expr* v) {
            expr_fast_mark2 visited;
            occ.mark(v, true);
            visited.mark(v, true);
            for (unsigned j = 0; j < g.size(); ++j) {              
                m_todo.push_back(g.form(j));
            }
            while (!m_todo.empty()) {
                expr* e = m_todo.back();
                if (visited.is_marked(e)) {
                    m_todo.pop_back();
                    continue;
                }
                if (is_app(e)) {
                    bool does_occur = false;
                    bool all_visited = true;
                    for (expr* arg : *to_app(e)) {
                        if (!visited.is_marked(arg)) {
                            m_todo.push_back(arg);
                            all_visited = false;
                        }
                        else {
                            does_occur |= occ.is_marked(arg);
                        }
                    }
                    if (all_visited) {
                        occ.mark(e, does_occur);
                        visited.mark(e, true);
                        m_todo.pop_back();
                    }
                }
                else if (is_quantifier(e)) {
                    expr* body = to_quantifier(e)->get_expr();
                    if (visited.is_marked(body)) {
                        visited.mark(e, true);
                        occ.mark(e, occ.is_marked(body));
                        m_todo.pop_back();
                    }
                }
                else {
                    visited.mark(e, true);
                    m_todo.pop_back();
                }
            }
        }

        bool is_compatible(goal const& g, unsigned idx, vector<nnf_context> const & path, expr* v, expr* eq) {
            expr_mark occ;
            svector<lbool> cache;
            mark_occurs(occ, g, v);
            return is_goal_compatible(g, occ, cache, idx, v, eq) && is_path_compatible(occ, cache, path, v, eq);
        }

        bool is_goal_compatible(goal const& g, expr_mark& occ, svector<lbool>& cache, unsigned idx, expr* v, expr* eq) {
            bool all_e = false;
            for (unsigned j = 0; j < g.size(); ++j) {              
                if (j != idx && !check_eq_compat_rec(occ, cache, g.form(j), v, eq, all_e)) {
                    TRACE("solve_eqs", tout << "occurs goal " << mk_pp(eq, m()) << "\n";);
                    return false;
                }
            }
            return true;
        }

        // 
        // all_e := all disjunctions contain eq
        //
        // or, all_e -> skip if all disjunctions contain eq
        // or, all_e -> fail if some disjunction contains v but not eq
        // or, all_e -> all_e := false if some disjunction does not contain v
        // and, all_e -> all_e
        //

        bool is_path_compatible(expr_mark& occ, svector<lbool>& cache, vector<nnf_context> const & path, expr* v, expr* eq) {
            bool all_e = true;
            for (unsigned i = path.size(); i-- > 0; ) {
                auto const& p = path[i];
                auto const& args = p.m_args;
                if (p.m_is_and && !all_e) {
                    for (unsigned j = 0; j < args.size(); ++j) {
                        if (j != p.m_index && occ.is_marked(args[j])) {
                            TRACE("solve_eqs", tout << "occurs and " << mk_pp(eq, m()) << " " << mk_pp(args[j], m()) << "\n";);
                            return false;
                        }
                    }
                }
                else if (!p.m_is_and) {
                    for (unsigned j = 0; j < args.size(); ++j) {
                        if (j != p.m_index) {
                            if (occurs(v, args[j])) {
                                if (!check_eq_compat_rec(occ, cache, args[j], v, eq, all_e)) {
                                    TRACE("solve_eqs", tout << "occurs or " << mk_pp(eq, m()) << " " << mk_pp(args[j], m()) << "\n";);
                                    return false;
                                }
                            }
                            else {
                                all_e = false;
                            }
                        }
                    }
                }
            }
            return true;
        }

        bool check_eq_compat_rec(expr_mark& occ, svector<lbool>& cache, expr* f, expr* v, expr* eq, bool& all) {
            expr_ref_vector args(m());
            expr* f1 = nullptr;
            if (!occ.is_marked(f)) {
                all = false;
                return true;
            }
            unsigned idx = f->get_id();
            if (cache.size() > idx && cache[idx] != l_undef) {
                return cache[idx] == l_true;
            }
            if (m().is_not(f, f1) && m().is_or(f1)) {
                flatten_and(f, args);
                for (expr* arg : args) {
                    if (arg == eq) {
                        cache.reserve(idx+1, l_undef);
                        cache[idx] = l_true;
                        return true;
                    }
                }                
            }
            else if (m().is_or(f)) {
                flatten_or(f, args);
            }
            else {
                return false;
            }

            for (expr* arg : args) {
                if (!check_eq_compat_rec(occ, cache, arg, v, eq, all)) {
                    cache.reserve(idx+1, l_undef);
                    cache[idx] = l_false;
                    return false;
                }
            }
            cache.reserve(idx+1, l_undef);
            cache[idx] = l_true;
            return true;
        }

        void hoist_nnf(goal const& g, expr* f, vector<nnf_context> & path, unsigned idx, unsigned depth) {
            if (depth > 4) {
                return;
            }
            app_ref var(m());
            expr_ref def(m());
            proof_ref pr(m());
            expr_ref_vector args(m());
            expr* f1 = nullptr;

            if (m().is_not(f, f1) && m().is_or(f1)) {
                flatten_and(f, args);
                for (unsigned i = 0; i < args.size(); ++i) {
                    expr* arg = args.get(i), *lhs = nullptr, *rhs = nullptr;
                    if (m().is_eq(arg, lhs, rhs)) { 
                        if (trivial_solve1(lhs, rhs, var, def, pr) && is_compatible(g, idx, path, var, arg)) {
                            insert_solution(g, idx, arg, var, def, pr);
                        }
                        else if (trivial_solve1(rhs, lhs, var, def, pr) && is_compatible(g, idx, path, var, arg)) {
                            insert_solution(g, idx, arg, var, def, pr);
                        }
                        else {
                            IF_VERBOSE(10000, 
                                       verbose_stream() << "eq not solved " << mk_pp(arg, m()) << "\n";
                                       verbose_stream() << is_uninterp_const(lhs) << " " << !m_candidate_vars.is_marked(lhs) << " " 
                                       << !occurs(lhs, rhs) << " " << check_occs(lhs) << "\n";);
                        }
                    }
                    else {
                        path.push_back(nnf_context(true, args, i));
                        hoist_nnf(g, arg, path, idx, depth + 1);
                        path.pop_back();
                    }                             
                }
            }
            else if (m().is_or(f)) {
                flatten_or(f, args);
                for (unsigned i = 0; i < args.size(); ++i) {
                    path.push_back(nnf_context(false, args, i));
                    hoist_nnf(g, args.get(i), path, idx, depth + 1);
                    path.pop_back();
                }
            }
        }

        void collect_hoist(goal const& g) {
            unsigned size = g.size();
            vector<nnf_context> path;
            for (unsigned idx = 0; idx < size; idx++) {
                checkpoint();
                hoist_nnf(g, g.form(idx), path, idx, 0);
            }
        }

        void distribute_and_or(goal & g) {
            unsigned size = g.size();
            hoist_rewriter_star rw(m());
            th_rewriter thrw(m());
            expr_ref tmp(m()), tmp2(m());
            TRACE("solve_eqs", g.display(tout););
            for (unsigned idx = 0; idx < size; idx++) {
                checkpoint();
                if (g.is_decided_unsat()) break;
                expr* f = g.form(idx);
                thrw(f, tmp);
                rw(tmp, tmp2);
                TRACE("solve_eqs", tout << mk_pp(f, m()) << " " << tmp2 << "\n";);
                g.update(idx, tmp2, g.pr(idx), g.dep(idx));
            }
            
        }
        
        void sort_vars() {
            SASSERT(m_candidates.size() == m_vars.size());
            TRACE("solve_eqs_bug", tout << "sorting vars...\n";);
            m_ordered_vars.reset();
            

            // The variables (and its definitions) in m_subst must remain alive until the end of this procedure.
            // Reason: they are scheduled for unmarking in visiting/done. 
            // They should remain alive while they are on the stack.
            // To make sure this is the case, whenever a variable (and its definition) is removed from m_subst,
            // I add them to the saved vector. 
            
            expr_ref_vector saved(m());
            
            expr_fast_mark1 visiting;
            expr_fast_mark2 done;
            
            typedef std::pair<expr *, unsigned> frame;
            svector<frame> todo;
            unsigned num = 0;
            for (app* v : m_vars) {
                checkpoint();
                if (!m_candidate_vars.is_marked(v))
                    continue;
                todo.push_back(frame(v, 0));
                while (!todo.empty()) {
                start:
                    frame & fr = todo.back();
                    expr * t   = fr.first;
                    m_num_steps++;
                    TRACE("solve_eqs_bug", tout << "processing:\n" << mk_ismt2_pp(t, m()) << "\n";);
                    if (t->get_ref_count() > 1 && done.is_marked(t)) {
                        todo.pop_back();
                        continue;
                    }
                    switch (t->get_kind()) {
                    case AST_VAR:
                        todo.pop_back();
                        break;
                    case AST_QUANTIFIER:
                        num = to_quantifier(t)->get_num_children();
                        while (fr.second < num) {
                            expr * c = to_quantifier(t)->get_child(fr.second);
                            fr.second++;
                            if (c->get_ref_count() > 1 && done.is_marked(c))
                                continue;
                            todo.push_back(frame(c, 0));
                            goto start;
                        }
                        if (t->get_ref_count() > 1)
                            done.mark(t);
                        todo.pop_back();
                        break;
                    case AST_APP:
                        num = to_app(t)->get_num_args();
                        if (num == 0) {
                            if (fr.second == 0) {
                                if (m_candidate_vars.is_marked(t)) {
                                    if (visiting.is_marked(t)) {
                                        // cycle detected: remove t
                                        visiting.reset_mark(t);
                                        m_candidate_vars.mark(t, false);
                                        SASSERT(!m_candidate_vars.is_marked(t));
                                        
                                        // Must save t and its definition.
                                        // See comment in the beginning of the function
                                        expr * def = nullptr;
                                        proof * pr;
                                        expr_dependency * dep;
                                        m_subst->find(to_app(t), def, pr, dep);
                                        SASSERT(def != 0);
                                        saved.push_back(t); 
                                        saved.push_back(def);
                                        // 
                                        
                                        m_subst->erase(t);
                                    }
                                    else {
                                        visiting.mark(t);
                                        fr.second = 1;
                                        expr * def = nullptr;
                                        proof * pr;
                                        expr_dependency * dep;
                                        m_subst->find(to_app(t), def, pr, dep);
                                        SASSERT(def != 0);
                                        todo.push_back(frame(def, 0));
                                        goto start;
                                    }
                                }
                            }
                            else {
                                SASSERT(fr.second == 1);
                                if (m_candidate_vars.is_marked(t)) {
                                    visiting.reset_mark(t);
                                    m_ordered_vars.push_back(to_app(t));
                                }
                                else {
                                    // var was removed from the list of candidate vars to elim cycle
                                    // do nothing
                                }
                            }
                        }
                        else {
                            while (fr.second < num) {
                                expr * arg = to_app(t)->get_arg(fr.second);
                                fr.second++;
                                if (arg->get_ref_count() > 1 && done.is_marked(arg))
                                    continue;
                                todo.push_back(frame(arg, 0));
                                goto start;
                            }
                        }
                        if (t->get_ref_count() > 1)
                            done.mark(t);
                        todo.pop_back();
                        break;
                    default:
                        UNREACHABLE();
                        todo.pop_back();
                        break;
                    }
                }
            }
            
            // cleanup
            unsigned idx = 0;
            for (expr* v : m_vars) {
                if (!m_candidate_vars.is_marked(v)) {
                    m_candidate_set.mark(m_candidates[idx], false);
                }
                ++idx;
            }
            
            IF_VERBOSE(10000, 
                       verbose_stream() << "ordered vars: ";
                       for (app* v : m_ordered_vars) verbose_stream() << mk_pp(v, m()) << " ";
                       verbose_stream() << "\n";);
            TRACE("solve_eqs", 
                  tout << "ordered vars:\n";
                  for (app* v : m_ordered_vars) {
                      SASSERT(m_candidate_vars.is_marked(v));
                      tout << mk_ismt2_pp(v, m()) << " ";
                  }
                  tout << "\n";);
            m_candidate_vars.reset();
        }
        
        void normalize() {
            m_norm_subst->reset();
            m_r->set_substitution(m_norm_subst.get());
            
            expr_ref new_def(m());
            proof_ref new_pr(m());
            expr_dependency_ref new_dep(m());
            for (app * v : m_ordered_vars) {
                checkpoint();
                expr * def = nullptr;
                proof * pr = nullptr;
                expr_dependency * dep = nullptr;
                m_subst->find(v, def, pr, dep);
                SASSERT(def != 0);
                m_r->operator()(def, new_def, new_pr, new_dep);
                m_num_steps += m_r->get_num_steps() + 1;
                if (m_produce_proofs)
                    new_pr = m().mk_transitivity(pr, new_pr);
                new_dep = m().mk_join(dep, new_dep);
                m_norm_subst->insert(v, new_def, new_pr, new_dep);
                // we updated the substituting, but we don't need to reset m_r
                // because all cached values there do not depend on v.
            }
            m_subst->reset();
            TRACE("solve_eqs", 
                  tout << "after normalizing variables\n";
                  for (expr * v : m_ordered_vars) {
                      expr * def = 0;
                      proof * pr = 0;
                      expr_dependency * dep = 0;
                      m_norm_subst->find(v, def, pr, dep);
                      tout << mk_ismt2_pp(v, m()) << "\n----->\n" << mk_ismt2_pp(def, m()) << "\n\n";
                  });
#if 0
            DEBUG_CODE({
                    for (expr * v : m_ordered_vars) {
                        expr * def = 0;
                        proof * pr = 0;
                        expr_dependency * dep = 0;
                        m_norm_subst->find(v, def, pr, dep);
                        SASSERT(def != 0);
                        CASSERT("solve_eqs_bug", !occurs(v, def));
                    }
                });
#endif
        }

        void substitute(goal & g) {
            // force the cache of m_r to be reset.
            m_r->set_substitution(m_norm_subst.get());
            
            expr_ref new_f(m());
            proof_ref new_pr(m());
            expr_dependency_ref new_dep(m());
            unsigned size = g.size();
            for (unsigned idx = 0; idx < size; idx++) {
                checkpoint();
                expr * f = g.form(idx);
                TRACE("gaussian_leak", tout << "processing:\n" << mk_ismt2_pp(f, m()) << "\n";);
                if (m_candidate_set.is_marked(f)) {
                    // f may be deleted after the following update.
                    // so, we must remove the mark before doing the update
                    m_candidate_set.mark(f, false);
                    SASSERT(!m_candidate_set.is_marked(f));
                    g.update(idx, m().mk_true(), m().mk_true_proof(), nullptr);
                    m_num_steps ++;
                    continue;
                }

                m_r->operator()(f, new_f, new_pr, new_dep);

                TRACE("solve_eqs_subst", tout << mk_ismt2_pp(f, m()) << "\n--->\n" << mk_ismt2_pp(new_f, m()) << "\n";);
                m_num_steps += m_r->get_num_steps() + 1;
                if (m_produce_proofs)
                    new_pr = m().mk_modus_ponens(g.pr(idx), new_pr);
                if (m_produce_unsat_cores)
                    new_dep = m().mk_join(g.dep(idx), new_dep);
                
                g.update(idx, new_f, new_pr, new_dep);
                if (g.inconsistent())
                    return;
            }
            g.elim_true();
            TRACE("solve_eqs", g.display(tout << "after applying substitution\n"););
#if 0
            DEBUG_CODE({
                    for (expr* v : m_ordered_vars) {
                        for (unsigned j = 0; j < g.size(); j++) {
                            CASSERT("solve_eqs_bug", !occurs(v, g.form(j)));
                        }
                    }});
#endif
        }

        void save_elim_vars(model_converter_ref & mc) {
            IF_VERBOSE(100, if (!m_ordered_vars.empty()) verbose_stream() << "num. eliminated vars: " << m_ordered_vars.size() << "\n";);
            m_num_eliminated_vars += m_ordered_vars.size();
            if (m_produce_models) {
                if (!mc.get())
                    mc = alloc(gmc, m(), "solve-eqs");
                for (app* v : m_ordered_vars) {
                    expr * def = nullptr;
                    proof * pr;
                    expr_dependency * dep = nullptr;
                    m_norm_subst->find(v, def, pr, dep);
                    SASSERT(def);
                    static_cast<gmc*>(mc.get())->add(v, def);
                }
            }
        }
        
        void collect_num_occs(expr * t, expr_fast_mark1 & visited) {
            ptr_buffer<expr, 128> stack;
            
#define VISIT(ARG) {                                                                                            \
            if (is_uninterp_const(ARG)) {                                                                       \
                obj_map<expr, unsigned>::obj_map_entry * entry = m_num_occs.insert_if_not_there2(ARG, 0);       \
                entry->get_data().m_value++;                                                                    \
            }                                                                                                   \
            if (!visited.is_marked(ARG)) {                                                                      \
                visited.mark(ARG, true);                                                                        \
                stack.push_back(ARG);                                                                           \
            }                                                                                                   \
        }
            
            VISIT(t);
            
            while (!stack.empty()) {
                expr * t = stack.back();
                stack.pop_back();
                if (!is_app(t))
                    continue;
                unsigned j = to_app(t)->get_num_args();
                while (j > 0) {
                    --j;
                    expr * arg = to_app(t)->get_arg(j);
                    VISIT(arg);
                }
            }
        }
        
        void collect_num_occs(goal const & g) {
            if (m_max_occs == UINT_MAX)
                return; // no need to compute num occs
            m_num_occs.reset();
            expr_fast_mark1 visited;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++)
                collect_num_occs(g.form(i), visited);
        }
        
        unsigned get_num_steps() const {
            return m_num_steps;
        }
        
        unsigned get_num_eliminated_vars() const {
            return m_num_eliminated_vars;
        }
        
        void operator()(goal_ref const & g, goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            model_converter_ref mc;
            tactic_report report("solve_eqs", *g);
            m_produce_models = g->models_enabled();
            m_produce_proofs = g->proofs_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();

            if (!g->inconsistent()) {
                m_subst      = alloc(expr_substitution, m(), m_produce_unsat_cores, m_produce_proofs);
                m_norm_subst = alloc(expr_substitution, m(), m_produce_unsat_cores, m_produce_proofs);
                while (true) {
                    if (m_context_solve) {
                        distribute_and_or(*(g.get()));
                    }
                    collect_num_occs(*g);
                    collect(*g);
                    if (m_context_solve) {
                        collect_hoist(*g);
                    }
                    if (m_subst->empty()) {
                        break;
                    }
                    sort_vars();
                    if (m_ordered_vars.empty()) {
                        break;
                    }
                    normalize();
                    substitute(*(g.get()));
                    if (g->inconsistent()) {
                        break;
                    }
                    save_elim_vars(mc);
                    TRACE("solve_eqs_round", g->display(tout); if (mc) mc->display(tout););
                }
            }
            g->inc_depth();
            g->add(mc.get());
            result.push_back(g.get());
            TRACE("solve_eqs", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    solve_eqs_tactic(ast_manager & m, params_ref const & p, expr_replacer * r, bool owner):
        m_params(p) {
        m_imp = alloc(imp, m, p, r, owner);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(solve_eqs_tactic, m, m_params, mk_expr_simp_replacer(m, m_params), true);
    }
        
    ~solve_eqs_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {        
        r.insert("solve_eqs_max_occs", CPK_UINT, "(default: infty) maximum number of occurrences for considering a variable for gaussian eliminations.");
        r.insert("theory_solver", CPK_BOOL, "(default: true) use theory solvers.");
        r.insert("ite_solver", CPK_BOOL, "(default: true) use if-then-else solver.");
        r.insert("context_solve", CPK_BOOL, "(default: false) solve equalities under disjunctions.");
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
        report_tactic_progress(":num-elim-vars", m_imp->get_num_eliminated_vars());
    }
    
    void cleanup() override {
        unsigned num_elim_vars = m_imp->m_num_eliminated_vars;
        ast_manager & m = m_imp->m();
        expr_replacer * r = m_imp->m_r;
        if (r)
            r->set_substitution(nullptr);
        bool owner = m_imp->m_r_owner;
        m_imp->m_r_owner  = false; // stole replacer

        imp * d = alloc(imp, m, m_params, r, owner);
        d->m_num_eliminated_vars = num_elim_vars;
        std::swap(d, m_imp);        
        dealloc(d);
    }

    void collect_statistics(statistics & st) const override {
        st.update("eliminated vars", m_imp->get_num_eliminated_vars());
    }

    void reset_statistics() override {
        m_imp->m_num_eliminated_vars = 0;
    }
    
};

tactic * mk_solve_eqs_tactic(ast_manager & m, params_ref const & p, expr_replacer * r) {
    if (r == nullptr)
        return clean(alloc(solve_eqs_tactic, m, p, mk_expr_simp_replacer(m, p), true));
    else
        return clean(alloc(solve_eqs_tactic, m, p, r, false));
}
