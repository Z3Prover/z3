/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    gaussian_elim.cpp

Abstract:

    (extended) Gaussian elimination for assertion sets.
    It also supports other theories besides arithmetic.

Author:

    Leonardo (leonardo) 2011-04-29

Notes:

--*/
#include"gaussian_elim.h"
#include"ast.h"
#include"expr_replacer.h"
#include"model_converter.h"
#include"assertion_set.h"
#include"ast_smt2_pp.h"
#include"elim_var_model_converter.h"
#include"occurs.h"
#include"cooperate.h"
#include"assertion_set_util.h"

struct gaussian_elim::imp {
    ast_manager &                m_manager;
    expr_replacer *              m_r;
    bool                         m_r_owner;
    arith_util                   m_a_util;
    obj_map<expr, unsigned>      m_num_occs;
    unsigned                     m_num_steps;
    unsigned                     m_num_eliminated_vars;
    bool                         m_produce_models;
    bool                         m_theory_solver;
    bool                         m_ite_solver;
    unsigned                     m_max_occs;

    void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
        m_ite_solver     = p.get_bool(":ite-solver", true);
        m_theory_solver  = p.get_bool(":theory-solver", true);
        m_max_occs       = p.get_uint(":gaussian-max-occs", UINT_MAX);
    }

    typedef elim_var_model_converter gmc;

    expr_substitution    m_subst;
    expr_substitution    m_norm_subst;
    expr_sparse_mark     m_candidate_vars;
    expr_sparse_mark     m_candidate_set;
    ptr_vector<expr>     m_candidates;
    ptr_vector<app>      m_vars;
    ptr_vector<app>      m_ordered_vars;
    volatile bool        m_cancel;

    imp(ast_manager & m, params_ref const & p, expr_replacer * r, bool owner):
        m_manager(m),
        m_r(r),
        m_r_owner(r == 0 || owner),
        m_a_util(m),
        m_num_steps(0),
        m_num_eliminated_vars(0),
        m_subst(m),
        m_norm_subst(m),
        m_cancel(false) {
        updt_params(p);
        if (m_r == 0)
            m_r       = mk_default_expr_replacer(m);
    }

    ~imp() {
        if (m_r_owner)
            dealloc(m_r);
    }

    ast_manager & m() const { return m_manager; }

    bool check_occs(expr * t) const {
        if (m_max_occs == UINT_MAX)
            return true;
        unsigned num = 0;
        m_num_occs.find(t, num);
        TRACE("gaussian_check_occs", tout << mk_ismt2_pp(t, m_manager) << " num_occs: " << num << " max: " << m_max_occs << "\n";);
        return num <= m_max_occs;
    }

    // Use: (= x def) and (= def x)
    bool trivial_solve(expr * lhs, expr * rhs, app_ref & var, expr_ref & def, proof_ref & pr) {
        if (is_uninterp_const(lhs) && !m_candidate_vars.is_marked(lhs) && !occurs(lhs, rhs) && check_occs(lhs)) {
            var = to_app(lhs); 
            def = rhs;
            pr  = 0;
            return true;
        }
        else if (is_uninterp_const(rhs) && !m_candidate_vars.is_marked(rhs) && !occurs(rhs, lhs) && check_occs(rhs)) {
            var = to_app(rhs);
            def = lhs;
            if (m_manager.proofs_enabled()) 
                pr = m().mk_commutativity(m().mk_eq(lhs, rhs));
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
        
        if (m().proofs_enabled())
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

    bool solve_arith_core(app * lhs, expr * rhs, expr * eq, app_ref & var, expr_ref & def, proof_ref & pr) {
        SASSERT(m_a_util.is_add(lhs));
        bool is_int  = m_a_util.is_int(lhs);
        expr * a; 
        expr * v;
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
                     is_uninterp_const(v) && !m_candidate_vars.is_marked(v) &&
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
        if (m().proofs_enabled()) {
            pr = m().mk_rewrite(eq, m().mk_eq(var, def));
        }
        return true;
    }

    bool solve_arith(expr * lhs, expr * rhs, expr * eq, app_ref & var, expr_ref & def, proof_ref & pr) {
        return 
            (m_a_util.is_add(lhs) && solve_arith_core(to_app(lhs), rhs, eq, var, def, pr)) ||
            (m_a_util.is_add(rhs) && solve_arith_core(to_app(rhs), lhs, eq, var, def, pr));
    }

    bool solve(expr * f, app_ref & var, expr_ref & def, proof_ref & pr) {
        if (m().is_eq(f)) {
            if (trivial_solve(to_app(f)->get_arg(0), to_app(f)->get_arg(1), var, def, pr))
                return true;
            if (m_theory_solver) {
                expr * lhs = to_app(f)->get_arg(0);
                expr * rhs = to_app(f)->get_arg(1);
                if (solve_arith(lhs, rhs, f, var, def, pr))
                    return true;
            }
            return false;
        }

        if (m().is_iff(f))
            return trivial_solve(to_app(f)->get_arg(0), to_app(f)->get_arg(1), var, def, pr);

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
            if (m().proofs_enabled()) {
                // [rewrite]: (iff (iff l true) l)
                // [symmetry T1]: (iff l (iff l true))
                pr = m().mk_rewrite(m().mk_eq(var, def), var);
                pr = m().mk_symmetry(pr);
            }
            TRACE("gaussian_elim_bug2", tout << "eliminating: " << mk_ismt2_pp(f, m()) << "\n";);
            return true;
        }
        
        if (is_neg_literal(f)) {
            var = to_app(to_app(f)->get_arg(0));
            if (m_candidate_vars.is_marked(var))
                return false;
            def = m().mk_false();
            if (m().proofs_enabled()) {
                // [rewrite]: (iff (iff l false) ~l)
                // [symmetry T1]: (iff ~l (iff l false))
                pr = m().mk_rewrite(m().mk_eq(var, def), f);
                pr = m().mk_symmetry(pr);
            }
            return true;
        }
       
        return false;
    }

    void checkpoint() {
        if (m_cancel)
            throw gaussian_elim_exception(STE_CANCELED_MSG);
        cooperate("gaussian elimination");
    }

    /**
       \brief Start collecting candidates
    */
    void collect(assertion_set & set) {
        m_subst.reset();
        m_norm_subst.reset();
        m_r->set_substitution(0);
        m_candidate_vars.reset();
        m_candidate_set.reset();
        m_candidates.reset();
        m_vars.reset();

        app_ref  var(m());
        expr_ref  def(m());
        proof_ref pr(m());
        unsigned size = set.size();
        for (unsigned idx = 0; idx < size; idx++) {
            checkpoint();
            expr * f = set.form(idx);
            if (solve(f, var, def, pr)) {
                m_vars.push_back(var);
                m_candidates.push_back(f);
                m_candidate_set.mark(f);
                m_candidate_vars.mark(var);
                if (m().proofs_enabled()) {
                    if (pr == 0)
                        pr = set.pr(idx);
                    else
                        pr = m().mk_modus_ponens(set.pr(idx), pr);
                }
                m_subst.insert(var, def, pr);
            }
            m_num_steps++;
        }
        
        TRACE("gaussian_elim", 
              tout << "candidate vars:\n";
              ptr_vector<app>::iterator it = m_vars.begin();
              ptr_vector<app>::iterator end = m_vars.end();
              for (; it != end; ++it) {
                  tout << mk_ismt2_pp(*it, m()) << " ";
              }
              tout << "\n";);
    }
    

    void sort_vars() {
        SASSERT(m_candidates.size() == m_vars.size());
        TRACE("gaussian_elim_bug", tout << "sorting vars...\n";);
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
        ptr_vector<app>::const_iterator it  = m_vars.begin();
        ptr_vector<app>::const_iterator end = m_vars.end();
        unsigned num;
        for (; it != end; ++it) {
            checkpoint();
            app * v = *it;
            if (!m_candidate_vars.is_marked(v))
                continue;
            todo.push_back(frame(v, 0));
            while (!todo.empty()) {
            start:
                frame & fr = todo.back();
                expr * t   = fr.first;
                m_num_steps++;
                TRACE("gaussian_elim_bug", tout << "processing:\n" << mk_ismt2_pp(t, m()) << "\n";);
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
                                    expr * def = 0;
                                    proof * pr;
                                    m_subst.find(to_app(t), def, pr);
                                    SASSERT(def != 0);
                                    saved.push_back(t); 
                                    saved.push_back(def);
                                    // 

                                    m_subst.erase(t);
                                }
                                else {
                                    visiting.mark(t);
                                    fr.second = 1;
                                    expr * def = 0;
                                    proof * pr;
                                    m_subst.find(to_app(t), def, pr);
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
        it  = m_vars.begin();
        for (unsigned idx = 0; it != end; ++it, ++idx) {
            if (!m_candidate_vars.is_marked(*it)) {
                m_candidate_set.mark(m_candidates[idx], false);
            }
        }
        
        TRACE("gaussian_elim", 
              tout << "ordered vars:\n";
              ptr_vector<app>::iterator it = m_ordered_vars.begin();
              ptr_vector<app>::iterator end = m_ordered_vars.end();
              for (; it != end; ++it) {
                  SASSERT(m_candidate_vars.is_marked(*it));
                  tout << mk_ismt2_pp(*it, m()) << " ";
              }
              tout << "\n";);
        m_candidate_vars.reset();
    }

    void normalize() {
        m_norm_subst.reset();
        m_r->set_substitution(&m_norm_subst);
        
        expr_ref new_def(m());
        proof_ref new_pr(m());
        unsigned size = m_ordered_vars.size();
        for (unsigned idx = 0; idx < size; idx++) {
            checkpoint();
            expr * v   = m_ordered_vars[idx];
            expr * def = 0;
            proof * pr = 0;
            m_subst.find(v, def, pr);
            SASSERT(def != 0);
            m_r->operator()(def, new_def, new_pr);
            m_num_steps += m_r->get_num_steps() + 1;
            if (m().proofs_enabled())
                new_pr = m().mk_transitivity(pr, new_pr);
            m_norm_subst.insert(v, new_def, new_pr);
            // we updated the substituting, but we don't need to reset m_r
            // because all cached values there do not depend on v.
        }
        m_subst.reset();
        TRACE("gaussian_elim", 
              tout << "after normalizing variables\n";
              for (unsigned i = 0; i < m_ordered_vars.size(); i++) {
                  expr * v = m_ordered_vars[i];
                  expr * def = 0;
                  proof * pr = 0;
                  m_norm_subst.find(v, def, pr);
                  tout << mk_ismt2_pp(v, m()) << "\n----->\n" << mk_ismt2_pp(def, m()) << "\n\n";
              });
#if 0
        DEBUG_CODE({
              for (unsigned i = 0; i < m_ordered_vars.size(); i++) {
                  expr * v = m_ordered_vars[i];
                  expr * def = 0;
                  proof * pr = 0;
                  m_norm_subst.find(v, def, pr);
                  SASSERT(def != 0);
                  CASSERT("gaussian_elim_bug", !occurs(v, def));
              }
        });
#endif
    }

    void substitute(assertion_set & set) {
        // force the cache of m_r to be reset.
        m_r->set_substitution(&m_norm_subst);
     
        expr_ref new_f(m());
        proof_ref new_pr(m());
        unsigned size = set.size();
        for (unsigned idx = 0; idx < size; idx++) {
            checkpoint();
            expr * f = set.form(idx);
            TRACE("gaussian_leak", tout << "processing:\n" << mk_ismt2_pp(f, m()) << "\n";);
            if (m_candidate_set.is_marked(f)) {
                // f may be deleted after the following update.
                // so, we must remove remove the mark before doing the update
                m_candidate_set.mark(f, false);
                SASSERT(!m_candidate_set.is_marked(f));
                set.update(idx, m().mk_true(), m().mk_true_proof());
                m_num_steps ++;
                continue;
            }
            else {
                m_r->operator()(f, new_f, new_pr);
            }
            TRACE("gaussian_elim_subst", tout << mk_ismt2_pp(f, m()) << "\n--->\n" << mk_ismt2_pp(new_f, m()) << "\n";);
            m_num_steps += m_r->get_num_steps() + 1;
            if (m().proofs_enabled()) {
                new_pr = m().mk_modus_ponens(set.pr(idx), new_pr);
            }
            set.update(idx, new_f, new_pr);
            if (set.inconsistent())
                return;
        }
        set.elim_true();
        TRACE("gaussian_elim", 
              tout << "after applying substitution\n";
              set.display(tout););
#if 0
        DEBUG_CODE({
              for (unsigned i = 0; i < m_ordered_vars.size(); i++) {
                  expr * v = m_ordered_vars[i];
                  for (unsigned j = 0; j < set.size(); j++) {
                      CASSERT("gaussian_elim_bug", !occurs(v, set.form(j)));
                  }
              }});
#endif
    }

    void save_elim_vars(model_converter_ref & mc) {
        IF_VERBOSE(100, if (!m_ordered_vars.empty()) verbose_stream() << "num. eliminated vars: " << m_ordered_vars.size() << "\n";);
        m_num_eliminated_vars += m_ordered_vars.size();
        if (m_produce_models) {
            if (mc.get() == 0)
                mc = alloc(gmc, m());
            ptr_vector<app>::iterator it  = m_ordered_vars.begin();
            ptr_vector<app>::iterator end = m_ordered_vars.end();
            for (; it != end; ++it) {
                app * v    = *it;
                expr * def = 0;
                proof * pr;
                m_norm_subst.find(v, def, pr);
                SASSERT(def != 0);
                static_cast<gmc*>(mc.get())->insert(v->get_decl(), def);
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

    void collect_num_occs(assertion_set & s) {
        if (m_max_occs == UINT_MAX)
            return; // no need to compute num occs
        m_num_occs.reset();
        expr_fast_mark1 visited;
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++)
            collect_num_occs(s.form(i), visited);
    }
    
    void operator()(assertion_set & s, model_converter_ref & mc) {
        SASSERT(is_well_sorted(s));
        as_st_report report("gaussian-elimination", s);
        TRACE("gaussian_elim", tout << "starting guassian elimination\n"; s.display(tout); tout << "\n";);
        m_num_steps = 0;
        mc        = 0;
        if (s.inconsistent())
            return;

        while (true) {
            collect_num_occs(s);
            collect(s);
            if (m_subst.empty()) 
                break;
            sort_vars();
            if (m_ordered_vars.empty())
                break;
            normalize();
            substitute(s);
            if (s.inconsistent()) {
                mc   = 0;
                break;
            }
            save_elim_vars(mc);
            TRACE("gaussian_elim_round", s.display(tout); if (mc) mc->display(tout););
        }
        TRACE("gaussian_elim", s.display(tout););
        SASSERT(is_well_sorted(s));
    }

    void set_cancel(bool f) {
        m_cancel = f;
        m_r->set_cancel(f);
    }
    
    unsigned get_num_steps() const {
        return m_num_steps;
    }

    unsigned get_num_eliminated_vars() const {
        return m_num_eliminated_vars;
    }
};

gaussian_elim::gaussian_elim(ast_manager & m, params_ref const & p, expr_replacer * r, bool owner):
    m_params(p) {
    m_imp = alloc(imp, m, p, r, owner);
}

gaussian_elim::~gaussian_elim() {
    dealloc(m_imp);
}

ast_manager & gaussian_elim::m() const {
    return m_imp->m();
}

void gaussian_elim::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void gaussian_elim::get_param_descrs(param_descrs & r) {
    insert_produce_models(r);                                        
    r.insert(":gaussian-max-occs", CPK_UINT, "(default: infty) maximum number of occurrences for considering a variable for gaussian eliminations.");
    r.insert(":theory-solver", CPK_BOOL, "(default: true) use theory solvers.");
    r.insert(":ite-solver", CPK_BOOL, "(default: true) use if-then-else solver.");
}

void gaussian_elim::operator()(assertion_set & s, model_converter_ref & mc) {
    m_imp->operator()(s, mc);
    report_st_progress(":num-elim-vars", get_num_eliminated_vars());
}

void gaussian_elim::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}

void gaussian_elim::cleanup() {
    unsigned num_elim_vars = m_imp->m_num_eliminated_vars;
    ast_manager & m   = m_imp->m();
    imp * d = m_imp;
    expr_replacer * r = m_imp->m_r_owner ? m_imp->m_r : 0;
    if (r)
        r->set_substitution(0);
    bool owner = m_imp->m_r_owner;
    m_imp->m_r_owner  = false; // stole replacer
    #pragma omp critical (as_st_cancel)
    {
        m_imp = 0;
    }
    dealloc(d);
    d = alloc(imp, m, m_params, r, owner);
    #pragma omp critical (as_st_cancel)
    {
        m_imp = d;
    }
    m_imp->m_num_eliminated_vars = num_elim_vars;
}

unsigned gaussian_elim::get_num_steps() const {
    return m_imp->get_num_steps();
}

unsigned gaussian_elim::get_num_eliminated_vars() const {
    return m_imp->get_num_eliminated_vars();
}

void gaussian_elim::collect_statistics(statistics & st) const {
    st.update("eliminated vars", get_num_eliminated_vars());
}

void gaussian_elim::reset_statistics() {
    m_imp->m_num_eliminated_vars = 0;
}

as_st * mk_gaussian(ast_manager & m, params_ref const & p) {
    return clean(alloc(gaussian_elim, m, p, mk_expr_simp_replacer(m, p), true));
}
