/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_arrays.cpp

Abstract:

    Model based projection for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/


#include "util/lbool.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "model/model_evaluator.h"
#include "qe/qe_arrays.h"
#include "qe/qe_term_graph.h"


namespace {
    bool is_partial_eq (app* a);

    /**
     * \brief utility class for partial equalities
     *
     * A partial equality (a ==I b), for two arrays a,b and a finite set of indices I holds
     *   iff (Forall i. i \not\in I => a[i] == b[i]); in other words, it is a
     *   restricted form of the extensionality axiom
     *
     * using this class, we denote (a =I b) as f(a,b,i0,i1,...)
     *   where f is an uninterpreted predicate with name PARTIAL_EQ and
     *   I = {i0,i1,...}
     */

    // TBD: make work for arrays with multiple arguments.
    class peq {
        ast_manager&        m;
        expr_ref            m_lhs;
        expr_ref            m_rhs;
        vector<expr_ref_vector>  m_diff_indices;
        func_decl_ref       m_decl;     // the partial equality declaration
        app_ref             m_peq;      // partial equality application
        app_ref             m_eq;       // equivalent std equality using def. of partial eq
        array_util          m_arr_u;

    public:
        static const char* PARTIAL_EQ;

        peq (app* p, ast_manager& m):
            m (m),
            m_lhs (p->get_arg (0), m),
            m_rhs (p->get_arg (1), m),
            m_decl (p->get_decl (), m),
            m_peq (p, m),
            m_eq (m),
            m_arr_u (m)
        {
            VERIFY (is_partial_eq (p));
            SASSERT (m_arr_u.is_array (m_lhs) &&
                     m_arr_u.is_array (m_rhs) &&
                     m.get_sort(m_lhs) == m.get_sort(m_rhs));
            unsigned arity = get_array_arity(m.get_sort(m_lhs));
            for (unsigned i = 2; i < p->get_num_args (); i += arity) {
                SASSERT(arity + i <= p->get_num_args());
                expr_ref_vector vec(m);
                vec.append(arity, p->get_args() + i);
                m_diff_indices.push_back (vec);
            }
        }

        peq (expr* lhs, expr* rhs, vector<expr_ref_vector> const& diff_indices, ast_manager& m):
            m (m),
            m_lhs (lhs, m),
            m_rhs (rhs, m),
            m_diff_indices (diff_indices),
            m_decl (m),
            m_peq (m),
            m_eq (m),
            m_arr_u (m) {
            SASSERT (m_arr_u.is_array (lhs) &&
                     m_arr_u.is_array (rhs) &&
                     m.get_sort(lhs) == m.get_sort(rhs));
            ptr_vector<sort> sorts;
            sorts.push_back (m.get_sort (m_lhs));
            sorts.push_back (m.get_sort (m_rhs));
            for (auto const& v : diff_indices) {
                SASSERT(v.size() == get_array_arity(m.get_sort(m_lhs)));
                for (expr* e : v)
                    sorts.push_back (m.get_sort(e));
            }
            m_decl = m.mk_func_decl (symbol (PARTIAL_EQ), sorts.size (), sorts.c_ptr (), m.mk_bool_sort ());
        }

        expr_ref lhs () { return m_lhs; }

        expr_ref rhs () { return m_rhs; }

        void get_diff_indices (vector<expr_ref_vector>& result) { result.append(m_diff_indices); }

        app_ref mk_peq () {
            if (!m_peq) {
                ptr_vector<expr> args;
                args.push_back (m_lhs);
                args.push_back (m_rhs);
                for (auto const& v : m_diff_indices) {
                    args.append (v.size(), v.c_ptr());
                }
                m_peq = m.mk_app (m_decl, args.size (), args.c_ptr ());
            }
            return m_peq;
        }

        app_ref mk_eq (app_ref_vector& aux_consts, bool stores_on_rhs = true) {
            if (!m_eq) {
                expr_ref lhs (m_lhs, m), rhs (m_rhs, m);
                if (!stores_on_rhs) {
                    std::swap (lhs, rhs);
                }
                // lhs = (...(store (store rhs i0 v0) i1 v1)...)
                sort* val_sort = get_array_range (m.get_sort (lhs));
                for (expr_ref_vector const& diff : m_diff_indices) {
                    ptr_vector<expr> store_args;
                    store_args.push_back (rhs);
                    store_args.append (diff.size(), diff.c_ptr());
                    app_ref val(m.mk_fresh_const ("diff", val_sort), m);
                    store_args.push_back (val);
                    aux_consts.push_back (val);
                    rhs = m_arr_u.mk_store (store_args);
                }
                m_eq = m.mk_eq (lhs, rhs);
            }
            return m_eq;
        }
    };

    const char* peq::PARTIAL_EQ = "!partial_eq";

    bool is_partial_eq (app* a) {
        return a->get_decl ()->get_name () == peq::PARTIAL_EQ;
    }
}

namespace qe {


    static bool is_eq(expr_ref_vector const& xs, expr_ref_vector const& ys) {
        for (unsigned i = 0; i < xs.size(); ++i) if (xs[i] != ys[i]) return false;
        return true;
    }

    static expr_ref mk_eq(expr_ref_vector const& xs, expr_ref_vector const& ys) {
        ast_manager& m = xs.get_manager();
        expr_ref_vector eqs(m);
        for (unsigned i = 0; i < xs.size(); ++i) eqs.push_back(m.mk_eq(xs[i], ys[i]));
        return mk_and(eqs);
    }

    /**
     *  1. Extract all equalities (store (store .. (store x i1 v1) i2 v2) .. ) = ...
     *     where x appears and the equalities do not evaluate to false in the current model.
     *  2. Track them as partial equivalence relations.
     *  3. Sort them according to nesting depth.
     *  4. Solve for x by potentially introducing fresh variables.
     *     Thus, (store x i v) = y, then
     *     x = (store y i w), (select y i) = v, where w is fresh and evaluates to (select x i).
     *     Generally, equalities are tracked as x =_idxs y, where x, y are equal up to idxs.
     */

    class array_project_eqs_util {
        ast_manager&                m;
        array_util                  m_arr_u;
        model_ref                   M;
        model_evaluator*            m_mev;
        app_ref                     m_v;    // array var to eliminate
        ast_mark                    m_has_stores_v; // has stores for m_v
        expr_ref                    m_subst_term_v; // subst term for m_v
        expr_safe_replace           m_true_sub_v; // subst for true equalities
        expr_safe_replace           m_false_sub_v; // subst for false equalities
        expr_ref_vector             m_aux_lits_v;
        expr_ref_vector             m_idx_lits_v;
        app_ref_vector              m_aux_vars;

        void reset_v () {
            m_v = nullptr;
            m_has_stores_v.reset ();
            m_subst_term_v = nullptr;
            m_true_sub_v.reset ();
            m_false_sub_v.reset ();
            m_aux_lits_v.reset ();
            m_idx_lits_v.reset ();
        }

        void reset () {
            M = nullptr;
            m_mev = nullptr;
            reset_v ();
            m_aux_vars.reset ();
        }

        /**
         * find all array equalities on m_v or containing stores on/of m_v
         *
         * also mark terms containing stores on/of m_v
         */
        void find_arr_eqs (expr_ref const& fml, app_ref_vector& eqs) {
            if (!is_app (fml)) return;
            ast_mark done;
            ptr_vector<app> todo;
            todo.push_back (to_app (fml));
            while (!todo.empty ()) {
                app* a = todo.back ();
                if (done.is_marked (a)) {
                    todo.pop_back ();
                    continue;
                }
                bool all_done = true;
                bool args_have_stores = false;
                for (expr * arg : *a) {
                    if (!is_app (arg)) continue;
                    if (!done.is_marked (arg)) {
                        all_done = false;
                        todo.push_back (to_app (arg));
                    }
                    else if (!args_have_stores && m_has_stores_v.is_marked (arg)) {
                        args_have_stores = true;
                    }
                }
                if (!all_done) continue;
                todo.pop_back ();

                // mark if a has stores
                if ((!m_arr_u.is_select (a) && args_have_stores) ||
                    (m_arr_u.is_store (a) && (a->get_arg (0) == m_v))) {
                    m_has_stores_v.mark (a, true);

                    TRACE ("qe",
                            tout << "has stores:\n";
                            tout << mk_pp (a, m) << "\n";
                          );
                }

                // check if a is a relevant array equality
                expr * a0 = nullptr, *a1 = nullptr;
                if (m.is_eq (a, a0, a1)) {
                    if (a0 == m_v || a1 == m_v ||
                        (m_arr_u.is_array (a0) && m_has_stores_v.is_marked (a))) {
                        eqs.push_back (a);
                    }
                }
                // else, we can check for disequalities and handle them using extensionality,
                // but it's not necessary

                done.mark (a, true);
            }
        }

        /**
         * factor out select terms on m_v using fresh consts
         */
        void factor_selects (app_ref& fml) {
            expr_map sel_cache (m);
            ast_mark done;
            ptr_vector<app> todo;
            expr_ref_vector pinned (m); // to ensure a reference

            todo.push_back (fml);
            while (!todo.empty ()) {
                app* a = todo.back ();
                if (done.is_marked (a)) {
                    todo.pop_back ();
                    continue;
                }
                expr_ref_vector args (m);
                bool all_done = true;
                for (expr * arg : *a) {
                    if (!is_app (arg)) {
                        args.push_back(arg);
                    }
                    else if (!done.is_marked (arg)) {
                        all_done = false;
                        todo.push_back (to_app (arg));
                    }
                    else if (all_done) { // all done so far..
                        expr* arg_new = nullptr; proof* pr;
                        sel_cache.get (arg, arg_new, pr);
                        if (!arg_new) {
                            arg_new = arg;
                        }
                        args.push_back (arg_new);
                    }
                }
                if (!all_done) continue;
                todo.pop_back ();

                expr_ref a_new (m.mk_app (a->get_decl (), args.size (), args.c_ptr ()), m);

                // if a_new is select on m_v, introduce new constant
                if (m_arr_u.is_select (a) &&
                    (args.get (0) == m_v || m_has_stores_v.is_marked (args.get (0)))) {
                    sort* val_sort = get_array_range (m.get_sort (m_v));
                    app_ref val_const (m.mk_fresh_const ("sel", val_sort), m);
                    m_aux_vars.push_back (val_const);
                    // extend M to include val_const
                    expr_ref val = (*m_mev)(a_new);
                    M->register_decl (val_const->get_decl (), val);
                    // add equality
                    m_aux_lits_v.push_back (m.mk_eq (val_const, a_new));
                    // replace select by const
                    a_new = val_const;
                }

                if (a != a_new) {
                    sel_cache.insert (a, a_new, nullptr);
                    pinned.push_back (a_new);
                }
                done.mark (a, true);
            }
            expr* res = nullptr; proof* pr;
            sel_cache.get (fml, res, pr);
            if (res) {
                fml = to_app (res);
            }
        }

        /**
         * convert partial equality expression p_exp to an equality by
         * recursively adding stores on diff indices
         *
         * add stores on lhs or rhs depending on whether stores_on_rhs is false/true
         */
        void convert_peq_to_eq (expr* p_exp, app_ref& eq, bool stores_on_rhs = true) {
            peq p (to_app (p_exp), m);
            app_ref_vector diff_val_consts (m);
            eq = p.mk_eq (diff_val_consts, stores_on_rhs);
            m_aux_vars.append (diff_val_consts);
            // extend M to include diff_val_consts
            vector<expr_ref_vector> I;
            expr_ref arr = p.lhs ();
            p.get_diff_indices (I);
            expr_ref val (m);
            unsigned num_diff = diff_val_consts.size ();
            SASSERT (num_diff == I.size ());
            for (unsigned i = 0; i < num_diff; i++) {
                // mk val term
                ptr_vector<expr> sel_args;
                sel_args.push_back (arr);
                sel_args.append(I[i].size(), I[i].c_ptr());
                expr_ref val_term (m_arr_u.mk_select (sel_args), m);
                // evaluate and assign to ith diff_val_const
                val = (*m_mev)(val_term);
                M->register_decl (diff_val_consts.get (i)->get_decl (), val);
            }
        }

        /**
         * mk (e0 ==indices e1)
         *
         * result has stores if either e0 or e1 or an index term has stores
         */
        app_ref mk_peq (expr* e0, expr* e1, vector<expr_ref_vector> const& indices) {
            peq p (e0, e1, indices, m);
            return p.mk_peq ();
        }

        void find_subst_term (app* eq) {
            SASSERT(m.is_eq(eq));
            vector<expr_ref_vector> empty;
            app_ref p_exp = mk_peq (eq->get_arg (0), eq->get_arg (1), empty);
            bool subst_eq_found = false;
            while (true) {
                TRACE ("qe", tout << "processing peq:\n" << p_exp << "\n";);

                peq p (p_exp, m);
                expr_ref lhs = p.lhs(), rhs = p.rhs();
                if (!m_has_stores_v.is_marked (lhs)) {
                    std::swap (lhs, rhs);
                }
                if (m_has_stores_v.is_marked (lhs) && m_arr_u.is_store(lhs)) {
                    /** project using the equivalence:
                     *
                     *  (store(arr0,idx,x) ==I arr1) <->
                     *
                     *  (idx \in I => (arr0 ==I arr1)) /\
                     *  (idx \not\in I => (arr0 ==I+idx arr1) /\ (arr1[idx] == x)))
                     */
                    vector<expr_ref_vector> I;
                    expr_ref_vector idxs (m);
                    p.get_diff_indices (I);
                    app* a_lhs = to_app (lhs);
                    expr* arr0 = a_lhs->get_arg (0);
                    idxs.append(a_lhs->get_num_args() - 2, a_lhs->get_args() + 1);
                    expr* x = a_lhs->get_arg (2);
                    expr* arr1 = rhs;
                    // check if (idx \in I) in M
                    bool idx_in_I = false;
                    expr_ref_vector idx_diseq (m);
                    if (!I.empty ()) {
                        expr_ref_vector vals = (*m_mev)(idxs);
                        for (unsigned i = 0; i < I.size () && !idx_in_I; i++) {
                            if (is_eq(idxs, I.get(i))) {
                                idx_in_I = true;
                            }
                            else {
                                expr_ref idx_eq = mk_eq(idxs, I[i]);
                                expr_ref_vector vals1 = (*m_mev)(I[i]);
                                if (is_eq(vals, vals1)) {
                                    idx_in_I = true;
                                    m_idx_lits_v.push_back (idx_eq);
                                }
                                else {
                                    idx_diseq.push_back (m.mk_not (idx_eq));
                                }
                            }
                        }
                    }
                    if (idx_in_I) {
                        TRACE ("qe",
                                tout << "store index in diff indices:\n";
                                tout << mk_pp (m_idx_lits_v.back (), m) << "\n";
                              );

                        // arr0 ==I arr1
                        p_exp = mk_peq (arr0, arr1, I);

                        TRACE ("qe",
                                tout << "new peq:\n";
                                tout << mk_pp (p_exp, m) << "\n";
                              );
                    }
                    else {
                        m_idx_lits_v.append (idx_diseq);
                        // arr0 ==I+idx arr1
                        I.push_back (idxs);
                        p_exp = mk_peq (arr0, arr1, I);

                        TRACE ("qe", tout << "new peq:\n" << p_exp << "\n"; );

                        // arr1[idx] == x
                        ptr_vector<expr> sel_args;
                        sel_args.push_back (arr1);
                        sel_args.append(idxs.size(), idxs.c_ptr());
                        expr_ref arr1_idx (m_arr_u.mk_select (sel_args), m);
                        expr_ref eq (m.mk_eq (arr1_idx, x), m);
                        m_aux_lits_v.push_back (eq);

                        TRACE ("qe",
                                tout << "new eq:\n";
                                tout << mk_pp (eq, m) << "\n";
                              );
                    }
                }
                else if (lhs == rhs) { // trivial peq (a ==I a)
                    break;
                }
                else if (lhs == m_v || rhs == m_v) {
                    subst_eq_found = true;
                    TRACE ("qe",
                            tout << "subst eq found!\n";
                          );
                    break;
                }
                else {
                    UNREACHABLE ();
                }
            }

            // factor out select terms on m_v from p_exp using fresh constants
            if (subst_eq_found) {
                factor_selects (p_exp);

                TRACE ("qe",
                        tout << "after factoring selects:\n";
                        tout << mk_pp (p_exp, m) << "\n";
                        for (unsigned i = m_aux_lits_v.size () - m_aux_vars.size (); i < m_aux_lits_v.size (); i++) {
                            tout << mk_pp (m_aux_lits_v.get (i), m) << "\n";
                        }
                      );

                // find subst_term
                bool stores_on_rhs = true;
                app* a = to_app (p_exp);
                if (a->get_arg (1) == m_v) {
                    stores_on_rhs = false;
                }
                app_ref eq (m);
                convert_peq_to_eq (p_exp, eq, stores_on_rhs);
                m_subst_term_v = eq->get_arg (1);

                TRACE ("qe",
                        tout << "subst term found:\n";
                        tout << mk_pp (m_subst_term_v, m) << "\n";
                      );
            }
        }

        /**
         * compute nesting depths of stores on m_v in true_eqs, as follows:
         * 0 if m_v appears on both sides of equality
         * 1 if equality is (m_v=t)
         * 2 if equality is (store(m_v,i,v)=t)
         * ...
         */
        unsigned get_nesting_depth(app* eq) {
            expr* lhs = nullptr, *rhs = nullptr;
            VERIFY(m.is_eq(eq, lhs, rhs));
            bool lhs_has_v = (lhs == m_v || m_has_stores_v.is_marked (lhs));
            bool rhs_has_v = (rhs == m_v || m_has_stores_v.is_marked (rhs));
            app* store = nullptr;

            SASSERT (lhs_has_v || rhs_has_v);

            if (!lhs_has_v && is_app(rhs)) {
                store = to_app (rhs);
            }
            else if (!rhs_has_v && is_app(lhs)) {
                store = to_app (lhs);
            }
            else {
                // v appears on both sides -- trivial equality
                // put it in the beginning to simplify it away
                return 0;
            }

            unsigned nd = 0; // nesting depth
            for (nd = 1; m_arr_u.is_store (store); nd++, store = to_app (store->get_arg (0))) {
                /* empty */ ;
            }
            if (store != m_v) {
                TRACE("qe", tout << "not a store " << mk_pp(eq, m) << " " << lhs_has_v << " " << rhs_has_v << " " << mk_pp(m_v, m) << "\n";);
                return UINT_MAX;
            }
            return nd;
        }

        struct compare_nd {
            bool operator()(std::pair<unsigned, app*> const& x, std::pair<unsigned, app*> const& y) const {
                return x < y;
            }
        };

        /**
         * try to substitute for m_v, using array equalities
         *
         * compute substitution term and aux lits
         */
        bool project (expr_ref const& fml) {
            app_ref_vector eqs (m);
            svector<std::pair<unsigned, app*> > true_eqs;

            find_arr_eqs (fml, eqs);
            TRACE ("qe", tout << "array equalities:\n" << eqs << "\n";);

            // evaluate eqs in M
            for (app * eq : eqs) {
                TRACE ("qe", tout << "array equality:\n" << mk_pp (eq, m) << "\n"; );

                if (m_mev->is_false(eq)) {
                    m_false_sub_v.insert (eq, m.mk_false());
                }
                else {
                    true_eqs.push_back (std::make_pair(get_nesting_depth(eq), eq));
                }
            }
            std::sort(true_eqs.begin(), true_eqs.end(), compare_nd());
            DEBUG_CODE(for (unsigned i = 0; i + 1 < true_eqs.size(); ++i) SASSERT(true_eqs[i].first <= true_eqs[i+1].first););

            // search for subst term
            for (unsigned i = 0; !m_subst_term_v && i < true_eqs.size(); i++) {
                app* eq = true_eqs[i].second;
                m_true_sub_v.insert (eq, m.mk_true ());
                // try to find subst term
                find_subst_term (eq);
            }

            return true;
        }

        void mk_result (expr_ref& fml) {
            th_rewriter rw(m);
            rw (fml);
            // add in aux_lits and idx_lits
            expr_ref_vector lits (m);
            // TODO: eliminate possible duplicates, especially in idx_lits
            //       theory rewriting is a possibility, but not sure if it
            //          introduces unwanted terms such as ite's
            lits.append (m_idx_lits_v);
            lits.append (m_aux_lits_v);
            lits.push_back (fml);
            fml = mk_and(lits);

            if (m_subst_term_v) {
                m_true_sub_v.insert (m_v, m_subst_term_v);
                m_true_sub_v (fml);
            }
            else {
                m_true_sub_v (fml);
                m_false_sub_v (fml);
            }
            rw(fml);
            SASSERT (!m.is_false (fml));
        }

    public:

        array_project_eqs_util (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_v (m),
            m_subst_term_v (m),
            m_true_sub_v (m),
            m_false_sub_v (m),
            m_aux_lits_v (m),
            m_idx_lits_v (m),
            m_aux_vars (m)
        {}

        void operator () (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
            reset ();
            model_evaluator mev(mdl);
            mev.set_model_completion(true);
            M = &mdl;
            m_mev = &mev;

            unsigned j = 0;
            for (unsigned i = 0; i < arr_vars.size (); i++) {
                reset_v ();
                m_v = arr_vars.get (i);
                if (!m_arr_u.is_array (m_v)) {
                    TRACE ("qe",
                            tout << "not an array variable: " << m_v << "\n";
                          );
                    aux_vars.push_back (m_v);
                    continue;
                }
                TRACE ("qe", tout << "projecting equalities on variable: " << m_v << "\n"; );

                if (project (fml)) {
                    mk_result (fml);

                    contains_app contains_v (m, m_v);
                    if (!m_subst_term_v || contains_v (m_subst_term_v)) {
                        arr_vars[j++] = m_v;
                    }
                    TRACE ("qe", tout << "after projection: \n" << fml << "\n";);
                }
                else {
                    IF_VERBOSE(2, verbose_stream() << "can't project:" << m_v << "\n";);
                    TRACE ("qe", tout << "Failed to project: " << m_v << "\n";);
                    arr_vars[j++] = m_v;
                }
            }
            arr_vars.shrink(j);
            aux_vars.append (m_aux_vars);
        }
    };

    /**
     *  Eliminate (select (store ..) ..) redexes by evaluating indices under model M.
     *  This does not eliminate variables, but introduces additional constraints on index equalities.
     */

    class array_select_reducer {
        ast_manager&                m;
        array_util                  m_arr_u;
        obj_map<expr, expr*>        m_cache;
        expr_ref_vector             m_pinned;   // to ensure a reference
        expr_ref_vector             m_idx_lits;
        model_ref                   M;
        model_evaluator*            m_mev;
        th_rewriter                 m_rw;
        ast_mark                    m_arr_test;
        ast_mark                    m_has_stores;
        bool                        m_reduce_all_selects;

        void reset () {
            m_cache.reset ();
            m_pinned.reset ();
            m_idx_lits.reset ();
            M = nullptr;
            m_mev = nullptr;
            m_arr_test.reset ();
            m_has_stores.reset ();
            m_reduce_all_selects = false;
        }

        bool is_equals (expr *e1, expr *e2) {
            return e1 == e2 || (*m_mev)(e1) == (*m_mev)(e2);
        }

        bool is_equals (unsigned arity, expr * const* xs, expr * const * ys) {
            for (unsigned i = 0; i < arity; ++i) {
                if (!is_equals(xs[i], ys[i])) return false;
            }
            return true;
        }

        expr_ref mk_eq(unsigned arity, expr * const* xs, expr * const * ys) {
            expr_ref_vector r(m);
            for (unsigned i = 0; i < arity; ++i) {
                r.push_back(m.mk_eq(xs[i], ys[i]));
            }
            return mk_and(r);
        }

        void add_idx_cond (expr_ref& cond) {
            m_rw (cond);
            if (!m.is_true (cond)) m_idx_lits.push_back (cond);
        }

        bool has_stores (expr* e) {
            if (m_reduce_all_selects) return true;
            return m_has_stores.is_marked (e);
        }

        void mark_stores (app* a, bool args_have_stores) {
            if (m_reduce_all_selects) return;
            if (args_have_stores ||
                (m_arr_u.is_store (a) && m_arr_test.is_marked (a->get_arg (0)))) {
                m_has_stores.mark (a, true);
            }
        }

        bool reduce (expr_ref& e) {
            if (!is_app (e)) return true;

            expr *r = nullptr;
            if (m_cache.find (e, r)) {
                e = r;
                return true;
            }

            ptr_vector<app> todo;
            todo.push_back (to_app (e));
            expr_ref_vector args (m);

            while (!todo.empty ()) {
                app *a = todo.back ();
                unsigned sz = todo.size ();
                bool dirty = false;
                bool args_have_stores = false;
                args.reset();
                for (expr * arg : *a) {
                    expr *narg = nullptr;
                    if (!is_app (arg)) {
                        args.push_back (arg);
                    }
                    else if (m_cache.find (arg, narg)) {
                        args.push_back (narg);
                        dirty |= (arg != narg);
                        if (!args_have_stores && has_stores (narg)) {
                            args_have_stores = true;
                        }
                    }
                    else {
                        todo.push_back (to_app (arg));
                    }
                }

                if (todo.size () > sz) continue;
                todo.pop_back ();

                if (dirty) {
                    r = m.mk_app (a->get_decl (), args.size (), args.c_ptr ());
                    m_pinned.push_back (r);
                }
                else {
                    r = a;
                }

                if (m_arr_u.is_select (r) && has_stores (to_app (r)->get_arg (0))) {
                    r = reduce_core (to_app(r));
                }
                else {
                    mark_stores (to_app (r), args_have_stores);
                }

                m_cache.insert (a, r);
            }

            SASSERT (r);
            e = r;
            return true;
        }

        /**
         * \brief reduce (select (store (store x i1 v1) i2 v2) idx) under model M
         *        such that the result is v2 if idx = i2 under M, it is v1 if idx = i1, idx != i2 under M,
         *        and it is (select x idx) if idx != i1, idx !+ i2 under M.
         */
        expr* reduce_core (app *a) {
            if (!m_arr_u.is_store (a->get_arg (0))) return a;
            expr* array = a->get_arg(0);
            unsigned arity = get_array_arity(m.get_sort(array));

            expr* const* js = a->get_args() + 1;

            while (m_arr_u.is_store (array)) {
                a = to_app (array);
                expr* const* idxs = a->get_args() + 1;
                expr_ref cond = mk_eq(arity, idxs, js);

                if (is_equals (arity, idxs, js)) {
                    add_idx_cond (cond);
                    return a->get_arg (a->get_num_args() - 1);
                }
                else {
                    cond = m.mk_not (cond);
                    add_idx_cond (cond);
                    array = a->get_arg (0);
                }
            }
            ptr_vector<expr> args;
            args.push_back(array);
            args.append(arity, js);
            expr* r = m_arr_u.mk_select (args);
            m_pinned.push_back (r);
            return r;
        }

        void mk_result (expr_ref& fml) {
            // conjoin idx lits
            expr_ref_vector lits (m);
            lits.append (m_idx_lits);
            lits.push_back (fml);
            fml = mk_and(lits);
            // simplify all trivial expressions introduced
            m_rw (fml);
            TRACE ("qe", tout << "after reducing selects:\n" << fml << "\n";);
        }

    public:

        array_select_reducer (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_pinned (m),
            m_idx_lits (m),
            m_rw (m),
            m_reduce_all_selects (false)
        {}

        void operator () (model& mdl, app_ref_vector const& arr_vars, expr_ref& fml, bool reduce_all_selects = false) {
            if (!reduce_all_selects && arr_vars.empty ()) return;

            reset ();
            model_evaluator mev(mdl);
            mev.set_model_completion(true);
            M = &mdl;
            m_mev = &mev;
            m_reduce_all_selects = reduce_all_selects;

            // mark vars to eliminate
            for (app* v : arr_vars) {
                m_arr_test.mark (v, true);
            }

            // assume all arr_vars are of array sort
            // and assume no store equalities on arr_vars
            if (reduce (fml)) {
                mk_result (fml);
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "can't project arrays:" << "\n";);
                TRACE ("qe", tout << "Failed to project arrays\n";);
            }
        }
    };

    /**
     * Perform Ackerman reduction on arrays.
     *  for occurrences (select a i1), (select a i2), ... assuming these are all occurrences.
     *  - collect i1, i2, i3, into equivalence classes according to M
     *  - for distinct index classes accumulate constraint i1 < i2 < i3 .. (for arithmetic)
     *    and generally distinct(i1, i2, i3) for arbitrary index sorts.
     *  - for equal indices accumulate constraint i1 = i2, i3 = i5, ..
     *  - introduce variables v1, v2, .., for each equivalence class.
     *  - replace occurrences of select by v1, v2, ...
     *  - update M to evaluate v1, v2, the same as (select a i1) (select a i2)
     */

    class array_project_selects_util {
        typedef obj_map<app, ptr_vector<app>*> sel_map;

        struct idx_val {
            expr_ref_vector idx;
            expr_ref_vector val;
            vector<rational> rval;
            idx_val(expr_ref_vector & idx, expr_ref_vector & val, vector<rational> const& rval): idx(idx), val(val), rval(rval) {}
            idx_val& operator=(idx_val const& o) {
                idx.reset(); val.reset(); rval.reset();
                idx.append(o.idx); val.append(o.val); rval.append(o.rval);
                return *this;
            }
        };
        ast_manager&                m;
        array_util                  m_arr_u;
        arith_util                  m_ari_u;
        bv_util                     m_bv_u;
        sel_map                     m_sel_terms;
        // representative indices for eliminating selects
        vector<idx_val>             m_idxs;
        app_ref_vector              m_sel_consts;
        expr_ref_vector             m_idx_lits;
        model_ref                   M;
        model_evaluator*            m_mev;
        expr_safe_replace           m_sub;
        ast_mark                    m_arr_test;

        void reset () {
            m_sel_terms.reset ();
            m_idxs.reset();
            m_sel_consts.reset ();
            m_idx_lits.reset ();
            M = nullptr;
            m_mev = nullptr;
            m_sub.reset ();
            m_arr_test.reset ();
        }

        /**
         * collect sel terms on array vars as given by m_arr_test
         */
        void collect_selects (expr* fml) {
            if (!is_app (fml)) return;
            ast_mark done;
            ptr_vector<app> todo;
            todo.push_back (to_app (fml));
            for (unsigned i = 0; i < todo.size(); ++i) {
                app* a = todo[i];
                if (done.is_marked (a)) continue;
                done.mark (a, true);
                for (expr* arg : *a) {
                    if (!done.is_marked (arg) && is_app (arg)) {
                        todo.push_back (to_app (arg));
                    }
                }
                if (m_arr_u.is_select (a)) {
                    expr* arr = a->get_arg (0);
                    if (m_arr_test.is_marked (arr)) {
                        ptr_vector<app>* lst = m_sel_terms.find (to_app (arr));;
                        lst->push_back (a);
                    }
                }
            }
        }

        vector<rational> to_num(expr_ref_vector const& vals) {
            vector<rational> rs;
            rational r;
            for (expr* v : vals) {
                if (m_bv_u.is_bv(v)) {
                    VERIFY (m_bv_u.is_numeral(v, r));
                }
                else if (m_ari_u.is_real(v) || m_ari_u.is_int(v)) {
                    VERIFY (m_ari_u.is_numeral(v, r));
                }
                else {
                    r.reset();
                }
                rs.push_back(r);
            }
            return rs;
        }

        struct compare_idx {
            array_project_selects_util& u;
            compare_idx(array_project_selects_util& u):u(u) {}
            bool operator()(idx_val const& x, idx_val const& y) {
                SASSERT(x.rval.size() == y.rval.size());
                for (unsigned j = 0; j < x.rval.size(); ++j) {
                    rational const& xv = x.rval[j];
                    rational const& yv = y.rval[j];
                    if (xv < yv) return true;
                    if (xv > yv) return false;
                }
                return false;
            }
        };

        expr* mk_lt(expr* x, expr* y) {
            if (m_bv_u.is_bv(x)) {
                return m.mk_not(m_bv_u.mk_ule(y, x));
            }
            else {
                return m_ari_u.mk_lt(x, y);
            }
        }

        expr_ref mk_lex_lt(expr_ref_vector const& xs, expr_ref_vector const& ys) {
            SASSERT(xs.size() == ys.size() && !xs.empty());
            expr_ref result(mk_lt(xs.back(), ys.back()), m);
            for (unsigned i = xs.size()-1; i-- > 0; ) {
                result = m.mk_or(mk_lt(xs[i], ys[i]),
                                 m.mk_and(m.mk_eq(xs[i], ys[i]), result));
            }
            return result;
        }

        /**
         * model based ackermannization for sel terms of some array
         *
         * update sub with val consts for sel terms
         */
        void ackermann (ptr_vector<app> const& sel_terms) {
            if (sel_terms.empty ()) return;

            expr* v = sel_terms.get (0)->get_arg (0); // array variable
            sort* v_sort = m.get_sort (v);
            sort* val_sort = get_array_range (v_sort);
            unsigned arity = get_array_arity(v_sort);
            bool is_numeric = true;
            for (unsigned i = 0; i < arity && is_numeric; ++i) {
                sort* srt = get_array_domain(v_sort, i);
                if (!m_ari_u.is_real(srt) && !m_ari_u.is_int(srt) && !m_bv_u.is_bv_sort(srt)) {
                    TRACE("qe", tout << "non-numeric index sort for Ackerman" << mk_pp(srt, m) << "\n";);
                    is_numeric = false;
                }
            }

            unsigned start = m_idxs.size (); // append at the end
            for (app * a : sel_terms) {
                expr_ref_vector idxs(m, arity, a->get_args() + 1);
                expr_ref_vector vals = (*m_mev)(idxs);
                bool is_new = true;
                for (unsigned j = start; j < m_idxs.size (); j++) {
                    if (!is_eq(m_idxs[j].val, vals)) continue;
                    // idx belongs to the jth equivalence class;
                    // substitute sel term with ith sel const
                    expr* c = m_sel_consts.get (j);
                    m_sub.insert (a, c);
                    // add equality (idx == repr)
                    m_idx_lits.push_back (mk_eq (idxs, m_idxs[j].idx));
                    is_new = false;
                    break;
                }
                if (is_new) {
                    // new repr, val, and sel const
                    vector<rational> rvals = to_num(vals);
                    m_idxs.push_back(idx_val(idxs, vals, rvals));
                    app_ref c (m.mk_fresh_const ("sel", val_sort), m);
                    m_sel_consts.push_back (c);
                    // substitute sel term with new const
                    m_sub.insert (a, c);
                    // extend M to include c
                    expr_ref val = (*m_mev)(a);
                    M->register_decl (c->get_decl (), val);
                }
            }

            if (start + 1 == m_idxs.size()) {
                // nothing to differentiate.
            }
            else if (is_numeric) {
                // sort reprs by their value and add a chain of strict inequalities
                compare_idx cmp(*this);
                std::sort(m_idxs.begin() + start, m_idxs.end(), cmp);
                for (unsigned i = start; i + 1 < m_idxs.size(); ++i) {
                    m_idx_lits.push_back (mk_lex_lt(m_idxs[i].idx, m_idxs[i+1].idx));
                }
            }
            else if (arity == 1) {
                // create distinct constraint.
                expr_ref_vector xs(m);
                for (unsigned i = start; i < m_idxs.size(); ++i) {
                    xs.append(m_idxs[i].idx);
                }
                m_idx_lits.push_back(m.mk_distinct(xs.size(), xs.c_ptr()));
            }
            else {
                datatype::util dt(m);
                sort_ref_vector srts(m);
                ptr_vector<accessor_decl> acc;
                unsigned i = 0;
                for (expr * x : m_idxs[0].idx) {
                    std::stringstream name;
                    name << "get" << (i++);
                    acc.push_back(mk_accessor_decl(m, symbol(name.str().c_str()), type_ref(m.get_sort(x))));
                }
                constructor_decl* constrs[1] = { mk_constructor_decl(symbol("tuple"), symbol("is-tuple"), acc.size(), acc.c_ptr()) };
                datatype::def* dts = mk_datatype_decl(dt, symbol("tuple"), 0, nullptr, 1, constrs);
                VERIFY(dt.get_plugin()->mk_datatypes(1, &dts, 0, nullptr, srts));
                del_datatype_decl(dts);
                sort* tuple = srts.get(0);
                ptr_vector<func_decl> const & decls = *dt.get_datatype_constructors(tuple);
                expr_ref_vector xs(m);
                for (unsigned i = start; i < m_idxs.size(); ++i) {
                    xs.push_back(m.mk_app(decls[0], m_idxs[i].idx.size(), m_idxs[i].idx.c_ptr()));
                }
                m_idx_lits.push_back(m.mk_distinct(xs.size(), xs.c_ptr()));
            }
        }

        void mk_result (expr_ref& fml) {
            // conjoin idx lits
            m_idx_lits.push_back(fml);
            fml = mk_and (m_idx_lits);

            // substitute for sel terms
            m_sub (fml);

            TRACE ("qe", tout << "after projection of selects:\n" << fml << "\n";);
        }

        /**
         * project selects
         * populates idx lits and obtains substitution for sel terms
         */
        bool project (expr* fml) {
            // collect sel terms -- populate the map m_sel_terms
            collect_selects (fml);
            // model based ackermannization
            for (auto & kv : m_sel_terms) {
                TRACE ("qe",tout << "ackermann for var: " << mk_pp (kv.m_key, m) << "\n";);
                ackermann (*(kv.m_value));
            }
            TRACE ("qe", tout << "idx lits:\n" << m_idx_lits; );
            return true;
        }

    public:

        array_project_selects_util (ast_manager& m):
            m (m),
            m_arr_u (m),
            m_ari_u (m),
            m_bv_u (m),
            m_sel_consts (m),
            m_idx_lits (m),
            m_sub (m)
        {}

        void operator () (model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars) {
            if (arr_vars.empty()) return;
            reset ();
            model_evaluator mev(mdl);
            mev.set_model_completion(true);
            M = &mdl;
            m_mev = &mev;

            // mark vars to eliminate
            // alloc empty map from array var to sel terms over it
            for (app* v : arr_vars) {
                m_arr_test.mark(v, true);
                m_sel_terms.insert(v, alloc (ptr_vector<app>));
            }

            // assume all arr_vars are of array sort
            // and they only appear in select terms
            if (project (fml)) {
                mk_result (fml);
                aux_vars.append (m_sel_consts);
                arr_vars.reset ();
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "can't project arrays:" << "\n";);
                TRACE ("qe", tout << "Failed to project arrays\n";);
            }

            // dealloc
            for (auto & kv : m_sel_terms) dealloc(kv.m_value);
            m_sel_terms.reset ();
        }
    };


    struct array_project_plugin::imp {

        struct indices {
            expr_ref_vector m_values;
            expr* const*    m_vars;

            indices(ast_manager& m, model& model, unsigned n, expr* const* vars):
                m_values(m), m_vars(vars) {
                expr_ref val(m);
                for (unsigned i = 0; i < n; ++i) {                    
                    m_values.push_back(model(vars[i]));
                }
            }
        };

        ast_manager& m;
        array_util   a;
        scoped_ptr<contains_app> m_var;

        imp(ast_manager& m): m(m), a(m), m_stores(m) {}
        ~imp() {}

        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            return false;
        }

        void remove_true(expr_ref_vector& lits) {
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (m.is_true(lits[i].get())) {
                    project_plugin::erase(lits, i);
                }
            }
        }

        bool contains_x(expr* e) {
            return (*m_var)(e);
        }

        void mk_eq(indices const& x, indices const& y, expr_ref_vector& lits) {
            SASSERT(x.m_values.size() == y.m_values.size());
            unsigned n = x.m_values.size();
            for (unsigned j = 0; j < n; ++j) {
                lits.push_back(m.mk_eq(x.m_vars[j], y.m_vars[j]));
            }
        }

        bool solve_eq(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            // find an equality to solve for.
            expr* s, *t;
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (m.is_eq(lits[i].get(), s, t)) {
                    vector<indices> idxs;
                    expr_ref save(m), back(m);
                    save = lits[i].get();
                    back = lits.back();
                    lits[i] = back;
                    lits.pop_back();
                    unsigned sz = lits.size();
                    if (contains_x(s) && !contains_x(t) && is_app(s)) {
                        if (solve(model, to_app(s), t, idxs, vars, lits)) {
                            return true;
                        }
                    }
                    else if (contains_x(t) && !contains_x(s) && is_app(t)) {
                        if (solve(model, to_app(t), s, idxs, vars, lits)) {
                            return true;
                        }
                    }
                    // put back the equality literal.
                    lits.resize(sz);
                    lits.push_back(back);
                    lits[i] = save;
                }
                // TBD: not distinct?
            }
            return false;
        }

        bool solve(model& model, app* s, expr* t, vector<indices>& idxs, app_ref_vector& vars, expr_ref_vector& lits) {
            SASSERT(contains_x(s));
            SASSERT(!contains_x(t));

            if (s == m_var->x()) {
                expr_ref result(t, m);
                expr_ref_vector args(m);
                sort* range = get_array_range(m.get_sort(s));
                for (unsigned i = 0; i < idxs.size(); ++i) {
                    app_ref var(m), sel(m);
                    expr_ref val(m);
                    var = m.mk_fresh_const("value", range);
                    vars.push_back(var);
                    args.reset();

                    args.push_back (s);
                    args.append(idxs[i].m_values.size(), idxs[i].m_vars);
                    sel = a.mk_select (args);
                    val = model(sel);
                    model.register_decl (var->get_decl (), val);

                    args[0] = result;
                    args.push_back(var);
                    result = a.mk_store(args.size(), args.c_ptr());
                }
                expr_safe_replace sub(m);
                sub.insert(s, result);
                for (unsigned i = 0; i < lits.size(); ++i) {
                    sub(lits[i].get(), result);
                    lits[i] = result;
                }
                return true;
            }

            if (a.is_store(s)) {
                unsigned n = s->get_num_args()-2;
                indices idx(m, model, n, s->get_args()+1);
                for (unsigned i = 1; i < n; ++i) {
                    if (contains_x(s->get_arg(i))) {
                        return false;
                    }
                }
                unsigned i;
                expr_ref_vector args(m);
                switch (contains(idx, idxs, i)) {
                case l_true:
                    mk_eq(idx, idxs[i], lits);
                    return solve(model, to_app(s->get_arg(0)), t, idxs, vars, lits);
                case l_false:
                    for (unsigned i = 0; i < idxs.size(); ++i) {
                        expr_ref_vector eqs(m);
                        mk_eq(idx, idxs[i], eqs);
                        lits.push_back(m.mk_not(mk_and(eqs))); // TBD: extract single index of difference based on model.
                    }
                    args.push_back(t);
                    args.append(n, s->get_args()+1);
                    lits.push_back(m.mk_eq(a.mk_select(args), s->get_arg(n+1)));
                    idxs.push_back(idx);
                    return solve(model, to_app(s->get_arg(0)), t, idxs, vars, lits);
                case l_undef:
                    return false;
                }
            }
            return false;
        }

        lbool contains(indices const& idx, vector<indices> const& idxs, unsigned& j) {
            for (unsigned i = 0; i < idxs.size(); ++i) {
                switch (compare(idx, idxs[i])) {
                case l_true:
                    j = i;
                    return l_true;
                case l_false:
                    break;
                case l_undef:
                    return l_undef;
                }
            }
            return l_false;
        }

        lbool compare(indices const& idx1, indices const& idx2) {
            unsigned n = idx1.m_values.size();
            for (unsigned i = 0; i < n; ++i) {
                switch (compare(idx1.m_values[i], idx2.m_values[i])) {
                case l_true:
                    break;
                case l_false:
                    return l_false;
                case l_undef:
                    return l_undef;
                }
            }
            return l_true;
        }

        lbool compare(expr* val1, expr* val2) {
            if (m.are_equal (val1, val2)) return l_true;
            if (m.are_distinct (val1, val2)) return l_false;

            if (is_uninterp(val1) ||
                is_uninterp(val2)) {
                // TBD chase definition of nested array.
                return l_undef;
            }
            return l_undef;
        }

        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) {
            term_graph tg(m);
            tg.set_vars(shared, false);
            tg.add_model_based_terms(model, lits);

            // need tg to take term and map it to optional rep over the
            // shared vocabulary if it exists.
            
            // . collect shared store expressions, index sorts 
            // . collect shared index expressions
            // . assert extensionality (add shared index expressions)
            // . assert store axioms for collected expressions

            collect_store_expressions(tg, lits);
            collect_index_expressions(tg, lits);

            TRACE("qe",
                  tout << "indices\n";
                  for (auto& kv : m_indices) {
                      tout << sort_ref(kv.m_key, m) << " |-> " << *kv.m_value << "\n";
                  }
                  tout << "stores " << m_stores << "\n";
                  tout << "arrays\n";
                  for (auto& kv : m_arrays) {
                      tout << sort_ref(kv.m_key, m) << " |-> " << *kv.m_value << "\n";
                  });

            assert_extensionality(model, tg, lits);
            assert_store_select(model, tg, lits);

            TRACE("qe", tout << lits << "\n";);

            for (auto& kv : m_indices) {
                dealloc(kv.m_value);
            }
            for (auto& kv : m_arrays) {
                dealloc(kv.m_value);
            }
            m_stores.reset();
            m_indices.reset();
            m_arrays.reset();

            TRACE("qe", tout << "done: " << lits << "\n";);

        }

        app_ref_vector                  m_stores;
        obj_map<sort, app_ref_vector*> m_indices;
        obj_map<sort, app_ref_vector*> m_arrays;

        void add_index_sort(expr* n) {
            sort* s = m.get_sort(n);
            if (!m_indices.contains(s)) {
                m_indices.insert(s, alloc(app_ref_vector, m));
            }
        }

        void add_array(app* n) {
            sort* s = m.get_sort(n);
            app_ref_vector* vs = nullptr;
            if (!m_arrays.find(s, vs)) {
                vs = alloc(app_ref_vector, m);
                m_arrays.insert(s, vs);
            }
            vs->push_back(n);
        }

        app_ref_vector* is_index(expr* n) {
            app_ref_vector* result = nullptr;
            m_indices.find(m.get_sort(n), result);
            return result;
        }

        struct for_each_store_proc {
            imp&               m_imp;
            term_graph&        tg;
            for_each_store_proc(imp& i, term_graph& tg) : m_imp(i), tg(tg) {}

            void operator()(app* n) {
                if (m_imp.a.is_array(n) && tg.get_model_based_rep(n)) {
                    m_imp.add_array(n);
                }

                if (m_imp.a.is_store(n) &&
                    (tg.get_model_based_rep(n->get_arg(0)) ||
                     tg.get_model_based_rep(n->get_arg(n->get_num_args() - 1)))) {
                    m_imp.m_stores.push_back(n);
                    for (unsigned i = 1; i + 1 < n->get_num_args(); ++i) {
                        m_imp.add_index_sort(n->get_arg(i));
                    }
                }
            }
            
            void operator()(expr* e) {}
        };

        struct for_each_index_proc {
            imp&               m_imp;
            term_graph&        tg;
            for_each_index_proc(imp& i, term_graph& tg) : m_imp(i), tg(tg) {}

            void operator()(app* n) {
                auto* v = m_imp.is_index(n);
                if (v && tg.get_model_based_rep(n)) {
                    v->push_back(n);
                }
            }
            
            void operator()(expr* e) {}

        };

        void collect_store_expressions(term_graph& tg, expr_ref_vector const& terms) {
            for_each_store_proc proc(*this, tg);
            for_each_expr<for_each_store_proc>(proc, terms);
        }

        void collect_index_expressions(term_graph& tg, expr_ref_vector const& terms) {
            for_each_index_proc proc(*this, tg);
            for_each_expr<for_each_index_proc>(proc, terms);
        }

        bool are_equal(model& mdl, expr* s, expr* t) {
            return mdl.are_equal(s, t);
        }

        void assert_extensionality(model & mdl, term_graph& tg, expr_ref_vector& lits) {
            for (auto& kv : m_arrays) {
                app_ref_vector const& vs = *kv.m_value;
                if (vs.size() <= 1) continue;
                func_decl_ref_vector ext(m);
                sort* s = kv.m_key;
                unsigned arity = get_array_arity(s);
                for (unsigned i = 0; i < arity; ++i) {
                    ext.push_back(a.mk_array_ext(s, i));
                } 
                expr_ref_vector args(m);
                args.resize(arity + 1);
                for (unsigned i = 0; i < vs.size(); ++i) {
                    expr* s = vs[i];
                    for (unsigned j = i + 1; j < vs.size(); ++j) {
                        expr* t = vs[j];
                        if (are_equal(mdl, s, t)) {
                            lits.push_back(m.mk_eq(s, t));
                        }
                        else {
                            for (unsigned k = 0; k < arity; ++k) {
                                args[k+1] = m.mk_app(ext.get(k), s, t);
                            }
                            args[0] = t;
                            expr* t1 = a.mk_select(args);
                            args[0] = s;
                            expr* s1 = a.mk_select(args);
                            lits.push_back(m.mk_not(m.mk_eq(t1, s1)));
                        }
                    }
                }
            }
        }

        void assert_store_select(model & mdl, term_graph& tg, expr_ref_vector& lits) {
            for (auto& store : m_stores) {
                assert_store_select(store, mdl, tg, lits);                
            }
        }

        void assert_store_select(app* store, model & mdl, term_graph& tg, expr_ref_vector& lits) {
            SASSERT(a.is_store(store));
            ptr_vector<app> indices;
            for (unsigned i = 1; i + 1 < store->get_num_args(); ++i) {
                SASSERT(indices.empty());
                assert_store_select(indices, store, mdl, tg, lits);
            }
        }

        void assert_store_select(ptr_vector<app>& indices, app* store, model & mdl, term_graph& tg, expr_ref_vector& lits) {
            unsigned sz = store->get_num_args();
            if (indices.size() + 2 == sz) {
                ptr_vector<expr> args;
                args.push_back(store);
                for (expr* idx : indices) args.push_back(idx);
                for (unsigned i = 1; i + 1 < sz; ++i) {
                    expr* idx1 = store->get_arg(i);
                    expr* idx2 = indices[i - 1];
                    if (!are_equal(mdl, idx1, idx2)) {
                        lits.push_back(m.mk_not(m.mk_eq(idx1, idx2)));
                        lits.push_back(m.mk_eq(store->get_arg(sz-1), a.mk_select(args)));
                        return;
                    }
                }
                for (unsigned i = 1; i + 1 < sz; ++i) {
                    expr* idx1 = store->get_arg(i);
                    expr* idx2 = indices[i - 1];
                    lits.push_back(m.mk_eq(idx1, idx2));
                }
                expr* a1 = a.mk_select(args);
                args[0] = store->get_arg(0);
                expr* a2 = a.mk_select(args);
                lits.push_back(m.mk_eq(a1, a2));
            }
            else {
                sort* s = m.get_sort(store->get_arg(indices.size() + 1));
                for (app* idx : *m_indices[s]) {
                    indices.push_back(idx);
                    assert_store_select(indices, store, mdl, tg, lits);
                    indices.pop_back();
                }
            }
        }

    };


    array_project_plugin::array_project_plugin(ast_manager& m) {
        m_imp = alloc(imp, m);
    }

    array_project_plugin::~array_project_plugin() {
        dealloc(m_imp);
    }

    bool array_project_plugin::operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        ast_manager& m = vars.get_manager();
        app_ref_vector vvars(m, 1, &var);
        expr_ref fml = mk_and(lits);
        (*this)(model, vvars, fml, vars, false);
        lits.reset();
        flatten_and(fml, lits);
        return true;
    }

    bool array_project_plugin::solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return m_imp->solve(model, vars, lits);
    }

    family_id array_project_plugin::get_family_id() {
        return m_imp->a.get_family_id();
    }

    void array_project_plugin::operator()(model& mdl, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars, bool reduce_all_selects) {
        // 1. project array equalities
        ast_manager& m = fml.get_manager();
        array_project_eqs_util pe (m);
        pe (mdl, arr_vars, fml, aux_vars);
        TRACE ("qe",
               tout << "Projected array eqs: " << fml << "\n";
               tout << "Remaining array vars: " << arr_vars << "\n";
               tout << "Aux vars: " << aux_vars << "\n";
              );

        // 2. reduce selects
        array_select_reducer rs (m);
        rs (mdl, arr_vars, fml, reduce_all_selects);

        TRACE ("qe", tout << "Reduced selects:\n" << fml << "\n"; );

        // 3. project selects using model based ackermannization
        array_project_selects_util ps (m);
        ps (mdl, arr_vars, fml, aux_vars);

        TRACE ("qe",
               tout << "Projected array selects: " << fml << "\n";
               tout << "All aux vars: " << aux_vars << "\n";
              );
    }

    vector<def> array_project_plugin::project(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return vector<def>();
    }

    void array_project_plugin::saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) {
        m_imp->saturate(model, shared, lits);
    }


};
