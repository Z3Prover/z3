/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    ho_matcher

Abstract:

    second and higher-order matcher
    
Author:

    Nikolaj Bjorner (nbjorner) 2025-07-07

   Ho-matcher performs a tree search over match_goals.
   Let Q be the current set of match_goals
   Let B be the current state of a backtracking stack.
   Each element in Q is a work item. 
   The workflow is as follows:
   elements w of Q are removed and added to B, 
   if processing of w results in a unitary match, it is removed from B and the match_goals are added to Q.

   match_goals in Q can be processed independently on when they are generated.
   If a subgoal of Q fails to match, the algorithm backtracks.
   Backtracking can be tuned by keeping track of dependencies.

   Elements in Q are simplified relative to a current substitution. 
   The level where the current substitution affects simplification determines 
   the persistence level of simplification.
  
   A v1 ignores dependencies and assumes always that side-effects are relative to the current backtracking scope.
   A v2 should address and measure the overhead.

   Elements in Q need to persist relative to changes made within a backtracking scope.
   Every operation on Q should be replayed. 
   Thus, elements removed from Q are re-inserted.

   (pat, offset) (t, offset)
   - a variable is considered bound if it's index is below offset.
   - meta variables are adjusted relative to offset

--*/

#include "ast/euf/ho_matcher.h"



namespace euf {


    void ho_matcher::operator()(expr* pat, expr* t, unsigned num_vars) {
        (*this)(pat, t, 0, num_vars);
    }

    void ho_matcher::operator()(expr* pat, expr* t, unsigned num_bound, unsigned num_vars) {               
        m_trail.push_scope();
        m_subst.resize(0);
        m_subst.resize(num_vars);
        m_goals.reset();
        m_goals.push(0, num_bound, pat, t); 
        search();
        m_trail.pop_scope(1);
    }

    void ho_matcher::search() {
        IF_VERBOSE(1, display(verbose_stream()));

        while (m.inc()) {
            // Q, B -> Q', B'. Push work on the backtrack stack and new work items
            // e, Bw -> Q', B'. Consume backtrack stack
            if (!m_goals.empty())
                push_backtrack();
            else if (!m_backtrack.empty())
                resume();
            else
                break;
        }

        IF_VERBOSE(1, display(verbose_stream() << "ho_matcher: done\n"));
    }

    void ho_matcher::backtrack() {
        SASSERT(!m_backtrack.empty());
        auto wi = m_backtrack.back();
        if (wi->in_scope()) 
            m_trail.pop_scope(1);        
        m_backtrack.pop_back();
    }

    void ho_matcher::resume() {
        while (!m_backtrack.empty()) {
            auto& wi = *m_backtrack.back();
            bool st = consume_work(wi);
            IF_VERBOSE(3, display(verbose_stream() << "ho_matcher::consume_work: " << wi.pat << " =?= " << wi.t << " -> " << (st?"true":"false") << "\n"););
            if (st) {
                if (m_goals.empty())                     
                    m_on_match(m_subst);                
                break;
            }
            else 
                backtrack();            
        }
    }

    void ho_matcher::push_backtrack() {
        SASSERT(!m_goals.empty());      
        m_backtrack.push_back(m_goals.pop());
        resume();
    }

    lbool ho_matcher::are_equal(unsigned o1, expr* p, unsigned o2, expr* t) const {
        SASSERT(p->get_sort() == t->get_sort());
        if (o1 == o2 && p == t)
            return l_true;

        if (is_ground(p) && is_ground(t)) 
            return to_lbool(p == t);
        
        if (is_lambda(p) && is_lambda(t)) {
            auto q1 = to_quantifier(p);
            auto q2 = to_quantifier(t);
            SASSERT(q1->get_num_decls() == q2->get_num_decls());
            return are_equal(o1 + q1->get_num_decls(), q1->get_expr(), o2 + q2->get_num_decls(), q2->get_expr());
        }

        if (is_meta_var(p, o1)) {
            auto p1 = m_subst.get(to_var(p)->get_idx() - o1);
            if (p1) 
                return are_equal(0, p1, o2, t);
            return l_undef;
        }

        if (is_meta_var(t, o2)) {
            auto t1 = m_subst.get(to_var(t)->get_idx() - o2);
            if (t1) 
                return are_equal(o1, p, 0, t1);
            return l_undef;
        }       


        if (m_unitary.is_flex(o1, p)) {
            expr_ref h = whnf(p, o1);
            if (h != p)
                return are_equal(o1, h, o2, t);
            return l_undef;
        }
        if (m_unitary.is_flex(o2, t)) {
            expr_ref h = whnf(t, o2);
            if (h != t)
                return are_equal(o1, p, o2, h);
            return l_undef;
        }
        if (m_array.is_select(p))
            return l_undef; // TODO: interleave check with whnf expansion
        
        if (is_app(p) && is_app(t)) {          
            auto a1 = to_app(p);
            auto a2 = to_app(t);
            if (a1->get_decl() != a2->get_decl())
                return l_false;
            if (a1->get_num_args() != a2->get_num_args())
                return l_false;
            for (unsigned i = 0; i < a1->get_num_args(); ++i) {
                auto r = are_equal(o1, a1->get_arg(i), o2, a2->get_arg(i));
                if (r != l_true)
                    return r;
            }
            return l_true;
        }
        if (is_bound_var(p, o1) || is_bound_var(t, o2))
            return to_lbool(p == t);

        return l_undef;
    }

    //
    // reduces (M N)
    // and recurisvely ((M N) K)
    // such that M is not a lambda
    //
    expr_ref ho_matcher::whnf(expr* e, unsigned offset) const {
        expr_ref r(e, m), t(m);
//        verbose_stream() << "ho_matcher::whnf: " << r << "\n";
        if (is_meta_var(r, offset)) {
            auto v = to_var(e);
            auto idx = v->get_idx();
            if (idx >= offset && m_subst.get(idx - offset)) {
                auto e = m_subst.get(idx - offset);
                r = e;
                if (offset > 0) {
                    var_shifter sh(m);
                    sh(e, offset, r);
                }
                return r;
            }
        }
        while (m_array.is_select(r)) {
            app* a = to_app(r);
            auto arg0 = a->get_arg(0);
            //  apply substitution:
            if (is_meta_var(arg0, offset)) {
                auto v = to_var(arg0);
                auto idx = v->get_idx();
                if (idx >= offset && m_subst.get(idx - offset)) {
                    auto e = m_subst.get(idx - offset);
                    if (offset > 0) {
                        var_shifter sh(m);
                        sh(e, offset, r);
                        e = r;
                    }
                    expr_ref_vector args(m);
                    args.push_back(e);
                    for (unsigned i = 1; i < a->get_num_args(); ++i) 
                        args.push_back(a->get_arg(i));
                    
                    r = m.mk_app(a->get_decl(), args.size(), args.data());
  //                  verbose_stream() << "ho_matcher::whnf: " << r << "\n";
                    continue;
                }
            }
            if (m_array.is_select(arg0)) {
                t = whnf(arg0, offset);
                if (t != arg0) {
                    ptr_vector<expr> args(a->get_num_args(), a->get_args());
                    args[0] = t;
                    r = m_array.mk_select(args.size(), args.data());
   //                 verbose_stream() << "ho_matcher::whnf-rec: " << r << "\n";
                    continue;
                }
            }
            // outer beta reduction
            auto st = m_rewriter.mk_app_core(a->get_decl(), a->get_num_args(), a->get_args(), t);
            if (st != BR_FAILED)
                r = t;
            else
                break;
        }
        return r;    
    }

    // We assume that m_rewriter should produce
    // something amounting to weak-head normal form WHNF

    void ho_matcher::reduce(match_goal& wi) {
        while (true) {
            expr_ref r = whnf(wi.pat, wi.pat_offset());
            if (r == wi.pat)
                break;
            IF_VERBOSE(3, verbose_stream() << "ho_matcher::reduce: " << wi.pat << " -> " << r << "\n";);
            wi.pat = r;
        } 

        while (true) {
            expr_ref r = whnf(wi.t, wi.term_offset());
            if (r == wi.t)
                break;
            IF_VERBOSE(3, verbose_stream() << "ho_matcher::reduce: " << wi.t << " -> " << r << "\n";);
            wi.t = r;
        } 
    }

    bool ho_matcher::consume_work(match_goal &wi) {
//        IF_VERBOSE(1, display(verbose_stream() << "ho_matcher::consume_work: " << wi.pat << " =?= " << wi.t << "\n"););

        if (wi.in_scope()) 
            m_trail.pop_scope(1);
        
        wi.set_in_scope();
        m_trail.push_scope();
        
        if (wi.is_done())
            return false;

        reduce(wi);

        auto t = wi.t;
        auto p = wi.pat;

        switch (are_equal(wi.pat_offset(), p, wi.term_offset(), t)) {
        case l_false:
            wi.set_done();
            return false;
        case l_true:
            wi.set_done();
            return true;
        case l_undef:
            break;
        }
        

        // v >= offset
        // v - offset |-> t
        if (is_meta_var(p, wi.pat_offset()) && is_closed(t, 0, wi.term_offset())) {
            auto v = to_var(p);
            auto idx = v->get_idx() - wi.pat_offset();
            SASSERT(!m_subst.get(idx)); // reduce ensures meta variables are not in substitutions
            add_binding(v, wi.pat_offset(), t);
            wi.set_done();
            return true;
        }


        // N = \ x. T => ((shift1 N) x) = T
        if (is_lambda(t) && !is_lambda(p)) {
            auto q = to_quantifier(t);
            auto t_body = q->get_expr();
            auto nd = q->get_num_decls();
            var_shifter vs(m);
            expr_ref r(m);
            vs(p, nd, r);
            expr_ref_vector args(m);
            args.push_back(r);
            for (unsigned i = 0; i < nd; ++i)
                args.push_back(m.mk_var(nd - 1 - i, q->get_decl_sort(i)));
            r = m_array.mk_select(args);
            m_goals.push(wi.level, wi.term_offset() + nd, r, t_body);
            wi.set_done();
            return true;
        }

        // Flex head unitary
        // H(pat) = t

        if (m_array.is_select(p) && m_unitary.is_flex(wi.pat_offset(), p) && is_pattern(p, wi.pat_offset(), t)) {
            auto lam = abstract_pattern(p, wi.pat_offset(), t);
            while (m_array.is_select(p))
                p = to_app(p)->get_arg(0);
            SASSERT(is_meta_var(p, wi.pat_offset()));
            add_binding(to_var(p), wi.pat_offset(), lam);
            wi.set_done();
            return true;
        }       

        // Flex head general case

        if (m_array.is_select(p) && m_unitary.is_flex(wi.pat_offset(), p)) {
            ptr_vector<app> pats;
            auto p1 = p;
            while (m_array.is_select(p1)) {
                pats.push_back(to_app(p1));
                p1 = to_app(p1)->get_arg(0);
            }
            auto v = to_var(p1);
            if (wi.is_init())
                wi.set_project();

            if (wi.is_project()) {
                // v -> \x\y . x_i
                unsigned start = wi.index();
                unsigned i = 0;
                for (auto pa : pats) {
                    for (auto pi : array_select_indices(pa)) {
                        if (start <= i && pi->get_sort() == t->get_sort()) {                            
                            auto eq = are_equal(wi.pat_offset(), pi, wi.term_offset(), t);
                            if (eq == l_false) {
                                ++i;
                                continue;
                            }
                            auto e = mk_project(pats.size(), i, v->get_sort());
                            add_binding(v, wi.pat_offset(), e);
                            if (eq == l_undef)
                                m_goals.push(wi.level + 1, wi.pat_offset(), pi, t);
                            wi.set_index(i + 1);
                            return true;
                        }
                        ++i;
                    }
                }
            }

            SASSERT(!is_lambda(t));            

            if (!is_app(t))
                return false;

            auto ta = to_app(t);

            if (wi.is_project())
                wi.set_app();           

            if (wi.is_app()) {
                unsigned sz = ta->get_num_args();
                if (sz > 0) {
                    wi.inc_index();
                    m_trail.push(undo_resize(m_subst));
                }

                // H (p1) (p2) = f(t1, .., tn)
                // H -> \x1 \x2 f(H1(x1, x2), .., Hn(x1, x2))
                // H1(p1, p2) = t1, .., Hn(p1, p2) = tn
                ptr_vector<sort> domain, pat_domain;
                ptr_vector<expr> pat_args;
                expr_ref_vector args(m), pat_vars(m), bound_args(m);
                vector<symbol> names;
                pat_args.push_back(nullptr);
                pat_vars.push_back(nullptr);
                unsigned num_bound = 0;
                expr_mark seen;
                for (auto pat : pats) {
                    for (auto pi : array_select_indices(pat)) {
                        ++num_bound;
                        domain.push_back(pi->get_sort());
                        names.push_back(symbol(num_bound));
                        if (seen.is_marked(pi))
                            continue;
                        pat_domain.push_back(pi->get_sort());
                        pat_args.push_back(pi); 
                        seen.mark(pi);
                    }
                }

                for (unsigned i = pat_args.size(); i-- > 1; ) {
                    auto pi = pat_args.get(i);
                    pat_vars.push_back(m.mk_var(pat_args.size() - i - 1, pi->get_sort()));
                }                        

                for (auto ti : *ta) {
                    sort* v_sort = m_array.mk_array_sort(pat_domain.size(), pat_domain.data(), ti->get_sort());
                    auto v = m.mk_var(m_subst.size() + wi.pat_offset(), v_sort);
                    auto w = m.mk_var(m_subst.size() + wi.pat_offset() + num_bound, v_sort); // shifted by number of bound
                    m_subst.resize(m_subst.size() + 1);
                    pat_args[0] = v;
                    auto sel = m_array.mk_select(pat_args.size(), pat_args.data());
                    m_goals.push(wi.level + 1, wi.term_offset(), sel, ti);
                    pat_vars[0] = w;
                    sel = m_array.mk_select(pat_vars.size(), pat_vars.data());
                    bound_args.push_back(sel);
                }

                expr_ref lam(m);
                lam = m.mk_app(ta->get_decl(), bound_args.size(), bound_args.data());

                for (unsigned i = pats.size(); i-- > 0; ) {
                    auto pa = pats[i];
                    auto sz = pa->get_num_args() - 1;
                    num_bound -= sz;
                    lam = m.mk_lambda(sz, domain.data() + num_bound, names.data() + num_bound, lam);
                }
                add_binding(v, wi.pat_offset(), lam);
                wi.set_done();
                return true;
            }
            return false;
        }

        wi.set_done();

        // first order match
        if (is_app(t) && is_app(p)) {
            auto ta = to_app(t);
            auto tp = to_app(p);
            if (ta->get_decl() != tp->get_decl())
                return false;
            if (ta->get_num_args() != tp->get_num_args())
                return false;
            for (unsigned i = 0; i < ta->get_num_args(); ++i)
                m_goals.push(wi.level, wi.term_offset(), tp->get_arg(i), ta->get_arg(i));
            return true;
        }               
                        
        //
        // lambda x . p == lambda x . t
        // 
        if (is_quantifier(p) && is_quantifier(t)) {
            auto qp = to_quantifier(p);
            auto qt = to_quantifier(t);
            unsigned pd = qp->get_num_decls();
            unsigned td = qt->get_num_decls();
            if (qp->get_kind() != qt->get_kind())
                return false;
            if (pd != td)
                return false;
            for (unsigned i = 0; i < pd; ++i)
                if (qp->get_decl_sort(i) != qt->get_decl_sort(i))
                    return false;
            m_goals.push(wi.level, wi.term_offset() + td, qp->get_expr(), qt->get_expr());
            return true;
        }

        return false;		       
    }

    // M p1 p2 ... pk
    // where M is a meta-variable and p1, .., pk are distinct bound variables
    // and t does not contain a bound variable not mentioned in p1,..,pk
    // or terms that don't occur in t.
    bool ho_matcher::is_pattern(expr* p, unsigned offset, expr* t) {
        uint_set vars;
        while (m_array.is_select(p)) {
            auto a = to_app(p);
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                auto arg = a->get_arg(i);
                if (!is_bound_var(arg, offset))
                    return false;
                auto idx = to_var(arg)->get_idx();
                if (vars.contains(idx))
                    return false;
                vars.insert(idx);
            }
            p = a->get_arg(0);
        }
        if (!is_meta_var(p, offset))
            return false;
        // check that every free variable in t is in vars.
        vector<ptr_vector<expr>> btodo;
        btodo.push_back(ptr_vector<expr>());
        btodo[0].push_back(t);
        for (unsigned i = 0; i < btodo.size(); ++i) {
            expr_fast_mark1 visited;
            for (unsigned j = 0; j < btodo[i].size(); ++j) {
                auto t = btodo[i][j];
                if (visited.is_marked(t))
                    continue;
                visited.mark(t);
                
                if (is_app(t)) {
                    auto a = to_app(t);
                    btodo[i].append(a->get_num_args(), a->get_args());
                }
                else if (is_var(t)) {
                    auto idx = to_var(t)->get_idx();
                    if (idx >= i && !vars.contains(idx - i))
                        return false;
                }
                else {
                    quantifier* q = to_quantifier(t);
                    btodo.reserve(i + q->get_num_decls() + 1);
                    btodo[i + q->get_num_decls()].push_back(q->get_expr());
                }
            }
        }

        return true;
    }

    // create a lambda abstraction for the meta variable such that
    // when applied to patterns, the result is t.
    // pre-condition: is_pattern(p, offset, t);
    // H (v1, v2) (v3, v4, v5)
    // lambda x1 x2 . lambda x3 x4 x5. t[v5 -> 0, v4 -> 1, v3 -> 2, v2 -> 3, v1 -> 4] 
    expr_ref ho_matcher::abstract_pattern(expr* p, unsigned offset, expr* t) {
        unsigned num_bound = 0;
        expr* p1 = p;
        ptr_vector<app> pats;
        while (m_array.is_select(p1)) {
            pats.push_back(to_app(p1));
            num_bound += to_app(p1)->get_num_args() - 1;
            p1 = to_app(p1)->get_arg(0);            
        }
        expr_ref_vector pat2bound(m);        
        for (auto a : pats) {
            unsigned sz = a->get_num_args();
            for (unsigned i = 1; i < sz; ++i) {
                auto arg = a->get_arg(i);
                SASSERT(is_bound_var(arg, offset));
                auto idx = to_var(arg)->get_idx();
                pat2bound.reserve(idx + 1);
                pat2bound[idx] = m.mk_var(--num_bound, arg->get_sort());
            }   
            p1 = a->get_arg(0);
        }
        var_subst sub(m, false);
        expr_ref lam = sub(t, pat2bound);
        for (unsigned i = pats.size(), j = 0; i-- > 0; ) {
            vector<symbol> names;
            ptr_vector<sort> sorts;
            for (unsigned k = 1; k < pats[i]->get_num_args(); ++k) {
                names.push_back(symbol(j++));
                sorts.push_back(pats[i]->get_arg(k)->get_sort());
            }
            lam = m.mk_lambda(names.size(), sorts.data(), names.data(), lam);
        }
        return lam;
    }

    //
    // keep track of number of internal scopes and offset to non-capture variables.
    // a variable is captured if it's index is in the interval [scopes, offset[.
    //
    bool ho_matcher::is_closed(expr* v, unsigned scopes, unsigned offset) const {
        if (is_ground(v))
            return true;
        if (is_app(v)) 
            return all_of(*to_app(v), [&](expr* arg) { return is_closed(arg, scopes, offset); });
        if (is_var(v)) 
            return to_var(v)->get_idx() < scopes || to_var(v)->get_idx() >= offset;
        if (is_quantifier(v)) {
            auto q = to_quantifier(v);
            return is_closed(q->get_expr(), scopes + q->get_num_decls(), offset + q->get_num_decls());
        }
        return false;
    }

    // (T1, T2,.., Tn) -> (Tn+1,.., Ti,.., Tm) -> Ti => lambda x1...xn . lambda x_n+1,..x_m . x_i
    expr_ref ho_matcher::mk_project(unsigned num_lambdas, unsigned i, sort* s) {
        SASSERT(num_lambdas > 0);
        SASSERT(m_array.is_array(s));
        unsigned num_binders = 0;
        expr_ref body(m);
        sort* a = s, * var_sort = nullptr;
        unsigned j = i;
        for (unsigned k = 0; k < num_lambdas; ++k) {
            auto arity = get_array_arity(a);
            if (j >= arity)
                j -= arity;
            else if (j < arity && !var_sort)
                var_sort = get_array_domain(a, j);
            num_binders += arity;
            a = get_array_range(a);
        }
        SASSERT(var_sort);
        body = m.mk_var(num_binders - i - 1, var_sort);
        bind_lambdas(num_lambdas, s, body);
        return body;
    }

    void ho_matcher::bind_lambdas(unsigned j, sort* s, expr_ref& body) {
        if (j > 1) 
            bind_lambdas(j - 1, get_array_range(s), body);        
        unsigned sz = get_array_arity(s);
        ptr_vector<sort> decl_sorts;
        vector<symbol> decl_names;
        for (unsigned i = 0; i < sz; ++i) {
            decl_sorts.push_back(get_array_domain(s, i));
            decl_names.push_back(symbol(i));
        }
        body = m.mk_lambda(sz, decl_sorts.data(), decl_names.data(), body);
    }

    void ho_matcher::add_binding(var* v, unsigned offset, expr* t) {
        SASSERT(v->get_idx() >= offset);
        m_subst.set(v->get_idx() - offset, t);
        IF_VERBOSE(1, verbose_stream() << "ho_matcher::add_binding: v" << v->get_idx() - offset << " -> " << mk_pp(t, m) << "\n";);
        m_trail.push(undo_set(m_subst, v->get_idx() - offset));
    }


    std::pair<quantifier*, app*> ho_matcher::compile_ho_pattern(quantifier* q, app* p) {
        app* p1 = nullptr;
        if (m_pat2hopat.find(p, p)) {
            q = m_q2hoq[q];
            return { q, p };
        }
        auto is_ho = any_of(subterms::all(expr_ref(p, m)), [&](expr* t) { return m_unitary.is_flex(0, t); });
        if (!is_ho)
            return { q, p };
        ptr_vector<expr> todo;
        ptr_buffer<var> bound;
        expr_ref_vector cache(m);
        unsigned nb = q->get_num_decls();
        todo.push_back(p);
        while (!todo.empty()) {
            auto t = todo.back();
            if (is_var(t)) {
                cache.setx(t->get_id(), t);
                todo.pop_back();
                continue;
            }
            if (m_unitary.is_flex(0, t)) {
                m_pat2abs.insert_if_not_there(p, svector<std::pair<unsigned, expr*>>()).push_back({ nb, t });
                auto v = m.mk_var(nb++, t->get_sort());
                bound.push_back(v);
                cache.setx(t->get_id(), v);
                todo.pop_back();
                continue;
            }
            if (is_app(t)) {
                auto a = to_app(t);
                unsigned sz = a->get_num_args();
                ptr_buffer<expr> args;
                for (auto arg : *a) {
                    cache.reserve(arg->get_id() + 1);
                    expr* arg1 = cache.get(arg->get_id());
                    if (!arg1)
                        todo.push_back(arg);
                    else
                        args.push_back(arg1);
                }
                if (sz != args.size())
                    continue;
                todo.pop_back();
                cache.setx(t->get_id(), m.mk_app(a->get_decl(), args.size(), args.data()));
            }
            if (is_quantifier(t)) {
                m_pat2abs.remove(p);
                return { q, p };
            }
        }
        p1 = to_app(cache.get(p->get_id()));
        expr_free_vars free_vars;
        free_vars(p1);
        app_ref_vector new_ground(m);
        app_ref_vector new_patterns(m);

        ptr_buffer<sort> sorts;
        vector<symbol> names;
        for (unsigned i = bound.size(); i-- > 0; ) {
            sorts.push_back(bound[i]->get_sort());
            names.push_back(symbol(bound[i]->get_idx()));
        }
        unsigned sz = q->get_num_decls();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned idx = sz - i - 1;
            auto s = q->get_decl_sort(i);
            sorts.push_back(s);
            names.push_back(q->get_decl_name(i));
            if (!free_vars.contains(idx)) {
                auto p = m.mk_fresh_func_decl("p", 1, &s, m.mk_bool_sort());
                new_patterns.push_back(m.mk_app(p, m.mk_var(idx, s)));
                new_ground.push_back(m.mk_app(p, m.mk_fresh_const(symbol("c"), s)));
            }
        }
        auto body = q->get_expr();
        if (!new_patterns.empty()) {
            ptr_vector<app> pats;
            VERIFY(m.is_pattern(p1, pats));
            for (auto p : new_patterns) // patterns for variables that are not free in new pattern
                pats.push_back(p);
            for (auto g : new_ground) // ensure ground terms are in pattern so they have enodes
                pats.push_back(g);
            p1 = m.mk_pattern(pats.size(), pats.data());
        }

        quantifier* q1 = m.mk_forall(sorts.size(), sorts.data(), names.data(), body);

        m_pat2hopat.insert(p, p1);
        m_hopat2pat.insert(p1, p);
        m_q2hoq.insert(q, q1);
        m_hoq2q.insert(q1, q);
        m_hopat2free_vars.insert(p1, free_vars);
        m_ho_patterns.push_back(p1);
        m_ho_qs.push_back(q1);
        trail().push(push_back_vector(m_ho_patterns));
        trail().push(push_back_vector(m_ho_qs));
        trail().push(insert_map(m_pat2hopat, p));
        trail().push(insert_map(m_hopat2pat, p1));
        trail().push(insert_map(m_pat2abs, p));
        trail().push(insert_map(m_q2hoq, q));
        trail().push(insert_map(m_hoq2q, q1));
        trail().push(insert_map(m_hopat2free_vars, p1));        
        return { q1, p1 };
    }

    bool ho_matcher::is_ho_pattern(app* p) {
        return m_hopat2pat.contains(p);
    }

    void ho_matcher::refine_ho_match(app* p, expr_ref_vector& s) {
        auto fo_pat = m_hopat2pat[p];
        m_trail.push_scope();
        m_subst.resize(0);
        m_subst.resize(s.size());
        m_goals.reset();
        for (unsigned i = 0; i < s.size(); ++i) {
            auto idx = s.size() - i - 1;
            if (!m_hopat2free_vars[p].contains(idx))
                s[i] = m.mk_var(idx, s[i]->get_sort());
            else if (s.get(i))
                m_subst.set(i, s.get(i));
        }

        IF_VERBOSE(1, verbose_stream() << "refine " << mk_pp(p, m) << "\n" << s << "\n");

        unsigned num_bound = 0, level = 0;
        for (auto [v, pat] : m_pat2abs[fo_pat]) {
            var_subst sub(m, true);
            auto pat_refined = sub(pat, s);
            IF_VERBOSE(1, verbose_stream() << mk_pp(pat, m) << " -> " << pat_refined << "\n");
            m_goals.push(level, num_bound, pat_refined, s.get(s.size() - v - 1));
        }

        search();
        m_trail.pop_scope(1);
    }

    std::ostream& ho_matcher::display(std::ostream& out) const {
        m_subst.display(out << "subst\n");
        m_goals.display(out << "goals\n");
        out << "stack\n";
        for (auto const* mi : m_backtrack)
            mi->display(out);       
        return out;
    }

    struct retire_match_goal : public trail {
        match_goal& mg;        
        retire_match_goal(match_goal& mg) : mg(mg) {}
        void undo() override {
            mg.reset();
        }
    };

    void match_goals::push(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t) {
        match_goal* wi = new (ho.trail().get_region()) match_goal(level, offset, pat, t);
        ho.trail().push(retire_match_goal(*wi)); // reset on undo
        wi->init(wi);
        if (ho.is_cheap(*wi)) {
            match_goal::push_to_front(m_cheap, wi);
            ho.trail().push(remove_dll(m_cheap, wi));    // remove from cheap
        }
        else {
            ho.reduce(*wi);
            if (ho.is_cheap(*wi)) {
                match_goal::push_to_front(m_cheap, wi);
                ho.trail().push(remove_dll(m_cheap, wi));
            }
            else {
                match_goal::push_to_front(m_expensive, wi);
                ho.trail().push(remove_dll(m_expensive, wi)); // remove from expensive
            }
        }
    }

    match_goal* match_goals::pop() {
        SASSERT(!empty());
        if (m_cheap)
            return pop(m_cheap);
        auto* wi = m_expensive;
        do {
            expr_ref pat(wi->pat), t(wi->t);
            ho.reduce(*wi);
            if (pat == wi->pat && t == wi->t)
                continue;
            if (pat != wi->pat)
                ho.trail().push(update_value(wi->pat, pat));
            if (t != wi->t)
                ho.trail().push(update_value(wi->t, t));
            if (ho.is_cheap(*wi)) {
                dll_base<match_goal>::remove_from(m_expensive, wi);
                match_goal::push_to_front(m_cheap, wi);

                ho.trail().push(insert_dll(m_expensive, wi)); // remove from expensive
                ho.trail().push(remove_dll(m_cheap, wi));
                return pop(m_cheap);
            }
            wi = wi->next();
        } 
        while (wi != m_expensive);
                
        return pop(m_expensive);
    }    

    match_goal* match_goals::pop(match_goal* &ws) {
        SASSERT(ws);
        auto* wi = ws->pop(ws);
        ho.trail().push(insert_dll(ws, wi)); // insert wi into ws   
        wi->set_init();
        return wi;
    }

    std::ostream& match_goals::display(std::ostream& out) const {
        for (auto const& wi : dll_elements(m_cheap))
            wi.display(out << "c ");
        
        for (auto const& wi : dll_elements(m_expensive))
            wi.display(out << "e ");
        
        return out;
    }

}
