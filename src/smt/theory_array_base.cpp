/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_base.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-02.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/theory_array_base.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "smt/smt_model_generator.h"
#include "model/func_interp.h"
#include "ast/ast_smt2_pp.h"

namespace smt {

    theory_array_base::theory_array_base(ast_manager & m):
        theory(m.mk_family_id("array")),
        m_found_unsupported_op(false),
        m_array_weak_head(0)
    {
    }

    void theory_array_base::add_weak_var(theory_var v) {
        get_context().push_trail(push_back_vector<context, svector<theory_var>>(m_array_weak_trail));
        m_array_weak_trail.push_back(v);
    }

    void theory_array_base::found_unsupported_op(expr * n) {
        if (!get_context().get_fparams().m_array_fake_support && !m_found_unsupported_op) {
            TRACE("array", tout << mk_ll_pp(n, get_manager()) << "\n";);            
            get_context().push_trail(value_trail<context, bool>(m_found_unsupported_op));
            m_found_unsupported_op = true;
        }
    }
    
    app * theory_array_base::mk_select(unsigned num_args, expr * const * args) {
        app * r = get_manager().mk_app(get_family_id(), OP_SELECT, 0, nullptr, num_args, args);
        TRACE("mk_var_bug", tout << "mk_select: " << r->get_id() << " num_args: " << num_args;
              for (unsigned i = 0; i < num_args; i++) tout << " " << args[i]->get_id();
              tout << "\n";);
        return r;
    }

    app * theory_array_base::mk_store(unsigned num_args, expr * const * args) {
        return get_manager().mk_app(get_family_id(), OP_STORE, 0, nullptr, num_args, args);
    }

    app * theory_array_base::mk_default(expr * a) {
        sort * s = get_manager().get_sort(a);
        unsigned num_params = get_dimension(s);
        parameter const* params = s->get_info()->get_parameters();
        return get_manager().mk_app(get_family_id(), OP_ARRAY_DEFAULT, num_params, params, 1, & a);
    }

    unsigned theory_array_base::get_dimension(sort * s) const {
        SASSERT(s->is_sort_of(get_family_id(), ARRAY_SORT));
        SASSERT(s->get_info()->get_num_parameters() >= 2);
        return s->get_info()->get_num_parameters()-1;
    }

    void theory_array_base::assert_axiom(unsigned num_lits, literal * lits) {
        context & ctx = get_context();
        TRACE("array_axiom",
              tout << "literals:\n";
              for (unsigned i = 0; i < num_lits; ++i) {
                  expr * e = ctx.bool_var2expr(lits[i].var());
                  if (lits[i].sign())
                      tout << "not ";
                  tout << mk_pp(e, get_manager()) << " ";
                  tout << "\n";
              });
        ctx.mk_th_axiom(get_id(), num_lits, lits);
    }

    void theory_array_base::assert_axiom(literal l1, literal l2) {
        literal ls[2] = { l1, l2 };
        assert_axiom(2, ls);
    }

    void theory_array_base::assert_axiom(literal l) {
        assert_axiom(1, &l);
    }

    void theory_array_base::assert_store_axiom1_core(enode * e) {
        app * n           = e->get_owner();
        SASSERT(is_store(n));
        context & ctx     = get_context();
        ast_manager & m   = get_manager();
        ptr_buffer<expr> sel_args;
        unsigned num_args = n->get_num_args();
        SASSERT(num_args >= 3);
        sel_args.push_back(n);
        for (unsigned i = 1; i < num_args - 1; ++i) {
            sel_args.push_back(to_app(n->get_arg(i)));
        }
        expr_ref sel(m);
        sel = mk_select(sel_args.size(), sel_args.c_ptr());
        expr * val = n->get_arg(num_args - 1);
        TRACE("array", tout << mk_bounded_pp(sel, m) << " = " << mk_bounded_pp(val, m) << "\n";);
        if (m.proofs_enabled()) {
            literal l(mk_eq(sel, val, true));
            ctx.mark_as_relevant(l);
            if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(l.var()));
            assert_axiom(l);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
        else {
            TRACE("mk_var_bug", tout << "mk_sel: " << sel->get_id() << "\n";);
            ctx.internalize(sel, false);
            ctx.assign_eq(ctx.get_enode(sel), ctx.get_enode(val), eq_justification::mk_axiom());
            ctx.mark_as_relevant(sel.get());
        }
    }

    /**
       \brief Assert axiom 2:

       FORALL a, i_i, ..., i_n, j_1, ..., j_n
         i_1 /= j_1 => select(store(a, i_1, ..., i_n, v), j_1, ..., j_n) = select(a, j_1, ..., j_n)
         and
         ...
         and
         i_n /= j_n => select(store(a, i_1, ..., i_n, v), j_1, ..., j_n) = select(a, j_1, ..., j_n)
    */
    void theory_array_base::assert_store_axiom2_core(enode * store, enode * select) {
        TRACE("array", tout << "generating axiom2: #" << store->get_owner_id() << " #" << select->get_owner_id() << "\n";
              tout << mk_bounded_pp(store->get_owner(), get_manager()) << "\n" << mk_bounded_pp(select->get_owner(), get_manager()) << "\n";);
        SASSERT(is_store(store));
        SASSERT(is_select(select));
        SASSERT(store->get_num_args() == 1 + select->get_num_args());
                
        ptr_buffer<expr> sel1_args, sel2_args;
        context & ctx      = get_context();
        ast_manager & m    = get_manager();
        enode *         a  = store->get_arg(0);
        enode * const * is = select->get_args() + 1;
        enode * const * js = store->get_args() + 1;
        unsigned num_args = select->get_num_args() - 1;
        sel1_args.push_back(store->get_owner());
        sel2_args.push_back(a->get_owner());

        for (unsigned i = 0; i < num_args; i++) {
            sel1_args.push_back(is[i]->get_owner());
            sel2_args.push_back(is[i]->get_owner());
        }

        expr_ref sel1(m), sel2(m);
        bool init = false;
        literal conseq = null_literal;
        expr * conseq_expr = nullptr;

        for (unsigned i = 0; i < num_args; i++) {
            enode * idx1 = js[i];
            enode * idx2 = is[i];
            
            if (idx1->get_root() == idx2->get_root()) {
                TRACE("array_bug", tout << "indexes are equal... skipping...\n";);
                continue;
            }

            if (!init) {
                sel1 = mk_select(sel1_args.size(), sel1_args.c_ptr());
                sel2 = mk_select(sel2_args.size(), sel2_args.c_ptr());
                if (sel1 == sel2) {
                    TRACE("array_bug", tout << "sel1 and sel2 are equal:\n";);
                    break;
                }
                init = true;
                TRACE("array", tout << mk_bounded_pp(sel1, m) << " " << mk_bounded_pp(sel2, m) << "\n";);
                conseq = mk_eq(sel1, sel2, true);
                conseq_expr = ctx.bool_var2expr(conseq.var());
            }

            literal ante = mk_eq(idx1->get_owner(), idx2->get_owner(), true);
            ctx.mark_as_relevant(ante);
            // ctx.force_phase(ante);
            ctx.add_rel_watch(~ante, conseq_expr);
            // ctx.mark_as_relevant(conseq_expr);
            TRACE("array", tout << "asserting axiom2: " << ante << "\n";);
            TRACE("array_map_bug", tout << "axiom2:\n";
                  tout << mk_ismt2_pp(idx1->get_owner(), m) << "\n=\n" << mk_ismt2_pp(idx2->get_owner(), m);
                  tout << "\nimplies\n" << mk_ismt2_pp(conseq_expr, m) << "\n";);
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_or(ctx.bool_var2expr(ante.var()), conseq_expr);
                log_axiom_instantiation(body);
            }
            assert_axiom(ante, conseq);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
    }
    
    bool theory_array_base::assert_store_axiom2(enode * store, enode * select) { 
        unsigned num_args = select->get_num_args();
        unsigned        i = 1;
        for (; i < num_args; i++) 
            if (store->get_arg(i)->get_root() != select->get_arg(i)->get_root())
                break;
        if (i == num_args)
            return false;
        if (get_context().add_fingerprint(store, store->get_owner_id(), select->get_num_args() - 1, select->get_args() + 1)) {
            TRACE("array", tout << "adding axiom2 to todo queue\n";);
            m_axiom2_todo.push_back(std::make_pair(store, select)); 
            return true;
        }
        TRACE("array", tout << "axiom already instantiated: #" << store->get_owner_id() << " #" << select->get_owner_id() << "\n";);
        return false;
    }

 



    func_decl_ref_vector * theory_array_base::register_sort(sort * s_array) {
        unsigned dimension = get_dimension(s_array);
        func_decl_ref_vector * ext_skolems = nullptr;
        if (!m_sort2skolem.find(s_array, ext_skolems)) {       
            array_util util(get_manager());
            ast_manager & m = get_manager();
            ext_skolems = alloc(func_decl_ref_vector, m);
            for (unsigned i = 0; i < dimension; ++i) {
                func_decl * ext_sk_decl = util.mk_array_ext(s_array, i);
                ext_skolems->push_back(ext_sk_decl);
            }
            m_sort2skolem.insert(s_array, ext_skolems);
            m_sorts_trail.push_back(s_array);
        }
        return ext_skolems;
    }

    bool theory_array_base::value_eq_proc::operator()(enode * n1, enode * n2) const {
        SASSERT(n1->get_num_args() == n2->get_num_args());
        unsigned n = n1->get_num_args();
        // skipping first argument of the select.
        for(unsigned i = 1; i < n; i++) {
            if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root()) {
                return false;
            }
        }
        return true;
    }

    /**
       \brief Return true if there is a select(v1', i1) and a select(v2', i2) such that:
       v1' = v1, v2' = v2, i1  = i2, select(v1', i1) /= select(v2', i2) in the logical context.
    */
    bool theory_array_base::already_diseq(enode * v1, enode * v2) {
        context & ctx = get_context();
        enode * r1    = v1->get_root();
        enode * r2    = v2->get_root();

        if (r1->get_class_size() > r2->get_class_size()) {
            std::swap(r1, r2);
        }

        m_array_value.reset();
        // populate m_array_value if the select(a, i) parent terms of r1
        for (enode* parent : r1->get_const_parents()) {
            if (parent->is_cgr() &&
                ctx.is_relevant(parent) &&
                is_select(parent->get_owner()) &&
                parent->get_arg(0)->get_root() == r1) {
                m_array_value.insert(parent);
            }
        }
        // traverse select(a, i) parent terms of r2 trying to find a match.
        for (enode * parent : r2->get_const_parents()) {
            enode * other;
            if (parent->is_cgr() && 
                ctx.is_relevant(parent) &&
                is_select(parent->get_owner()) &&
                parent->get_arg(0)->get_root() == r2 &&
                m_array_value.find(parent, other)) {
                
                if (ctx.is_diseq(parent, other)) {
                    TRACE("array_ext", tout << "selects are disequal\n";);
                    return true;
                }
            }
        }
        return false;
    }

    bool theory_array_base::assert_extensionality(enode * n1, enode * n2) {
        context & ctx = get_context();
        if (n1->get_owner_id() > n2->get_owner_id())
            std::swap(n1, n2);
        enode * nodes[2] = { n1, n2 };
        if (!ctx.add_fingerprint(this, 0, 2, nodes))
            return false; // axiom was already instantiated
        if (already_diseq(n1, n2))
            return false;
        m_extensionality_todo.push_back(std::make_pair(n1, n2));         
        return true;
    }

    void theory_array_base::assert_congruent(enode * a1, enode * a2) {
        TRACE("array", tout << "congruent: #" << a1->get_owner_id() << " #" << a2->get_owner_id() << "\n";);
        SASSERT(is_array_sort(a1));
        SASSERT(is_array_sort(a2));
        context & ctx = get_context();
        if (a1->get_owner_id() > a2->get_owner_id())
            std::swap(a1, a2);
        enode * nodes[2] = { a1, a2 };
        if (!ctx.add_fingerprint(this, 1, 2, nodes))
            return; // axiom was already instantiated
        m_congruent_todo.push_back(std::make_pair(a1, a2));         
    }

   
    void theory_array_base::assert_extensionality_core(enode * n1, enode * n2) {
        app * e1        = n1->get_owner();
        app * e2        = n2->get_owner();
        context & ctx   = get_context();
        ast_manager & m = get_manager();

        func_decl_ref_vector * funcs = nullptr;
        sort *                     s = m.get_sort(e1);

        VERIFY(m_sort2skolem.find(s, funcs));

        unsigned dimension = funcs->size();

        expr_ref_vector args1(m), args2(m);
        args1.push_back(e1);
        args2.push_back(e2);
        for (unsigned i = 0; i < dimension; i++) {
            expr * k = m.mk_app(funcs->get(i), e1, e2);
            args1.push_back(k);
            args2.push_back(k);
        }
        expr_ref sel1(mk_select(args1.size(), args1.c_ptr()), m);
        expr_ref sel2(mk_select(args2.size(), args2.c_ptr()), m);
        TRACE("ext", tout << mk_bounded_pp(sel1, m) << "\n" << mk_bounded_pp(sel2, m) << "\n";);
        literal n1_eq_n2     = mk_eq(e1, e2, true);
        literal sel1_eq_sel2 = mk_eq(sel1, sel2, true);
        ctx.mark_as_relevant(n1_eq_n2);
        ctx.mark_as_relevant(sel1_eq_sel2);
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(m.mk_not(ctx.bool_var2expr(n1_eq_n2.var())), m.mk_not(ctx.bool_var2expr(sel1_eq_sel2.var())));
            log_axiom_instantiation(body);
        }
        assert_axiom(n1_eq_n2, ~sel1_eq_sel2);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    /**
       \brief assert n1 = n2 => forall vars . (n1 vars) = (n2 vars)
     */
    void theory_array_base::assert_congruent_core(enode * n1, enode * n2) {
        app * e1        = n1->get_owner();
        app * e2        = n2->get_owner();
        context & ctx   = get_context();
        ast_manager & m = get_manager();
        sort* s         = m.get_sort(e1);
        unsigned dimension = get_array_arity(s);
        literal n1_eq_n2 = mk_eq(e1, e2, true);
        ctx.mark_as_relevant(n1_eq_n2);
        expr_ref_vector args1(m), args2(m);
        args1.push_back(instantiate_lambda(e1));
        args2.push_back(instantiate_lambda(e2));
        svector<symbol> names;
        sort_ref_vector sorts(m);
        for (unsigned i = 0; i < dimension; i++) {
            sort * srt = get_array_domain(s, i);
            sorts.push_back(srt);
            names.push_back(symbol(i));
            expr * k = m.mk_var(dimension - i - 1, srt);
            args1.push_back(k);
            args2.push_back(k);            
        }
        expr * sel1 = mk_select(dimension+1, args1.c_ptr());
        expr * sel2 = mk_select(dimension+1, args2.c_ptr());
        expr * eq = m.mk_eq(sel1, sel2);
        expr_ref q(m.mk_forall(dimension, sorts.c_ptr(), names.c_ptr(), eq), m);
        ctx.get_rewriter()(q);
        if (!ctx.b_internalized(q)) {
            ctx.internalize(q, true);
        }
        literal fa_eq = ctx.get_literal(q);
        ctx.mark_as_relevant(fa_eq);
        assert_axiom(~n1_eq_n2, fa_eq);
    }

    expr_ref theory_array_base::instantiate_lambda(app* e) {
        ast_manager& m = get_manager();
        quantifier * q = m.is_lambda_def(e->get_decl());
        expr_ref f(e, m);
        if (q) {
            var_subst sub(m);
            f = sub(q, e->get_num_args(), e->get_args());
        }
        return f;
    }

    bool theory_array_base::can_propagate() {
        return 
            !m_axiom1_todo.empty() || 
            !m_axiom2_todo.empty() || 
            !m_extensionality_todo.empty() || 
            !m_congruent_todo.empty() ||
            (!get_context().get_fparams().m_array_weak && has_propagate_up_trail());
    }

    void theory_array_base::propagate() {
        while (can_propagate()) {
            for (unsigned i = 0; i < m_axiom1_todo.size(); i++)
                assert_store_axiom1_core(m_axiom1_todo[i]);
            m_axiom1_todo.reset();
            for (unsigned i = 0; i < m_axiom2_todo.size(); i++)
                assert_store_axiom2_core(m_axiom2_todo[i].first, m_axiom2_todo[i].second);
            m_axiom2_todo.reset();
            for (unsigned i = 0; i < m_extensionality_todo.size(); i++)
                assert_extensionality_core(m_extensionality_todo[i].first, m_extensionality_todo[i].second);
            for (unsigned i = 0; i < m_congruent_todo.size(); i++)
                assert_congruent_core(m_congruent_todo[i].first, m_congruent_todo[i].second);
            m_extensionality_todo.reset();
            m_congruent_todo.reset();
            if (!get_context().get_fparams().m_array_weak && has_propagate_up_trail()) {
                get_context().push_trail(value_trail<context, unsigned>(m_array_weak_head));
                for (; m_array_weak_head < m_array_weak_trail.size(); ++m_array_weak_head) {
                    set_prop_upward(m_array_weak_trail[m_array_weak_head]);
                }                
            }
        }
    }

    /**
       \brief Return true if v is shared between two different "instances" of the array theory.
       It is shared if it is used in more than one role. The possible roles are: array, index, and value.
       Example:
         (store v i j) <--- v is used as an array
         (select A v)  <--- v is used as an index
         (store A i v) <--- v is used as an value
    */
    bool theory_array_base::is_shared(theory_var v) const {
        enode * n      = get_enode(v);
        enode * r      = n->get_root();
        bool is_array  = false;
        bool is_index  = false;
        bool is_value  = false;
        int  num_roles = 0;
#define SET_ARRAY(arg) if (arg->get_root() == r && !is_array) { is_array = true; num_roles++; } if (num_roles > 1) return true
#define SET_INDEX(arg) if (arg->get_root() == r && !is_index) { is_index = true; num_roles++; } if (num_roles > 1) return true
#define SET_VALUE(arg) if (arg->get_root() == r && !is_value) { is_value = true; num_roles++; } if (num_roles > 1) return true
        enode_vector::const_iterator it  = r->begin_parents();
        enode_vector::const_iterator end = r->end_parents();
        for (; it != end; ++it) {
            enode * parent       = *it;
#if 0
            if (!ctx.is_relevant(parent))
                continue;
#endif
            unsigned    num_args = parent->get_num_args();
            if (is_store(parent)) {
                SET_ARRAY(parent->get_arg(0));
                for (unsigned i = 1; i < num_args - 1; i++) {
                    SET_INDEX(parent->get_arg(i));
                }
                SET_VALUE(parent->get_arg(num_args - 1));
            }
            else if (is_select(parent)) {
                SET_ARRAY(parent->get_arg(0));
                for (unsigned i = 1; i < num_args; i++) {
                    SET_INDEX(parent->get_arg(i));
                }
            }
            else if (is_const(parent)) {
                SET_VALUE(parent->get_arg(0));
            }
        }
        return false;
    }

#if 0
    void theory_array_base::collect_shared_vars(sbuffer<theory_var> & result) {
        TRACE("array_shared", tout << "collecting shared vars...\n";);
        context & ctx = get_context();
        ptr_buffer<enode> to_unmark;
        unsigned num_vars = get_num_vars();
        for (unsigned i = 0; i < num_vars; i++) {
            enode * n = get_enode(i);
            if (ctx.is_relevant(n) && ctx.is_shared(n)) {
                enode * r = n->get_root();
                if (!r->is_marked() && is_array_sort(r)) {
                    TRACE("array_shared", tout << "new shared var: #" << r->get_owner_id() << "\n";);
                    r->set_mark();
                    to_unmark.push_back(r);
                    theory_var r_th_var = r->get_th_var(get_id());
                    SASSERT(r_th_var != null_theory_var);
                    result.push_back(r_th_var);
                }
            }
        }
        unmark_enodes(to_unmark.size(), to_unmark.c_ptr());
    }
#else
    void theory_array_base::collect_shared_vars(sbuffer<theory_var> & result) {
        TRACE("array_shared", tout << "collecting shared vars...\n";);
        context & ctx = get_context();
        ptr_buffer<enode> to_unmark;
        unsigned num_vars = get_num_vars();
        for (unsigned i = 0; i < num_vars; i++) {
        enode * n = get_enode(i);
            if (ctx.is_relevant(n)) {
            enode * r = n->get_root();
        if (!r->is_marked()){
            if(is_array_sort(r) && ctx.is_shared(r)) {
              TRACE("array_shared", tout << "new shared var: #" << r->get_owner_id() << "\n";);
              theory_var r_th_var = r->get_th_var(get_id());
              SASSERT(r_th_var != null_theory_var);
              result.push_back(r_th_var);
            }
            r->set_mark();
            to_unmark.push_back(r);
        }
            }
        }
        unmark_enodes(to_unmark.size(), to_unmark.c_ptr());
    }
#endif

    /**
       \brief Create interface variables for shared array variables.
       Return the number of new interface equalities.
    */
    unsigned theory_array_base::mk_interface_eqs() {
        context & ctx   = get_context();
        ast_manager & m = get_manager();
        sbuffer<theory_var> roots;
        collect_shared_vars(roots);
        unsigned result = 0;
        sbuffer<theory_var>::iterator it1  = roots.begin();
        sbuffer<theory_var>::iterator end1 = roots.end();
        for (; it1 != end1; ++it1) {
            TRACE("array_bug", tout << "mk_interface_eqs: processing: v" << *it1 << "\n";);
            theory_var  v1 = *it1;
            enode *     n1 = get_enode(v1);
            sort *      s1 = m.get_sort(n1->get_owner());
            sbuffer<theory_var>::iterator it2 = it1;
            ++it2;
            for (; it2 != end1; ++it2) {
                theory_var v2 = *it2;
                enode *    n2 = get_enode(v2);
                sort *     s2 = m.get_sort(n2->get_owner());
                if (s1 == s2 && !ctx.is_diseq(n1, n2)) {
                    app * eq  = mk_eq_atom(n1->get_owner(), n2->get_owner());
                    if (!ctx.b_internalized(eq) || !ctx.is_relevant(eq)) {
                        result++;
                        ctx.internalize(eq, true);
                        ctx.mark_as_relevant(eq);
                    }
                }
            }
        }
        return result;
    }

    void theory_array_base::push_scope_eh() {
        m_scopes.push_back(scope(m_sorts_trail.size()));
        theory::push_scope_eh();
    }

    void theory_array_base::pop_scope_eh(unsigned num_scopes) {
        reset_queues();
        scope const & s = m_scopes[m_scopes.size() - num_scopes];
        restore_sorts(s.m_sorts_trail_lim);
        m_scopes.shrink(m_scopes.size()-num_scopes);
        theory::pop_scope_eh(num_scopes);
    }

    void theory_array_base::restore_sorts(unsigned old_size) {
        while (m_sorts_trail.size() > old_size) {
            sort * s = m_sorts_trail.back();
            func_decl_ref_vector * funcs = nullptr;
            if (m_sort2skolem.find(s, funcs)) {
                m_sort2skolem.remove(s);
                dealloc(funcs);
            }
            m_sorts_trail.pop_back();
        }
    }

    void theory_array_base::reset_eh() {
        reset_queues();
        pop_scope_eh(0);
        theory::reset_eh();
    }

    void theory_array_base::reset_queues() {
        m_axiom1_todo.reset();
        m_axiom2_todo.reset();
        m_extensionality_todo.reset();
        m_congruent_todo.reset();
    }


    void theory_array_base::set_default(theory_var v, enode* n) {
        TRACE("array", tout << "set default: " << v << " " << mk_pp(n->get_owner(), get_manager()) << "\n";);
        v = mg_find(v);
        if (m_defaults[v] == 0) {
            m_defaults[v] = n;
        }
    }

    enode* theory_array_base::get_default(theory_var v) {
        return m_defaults[mg_find(v)];
    }

    theory_var theory_array_base::mg_find(theory_var n) {
        if (m_parents[n] < 0) {
            return n;
        }
        theory_var n0 = n;
        n = m_parents[n0];
        if (m_parents[n] < -1) {
            return n;
        }
        while (m_parents[n] >= 0) {
            n = m_parents[n];        
        }
        // compress path.
        while (m_parents[n0] >= 0) {
            theory_var n1 = m_parents[n0];
            m_parents[n0] = n;
            n0 = n1;
        }
        return n;
    }

    void theory_array_base::mg_merge(theory_var n, theory_var m) {
        n = mg_find(n);
        m = mg_find(m);
        if (n != m) {
            SASSERT(m_parents[n] < 0);
            SASSERT(m_parents[m] < 0);
            if (m_parents[n] > m_parents[m]) {
                std::swap(n, m);
            }
            m_parents[n] += m_parents[m];
            m_parents[m] = n;

            if (m_defaults[n] == 0) {
                m_defaults[n] = m_defaults[m];
            }
            CTRACE("array", m_defaults[m], 
                   tout << mk_pp(m_defaults[m]->get_root()->get_owner(), get_manager()) << "\n";
                   tout << mk_pp(m_defaults[n]->get_root()->get_owner(), get_manager()) << "\n";
                  );

            // NB. it may be the case that m_defaults[m] != m_defaults[n]
            //     when m and n are finite arrays.

        }
    }


    void theory_array_base::init_model(model_generator & m) {
        m_factory = alloc(array_factory, get_manager(), m.get_model());
        m.register_factory(m_factory);
        m_use_unspecified_default = is_unspecified_default_ok();
        collect_defaults();
        collect_selects();
        propagate_selects();
        if (m_bapa) m_bapa->init_model();
    }

    /**
       \brief It is ok to use an unspecified default value for arrays, when the 
       logical context does not contain store, default and const terms.
       
       That is, other modules (such as smt_model_finder) may set the default value to an arbitrary value.
    */
    bool theory_array_base::is_unspecified_default_ok() const {
        context & ctx = get_context();
        int num_vars = get_num_vars();
        for (theory_var v = 0; v < num_vars; ++v) {
            enode * n    = get_enode(v);
            
            // If n is not relevant, then it should not be used to set defaults.
            if (!ctx.is_relevant(n))
                continue;
            
            if (is_store(n) || is_const(n) || is_default(n) || is_set_has_size(n))
                return false;
        }
        return true;
    }
        

    void theory_array_base::collect_defaults() {
        int num_vars = get_num_vars();
        m_defaults.reset();
        m_else_values.reset();
        m_parents.reset();
        m_parents.resize(num_vars, -1);
        m_defaults.resize(num_vars);
        m_else_values.resize(num_vars);
    
        if (m_use_unspecified_default)
            return;

        context & ctx = get_context();

        //
        // Create equivalence classes for defaults.
        //
        for (theory_var v = 0; v < num_vars; ++v) {
            enode * n    = get_enode(v);
            
            // If n is not relevant, then it should not be used to set defaults.
            if (!ctx.is_relevant(n))
                continue;
            
            theory_var r = get_representative(v);

            mg_merge(v, r);

            if (is_store(n)) {
                theory_var w = n->get_arg(0)->get_th_var(get_id());
                SASSERT(w != null_theory_var);

                mg_merge(v, get_representative(w));
                                
                TRACE("array", tout << "merge: " << mk_pp(n->get_owner(), get_manager()) << " " << v << " " << w << "\n";);
            }
            else if (is_const(n)) {
                set_default(v, n->get_arg(0));
            }
            else if (is_default(n)) {
                theory_var w = n->get_arg(0)->get_th_var(get_id());
                SASSERT(w != null_theory_var);
                set_default(w, n);
            }
        }
    }

    unsigned theory_array_base::sel_hash::operator()(enode * n) const {
        return get_composite_hash<enode *, sel_khasher, sel_chasher>(n, n->get_num_args() - 1, sel_khasher(), sel_chasher());
    }

    bool theory_array_base::sel_eq::operator()(enode * n1, enode * n2) const {
        SASSERT(n1->get_num_args() == n2->get_num_args());
        unsigned num_args = n1->get_num_args();
        for (unsigned i = 1; i < num_args; i++) {
            if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                return false;
        }
        return true;
    }

    theory_array_base::select_set * theory_array_base::get_select_set(enode * n) {
        enode * r = n->get_root();
        select_set * set = nullptr;
        m_selects.find(r, set);
        if (set == nullptr) {
            set = alloc(select_set);
            m_selects.insert(r, set);
            m_selects_domain.push_back(r);
            m_selects_range.push_back(set);
        }
        return set;
    }

    void theory_array_base::collect_selects() {
        int num_vars = get_num_vars();

        m_selects.reset();
        m_selects_domain.reset();
        m_selects_range.reset();

        for (theory_var v = 0; v < num_vars; ++v) {
            enode * r = get_enode(v)->get_root();                
            if (is_representative(v) && get_context().is_relevant(r)) {
                for (enode * parent : r->get_const_parents()) {
                    if (parent->get_cg() == parent &&
                        get_context().is_relevant(parent) &&
                        is_select(parent) &&
                        parent->get_arg(0)->get_root() == r) {
                        select_set * s = get_select_set(r);
                        SASSERT(!s->contains(parent) || (*(s->find(parent)))->get_root() == parent->get_root());
                        s->insert(parent);
                    }
                }
            }
        }
    }
    
    void theory_array_base::propagate_select_to_store_parents(enode * r, enode * sel, enode_pair_vector & todo) {
        SASSERT(r->get_root() == r);
        SASSERT(is_select(sel));
        if (!get_context().is_relevant(r)) {
            return;
        }
        for (enode * parent : r->get_const_parents()) {
            if (get_context().is_relevant(parent) &&
                is_store(parent) &&
                parent->get_arg(0)->get_root() == r) {
                // propagate upward
                select_set * parent_sel_set = get_select_set(parent);
                enode * parent_root = parent->get_root();
                
                if (parent_sel_set->contains(sel))
                    continue;

                SASSERT(sel->get_num_args() + 1 == parent->get_num_args());
                    
                // check whether the sel idx was overwritten by the store
                unsigned num_args = sel->get_num_args();
                unsigned i = 1;
                for (; i < num_args; i++) {
                    if (sel->get_arg(i)->get_root() != parent->get_arg(i)->get_root())
                        break;
                }

                if (i < num_args) {
                    SASSERT(!parent_sel_set->contains(sel) || (*(parent_sel_set->find(sel)))->get_root() == sel->get_root());
                    parent_sel_set->insert(sel);
                    todo.push_back(std::make_pair(parent_root, sel));
                }
            }
        }
    }

    void theory_array_base::propagate_selects_to_store_parents(enode * r, enode_pair_vector & todo) {
        select_set * sel_set = get_select_set(r);
        for (enode* sel : *sel_set) {
            SASSERT(is_select(sel));
            propagate_select_to_store_parents(r, sel, todo);
        }
    }

    void theory_array_base::propagate_selects() {
        enode_pair_vector todo;
        for (enode * r : m_selects_domain) {
            propagate_selects_to_store_parents(r, todo);
        }
        for (unsigned qhead = 0; qhead < todo.size(); qhead++) {
            enode_pair & pair = todo[qhead];
            enode * r   = pair.first;
            enode * sel = pair.second;
            propagate_select_to_store_parents(r, sel, todo);
        }
    }

    void theory_array_base::finalize_model(model_generator & m) {
        std::for_each(m_selects_range.begin(), m_selects_range.end(), delete_proc<select_set>());
    }

    class array_value_proc : public model_value_proc {
        family_id                       m_fid;
        sort *                          m_sort;
        unsigned                        m_num_entries;
        unsigned                        m_dim; //!< number of dimensions;
        app *                           m_else;
        bool                            m_unspecified_else;
        svector<model_value_dependency> m_dependencies;

    public:
        array_value_proc(family_id fid, sort * s, extra_fresh_value * v):
            m_fid(fid), 
            m_sort(s), 
            m_num_entries(0), 
            m_dim(0), 
            m_else(nullptr),
            m_unspecified_else(false) {
            m_dependencies.push_back(model_value_dependency(v));
        }

        array_value_proc(family_id fid, sort * s, app * else_value):
            m_fid(fid), 
            m_sort(s), 
            m_num_entries(0), 
            m_dim(0), 
            m_else(else_value),
            m_unspecified_else(false) {
        }

        array_value_proc(family_id fid, sort * s, enode * else_value):
            m_fid(fid), 
            m_sort(s), 
            m_num_entries(0), 
            m_dim(0), 
            m_else(nullptr),
            m_unspecified_else(false) {
            m_dependencies.push_back(model_value_dependency(else_value));
        }

        array_value_proc(family_id fid, sort * s):
            m_fid(fid), 
            m_sort(s), 
            m_num_entries(0), 
            m_dim(0), 
            m_else(nullptr),
            m_unspecified_else(true) {
        }

        ~array_value_proc() override {}
     
        void add_entry(unsigned num_args, enode * const * args, enode * value) {
            SASSERT(num_args > 0);
            SASSERT(m_dim == 0 || m_dim == num_args);
            m_dim = num_args;
            m_num_entries ++;
            for (unsigned i = 0; i < num_args; i++) 
                m_dependencies.push_back(model_value_dependency(args[i]));
            m_dependencies.push_back(model_value_dependency(value));
        }

        void get_dependencies(buffer<model_value_dependency> & result) override {
            result.append(m_dependencies.size(), m_dependencies.c_ptr());
        }
        
        app * mk_value(model_generator & mg, expr_ref_vector const & values) override {
            // values must have size = m_num_entries * (m_dim + 1) + ((m_else || m_unspecified_else) ? 0 : 1) 
            // an array value is a lookup table + else_value
            // each entry has m_dim indexes that map to a value.
            ast_manager & m = mg.get_manager();
            SASSERT(values.size() == m_dependencies.size());
            SASSERT(values.size() == m_num_entries * (m_dim + 1) + ((m_else || m_unspecified_else) ? 0 : 1));

            unsigned arity = get_array_arity(m_sort);
            func_decl * f    = mk_aux_decl_for_array_sort(m, m_sort);
            func_interp * fi = alloc(func_interp, m, arity);
            mg.get_model().register_decl(f, fi);

            unsigned idx     = 0;
            if (m_else || m_unspecified_else) {
                fi->set_else(m_else);
            }
            else {
                fi->set_else(to_app(values[0]));
                idx = 1;
            }
            
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < m_num_entries; i++) {
                args.reset();
                // copy indices
                for (unsigned j = 0; j < m_dim; j++, idx++) 
                    args.push_back(values[idx]);
                expr * result = values[idx];
                idx++;
                fi->insert_entry(args.c_ptr(), result);
            }

            parameter p[1] = { parameter(f) };
            return m.mk_app(m_fid, OP_AS_ARRAY, 1, p); 
        }
    };

    bool theory_array_base::include_func_interp(func_decl* f) {
        return is_decl_of(f, get_id(), OP_ARRAY_EXT);
    }

    model_value_proc * theory_array_base::mk_value(enode * n, model_generator & m) {
        SASSERT(get_context().is_relevant(n));
        theory_var v       = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        sort * s           = get_manager().get_sort(n->get_owner());
        enode * else_val_n = get_default(v);
        array_value_proc * result = nullptr;

        if (m_use_unspecified_default) {
            SASSERT(else_val_n == 0);
            result = alloc(array_value_proc, get_id(), s);
        }
        else {
            if (else_val_n != nullptr) {
                SASSERT(get_context().is_relevant(else_val_n));
                result   = alloc(array_value_proc, get_id(), s, else_val_n);
            }
            else {
                theory_var r    = mg_find(v);
                void * else_val = m_else_values[r];                
                // DISABLED. It seems wrong, since different nodes can share the same
                // else_val according to the mg class.
                // SASSERT(else_val == 0 || get_context().is_relevant(UNTAG(app*, else_val)));
                if (else_val == nullptr) {
                    sort * range = to_sort(s->get_parameter(s->get_num_parameters() - 1).get_ast());
                    // IMPORTANT:
                    // The implementation should not assume a fresh value is created for 
                    // the else_val if the range is finite

                    TRACE("array", tout << mk_pp(n->get_owner(), get_manager()) << " " << mk_pp(range, get_manager()) << " " << range->is_infinite() << "\n";);
                    if (range->is_infinite())
                        else_val = TAG(void*, m.mk_extra_fresh_value(range), 1);
                    else
                        else_val = TAG(void*, m.get_some_value(range), 0);
                    m_else_values[r] = else_val;
                }
                if (GET_TAG(else_val) == 0) {
                    result = alloc(array_value_proc, get_id(), s, UNTAG(app*, else_val));
                }
                else {
                    result = alloc(array_value_proc, get_id(), s, UNTAG(extra_fresh_value*, else_val));
                }
            }
        }
        SASSERT(result != 0);
        select_set * sel_set = nullptr;
        m_selects.find(n->get_root(), sel_set);
        if (sel_set != nullptr) {
            ptr_buffer<enode> args;
            for (enode * select : *sel_set) {
                args.reset();
                unsigned num = select->get_num_args();
                for (unsigned j = 1; j < num; ++j)
                    args.push_back(select->get_arg(j));
                SASSERT(get_context().is_relevant(select));
                result->add_entry(args.size(), args.c_ptr(), select);
            }
        }
        TRACE("array", 
              tout << mk_pp(n->get_root()->get_owner(), get_manager()) << "\n";
              if (sel_set) {
                  for (enode* s : *sel_set) {
                      tout << "#" << s->get_root()->get_owner()->get_id() << " " << mk_pp(s->get_owner(), get_manager()) << "\n";
                  }
              }
              if (else_val_n) {
                  tout << "else: " << mk_pp(else_val_n->get_owner(), get_manager()) << "\n";
              });
        return result;
    }

};
