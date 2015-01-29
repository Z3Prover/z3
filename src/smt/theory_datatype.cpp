/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_datatype.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-31.

Revision History:

--*/

#include"smt_context.h"
#include"theory_datatype.h"
#include"smt_model_generator.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"stats.h"
#include"ast_smt2_pp.h"

namespace smt {
    
    class dt_eq_justification : public ext_theory_eq_propagation_justification {
    public:
        dt_eq_justification(family_id fid, region & r, literal antecedent, enode * lhs, enode * rhs):
            ext_theory_eq_propagation_justification(fid, r, 1, &antecedent, 0, 0, lhs, rhs) {
        }
        // Remark: the assignment must be propagated back to the datatype theory.
        virtual theory_id get_from_theory() const { return null_theory_id; } 
    };

    /**
       \brief Assert the axiom (antecedent => lhs = rhs)
       antecedent may be null_literal
    */
    void theory_datatype::assert_eq_axiom(enode * lhs, expr * rhs, literal antecedent) {
        ast_manager & m   = get_manager();
        context & ctx     = get_context();
        if (m.proofs_enabled()) {
            literal l(mk_eq(lhs->get_owner(), rhs, true));
            ctx.mark_as_relevant(l);
            if (antecedent != null_literal) {
                literal lits[2] = {l, ~antecedent};
                ctx.mk_th_axiom(get_id(), 2, lits);
            }
            else {
                literal lits[1] = {l};
                ctx.mk_th_axiom(get_id(), 1, lits);
            }
        }
        else {
            ctx.internalize(rhs, false);
            TRACE("datatype", tout << "adding axiom:\n" << mk_pp(lhs->get_owner(), m) << "\n=\n" << mk_pp(rhs, m) << "\n";);
            if (antecedent == null_literal) {
                ctx.assign_eq(lhs, ctx.get_enode(rhs), eq_justification::mk_axiom());
            }
            else if (ctx.get_assignment(antecedent) != l_true) {
                literal l(mk_eq(lhs->get_owner(), rhs, true));
                ctx.mark_as_relevant(l);
                ctx.mark_as_relevant(antecedent);
                literal lits[2] = {l, ~antecedent};
                ctx.mk_th_axiom(get_id(), 2, lits);
            }
            else {
                SASSERT(ctx.get_assignment(antecedent) == l_true);
                region & r   = ctx.get_region();
                enode * _rhs = ctx.get_enode(rhs);
                justification * js = ctx.mk_justification(dt_eq_justification(get_id(), r, antecedent, lhs, _rhs));
                TRACE("datatype", tout << "assigning... #" << lhs->get_owner_id() << " #" << _rhs->get_owner_id() << "\n";
                      tout << "v" << lhs->get_th_var(get_id()) << " v" << _rhs->get_th_var(get_id()) << "\n";);
                TRACE("datatype_detail", display(tout););
                ctx.assign_eq(lhs, _rhs, eq_justification(js));
            }
        }
    }

    /**
       \brief Assert the equality (= n (c (acc_1 n) ... (acc_m n))) where 
       where acc_i are the accessors of constructor c.
    */
    void theory_datatype::assert_is_constructor_axiom(enode * n, func_decl * c, literal antecedent) {
        TRACE("datatype_bug", tout << "creating axiom (= n (c (acc_1 n) ... (acc_m n))) for\n" << mk_pp(n->get_owner(), get_manager()) << "\n";);
        m_stats.m_assert_cnstr++;
        SASSERT(m_util.is_constructor(c));
        SASSERT(m_util.is_datatype(get_manager().get_sort(n->get_owner())));
        ast_manager & m = get_manager();
        ptr_vector<expr> args;
        ptr_vector<func_decl> const * accessors   = m_util.get_constructor_accessors(c);
        SASSERT(c->get_arity() == accessors->size());
        ptr_vector<func_decl>::const_iterator it  = accessors->begin();
        ptr_vector<func_decl>::const_iterator end = accessors->end();
        for (; it != end; ++it) {
            func_decl * d = *it;
            SASSERT(d->get_arity() == 1);
            expr * acc    = m.mk_app(d, n->get_owner());
            args.push_back(acc);
        }
        expr * mk       = m.mk_app(c, args.size(), args.c_ptr());
        assert_eq_axiom(n, mk, antecedent);
    }

    /**
       \brief Given a constructor n := (c a_1 ... a_m) assert the axioms
       (= (acc_1 n) a_1)
       ...
       (= (acc_m n) a_m)
    */
    void theory_datatype::assert_accessor_axioms(enode * n) {
        m_stats.m_assert_accessor++;

        SASSERT(is_constructor(n));
        ast_manager & m   = get_manager();
        func_decl * d     = n->get_decl();
        ptr_vector<func_decl> const * accessors   = m_util.get_constructor_accessors(d);
        SASSERT(n->get_num_args() == accessors->size());
        ptr_vector<func_decl>::const_iterator it  = accessors->begin();
        ptr_vector<func_decl>::const_iterator end = accessors->end();
        for (unsigned i = 0; it != end; ++it, ++i) {
            func_decl * acc   = *it;
            app * acc_app     = m.mk_app(acc, n->get_owner());
            enode * arg       = n->get_arg(i);
            assert_eq_axiom(arg, acc_app, null_literal);
        }
    }

    /**
       \brief Sign a conflict for r := is_mk(a), c := mk(...), not(r),  and c == a.
    */
    void theory_datatype::sign_recognizer_conflict(enode * c, enode * r) {
        SASSERT(is_constructor(c));
        SASSERT(is_recognizer(r));
        SASSERT(m_util.get_recognizer_constructor(r->get_decl()) == c->get_decl());
        SASSERT(c->get_root() == r->get_arg(0)->get_root());
        TRACE("recognizer_conflict",
              tout << mk_ismt2_pp(c->get_owner(), get_manager()) << "\n" << mk_ismt2_pp(r->get_owner(), get_manager()) << "\n";);
        context & ctx = get_context();
        literal l(ctx.enode2bool_var(r));
        SASSERT(ctx.get_assignment(l) == l_false);
        l.neg();
        SASSERT(ctx.get_assignment(l) == l_true);
        enode_pair p(c, r->get_arg(0));
        region & reg = ctx.get_region();
        ctx.set_conflict(ctx.mk_justification(ext_theory_conflict_justification(get_id(), reg, 1, &l, 1, &p)));
    }

    /**
       \brief Given a field update n := { r with field := v } for constructor C, assert the axioms:
       (=> (is-C r) (= (acc_j n) (acc_j r))) for acc_j != field
       (=> (is-C r) (= (field n) v))         for acc_j != field
       (=> (not (is-C r)) (= n r))
    */
    void theory_datatype::assert_update_field_axioms(enode * n) {
        m_stats.m_assert_update_field++;
        SASSERT(is_update_field(n));
        context & ctx = get_context();
        ast_manager & m  = get_manager();
        app*        own  = n->get_owner();
        expr*       arg1 = own->get_arg(0);
        expr*       arg2 = own->get_arg(1);
        func_decl * upd  = n->get_decl();
        func_decl * acc  = to_func_decl(upd->get_parameter(0).get_ast());
        func_decl * con  = m_util.get_accessor_constructor(acc);
        func_decl * rec  = m_util.get_constructor_recognizer(con);
        ptr_vector<func_decl> const * accessors   = m_util.get_constructor_accessors(con);
        ptr_vector<func_decl>::const_iterator it  = accessors->begin();
        ptr_vector<func_decl>::const_iterator end = accessors->end();
        app_ref rec_app(m.mk_app(rec, arg1), m);
        ctx.internalize(rec_app, false);
        literal is_con(ctx.get_bool_var(rec_app));
        for (; it != end; ++it) {
            enode* arg;
            func_decl * acc1   = *it;
            if (acc1 == acc) {
                arg = n->get_arg(1);
            }
            else {
                app* acc_app = m.mk_app(acc1, arg1);
                ctx.internalize(acc_app, false);
                arg = ctx.get_enode(acc_app);
            }
            app * acc_own = m.mk_app(acc1, own);
            assert_eq_axiom(arg, acc_own, is_con); 
        }
        // update_field is identity if 'n' is not created by a matching constructor.        
        assert_eq_axiom(n, arg1, ~is_con);
    }

    theory_var theory_datatype::mk_var(enode * n) {
        theory_var r  = theory::mk_var(n);
        theory_var r2 = m_find.mk_var();
        SASSERT(r == r2);
        SASSERT(r == static_cast<int>(m_var_data.size()));
        m_var_data.push_back(alloc(var_data));
        var_data * d  = m_var_data[r];
        context & ctx   = get_context();
        ctx.attach_th_var(n, this, r);
        if (is_constructor(n)) {
            d->m_constructor = n;
            assert_accessor_axioms(n);
        }
        else if (is_update_field(n)) {
            assert_update_field_axioms(n);
        }
        else {
            ast_manager & m = get_manager();
            sort * s      = m.get_sort(n->get_owner());
            if (m_util.get_datatype_num_constructors(s) == 1) {
                func_decl * c = m_util.get_datatype_constructors(s)->get(0);
                assert_is_constructor_axiom(n, c, null_literal);
            }
            else {
                if (m_params.m_dt_lazy_splits == 0 || (m_params.m_dt_lazy_splits == 1 && !s->is_infinite()))
                    mk_split(r);
            }
        }
        return r;
    }

    bool theory_datatype::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("datatype", tout << "internalizing atom:\n" << mk_pp(atom, get_manager()) << "\n";);
        return internalize_term(atom);
    }

    bool theory_datatype::internalize_term(app * term) {
        TRACE("datatype", tout << "internalizing term:\n" << mk_pp(term, get_manager()) << "\n";);
        context & ctx     = get_context();
        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        // the internalization of the arguments may trigger the internalization of term.
        if (ctx.e_internalized(term))
            return true;
        enode * e       = ctx.mk_enode(term, false, get_manager().is_bool(term), true); // possible optimization, the third argument may be set to false, if the term (actually, atom) is not in the context of a gate.
        if (get_manager().is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        if (is_constructor(term) || is_update_field(term)) {
            SASSERT(!is_attached_to_var(e));
            // *** We must create a theory variable for each argument that has sort datatype ***
            //
            // The apply_sort_cnstr method will not create a theory
            // variable for an expression N when sort of N has an
            // infinite number of elements.
            //
            // This may create problems during model construction.
            // For example, suppose we have
            //    x1 = cons(v1, x2)
            // and x1 and x2 are lists of integers. 
            // This sort has an infinite number of elements. So, in principle,
            // we do not need a theory variable for x2. 
            // Recall that if an expression is not associated with a
            // theory variable, then a fresh value is associated with
            // it.
            // Moreover, fresh variables of sort S can only be created after the
            // interpretation for each (relevant) expression of sort S in the
            // logical context is created.  Returning to the example,
            // to create the interpretation of x1 we need the
            // interpretation for x2.  So, x2 cannot be a fresh value,
            // since it would have to be created after x1.
            //
            for (unsigned i = 0; i < num_args; i++) {
                enode * arg = e->get_arg(i);
                sort * s    = get_manager().get_sort(arg->get_owner());
                if (!m_util.is_datatype(s))
                    continue;
                if (is_attached_to_var(arg))
                    continue;
                mk_var(arg);
            }
            mk_var(e);
        }
        else {
            SASSERT(is_accessor(term) || is_recognizer(term));
            SASSERT(term->get_num_args() == 1);
            enode * arg = e->get_arg(0);
            if (!is_attached_to_var(arg))
                mk_var(arg);
            SASSERT(is_attached_to_var(arg));
        }
        if (is_recognizer(term)) {
            enode * arg = e->get_arg(0);
            theory_var v = arg->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            // When relevancy propagation is enabled, the recognizer is only added when it is marked as relevant.
            if (!ctx.relevancy()) 
                add_recognizer(v, e);
        }
        return true;
    }

    void theory_datatype::apply_sort_cnstr(enode * n, sort * s) {
        // Remark: If s is an infinite sort, then it is not necessary to create
        // a theory variable. 
        // 
        // Actually, when the logical context has quantifiers, it is better to 
        // disable this optimization.
        // Example:
        // 
        //   (forall (l list) (a Int) (= (len (cons a l)) (+ (len l) 1)))
        //   (assert (> (len a) 1)
        //   
        // If the theory variable is not created for 'a', then a wrong model will be generated.
        TRACE("datatype", tout << "apply_sort_cnstr: #" << n->get_owner_id() << "\n";);
        TRACE("datatype_bug", tout << "apply_sort_cnstr:\n" << mk_pp(n->get_owner(), get_manager()) << "\n";);
        if ((get_context().has_quantifiers() || (m_util.is_datatype(s) && !s->is_infinite())) && !is_attached_to_var(n)) {
            mk_var(n);
        }
    }

    void theory_datatype::new_eq_eh(theory_var v1, theory_var v2) {
        m_find.merge(v1, v2);
    }

    bool theory_datatype::use_diseqs() const {
        return false;
    }

    void theory_datatype::new_diseq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    void theory_datatype::assign_eh(bool_var v, bool is_true) {
        context & ctx = get_context();
        enode * n     = ctx.bool_var2enode(v);
        if (!is_recognizer(n))
            return;
        TRACE("datatype", tout << "assigning recognizer: #" << n->get_owner_id() << " is_true: " << is_true << "\n" 
              << mk_bounded_pp(n->get_owner(), get_manager()) << "\n";);
        SASSERT(n->get_num_args() == 1);
        enode * arg   = n->get_arg(0);
        theory_var tv = arg->get_th_var(get_id());
        tv = m_find.find(tv);
        var_data * d  = m_var_data[tv];
        func_decl * r = n->get_decl();
        func_decl * c = m_util.get_recognizer_constructor(r);
        if (is_true) {
            SASSERT(tv != null_theory_var);
            if (d->m_constructor != 0 && d->m_constructor->get_decl() == c)
                return; // do nothing
            assert_is_constructor_axiom(arg, c, literal(v));
        }
        else {
            if (d->m_constructor != 0) {
                if (d->m_constructor->get_decl() == c) {
                    // conflict
                    sign_recognizer_conflict(d->m_constructor, n);
                }
            }
            else {
                propagate_recognizer(tv, n);
            }
        }
    }

    void theory_datatype::relevant_eh(app * n) {
        TRACE("datatype", tout << "relevant_eh: " << mk_bounded_pp(n, get_manager()) << "\n";);
        context & ctx = get_context();
        SASSERT(ctx.relevancy());
        if (is_recognizer(n)) {
            TRACE("datatype", tout << "relevant_eh: #" << n->get_id() << "\n" << mk_bounded_pp(n, get_manager()) << "\n";);
            SASSERT(ctx.e_internalized(n));
            enode * e = ctx.get_enode(n);
            theory_var v = e->get_arg(0)->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            add_recognizer(v, e);
        }
    }

    void theory_datatype::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_datatype::pop_scope_eh(unsigned num_scopes) {
        m_trail_stack.pop_scope(num_scopes);
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        std::for_each(m_var_data.begin() + num_old_vars, m_var_data.end(), delete_proc<var_data>());
        m_var_data.shrink(num_old_vars);
        theory::pop_scope_eh(num_scopes);
        SASSERT(m_find.get_num_vars() == m_var_data.size());
        SASSERT(m_find.get_num_vars() == get_num_vars());
    }

    final_check_status theory_datatype::final_check_eh() {
        int num_vars = get_num_vars();
        final_check_status r = FC_DONE;
        for (int v = 0; v < num_vars; v++) {
            if (v == static_cast<int>(m_find.find(v))) {
                enode * node = get_enode(v);
                if (occurs_check(node)) {
                    // conflict was detected... 
                    // return...
                    return FC_CONTINUE;
                }
                if (m_params.m_dt_lazy_splits > 0) {
                    // using lazy case splits...
                    var_data * d = m_var_data[v];
                    if (d->m_constructor == 0) {
                        mk_split(v);
                        r = FC_CONTINUE;
                    }
                }
            }
        }
        return r;
    }

    /**
       \brief Check if n can be reached starting from n and following equalities and constructors.
       For example, occur_check(a1) returns true in the following set of equalities:
       a1 = cons(v1, a2)
       a2 = cons(v2, a3)
       a3 = cons(v3, a1)
    */
    bool theory_datatype::occurs_check(enode * n) {
        TRACE("datatype", tout << "occurs check: #" << n->get_owner_id() << "\n";);
        m_to_unmark.reset();
        m_used_eqs.reset();
        m_main   = n;
        bool res = occurs_check_core(m_main);
        unmark_enodes(m_to_unmark.size(), m_to_unmark.c_ptr());
        if (res) {
            context & ctx = get_context();
            region & r    = ctx.get_region();
            ctx.set_conflict(ctx.mk_justification(ext_theory_conflict_justification(get_id(), r, 0, 0, m_used_eqs.size(), m_used_eqs.c_ptr())));
            TRACE("occurs_check",
                  tout << "occurs_check: true\n";
                  svector<enode_pair>::const_iterator it  = m_used_eqs.begin();
                  svector<enode_pair>::const_iterator end = m_used_eqs.end();
                  for(; it != end; ++it) {
                      enode_pair const & p = *it;
                      tout << "eq: #" << p.first->get_owner_id() << " #" << p.second->get_owner_id() << "\n";
                      tout << mk_bounded_pp(p.first->get_owner(), get_manager()) << " " << mk_bounded_pp(p.second->get_owner(), get_manager()) << "\n";
                  });
        }
        return res;
    }

    /**
       \brief Auxiliary method for occurs_check.
       TODO: improve performance.
    */
    bool theory_datatype::occurs_check_core(enode * app) {
        if (app->is_marked())
            return false;
        
        m_stats.m_occurs_check++;
        app->set_mark();
        m_to_unmark.push_back(app);
        
        TRACE("datatype", tout << "occurs check_core: #" << app->get_owner_id() << " #" << m_main->get_owner_id() << "\n";);

        theory_var v = app->get_root()->get_th_var(get_id());
        if (v != null_theory_var) {
            v = m_find.find(v);
            var_data * d = m_var_data[v];
            if (d->m_constructor) {
                if (app != d->m_constructor)
                    m_used_eqs.push_back(enode_pair(app, d->m_constructor));
                unsigned num_args = d->m_constructor->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    enode * arg = d->m_constructor->get_arg(i);
                    if (arg->get_root() == m_main->get_root()) {
                        if (arg != m_main)
                            m_used_eqs.push_back(enode_pair(arg, m_main));
                        return true;
                    }
                    if (m_util.is_datatype(get_manager().get_sort(arg->get_owner())) && occurs_check_core(arg))
                        return true;
                }
                if (app != d->m_constructor) {
                    SASSERT(m_used_eqs.back().first  == app);
                    SASSERT(m_used_eqs.back().second == d->m_constructor);
                    m_used_eqs.pop_back();
                }
            }
        }
        return false;
    }
        
    void theory_datatype::reset_eh() {
        m_trail_stack.reset();
        std::for_each(m_var_data.begin(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.reset();
        theory::reset_eh();
        m_util.reset();
        m_stats.reset();
    }

    bool theory_datatype::is_shared(theory_var v) const {
        // In principle, parametric theories such as Array Theory and
        // Datatype Theory need to implement this method. However, the datatype theory
        // propagates all implied equalities. And, the is_shared method is essentially used
        // to create interface equalities. So, it is safe to return false.
        return false;
    }

    theory_datatype::theory_datatype(ast_manager & m, theory_datatype_params & p):
        theory(m.mk_family_id("datatype")),
        m_params(p),
        m_util(m),
        m_find(*this),
        m_trail_stack(*this) {
    }

    theory_datatype::~theory_datatype() {
        std::for_each(m_var_data.begin(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.reset();
    }

    void theory_datatype::display(std::ostream & out) const {
        out << "Theory datatype:\n";
        unsigned num_vars = get_num_vars();
        for (unsigned v = 0; v < num_vars; v++) 
            display_var(out, v);
    }

    void theory_datatype::collect_statistics(::statistics & st) const {
        st.update("datatype occurs check", m_stats.m_occurs_check);
        st.update("datatype splits", m_stats.m_splits);
        st.update("datatype constructor ax", m_stats.m_assert_cnstr);
        st.update("datatype accessor ax", m_stats.m_assert_accessor);
        st.update("datatype update ax", m_stats.m_assert_update_field);
    }
    
    void theory_datatype::display_var(std::ostream & out, theory_var v) const {
        var_data * d = m_var_data[v];
        out << "v" << v << " #" << get_enode(v)->get_owner_id() << " -> v" << m_find.find(v) << " ";
        if (d->m_constructor)
            out << mk_bounded_pp(d->m_constructor->get_owner(), get_manager());
        else
            out << "(null)";
        out << "\n";
    }

    void theory_datatype::init_model(model_generator & m) {
        m_factory = alloc(datatype_factory, get_manager(), m.get_model());
        m.register_factory(m_factory);
    }

    class datatype_value_proc : public model_value_proc {
        func_decl *                     m_constructor;
        svector<model_value_dependency> m_dependencies;
    public:
        datatype_value_proc(func_decl * d):m_constructor(d) {}
        void add_dependency(enode * n) { m_dependencies.push_back(model_value_dependency(n)); }
        virtual ~datatype_value_proc() {}
        virtual void get_dependencies(buffer<model_value_dependency> & result) {
            result.append(m_dependencies.size(), m_dependencies.c_ptr());
        }
        virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values) {
            SASSERT(values.size() == m_dependencies.size());
            return mg.get_manager().mk_app(m_constructor, values.size(), values.c_ptr());
        }
    };

    model_value_proc * theory_datatype::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        v            = m_find.find(v);
        SASSERT(v != null_theory_var);
        var_data * d = m_var_data[v];
        SASSERT(d->m_constructor);
        func_decl * c_decl = d->m_constructor->get_decl();
        datatype_value_proc * result = alloc(datatype_value_proc, c_decl);
        unsigned num = d->m_constructor->get_num_args();
        for (unsigned i = 0; i < num; i++) 
            result->add_dependency(d->m_constructor->get_arg(i));
        return result;
    }

    void theory_datatype::merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) {
        // v1 is the new root
        TRACE("datatype", tout << "merging v" << v1 << " v" << v2 << "\n";);
        SASSERT(v1 == static_cast<int>(m_find.find(v1)));
        var_data * d1 = m_var_data[v1];
        var_data * d2 = m_var_data[v2];
        if (d2->m_constructor != 0) {
            context & ctx = get_context();
            if (d1->m_constructor != 0 && d1->m_constructor->get_decl() != d2->m_constructor->get_decl()) {
                region & r    = ctx.get_region();
                enode_pair p(d1->m_constructor, d2->m_constructor);
                SASSERT(d1->m_constructor->get_root() == d2->m_constructor->get_root());
                ctx.set_conflict(ctx.mk_justification(ext_theory_conflict_justification(get_id(), r, 0, 0, 1, &p)));
            }
            if (d1->m_constructor == 0) {
                m_trail_stack.push(set_ptr_trail<theory_datatype, enode>(d1->m_constructor)); 
                // check whether there is a recognizer in d1 that conflicts with d2->m_constructor;
                if (!d1->m_recognizers.empty()) {
                    unsigned c_idx = m_util.get_constructor_idx(d2->m_constructor->get_decl());
                    enode * recognizer = d1->m_recognizers[c_idx];
                    if (recognizer != 0 && ctx.get_assignment(recognizer) == l_false) {
                        sign_recognizer_conflict(d2->m_constructor, recognizer);
                        return;
                    }
                }
                d1->m_constructor = d2->m_constructor;
            }
        }
        ptr_vector<enode>::iterator it   = d2->m_recognizers.begin();
        ptr_vector<enode>::iterator end  = d2->m_recognizers.end();
        for (; it != end; ++it) 
            if (*it)
                add_recognizer(v1, *it);
    }

    void theory_datatype::unmerge_eh(theory_var v1, theory_var v2) {
        // do nothing
    }

    void theory_datatype::add_recognizer(theory_var v, enode * recognizer) {
        SASSERT(is_recognizer(recognizer));
        context & ctx = get_context();
        v = m_find.find(v);
        var_data * d = m_var_data[v];
        sort * s     = recognizer->get_decl()->get_domain(0);
        if (d->m_recognizers.empty()) {
            SASSERT(m_util.is_datatype(s));
            d->m_recognizers.resize(m_util.get_datatype_num_constructors(s), 0);
        }
        SASSERT(d->m_recognizers.size() == m_util.get_datatype_num_constructors(s));
        unsigned c_idx = m_util.get_recognizer_constructor_idx(recognizer->get_decl());
        if (d->m_recognizers[c_idx] == 0) {
            lbool val = ctx.get_assignment(recognizer);
            TRACE("datatype", tout << "adding recognizer to v" << v << " rec: #" << recognizer->get_owner_id() << " val: " << val << "\n";);
            if (val == l_true) {
                // do nothing... 
                // If recognizer assignment was already processed, then
                // d->m_constructor is already set.
                // Otherwise, it will be set when assign_eh is invoked.
                return; 
            }
            if (val == l_false && d->m_constructor != 0) {
                func_decl * c_decl = m_util.get_recognizer_constructor(recognizer->get_decl());
                if (d->m_constructor->get_decl() == c_decl) {
                    // conflict
                    sign_recognizer_conflict(d->m_constructor, recognizer);
                }
                return;
            }
            SASSERT(val == l_undef || (val == l_false && d->m_constructor == 0));
            d->m_recognizers[c_idx] = recognizer;
            m_trail_stack.push(set_vector_idx_trail<theory_datatype, enode>(d->m_recognizers, c_idx));
            if (val == l_false) {
                propagate_recognizer(v, recognizer);
            }
        }
    }

    /**
       \brief Propagate a recognizer assigned to false.
    */
    void theory_datatype::propagate_recognizer(theory_var v, enode * recognizer) {
        SASSERT(is_recognizer(recognizer));
        SASSERT(static_cast<int>(m_find.find(v)) == v);
        context & ctx = get_context();
        SASSERT(ctx.get_assignment(recognizer) == l_false);
        unsigned num_unassigned  = 0;
        unsigned unassigned_idx  = UINT_MAX;
        enode * n       = get_enode(v);
        sort * dt       = get_manager().get_sort(n->get_owner());
        var_data * d    = m_var_data[v];
        CTRACE("datatype", d->m_recognizers.empty(), ctx.display(tout););
        SASSERT(!d->m_recognizers.empty());
        literal_vector lits;
        svector<enode_pair> eqs;
        ptr_vector<enode>::const_iterator it  = d->m_recognizers.begin();
        ptr_vector<enode>::const_iterator end = d->m_recognizers.end();
        for (unsigned idx = 0; it != end; ++it, ++idx) {
            enode * r = *it;
            if (r && ctx.get_assignment(r) == l_true)
                return; // nothing to be propagated
            if (r && ctx.get_assignment(r) == l_false) {
                SASSERT(r->get_num_args() == 1);
                lits.push_back(literal(ctx.enode2bool_var(r), true));
                if (n != r->get_arg(0)) {
                    // Argument of the current recognizer is not necessarily equal to n.
                    // This can happen when n and r->get_arg(0) are in the same equivalence class.
                    // We must add equality as an assumption to the conflict or propagation
                    SASSERT(n->get_root() == r->get_arg(0)->get_root());
                    eqs.push_back(enode_pair(n, r->get_arg(0)));
                }
                continue;
            }
            if (num_unassigned == 0)
                unassigned_idx = idx;
            num_unassigned++;
        }
        if (num_unassigned == 0) {
            // conflict
            SASSERT(!lits.empty());
            region & reg = ctx.get_region();
            TRACE("datatype_conflict", tout << mk_ismt2_pp(recognizer->get_owner(), get_manager()) << "\n";
                  for (unsigned i = 0; i < lits.size(); i++) {
                      ctx.display_detailed_literal(tout, lits[i]); tout << "\n";
                  }
                  for (unsigned i = 0; i < eqs.size(); i++) {
                      tout << mk_ismt2_pp(eqs[i].first->get_owner(), get_manager()) << " = " << mk_ismt2_pp(eqs[i].second->get_owner(), get_manager()) << "\n";
                  });
            ctx.set_conflict(ctx.mk_justification(ext_theory_conflict_justification(get_id(), reg, lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr())));
        }
        else if (num_unassigned == 1) {
            // propagate remaining recognizer
            SASSERT(!lits.empty());
            enode * r = d->m_recognizers[unassigned_idx];
            literal consequent;
            if (!r) {
                ptr_vector<func_decl> const * constructors = m_util.get_datatype_constructors(dt);
                func_decl * rec = m_util.get_constructor_recognizer(constructors->get(unassigned_idx));
                app * rec_app   = get_manager().mk_app(rec, n->get_owner());
                ctx.internalize(rec_app, false);
                consequent = literal(ctx.get_bool_var(rec_app));
            }
            else {
                consequent = literal(ctx.enode2bool_var(r));
            }
            ctx.mark_as_relevant(consequent);
            region & reg = ctx.get_region();
            ctx.assign(consequent, 
                       ctx.mk_justification(ext_theory_propagation_justification(get_id(), reg, lits.size(), lits.c_ptr(), 
                                                                                 eqs.size(), eqs.c_ptr(), consequent)));
        }
        else {
            // there are more than 2 unassigned recognizers...
            // if eager splits are enabled... create new case split
            if (m_params.m_dt_lazy_splits == 0 || (!dt->is_infinite() && m_params.m_dt_lazy_splits == 1))
                mk_split(v);
        }
    }

    /**
       \brief Create a new case split for v. That is, create the atom (is_mk v) and mark it as relevant.
       If first is true, it means that v does not have recognizer yet.
    */
    void theory_datatype::mk_split(theory_var v) {
        context & ctx         = get_context();
        ast_manager & m       = get_manager();
        v                     = m_find.find(v);
        enode * n             = get_enode(v);
        sort * s              = m.get_sort(n->get_owner());
        func_decl * non_rec_c = m_util.get_non_rec_constructor(s); 
        TRACE("datatype_bug", tout << "non_rec_c: " << non_rec_c->get_name() << "\n";);
        unsigned non_rec_idx  = m_util.get_constructor_idx(non_rec_c);
        var_data * d          = m_var_data[v];
        SASSERT(d->m_constructor == 0);
        func_decl * r         = 0;
        m_stats.m_splits++;

        if (d->m_recognizers.empty()) {
            r = m_util.get_constructor_recognizer(non_rec_c);
        }
        else {
            enode * recognizer    = d->m_recognizers[non_rec_idx];
            if (recognizer == 0) {
                r = m_util.get_constructor_recognizer(non_rec_c);
            }
            else if (!ctx.is_relevant(recognizer)) {
                ctx.mark_as_relevant(recognizer);
                return;
            }
            else if (ctx.get_assignment(recognizer) != l_false) {
                // if is l_true, then we are done
                // otherwise wait recognizer to be assigned.
                return;
            }
            else {
                // look for a slot of d->m_recognizers that is 0, or it is not marked as relevant and is unassigned.
                ptr_vector<enode>::const_iterator it  = d->m_recognizers.begin();
                ptr_vector<enode>::const_iterator end = d->m_recognizers.end();
                for (unsigned idx = 0; it != end; ++it, ++idx) {
                    enode * curr = *it;
                    if (curr == 0) {
                        ptr_vector<func_decl> const * constructors = m_util.get_datatype_constructors(s);
                        // found empty slot...
                        r = m_util.get_constructor_recognizer(constructors->get(idx));
                        break;
                    }
                    else if (!ctx.is_relevant(curr)) { 
                        ctx.mark_as_relevant(curr);
                        return;
                    }
                    else if (ctx.get_assignment(curr) != l_false) {
                        return;
                    }
                }
                if (r == 0)
                    return; // all recognizers are asserted to false... conflict will be detected...
            }
        }
        SASSERT(r != 0);
        app * r_app     = m.mk_app(r, n->get_owner());
        TRACE("datatype", tout << "creating split: " << mk_bounded_pp(r_app, m) << "\n";);
        ctx.internalize(r_app, false);
        bool_var bv     = ctx.get_bool_var(r_app);
        ctx.set_true_first_flag(bv);
        ctx.mark_as_relevant(bv);
    }

};
