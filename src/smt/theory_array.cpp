/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-01.

Revision History:

--*/
#include"smt_context.h"
#include"theory_array.h"
#include"ast_ll_pp.h"
#include"stats.h"

namespace smt {

    theory_array::theory_array(ast_manager & m, theory_array_params & params):
        theory_array_base(m), 
        m_params(params),
        m_find(*this),
        m_trail_stack(*this),
        m_final_check_idx(0) {
    }

    theory_array::~theory_array() {
        std::for_each(m_var_data.begin(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.reset();
    }

    void theory_array::init(context * ctx) {
        theory_array_base::init(ctx);
        if (!ctx->relevancy())
            m_params.m_array_laziness = 0;
    }

    void theory_array::merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) {
        // v1 is the new root
        TRACE("array", tout << "merging v" << v1 << " v" << v2 << "\n"; display_var(tout, v1););
        SASSERT(v1 == find(v1));
        var_data * d1 = m_var_data[v1];
        var_data * d2 = m_var_data[v2];
        if (!d1->m_prop_upward && d2->m_prop_upward)
            set_prop_upward(v1);
        ptr_vector<enode>::iterator it   = d2->m_stores.begin();
        ptr_vector<enode>::iterator end  = d2->m_stores.end();
        for (; it != end; ++it) 
            add_store(v1, *it);
        it  = d2->m_parent_stores.begin();
        end = d2->m_parent_stores.end();
        for (; it != end; ++it)
            add_parent_store(v1, *it);
        it  = d2->m_parent_selects.begin();
        end = d2->m_parent_selects.end();
        for (; it != end; ++it)
            add_parent_select(v1, *it);
        TRACE("array", tout << "after merge\n"; display_var(tout, v1););
    }

    void theory_array::unmerge_eh(theory_var v1, theory_var v2) {
        // do nothing
    }

    theory_var theory_array::mk_var(enode * n) {
        theory_var r  = theory_array_base::mk_var(n);
        theory_var r2 = m_find.mk_var();
        SASSERT(r == r2);
        SASSERT(r == static_cast<int>(m_var_data.size()));
        m_var_data.push_back(alloc(var_data));
        var_data * d  = m_var_data[r];
        TRACE("array", tout << mk_bounded_pp(n->get_owner(), get_manager()) << "\nis_array: " << is_array_sort(n) << ", is_select: " << is_select(n) <<
              ", is_store: " << is_store(n) << "\n";);
        d->m_is_array  = is_array_sort(n);
        if (d->m_is_array) 
            register_sort(get_manager().get_sort(n->get_owner()));
        d->m_is_select = is_select(n);
        if (is_store(n))
            d->m_stores.push_back(n);
        get_context().attach_th_var(n, this, r);
        if (m_params.m_array_laziness <= 1 && is_store(n))
            instantiate_axiom1(n);
        return r;
    }
    
    void theory_array::add_parent_select(theory_var v, enode * s) {
        if (m_params.m_array_cg && !s->is_cgr())
            return;
        SASSERT(is_select(s));
        v                = find(v);
        var_data * d     = m_var_data[v];
        d->m_parent_selects.push_back(s);
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(d->m_parent_selects));
        ptr_vector<enode>::iterator it  = d->m_stores.begin();
        ptr_vector<enode>::iterator end = d->m_stores.end();
        for (; it != end; ++it) {
            instantiate_axiom2a(s, *it);
        }
        if (!m_params.m_array_weak && !m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            it  = d->m_parent_stores.begin();
            end = d->m_parent_stores.end();
            for (; it != end; ++it) {
                enode * store = *it;
                SASSERT(is_store(store));
                if (!m_params.m_array_cg || store->is_cgr())
                    instantiate_axiom2b(s, store);
            }
        }
    }

    void theory_array::add_parent_store(theory_var v, enode * s) {
        if (m_params.m_array_cg && !s->is_cgr())
            return;
        SASSERT(is_store(s));
        v                = find(v);
        var_data * d     = m_var_data[v];
        d->m_parent_stores.push_back(s);
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(d->m_parent_stores));
        if (!m_params.m_array_weak && !m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
            ptr_vector<enode>::iterator end = d->m_parent_selects.end();
            for (; it != end; ++it) 
                if (!m_params.m_array_cg || (*it)->is_cgr())
                    instantiate_axiom2b(*it, s);
        }
    }

    bool theory_array::instantiate_axiom2b_for(theory_var v) {
        bool result = false;
        var_data * d = m_var_data[v];
        ptr_vector<enode>::iterator it  = d->m_parent_stores.begin();
        ptr_vector<enode>::iterator end = d->m_parent_stores.end();
        for (; it != end; ++it) {
            ptr_vector<enode>::iterator it2  = d->m_parent_selects.begin();
            ptr_vector<enode>::iterator end2 = d->m_parent_selects.end();
            for (; it2 != end2; ++it2) 
                if (instantiate_axiom2b(*it2, *it))
                    result = true;
        }
        return result;
    }

    /**
       \brief Mark v for upward propagation. That is, enables the propagation of select(v, i) to store(v,j,k).
    */
    void theory_array::set_prop_upward(theory_var v) {
        if (m_params.m_array_weak)
            return;
        v = find(v);
        var_data * d = m_var_data[v];
        if (!d->m_prop_upward) {
            TRACE("array", tout << "#" << v << "\n";);
            m_trail_stack.push(reset_flag_trail<theory_array>(d->m_prop_upward));
            d->m_prop_upward = true;
            if (!m_params.m_array_delay_exp_axiom)
                instantiate_axiom2b_for(v);
            ptr_vector<enode>::iterator it  = d->m_stores.begin();
            ptr_vector<enode>::iterator end = d->m_stores.end();
            for (; it != end; ++it)
                set_prop_upward(*it);
        }
    }

    void theory_array::set_prop_upward(enode * store) {
        if (is_store(store)) {
            theory_var st_v = store->get_arg(0)->get_th_var(get_id());
            set_prop_upward(st_v);
        }
    }

    void theory_array::set_prop_upward(theory_var v, var_data* d) {
        unsigned sz = d->m_stores.size();
        for (unsigned i = 0; i < sz; ++i) {
            set_prop_upward(d->m_stores[i]);
        }
    }


    /**
       \brief Return the size of the equivalence class for array terms 
              that can be expressed as \lambda i : Index . [.. (select a i) ..]
     */
    unsigned theory_array::get_lambda_equiv_size(theory_var v, var_data* d) {
        return d->m_stores.size();
    }

    void theory_array::add_store(theory_var v, enode * s) {
        if (m_params.m_array_cg && !s->is_cgr())
            return;
        SASSERT(is_store(s));
        v                = find(v);
        var_data * d     = m_var_data[v];
        unsigned lambda_equiv_class_size = get_lambda_equiv_size(v, d);
        if (m_params.m_array_always_prop_upward || lambda_equiv_class_size >= 1) {
            set_prop_upward(v, d);
        }
        d->m_stores.push_back(s);
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(d->m_stores));
        ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
        ptr_vector<enode>::iterator end = d->m_parent_selects.end();
        for (; it != end; ++it) {
            SASSERT(is_select(*it));
            instantiate_axiom2a(*it, s);
        }
        if (m_params.m_array_always_prop_upward || lambda_equiv_class_size >= 1) 
            set_prop_upward(s);
    }

    void theory_array::instantiate_axiom1(enode * store) {
        TRACE("array", tout << "axiom 1:\n" << mk_bounded_pp(store->get_owner(), get_manager()) << "\n";);
        SASSERT(is_store(store));
        m_stats.m_num_axiom1++;
        assert_store_axiom1(store);
    }

    void theory_array::instantiate_axiom2a(enode * select, enode * store) {
        TRACE("array", tout << "axiom 2a: #" << select->get_owner_id() << " #" << store->get_owner_id() << "\n";);
        SASSERT(is_select(select));
        SASSERT(is_store(store));
        if (assert_store_axiom2(store, select))
            m_stats.m_num_axiom2a++;
    }

    bool theory_array::instantiate_axiom2b(enode * select, enode * store) {
        TRACE("array_axiom2b", tout << "axiom 2b: #" << select->get_owner_id() << " #" << store->get_owner_id() << "\n";);
        SASSERT(is_select(select));
        SASSERT(is_store(store));
        if (assert_store_axiom2(store, select)) {
            m_stats.m_num_axiom2b++;
            return true;
        }
        return false;
    }

    void theory_array::instantiate_extensionality(enode * a1, enode * a2) {
        TRACE("array", tout << "extensionality: #" << a1->get_owner_id() << " #" << a2->get_owner_id() << "\n";);
        SASSERT(is_array_sort(a1));
        SASSERT(is_array_sort(a2));
        if (m_params.m_array_extensional && assert_extensionality(a1, a2)) 
            m_stats.m_num_extensionality++;
    }

    bool theory_array::internalize_atom(app * atom, bool) {
        return internalize_term(atom);
    }

    //
    // Internalize the term. If it has already been internalized, return false.
    // 
    bool theory_array::internalize_term_core(app * n) {
        TRACE("array_bug", tout << mk_bounded_pp(n, get_manager()) << "\n";);
        context & ctx     = get_context();
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(n->get_arg(i), false);
        if (ctx.e_internalized(n)) {
            return false;
        }
        enode * e        = ctx.mk_enode(n, false, false, true);
        if (!is_attached_to_var(e))
            mk_var(e);

        if (get_manager().is_bool(n)) {
            bool_var bv = ctx.mk_bool_var(n);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        return true;
    }

    bool theory_array::internalize_term(app * n) {
        if (!is_store(n) && !is_select(n)) {
            if (!is_array_ext(n))
                found_unsupported_op(n);
            return false;
        }
        TRACE("array_bug", tout << mk_bounded_pp(n, get_manager()) << "\n";);
        if (!internalize_term_core(n)) {
            return true;
        }
        context & ctx     = get_context();
        enode * arg0      = ctx.get_enode(n->get_arg(0));
        if (!is_attached_to_var(arg0))
            mk_var(arg0);


        if (m_params.m_array_laziness == 0) {
            theory_var v_arg = arg0->get_th_var(get_id());
            
            SASSERT(v_arg != null_theory_var);
            if (is_select(n)) {
                add_parent_select(v_arg, ctx.get_enode(n));
            }
            else if (is_store(n)) {
                add_parent_store(v_arg, ctx.get_enode(n));
            }
        }

        return true;
    }

    void theory_array::apply_sort_cnstr(enode * n, sort * s) {
        SASSERT(is_array_sort(s));
        if (!is_attached_to_var(n))
            mk_var(n);
    }

    void theory_array::new_eq_eh(theory_var v1, theory_var v2) {
        m_find.merge(v1, v2);
    }

    void theory_array::new_diseq_eh(theory_var v1, theory_var v2) {
        v1 = find(v1);
        v2 = find(v2);
        var_data * d1 = m_var_data[v1];
        if (d1->m_is_array) {
            SASSERT(m_var_data[v2]->m_is_array);
            TRACE("ext", tout << "extensionality:\n" << mk_bounded_pp(get_enode(v1)->get_owner(), get_manager(), 5) << "\n" << 
                  mk_bounded_pp(get_enode(v2)->get_owner(), get_manager(), 5) << "\n";);
            instantiate_extensionality(get_enode(v1), get_enode(v2));
        }
    }

    void theory_array::relevant_eh(app * n) {
        if (m_params.m_array_laziness == 0)
            return;
        if (!is_store(n) && !is_select(n))
            return;
        context & ctx    = get_context();
        enode * arg      = ctx.get_enode(n->get_arg(0));
        theory_var v_arg = arg->get_th_var(get_id());
        SASSERT(v_arg != null_theory_var);
        if (is_select(n)) {
            add_parent_select(v_arg, ctx.get_enode(n));
        }
        else {
            SASSERT(is_store(n));
            if (m_params.m_array_laziness > 1)
                instantiate_axiom1(ctx.get_enode(n));
            add_parent_store(v_arg, ctx.get_enode(n));
        }
    }
     
    void theory_array::push_scope_eh() {
        theory_array_base::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_array::pop_scope_eh(unsigned num_scopes) {
        m_trail_stack.pop_scope(num_scopes);
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        std::for_each(m_var_data.begin() + num_old_vars, m_var_data.end(), delete_proc<var_data>());
        m_var_data.shrink(num_old_vars);
        theory_array_base::pop_scope_eh(num_scopes);
        SASSERT(m_find.get_num_vars() == m_var_data.size());
        SASSERT(m_find.get_num_vars() == get_num_vars());
    }
    
    final_check_status theory_array::final_check_eh() {
        m_final_check_idx++;
        final_check_status r;
        if (m_params.m_array_lazy_ieq) {
            // Delay the creation of interface equalities...  The
            // motivation is too give other theories and quantifier
            // instantiation to do something useful during final
            // check.
            if (m_final_check_idx % m_params.m_array_lazy_ieq_delay != 0) {
                assert_delayed_axioms();
                r = FC_CONTINUE;
            }
            else {
                if (mk_interface_eqs_at_final_check() == FC_CONTINUE)
                    r = FC_CONTINUE;
                else 
                    r = assert_delayed_axioms();
            }
        }
        else {
            if (m_final_check_idx % 2 == 1) {
                if (assert_delayed_axioms() == FC_CONTINUE)
                    r = FC_CONTINUE;
                else 
                    r = mk_interface_eqs_at_final_check();
            }
            else {
                if (mk_interface_eqs_at_final_check() == FC_CONTINUE)
                    r = FC_CONTINUE;
                else
                    r = assert_delayed_axioms();
            }
        }
        TRACE("as_array", tout << "m_found_unsupported_op: " << m_found_unsupported_op << " " << r << "\n";);
        if (r == FC_DONE && m_found_unsupported_op) 
            r = FC_GIVEUP;
        return r;
    }

    final_check_status theory_array::assert_delayed_axioms() {
        if (!m_params.m_array_delay_exp_axiom)
            return FC_DONE;
        final_check_status r = FC_DONE;
        unsigned num_vars = get_num_vars();
        for (unsigned v = 0; v < num_vars; v++) {
            var_data * d = m_var_data[v];
            if (d->m_prop_upward && instantiate_axiom2b_for(v))
                r = FC_CONTINUE;
        }
        return r;
    }

    final_check_status theory_array::mk_interface_eqs_at_final_check() {
        unsigned n = mk_interface_eqs();
        m_stats.m_num_eq_splits += n;
        if (n > 0)
            return FC_CONTINUE;
        return FC_DONE;
    }

    void theory_array::reset_eh() {
        m_trail_stack.reset();
        std::for_each(m_var_data.begin(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.reset();
        theory_array_base::reset_eh();
    }

    void theory_array::display(std::ostream & out) const {
        unsigned num_vars = get_num_vars();
        if (num_vars == 0) return;
        out << "Theory array:\n";
        for (unsigned v = 0; v < num_vars; v++) {
            display_var(out, v);
        }
    }

    // TODO: move to another file
    void theory_array::display_ids(std::ostream & out, unsigned n, enode * const * v) {
        for (unsigned i = 0; i < n; i++) {
            if (i > 0) out << " ";
            out << "#" << v[i]->get_owner_id();
        }
    }

    void theory_array::display_var(std::ostream & out, theory_var v) const {
        var_data const * d = m_var_data[v];
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " #";
        out.width(4);
        out << get_enode(v)->get_owner_id() << " -> #";
        out.width(4);
        out << get_enode(find(v))->get_owner_id();
        out << std::right;
        out << " is_array: " << d->m_is_array  << " is_select: " << d->m_is_select << " upward: " << d->m_prop_upward;
        out << " stores: {";
        display_ids(out, d->m_stores.size(), d->m_stores.c_ptr());
        out << "} p_stores: {";
        display_ids(out, d->m_parent_stores.size(), d->m_parent_stores.c_ptr());
        out << "} p_selects: {";
        display_ids(out, d->m_parent_selects.size(), d->m_parent_selects.c_ptr());
        out << "}";
        out << "\n";
     }

    void theory_array::collect_statistics(::statistics & st) const {
        st.update("array ax1", m_stats.m_num_axiom1);
        st.update("array ax2", m_stats.m_num_axiom2a);
        st.update("array exp ax2", m_stats.m_num_axiom2b);
        st.update("array ext ax", m_stats.m_num_extensionality);
        st.update("array splits", m_stats.m_num_eq_splits);
    }

};
