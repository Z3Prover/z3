/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_full.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner 2008-22-10

Revision History:

--*/

#include "smt_context.h"
#include "theory_array_full.h"
#include "ast_ll_pp.h"
#include "ast_pp.h"
#include "ast_smt2_pp.h"
#include "stats.h"

namespace smt {

    theory_array_full::theory_array_full(ast_manager & m, theory_array_params & params) : 
        theory_array(m, params),
        m_sort2epsilon(m) {}

    theory_array_full::~theory_array_full() {
        std::for_each(m_var_data_full.begin(), m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.reset();
    }

    theory* theory_array_full::mk_fresh(context* new_ctx) { 
        return alloc(theory_array_full, new_ctx->get_manager(), m_params); 
    }

    void theory_array_full::add_map(theory_var v, enode* s) {
        if (m_params.m_array_cg && !s->is_cgr()) {
            return;
        }
        SASSERT(is_map(s));
        v                = find(v);
        var_data_full * d_full = m_var_data_full[v];
        var_data *     d     = m_var_data[v];
        //
        // TODO: defaulting to exhaustive up-propagation.
        //       instead apply stratified filter.
        set_prop_upward(v,d);
        d_full->m_maps.push_back(s);
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(d_full->m_maps));
        ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
        ptr_vector<enode>::iterator end = d->m_parent_selects.end();
        for (; it != end; ++it) {
            SASSERT(is_select(*it));
            instantiate_select_map_axiom(*it, s);
        }
        set_prop_upward(s);
    }

    bool theory_array_full::instantiate_axiom_map_for(theory_var v) {
        bool result = false;
        var_data * d = m_var_data[v];
        var_data_full * d_full = m_var_data_full[v];
        unsigned num_maps = d_full->m_parent_maps.size();
        unsigned num_selects = d->m_parent_selects.size();
        for (unsigned i = 0; i < num_maps; ++i) {
            for (unsigned j = 0; j < num_selects; ++j) {
                if (instantiate_select_map_axiom(d->m_parent_selects[j], d_full->m_parent_maps[i])) {
                    result = true;
                }
            }
        }
        return result;
    }

    void theory_array_full::add_parent_map(theory_var v, enode* s) {
        if (m_params.m_array_cg && !s->is_cgr()) {
            return;
        }
        SASSERT(v != null_theory_var);
        SASSERT(is_map(s));
        v                = find(v);
        var_data * d     = m_var_data[v];
        var_data_full * d_full     = m_var_data_full[v];
        d_full->m_parent_maps.push_back(s);
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(d_full->m_parent_maps));
        if (!m_params.m_array_weak && !m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
            ptr_vector<enode>::iterator end = d->m_parent_selects.end();
            for (; it != end; ++it) {
                if (!m_params.m_array_cg || (*it)->is_cgr()) {
                    instantiate_select_map_axiom(*it, s);
                }                
            }
        }
    }

    //
    // set set_prop_upward on root and recursively on children if necessary.
    // 
    void theory_array_full::set_prop_upward(theory_var v) {
        if (m_params.m_array_weak)
            return;
        v = find(v);
        var_data * d = m_var_data[v];
        if (!d->m_prop_upward) {
            m_trail_stack.push(reset_flag_trail<theory_array>(d->m_prop_upward));
            d->m_prop_upward = true;
            TRACE("array", tout << "#" << v << "\n";);
            if (!m_params.m_array_delay_exp_axiom) {
                instantiate_axiom2b_for(v);
                instantiate_axiom_map_for(v);
            }
            var_data_full * d2 = m_var_data_full[v];
            ptr_vector<enode>::iterator it  = d->m_stores.begin();
            ptr_vector<enode>::iterator end = d->m_stores.end();
            for (; it != end; ++it) {
                set_prop_upward(*it);
            }
            it   = d2->m_maps.begin();
            end  = d2->m_maps.end();
            for (; it != end; ++it) {
                set_prop_upward(*it);
            }
            it   = d2->m_consts.begin();
            end  = d2->m_consts.end();
            for (; it != end; ++it) {
                set_prop_upward(*it);
            }
        }        
    }

    //
    // call set_prop_upward on array arguments.
    // 
    void theory_array_full::set_prop_upward(enode * n) {
        TRACE("array", tout << mk_pp(n->get_owner(), get_manager()) << "\n";);
        if (is_store(n)) {
            set_prop_upward(n->get_arg(0)->get_th_var(get_id()));
        }
        else if (is_map(n)) {
            for (unsigned i = 0; i < n->get_num_args(); ++i) {
                set_prop_upward(n->get_arg(i)->get_th_var(get_id()));
            }
        }
    }

    void theory_array_full::set_prop_upward(theory_var v, var_data* d) {
        if (m_params.m_array_always_prop_upward || d->m_stores.size() >= 1) {
            theory_array::set_prop_upward(v, d);
        }
        else {
            var_data_full * d2 = m_var_data_full[v];
            unsigned sz = d2->m_maps.size();
            for(unsigned i = 0; i < sz; ++i) {
                set_prop_upward(d2->m_maps[i]);
            }
        }
    }


    unsigned theory_array_full::get_lambda_equiv_size(theory_var v, var_data* d) {
        var_data_full * d2 = m_var_data_full[v];        
        return d->m_stores.size() + 2*d2->m_consts.size() + 2*d2->m_maps.size();
    }

    void theory_array_full::add_const(theory_var v, enode* cnst) {
        var_data * d  = m_var_data[v];
        unsigned lambda_equiv_class_size = get_lambda_equiv_size(v, d);
        if (m_params.m_array_always_prop_upward || lambda_equiv_class_size >= 1) {
            set_prop_upward(v, d);
        }
        ptr_vector<enode> & consts = m_var_data_full[v]->m_consts;
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(consts));
        consts.push_back(cnst);
        instantiate_default_const_axiom(cnst);

        ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
        ptr_vector<enode>::iterator end = d->m_parent_selects.end();
        for (; it != end; ++it) {
            SASSERT(is_select(*it));
            instantiate_select_const_axiom(*it, cnst);
        }
    }

    void theory_array_full::add_as_array(theory_var v, enode* arr) {
        var_data * d  = m_var_data[v];
        unsigned lambda_equiv_class_size = get_lambda_equiv_size(v, d);
        if (m_params.m_array_always_prop_upward || lambda_equiv_class_size >= 1) {
            set_prop_upward(v, d);
        }
        ptr_vector<enode> & as_arrays = m_var_data_full[v]->m_as_arrays;
        m_trail_stack.push(push_back_trail<theory_array, enode *, false>(as_arrays));
        as_arrays.push_back(arr);
        instantiate_default_as_array_axiom(arr);

        ptr_vector<enode>::iterator it  = d->m_parent_selects.begin();
        ptr_vector<enode>::iterator end = d->m_parent_selects.end();
        for (; it != end; ++it) {
            SASSERT(is_select(*it));
            instantiate_select_as_array_axiom(*it, arr);
        }
    }


    void theory_array_full::reset_eh() {
        theory_array::reset_eh();
        std::for_each(m_var_data_full.begin(), m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.reset();
        m_eqs.reset();
        m_eqsv.reset();
    }

    void theory_array_full::display_var(std::ostream & out, theory_var v) const {
        theory_array::display_var(out, v);
        var_data_full const * d = m_var_data_full[v];
        out << " maps: {";
        display_ids(out, d->m_maps.size(), d->m_maps.c_ptr());
        out << "} p_parent_maps: {";
        display_ids(out, d->m_parent_maps.size(), d->m_parent_maps.c_ptr());
        out << "} p_const: {";
        display_ids(out, d->m_consts.size(), d->m_consts.c_ptr());
        out << "}\n";
    }
    
    theory_var theory_array_full::mk_var(enode * n) {
        theory_var r = theory_array::mk_var(n);
        SASSERT(r == static_cast<int>(m_var_data_full.size()));
        m_var_data_full.push_back(alloc(var_data_full));
        var_data_full * d = m_var_data_full.back();
        if (is_map(n)) {
            instantiate_default_map_axiom(n);
            d->m_maps.push_back(n);
        }
        else if (is_const(n)) {
            instantiate_default_const_axiom(n);
            d->m_consts.push_back(n);
        }
        else if (is_default(n)) {
            // no-op
        }
        else if (is_as_array(n)) {
            instantiate_default_as_array_axiom(n);
            d->m_as_arrays.push_back(n);
        }
        return r;
    }

    bool theory_array_full::internalize_atom(app * atom, bool) {
        return internalize_term(atom);
    }

    bool theory_array_full::internalize_term(app * n) {
        TRACE("array", tout << mk_pp(n, get_manager()) << "\n";);

        if (is_store(n) || is_select(n)) {
            return theory_array::internalize_term(n);
        }

        if (!is_const(n) && !is_default(n)  && !is_map(n) && !is_as_array(n)) {
            if (!is_array_ext(n))
                found_unsupported_op(n);
            return false;
        }

        if (!internalize_term_core(n)) {
            return true;
        }
        context & ctx = get_context();

        if (is_map(n) || is_array_ext(n)) {
            for (unsigned i = 0; i < n->get_num_args(); ++i) {
                enode* arg = ctx.get_enode(n->get_arg(i));
                if (!is_attached_to_var(arg)) {
                    mk_var(arg);
                }
            }
        }
        else if (is_default(n)) {
            enode* arg0 = ctx.get_enode(n->get_arg(0));
            if (!is_attached_to_var(arg0)) {
                mk_var(arg0);
            }
        }

        enode* node = ctx.get_enode(n);
        if (!is_attached_to_var(node)) {
            mk_var(node);
        }

        if (is_default(n)) {
            enode* arg0 = ctx.get_enode(n->get_arg(0));
            theory_var v_arg = arg0->get_th_var(get_id());
            add_parent_default(v_arg);
        }
        else if (is_map(n)) {
            for (unsigned i = 0; i < n->get_num_args(); ++i) {
                enode* arg = ctx.get_enode(n->get_arg(i));
                theory_var v_arg = arg->get_th_var(get_id());
                add_parent_map(v_arg, node);
            }
            instantiate_default_map_axiom(node);
        }
        else if (is_const(n)) {
            instantiate_default_const_axiom(node);
        }           
        else if (is_as_array(n)) {
            // The array theory is not a decision procedure
            // for as-array. 
            // Ex: (as-array f) = (as-array g) & f(0) = 0 & g(0) = 1
            // There is nothing to propagate the disequality.
            // Even if there was, as-array on interpreted 
            // functions will be incomplete.
            // The instantiation operations are still sound to include.
            found_unsupported_op(n);
            instantiate_default_as_array_axiom(node);
        }
        else if (is_array_ext(n)) {
            SASSERT(n->get_num_args() == 2);
            instantiate_extensionality(ctx.get_enode(n->get_arg(0)), ctx.get_enode(n->get_arg(1)));
        }
        return true;
    }


    void theory_array_full::merge_eh(theory_var v1, theory_var v2, theory_var u, theory_var w) {
        theory_array::merge_eh(v1, v2, u, w);
        // v1 is the new root
        SASSERT(v1 == find(v1));
        var_data_full * d2 = m_var_data_full[v2];
        ptr_vector<enode>::iterator it, end;

        it   = d2->m_maps.begin();
        end  = d2->m_maps.end();
        for (; it != end; ++it) {
            add_map(v1, *it);
        }
        it  = d2->m_parent_maps.begin();
        end = d2->m_parent_maps.end();
        for (; it != end; ++it) {
            add_parent_map(v1, *it);
        }
        it = d2->m_consts.begin();
        end = d2->m_consts.end();
        for (; it != end; ++it) {
            add_const(v1, *it);
        }
        it = d2->m_as_arrays.begin();
        end = d2->m_as_arrays.end();
        for (; it != end; ++it) {
            add_as_array(v1, *it);
        }
        TRACE("array", 
              tout << mk_pp(get_enode(v1)->get_owner(), get_manager()) << "\n";
              tout << mk_pp(get_enode(v2)->get_owner(), get_manager()) << "\n";
              tout << "merge in\n"; display_var(tout, v2);
              tout << "after merge\n"; display_var(tout, v1););
    }

    void theory_array_full::add_parent_default(theory_var v) {
        SASSERT(v != null_theory_var);
        v = find(v);
        var_data* d = m_var_data[v];
        ptr_vector<enode>::iterator it, end;

        it  = d->m_stores.begin();
        end = d->m_stores.end();
        for(; it != end; ++it) {
            enode * store = *it;
            SASSERT(is_store(store));
            instantiate_default_store_axiom(store);
        }        

        if (!m_params.m_array_weak && !m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            it  = d->m_parent_stores.begin();
            end = d->m_parent_stores.end();
            for (; it != end; ++it) {
                enode* store = *it;
                SASSERT(is_store(store));
                if (!m_params.m_array_cg || store->is_cgr()) {
                    instantiate_default_store_axiom(store);
                }
            }
        }
    }

    void theory_array_full::add_parent_select(theory_var v, enode * s) {
        TRACE("array", 
              tout << v << " select parent: " << mk_pp(s->get_owner(), get_manager()) << "\n";
              display_var(tout, v);
              );
        theory_array::add_parent_select(v,s);
        v = find(v);
        var_data_full* d_full = m_var_data_full[v];
        var_data* d = m_var_data[v];
        ptr_vector<enode>::iterator it  = d_full->m_consts.begin();
        ptr_vector<enode>::iterator end = d_full->m_consts.end();
        for (; it != end; ++it) {
            instantiate_select_const_axiom(s, *it);
        }
        it  = d_full->m_maps.begin();
        end = d_full->m_maps.end();
        for (; it != end; ++it) {
            enode* map = *it;
            SASSERT(is_map(map));
            instantiate_select_map_axiom(s, map);
        }
        if (!m_params.m_array_weak && !m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            it  = d_full->m_parent_maps.begin();
            end = d_full->m_parent_maps.end();
            for (; it != end; ++it) {
                enode* map = *it;
                SASSERT(is_map(map));
                if (!m_params.m_array_cg || map->is_cgr()) {
                    instantiate_select_map_axiom(s, map);
                }
            }
        }
    }
    
    void theory_array_full::relevant_eh(app* n) {
        TRACE("array", tout << mk_pp(n, get_manager()) << "\n";);
        theory_array::relevant_eh(n);
        if (!is_default(n) && !is_select(n) && !is_map(n) && !is_const(n) && !is_as_array(n)) {
            return;
        }
        context & ctx = get_context();
        enode* node = ctx.get_enode(n);

        if (is_select(n)) {
            enode * arg = ctx.get_enode(n->get_arg(0));
            theory_var v = arg->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            add_parent_select(find(v), node);
        }
        else if (is_default(n)) {
            enode * arg = ctx.get_enode(n->get_arg(0));
            theory_var v = arg->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            add_parent_default(find(v));
        }
        else if (is_const(n)) {
            instantiate_default_const_axiom(node);
        }
        else if (is_map(n)) {
            for (unsigned i = 0; i < n->get_num_args(); ++i) {
                enode* arg = ctx.get_enode(n->get_arg(i));
                theory_var v_arg = find(arg->get_th_var(get_id()));
                add_parent_map(v_arg, node);
                set_prop_upward(v_arg);
            }
            instantiate_default_map_axiom(node);
        }
        else if (is_as_array(n)) {
            instantiate_default_as_array_axiom(node);
        }
    }

       
    //
    // Assert axiom: 
    // select(map[f](a, ... d), i) = f(select(a,i),...,select(d,i))
    //  
    bool theory_array_full::instantiate_select_map_axiom(enode* sl, enode* mp) {
        app* map = mp->get_owner();
        app* select = sl->get_owner();
        SASSERT(is_map(map));
        SASSERT(is_select(select));
        SASSERT(map->get_num_args() > 0);
        func_decl* f = to_func_decl(map->get_decl()->get_parameter(0).get_ast());

        context& ctx = get_context();
        ast_manager& m = get_manager();

        TRACE("array_map_bug", tout << "invoked instantiate_select_map_axiom\n";
              tout << sl->get_owner_id() << " " << mp->get_owner_id() << "\n";
              tout << mk_ismt2_pp(sl->get_owner(), m) << "\n" << mk_ismt2_pp(mp->get_owner(), m) << "\n";);

        if (!ctx.add_fingerprint(mp, mp->get_owner_id(), sl->get_num_args() - 1, sl->get_args() + 1)) {
            return false;
        }

        TRACE("array_map_bug", tout << "new axiom\n";);

        m_stats.m_num_map_axiom++;
        TRACE("array", 
              tout << mk_bounded_pp(mp->get_owner(), get_manager()) << "\n";
              tout << mk_bounded_pp(sl->get_owner(), get_manager()) << "\n";);
        unsigned num_args   = select->get_num_args();
        unsigned num_arrays = map->get_num_args();
        ptr_buffer<expr>       args1, args2;
        vector<ptr_vector<expr> > args2l;
        args1.push_back(map);
        for (unsigned j = 0; j < num_arrays; ++j) {
            ptr_vector<expr> arg;
            arg.push_back(map->get_arg(j));
            args2l.push_back(arg);
        }
        for (unsigned i = 1; i < num_args; ++i) {
            expr* arg = select->get_arg(i);
            for (unsigned j = 0; j < num_arrays; ++j) {
                args2l[j].push_back(arg);
            }
            args1.push_back(arg);
        }
        for (unsigned j = 0; j < num_arrays; ++j) {
            expr* sel = mk_select(args2l[j].size(), args2l[j].c_ptr());
            args2.push_back(sel);
        }

        expr_ref sel1(m), sel2(m);
        sel1 = mk_select(args1.size(), args1.c_ptr());
        m_simp->mk_app(f, args2.size(), args2.c_ptr(), sel2);
        ctx.internalize(sel1, false);
        ctx.internalize(sel2, false);
        
        TRACE("array_map_bug",
              tout << "select-map axiom\n" << mk_ismt2_pp(sel1, m) << "\n=\n" << mk_ismt2_pp(sel2,m) << "\n";);

        return try_assign_eq(sel1, sel2);
    }


    //
    //
    // Assert axiom: 
    // default(map[f](a,..,d)) = f(default(a),..,default(d))
    //  

    bool theory_array_full::instantiate_default_map_axiom(enode* mp) {
        SASSERT(is_map(mp));
                
        app* map = mp->get_owner();
        context& ctx = get_context();
        if (!ctx.add_fingerprint(this, 0, 1, &mp)) {
            return false;
        }
        TRACE("array", tout << mk_bounded_pp(map, get_manager()) << "\n";);

        m_stats.m_num_default_map_axiom++;

        func_decl* f = to_func_decl(map->get_decl()->get_parameter(0).get_ast());
        SASSERT(map->get_num_args() == f->get_arity());
        ptr_buffer<expr> args2;
        for (unsigned i = 0; i < map->get_num_args(); ++i) {
            args2.push_back(mk_default(map->get_arg(i)));
        }

        expr* def1 = mk_default(map);
        expr_ref def2(get_manager());
        m_simp->mk_app(f, args2.size(), args2.c_ptr(), def2);
        ctx.internalize(def1, false);
        ctx.internalize(def2, false);
        return try_assign_eq(def1, def2);
    }


    bool theory_array_full::instantiate_default_const_axiom(enode* cnst) {
        context& ctx = get_context();
        if (!ctx.add_fingerprint(this, 0, 1, &cnst)) {
            return false;
        }
        m_stats.m_num_default_const_axiom++;
        SASSERT(is_const(cnst));
        TRACE("array", tout << mk_bounded_pp(cnst->get_owner(), get_manager()) << "\n";);
        expr* val = cnst->get_arg(0)->get_owner();
        expr* def = mk_default(cnst->get_owner());
        ctx.internalize(def, false);
        return try_assign_eq(val, def);
    }

    bool theory_array_full::instantiate_default_as_array_axiom(enode* arr) {
        context& ctx = get_context();
        if (!ctx.add_fingerprint(this, 0, 1, &arr)) {
            return false;
        }
        m_stats.m_num_default_as_array_axiom++;
        SASSERT(is_as_array(arr));
        TRACE("array", tout << mk_bounded_pp(arr->get_owner(), get_manager()) << "\n";);
        expr* def = mk_default(arr->get_owner());
        func_decl * f = array_util(get_manager()).get_as_array_func_decl(arr->get_owner());
        ptr_vector<expr> args;
        for (unsigned i = 0; i < f->get_arity(); ++i) {
            args.push_back(mk_epsilon(f->get_domain(i)));
        }
        expr_ref val(get_manager().mk_app(f, args.size(), args.c_ptr()), get_manager());
        ctx.internalize(def, false);
        ctx.internalize(val.get(), false);
        return try_assign_eq(val.get(), def);
    }

    bool theory_array_full::has_large_domain(app* array_term) {
        SASSERT(is_array_sort(array_term));
        sort* s = get_manager().get_sort(array_term);
        unsigned dim = get_dimension(s);
        parameter const *  params = s->get_info()->get_parameters();
        rational sz(1);
        for (unsigned i = 0; i < dim; ++i) {
            SASSERT(params[i].is_ast());
            sort* d = to_sort(params[i].get_ast());
            if (d->is_infinite() || d->is_very_big()) {
                return true;
            }
            sz *= rational(d->get_num_elements().size(),rational::ui64());
            if (sz >= rational(1 << 20)) {
                return true;
            }
        }
        return false;        
    }

    //
    // Assert axiom:
    // select(const v, i_1, ..., i_n) = v
    //
    bool theory_array_full::instantiate_select_const_axiom(enode* select, enode* cnst) {
        SASSERT(is_const(cnst));
        SASSERT(is_select(select));
        SASSERT(cnst->get_num_args() == 1);
        context& ctx = get_context();
        unsigned num_args = select->get_num_args();
        if (!ctx.add_fingerprint(cnst, cnst->get_owner_id(), select->get_num_args() - 1, select->get_args() + 1)) {
            return false;
        }

        m_stats.m_num_select_const_axiom++;   
        ptr_buffer<expr> sel_args;
        sel_args.push_back(cnst->get_owner());
        for (unsigned short i = 1; i < num_args; ++i) {
            sel_args.push_back(select->get_owner()->get_arg(i));
        }
        expr * sel = mk_select(sel_args.size(), sel_args.c_ptr());
        expr * val = cnst->get_owner()->get_arg(0);
        TRACE("array", tout << "new select-const axiom...\n";
              tout << "const: " << mk_bounded_pp(cnst->get_owner(), get_manager()) << "\n";
              tout << "select: " << mk_bounded_pp(select->get_owner(), get_manager()) << "\n";
              tout << " sel/const: " << mk_bounded_pp(sel, get_manager()) << "\n";
              tout << "value: " << mk_bounded_pp(val, get_manager()) << "\n";
              tout << "#" << sel->get_id() << " = #" << val->get_id() << "\n";
              );
        
        ctx.internalize(sel, false);
        return try_assign_eq(sel,val);
    }


    //
    // Assert axiom:
    // select(as-array f, i_1, ..., i_n) = (f i_1 ... i_n)
    //
    bool theory_array_full::instantiate_select_as_array_axiom(enode* select, enode* arr) {
        SASSERT(is_as_array(arr->get_owner()));
        SASSERT(is_select(select));
        SASSERT(arr->get_num_args() == 0);
        context& ctx = get_context();
        unsigned num_args = select->get_num_args();
        if (!ctx.add_fingerprint(arr, arr->get_owner_id(), select->get_num_args() - 1, select->get_args() + 1)) {
            return false;
        }

        m_stats.m_num_select_as_array_axiom++;   
        ptr_buffer<expr> sel_args;
        sel_args.push_back(arr->get_owner());
        for (unsigned short i = 1; i < num_args; ++i) {
            sel_args.push_back(select->get_owner()->get_arg(i));
        }
        expr * sel = mk_select(sel_args.size(), sel_args.c_ptr());
        func_decl * f = array_util(get_manager()).get_as_array_func_decl(arr->get_owner());
        expr_ref val(get_manager().mk_app(f, sel_args.size()-1, sel_args.c_ptr()+1), get_manager());
        TRACE("array", tout << "new select-as-array axiom...\n";
              tout << "as-array: " << mk_bounded_pp(arr->get_owner(), get_manager()) << "\n";
              tout << "select: " << mk_bounded_pp(select->get_owner(), get_manager()) << "\n";
              tout << " sel/as-array: " << mk_bounded_pp(sel, get_manager()) << "\n";
              tout << "value: " << mk_bounded_pp(val.get(), get_manager()) << "\n";
              tout << "#" << sel->get_id() << " = #" << val->get_id() << "\n";
              );
        
        ctx.internalize(sel, false);
        ctx.internalize(val.get(), false);
        return try_assign_eq(sel,val);
    }

    
    bool theory_array_full::instantiate_default_store_axiom(enode* store) {
        SASSERT(is_store(store));
        SASSERT(store->get_num_args() >= 3);
        app* store_app = store->get_owner();
        context& ctx = get_context();
        ast_manager& m = get_manager();
        if (!ctx.add_fingerprint(this, 0, 1, &store)) {
            return false;
        }

        m_stats.m_num_default_store_axiom++;

        app* def1;
        app* def2;

        TRACE("array", tout << mk_bounded_pp(store_app, m) << "\n";);

        if (has_large_domain(store_app)) {
            def2 = mk_default(store_app->get_arg(0));
        }
        else {
            //
            // let A = store(B, i, v)
            // 
            // Add:
            //   default(A) = ite(epsilon = i, v, default(B))
            // 
            expr_ref_vector eqs(m);
            unsigned num_args = store_app->get_num_args();
            for (unsigned i = 1; i + 1 < num_args; ++i) {
                sort* srt = m.get_sort(store_app->get_arg(i));
                app* ep = mk_epsilon(srt);
                eqs.push_back(m.mk_eq(ep, store_app->get_arg(i)));
            }
            
            expr_ref eq(m);
            simplifier_plugin* p = m_simp->get_plugin(m.get_basic_family_id());
            basic_simplifier_plugin* bp = static_cast<basic_simplifier_plugin*>(p);
            bp->mk_and(eqs.size(), eqs.c_ptr(), eq);
            expr* defA = mk_default(store_app->get_arg(0));
            def2 = m.mk_ite(eq, store_app->get_arg(num_args-1), defA); 
#if 0
            // 
            // add soft constraints to guide model construction so that 
            // epsilon agrees with the else case in the model construction.
            // 
            for (unsigned i = 0; i < eqs.size(); ++i) {
                // assume_diseq(eqs[i]);
            }
#endif 
        }

        def1 = mk_default(store_app);
        ctx.internalize(def1, false);
        ctx.internalize(def2, false);
        return try_assign_eq(def1, def2);
    }

    app* theory_array_full::mk_epsilon(sort* s) {
        app* eps = 0;
        if (m_sort2epsilon.find(s, eps)) {
            return eps;
        }
        eps = get_manager().mk_fresh_const("epsilon", s);
        m_trail_stack.push(
            ast2ast_trail<theory_array, sort, app>(m_sort2epsilon, s, eps));   
        return eps;
    }

    final_check_status theory_array_full::assert_delayed_axioms() {        
        final_check_status r = FC_DONE;
        if (!m_params.m_array_delay_exp_axiom) {
            r = FC_DONE;
        }
        else { 
            r = theory_array::assert_delayed_axioms();
            unsigned num_vars = get_num_vars();
            for (unsigned v = 0; v < num_vars; v++) {
                var_data * d = m_var_data[v];
                if (d->m_prop_upward && instantiate_axiom_map_for(v))
                    r = FC_CONTINUE;
            }
        }
        while (!m_eqsv.empty()) {
            literal eq = m_eqsv.back();
            m_eqsv.pop_back();
            get_context().mark_as_relevant(eq);            
            assert_axiom(eq);
            r = FC_CONTINUE;
        }
        if (r == FC_DONE && m_found_unsupported_op)
            r = FC_GIVEUP;
        return r;
    }


    bool theory_array_full::try_assign_eq(expr* v1, expr* v2) {
        TRACE("array", 
              tout << mk_bounded_pp(v1, get_manager()) << "\n==\n" 
              << mk_bounded_pp(v2, get_manager()) << "\n";);
        
        if (m_eqs.contains(v1, v2)) {
            return false;
        }
        else {
            m_eqs.insert(v1, v2, true);
            literal eq(mk_eq(v1, v2, true));
            get_context().mark_as_relevant(eq);            
            assert_axiom(eq);

            // m_eqsv.push_back(eq);
            return true;
        }
    }

    void theory_array_full::pop_scope_eh(unsigned num_scopes) {
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        theory_array::pop_scope_eh(num_scopes);
        std::for_each(m_var_data_full.begin() + num_old_vars, m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.shrink(num_old_vars);        
        m_eqs.reset();
        m_eqsv.reset();
    }

    void theory_array_full::collect_statistics(::statistics & st) const {
        theory_array::collect_statistics(st);
        st.update("array map ax", m_stats.m_num_map_axiom);
        st.update("array def const", m_stats.m_num_default_const_axiom);
        st.update("array sel const", m_stats.m_num_select_const_axiom);
        st.update("array def store", m_stats.m_num_default_store_axiom);
        st.update("array def as-array", m_stats.m_num_default_as_array_axiom);
        st.update("array sel as-array", m_stats.m_num_select_as_array_axiom);
    }
}
