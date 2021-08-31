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

#include "util/stats.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_array_full.h"

namespace smt {

    theory_array_full::theory_array_full(context& ctx) : 
        theory_array(ctx),
        m_sort2epsilon(ctx.get_manager()),
        m_sort2diag(ctx.get_manager()) {}

    theory_array_full::~theory_array_full() {
        std::for_each(m_var_data_full.begin(), m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.reset();
    }

    theory* theory_array_full::mk_fresh(context* new_ctx) { 
        return alloc(theory_array_full, *new_ctx);
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
        m_trail_stack.push(push_back_trail<enode *, false>(d_full->m_maps));
        for (unsigned i = 0; i < d->m_parent_selects.size(); ++i) {
            enode* n = d->m_parent_selects[i];
            SASSERT(is_select(n));
            instantiate_select_map_axiom(n, s);
        }
        set_prop_upward(s);
    }

    bool theory_array_full::instantiate_axiom_map_for(theory_var v) {
        bool result = false;
        var_data * d = m_var_data[v];
        var_data_full * d_full = m_var_data_full[v];
        for (unsigned i = 0; i < d_full->m_parent_maps.size(); ++i) {
            enode* pm = d_full->m_parent_maps[i];
            for (unsigned j = 0; j < d->m_parent_selects.size(); ++j) {
                enode* ps = d->m_parent_selects[j];
                if (instantiate_select_map_axiom(ps, pm)) 
                    result = true;                  
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
        m_trail_stack.push(push_back_trail<enode *, false>(d_full->m_parent_maps));
        if (!m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            for (unsigned i = 0; i < d->m_parent_selects.size(); ++i) {
                enode * n = d->m_parent_selects[i];
                if (!m_params.m_array_cg || n->is_cgr()) {
                    instantiate_select_map_axiom(n, s);
                }                
            }
        }
    }

    //
    // set set_prop_upward on root and recursively on children if necessary.
    // 
    void theory_array_full::set_prop_upward(theory_var v) {
        v = find(v);
        var_data * d = m_var_data[v];
        if (!d->m_prop_upward) {
            if (m_params.m_array_weak) {
                add_weak_var(v);
                return;
            }
            m_trail_stack.push(reset_flag_trail(d->m_prop_upward));
            d->m_prop_upward = true;
            TRACE("array", tout << "#" << v << "\n";);
            if (!m_params.m_array_delay_exp_axiom) {
                instantiate_axiom2b_for(v);
                instantiate_axiom_map_for(v);
            }
            var_data_full * d2 = m_var_data_full[v];
            for (enode * n : d->m_stores) {
                set_prop_upward(n);
            }
            for (enode * n : d2->m_maps) {
                set_prop_upward(n);
            }
            for (enode * n : d2->m_consts) {
                set_prop_upward(n);
            }
        }        
    }

    //
    // call set_prop_upward on array arguments.
    // 
    void theory_array_full::set_prop_upward(enode * n) {
        TRACE("array", tout << pp(n, m) << "\n";);
        if (is_store(n)) {
            set_prop_upward(n->get_arg(0)->get_th_var(get_id()));
        }
        else if (is_map(n)) {
            for (enode* arg : enode::args(n)) {
                set_prop_upward(arg->get_th_var(get_id()));
            }
        }
    }

    void theory_array_full::set_prop_upward(theory_var v, var_data* d) {
        if (m_params.m_array_always_prop_upward || !d->m_stores.empty()) {
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
        m_trail_stack.push(push_back_trail<enode *, false>(consts));
        consts.push_back(cnst);
        instantiate_default_const_axiom(cnst);
        for (unsigned i = 0; i < d->m_parent_selects.size(); ++i) {
            enode * n = d->m_parent_selects[i];
            SASSERT(is_select(n));
            instantiate_select_const_axiom(n, cnst);
        }
    }

    void theory_array_full::add_as_array(theory_var v, enode* arr) {
        var_data * d  = m_var_data[v];
        unsigned lambda_equiv_class_size = get_lambda_equiv_size(v, d);
        if (m_params.m_array_always_prop_upward || lambda_equiv_class_size >= 1) {
            set_prop_upward(v, d);
        }
        ptr_vector<enode> & as_arrays = m_var_data_full[v]->m_as_arrays;
        m_trail_stack.push(push_back_trail<enode *, false>(as_arrays));
        as_arrays.push_back(arr);
        instantiate_default_as_array_axiom(arr);        
        for (unsigned i = 0; i < d->m_parent_selects.size(); ++i) {
            enode* n = d->m_parent_selects[i];
            SASSERT(is_select(n));
            instantiate_select_as_array_axiom(n, arr);
        }
    }


    void theory_array_full::reset_eh() {
        theory_array::reset_eh();
        std::for_each(m_var_data_full.begin(), m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.reset();
        m_eqs.reset();
    }

    void theory_array_full::display_var(std::ostream & out, theory_var v) const {
        theory_array::display_var(out, v);
        var_data_full const * d = m_var_data_full[v];
        out << " maps: {";
        display_ids(out, d->m_maps.size(), d->m_maps.data());
        out << "} p_parent_maps: {";
        display_ids(out, d->m_parent_maps.size(), d->m_parent_maps.data());
        out << "} p_const: {";
        display_ids(out, d->m_consts.size(), d->m_consts.data());
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
        if (ctx.e_internalized(n)) {
            return true;
        }
        TRACE("array", tout << mk_pp(n, m) << "\n";);

        if (is_store(n) || is_select(n)) {
            return theory_array::internalize_term(n);
        }

        if (!is_const(n) && !is_default(n)  && !is_map(n) && !is_as_array(n) && !is_set_has_size(n) && !is_set_card(n)) {
            if (!is_array_ext(n))
                found_unsupported_op(n);
            return false;
        }

        if (!internalize_term_core(n)) {
            return true;
        }

        if (is_map(n) || is_array_ext(n)) {
            for (expr* e : *n) {
                enode* arg = ctx.get_enode(e);
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
        else if (is_set_has_size(n) || is_set_card(n)) {
            if (!m_bapa) {
                m_bapa = alloc(theory_array_bapa, *this);
            }
            m_bapa->internalize_term(n);
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
            for (expr* e : *n) {
                enode* arg = ctx.get_enode(e);
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
        for (enode * n : d2->m_maps) {
            add_map(v1, n);
        }
        for (enode * n : d2->m_parent_maps) {
            add_parent_map(v1, n);
        }
        for (enode * n : d2->m_consts) {
            add_const(v1, n);
        }
        for (enode * n : d2->m_as_arrays) {
            add_as_array(v1, n);
        }
        TRACE("array", 
              tout << pp(get_enode(v1), m) << "\n";
              tout << pp(get_enode(v2), m) << "\n";
              tout << "merge in\n"; display_var(tout, v2);
              tout << "after merge\n"; display_var(tout, v1););
    }

    void theory_array_full::add_parent_default(theory_var v) {
        SASSERT(v != null_theory_var);
        v = find(v);
        var_data* d = m_var_data[v];
        TRACE("array", tout << "v" << v << " " << pp(get_enode(v), m) << " " 
              << d->m_prop_upward << " " << m_params.m_array_delay_exp_axiom << "\n";);
        for (enode * store : d->m_stores) {
            SASSERT(is_store(store));
            instantiate_default_store_axiom(store);
        }        

        if (!m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            instantiate_parent_stores_default(v);            
        }
    }

    void theory_array_full::add_parent_select(theory_var v, enode * s) {
        TRACE("array", 
              tout << v << " select parent: " << pp(s, m) << "\n";
              display_var(tout, v);
              );
        theory_array::add_parent_select(v,s);
        v = find(v);
        var_data_full* d_full = m_var_data_full[v];
        var_data* d = m_var_data[v];
        for (enode * n : d_full->m_consts) {
            instantiate_select_const_axiom(s, n);
        }
        for (enode * map : d_full->m_maps) {
            SASSERT(is_map(map));
            instantiate_select_map_axiom(s, map);
        }
        if (!m_params.m_array_delay_exp_axiom && d->m_prop_upward) {
            for (enode * map : d_full->m_parent_maps) {
                SASSERT(is_map(map));
                if (!m_params.m_array_cg || map->is_cgr()) {
                    instantiate_select_map_axiom(s, map);
                }
            }
        }
    }
    
    void theory_array_full::relevant_eh(app* n) {
        TRACE("array", tout << mk_pp(n, m) << "\n";);
        theory_array::relevant_eh(n);
        if (!is_default(n) && !is_select(n) && !is_map(n) && !is_const(n) && !is_as_array(n)){
            return;
        }
        ctx.ensure_internalized(n);
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
            set_prop_upward(v);               
            add_parent_default(find(v));
        }
        else if (is_const(n)) {
            instantiate_default_const_axiom(node);
            theory_var v = node->get_th_var(get_id());
            set_prop_upward(v);
            add_parent_default(find(v));
        }
        else if (is_map(n)) {
            for (expr * e : *n) {
                enode* arg = ctx.get_enode(e);
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

    bool theory_array_full::should_research(expr_ref_vector & unsat_core) {
        return m_bapa && m_bapa->should_research(unsat_core);
    }

    void theory_array_full::add_theory_assumptions(expr_ref_vector & assumptions) {
        if (m_bapa) m_bapa->add_theory_assumptions(assumptions);
    }
       
    //
    // Assert axiom: 
    // select(map[f](a, ... d), i) = f(select(a,i),...,select(d,i))
    //  
    bool theory_array_full::instantiate_select_map_axiom(enode* sl, enode* mp) {
        app* map = mp->get_expr();
        app* select = sl->get_expr();
        SASSERT(is_map(map));
        SASSERT(is_select(select));
        SASSERT(map->get_num_args() > 0);
        func_decl* f = to_func_decl(map->get_decl()->get_parameter(0).get_ast());


        TRACE("array_map_bug", tout << "invoked instantiate_select_map_axiom\n";
              tout << sl->get_owner_id() << " " << mp->get_owner_id() << "\n";
              tout << mk_ismt2_pp(sl->get_expr(), m) << "\n" << mk_ismt2_pp(mp->get_expr(), m) << "\n";);

        if (!ctx.add_fingerprint(mp, mp->get_owner_id(), sl->get_num_args() - 1, sl->get_args() + 1)) {
            return false;
        }

        TRACE("array_map_bug", tout << "new axiom\n";);

        m_stats.m_num_map_axiom++;
        TRACE("array", 
              tout << mk_bounded_pp(mp->get_expr(), m) << "\n";
              tout << mk_bounded_pp(sl->get_expr(), m) << "\n";);
        unsigned num_args   = select->get_num_args();
        unsigned num_arrays = map->get_num_args();
        ptr_buffer<expr> args1, args2;
        vector<ptr_vector<expr> > args2l;
        args1.push_back(map);
        for (expr* ar : *map) {
            ptr_vector<expr> arg;
            arg.push_back(ar);
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
            expr* sel = mk_select(args2l[j].size(), args2l[j].data());
            args2.push_back(sel);
        }

        expr_ref sel1(m), sel2(m);
        sel1 = mk_select(args1.size(), args1.data());
        sel2 = m.mk_app(f, args2.size(), args2.data());
        ctx.get_rewriter()(sel2);
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
                
        app* map = mp->get_expr();
        if (!ctx.add_fingerprint(this, m_default_map_fingerprint, 1, &mp)) {
            return false;
        }
        TRACE("array", tout << mk_bounded_pp(map, m) << "\n";);

        m_stats.m_num_default_map_axiom++;

        func_decl* f = to_func_decl(map->get_decl()->get_parameter(0).get_ast());
        SASSERT(map->get_num_args() == f->get_arity());
        ptr_buffer<expr> args2;
        for (expr* arg : *map) {
            args2.push_back(mk_default(arg));
        }

        expr_ref def2(m.mk_app(f, args2.size(), args2.data()), m);
        ctx.get_rewriter()(def2);
        expr* def1 = mk_default(map);
        ctx.internalize(def1, false);
        ctx.internalize(def2, false);
        return try_assign_eq(def1, def2);
    }


    bool theory_array_full::instantiate_default_const_axiom(enode* cnst) {
        if (!ctx.add_fingerprint(this, m_default_const_fingerprint, 1, &cnst)) {
            return false;
        }
        m_stats.m_num_default_const_axiom++;
        SASSERT(is_const(cnst));
        TRACE("array", tout << mk_bounded_pp(cnst->get_expr(), m) << "\n";);
        expr* val = cnst->get_arg(0)->get_expr();
        expr* def = mk_default(cnst->get_expr());
        ctx.internalize(def, false);
        return try_assign_eq(val, def);
    }

    /**
     * instantiate f(ep1,ep2,..,ep_n) = default(as-array f)
     * it is disabled to avoid as-array terms during search.
     */

    bool theory_array_full::instantiate_default_as_array_axiom(enode* arr) {
        return false;
#if 0
        if (!ctx.add_fingerprint(this, m_default_as_array_fingerprint, 1, &arr)) {
            return false;
        }
        m_stats.m_num_default_as_array_axiom++;
        SASSERT(is_as_array(arr));
        TRACE("array", tout << mk_bounded_pp(arr->get_owner(), m) << "\n";);
        expr* def = mk_default(arr->get_owner());
        func_decl * f = array_util(m).get_as_array_func_decl(arr->get_owner());
        ptr_vector<expr> args;
        for (unsigned i = 0; i < f->get_arity(); ++i) {
            args.push_back(mk_epsilon(f->get_domain(i)));
        }
        expr_ref val(m.mk_app(f, args.size(), args.c_ptr()), m);
        ctx.internalize(def, false);
        ctx.internalize(val.get(), false);
        return try_assign_eq(val.get(), def);
#endif
    }

    bool theory_array_full::has_unitary_domain(app* array_term) {
        SASSERT(is_array_sort(array_term));
        sort* s = array_term->get_sort();
        unsigned dim = get_dimension(s);
        parameter const * params = s->get_info()->get_parameters();
        for (unsigned i = 0; i < dim; ++i) {
            SASSERT(params[i].is_ast());
            sort* d = to_sort(params[i].get_ast());
            if (d->is_infinite() || d->is_very_big() || 1 != d->get_num_elements().size())
                return false;
        }
        return true;        
    }

   bool theory_array_full::has_large_domain(app* array_term) {
        SASSERT(is_array_sort(array_term));
        sort* s = array_term->get_sort();
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
            if (sz >= rational(1 << 14)) {
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
        unsigned num_args = select->get_num_args();
        if (!ctx.add_fingerprint(cnst, cnst->get_owner_id(), select->get_num_args() - 1, select->get_args() + 1)) {
            return false;
        }

        m_stats.m_num_select_const_axiom++;   
        ptr_buffer<expr> sel_args;
        sel_args.push_back(cnst->get_expr());
        for (unsigned short i = 1; i < num_args; ++i) {
            sel_args.push_back(select->get_expr()->get_arg(i));
        }
        expr * sel = mk_select(sel_args.size(), sel_args.data());
        expr * val = cnst->get_expr()->get_arg(0);
        TRACE("array", tout << "new select-const axiom...\n";
              tout << "const: " << mk_bounded_pp(cnst->get_expr(), m) << "\n";
              tout << "select: " << mk_bounded_pp(select->get_expr(), m) << "\n";
              tout << " sel/const: " << mk_bounded_pp(sel, m) << "\n";
              tout << "value: " << mk_bounded_pp(val, m) << "\n";
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
        SASSERT(is_as_array(arr->get_expr()));
        SASSERT(is_select(select));
        SASSERT(arr->get_num_args() == 0);
        unsigned num_args = select->get_num_args();
        if (!ctx.add_fingerprint(arr, arr->get_owner_id(), select->get_num_args() - 1, select->get_args() + 1)) {
            return false;
        }

        m_stats.m_num_select_as_array_axiom++;   
        ptr_buffer<expr> sel_args;
        sel_args.push_back(arr->get_expr());
        for (unsigned short i = 1; i < num_args; ++i) {
            sel_args.push_back(select->get_expr()->get_arg(i));
        }
        expr * sel = mk_select(sel_args.size(), sel_args.data());
        func_decl * f = array_util(m).get_as_array_func_decl(arr->get_expr());
        expr_ref val(m.mk_app(f, sel_args.size()-1, sel_args.data()+1), m);
        TRACE("array", tout << "new select-as-array axiom...\n";
              tout << "as-array: " << mk_bounded_pp(arr->get_expr(), m) << "\n";
              tout << "select: " << mk_bounded_pp(select->get_expr(), m) << "\n";
              tout << " sel/as-array: " << mk_bounded_pp(sel, m) << "\n";
              tout << "value: " << mk_bounded_pp(val.get(), m) << "\n";
              tout << "#" << sel->get_id() << " = #" << val->get_id() << "\n";
              );
        
        ctx.internalize(sel, false);
        ctx.internalize(val.get(), false);
        return try_assign_eq(sel,val);
    }

    
    bool theory_array_full::instantiate_default_store_axiom(enode* store) {
        SASSERT(is_store(store));
        SASSERT(store->get_num_args() >= 3);
        app* store_app = store->get_expr();
        if (!ctx.add_fingerprint(this, m_default_store_fingerprint, store->get_num_args(), store->get_args())) {
            return false;
        }

        m_stats.m_num_default_store_axiom++;

        expr_ref def1(m), def2(m);

        TRACE("array", tout << mk_bounded_pp(store_app, m) << "\n";);

        unsigned num_args = store_app->get_num_args();

        def1 = mk_default(store_app);
        def2 = mk_default(store_app->get_arg(0));

        bool is_new = false;

        if (has_unitary_domain(store_app)) {
            def2 = store_app->get_arg(num_args - 1);
        }        
        else if (!has_large_domain(store_app)) {
            //
            // let A = store(B, i, v)
            // 
            // Add:
            //   default(A) = ite(epsilon1 = i, v, default(B))
            //   A[diag(i)] = B[diag(i)]
            // 
            expr_ref_vector eqs(m);
            expr_ref_vector args1(m), args2(m);
            args1.push_back(store_app->get_arg(0));
            args2.push_back(store_app);

            for (unsigned i = 1; i + 1 < num_args; ++i) {
                expr* arg = store_app->get_arg(i);
                sort* srt = arg->get_sort();
                auto ep = mk_epsilon(srt);
                eqs.push_back(m.mk_eq(ep.first, arg));
                args1.push_back(m.mk_app(ep.second, arg));
                args2.push_back(m.mk_app(ep.second, arg));
            }            
            expr_ref eq(mk_and(eqs), m);
            def2 = m.mk_ite(eq, store_app->get_arg(num_args-1), def2);             
            app_ref sel1(m), sel2(m);
            sel1 = mk_select(args1);
            sel2 = mk_select(args2);
            is_new = try_assign_eq(sel1, sel2);
        }

        ctx.internalize(def1, false);
        ctx.internalize(def2, false);
        return try_assign_eq(def1, def2) || is_new;
    }

    std::pair<app*,func_decl*> theory_array_full::mk_epsilon(sort* s) {
        app* eps = nullptr;
        func_decl* diag = nullptr;
        if (!m_sort2epsilon.find(s, eps)) {
            eps = m.mk_fresh_const("epsilon", s);
            m_trail_stack.push(ast2ast_trail<sort, app>(m_sort2epsilon, s, eps));   
        }
        if (!m_sort2diag.find(s, diag)) {
            diag = m.mk_fresh_func_decl("diag", 1, &s, s);
            m_trail_stack.push(ast2ast_trail<sort, func_decl>(m_sort2diag, s, diag));   
        }
        return std::make_pair(eps, diag);
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
                if (d->m_prop_upward) {
                    if (instantiate_parent_stores_default(v))
                        r = FC_CONTINUE;
                }
            }
        }
        if (r == FC_DONE && m_bapa) {
            r = m_bapa->final_check();
        }
        bool should_giveup = m_found_unsupported_op || has_propagate_up_trail();
        if (r == FC_DONE && should_giveup)
            r = FC_GIVEUP;
        return r;
    }

    bool theory_array_full::instantiate_parent_stores_default(theory_var v) {
        SASSERT(v != null_theory_var);
        TRACE("array", tout << "v" << v << "\n";);
        v = find(v);
        var_data* d = m_var_data[v];
        bool result = false;
        for (unsigned i = 0; i < d->m_parent_stores.size(); ++i) {
            enode* store = d->m_parent_stores[i];
            SASSERT(is_store(store));
            if ((!m_params.m_array_cg || store->is_cgr()) && 
                instantiate_default_store_axiom(store)) {
                result = true;
            }
        }
        return result;
    }

    bool theory_array_full::try_assign_eq(expr* v1, expr* v2) {
        TRACE("array", tout << mk_bounded_pp(v1, m) << "\n==\n" << mk_bounded_pp(v2, m) << "\n";);
        
        if (m_eqs.contains(v1, v2)) {
            return false;
        }
        else {
            m_eqs.insert(v1, v2, true);
            literal eq(mk_eq(v1, v2, true));
            scoped_trace_stream _sc(*this, eq);
            ctx.mark_as_relevant(eq);            
            assert_axiom(eq);
            return true;
        }
    }

    void theory_array_full::pop_scope_eh(unsigned num_scopes) {
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        theory_array::pop_scope_eh(num_scopes);
        std::for_each(m_var_data_full.begin() + num_old_vars, m_var_data_full.end(), delete_proc<var_data_full>());
        m_var_data_full.shrink(num_old_vars);        
        m_eqs.reset();
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
