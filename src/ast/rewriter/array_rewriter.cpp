/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    array_rewriter.cpp

Abstract:

    Basic rewriting rules for Arrays.

Author:

    Leonardo (leonardo) 2011-04-06

Notes:

--*/
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/array_rewriter_params.hpp"
#include "ast/ast_lt.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"

void array_rewriter::updt_params(params_ref const & _p) {
    array_rewriter_params p(_p);
    m_sort_store = p.sort_store();
    m_expand_select_store = p.expand_select_store();
    m_expand_store_eq = p.expand_store_eq();
    m_expand_nested_stores = p.expand_nested_stores();
    m_expand_select_ite = false;
}

void array_rewriter::get_param_descrs(param_descrs & r) {
    array_rewriter_params::collect_param_descrs(r);
}

br_status array_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    br_status st;
    switch (f->get_decl_kind()) {
    case OP_SELECT:
        st = mk_select_core(num_args, args, result);
        break;
    case OP_STORE:
        st = mk_store_core(num_args, args, result);
        break;
    case OP_ARRAY_MAP:
        st = mk_map_core(m_util.get_map_func_decl(f), num_args, args, result);
        break;
    case OP_SET_UNION:
        st = mk_set_union(num_args, args, result);
        break;
    case OP_SET_INTERSECT:
        st = mk_set_intersect(num_args, args, result);
        break;
    case OP_SET_SUBSET: 
        SASSERT(num_args == 2);
        st = mk_set_subset(args[0], args[1], result);
        break;
    case OP_SET_COMPLEMENT:
        SASSERT(num_args == 1);
        st = mk_set_complement(args[0], result);
        break;
    case OP_SET_DIFFERENCE:
        SASSERT(num_args == 2);
        st = mk_set_difference(args[0], args[1], result);
        break;
    default:
        st = BR_FAILED;
        break;
    }
    CTRACE("array_rewriter", st != BR_FAILED, 
           tout << mk_pp(f, m()) << "\n";
           for (unsigned i = 0; i < num_args; ++i) {
               tout << mk_pp(args[i], m()) << "\n";
           }
           tout << "\n --> " << result << "\n";);
    return st;
}

// l_true  -- all equal
// l_false -- at least one disequal
// l_undef -- don't know
template<bool CHECK_DISEQ>
lbool array_rewriter::compare_args(unsigned num_args, expr * const * args1, expr * const * args2) {
    for (unsigned i = 0; i < num_args; i++) {
        if (args1[i] == args2[i])
            continue;
        if (CHECK_DISEQ && m().are_distinct(args1[i], args2[i]))
            return l_false;
        return l_undef;
    }
    return l_true;
}

br_status array_rewriter::mk_store_core(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args >= 3);

    if (m_util.is_store(args[0])) {
        lbool r = m_sort_store ? 
            compare_args<true>(num_args - 2, args + 1, to_app(args[0])->get_args() + 1) :
            compare_args<false>(num_args - 2, args + 1, to_app(args[0])->get_args() + 1);
        switch (r) {
        case l_true: {
            //
            // store(store(a,i,v),i,w) --> store(a,i,w)
            // 
            ptr_buffer<expr> new_args;
            new_args.push_back(to_app(args[0])->get_arg(0));
            new_args.append(num_args-1, args+1);
            SASSERT(new_args.size() == num_args);
            result = m().mk_app(get_fid(), OP_STORE, num_args, new_args.c_ptr());
            return BR_DONE;
        }
        case l_false:
            SASSERT(m_sort_store);
            // 
            // store(store(a,i,v),j,w) -> store(store(a,j,w),i,v)
            // if i, j are different, lt(i,j)
            // 
            if (lex_lt(num_args-2, args+1, to_app(args[0])->get_args() + 1)) {
                ptr_buffer<expr> new_args;
                new_args.push_back(to_app(args[0])->get_arg(0));
                new_args.append(num_args-1, args+1);
                expr * nested_store = m().mk_app(get_fid(), OP_STORE, num_args, new_args.c_ptr());
                new_args.reset();
                new_args.push_back(nested_store);
                new_args.append(num_args - 1, to_app(args[0])->get_args() + 1);
                result = m().mk_app(get_fid(), OP_STORE, num_args, new_args.c_ptr());
                return BR_REWRITE2;
            }
            break;
        case l_undef:
            break;
        }
    }
        
    //
    // store(const(v),i,v) --> const(v)
    //
    if (m_util.is_const(args[0]) &&
        to_app(args[0])->get_arg(0) == args[num_args-1]) {
        result = args[0];
        return BR_DONE;
    }

    expr * v = args[num_args-1];

    // 
    // store(a, i, select(a, i)) --> a
    //
    if (m_util.is_select(v) && 
        compare_args<false>(num_args-1, args, to_app(v)->get_args())) {
        result = args[0];
        return BR_DONE;
    }

    return BR_FAILED;
}
        
br_status array_rewriter::mk_select_core(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args >= 2);
    if (m_util.is_store(args[0])) {
        SASSERT(to_app(args[0])->get_num_args() == num_args+1);
        switch (compare_args<true>(num_args - 1, args+1, to_app(args[0])->get_args()+1)) {
        case l_true:
            // select(store(a, I, v), I) --> v
            result = to_app(args[0])->get_arg(num_args);
            return BR_DONE;
        case l_false: {
            // select(store(a, I, v), J) --> select(a, J) if I != J
            ptr_buffer<expr> new_args;
            new_args.push_back(to_app(args[0])->get_arg(0));
            new_args.append(num_args-1, args+1);
            result = m().mk_app(get_fid(), OP_SELECT, num_args, new_args.c_ptr());
            return BR_REWRITE1;
        }
        default:
            if (m_expand_select_store) {
                // select(store(a, I, v), J) --> ite(I=J, v, select(a, J))
                ptr_buffer<expr> new_args;
                new_args.push_back(to_app(args[0])->get_arg(0));
                new_args.append(num_args-1, args+1);
                expr * sel_a_j = m().mk_app(get_fid(), OP_SELECT, num_args, new_args.c_ptr());
                expr * v       = to_app(args[0])->get_arg(num_args);
                ptr_buffer<expr> eqs;
                unsigned num_indices = num_args-1;
                for (unsigned i = 0; i < num_indices; i++) {
                    eqs.push_back(m().mk_eq(to_app(args[0])->get_arg(i+1), args[i+1]));
                }
                if (num_indices == 1) {
                    result = m().mk_ite(eqs[0], v, sel_a_j);
                    return BR_REWRITE2;
                }
                else {
                    result = m().mk_ite(m().mk_and(eqs.size(), eqs.c_ptr()), v, sel_a_j);
                    return BR_REWRITE3;
                }
            }
            return BR_FAILED;
        }
    }

    if (m_util.is_const(args[0])) {
        // select(const(v), I) --> v
        result = to_app(args[0])->get_arg(0);
        return BR_DONE;
    }

    if (is_lambda(args[0])) {
        // anywhere lambda reduction as opposed to whnf
        // select(lambda(X) M, N) -> M[N/X]
        quantifier* q = to_quantifier(args[0]);
        SASSERT(q->get_num_decls() == num_args - 1);
        var_subst subst(m());
        result = subst(q->get_expr(), num_args - 1, args + 1);
        return BR_REWRITE_FULL;
        
    }

    if (m_util.is_map(args[0])) {
        app* a = to_app(args[0]);
        func_decl* f0 = m_util.get_map_func_decl(a);
        expr_ref_vector args0(m());
        for (expr* arg : *a) {
            ptr_vector<expr> args1;
            args1.push_back(arg);
            args1.append(num_args-1, args + 1);
            args0.push_back(m_util.mk_select(args1.size(), args1.c_ptr()));
        }
        result = m().mk_app(f0, args0.size(), args0.c_ptr());
        return BR_REWRITE2;
    }

    if (m_util.is_as_array(args[0])) {
        // select(as-array[f], I) --> f(I)
        func_decl * f = m_util.get_as_array_func_decl(to_app(args[0]));
        result = m().mk_app(f, num_args - 1, args + 1);
        return BR_REWRITE1;
    }

    expr* c, *th, *el;
    if (m().is_ite(args[0], c, th, el) && (m_expand_select_ite || (th->get_ref_count() == 1 || el->get_ref_count() == 1))) {
        ptr_vector<expr> args1, args2;
        args1.push_back(th);
        args1.append(num_args-1, args + 1);
        args2.push_back(el);
        args2.append(num_args-1, args + 1);
        result = m().mk_ite(c, m_util.mk_select(num_args, args1.c_ptr()), m_util.mk_select(num_args, args2.c_ptr()));
        return BR_REWRITE2;
    }
    
    return BR_FAILED;
}

sort_ref array_rewriter::get_map_array_sort(func_decl* f, unsigned num_args, expr* const* args) {
    sort* s0 = m().get_sort(args[0]);
    unsigned sz = get_array_arity(s0);
    ptr_vector<sort> domain;
    for (unsigned i = 0; i < sz; ++i) domain.push_back(get_array_domain(s0, i));
    return sort_ref(m_util.mk_array_sort(sz, domain.c_ptr(), f->get_range()), m());
}

br_status array_rewriter::mk_map_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {

    app* store_expr = nullptr;
    unsigned num_indices = 0;
    bool same_store = true;
    for (unsigned i = 0; same_store && i < num_args; i++) {
        expr* a = args[i];
        if (m_util.is_const(a)) {
            continue;
        }
        else if (!m_util.is_store(a)) {
            same_store = false;
        }
        else if (!store_expr) {
            num_indices = to_app(a)->get_num_args() - 2;
            store_expr = to_app(a);
        }
        else {
            for (unsigned j = 1; same_store && j < num_indices + 1; j++) {
                same_store = (store_expr->get_arg(j) == to_app(a)->get_arg(j));
            }
        }
    }
    
    //
    // map_f (store a_1 j v_1) ... (store a_n j v_n) --> (store (map_f a_1 ... a_n) j (f v_1 ... v_n))
    //
    if (same_store) {
        ptr_buffer<expr> arrays;
        ptr_buffer<expr> values;
        for (unsigned i = 0; i < num_args; i++) {
            expr* a = args[i];
            if (m_util.is_const(a)) {
                arrays.push_back(a);
                values.push_back(to_app(a)->get_arg(0));
            }
            else {
                arrays.push_back(to_app(a)->get_arg(0));
                values.push_back(to_app(a)->get_arg(num_indices+1));
            }
        }
        if (store_expr) {
            ptr_buffer<expr> new_args;
            new_args.push_back(m_util.mk_map(f, arrays.size(), arrays.c_ptr()));
            new_args.append(num_indices, store_expr->get_args() + 1);
            new_args.push_back(m().mk_app(f, values.size(), values.c_ptr()));
            result = m().mk_app(get_fid(), OP_STORE, new_args.size(), new_args.c_ptr());
        }
        else {
            expr_ref value(m().mk_app(f, values.size(), values.c_ptr()), m());
            sort_ref s = get_map_array_sort(f, num_args, args);
            result = m_util.mk_const_array(s, value);
        }
        TRACE("array", tout << result << "\n";);
        return BR_REWRITE2;
    }

    //
    // map_f (lambda x1 b1) ... (lambda x1 bn) -> lambda x1 (f b1 .. bn)
    //
    quantifier* lam = nullptr;
    for (unsigned i = 0; i < num_args; ++i) {
        if (is_lambda(args[i])) {
            lam = to_quantifier(args[i]);
        }
    }
    if (lam) {
        expr_ref_vector args1(m());
        for (unsigned i = 0; i < num_args; ++i) {
            expr* a = args[i];
            if (m_util.is_const(a)) {
                args1.push_back(to_app(a)->get_arg(0));
            }
            else if (is_lambda(a)) {
                lam = to_quantifier(a);
                args1.push_back(lam->get_expr());
            }
            else {
                expr_ref_vector sel(m());
                sel.push_back(a);
                unsigned n = lam->get_num_decls();
                for (unsigned i = 0; i < n; ++i) {
                    sel.push_back(m().mk_var(n - i - 1, lam->get_decl_sort(i)));
                }
                args1.push_back(m_util.mk_select(sel.size(), sel.c_ptr()));
            }
        }
        result = m().mk_app(f, args1.size(), args1.c_ptr());
        result = m().update_quantifier(lam, result);
        return BR_REWRITE3;        
    }

    if (m().is_not(f) && m_util.is_map(args[0]) && m().is_not(m_util.get_map_func_decl(args[0]))) {
        result = to_app(args[0])->get_arg(0);
        return BR_DONE;
    }

    if (m().is_and(f)) {
        ast_mark mark;
        ptr_buffer<expr> es;
        bool change = false;
        unsigned j = 0;
        es.append(num_args, args);
        for (unsigned i = 0; i < es.size(); ++i) {
            expr* e = es[i];
            if (mark.is_marked(e)) {
                change = true;
            }
            else if (m_util.is_map(e) && m().is_and(m_util.get_map_func_decl(e))) {
                mark.mark(e, true);                
                es.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else {
                mark.mark(e, true);
                es[j++] = es[i];
            }
        }
        es.shrink(j);
        j = 0;
        for (expr* e : es) {
            if (m_util.is_map(e) && m().is_not(m_util.get_map_func_decl(e))) {
                expr * arg = to_app(e)->get_arg(0);
                if (mark.is_marked(arg)) {
                    sort_ref s = get_map_array_sort(f, num_args, args);
                    result = m_util.mk_const_array(s, m().mk_false());
                    return BR_DONE;
                }
                // a & (!a & b & c) -> a & !(b & c)
                if (m_util.is_map(arg) && m().is_and(m_util.get_map_func_decl(arg))) {
                    unsigned k = 0;
                    ptr_buffer<expr> gs;
                    bool and_change = false;
                    gs.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
                    for (unsigned i = 0; i < gs.size(); ++i) {
                        expr* g = gs[i];
                        if (mark.is_marked(g)) {
                            change = true;
                            and_change = true;
                        }
                        else if (m_util.is_map(g) && m().is_and(m_util.get_map_func_decl(g))) {
                            gs.append(to_app(g)->get_num_args(), to_app(g)->get_args());
                        }
                        else {
                            gs[k++] = gs[i];
                        }                        
                    }
                    gs.shrink(k);
                    if (and_change) {
                        std::sort(gs.begin(), gs.end(), [](expr* a, expr* b) { return a->get_id() < b->get_id(); });
                        expr* arg = m_util.mk_map_assoc(f, gs.size(), gs.c_ptr());
                        es[j] = m_util.mk_map(m().mk_not_decl(), 1, &arg);                          
                    }
                }
            }
            ++j;
        }        
        if (change) {
            std::sort(es.begin(), es.end(), [](expr* a, expr* b) { return a->get_id() < b->get_id(); });
            result = m_util.mk_map_assoc(f, es.size(), es.c_ptr());
            return BR_REWRITE2;
        }
    }

    if (m().is_or(f)) {
        ast_mark mark;
        ptr_buffer<expr> es;
        es.append(num_args, args);
        unsigned j = 0;
        bool change = false;
        for (unsigned i = 0; i < es.size(); ++i) {
            expr* e = es[i];
            if (mark.is_marked(e)) {
                change = true;
            }
            else if (m_util.is_map(e) && m().is_or(m_util.get_map_func_decl(e))) {
                mark.mark(e, true);                
                es.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else {
                mark.mark(e, true);
                es[j++] = es[i];
            }
        }
        es.shrink(j);
        for (expr* e : es) {
            if (m_util.is_map(e) && m().is_not(m_util.get_map_func_decl(e)) && mark.is_marked(to_app(e)->get_arg(0))) {
                sort_ref s = get_map_array_sort(f, num_args, args);
                result = m_util.mk_const_array(s, m().mk_true());
                return BR_DONE;
            }
        }        
        if (change) {
            result = m_util.mk_map_assoc(f, es.size(), es.c_ptr());
            return BR_REWRITE1;
        }
    }


    return BR_FAILED;
}

void array_rewriter::mk_store(unsigned num_args, expr * const * args, expr_ref & result) {
    if (mk_store_core(num_args, args, result) == BR_FAILED)
        result = m().mk_app(get_fid(), OP_STORE, num_args, args);
}
        
void array_rewriter::mk_select(unsigned num_args, expr * const * args, expr_ref & result) {
    if (mk_select_core(num_args, args, result) == BR_FAILED)
        result = m().mk_app(get_fid(), OP_SELECT, num_args, args);
}

void array_rewriter::mk_map(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (mk_map_core(f, num_args, args, result) == BR_FAILED)
        result = m_util.mk_map(f, num_args, args);
}

br_status array_rewriter::mk_set_union(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0);
    if (num_args == 1) {
        result = args[0];
        return BR_DONE;
    }
    SASSERT(num_args >= 2);
    br_status r = unsigned2br_status(num_args - 2);
    result = m_util.mk_map(m().mk_or_decl(), num_args, args);
    return r;
}

br_status array_rewriter::mk_set_intersect(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0);
    if (num_args == 1) {
        result = args[0];
        return BR_DONE;
    }
    SASSERT(num_args >= 2);
    br_status r = unsigned2br_status(num_args - 2);
    result = m_util.mk_map(m().mk_and_decl(), num_args, args);
    return r;
}


br_status array_rewriter::mk_set_complement(expr * arg, expr_ref & result) {
    func_decl* fnot = m().mk_not_decl();
    br_status st = mk_map_core(fnot, 1, &arg, result);
    if (BR_FAILED == st) {
        result = m_util.mk_map(fnot, 1, &arg);
        st = BR_DONE;
    }
    return st;
}

br_status array_rewriter::mk_set_difference(expr * arg1, expr * arg2, expr_ref & result) {
    expr * args[2] = { arg1, m_util.mk_map(m().mk_not_decl(), 1, &arg2) };
    result = m_util.mk_map(m().mk_and_decl(), 2, args);
    return BR_REWRITE2;
}

br_status array_rewriter::mk_set_subset(expr * arg1, expr * arg2, expr_ref & result) {
    mk_set_difference(arg1, arg2, result);
    result = m().mk_eq(result.get(), m_util.mk_empty_set(m().get_sort(arg1)));
    return BR_REWRITE3;
}

void array_rewriter::mk_eq(expr* e, expr* lhs, expr* rhs, expr_ref_vector& fmls) {
    expr_ref tmp1(m()), tmp2(m());
    expr_ref a(m()), v(m());
    expr_ref_vector args0(m()), args(m());
    while (m_util.is_store_ext(e, a, args0, v)) {                                        
        args.reset();
        args.push_back(lhs);
        args.append(args0);
        mk_select(args.size(), args.c_ptr(), tmp1);                     
        args[0] = rhs;                                                  
        mk_select(args.size(), args.c_ptr(), tmp2);                     
        fmls.push_back(m().mk_eq(tmp1, tmp2));    
        e = a;
    }                                                
}

bool array_rewriter::has_index_set(expr* e, expr_ref& else_case, vector<expr_ref_vector>& stores) {
    expr_ref_vector args(m());
    expr_ref a(m()), v(m());
    a = e;
    while (m_util.is_store_ext(e, a, args, v)) {
        args.push_back(v);
        stores.push_back(args);
        e = a;
    }
    if (m_util.is_const(e, e)) {
        else_case = e;
        return true;
    }
    if (is_lambda(e)) {
        quantifier* q = to_quantifier(e);
        e = q->get_expr();
        unsigned num_idxs = q->get_num_decls();
        expr* e1, *e3, *store_val;
        if (!is_ground(e) && m().is_or(e)) {
            for (expr* arg : *to_app(e)) {
                if (!add_store(args, num_idxs, arg, m().mk_true(), stores)) {
                    return false;
                }                            
            }
            else_case = m().mk_false();
            return true;
        }
        if (!is_ground(e) && m().is_and(e)) {
            for (expr* arg : *to_app(e)) {
                if (!add_store(args, num_idxs, arg, m().mk_true(), stores)) {
                    return false;
                }                            
            }
            else_case = m().mk_true();
            return true;
        }
        while (!is_ground(e) && m().is_ite(e, e1, store_val, e3) && is_ground(store_val)) {            
            if (!add_store(args, num_idxs, e1, store_val, stores)) {
                return false;
            }            
            e = e3;
        }
        else_case = e;
        return is_ground(e);
    }
    return false;
}

bool array_rewriter::add_store(expr_ref_vector& args, unsigned num_idxs, expr* e, expr* store_val, vector<expr_ref_vector>& stores) {

    expr* e1, *e2;
    ptr_vector<expr> eqs;    
    args.reset();
    args.resize(num_idxs + 1, nullptr);
    bool is_not = m().is_bool(store_val) && m().is_not(e, e);

    eqs.push_back(e);
    for (unsigned i = 0; i < eqs.size(); ++i) {
        e = eqs[i];
        if (m().is_and(e)) {
            eqs.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            continue;
        }
        if (m().is_eq(e, e1, e2)) {
            if (is_var(e2)) {
                std::swap(e1, e2);
            }
            if (is_var(e1) && is_ground(e2)) {
                unsigned idx = to_var(e1)->get_idx();
                args[num_idxs - idx - 1] = e2;
            }
            else {
                return false;
            }
            continue;
        }    
        return false;
    }
    for (unsigned i = 0; i < num_idxs; ++i) {
        if (!args.get(i)) return false;
    }
    if (is_not) {
        store_val = mk_not(m(), store_val);
    }
    args[num_idxs] = store_val;
    stores.push_back(args);
    return true;
}

bool array_rewriter::is_expandable_store(expr* s) {
    unsigned count = s->get_ref_count();
    unsigned depth = 0;
    while (m_util.is_store(s)) {
        s = to_app(s)->get_arg(0);
        count += s->get_ref_count();
        depth++;
    }
    return (depth >= 3 && count <= depth*2);
}

expr_ref array_rewriter::expand_store(expr* s) {
    ptr_vector<app> stores;
    expr_ref result(m());
    while (m_util.is_store(s)) {
        stores.push_back(to_app(s));
        s = to_app(s)->get_arg(0);
    }
    stores.reverse();
    expr_ref_vector args(m()), eqs(m());
    ptr_vector<sort> sorts;
    svector<symbol> names;
    sort* srt = m().get_sort(s);    
    args.push_back(s);
    for (unsigned i = get_array_arity(srt); i-- > 0; ) {
        args.push_back(m().mk_var(i, get_array_domain(srt, i)));
        sorts.push_back(get_array_domain(srt, i));
        names.push_back(symbol(i));
    }
    names.reverse();
    sorts.reverse();
    result = m_util.mk_select(args);
    for (app* st : stores) {
        eqs.reset();
        for (unsigned i = 1; i < args.size(); ++i) {
            eqs.push_back(m().mk_eq(args.get(i), st->get_arg(i)));
        }
        result = m().mk_ite(mk_and(eqs), st->get_arg(args.size()), result);
    }
    result = m().mk_lambda(sorts.size(), sorts.c_ptr(), names.c_ptr(), result);
    return result;
}

br_status array_rewriter::mk_eq_core(expr * lhs, expr * rhs, expr_ref & result) {
    TRACE("array_rewriter", tout << mk_pp(lhs, m()) << " " << mk_pp(rhs, m()) << "\n";);
    expr* v = nullptr;
    if (m_util.is_const(rhs) && is_lambda(lhs)) {
        std::swap(lhs, rhs);
    }
    if (m_util.is_const(lhs, v) && is_lambda(rhs)) {
        quantifier* lam = to_quantifier(rhs);
        expr_ref e(m().mk_eq(lam->get_expr(), v), m());
        result = m().update_quantifier(lam, quantifier_kind::forall_k, e);
        return BR_REWRITE2; 
    }
    expr_ref lh1(m()), rh1(m());
    if (m_expand_nested_stores) {
        if (is_expandable_store(lhs)) {
            lh1 = expand_store(lhs);        
        }
        if (is_expandable_store(rhs)) {
            rh1 = expand_store(rhs);        
        }
        if (lh1 || rh1) {
            if (!lh1) lh1 = lhs;
            if (!rh1) rh1 = rhs;
            result = m().mk_eq(lh1, rh1);
            return BR_REWRITE_FULL;
        }
    }

    if (!m_expand_store_eq) {
        return BR_FAILED;
    }
    expr_ref_vector fmls(m());

#if 0
    // lambda friendly version of array equality rewriting.
    vector<expr_ref_vector> indices;
    expr_ref lhs0(m()), rhs0(m());
    expr_ref tmp1(m()), tmp2(m());
    if (has_index_set(lhs, lhs0, indices) && has_index_set(rhs, rhs0, indices) && lhs0 == rhs0) {
        expr_ref_vector args(m());
        for (auto const& idxs : indices) {
            args.reset();
            args.push_back(lhs);
            idxs.pop_back();
            args.append(idxs);            
            mk_select(args.size(), args.c_ptr(), tmp1);
            args[0] = rhs;
            mk_select(args.size(), args.c_ptr(), tmp2);
            fmls.push_back(m().mk_eq(tmp1, tmp2));
        }
    }
#endif

    expr* lhs1 = lhs;
    while (m_util.is_store(lhs1)) {
        lhs1 = to_app(lhs1)->get_arg(0);
    }
    expr* rhs1 = rhs;
    while (m_util.is_store(rhs1)) {
        rhs1 = to_app(rhs1)->get_arg(0);
    }
    if (lhs1 != rhs1) {
        return BR_FAILED;
    }

    mk_eq(lhs, lhs, rhs, fmls);
    mk_eq(rhs, lhs, rhs, fmls);
    result = m().mk_and(fmls.size(), fmls.c_ptr());
    return BR_REWRITE_FULL;
}
