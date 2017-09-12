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
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"

void array_rewriter::updt_params(params_ref const & _p) {
    array_rewriter_params p(_p);
    m_sort_store = p.sort_store();
    m_expand_select_store = p.expand_select_store();
    m_expand_store_eq = p.expand_store_eq();
    m_expand_select_ite = false;
}

void array_rewriter::get_param_descrs(param_descrs & r) {
    array_rewriter_params::collect_param_descrs(r);
}

br_status array_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    TRACE("array_rewriter", tout << mk_pp(f, m()) << "\n";
          for (unsigned i = 0; i < num_args; ++i) {
              tout << mk_pp(args[i], m()) << "\n";
          });
    switch (f->get_decl_kind()) {
    case OP_SELECT:
        return mk_select_core(num_args, args, result);
    case OP_STORE:
        return mk_store_core(num_args, args, result);
    case OP_ARRAY_MAP:
        SASSERT(f->get_num_parameters() == 1);
        SASSERT(f->get_parameter(0).is_ast());
        SASSERT(is_func_decl(f->get_parameter(0).get_ast()));
        return mk_map_core(to_func_decl(f->get_parameter(0).get_ast()), num_args, args, result);
    case OP_SET_UNION:
        return mk_set_union(num_args, args, result);
    case OP_SET_INTERSECT:
        return mk_set_intersect(num_args, args, result);
    case OP_SET_SUBSET: 
        SASSERT(num_args == 2);
        return mk_set_subset(args[0], args[1], result);
    case OP_SET_COMPLEMENT:
        SASSERT(num_args == 1);
        return mk_set_complement(args[0], result);
    case OP_SET_DIFFERENCE:
        SASSERT(num_args == 2);
        return mk_set_difference(args[0], args[1], result);
    default:
        return BR_FAILED;
    }
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

    if (m_util.is_as_array(args[0])) {
        // select(as-array[f], I) --> f(I)
        func_decl * f = m_util.get_as_array_func_decl(to_app(args[0]));
        result = m().mk_app(f, num_args - 1, args + 1);
        return BR_REWRITE1;
    }

    expr* c, *th, *el;
    if (m_expand_select_ite && m().is_ite(args[0], c, th, el)) {
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

br_status array_rewriter::mk_map_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args >= 0);
    bool is_store0 = m_util.is_store(args[0]);
    bool is_const0 = m_util.is_const(args[0]);
    if (num_args == 1) {
        //
        // map_f (store a j v) = (store (map_f a) j (f v)) 
        //
        if (is_store0) {
            app * store_expr = to_app(args[0]);
            unsigned num_args = store_expr->get_num_args();
            SASSERT(num_args >= 3);
            expr * a = store_expr->get_arg(0);
            expr * v = store_expr->get_arg(num_args-1);
            
            ptr_buffer<expr> new_args;
            
            new_args.push_back(m_util.mk_map(f, 1, &a)); // (map_f a)
            new_args.append(num_args - 2, store_expr->get_args() + 1); // j
            new_args.push_back(m().mk_app(f, v));   // (f v)
            
            result = m().mk_app(get_fid(), OP_STORE, new_args.size(), new_args.c_ptr());
            return BR_REWRITE2;
        }
        
        //
        // map_f (const v) = (const (f v))
        //
        if (is_const0) {
            expr * fv = m().mk_app(f, to_app(args[0])->get_arg(0));
            result = m_util.mk_const_array(m().get_sort(args[0]), fv);
            return BR_REWRITE2;
        }
        return BR_FAILED;
    }

    SASSERT(num_args > 1);
    
    if (is_store0) {
        unsigned num_indices = to_app(args[0])->get_num_args() - 2;
        unsigned i;
        for (i = 1; i < num_args; i++) {
            if (!m_util.is_store(args[i]))
                break;
            unsigned j;
            for (j = 1; j < num_indices+1; j++) {
                if (to_app(args[0])->get_arg(j) != to_app(args[i])->get_arg(j))
                    break;
            }
            if (j < num_indices+1)
                break;
        }
        //
        // map_f (store a_1 j v_1) ... (store a_n j v_n) --> (store (map_f a_1 ... a_n) j (f v_1 ... v_n))
        //
        if (i == num_args) {
            ptr_buffer<expr> arrays;
            ptr_buffer<expr> values;
            for (unsigned i = 0; i < num_args; i++) {
                arrays.push_back(to_app(args[i])->get_arg(0));
                values.push_back(to_app(args[i])->get_arg(num_indices+1));
            }
            ptr_buffer<expr> new_args;
            new_args.push_back(m_util.mk_map(f, arrays.size(), arrays.c_ptr()));
            new_args.append(num_indices, to_app(args[0])->get_args() + 1);
            new_args.push_back(m().mk_app(f, values.size(), values.c_ptr()));
            result = m().mk_app(get_fid(), OP_STORE, new_args.size(), new_args.c_ptr());
            return BR_REWRITE2;
        }
        return BR_FAILED;
    }

    if (is_const0) {
        unsigned i;
        for (i = 1; i < num_args; i++) {
            if (!m_util.is_const(args[i]))
                break;
        }
        if (i == num_args) {
            //
            // map_f (const v_1) ... (const v_n) = (const (f v_1 ... v_n))
            //
            ptr_buffer<expr> values;
            for (unsigned i = 0; i < num_args; i++) {
                values.push_back(to_app(args[i])->get_arg(0));
            }
            
            expr * fv = m().mk_app(f, values.size(), values.c_ptr());
            sort * in_s = get_sort(args[0]);
            ptr_vector<sort> domain;
            unsigned domain_sz = get_array_arity(in_s);
            for (unsigned i = 0; i < domain_sz; i++) 
                domain.push_back(get_array_domain(in_s, i));
            sort_ref out_s(m());
            out_s = m_util.mk_array_sort(domain_sz, domain.c_ptr(), f->get_range());
            parameter p(out_s.get());
            result = m().mk_app(get_fid(), OP_CONST_ARRAY, 1, &p, 1, &fv);
            return BR_REWRITE2;
        }
        return BR_FAILED;
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
    return mk_map_core(m().mk_not_decl(), 1, &arg, result);
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

br_status array_rewriter::mk_eq_core(expr * lhs, expr * rhs, expr_ref & result) {
    if (!m_expand_store_eq) {
        return BR_FAILED;
    }
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
    ptr_buffer<expr> fmls, args;
    expr* e;
    expr_ref tmp1(m()), tmp2(m());
#define MK_EQ()                                                         \
    while (m_util.is_store(e)) {                                        \
        args.push_back(lhs);                                            \
        args.append(to_app(e)->get_num_args()-2,to_app(e)->get_args()+1); \
        mk_select(args.size(), args.c_ptr(), tmp1);                     \
        args[0] = rhs;                                                  \
        mk_select(args.size(), args.c_ptr(), tmp2);                     \
        fmls.push_back(m().mk_eq(tmp1, tmp2));                          \
        e = to_app(e)->get_arg(0);                                      \
        args.reset();                                                   \
    }                                                \
    
    e = lhs;
    MK_EQ();
    e = rhs;
    MK_EQ();
    result = m().mk_and(fmls.size(), fmls.c_ptr());
    return BR_REWRITE_FULL;
}
