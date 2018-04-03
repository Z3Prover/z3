/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    datatype_rewriter.cpp

Abstract:

    Basic rewriting rules for Datatypes.

Author:

    Leonardo (leonardo) 2011-04-06

Notes:

--*/
#include "ast/rewriter/datatype_rewriter.h"

br_status datatype_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    switch(f->get_decl_kind()) {
    case OP_DT_CONSTRUCTOR: return BR_FAILED;
    case OP_DT_RECOGNISER:
        SASSERT(num_args == 1);
        result = m_util.mk_is(m_util.get_recognizer_constructor(f), args[0]);
        return BR_REWRITE1;
    case OP_DT_IS:
        //
        // simplify is_cons(cons(x,y)) -> true
        // simplify is_cons(nil) -> false
        //
        SASSERT(num_args == 1);
        if (!is_app(args[0]) || !m_util.is_constructor(to_app(args[0])))
            return BR_FAILED;
        if (to_app(args[0])->get_decl() == m_util.get_recognizer_constructor(f))
            result = m().mk_true();
        else
            result = m().mk_false();
        return BR_DONE;
    case OP_DT_ACCESSOR: {
        // 
        // simplify head(cons(x,y)) -> x
        // 
        SASSERT(num_args == 1);
        if (!is_app(args[0]) || !m_util.is_constructor(to_app(args[0])))
            return BR_FAILED;
        
        app * a = to_app(args[0]);
        func_decl * c_decl = a->get_decl();
        if (c_decl != m_util.get_accessor_constructor(f))
            return BR_FAILED;
        ptr_vector<func_decl> const & acc = *m_util.get_constructor_accessors(c_decl);
        SASSERT(acc.size() == a->get_num_args());
        unsigned num = acc.size();
        for (unsigned i = 0; i < num; ++i) {
            if (f == acc[i]) {
                // found it.
                result = a->get_arg(i);
                return BR_DONE;
            }
        }
        UNREACHABLE();
        break;
    }
    case OP_DT_UPDATE_FIELD: {
        SASSERT(num_args == 2);
        if (!is_app(args[0]) || !m_util.is_constructor(to_app(args[0])))
            return BR_FAILED;
        app * a = to_app(args[0]);
        func_decl * c_decl = a->get_decl();
        if (c_decl != m_util.get_accessor_constructor(f)) {
            result = a;
            return BR_DONE;
        }
        ptr_vector<func_decl> const & acc = *m_util.get_constructor_accessors(c_decl);
        SASSERT(acc.size() == a->get_num_args());
        unsigned num = acc.size();
        ptr_buffer<expr> new_args;
        for (unsigned i = 0; i < num; ++i) {
            
            if (f == acc[i]) {
                new_args.push_back(args[1]);
            }
            else {
                new_args.push_back(a->get_arg(i));
            }
        }
        result = m().mk_app(c_decl, num, new_args.c_ptr());
        return BR_DONE;        
    }
    default:
        UNREACHABLE();
    }
    
    return BR_FAILED;
}

br_status datatype_rewriter::mk_eq_core(expr * lhs, expr * rhs, expr_ref & result) {
    if (!is_app(lhs) || !is_app(rhs) || !m_util.is_constructor(to_app(lhs)) || !m_util.is_constructor(to_app(rhs)))
        return BR_FAILED;
    if (to_app(lhs)->get_decl() != to_app(rhs)->get_decl()) {
        result = m().mk_false();
        return BR_DONE;
    }

    // Remark: In datatype_simplifier_plugin, we used
    // m_basic_simplifier to create '=' and 'and' applications in the
    // following code. This trick not guarantee that the final expression
    // will be fully simplified. 
    //
    // Example:
    // The assertion  
    // (assert (= (cons a1 (cons a2 (cons a3 (cons (+ a4 1) (cons (+ a5 c5) (cons a6 nil))))))
    //         (cons b1 (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 nil))))))))
    // 
    // After applying asserted_formulas::reduce(), the following formula was generated.
    //
    //   (= a1 b1)
    //   (= a2 b2)
    //   (= a3 b3)
    //   (= (+ a4 (* (- 1) b4)) (- 1))
    //   (= (+ c5 a5) b5)                    <<< NOT SIMPLIFIED WITH RESPECT TO ARITHMETIC
    //   (= (cons a6 nil) (cons b6 nil)))    <<< NOT SIMPLIFIED WITH RESPECT TO DATATYPE theory
    //
    // Note that asserted_formulas::reduce() applied the simplier many times.
    // After the first simplification step we had:
    //  (= a1 b1)
    //  (= (cons a2 (cons a3 (cons (+ a4 1) (cons (+ a5 c5) (cons a6 nil))))))
    //     (cons b2 (cons b3 (cons b4 (cons b5 (cons b6 nil))))))

    ptr_buffer<expr> eqs;
    unsigned num = to_app(lhs)->get_num_args();
    SASSERT(num == to_app(rhs)->get_num_args());
    for (unsigned i = 0; i < num; ++i) {            
        eqs.push_back(m().mk_eq(to_app(lhs)->get_arg(i), to_app(rhs)->get_arg(i)));
    }
    result = m().mk_and(eqs.size(), eqs.c_ptr());
    return BR_REWRITE2;
}
