/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_rewriter.cpp

Abstract:

    Basic rewriting rules for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-14-12

Notes:

--*/

#include "pb_rewriter.h"
#include "pb_rewriter_def.h"
#include "ast_pp.h"


class pb_ast_rewriter_util {
    ast_manager& m;
    expr_ref_vector m_refs;
public:

    typedef std::pair<expr*, rational> arg_t;
    typedef vector<arg_t> args_t;
    typedef rational numeral;

    pb_ast_rewriter_util(ast_manager& m): m(m), m_refs(m) {}

    expr* negate(expr* e) {
        if (m.is_true(e)) {
            return m.mk_false();
        }
        if (m.is_false(e)) {
            return m.mk_true();
        }
        if (m.is_not(e, e)) {
            return e;
        }
        m_refs.push_back(m.mk_not(e));
        return m_refs.back();
    }

    void display(std::ostream& out, expr* e) {
        out << mk_pp(e, m);
    }

    bool is_negated(expr* e) const {
        return m.is_not(e);
    }

    bool is_true(expr* e) const {
        return m.is_true(e);
    }

    bool is_false(expr* e) const {
        return m.is_false(e);
    }

    struct compare {
        bool operator()(std::pair<expr*,rational> const& a,
                        std::pair<expr*,rational> const& b) {
            return a.first->get_id() < b.first->get_id();
        }

    };
};


br_status pb_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    ast_manager& m = result.get_manager();
    rational sum(0), maxsum(0);
    for (unsigned i = 0; i < num_args; ++i) {
        if (m.is_true(args[i])) {
            sum += m_util.get_coeff(f, i);
            maxsum += m_util.get_coeff(f, i);
        }
        else if (!m.is_false(args[i])) {
            maxsum += m_util.get_coeff(f, i);            
        }
    }
    rational k = m_util.get_k(f);

    vector<std::pair<expr*,rational> > vec;
    for (unsigned i = 0; i < num_args; ++i) {
        vec.push_back(std::make_pair(args[i], m_util.get_coeff(f, i)));
    }
    
    switch(f->get_decl_kind()) {
    case OP_AT_MOST_K:
    case OP_PB_LE:
        for (unsigned i = 0; i < num_args; ++i) {
            vec[i].second.neg();
        }
        k.neg();
        break;
    case OP_AT_LEAST_K:
    case OP_PB_GE:
    case OP_PB_EQ:
        break;
    default:
        UNREACHABLE();
        return BR_FAILED;
    }    

    bool is_eq = f->get_decl_kind() == OP_PB_EQ;
    
    pb_ast_rewriter_util pbu(m);
    pb_rewriter_util<pb_ast_rewriter_util> util(pbu);

    util.unique(vec, k, is_eq);
    lbool is_sat = util.normalize(vec, k, is_eq);
    util.prune(vec, k, is_eq);
    switch (is_sat) {
    case l_true:
        result = m.mk_true();
        break;
    case l_false:
        result = m.mk_false();
        break;
    default:
        m_args.reset();
        m_coeffs.reset();
        for (unsigned i = 0; i < vec.size(); ++i) {
            m_args.push_back(vec[i].first);
            m_coeffs.push_back(vec[i].second);
        }
        if (is_eq) {
            result = m_util.mk_eq(vec.size(), m_coeffs.c_ptr(), m_args.c_ptr(), k);
        }
        else {
            result = m_util.mk_ge(vec.size(), m_coeffs.c_ptr(), m_args.c_ptr(), k);
        }
        break;
    }
    TRACE("pb",
          expr_ref tmp(m);
          tmp = m.mk_app(f, num_args, args);
          tout << tmp << "\n";
          tout << result << "\n";);
          
    return BR_DONE;
}


