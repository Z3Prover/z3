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
#include "ast_util.h"
#include "ast_smt_pp.h"


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

expr_ref pb_rewriter::translate_pb2lia(obj_map<expr,expr*>& vars, expr* fml) {
    pb_util util(m());
    arith_util a(m());
    expr_ref result(m()), tmp(m());
    expr_ref_vector es(m());
    expr*const* args = to_app(fml)->get_args();
    unsigned sz = to_app(fml)->get_num_args();
    for (unsigned i = 0; i < sz; ++i) {
        expr* e = args[i];
        if (m().is_not(e, e)) {
            es.push_back(a.mk_sub(a.mk_numeral(rational(1),true),vars.find(e)));
        }
        else {
            es.push_back(vars.find(e));
        }
    }

    if (util.is_at_most_k(fml) || util.is_at_least_k(fml)) {
        if (es.empty()) {
            tmp = a.mk_numeral(rational(0), true);
        }
        else {
            tmp = a.mk_add(es.size(), es.c_ptr());
        }
        if (util.is_at_most_k(fml)) {
            result = a.mk_le(tmp, a.mk_numeral(util.get_k(fml), false));
        }
        else {
            result = a.mk_ge(tmp, a.mk_numeral(util.get_k(fml), false));
        }
    }
    else if (util.is_le(fml) || util.is_ge(fml) || util.is_eq(fml)) {
        for (unsigned i = 0; i < sz; ++i) {
            es[i] = a.mk_mul(a.mk_numeral(util.get_coeff(fml, i),false), es[i].get());
        }
        if (es.empty()) {
            tmp = a.mk_numeral(rational(0), true);
        }
        else {
            tmp = a.mk_add(es.size(), es.c_ptr());
        }
        if (util.is_le(fml)) {
            result = a.mk_le(tmp, a.mk_numeral(util.get_k(fml), false));
        }
        else if (util.is_ge(fml)) {
            result = a.mk_ge(tmp, a.mk_numeral(util.get_k(fml), false));
        }
        else {
            result = m().mk_eq(tmp, a.mk_numeral(util.get_k(fml), false));
        }
    }
    else {
        result = fml;
    }
    return result;
}

expr_ref pb_rewriter::mk_validate_rewrite(app_ref& e1, app_ref& e2) {
    ast_manager& m = e1.get_manager();
    arith_util a(m);
    symbol name;
    obj_map<expr,expr*> vars;
    expr_ref_vector trail(m), fmls(m);    
    unsigned sz = to_app(e1)->get_num_args();
    expr*const*args = to_app(e1)->get_args();
    for (unsigned i = 0; i < sz; ++i) {
        expr* e = args[i];
        if (m.is_true(e)) {
            if (!vars.contains(e)) {
                trail.push_back(a.mk_numeral(rational(1), true));
                vars.insert(e, trail.back());            
            }
            continue;
        }
        if (m.is_false(e)) {
            if (!vars.contains(e)) {
                trail.push_back(a.mk_numeral(rational(0), true));
                vars.insert(e, trail.back());            
            }
            continue;
        }

        std::ostringstream strm;
        strm << "x" << i;
        name = symbol(strm.str().c_str());
        trail.push_back(m.mk_const(name, a.mk_int()));
        expr* x = trail.back();
        m.is_not(e,e);
        vars.insert(e, x);
        fmls.push_back(a.mk_le(a.mk_numeral(rational(0), true), x));
        fmls.push_back(a.mk_le(x, a.mk_numeral(rational(1), true)));
    }
    expr_ref tmp(m);
    expr_ref fml1 = translate_pb2lia(vars, e1);
    expr_ref fml2 = translate_pb2lia(vars, e2);    
    tmp = m.mk_not(m.mk_eq(fml1, fml2));
    fmls.push_back(tmp);
    tmp = m.mk_and(fmls.size(), fmls.c_ptr());
    return tmp;
}

static unsigned s_lemma = 0;

void pb_rewriter::validate_rewrite(func_decl* f, unsigned sz, expr*const* args, expr_ref& fml) {
    ast_manager& m = fml.get_manager();
    app_ref tmp1(m), tmp2(m);
    tmp1 = m.mk_app(f, sz, args);
    tmp2 = to_app(fml);
    expr_ref tmp = mk_validate_rewrite(tmp1, tmp2);
    dump_pb_rewrite(tmp);
}

void pb_rewriter::dump_pb_rewrite(expr* fml) {
    std::ostringstream strm;
    strm << "pb_rewrite_" << (s_lemma++) << ".smt2";
    std::ofstream out(strm.str().c_str());    
    ast_smt_pp pp(m());
    pp.display_smt2(out, fml);    
    out.close();
}

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
    default: {
        bool all_unit = true;
        unsigned sz = vec.size();
        m_args.reset();
        m_coeffs.reset();
        for (unsigned i = 0; i < sz; ++i) {
            m_args.push_back(vec[i].first);
            m_coeffs.push_back(vec[i].second);
            all_unit &= m_coeffs.back().is_one();
        }
        if (is_eq) {
            if (sz == 0) {
                result = k.is_zero()?m.mk_true():m.mk_false();
            }
            else {
                result = m_util.mk_eq(sz, m_coeffs.c_ptr(), m_args.c_ptr(), k);
            }
        }
        else if (all_unit && k.is_one()) {
            result = mk_or(m, sz, m_args.c_ptr());
        }
        else if (all_unit && k == rational(sz)) {
            result = mk_and(m, sz, m_args.c_ptr());
        }
        else {
            result = m_util.mk_ge(sz, m_coeffs.c_ptr(), m_args.c_ptr(), k);
        }
        break;
    }
    }
    TRACE("pb",
          expr_ref tmp(m);
          tmp = m.mk_app(f, num_args, args);
          tout << tmp << "\n";
          tout << result << "\n";
          );

    TRACE("pb_validate",
          validate_rewrite(f, num_args, args, result););
          
    return BR_DONE;
}


