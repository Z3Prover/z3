#include "expr_delta.h"
#include "ast_pp.h"

expr_delta::expr_delta(ast_manager& m) : m_manager(m), m_exprs(m) {}

void expr_delta::assert_cnstr(expr* n) {
    m_exprs.push_back(n);
}

bool expr_delta::delta_dfs(unsigned n, expr_ref_vector& result) {
    return delta_dfs(n, m_exprs.size(), m_exprs.c_ptr(), result);
}

bool expr_delta::delta_dfs(unsigned& n, unsigned sz, expr* const* exprs, expr_ref_vector& result) {
    expr_ref r(m_manager);
    for (unsigned i = 0; i < sz; ++i) {
        expr* e = exprs[i];
        if (delta_dfs(n, e, r)) {
            result.push_back(r.get());
            for (unsigned j = i+1; j < sz; ++j) {
                result.push_back(exprs[j]);
            }
            return true;
        }
        else {
            result.push_back(e);
        }
    }
    return false;
}

bool expr_delta::delta_dfs(unsigned& n, app* a, expr_ref& result) {
    expr_ref_vector args(m_manager);
    if (delta_dfs(n, a->get_num_args(), a->get_args(), args)) {
        result = m_manager.mk_app(a->get_decl(), args.size(), args.c_ptr());
        return true;
    }
    else {
        return false;
    }        
}

bool expr_delta::delta_dfs(unsigned& n, expr* e, expr_ref& result) {
    ast_manager& m = m_manager;
    if (m.is_true(e) || m.is_false(e)) {
        return false;
    }
    if (n == 0 && m.is_bool(e)) {
        result = m.mk_true();
        return true;
    }
    else if (n == 1 && m.is_bool(e)) {
        result = m.mk_false();
        return true;
    }
    else if (is_app(e)) {        
        if (m.is_bool(e)) {
            SASSERT(n >= 2);
            n -= 2;
        }
        return delta_dfs(n, to_app(e), result);
    }
    else if (is_quantifier(e)) {
        SASSERT(n >= 2);
        n -= 2;
        quantifier* q = to_quantifier(e);
        if (delta_dfs(n, q->get_expr(), result)) {
            result = m.update_quantifier(q, result.get());
            return true;
        }
        else {
            return false;
        }
    }
    return false;
}

