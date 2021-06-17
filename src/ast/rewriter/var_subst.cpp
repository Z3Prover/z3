/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    var_subst.cpp

Abstract:

    Variable substitution.

Author:

    Leonardo (leonardo) 2008-01-10

Notes:

--*/
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/well_sorted.h"
#include "ast/for_each_expr.h"

expr_ref var_subst::operator()(expr * n, unsigned num_args, expr * const * args) {
    ast_manager& m = m_reducer.m();
    expr_ref result(m);
    if (is_ground(n) || num_args == 0) {
        result = n;
        //application does not have free variables or nested quantifiers.
        //There is no need to print the bindings here?
        SCTRACE("bindings", is_trace_enabled("coming_from_quant"),
                tout << "(ground)\n";
                        for (unsigned i = 0; i < num_args; i++) {
                            if (args[i]) {
                                tout << i << ": " << mk_ismt2_pp(args[i], result.m()) << ";\n";
                            }
                        }
                        tout.flush(););

        return result;
    }
    if (has_quantifiers(n)) {
        expr_safe_replace rep(m);
        for (unsigned k = 0; k < num_args; ++k) {
            expr* arg = args[k];
            if (arg)
                rep.insert(m.mk_var(m_std_order ? num_args - k - 1 : k, arg->get_sort()), arg);
        }
        rep(n, result);
        return result;
    }
    SASSERT(is_well_sorted(result.m(), n));
    m_reducer.reset();
    if (m_std_order)
        m_reducer.set_inv_bindings(num_args, args);
    else
        m_reducer.set_bindings(num_args, args);
    m_reducer(n, result);
    SASSERT(is_well_sorted(m, result));
    TRACE("var_subst_bug",
          tout << "m_std_order: " << m_std_order << "\n" << mk_ismt2_pp(n, m) << "\nusing\n";
          for (unsigned i = 0; i < num_args; i++) tout << mk_ismt2_pp(args[i], m) << "\n";
          tout << "\n------>\n";
          tout << result << "\n";);
    return result;
}

unused_vars_eliminator::unused_vars_eliminator(ast_manager & m, params_ref const & params) :
    m(m), m_subst(m), m_params(params)
{
    m_ignore_patterns_on_ground_qbody = m_params.get_bool("ignore_patterns_on_ground_qbody", true);
}

expr_ref unused_vars_eliminator::operator()(quantifier* q) {
    expr_ref result(m);
    SASSERT(is_well_sorted(m, q));
    TRACE("elim_unused_vars", tout << expr_ref(q, m) << "\n";);
    if (is_lambda(q)) {
        result = q;
        return result;
    }
    if (m_ignore_patterns_on_ground_qbody && is_ground(q->get_expr())) {
        // Ignore patterns if the body is a ground formula.
        result = q->get_expr();
        return result;
    }
    if (!q->may_have_unused_vars()) {
        result = q;
        return result;
    }
    unsigned num_decls = q->get_num_decls();
    m_used.reset();
    m_used.set_num_decls(num_decls);
    m_used.process(q->get_expr());
    unsigned num_patterns = q->get_num_patterns();
    for (unsigned i = 0; i < num_patterns; i++)
        m_used.process(q->get_pattern(i));
    unsigned num_no_patterns = q->get_num_no_patterns();
    for (unsigned i = 0; i < num_no_patterns; i++)
        m_used.process(q->get_no_pattern(i));

    
    if (m_used.uses_all_vars(num_decls)) {
        q->set_no_unused_vars();
        result = q;
        return result;
    }

    ptr_buffer<sort>  used_decl_sorts;
    buffer<symbol>    used_decl_names;
    for (unsigned i = 0; i < num_decls; ++i) {
        if (m_used.contains(num_decls - i - 1)) {
            used_decl_sorts.push_back(q->get_decl_sort(i));
            used_decl_names.push_back(q->get_decl_name(i));
        }
    }

    unsigned         num_removed = 0;
    expr_ref_buffer  var_mapping(m);
    int              next_idx = 0;
    unsigned         sz = m_used.get_max_found_var_idx_plus_1();

    for (unsigned i = 0; i < num_decls; ++i) {
        sort * s = m_used.contains(i);
        if (s) {
            var_mapping.push_back(m.mk_var(next_idx, s));
            next_idx++;
        }
        else {
            num_removed++;
            var_mapping.push_back(nullptr);
        }
    }
    // (VAR 0) is in the first position of var_mapping.

    for (unsigned i = num_decls; i < sz; i++) {
        sort * s = m_used.contains(i);
        if (s)
            var_mapping.push_back(m.mk_var(i - num_removed, s));
        else
            var_mapping.push_back(nullptr);
    }

    // Remark:
    // (VAR 0) should be in the last position of var_mapping.
    // ...
    // (VAR (var_mapping.size() - 1)) should be in the first position.
    std::reverse(var_mapping.data(), var_mapping.data() + var_mapping.size());

    expr_ref  new_expr(m);

    new_expr = m_subst(q->get_expr(), var_mapping.size(), var_mapping.data());

    if (num_removed == num_decls) {
        result = new_expr;
        return result;
    }

    expr_ref_buffer new_patterns(m);
    expr_ref_buffer new_no_patterns(m);

    for (unsigned i = 0; i < num_patterns; i++) {
        new_patterns.push_back(m_subst(q->get_pattern(i), var_mapping.size(), var_mapping.data()));
    }
    for (unsigned i = 0; i < num_no_patterns; i++) {
        new_no_patterns.push_back(m_subst(q->get_no_pattern(i), var_mapping.size(), var_mapping.data()));
    }

    result = m.mk_quantifier(q->get_kind(),
                             used_decl_sorts.size(),
                             used_decl_sorts.data(),
                             used_decl_names.data(),
                             new_expr,
                             q->get_weight(),
                             q->get_qid(),
                             q->get_skid(),
                             num_patterns,
                             new_patterns.data(),
                             num_no_patterns,
                             new_no_patterns.data());
    to_quantifier(result)->set_no_unused_vars();
    SASSERT(is_well_sorted(m, result));
    return result;
}

expr_ref elim_unused_vars(ast_manager & m, quantifier * q, params_ref const & params) {
    unused_vars_eliminator el(m, params);
    expr_ref result = el(q);
    TRACE("elim_unused_vars", tout << expr_ref(q, m) << " -> " << result << "\n";);
    return result;
}

expr_ref instantiate(ast_manager & m, quantifier * q, expr * const * exprs) {
    var_subst subst(m);
    expr_ref new_expr(m), result(m);
    new_expr = subst(q->get_expr(), q->get_num_decls(), exprs);
    TRACE("var_subst", tout << mk_pp(q, m) << "\n" << new_expr << "\n";);
    inv_var_shifter shift(m);
    shift(new_expr, q->get_num_decls(), result);
    SASSERT(is_well_sorted(m, result));
    TRACE("instantiate_bug", tout << mk_ismt2_pp(q, m) << "\nusing\n";
          for (unsigned i = 0; i < q->get_num_decls(); i++) tout << mk_ismt2_pp(exprs[i], m) << "\n";
          tout << "\n----->\n" << mk_ismt2_pp(result, m) << "\n";);
    return result;
}

static void get_free_vars_offset(expr_sparse_mark& mark, ptr_vector<expr>& todo, unsigned offset, expr* e, ptr_vector<sort>& sorts) {
    todo.push_back(e);
    while (!todo.empty()) {
        e = todo.back();
        todo.pop_back();
        if (mark.is_marked(e)) {
            continue;
        }
        mark.mark(e, true);
        switch(e->get_kind()) {
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(e);
            expr_sparse_mark mark1;
            ptr_vector<expr> todo1;
            get_free_vars_offset(mark1, todo1, offset+q->get_num_decls(), q->get_expr(), sorts);
            break;
        }
        case AST_VAR: {
            var* v = to_var(e);
            if (v->get_idx() >= offset) {
                unsigned idx = v->get_idx()-offset;
                if (sorts.size() <= idx) {
                    sorts.resize(idx+1);
                }
                if (!sorts[idx]) {
                    sorts[idx] = v->get_sort();
                }
                SASSERT(sorts[idx] == v->get_sort());
            }
            break;
        }
        case AST_APP: {
            for (expr* arg : *to_app(e))  
                todo.push_back(arg);            
            break;
        }
        default:
            UNREACHABLE();
        }
    }
}


void get_free_vars(expr* e, ptr_vector<sort>& sorts) {
    expr_sparse_mark mark;
    ptr_vector<expr> todo;
    get_free_vars_offset(mark, todo, 0, e, sorts);
}

void get_free_vars(expr_sparse_mark& mark, ptr_vector<expr>& todo, expr* e, ptr_vector<sort>& sorts) {
    get_free_vars_offset(mark, todo, 0, e, sorts);
}

void expr_free_vars::reset() {
    m_mark.reset();
    m_sorts.reset();
    SASSERT(m_todo.empty());
}

void expr_free_vars::set_default_sort(sort *s) {
    for (unsigned i = 0; i < m_sorts.size(); ++i) {
        if (!m_sorts[i]) m_sorts[i] = s;
    }
}

void expr_free_vars::operator()(expr* e) {
    reset();
    get_free_vars_offset(m_mark, m_todo, 0, e, m_sorts);
}

void expr_free_vars::accumulate(expr* e) {
    SASSERT(m_todo.empty());
    get_free_vars_offset(m_mark, m_todo, 0, e, m_sorts);
}
