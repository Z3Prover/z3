/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_util.cpp

Abstract:

    Helper functions

Author:

    Leonardo de Moura (leonardo) 2007-06-08.

Revision History:

--*/
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/arith_decl_plugin.h"

app * mk_list_assoc_app(ast_manager & m, func_decl * f, unsigned num_args, expr * const * args) {
    SASSERT(f->is_associative());
    SASSERT(num_args >= 2);
    if (num_args > 2) {
        unsigned j = num_args - 1;
        app * r = m.mk_app(f, args[j-1], args[j]);
        -- j;
        while (j > 0) {
            --j;
            r = m.mk_app(f, args[j], r);
        }
        return r;
    }
    else {
        SASSERT(num_args == 2);
        return m.mk_app(f, args[0], args[1]);
    }
}

app * mk_list_assoc_app(ast_manager & m, family_id fid, decl_kind k, unsigned num_args, expr * const * args) {
    func_decl * decl = m.mk_func_decl(fid, k, 0, nullptr, num_args, args, nullptr);
    SASSERT(decl != 0);
    SASSERT(decl->is_associative());
    return mk_list_assoc_app(m, decl, num_args, args);
}

bool is_well_formed_vars(ptr_vector<sort>& bound, expr * top) {
    ptr_vector<expr> todo;
    ast_mark mark;
    todo.push_back(top);
    while (!todo.empty()) {
        expr * e = todo.back();
        todo.pop_back();
        if (mark.is_marked(e)) {
            continue;
        }
        mark.mark(e, true);
        if (is_quantifier(e)) {
            quantifier* q = to_quantifier(e);
            unsigned depth = q->get_num_decls();
            bound.append(depth, q->get_decl_sorts());
            if (!is_well_formed_vars(bound, q->get_expr())) {
                return false;
            }
            bound.resize(bound.size()-depth);
        }
        else if (is_app(e)) {
            app* a = to_app(e);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                todo.push_back(a->get_arg(i));
            }
        }
        else if (is_var(e)) {
            var* v = to_var(e);
            unsigned index = v->get_idx();
            sort* s = v->get_sort();
            SASSERT(index < bound.size());
            index = bound.size()-1-index;
            if (!bound[index]) {
                bound[index] = s;
            }
            if (bound[index] != s) {
                return false;
            }
        }
        else {
            UNREACHABLE();
        }
    }
    return true;
}


bool is_atom(ast_manager & m, expr * n) {
    if (is_quantifier(n) || !m.is_bool(n))
        return false;
    if (is_var(n))
        return true;
    SASSERT(is_app(n));
    if (to_app(n)->get_family_id() != m.get_basic_family_id()) {
        return true;
    }
    // the other operators of the basic family are not considered atomic: distinct, ite, and, or, iff, xor, not, implies.
    return (m.is_eq(n) && !m.is_bool(to_app(n)->get_arg(0))) || m.is_true(n) || m.is_false(n);
}


bool is_literal(ast_manager & m, expr * n) {
    return
        is_atom(m, n) ||
        (m.is_not(n) && is_atom(m, to_app(n)->get_arg(0)));
}

void get_literal_atom_sign(ast_manager & m, expr * n, expr * & atom, bool & sign) {
    SASSERT(is_literal(m, n));
    if (is_atom(m, n)) {
        atom = n;
        sign = false;
    }
    else {
        SASSERT(m.is_not(n));
        atom = to_app(n)->get_arg(0);
        sign = true;
    }
}

bool is_clause(ast_manager & m, expr * n) {
    if (is_literal(m, n))
        return true;
    if (m.is_or(n)) {
        for (expr* arg : *to_app(n))
            if (!is_literal(m, arg))
                return false;        
        return true;
    }
    return false;
}

unsigned get_clause_num_literals(ast_manager & m, expr * cls) {
    SASSERT(is_clause(m, cls));
    if (is_literal(m, cls))
        return 1;
    SASSERT(m.is_or(cls));
    return to_app(cls)->get_num_args();
}

expr * get_clause_literal(ast_manager & m, expr * cls, unsigned idx) {
    SASSERT(is_clause(m, cls));
    SASSERT(idx < get_clause_num_literals(m, cls));
    if (is_literal(m, cls)) {
        SASSERT(idx == 0);
        return cls;
    }
    SASSERT(m.is_or(cls));
    return to_app(cls)->get_arg(idx);
}

expr * mk_and(ast_manager & m, unsigned num_args, expr * const * args) {
    if (num_args == 0)
        return m.mk_true();
    else if (num_args == 1)
        return args[0];
    else
        return m.mk_and(num_args, args);
}

app* mk_and(ast_manager & m, unsigned num_args, app * const * args) {
    return to_app(mk_and(m, num_args, (expr* const*) args));
}

expr * mk_or(ast_manager & m, unsigned num_args, expr * const * args) {
    if (num_args == 0)
        return m.mk_false();
    else if (num_args == 1)
        return args[0];
    else
        return m.mk_or(num_args, args);
}

app* mk_or(ast_manager & m, unsigned num_args, app * const * args) {
    return to_app(mk_or(m, num_args, (expr* const*) args));
}

expr * mk_not(ast_manager & m, expr * arg) {
    expr * atom;
    if (m.is_not(arg, atom))
        return atom;
    else if (m.is_true(arg))
        return m.mk_false();
    else if (m.is_false(arg))
        return m.mk_true();
    else
        return m.mk_not(arg);
}

expr_ref mk_not(const expr_ref& e) {
    return expr_ref(mk_not(e.m(), e), e.m());
}


expr_ref push_not(const expr_ref& e, unsigned limit) {
    ast_manager& m = e.get_manager();
    if (!is_app(e) || limit == 0) {
        return mk_not(e);
    }
    app* a = to_app(e);
    if (m.is_and(a)) {
        if (a->get_num_args() == 0) {
            return expr_ref(m.mk_false(), m);
        }
        expr_ref_vector args(m);
        for (expr* arg : *a) {
            args.push_back(push_not(expr_ref(arg, m), limit-1));
        }
        return mk_or(args);
    }
    if (m.is_or(a)) {
        if (a->get_num_args() == 0) {
            return expr_ref(m.mk_true(), m);
        }
        expr_ref_vector args(m);
        for (expr* arg : *a) {
            args.push_back(push_not(expr_ref(arg, m), limit-1));
        }
        return mk_and(args);
    }
    return mk_not(e);
}

expr * expand_distinct(ast_manager & m, unsigned num_args, expr * const * args) {
    expr_ref_buffer new_diseqs(m);
    for (unsigned i = 0; i < num_args; i++) {
        for (unsigned j = i + 1; j < num_args; j++)
            new_diseqs.push_back(m.mk_not(m.mk_eq(args[i], args[j])));
    }
    return mk_and(m, new_diseqs.size(), new_diseqs.data());
}

expr* mk_distinct(ast_manager& m, unsigned num_args, expr * const * args) {
    switch (num_args) {
    case 0:
    case 1:
        return m.mk_true();
    case 2:
        return m.mk_not(m.mk_eq(args[0], args[1]));
    default:
        return m.mk_distinct(num_args, args);
    }
}

expr_ref mk_distinct(expr_ref_vector const& args) {
    ast_manager& m = args.get_manager();
    return expr_ref(mk_distinct(m, args.size(), args.data()), m);
}


void flatten_and(expr_ref_vector& result) {
    ast_manager& m = result.get_manager();
    expr* e1, *e2, *e3;
    for (unsigned i = 0; i < result.size(); ++i) {
        if (m.is_and(result.get(i))) {
            app* a = to_app(result.get(i));
            for (expr* arg : *a) result.push_back(arg);
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_not(result.get(i), e1) && m.is_not(e1, e2)) {
            result[i] = e2;
            --i;
        }
        else if (m.is_not(result.get(i), e1) && m.is_or(e1)) {
            app* a = to_app(e1);
            for (expr* arg : *a) result.push_back(m.mk_not(arg));
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_not(result.get(i), e1) && m.is_implies(e1,e2,e3)) {
            result.push_back(e2);
            result[i] = m.mk_not(e3);
            --i;
        }
        else if (m.is_true(result.get(i)) ||
                 (m.is_not(result.get(i), e1) &&
                  m.is_false(e1))) {
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_false(result.get(i)) ||
                 (m.is_not(result.get(i), e1) &&
                  m.is_true(e1))) {
            result.reset();
            result.push_back(m.mk_false());
            return;
        }
    }
}

void flatten_and(expr* fml, expr_ref_vector& result) {
    SASSERT(result.get_manager().is_bool(fml));
    result.push_back(fml);
    flatten_and(result);
}

void flatten_and(expr_ref& fml) {
    expr_ref_vector fmls(fml.get_manager());
    fmls.push_back(fml);
    flatten_and(fmls);
    fml = mk_and(fmls);
}

void flatten_or(expr_ref_vector& result) {
    ast_manager& m = result.get_manager();
    expr* e1, *e2, *e3;
    for (unsigned i = 0; i < result.size(); ++i) {
        if (m.is_or(result.get(i))) {
            app* a = to_app(result.get(i));
            for (expr* arg : *a) result.push_back(arg);
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_not(result.get(i), e1) && m.is_not(e1, e2)) {
            result[i] = e2;
            --i;
        }
        else if (m.is_not(result.get(i), e1) && m.is_and(e1)) {
            app* a = to_app(e1);
            for (expr* arg : *a) result.push_back(m.mk_not(arg));
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_implies(result.get(i),e2,e3)) {
            result.push_back(e3);
            result[i] = m.mk_not(e2);
            --i;
        }
        else if (m.is_false(result.get(i)) ||
                 (m.is_not(result.get(i), e1) &&
                  m.is_true(e1))) {
            result[i] = result.back();
            result.pop_back();
            --i;
        }
        else if (m.is_true(result.get(i)) ||
                 (m.is_not(result.get(i), e1) &&
                  m.is_false(e1))) {
            result.reset();
            result.push_back(m.mk_true());
            return;
        }
    }
}


void flatten_or(expr* fml, expr_ref_vector& result) {
    SASSERT(result.get_manager().is_bool(fml));
    result.push_back(fml);
    flatten_or(result);
}

static app_ref plus(ast_manager& m, expr* a, expr* b) {
    arith_util arith(m);
    return app_ref(arith.mk_add(a, b), m);
}


app_ref operator+(expr_ref& a, expr_ref& b) { 
    return plus(a.m(), a.get(), b.get()); 
}

bool has_uninterpreted(ast_manager& m, expr* _e) {
    expr_ref e(_e, m);
    arith_util au(m);
    func_decl_ref f_out(m);
    for (expr* arg : subterms(e)) {
        if (!is_app(arg)) 
            continue;
        app* a = to_app(arg);
        func_decl* f = a->get_decl();
        if (a->get_num_args() == 0)
            continue;
        if (m.is_considered_uninterpreted(f))
            return true;
        if (au.is_considered_uninterpreted(f, a->get_num_args(), a->get_args(), f_out))
            return true;
    }
    return false;
}
