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
#include "ast_util.h"

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
    func_decl * decl = m.mk_func_decl(fid, k, 0, 0, num_args, args, 0);
    SASSERT(decl != 0);
    SASSERT(decl->is_associative());
    return mk_list_assoc_app(m, decl, num_args, args);
}

bool is_well_formed_vars(ptr_vector<sort>& bound, expr* e) {
    ptr_vector<expr> todo;
    ast_mark mark;
    todo.push_back(e);
    while (!todo.empty()) {
        expr* e = todo.back();
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
        unsigned num_args = to_app(n)->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (!is_literal(m, to_app(n)->get_arg(i)))
                return false;
        }
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

expr * mk_or(ast_manager & m, unsigned num_args, expr * const * args) {
    if (num_args == 0)
        return m.mk_false();
    else if (num_args == 1)
        return args[0];
    else
        return m.mk_or(num_args, args);
}

expr * mk_not(ast_manager & m, expr * arg) {
    expr * atom;
    if (m.is_not(arg, atom))
        return atom;
    else
        return m.mk_not(arg);
}

expr * expand_distinct(ast_manager & m, unsigned num_args, expr * const * args) {
    expr_ref_buffer new_diseqs(m);
    for (unsigned i = 0; i < num_args; i++) {
        for (unsigned j = i + 1; j < num_args; j++)
            new_diseqs.push_back(m.mk_not(m.mk_eq(args[i], args[j])));
    }
    return mk_and(m, new_diseqs.size(), new_diseqs.c_ptr());
}
