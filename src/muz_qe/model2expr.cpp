/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    model2expr.cpp

Abstract:

    Convert model to logical formula that forces it.

Author:

    Nikolaj Bjorner (nbjorner) 2012-09-17

Revision History:

--*/
#include "model2expr.h"
#include "for_each_ast.h"
#include "bool_rewriter.h"
#include "var_subst.h"

struct for_each_symbol_proc {
    symbol_set& m_symbols;
    for_each_symbol_proc(symbol_set& syms): m_symbols(syms) {}

    void operator()(func_decl* n) {
        m_symbols.insert(n->get_name());
    }

    void operator()(quantifier* n) {
        for (unsigned i = 0; i < n->get_num_decls(); ++i) {
            m_symbols.insert(n->get_decl_name(i));
        }
    }

    void operator()(var* n) {}
    void operator()(sort* s) {}
    void operator()(app* a) {}
};

void mk_fresh_name::add(ast* a) {
    for_each_symbol_proc proc(m_symbols);
    for_each_ast(proc, a);
}

symbol mk_fresh_name::next() {
    for (; ; ++m_num) {
        for(; m_char <= 'Z'; ++m_char) {
            std::stringstream _name;
            _name << m_char;
            if (m_num > 0) _name << m_num;
            ++m_char;
            symbol name(_name.str().c_str());
            if (!m_symbols.contains(name)) {
                return name;
            }                
        }
        m_char = 'A';
    }
}

static void mk_entry_cond(unsigned arity, func_entry const* entry, expr_ref& result) {
    ast_manager& m = result.get_manager();
    expr_ref_vector conjs(m);
    for (unsigned i = 0; i < arity; ++i) {
        expr* e = entry->get_arg(i);
        if (is_var(e) && to_var(e)->get_idx() == i) {
            // no-op
        }
        else {
            conjs.push_back(m.mk_eq(m.mk_var(i, m.get_sort(e)), e));
        }
    }
    bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), result);        
}

void model2expr(model& md, expr_ref& result) {
    ast_manager& m = result.get_manager();
    
    expr_ref_vector conjs(m);
    expr_ref tmp(m);
    unsigned sz;

    sz = md.get_num_constants();
    for (unsigned i = 0; i < sz; ++i) {
        func_decl* c = md.get_constant(i);
        expr* v = md.get_const_interp(c);
        conjs.push_back(m.mk_eq(m.mk_const(c), v));
    }

    sz = md.get_num_functions();
    for (unsigned i = 0; i < sz; ++i) {

        func_decl* f = md.get_function(i);
        func_interp* fi = md.get_func_interp(f);
        
        // Register names.
        mk_fresh_name fresh_name;
        unsigned num_entries = fi->num_entries();
        fresh_name.add(f);
        for (unsigned j = 0; j < num_entries; ++j) {
            func_entry const* entry = fi->get_entry(j);
            fresh_name.add(entry->get_result());
            for (unsigned k = 0; k < f->get_arity(); ++k) {
                fresh_name.add(entry->get_arg(k));
            }
        }
        
        expr_ref func(m), cond(m);
        expr_ref_vector args(m);
        for (unsigned j = 0; j < f->get_arity(); ++j) {
            args.push_back(m.mk_var(j, f->get_domain(j)));
        }
        func = m.mk_app(f, args.size(), args.c_ptr());
        if (fi->is_partial()) {
            if (num_entries == 0) {
                continue;
            }
            mk_entry_cond(f->get_arity(), fi->get_entry(num_entries-1), cond);
            tmp = m.mk_implies(cond, m.mk_eq(func, fi->get_entry(num_entries-1)->get_result()));
            for (unsigned j = num_entries-1; j > 0; ) {
                --j;
                mk_entry_cond(f->get_arity(), fi->get_entry(j), cond);
                tmp = m.mk_ite(cond, m.mk_eq(func, fi->get_entry(j)->get_result()), tmp);
            }
        }
        else {
            fresh_name.add(fi->get_else());
            tmp = fi->get_else();
            for (unsigned j = num_entries; j > 0; ) {
                --j;
                mk_entry_cond(f->get_arity(), fi->get_entry(j), cond);
                tmp = m.mk_ite(cond, fi->get_entry(j)->get_result(), tmp);
            }
            tmp = m.mk_eq(func, tmp);
        }
        ptr_vector<sort> sorts;
        expr_ref_vector  rev_vars(m);
        svector<symbol>  names;
        unsigned sz = f->get_arity();
        for (unsigned j = 0; j < sz; ++j) {
            sorts.push_back(f->get_domain(j));
            rev_vars.push_back(m.mk_var(sz-j-1, f->get_domain(j)));
            names.push_back(fresh_name.next());
        }
        if (f->get_arity() > 0) {
            var_subst vs(m, false);
            vs(tmp, rev_vars.size(), rev_vars.c_ptr(), tmp);
            tmp = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), tmp);
        }
        conjs.push_back(tmp);
    }

    bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), result);
}
