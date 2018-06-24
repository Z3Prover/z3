/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    atom2bool_var.cpp

Abstract:

    The mapping between SAT boolean variables and atoms

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/

#include "util/ref_util.h"
#include "ast/ast_smt2_pp.h"
#include "tactic/goal.h"
#include "sat/tactic/atom2bool_var.h"

void atom2bool_var::mk_inv(expr_ref_vector & lit2expr) const {
    for (auto const& kv : m_mapping) {
        sat::literal l(static_cast<sat::bool_var>(kv.m_value), false);
        lit2expr.set(l.index(), kv.m_key);
        l.neg();
        lit2expr.set(l.index(), m().mk_not(kv.m_key));
    }
}

void atom2bool_var::mk_var_inv(app_ref_vector & var2expr) const {
    for (auto const& kv : m_mapping) {
        var2expr.set(kv.m_value, to_app(kv.m_key));
    }
}

sat::bool_var atom2bool_var::to_bool_var(expr * n) const {
    sat::bool_var v = sat::null_bool_var;
    m_mapping.find(n, v);
    return v;
}

struct collect_boolean_interface_proc {
    struct visitor {
        obj_hashtable<expr> & m_r;
        visitor(obj_hashtable<expr> & r):m_r(r) {}
        void operator()(var * n)  {}
        void operator()(app * n)  { if (is_uninterp_const(n)) m_r.insert(n); }       
        void operator()(quantifier * n) {} 
    };

    ast_manager &    m;
    expr_fast_mark2  fvisited;
    expr_fast_mark1  tvisited;
    ptr_vector<expr> todo;
    visitor          proc;

    collect_boolean_interface_proc(ast_manager & _m, obj_hashtable<expr> & r):
        m(_m),
        proc(r) {
    }

    void process(expr * f) {
        if (fvisited.is_marked(f))
            return;
        fvisited.mark(f);
        todo.push_back(f);
        while (!todo.empty()) {
            expr * t = todo.back();
            todo.pop_back();
            if (is_uninterp_const(t))
                continue;
            if (is_app(t) && to_app(t)->get_family_id() == m.get_basic_family_id() && to_app(t)->get_num_args() > 0) {
                decl_kind k = to_app(t)->get_decl_kind();
                if (k == OP_OR || k == OP_NOT || ((k == OP_EQ || k == OP_ITE) && m.is_bool(to_app(t)->get_arg(1)))) {
                    unsigned num = to_app(t)->get_num_args();
                    for (unsigned i = 0; i < num; i++) {
                        expr * arg = to_app(t)->get_arg(i);
                        if (fvisited.is_marked(arg))
                            continue;
                        fvisited.mark(arg);
                        todo.push_back(arg);
                    }
                }
            }
            else {
                quick_for_each_expr(proc, tvisited, t);
            }
        }
    }
    
    template<typename T>
    void operator()(T const & g) {
        unsigned sz = g.size();
        ptr_vector<expr> deps, all_deps;
        for (unsigned i = 0; i < sz; i++) {
            if (g.dep(i)) {
                deps.reset();
                m.linearize(g.dep(i), deps);
                all_deps.append(deps);
            }
        }

        for (unsigned i = 0; i < all_deps.size(); i++) {
            quick_for_each_expr(proc, tvisited, all_deps[i]);
        }
        for (unsigned i = 0; i < sz; i++) {
            process(g.form(i));
        }

    }
    
    void operator()(unsigned sz, expr * const * fs) {
        for (unsigned i = 0; i < sz; i++)
            process(fs[i]);
    }
};

template<typename T>
void collect_boolean_interface_core(T const & s, obj_hashtable<expr> & r) {
    collect_boolean_interface_proc proc(s.m(), r);
    proc(s);
}

void collect_boolean_interface(goal const & g, obj_hashtable<expr> & r) {
    collect_boolean_interface_core(g, r);
}

void collect_boolean_interface(ast_manager & m, unsigned num, expr * const * fs, obj_hashtable<expr> & r) {
    collect_boolean_interface_proc proc(m, r);
    proc(num, fs);
}
