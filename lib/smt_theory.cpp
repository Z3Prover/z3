/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_theory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include"smt_context.h"
#include"buffer.h"
#include"ast_ll_pp.h"

namespace smt {

    void theory::init(context * ctx) {
        SASSERT(m_context == 0);
        m_context = ctx;
        m_manager = &(ctx->get_manager());
    }

    void theory::reset_eh() {
        m_var2enode.reset();
    }
    
    void theory::push_scope_eh() {
        SASSERT(m_context);
        m_var2enode_lim.push_back(m_var2enode.size());
    }

    void theory::pop_scope_eh(unsigned num_scopes) {
        SASSERT(m_context);
        unsigned scope_lvl = m_var2enode_lim.size();
        SASSERT(num_scopes <= scope_lvl);
        unsigned new_lvl   = scope_lvl - num_scopes;
        unsigned old_sz    = m_var2enode_lim[new_lvl];
        m_var2enode.shrink(old_sz);
        m_var2enode_lim.shrink(new_lvl);
    }

    void theory::display_var2enode(std::ostream & out) const {
        unsigned sz = m_var2enode.size();
        for (unsigned v = 0; v < sz; v++) {
            out << "v" << v << " -> #" << m_var2enode[v]->get_owner_id() << "\n";
        }
    }

    void theory::display_app(std::ostream & out, app * n) const {
        func_decl * d = n->get_decl();
        if (n->get_num_args() == 0) {
            out << d->get_name();
            display_parameters(out, d->get_num_parameters(), d->get_parameters());
        }
        else if (n->get_family_id() == get_family_id()) {
            out << "(" << d->get_name();
            display_parameters(out, d->get_num_parameters(), d->get_parameters());
            unsigned num = n->get_num_args();
            for (unsigned i = 0; i < num; i++) {
                out << " ";
                display_app(out, to_app(n->get_arg(i)));
            }
            out << ")";
        }
        else {
            out << "#" << n->get_id();
        }
    }

    void theory::display_flat_app(std::ostream & out, app * n) const {
        func_decl * d = n->get_decl();
        if (n->get_num_args() == 0) {
            out << d->get_name();
            display_parameters(out, d->get_num_parameters(), d->get_parameters());
        }
        else if (n->get_family_id() == get_family_id()) {
            out << "(" << d->get_name();
            display_parameters(out, d->get_num_parameters(), d->get_parameters());
            ptr_buffer<app> todo;
            todo.push_back(n);
            while (!todo.empty()) {
                n = todo.back();
                todo.pop_back();
                unsigned num = n->get_num_args();
                for (unsigned i = 0; i < num; i++) {
                    app * arg = to_app(n->get_arg(i));
                    if (d->is_associative() && arg->get_decl() == d) {
                        todo.push_back(arg);
                    }
                    else {
                        out << " ";
                        display_app(out, arg);
                    }
                }
            }
            out << ")";
        }
        else {
            out << "#" << n->get_id();
        }
    }
    
    bool theory::is_relevant_and_shared(enode * n) const {
        context & ctx = get_context();
        return ctx.is_relevant(n) && ctx.is_shared(n);
    }
    
    bool theory::assume_eq(enode * n1, enode * n2) {
        return get_context().assume_eq(n1, n2);
    }

    literal theory::mk_eq(expr * a, expr * b, bool gate_ctx) {
        context & ctx = get_context();
        app * eq = ctx.mk_eq_atom(a, b);
        TRACE("mk_var_bug", tout << "mk_eq: " << eq->get_id() << " " << a->get_id() << " " << b->get_id() << "\n";
              tout << mk_ll_pp(a, get_manager()) << "\n" << mk_ll_pp(b, get_manager()););
        ctx.internalize(eq, gate_ctx);
        return ctx.get_literal(eq);
    }

    theory::theory(family_id fid):
        m_id(fid),
        m_context(0),
        m_manager(0) {
    }

    theory::~theory() {
    }

};

