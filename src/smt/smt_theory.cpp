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
#include "smt/smt_context.h"
#include "util/buffer.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    void theory::reset_eh() {
        m_var2enode.reset();
    }
    
    void theory::push_scope_eh() {
        m_var2enode_lim.push_back(m_var2enode.size());
    }

    void theory::pop_scope_eh(unsigned num_scopes) {
        unsigned scope_lvl = m_var2enode_lim.size();
        SASSERT(num_scopes <= scope_lvl);
        unsigned new_lvl   = scope_lvl - num_scopes;
        unsigned old_sz    = m_var2enode_lim[new_lvl];
        m_var2enode.shrink(old_sz);
        m_var2enode_lim.shrink(new_lvl);
    }

    bool theory::lazy_push() {
        if (m_lazy)
            ++m_lazy_scopes;
        return m_lazy;
    }

    bool theory::lazy_pop(unsigned& num_scopes) {
        unsigned n = std::min(num_scopes, m_lazy_scopes);
        num_scopes -= n;
        m_lazy_scopes -= n;
        return num_scopes == 0;
    }

    void theory::force_push() {
        flet<bool> _lazy(m_lazy, false);
        for (; m_lazy_scopes > 0; --m_lazy_scopes) {
            push_scope_eh();
        }
    }

    void theory::display_var2enode(std::ostream & out) const {
        unsigned sz = m_var2enode.size();
        for (unsigned v = 0; v < sz; v++) {
            out << "v" << v << " -> #" << m_var2enode[v]->get_owner_id() << "\n";
        }
    }

    std::ostream& theory::display_app(std::ostream & out, app * n) const {
        func_decl * d = n->get_decl();
        if (n->get_num_args() == 0) {
            out << mk_bounded_pp(n, get_manager(), 1);
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
        return out;
    }

    std::ostream& theory::display_flat_app(std::ostream & out, app * n) const {
        func_decl * d = n->get_decl();
        if (n->get_num_args() == 0) {
            display_app(out, n);
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
            out << mk_bounded_pp(n, get_manager(), 1);
        }
        return out;
    }
    
    bool theory::is_relevant_and_shared(enode * n) const {
        return ctx.is_relevant(n) && ctx.is_shared(n);
    }
    
    bool theory::assume_eq(enode * n1, enode * n2) {
        return ctx.assume_eq(n1, n2);
    }

    literal theory::mk_eq(expr * a, expr * b, bool gate_ctx) {
        if (a == b) {
            return true_literal;
        }
        if (m.are_distinct(a, b))
            return false_literal;
        app_ref eq(ctx.mk_eq_atom(a, b), get_manager());
        TRACE("mk_var_bug", tout << "mk_eq: " << eq->get_id() << " " << a->get_id() << " " << b->get_id() << "\n";
              tout << mk_ll_pp(a, get_manager()) << "\n" << mk_ll_pp(b, get_manager()););		
        ctx.internalize(eq, gate_ctx);
        return ctx.get_literal(eq);
    }

    literal theory::mk_preferred_eq(expr* a, expr* b) {
        ctx.assume_eq(ensure_enode(a), ensure_enode(b));
        literal lit = mk_eq(a, b, false);
        ctx.force_phase(lit);
        return lit;
    }

    literal theory::mk_literal(expr* _e) {
        expr_ref e(_e, m);
        bool is_not = m.is_not(_e, _e);
        if (!ctx.e_internalized(_e)) {
            ctx.internalize(_e, is_quantifier(_e));
        }
        literal lit = ctx.get_literal(_e);
        ctx.mark_as_relevant(lit);
        if (is_not) lit.neg();
        return lit;
    }

    enode* theory::ensure_enode(expr* e) {
        if (!ctx.e_internalized(e)) 
            ctx.internalize(e, is_quantifier(e));
        ctx.ensure_internalized(e); // make sure theory variables are attached.
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    theory::theory(context& ctx, family_id fid):
        m_id(fid),
        ctx(ctx),
        m(ctx.get_manager()),
        m_lazy_scopes(0),
        m_lazy(true) {
    }

    theory::~theory() {
    }

    smt_params const& theory::get_fparams() const { 
        return ctx.get_fparams();
    }

    void theory::log_axiom_instantiation(literal_vector const& ls) {
        ast_manager& m = get_manager();
        expr_ref_vector fmls(m);
        expr_ref tmp(m);
        for (literal l : ls) {
            ctx.literal2expr(l, tmp);
            fmls.push_back(tmp);
        }
        log_axiom_instantiation(mk_or(fmls));
    }


    void theory::log_axiom_instantiation(literal_buffer const& ls) {
        ast_manager& m = get_manager();
        expr_ref_vector fmls(m);
        expr_ref tmp(m);
        for (literal l : ls) {
            ctx.literal2expr(l, tmp);
            fmls.push_back(tmp);
        }
        log_axiom_instantiation(mk_or(fmls));
    }

    void theory::log_axiom_instantiation(app * r, unsigned axiom_id, unsigned num_bindings, app * const * bindings, unsigned pattern_id, const vector<std::tuple<enode *, enode *>> & used_enodes) {
        ast_manager & m = get_manager();
        app_ref _r(r, m);
        std::ostream& out = m.trace_stream();
        symbol const & family_name = m.get_family_name(get_family_id());
        if (pattern_id == UINT_MAX) {
            out << "[inst-discovered] theory-solving " << static_cast<void *>(nullptr) << " " << family_name << "#";
            if (axiom_id != UINT_MAX)
                out << axiom_id;
            for (unsigned i = 0; i < num_bindings; ++i) {
                out << " #" << bindings[i]->get_id();
            }
            if (used_enodes.size() > 0) {
                out << " ;";
                for (auto n : used_enodes) {
                    enode *substituted = std::get<1>(n);
                    SASSERT(std::get<0>(n) == nullptr);
                    out << " #" << substituted->get_owner_id();
                }
            }
        } 
        else {
            SASSERT(axiom_id != UINT_MAX);
            obj_hashtable<enode> already_visited;
            for (auto n : used_enodes) {
                enode *orig = std::get<0>(n);
                enode *substituted = std::get<1>(n);
                if (orig != nullptr) {
                    quantifier_manager::log_justification_to_root(out, orig, already_visited, ctx, get_manager());
                    quantifier_manager::log_justification_to_root(out, substituted, already_visited, ctx, get_manager());
                }
            }
            out << "[new-match] " << static_cast<void *>(nullptr) << " " << family_name << "#" << axiom_id << " " << family_name << "#" << pattern_id;
            for (unsigned i = 0; i < num_bindings; ++i) {
                out << " #" << bindings[i]->get_id();
            }
            out << " ;";
            for (auto n : used_enodes) {
                enode *orig = std::get<0>(n);
                enode *substituted = std::get<1>(n);
                if (orig == nullptr) {
                    out << " #" << substituted->get_owner_id();
                } else {
                    out << " (#" << orig->get_owner_id() << " #" << substituted->get_owner_id() << ")";
                }
            }
        }
        out << "\n";
        out << "[instance] " << static_cast<void *>(nullptr) << " #" << r->get_id() << "\n";
        out.flush();
    }

    theory_var theory::get_th_var(expr* e) const {
        return get_th_var(ctx.get_enode(e));
    }

};

