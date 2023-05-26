/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ast_pp_util.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-6.

Revision History:

--*/

#include "ast/ast_pp_util.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_smt_pp.h"
#include "ast/recfun_decl_plugin.h"

void ast_pp_util::collect(expr* e) {
    coll.visit(e);
}

void ast_pp_util::collect(unsigned n, expr* const* es) {
    for (unsigned i = 0; i < n; ++i) 
        coll.visit(es[i]);
}

void ast_pp_util::collect(expr_ref_vector const& es) {
    collect(es.size(), es.data());
}

void ast_pp_util::display_decls(std::ostream& out) {
    ast_smt_pp pp(m);
    coll.order_deps(m_sorts);
    unsigned n = coll.get_num_sorts();
    ast_mark seen;
    for (unsigned i = m_sorts; i < n; ++i) 
        pp.display_sort_decl(out, coll.get_sorts()[i], seen);
    m_sorts = n;

    n = coll.get_num_decls();
    for (unsigned i = m_decls; i < n; ++i) {
        func_decl* f = coll.get_func_decls()[i];
        if (coll.should_declare(f) && !m_removed.contains(f)) 
            ast_smt2_pp(out, f, m_env) << "\n";
    }
    m_decls = n;
    
    n = coll.get_rec_decls().size();
    vector<std::pair<func_decl*, expr*>> recfuns;
    recfun::util u(m);
    for (unsigned i = m_rec_decls; i < n; ++i) {
        func_decl* f = coll.get_rec_decls()[i];
        recfuns.push_back(std::make_pair(f, u.get_def(f).get_rhs()));
    }
    if (!recfuns.empty())
        ast_smt2_pp_recdefs(out, recfuns, m_env);
    m_rec_decls = n;
}

void ast_pp_util::reset() {
    coll.reset();
    m_removed.reset();
    m_sorts.clear(0u);
    m_decls.clear(0u);
    m_rec_decls.clear(0u); 
    m_is_defined.reset();
    m_defined.reset();
    m_defined_lim.reset(); 
}

void ast_pp_util::display_skolem_decls(std::ostream& out) {
    ast_smt_pp pp(m);
    unsigned n = coll.get_num_decls();
    for (unsigned i = m_decls; i < n; ++i) {
        func_decl* f = coll.get_func_decls()[i];
        if (coll.should_declare(f) && !m_removed.contains(f) && f->is_skolem()) 
            ast_smt2_pp(out, f, m_env) << "\n";
    }
    m_decls = n;    
}

void ast_pp_util::remove_decl(func_decl* f) {
    m_removed.insert(f);
}

std::ostream& ast_pp_util::display_expr(std::ostream& out, expr* f, bool neat) {
    if (neat) {
        ast_smt2_pp(out, f, m_env);
    }
    else {
        ast_smt_pp ll_smt2_pp(m);
        ll_smt2_pp.display_expr_smt2(out, f);
    }
    return out;
}

void ast_pp_util::display_assert(std::ostream& out, expr* f, bool neat) {
    display_expr(out << "(assert ", f, neat) << ")\n";
}

void ast_pp_util::display_assert_and_track(std::ostream& out, expr* f, expr* t, bool neat) {
    if (neat) {
        ast_smt2_pp(out << "(assert (=> ", t, m_env) << " ";
        ast_smt2_pp(out, f, m_env) << "))\n";
    }
    else {
        ast_smt_pp ll_smt2_pp(m);
        ll_smt2_pp.display_expr_smt2(out << "(assert (=> ", t); out << " ";
        ll_smt2_pp.display_expr_smt2(out, f); out << "))\n";
    }
}

void ast_pp_util::display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat) {
    if (neat) {
        for (expr* f : fmls) {
            out << "(assert ";
            ast_smt2_pp(out, f, m_env);
            out << ")\n";
        }
    }
    else {
        ast_smt_pp ll_smt2_pp(m);
        for (expr* f : fmls) {
            out << "(assert ";
            ll_smt2_pp.display_expr_smt2(out, f);
            out << ")\n";
        }
    }
}

void ast_pp_util::push() {
    coll.push();
    m_rec_decls.push();
    m_decls.push();
    m_sorts.push();
    m_defined_lim.push_back(m_defined.size());
}

void ast_pp_util::pop(unsigned n) {
    coll.pop(n);
    m_rec_decls.pop(n);
    m_decls.pop(n);
    m_sorts.pop(n);
    unsigned old_sz = m_defined_lim[m_defined_lim.size() - n];
    for (unsigned i = m_defined.size(); i-- > old_sz; ) 
        m_is_defined.mark(m_defined.get(i), false);
    m_defined.shrink(old_sz);
    m_defined_lim.shrink(m_defined_lim.size() - n);
}

std::ostream& ast_pp_util::display_expr_def(std::ostream& out, expr* n) {
    if (is_app(n) && to_app(n)->get_num_args() == 0)
        return out << mk_pp(n, m);
    else
        return out << "$" << n->get_id();
}

std::ostream& ast_pp_util::define_expr(std::ostream& out, expr* n) {
    ptr_buffer<expr> visit;
    visit.push_back(n);
    while (!visit.empty()) {
        n = visit.back();
        if (m_is_defined.is_marked(n)) {
            visit.pop_back();
            continue;
        }
        if (is_app(n)) {
            bool all_visit = true;
            for (auto* e : *to_app(n)) {
                if (m_is_defined.is_marked(e))
                    continue;
                all_visit = false;
                visit.push_back(e);
            }
            if (!all_visit)
                continue;
            m_defined.push_back(n);
            m_is_defined.mark(n, true);
            visit.pop_back();
            if (to_app(n)->get_num_args() > 0) {
                out << "(define-const $" << n->get_id() << " " << mk_pp(n->get_sort(), m) << " (";            
                out << mk_ismt2_func(to_app(n)->get_decl(), m);
                for (auto* e : *to_app(n)) 
                    display_expr_def(out << " ", e);
                out << "))\n";
            }
            continue;
        }
        out << "(define-const $" << n->get_id() << " " << mk_pp(n->get_sort(), m) << " " << mk_pp(n, m) << ")\n";                
        m_defined.push_back(n);
        m_is_defined.mark(n, true);
        visit.pop_back();        
    }
    return out;
}
