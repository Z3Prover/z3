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
    for (unsigned i = 0; i < n; ++i) {
        coll.visit(es[i]);
    }
}

void ast_pp_util::collect(expr_ref_vector const& es) {
    collect(es.size(), es.c_ptr());
}

void ast_pp_util::display_decls(std::ostream& out) {
    ast_smt_pp pp(m);
    bool first = m_num_decls == 0;
    coll.order_deps(m_num_sorts);
    unsigned n = coll.get_num_sorts();
    for (unsigned i = m_num_sorts; i < n; ++i) {
        pp.display_ast_smt2(out, coll.get_sorts()[i], 0, 0, nullptr);
    }
    m_num_sorts = n;
    n = coll.get_num_decls();
    for (unsigned i = m_num_decls; i < n; ++i) {
        func_decl* f = coll.get_func_decls()[i];
        if (f->get_family_id() == null_family_id && !m_removed.contains(f)) {
            ast_smt2_pp(out, f, m_env) << "\n";
        }
    }
    m_num_decls = n;
    if (first) {
        vector<std::pair<func_decl*, expr*>> recfuns;
        recfun::util u(m);
        func_decl_ref_vector funs = u.get_rec_funs();
        if (funs.empty()) return;
        for (func_decl * f : funs) {
            recfuns.push_back(std::make_pair(f, u.get_def(f).get_rhs()));
        }
        ast_smt2_pp_recdefs(out, recfuns, m_env);
    }
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
    m_num_sorts_trail.push_back(m_num_sorts);
    m_num_decls_trail.push_back(m_num_decls);
}

void ast_pp_util::pop(unsigned n) {
    coll.pop(n);
    m_num_sorts = m_num_sorts_trail[m_num_sorts_trail.size() - n];
    m_num_decls = m_num_decls_trail[m_num_decls_trail.size() - n];
    m_num_sorts_trail.shrink(m_num_sorts_trail.size() - n);
    m_num_decls_trail.shrink(m_num_decls_trail.size() - n);
}
