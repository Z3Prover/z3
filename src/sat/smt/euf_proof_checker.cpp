/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_proof_checker.cpp

Abstract:

    Plugin manager for checking EUF proofs

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/ast_pp.h"
#include "sat/smt/euf_proof_checker.h"
#include "sat/smt/arith_proof_checker.h"

namespace euf {

    proof_checker::proof_checker(ast_manager& m):
        m(m) {
        arith::proof_checker* apc = alloc(arith::proof_checker, m);
        m_plugins.push_back(apc);
        apc->register_plugins(*this);
        (void)m;
    }

    proof_checker::~proof_checker() {}

    void proof_checker::register_plugin(symbol const& rule, proof_checker_plugin* p) {
        m_map.insert(rule, p);
    }

    bool proof_checker::check(expr_ref_vector const& clause, expr* e, expr_ref_vector& units) {
        if (!e || !is_app(e))
            return false;
        units.reset();
        app* a = to_app(e);
        proof_checker_plugin* p = nullptr;
        if (m_map.find(a->get_decl()->get_name(), p)) 
            return p->check(clause, a, units);
        return false;
    }

}

