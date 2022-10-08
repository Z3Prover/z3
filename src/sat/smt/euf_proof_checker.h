/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_proof_checker.h

Abstract:

    Plugin manager for checking EUF proofs

Author:

    Nikolaj Bjorner (nbjorner) 2022-08-25

--*/
#pragma once

#include "util/map.h"
#include "util/scoped_ptr_vector.h"
#include "ast/ast.h"

namespace euf {

    class proof_checker;

    class proof_checker_plugin {
    public:
        virtual ~proof_checker_plugin() {}
        virtual bool check(app* jst) = 0;
        virtual expr_ref_vector clause(app* jst) = 0;
        virtual void register_plugins(proof_checker& pc) = 0;
        virtual void vc(app* jst, expr_ref_vector& clause) { }
    };

    class proof_checker {
        ast_manager& m;
        scoped_ptr_vector<proof_checker_plugin> m_plugins;                          // plugins of proof checkers
        map<symbol, proof_checker_plugin*, symbol_hash_proc, symbol_eq_proc> m_map; // symbol table of proof checkers
        obj_map<expr, expr_ref_vector*> m_checked_clauses;                          // cache of previously checked proofs and their clauses.
        void add_plugin(proof_checker_plugin* p);
    public:
        proof_checker(ast_manager& m);
        ~proof_checker();
        void register_plugin(symbol const& rule, proof_checker_plugin*);
        bool check(expr* jst);
        expr_ref_vector clause(expr* jst);
        void vc(expr* jst, expr_ref_vector& clause);
        bool check(expr_ref_vector const& clause, expr* e, expr_ref_vector& units);
    };

    /**
       Base class for checking SMT proofs whose justifications are 
       provided as a set of literals and E-node equalities.
       It provides shared implementations for clause and register_plugin.
       It overrides check to always fail.
     */
    class smt_proof_checker_plugin : public proof_checker_plugin {
        ast_manager& m;
        symbol m_rule;
    public:
        smt_proof_checker_plugin(ast_manager& m, symbol const& n): m(m), m_rule(n) {}
        ~smt_proof_checker_plugin() override {}
        bool check(app* jst) override { return false; }
        expr_ref_vector clause(app* jst) override;        
        void register_plugins(proof_checker& pc) override { pc.register_plugin(m_rule, this); }
    };

}

