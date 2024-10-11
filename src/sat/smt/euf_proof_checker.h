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
#include "ast/ast_util.h"
#include "solver/solver.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"


namespace euf {

    class theory_checker;

    class theory_checker_plugin {
    public:
        virtual ~theory_checker_plugin() {}
        virtual bool check(app* jst) = 0;
        virtual expr_ref_vector clause(app* jst) = 0;
        virtual void register_plugins(theory_checker& pc) = 0;
        virtual bool vc(app* jst, expr_ref_vector const& clause, expr_ref_vector& v) { v.append(this->clause(jst)); return false; }
    };

    class theory_checker {
        ast_manager& m;
        scoped_ptr_vector<theory_checker_plugin> m_plugins;                          // plugins of proof checkers
        map<symbol, theory_checker_plugin*, symbol_hash_proc, symbol_eq_proc> m_map; // symbol table of proof checkers
        void add_plugin(theory_checker_plugin* p);
    public:
        theory_checker(ast_manager& m);
        void register_plugin(symbol const& rule, theory_checker_plugin*);
        bool check(expr* jst);
        expr_ref_vector clause(expr* jst);
        bool vc(expr* jst, expr_ref_vector const& clause, expr_ref_vector& v);
        bool check(expr_ref_vector const& clause, expr* e, expr_ref_vector& units);
    };

    /**
       Base class for checking SMT proofs whose justifications are 
       provided as a set of literals and E-node equalities.
       It provides shared implementations for clause and register_plugin.
       It overrides check to always fail.
     */
    class smt_theory_checker_plugin : public theory_checker_plugin {
        ast_manager& m;
    public:
        smt_theory_checker_plugin(ast_manager& m): m(m) {}
        bool check(app* jst) override { return false; }
        expr_ref_vector clause(app* jst) override;        
        void register_plugins(theory_checker& pc) override;
    };


    class smt_proof_checker {
        ast_manager& m;
        params_ref   m_params;
        
        // for checking proof rules (hints)
        euf::theory_checker m_checker;
        
        // for fallback SMT checker
        scoped_ptr<::solver> m_solver;
        
        // for RUP
        symbol       m_rup;
        sat::solver  m_sat_solver;
        sat::drat    m_drat;
        sat::literal_vector m_units;
        sat::literal_vector m_clause;
        bool         m_check_rup = false;

        // for logging

        map<symbol, unsigned, symbol_hash_proc, symbol_eq_proc> m_hint2hit, m_hint2miss;
        unsigned m_num_logs = 0;
        
        void add_units() {
            auto const& units = m_drat.units();
            for (unsigned i = m_units.size(); i < units.size(); ++i)
                m_units.push_back(units[i].first);
        }

        void log_verified(app* proof_hint, bool success);

        void diagnose_rup_failure(expr_ref_vector const& clause);

        void ensure_solver();
        
    public:
        smt_proof_checker(ast_manager& m, params_ref const& p);
        
        bool is_rup(app* proof_hint) {
            return
                proof_hint &&
                proof_hint->get_name() == m_rup;        
        }
        
        void mk_clause(expr_ref_vector const& clause) {
            m_clause.reset();
            for (expr* e : clause) {
                bool sign = false;
                while (m.is_not(e, e))
                    sign = !sign;
                m_clause.push_back(sat::literal(e->get_id(), sign));
            }
        }
        
        void mk_clause(expr* e) {
            m_clause.reset();
            bool sign = false;
            while (m.is_not(e, e))
                sign = !sign;
            m_clause.push_back(sat::literal(e->get_id(), sign));
        }
        
        bool check_rup(expr_ref_vector const& clause);
        
        bool check_rup(expr* u);
        
        void add_clause(expr_ref_vector const& clause) {
            if (!m_check_rup)
                return;
            mk_clause(clause);
            m_drat.add(m_clause, sat::status::input());
        }

        void assume(expr_ref_vector const& clause) {
            add_clause(clause);
            if (!m_check_rup)
                return;
            ensure_solver();
            m_solver->assert_expr(mk_or(clause));
        }
        
        void del(expr_ref_vector const& clause) {            
        }

        
        void infer(expr_ref_vector& clause, app* proof_hint);

        void collect_statistics(statistics& st) const;
        
    };


}

