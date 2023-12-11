/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    intblast_solver.h

Abstract:

    Int-blast solver.
    It assumes a full assignemnt to literals in 
    irredundant clauses. 
    It picks a satisfying Boolean assignment and 
    checks if it is feasible for bit-vectors using
    an arithmetic solver.

Author:

    Nikolaj Bjorner (nbjorner) 2023-12-10

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "solver/solver.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace intblast {

    class solver {
        struct var_info {
            expr* dst;
            rational sz;
        };

        euf::solver& ctx;
        sat::solver& s;
        ast_manager& m;
        bv_util bv;
        arith_util a;
        scoped_ptr<::solver> m_solver;
        obj_map<expr, var_info> m_vars;
        obj_map<func_decl, func_decl*> m_new_funs;
        expr_ref_vector m_trail;
        sat::literal_vector m_core;



        bool is_bv(sat::literal lit);
        void translate(expr_ref_vector& es);
        void add_root_equations(expr_ref_vector& es, ptr_vector<expr>& sorted);
        void sorted_subterms(expr_ref_vector& es, ptr_vector<expr>& sorted);

    public:
        solver(euf::solver& ctx);
        
        lbool check();

        sat::literal_vector const& unsat_core();

        rational get_value(expr* e) const;

        std::ostream& display(std::ostream& out) const;
    };

}
