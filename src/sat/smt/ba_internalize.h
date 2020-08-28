/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    ba_internalize.h

Abstract:

    INternalize methods for Boolean algebra operators.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/


#pragma once

#include "sat/smt/sat_th.h"
#include "sat/smt/ba_solver.h"
#include "ast/pb_decl_plugin.h"


namespace sat {
    
    class ba_internalize : public th_internalizer {
        typedef std::pair<unsigned, literal> wliteral;
        ast_manager& m;
        pb_util pb;
        ba_solver& ba;
        solver_core& m_solver;
        sat_internalizer& si;
        literal convert_eq_k(app* t, rational const& k, bool root, bool sign);
        literal convert_at_most_k(app* t, rational const& k, bool root, bool sign);
        literal convert_at_least_k(app* t, rational const& k, bool root, bool sign);
        literal convert_pb_eq(app* t, bool root, bool sign);
        literal convert_pb_le(app* t, bool root, bool sign);
        literal convert_pb_ge(app* t, bool root, bool sign);
        void check_unsigned(rational const& c);
        void convert_to_wlits(app* t, sat::literal_vector const& lits, svector<wliteral>& wlits);
        void convert_pb_args(app* t, svector<wliteral>& wlits);
        void convert_pb_args(app* t, literal_vector& lits);
        literal internalize_pb(expr* e, bool sign, bool root);
        literal internalize_xor(expr* e, bool sign, bool root);

    public:
        ba_internalize(ba_solver& ba, solver_core& s, sat_internalizer& si, ast_manager& m) : 
            m(m), pb(m), ba(ba), m_solver(s), si(si) {}
        ~ba_internalize() override {}
        literal internalize(expr* e, bool sign, bool root) override;
       
    };

    class ba_decompile : public sat::th_decompile {
        ast_manager& m;
        ba_solver& ba;
        solver_core& m_solver;
        pb_util pb;

        expr_ref get_card(std::function<expr_ref(sat::literal)>& l2e, ba_solver::card const& c);
        expr_ref get_pb(std::function<expr_ref(sat::literal)>& l2e, ba_solver::pb const& p);
        expr_ref get_xor(std::function<expr_ref(sat::literal)>& l2e, ba_solver::xr const& x);
    public:
        ba_decompile(ba_solver& ba, solver_core& s, ast_manager& m) :
            m(m),  ba(ba), m_solver(s), pb(m) {}

        ~ba_decompile() override {}

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;
    };
}
