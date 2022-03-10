/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat univariate solver

Abstract:

    Solve univariate constraints for polysat using bitblasting

Author:

    Nikolaj Bjorner (nbjorner) 2022-03-10
    Jakob Rath 2022-03-10

--*/

#include "math/polysat/univariate/univariate_solver.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "solver/solver.h"
#include "util/util.h"


namespace polysat {

    class univariate_bitblast_solver : public univariate_solver {
        ast_manager m;
        scoped_ptr<solver> s;

    public:
        univariate_bitblast_solver(solver_factory& mk_solver) {
            s = mk_solver(m, params_ref::get_empty(), false, true, true, symbol::null);
        }

        ~univariate_bitblast_solver() override = default;

        void push() override {
            s->push();
        }

        void pop(unsigned n) override {
            s->pop(n);
        }

        void add_ule(univariate lhs, univariate rhs, bool sign, dep_t dep) override {
            // s->assert_expr();
            NOT_IMPLEMENTED_YET();
        }

        void add_umul_ovfl(univariate lhs, univariate rhs, bool sign, dep_t dep) override {
            NOT_IMPLEMENTED_YET();
        }

        void add_smul_ovfl(univariate lhs, univariate rhs, bool sign, dep_t dep) override {
            NOT_IMPLEMENTED_YET();
        }

        void add_smul_udfl(univariate lhs, univariate rhs, bool sign, dep_t dep) override {
            NOT_IMPLEMENTED_YET();
        }

        lbool check() override {
            // TODO: need to pass assumptions to get an unsat core?
            return s->check_sat();
        }

        dep_vector unsat_core() override {
            SASSERT(s->status() == l_false);
            expr_ref_vector core(m);
            s->get_unsat_core(core);
            NOT_IMPLEMENTED_YET();
            return {};
        }

        rational model() override {
            SASSERT(s->status() == l_true);
            model_ref model;
            s->get_model(model);
            NOT_IMPLEMENTED_YET();
            return {};
        }
    };

    class univariate_bitblast_factory : public univariate_solver_factory {
        symbol qf_bv;
        scoped_ptr<solver_factory> sf;

    public:
        univariate_bitblast_factory() :
            qf_bv("QF_BV") {
            sf = mk_smt_strategic_solver_factory(qf_bv);
        }

        ~univariate_bitblast_factory() override = default;

        scoped_ptr<univariate_solver> operator()() override {
            return alloc(univariate_bitblast_solver, *sf);
        }
    };

    scoped_ptr<univariate_solver_factory> mk_univariate_bitblast_factory() {
        return alloc(univariate_bitblast_factory);
    }
}
