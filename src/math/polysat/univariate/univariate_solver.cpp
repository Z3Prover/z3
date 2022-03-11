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
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_smt2_pp.h"


namespace polysat {

    class univariate_bitblast_solver : public univariate_solver {
        // TODO: does it make sense to share m and bv between different solver instances?
        ast_manager m;
        scoped_ptr<bv_util> bv;
        scoped_ptr<solver> s;
        unsigned bit_width;
        func_decl* x_decl;
        expr* x;

    public:
        univariate_bitblast_solver(solver_factory& mk_solver, unsigned bit_width) :
            bit_width(bit_width)
        {
            // m.register_plugin(symbol("bv"), alloc(bv_decl_plugin));  // this alone doesn't work
            reg_decl_plugins(m);
            bv = alloc(bv_util, m);
            s = mk_solver(m, params_ref::get_empty(), false, true, true, symbol::null);
            x_decl = m.mk_const_decl("x", bv->mk_sort(bit_width));
            x = m.mk_const(x_decl);
        }

        ~univariate_bitblast_solver() override = default;

        void push() override {
            s->push();
        }

        void pop(unsigned n) override {
            s->pop(n);
        }

        expr* mk_numeral(rational const& r) const {
            return bv->mk_numeral(r, bit_width);
        }

        // [d,c,b,a]  ==>  ((a*x + b)*x + c)*x + d
        expr* mk_poly(univariate const& p) const {
            if (p.empty()) {
                return mk_numeral(rational::zero());
            } else {
                expr* e = mk_numeral(p.back());
                for (unsigned i = p.size() - 1; i-- > 0; ) {
                    e = bv->mk_bv_mul(e, x);
                    if (!p[i].is_zero())
                        e = bv->mk_bv_add(e, mk_numeral(p[i]));
                }
                return e;
            }
        }

        void add(expr* e, bool sign, dep_t dep) {
            if (sign)
                e = m.mk_not(e);
            expr* a = m.mk_const(m.mk_const_decl(symbol(dep), m.mk_bool_sort()));
            s->assert_expr(e, a);
            // std::cout << "add: " << expr_ref(e, m) << "  <==  " << expr_ref(a, m) << "\n";
        }

        void add_ule(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) override {
            add(bv->mk_ule(mk_poly(lhs), mk_poly(rhs)), sign, dep);
        }

        void add_umul_ovfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) override {
            add(bv->mk_bvumul_no_ovfl(mk_poly(lhs), mk_poly(rhs)), !sign, dep);
        }

        void add_smul_ovfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) override {
            add(bv->mk_bvsmul_no_ovfl(mk_poly(lhs), mk_poly(rhs)), !sign, dep);
        }

        void add_smul_udfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) override {
            add(bv->mk_bvsmul_no_udfl(mk_poly(lhs), mk_poly(rhs)), !sign, dep);
        }

        lbool check() override {
            return s->check_sat();
        }

        dep_vector unsat_core() override {
            dep_vector deps;
            expr_ref_vector core(m);
            s->get_unsat_core(core);
            for (expr* a : core) {
                unsigned dep = to_app(a)->get_decl()->get_name().get_num();
                deps.push_back(dep);
            }
            SASSERT(deps.size() > 0);
            return deps;
        }

        rational model() override {
            model_ref model;
            s->get_model(model);
            SASSERT(model);
            app* val = to_app(model->get_const_interp(x_decl));
            SASSERT(val->get_decl_kind() == OP_BV_NUM);
            SASSERT(val->get_num_parameters() == 2);
            auto const& p = val->get_parameter(0);
            SASSERT(p.is_rational());
            return p.get_rational();
        }

        std::ostream& display(std::ostream& out) const override {
            return out << *s;
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

        scoped_ptr<univariate_solver> operator()(unsigned bit_width) override {
            return alloc(univariate_bitblast_solver, *sf, bit_width);
        }
    };

    scoped_ptr<univariate_solver_factory> mk_univariate_bitblast_factory() {
        return alloc(univariate_bitblast_factory);
    }
}
