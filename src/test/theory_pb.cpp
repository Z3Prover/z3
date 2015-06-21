
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt_context.h"
#include "ast_pp.h"
#include "model_v2_pp.h"
#include "reg_decl_plugins.h"
#include "theory_pb.h"
#include "th_rewriter.h"

unsigned populate_literals(unsigned k, smt::literal_vector& lits) {
    SASSERT(k < (1u << lits.size()));
    unsigned t = 0;
    for (unsigned i = 0; i < lits.size(); ++i) {
        if (k & (1 << i)) {
            lits[i] = smt::true_literal;
            t++;
        }
        else {
            lits[i] = smt::false_literal;
        }
    }
    return t;
}

class pb_fuzzer {
    ast_manager& m;
    random_gen rand;
    smt_params params;
    smt::context ctx;
    expr_ref_vector vars;

public:
    pb_fuzzer(ast_manager& m): m(m), rand(0), ctx(m, params), vars(m) {
        params.m_model = true;
        params.m_pb_enable_simplex = true;
        unsigned N = 3;
        for (unsigned i = 0; i < N; ++i) {
            std::stringstream strm;
            strm << "b" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort()));
            std::cout << "(declare-const " << strm.str() << " Bool)\n";
        }
    }

    void fuzz() {
        enable_trace("pb");
        enable_trace("simplex");
        unsigned nr = 0;
        for (unsigned i = 0; i < 100000; ++i) {
            fuzz_round(nr, 2);
        }
    }

private:

    void add_ineq() {
        pb_util pb(m);
        expr_ref fml(m), tmp(m);
        th_rewriter rw(m);
        vector<rational> coeffs(vars.size());
        expr_ref_vector args(vars);
        while (true) {
            rational k(rand(6));
            for (unsigned i = 0; i < coeffs.size(); ++i) {
                int v = 3 - rand(5);
                coeffs[i] = rational(v);
                if (coeffs[i].is_neg()) {
                    args[i] = m.mk_not(args[i].get());
                    coeffs[i].neg();
                    k += coeffs[i];
                }
            }       
            fml = pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), k);
            rw(fml, tmp);
            rw(tmp, tmp);
            if (pb.is_ge(tmp)) {
                fml = tmp;
                break;
            }
        }
        std::cout << "(assert " << fml << ")\n";
        ctx.assert_expr(fml);
    }

    
    
    void fuzz_round(unsigned& num_rounds, unsigned lvl) {
        unsigned num_rounds2 = 0;
        lbool is_sat = l_true;    
        std::cout << "(push)\n";
        ctx.push();
        unsigned r = 0;
        while (is_sat == l_true && r <= num_rounds + 1) {
            add_ineq();
            std::cout << "(check-sat)\n";
            is_sat = ctx.check();
            if (lvl > 0 && is_sat == l_true) {
                fuzz_round(num_rounds2, lvl-1);
            }
            ++r;
        }
        num_rounds = r;
        std::cout << "; number of rounds: " << num_rounds << " level: " << lvl << "\n";
        ctx.pop(1);
        std::cout << "(pop)\n";
    }

};



static void fuzz_pb() 
{
    ast_manager m;
    reg_decl_plugins(m);
    pb_fuzzer fuzzer(m);
    fuzzer.fuzz();
}

void tst_theory_pb() {

    fuzz_pb();

    ast_manager m;
    smt_params params;
    params.m_model = true;
    reg_decl_plugins(m);
    expr_ref tmp(m);
    
    enable_trace("pb");
    for (unsigned N = 4; N < 11; ++N) {
        for (unsigned i = 0; i < (1u << N); ++i) {
            smt::literal_vector lits(N, smt::false_literal);
            unsigned k = populate_literals(i, lits);        
            std::cout << "k:" << k << " " << N << "\n";
            std::cout.flush();
            TRACE("pb", tout << "k " << k << ": ";
                  for (unsigned j = 0; j < lits.size(); ++j) {
                      tout << lits[j] << " ";
                  }
                  tout << "\n";);
            {
                smt::context ctx(m, params);
                ctx.push();
                smt::literal l = smt::theory_pb::assert_ge(ctx, k+1, lits.size(), lits.c_ptr());
                if (l != smt::false_literal) {
                    ctx.assign(l, 0, false);
                    TRACE("pb", tout << "assign: " << l << "\n";
                          ctx.display(tout););
                    VERIFY(l_false == ctx.check());
                }
                ctx.pop(1);
            }
            {
                smt::context ctx(m, params);            
                ctx.push();
                smt::literal l = smt::theory_pb::assert_ge(ctx, k, lits.size(), lits.c_ptr());
                SASSERT(l != smt::false_literal);
                ctx.assign(l, 0, false);
                TRACE("pb", ctx.display(tout););
                VERIFY(l_true == ctx.check());
                ctx.pop(1);
            }
        }
    }
}
