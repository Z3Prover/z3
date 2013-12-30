#include "smt_context.h"
#include "ast_pp.h"
#include "model_v2_pp.h"
#include "reg_decl_plugins.h"
#include "theory_pb.h"

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

void tst_theory_pb() {
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
