/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    pbmax.cpp

Abstract:

    pb based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "pbmax.h"
#include "pb_decl_plugin.h"
#include "uint_set.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"


namespace opt {

    // ----------------------------------
    // incrementally add pseudo-boolean 
    // lower bounds.

    class pbmax : public maxsmt_solver_base {
    public:
        pbmax(context& c, weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft) {
        }
        
        virtual ~pbmax() {}

        lbool operator()() {

            TRACE("opt", s().display(tout); tout << "\n";
                  for (unsigned i = 0; i < m_soft.size(); ++i) {
                      tout << mk_pp(m_soft[i].get(), m) << " " << m_weights[i] << "\n";
                  }
                  );
            pb_util u(m);
            expr_ref fml(m), val(m);
            app_ref b(m);
            expr_ref_vector nsoft(m);
            init();            
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                nsoft.push_back(mk_not(m_soft[i].get()));
            }
            lbool is_sat = l_true;
            while (l_true == is_sat) {
                TRACE("opt", s().display(tout<<"looping\n"); 
                      model_smt2_pp(tout << "\n", m, *(m_model.get()), 0););
                m_upper.reset();
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    VERIFY(m_model->eval(nsoft[i].get(), val));
                    m_assignment[i] = !m.is_true(val);
                    if (!m_assignment[i]) {
                        m_upper += m_weights[i];
                    }
                }                     
                IF_VERBOSE(1, verbose_stream() << "(opt.pb [" << m_lower << ":" << m_upper << "])\n";);
                TRACE("opt", tout << "new upper: " << m_upper << "\n";);
                
                fml = u.mk_lt(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper);
                solver::scoped_push _scope2(s());
                s().assert_expr(fml);
                is_sat = s().check_sat(0,0);
                if (m_cancel) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    s().get_model(m_model);
                }
            }            
            if (is_sat == l_false) {
                is_sat = l_true;
                m_lower = m_upper;
            }
            TRACE("opt", tout << "lower: " << m_lower << "\n";);
            return is_sat;
        }
    };

    maxsmt_solver_base* mk_pbmax(
        context & c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(pbmax, c, ws, soft);
    }

}
