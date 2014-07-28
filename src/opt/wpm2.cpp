/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    wpm2.cpp

Abstract:

    wpn2 based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "wpm2.h"
#include "pbmax.h"
#include "pb_decl_plugin.h"
#include "uint_set.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"


namespace opt {

    // ------------------------------------------------------
    // AAAI 2010
    class wpm2 : public maxsmt_solver_base {
        scoped_ptr<maxsmt_solver_base> maxs;
    public:
        wpm2(opt_solver* s, ast_manager& m, maxsmt_solver_base* _maxs, params_ref& p, 
             vector<rational> const& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(s, m, p, ws, soft), maxs(_maxs) {
        }

        virtual ~wpm2() {}

        lbool operator()() {
            enable_sls();
            IF_VERBOSE(1, verbose_stream() << "(opt.wpm2)\n";);
            solver::scoped_push _s(s());
            pb_util u(m);
            app_ref fml(m), a(m), b(m), c(m);
            expr_ref val(m);
            expr_ref_vector block(m), ans(m), al(m), am(m);
            obj_map<expr, unsigned> ans_index;
            vector<rational> amk;
            vector<uint_set> sc;
            init();
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                rational w = m_weights[i];

                b = mk_fresh_bool("b");
                block.push_back(b);
                expr* bb = b;

                a = mk_fresh_bool("a");
                ans.push_back(a);
                ans_index.insert(a, i);
                fml = m.mk_or(m_soft[i].get(), b, m.mk_not(a));
                s().assert_expr(fml);
                
                c = mk_fresh_bool("c");
                fml = m.mk_implies(c, u.mk_le(1,&w,&bb,rational(0)));
                s().assert_expr(fml);

                sc.push_back(uint_set());
                sc.back().insert(i);                
                am.push_back(c);
                amk.push_back(rational(0));
            }

            while (true) {
                expr_ref_vector asms(m);
                ptr_vector<expr> core;
                asms.append(ans);
                asms.append(am);
                lbool is_sat = s().check_sat(asms.size(), asms.c_ptr());
                TRACE("opt", 
                      tout << "\nassumptions: ";
                      for (unsigned i = 0; i < asms.size(); ++i) {
                          tout << mk_pp(asms[i].get(), m) << " ";
                      }
                      tout << "\n" << is_sat << "\n";
                      tout << "upper: " << m_upper << "\n";
                      tout << "lower: " << m_lower << "\n";
                      if (is_sat == l_true) {
                          model_ref mdl;
                          s().get_model(mdl);
                          model_smt2_pp(tout, m, *(mdl.get()), 0);
                      });

                if (m_cancel && is_sat != l_false) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    m_upper = m_lower;
                    s().get_model(m_model);
                    for (unsigned i = 0; i < block.size(); ++i) {
                        VERIFY(m_model->eval(m_soft[i].get(), val));
                        TRACE("opt", tout << mk_pp(block[i].get(), m) << " " << val << "\n";);
                        m_assignment[i] = m.is_true(val);
                    }
                }
                if (is_sat != l_false) {
                    return is_sat;
                }
                s().get_unsat_core(core);
                if (core.empty()) {
                    return l_false;
                }
                TRACE("opt",
                      tout << "core: ";
                      for (unsigned i = 0; i < core.size(); ++i) {
                          tout << mk_pp(core[i],m) << " ";
                      }
                      tout << "\n";);
                uint_set A;
                for (unsigned i = 0; i < core.size(); ++i) {
                    unsigned j;
                    if (ans_index.find(core[i], j)) {
                        A.insert(j);
                    }
                }
                if (A.empty()) {
                    return l_false;
                }
                uint_set B;
                rational k(0);
                rational old_lower(m_lower);
                for (unsigned i = 0; i < sc.size(); ++i) {
                    uint_set t(sc[i]);
                    t &= A;
                    if (!t.empty()) {
                        B |= sc[i];
                        k += amk[i];
                        m_lower -= amk[i];
                        sc[i] = sc.back();
                        sc.pop_back();
                        am[i] = am.back();
                        am.pop_back();
                        amk[i] = amk.back();
                        amk.pop_back();
                        --i;
                    }
                }
                vector<rational> ws;
                expr_ref_vector  bs(m);
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    if (B.contains(i)) {
                        ws.push_back(m_weights[i]);
                        bs.push_back(block[i].get());
                    }
                }
                TRACE("opt", tout << "at most bound: " << k << "\n";);
                is_sat = new_bound(al, ws, bs, k);
                if (is_sat != l_true) {
                    return is_sat;
                }
                m_lower += k;
                SASSERT(m_lower > old_lower);
                TRACE("opt", tout << "new bound: " << m_lower << "\n";);
                expr_ref B_le_k(m), B_ge_k(m);
                B_le_k = u.mk_le(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                B_ge_k = u.mk_ge(ws.size(), ws.c_ptr(), bs.c_ptr(), k);
                s().assert_expr(B_ge_k);
                al.push_back(B_ge_k);
                IF_VERBOSE(1, verbose_stream() << "(opt.wpm2 [" << m_lower << ":" << m_upper << "])\n";);
                IF_VERBOSE(2, verbose_stream() << "New lower bound: " << B_ge_k << "\n";);

                c = mk_fresh_bool("c");
                fml = m.mk_implies(c, B_le_k);
                s().assert_expr(fml);
                sc.push_back(B);
                am.push_back(c);
                amk.push_back(k);
            }            
        }

        virtual void set_cancel(bool f) { 
            maxsmt_solver_base::set_cancel(f); 
            maxs->set_cancel(f); 
        }

        virtual void collect_statistics(statistics& st) const {
            maxsmt_solver_base::collect_statistics(st);
            maxs->collect_statistics(st);
        }

    private:
        lbool new_bound(expr_ref_vector const& al, 
                        vector<rational> const& ws, 
                        expr_ref_vector const& bs, 
                        rational& k) {
            pb_util u(m);
            expr_ref_vector al2(m);
            al2.append(al);
            // w_j*b_j > k
            al2.push_back(m.mk_not(u.mk_le(ws.size(), ws.c_ptr(), bs.c_ptr(), k)));            
            return bound(al2, ws, bs, k);
        }

        // 
        // minimal k, such that  al & w_j*b_j >= k is sat
        // minimal k, such that  al & 3*x + 4*y >= k is sat
        // minimal k, such that al & (or (not x) w3) & (or (not y) w4)
        //
        lbool bound(expr_ref_vector const& al, 
                    vector<rational> const& ws, 
                    expr_ref_vector const& bs,
                    rational& k) {
            expr_ref_vector nbs(m);
            opt_solver::scoped_push _sc(maxs->s());
            for (unsigned i = 0; i < al.size(); ++i) {
                maxs->add_hard(al[i]);
            }
            for (unsigned i = 0; i < bs.size(); ++i) {
                nbs.push_back(mk_not(bs[i]));
            }    
            TRACE("opt", 
                  maxs->s().display(tout);
                  tout << "\n";
                  for (unsigned i = 0; i < bs.size(); ++i) {
                      tout << mk_pp(bs[i], m) << " " << ws[i] << "\n";
                  });
            maxs->init_soft(ws, nbs);
            lbool is_sat = maxs->s().check_sat(0,0);
            if (is_sat == l_true) {
                maxs->set_model();
                is_sat = (*maxs)();
            }
            SASSERT(maxs->get_lower() > k);
            k = maxs->get_lower();
            return is_sat;
        }
    };

    maxsmt_solver_base* opt::mk_wpm2(ast_manager& m, opt_solver* s, params_ref& p, 
                                    vector<rational> const& ws, expr_ref_vector const& soft) {

        ref<opt_solver> s0 = alloc(opt_solver, m, p, symbol());
        // initialize model.
        s0->check_sat(0,0);
        maxsmt_solver_base* s2 = mk_pbmax(m, s0.get(), p, ws, soft);
        return alloc(wpm2, s, m, s2, p, ws, soft);
    }

}
