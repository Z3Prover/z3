/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.cpp

Abstract:
    Fu & Malik built-in optimization method.
    Adapted from sample code in C.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

--*/

#include "fu_malik.h"
#include "qfbv_tactic.h"
#include "tactic2solver.h"
#include "goal.h"
#include "probe.h"
#include "tactic.h"
#include "smt_context.h"

/**
   \brief Fu & Malik procedure for MaxSAT. This procedure is based on 
   unsat core extraction and the at-most-one constraint.

   Return the number of soft-constraints that can be
   satisfied.  Return -1 if the hard-constraints cannot be
   satisfied. That is, the formula cannot be satisfied even if all
   soft-constraints are ignored.

   For more information on the Fu & Malik procedure:

   Z. Fu and S. Malik, On solving the partial MAX-SAT problem, in International
   Conference on Theory and Applications of Satisfiability Testing, 2006.
*/
namespace opt {

    struct fu_malik::imp {
        ast_manager& m;        
        expr_ref_vector m_soft;
        expr_ref_vector m_orig_soft;
        expr_ref_vector m_aux;
        expr_ref_vector m_assignment;
        unsigned        m_upper_size;

        ref<solver>     m_s;
        solver &        m_original_solver;
        bool            m_use_new_bv_solver; 

        imp(ast_manager& m, solver& s, expr_ref_vector const& soft):
            m(m),
            m_s(&s),
            m_soft(soft),
            m_orig_soft(soft),
            m_aux(m),
            m_assignment(m),
            m_original_solver(s),
            m_use_new_bv_solver(false)
        {
            m_upper_size = m_soft.size() + 1;
        }

        solver& s() { return *m_s; }

        /**
           \brief One step of the Fu&Malik algorithm.
           
           Input:    soft constraints + aux-vars (aka answer literals) 
           Output:   done/not-done  when not done return updated set of soft-constraints and aux-vars. 
           - if SAT --> terminates
           - if UNSAT 
           * compute unsat core
           * add blocking variable to soft-constraints in the core
           - replace soft-constraint with the one with the blocking variable
           - we should also add an aux-var
           - replace aux-var with a new one
           * add at-most-one constraint with blocking 
        */

        typedef obj_hashtable<expr> expr_set;

        void set2vector(expr_set const& set, expr_ref_vector & es) const {
            es.reset();
            expr_set::iterator it = set.begin(), end = set.end();
            for (; it != end; ++it) {
                es.push_back(*it);
            }
        }

        void set_union(expr_set const& set1, expr_set const& set2, expr_set & set) const {
            set.reset();
            expr_set::iterator it = set1.begin(), end = set1.end();
            for (; it != end; ++it) {
                set.insert(*it);
            }
            it = set2.begin();
            end = set2.end();
            for (; it != end; ++it) {
                set.insert(*it);
            }
        }

        void quick_explain(expr_ref_vector const& assumptions, expr_ref_vector & literals, bool has_set, expr_set & core) {
            if (has_set && s().check_sat(assumptions.size(), assumptions.c_ptr()) == l_false) {
                core.reset();
                return;
            }
            
            SASSERT(!literals.empty());
            if (literals.size() == 1) {
                core.reset();
                core.insert(literals[0].get());
                return;
            }

            unsigned mid = literals.size()/2;
            expr_ref_vector ls1(m), ls2(m);
            ls1.append(mid, literals.c_ptr());
            ls2.append(literals.size()-mid, literals.c_ptr() + mid);
#if Z3DEBUG
            expr_ref_vector ls(m); 
            ls.append(ls1); 
            ls.append(ls2); 
            SASSERT(ls.size() == literals.size());
            for (unsigned i = 0; i < literals.size(); ++i) {
                SASSERT(ls[i].get() == literals[i].get());
            }
#endif            
            expr_ref_vector as1(m);
            as1.append(assumptions);
            as1.append(ls1);
            expr_set core2;
            quick_explain(as1, ls2, !ls1.empty(), core2);

            expr_ref_vector as2(m), cs2(m);
            as2.append(assumptions);            
            set2vector(core2, cs2);
            as2.append(cs2);
            expr_set core1;
            quick_explain(as2, ls1, !core2.empty(), core1);

            set_union(core1, core2, core);
        }

        lbool step() {
            IF_VERBOSE(0, verbose_stream() << "(opt.max_sat step " << m_soft.size() + 2 - m_upper_size << ")\n";);
            expr_ref_vector assumptions(m), block_vars(m);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                assumptions.push_back(m.mk_not(m_aux[i].get()));
            }
            lbool is_sat = s().check_sat(assumptions.size(), assumptions.c_ptr());
            if (is_sat != l_false) {
                return is_sat;
            }

            ptr_vector<expr> core;
            if (m_use_new_bv_solver) {
                // Binary search for minimal unsat core
                expr_set core_set;
                expr_ref_vector empty(m);
                quick_explain(empty, assumptions, true, core_set);
                expr_set::iterator it = core_set.begin(), end = core_set.end();
                for (; it != end; ++it) {
                    core.push_back(*it);
                }

                //// Forward linear search for unsat core
                //unsigned i = 0;
                //while (s().check_sat(core.size(), core.c_ptr()) != l_false) {
                //    IF_VERBOSE(0, verbose_stream() << "(opt.max_sat get-unsat-core round " << i << ")\n";);
                //    core.push_back(assumptions[i].get());
                //    ++i;
                //}

                //// Backward linear search for unsat core
                //unsigned i = 0;
                //core.append(assumptions.size(), assumptions.c_ptr());
                //while (!core.empty() && s().check_sat(core.size()-1, core.c_ptr()) == l_false) {
                //    IF_VERBOSE(0, verbose_stream() << "(opt.max_sat get-unsat-core round " << i << ")\n";);
                //    core.pop_back();
                //    ++i;
                //}

                IF_VERBOSE(0, verbose_stream() << "(opt.max_sat unsat-core of size " << core.size() << ")\n";);
            }
            else {
                s().get_unsat_core(core);
            }

            SASSERT(!core.empty());

            // Update soft-constraints and aux_vars
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                
                bool found = false;
                for (unsigned j = 0; !found && j < core.size(); ++j) {
                    found = assumptions[i].get() == core[j];
                }
                if (!found) {
                    continue;
                }
                expr_ref block_var(m);
                block_var = m.mk_fresh_const("block_var", m.mk_bool_sort());
                m_aux[i] = m.mk_fresh_const("aux", m.mk_bool_sort());
                m_soft[i] = m.mk_or(m_soft[i].get(), block_var);
                block_vars.push_back(block_var);
                s().assert_expr(m.mk_or(m_soft[i].get(), m_aux[i].get()));
            }
            SASSERT (!block_vars.empty());
            assert_at_most_one(block_vars);
            IF_VERBOSE(0, verbose_stream() << "(opt.max_sat # of non-blocked soft constraints: " << m_soft.size() - block_vars.size() << ")\n";);
            return l_false;
        }

        void assert_at_most_one(expr_ref_vector const& block_vars) {
            expr_ref has_one(m), has_zero(m), at_most_one(m);
            mk_at_most_one(block_vars.size(), block_vars.c_ptr(), has_one, has_zero);
            at_most_one = m.mk_or(has_one, has_zero);
            s().assert_expr(at_most_one);
        }

        void mk_at_most_one(unsigned n, expr* const * vars, expr_ref& has_one, expr_ref& has_zero) {
            SASSERT(n != 0);
            if (n == 1) {
                has_one = vars[0];
                has_zero = m.mk_not(vars[0]);
            }
            else {
                unsigned mid = n/2;
                expr_ref has_one1(m), has_one2(m), has_zero1(m), has_zero2(m);
                mk_at_most_one(mid,   vars,     has_one1, has_zero1);
                mk_at_most_one(n-mid, vars+mid, has_one2, has_zero2);
                has_one = m.mk_or(m.mk_and(has_one1, has_zero2), m.mk_and(has_one2, has_zero1));
                has_zero  = m.mk_and(has_zero1, has_zero2);
            }
        }
        
        void set_solver() { 
            opt_solver & opt_s = opt_solver::to_opt(m_original_solver);
            if (opt_s.is_dumping_benchmark())
                return;

            solver& current_solver = s();
            goal g(m, true, false);
            unsigned num_assertions = current_solver.get_num_assertions();
            for (unsigned i = 0; i < num_assertions; ++i) {
                g.assert_expr(current_solver.get_assertion(i));
            }            
            probe *p = mk_is_qfbv_probe();
            bool all_bv = (*p)(g).is_true();
            if (all_bv) {                
                smt::context & ctx = opt_s.get_context();                
                tactic_ref t = mk_qfbv_tactic(m, ctx.get_params());                  
                // The new SAT solver hasn't supported unsat core yet
                m_s = mk_tactic2solver(m, t.get());
                SASSERT(m_s != &m_original_solver);
                for (unsigned i = 0; i < num_assertions; ++i) {
                    m_s->assert_expr(current_solver.get_assertion(i));
                }
                m_use_new_bv_solver = true;
                IF_VERBOSE(0, verbose_stream() << "Force to use the new BV solver." << std::endl;);
            }
        }

        // TBD: bug when cancel flag is set, fu_malik returns is_sat == l_true instead of l_undef
        lbool operator()() {
            set_solver();
            lbool is_sat = s().check_sat(0,0);
            if (!m_soft.empty() && is_sat == l_true) {
                solver::scoped_push _sp(s());
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    m_aux.push_back(m.mk_fresh_const("p", m.mk_bool_sort()));
                    s().assert_expr(m.mk_or(m_soft[i].get(), m_aux[i].get()));
                }
                
                lbool is_sat = l_true;                
                do {
                    is_sat = step();
                    --m_upper_size;
                }
                while (is_sat == l_false);
                
                if (is_sat == l_true) {
                    // Get a list of satisfying m_soft
                    model_ref model;
                    s().get_model(model);

                    m_assignment.reset();                    
                    for (unsigned i = 0; i < m_orig_soft.size(); ++i) {
                        expr_ref val(m);
                        VERIFY(model->eval(m_orig_soft[i].get(), val));
                        if (m.is_true(val)) {
                            m_assignment.push_back(m_orig_soft[i].get());
                        }
                    }
                }
            }
            statistics st;
            s().collect_statistics(st);
            SASSERT(st.size() > 0);            
            opt_solver & opt_s = opt_solver::to_opt(m_original_solver);
            opt_s.set_interim_stats(st);
            // We are done and soft_constraints has 
            // been updated with the max-sat assignment.            
            return is_sat;            
        }

    };

    fu_malik::fu_malik(ast_manager& m, solver& s, expr_ref_vector& soft_constraints) {
        m_imp = alloc(imp, m, s, soft_constraints);
    }
    fu_malik::~fu_malik() {
        dealloc(m_imp);
    }
    
    lbool fu_malik::operator()() {
        return (*m_imp)();
    }
    rational fu_malik::get_lower() const {
        return rational(0);
    }
    rational fu_malik::get_upper() const {
        return rational(m_imp->m_upper_size);
    }
    rational fu_malik::get_value() const {
        return rational(m_imp->m_assignment.size());
    }
    expr_ref_vector fu_malik::get_assignment() const {
        return m_imp->m_assignment;
    }
    void fu_malik::set_cancel(bool f) {
        // no-op
    }



};


