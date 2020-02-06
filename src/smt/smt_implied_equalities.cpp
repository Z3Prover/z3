/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_implied_equalities.cpp

Abstract:

    Procedure for obtaining implied equalities relative to the
    state of a solver.

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-29

Revision History:


--*/

#include "smt/smt_implied_equalities.h"
#include "util/union_find.h"
#include "ast/ast_pp.h"
#include "ast/array_decl_plugin.h"
#include "util/uint_set.h"
#include "smt/smt_value_sort.h"
#include "model/model_smt2_pp.h"
#include "util/stopwatch.h"
#include "model/model.h"
#include "solver/solver.h"

namespace {

    class get_implied_equalities_impl {
        
        ast_manager&                       m;
        solver&                            m_solver;
        union_find_default_ctx             m_df;
        union_find<union_find_default_ctx> m_uf;
        array_util                         m_array_util;
        stopwatch                          m_stats_timer;
        unsigned                           m_stats_calls;
        stopwatch                          m_stats_val_eq_timer;
        static stopwatch                   s_timer;
        static stopwatch                   s_stats_val_eq_timer;
                
        struct term_id {
            expr_ref term;
            unsigned id;
            term_id(expr_ref t, unsigned id): term(t), id(id) {}
        };
        
        typedef vector<term_id> term_ids;
        
        typedef obj_map<sort, term_ids> sort2term_ids; // partition of terms by sort.
        
        void partition_terms(unsigned num_terms, expr* const* terms, sort2term_ids& termids) {
            for (unsigned i = 0; i < num_terms; ++i) {
                sort* s = m.get_sort(terms[i]);
                term_ids& vec = termids.insert_if_not_there2(s, term_ids())->get_data().m_value;
                vec.push_back(term_id(expr_ref(terms[i],m), i));
            }
        }
        
        /**
           \brief Basic implied equalities method.
           It performs a simple N^2 loop over all pairs of terms.

           n1, .., n_k, 
           t1, .., t_l
        */
        
        void get_implied_equalities_filter_basic(uint_set const& non_values, term_ids& terms) {
            m_stats_timer.start();
            uint_set root_indices;
            for (unsigned j = 0; j < terms.size(); ++j) {
                if (terms[j].id == m_uf.find(terms[j].id)) {
                    root_indices.insert(j);
                }
            }
            uint_set::iterator it = non_values.begin(), end = non_values.end();

            for (; it != end; ++it) {
                unsigned i = *it;
                expr* t = terms[i].term;
                uint_set::iterator it2 = root_indices.begin(), end2 = root_indices.end();
                bool found_root_value = false;
                for (; it2 != end2; ++it2) {
                    unsigned j = *it2;
                    if (j == i) continue;
                    if (j < i && non_values.contains(j)) continue;
                    if (found_root_value && !non_values.contains(j)) continue;
                    expr* s = terms[j].term;
                    SASSERT(m.get_sort(t) == m.get_sort(s));
                    ++m_stats_calls;
                    m_solver.push();
                    m_solver.assert_expr(m.mk_not(m.mk_eq(s, t)));
                    bool is_eq = l_false == m_solver.check_sat(0,nullptr);
                    m_solver.pop(1);
                    TRACE("get_implied_equalities", tout << mk_pp(t, m) << " = " << mk_pp(s, m) << " " << (is_eq?"eq":"unrelated") << "\n";);
                    if (is_eq) {
                        m_uf.merge(terms[i].id, terms[j].id);
                        if (!non_values.contains(j)) {
                            found_root_value = true;
                        }
                    }
                }
            }            
            m_stats_timer.stop();
        }

        void get_implied_equalities_basic(term_ids& terms) {
            for (unsigned i = 0; i < terms.size(); ++i) {
                if (terms[i].id != m_uf.find(terms[i].id)) {
                    continue;
                }
                expr* t = terms[i].term;
                for (unsigned j = 0; j < i; ++j) {
                    expr* s = terms[j].term;
                    SASSERT(m.get_sort(t) == m.get_sort(s));
                    ++m_stats_calls;
                    m_stats_timer.start();
                    m_solver.push();
                    m_solver.assert_expr(m.mk_not(m.mk_eq(s, t)));
                    bool is_eq = l_false == m_solver.check_sat(0,nullptr);
                    m_solver.pop(1);
                    m_stats_timer.stop();
                    TRACE("get_implied_equalities", tout << mk_pp(t, m) << " = " << mk_pp(s, m) << " " << (is_eq?"eq":"unrelated") << "\n";);
                    if (is_eq) {
                        m_uf.merge(terms[i].id, terms[j].id);
                        break;
                    }                    
                }
            }
        }                
        
        /**
           \brief Extract implied equalities for a collection of terms in the current context.
           
           The routine relies on model values being unique for equal terms.           
           So in particular, arrays that are equal should be canonized to the same value.
           This is not the case for Z3's models of arrays.
           Arrays are treated by extensionality: introduce a fresh index and compare
           the select of the arrays.
        */
        void get_implied_equalities_model_based(model_ref& model, term_ids& terms) {
            
            SASSERT(!terms.empty());

            sort* srt = m.get_sort(terms[0].term);
                       
            if (m_array_util.is_array(srt)) {

                m_solver.push();
                unsigned arity = get_array_arity(srt);
                expr_ref_vector args(m);
                args.push_back(nullptr);
                for (unsigned i = 0; i < arity; ++i) {
                    sort* srt_i = get_array_domain(srt, i);
                    expr* idx = m.mk_fresh_const("index", srt_i);
                    args.push_back(idx);
                }
                for (unsigned i = 0; i < terms.size(); ++i) {
                    args[0] = terms[i].term;
                    terms[i].term = m.mk_app(m_array_util.get_family_id(), OP_SELECT, 0, nullptr, args.size(), args.c_ptr());
                }
                assert_relevant(terms);
                VERIFY(m_solver.check_sat(0,nullptr) != l_false);
                model_ref model1;
                m_solver.get_model(model1);
                SASSERT(model1.get());
                get_implied_equalities_model_based(model1, terms);
                m_solver.pop(1);
                return;
            }

            uint_set non_values;
            
            if (!smt::is_value_sort(m, srt)) {
                for (unsigned i = 0; i < terms.size(); ++i) {
                    non_values.insert(i);
                }
                get_implied_equalities_filter_basic(non_values, terms);
                //get_implied_equalities_basic(terms);
                return;
            }
            
            expr_ref_vector vals(m);
            expr_ref vl(m), eq(m);
            obj_map<expr, unsigned_vector>  vals_map;
            
            m_stats_val_eq_timer.start();
            s_stats_val_eq_timer.start();

            params_ref p;
            p.set_bool("produce_models", false);
            m_solver.updt_params(p);

            for (unsigned i = 0; i < terms.size(); ++i) {
                expr* t = terms[i].term;
                vl = (*model)(t);
                TRACE("get_implied_equalities", tout << mk_pp(t, m) << " |-> " << mk_pp(vl, m) << "\n";);
                reduce_value(model, vl);
                if (!m.is_value(vl)) {
                    TRACE("get_implied_equalities", tout << "Not a value: " << mk_pp(vl, m) << "\n";);
                    non_values.insert(i);
                    continue;
                }
                vals.push_back(vl);
                unsigned_vector& vec = vals_map.insert_if_not_there2(vl, unsigned_vector())->get_data().m_value;
                bool found = false;

                for (unsigned j = 0; !found && j < vec.size(); ++j) {
                    expr* s = terms[vec[j]].term;
                    m_solver.push();
                    m_solver.assert_expr(m.mk_not(m.mk_eq(t, s)));
                    lbool is_sat = m_solver.check_sat(0,nullptr);
                    m_solver.pop(1);
                    TRACE("get_implied_equalities", tout << mk_pp(t, m) << " = " << mk_pp(s, m) << " " << is_sat << "\n";);
                    if (is_sat == l_false) {
                        found = true;
                        m_uf.merge(terms[i].id, terms[vec[j]].id);
                    }
                }
                if (!found) {
                    vec.push_back(i);
                }
            }
            m_stats_val_eq_timer.stop();
            s_stats_val_eq_timer.stop();
            p.set_bool("produce_models", true);
            m_solver.updt_params(p);


            if (!non_values.empty()) {
                TRACE("get_implied_equalities", model_smt2_pp(tout, m, *model, 0););
                get_implied_equalities_filter_basic(non_values, terms);
                //get_implied_equalities_basic(terms);
            }
        }

        
        void get_implied_equalities_core(model_ref& model, term_ids& terms) {
            get_implied_equalities_model_based(model, terms);
            //get_implied_equalities_basic(terms);
        }
        

        void assert_relevant(unsigned num_terms, expr* const* terms) {
            for (unsigned i = 0; i < num_terms; ++i) {                
                sort* srt = m.get_sort(terms[i]);
                if (!m_array_util.is_array(srt)) {
                    m_solver.assert_expr(m.mk_app(m.mk_func_decl(symbol("Relevant!"), 1, &srt, m.mk_bool_sort()), terms[i]));
                }
            }            
        }

        void assert_relevant(term_ids& terms) {
            for (unsigned i = 0; i < terms.size(); ++i) {
                expr* t = terms[i].term;
                sort* srt = m.get_sort(t);
                if (!m_array_util.is_array(srt)) {
                    m_solver.assert_expr(m.mk_app(m.mk_func_decl(symbol("Relevant!"), 1, &srt, m.mk_bool_sort()), t));
                }
            }
        }

        void reduce_value(model_ref& model, expr_ref& vl) {
            expr* c, *e1, *e2;
            while (m.is_ite(vl, c, e1, e2)) {
                lbool r = reduce_cond(model, c);
                switch(r) {
                case l_true: 
                    vl = e1;
                    break;
                case l_false: 
                    vl = e2;
                    break;
                default:
                    return;
                }
            }
        }

        lbool reduce_cond(model_ref& model, expr* e) {
            expr* e1 = nullptr, *e2 = nullptr;
            if (m.is_eq(e, e1, e2) && m_array_util.is_as_array(e1) && m_array_util.is_as_array(e2)) {
                if (e1 == e2) {
                    return l_true;
                }
                func_decl* f1 = m_array_util.get_as_array_func_decl(to_app(e1));
                func_decl* f2 = m_array_util.get_as_array_func_decl(to_app(e2));
                func_interp* fi1 = model->get_func_interp(f1);
                func_interp* fi2 = model->get_func_interp(f2);
                if (fi1 == fi2) {
                    return l_true;
                }
                unsigned n1 = fi1->num_entries();
                for (unsigned i = 0; i < n1; ++i) {
                    func_entry const* h1 = fi1->get_entry(i);
                    for (unsigned j = 0; j < fi1->get_arity(); ++j) {
                        if (!m.is_value(h1->get_arg(j))) {
                            return l_undef;
                        }
                    }
                    func_entry* h2 = fi2->get_entry(h1->get_args());
                    if (h2 && 
                        h1->get_result() != h2->get_result() &&
                        m.is_value(h1->get_result()) &&
                        m.is_value(h2->get_result())) {
                        return l_false;
                    }
                }                               
            }
            return l_undef;
        }

    public:
        
        get_implied_equalities_impl(ast_manager& m, solver& s) : m(m), m_solver(s), m_uf(m_df), m_array_util(m), m_stats_calls(0) {}
        
        lbool operator()(unsigned num_terms, expr* const* terms, unsigned* class_ids) {
            params_ref p;
            p.set_bool("produce_models", true);
            m_solver.updt_params(p);
            sort2term_ids termids;
            stopwatch timer;
            timer.start();
            s_timer.start();

            for (unsigned i = 0; i < num_terms; ++i) {
                m_uf.mk_var();
            }

            m_solver.push();
            assert_relevant(num_terms, terms);
            lbool is_sat = m_solver.check_sat(0,nullptr);
            
            if (is_sat != l_false) {      
                model_ref model;
                m_solver.get_model(model);
                SASSERT(model.get());
                  
                partition_terms(num_terms, terms, termids);
                sort2term_ids::iterator it = termids.begin(), end = termids.end();
                for (; it != end; ++it) {
                    term_ids& term_ids = it->m_value;
                    get_implied_equalities_core(model, term_ids);                
                    for (unsigned i = 0; i < term_ids.size(); ++i) {
                        class_ids[term_ids[i].id] = m_uf.find(term_ids[i].id);
                    }
                }
                TRACE("get_implied_equalities",
                      for (unsigned i = 0; i < num_terms; ++i) {
                          tout << mk_pp(terms[i], m) << " |-> " << class_ids[i] << "\n";
                      });
            }
            m_solver.pop(1);
            timer.stop();
            s_timer.stop();
            IF_VERBOSE(1, verbose_stream()  << s_timer.get_seconds() << "\t" << num_terms << "\t" 
                       << timer.get_seconds()   << "\t" << m_stats_calls << "\t" 
                       << m_stats_timer.get_seconds() << "\t" 
                       << m_stats_val_eq_timer.get_seconds() << "\t"
                       << s_stats_val_eq_timer.get_seconds() << "\n";);
            return is_sat;
        }
    };

    stopwatch get_implied_equalities_impl::s_timer;
    stopwatch get_implied_equalities_impl::s_stats_val_eq_timer;
}

namespace smt {
    lbool implied_equalities(ast_manager& m, solver& solver, unsigned num_terms, expr* const* terms, unsigned* class_ids) {        
        get_implied_equalities_impl gi(m, solver);
        return gi(num_terms, terms, class_ids);
    }
}







#if 0
    // maxsat class for internal purposes.
    class maxsat {
        ast_manager& m;
        solver&      m_solver;
    public:
        maxsat(solver& s) : m(s.m()), m_solver(s) {}

        lbool operator()(ptr_vector<expr>& soft_cnstrs) {
            return l_undef;
        }

    };

    class term_equivs {
        union_find_default_ctx             m_df;
        union_find<union_find_default_ctx> m_uf;
        obj_map<expr,unsigned>             m_term2idx;
        ptr_vector<expr>                   m_idx2term;
        
    public:
        term_equivs(): m_uf(m_df) {}
        
        void merge(expr* t, expr* s) {
            m_uf.merge(var(t), var(s));
        }
    private:
        unsigned var(expr* t) {
            map::obj_map_entry* e = m_term2idx.insert_if_not_there(t, m_idx2term.size());
            unsigned idx = e->get_data().m_value; 
            if (idx == m_idx2term.size()) {
                m_idx2term.push_back(t);
            }
            return idx;
        }            
    };

    /**
       \brief class to find implied equalities.

       It implements the following half-naive algorithm.
       The algorithm is half-naive because the terms being checked for equivalence class membership
       are foreign and it is up to the theory integration whether pairs of interface equalities
       are checked. The idea is that the model-based combination would avoid useless equality literals 
       in the core.
       An alternative algorithm could use 'distinct' and an efficient solver for 'distinct'.

       Given terms t1, ..., tn, of the same type.
       - assert f(t1) = 1, .., f(tn) = n.
       - find MAX-SAT set A1, let the other literals be in B.
       - find MAX-SAT set of B, put it in A2, etc.
       - we now have MAX-SAT sets A1, A2, ... A_m.
       - terms in each set A_i can be different, but cannot be different at the same time as elements in A_{i+1}.
       - for i = m to 2 do:
       -   Let A = A_i B = A_{i-1}
       -   assert g(A) = 0, g(B) = 1
       -   find MAX-SAT set C over this constraint. 
       -   For each element t from A\C 
       -           check if g(t) = 0 and g(B) = 1 is unsat
       -           minimize core, if there is pair such that 
       -           g(t) = 0, g(b) = 1 is unsat, then equality is forced.
    */

    class implied_equalities_finder {
        ast_manager& m;
        solver&      m_solver;
        term_equivs  m_find;
        expr_ref_vector m_refs;
        obj_map<expr,expr*> m_fs; // t_i -> f(t_i) = i
        obj_map<expr,epxr*> m_gs; // t_i -> g(t_i)

    public:
        implied_equalities_finder(solver& solver): m(solver.m()), m_solver(solver), m_refs(m) {}

        lbool operator()(unsigned num_terms, expr* const* terms, unsigned* class_ids) {
            m_find.reset();
            //
            return l_undef;
        }
    private:

        void initialize(unsigned num_terms, expr* const* terms) {
            sort_ref bv(m);
            expr_ref eq(m), g(m), eq_proxy(m);
            symbol f("f"), g("g");
            unsigned log_terms = 1, nt = num_terms;
            while (nt > 0) { log_terms++; nt /= 2; }
            
            bv = m_bv.mk_bv_sort(log_terms);
            for (unsigned i = 0; i < num_terms; ++i) {
                expr* t = terms[i];
                sort* s = m.get_sort(t);
                eq = m.mk_eq(m.mk_app(m.mk_func_decl(f, 1, &s, bv), t), m_bv.mk_numeral(rational(i), bv));
                eq_proxy = m.mk_fresh_const("f", m.mk_bool_sort());
                m_solver.assert_expr(m.mk_iff(eq, eq_proxy));
                g = m.mk_app(m.mk_func_decl(g, 1, &s, bv), t)
                m_fs.insert(t, eq_proxy);
                m_gs.insert(t, g);
            }
        }

        // 
        // For each t in src, check if t can be different from all s in dst.
        // - if it can, then add t to dst.
        // - if it cannot, then record equivalence class.
        // 
        void merge_classes(expr_ref_vector& src, expr_ref_vector& dst, equivs& eqs) {
            
        }
    };

    lbool implied_equalities_core_based(
        solver& solver,
        unsigned num_terms, expr* const* terms, 
        unsigned* class_ids,            
        unsigned num_assumptions, expr * const * assumptions) {        
        implied_equalities_finder ief(solver);

        solver.push();
        for (unsigned i = 0; i < num_assumptions; ++i) {
            solver.assert_expr(assumptions[i]);
        }
        lbool is_sat = ief(num_terms, terms, class_ids);
        solver.pop(1);

        return is_sat;
    }

        /**
           \brief Extract implied equalities for a collection of terms in the current context.
           
           The routine uses a partition refinement approach.
           It assumes that all terms have the same sort.

           Initially, create the equalities E_1: t0 = t1, E_2: t1 = t2, ..., E_n: t_{n-1} = t_n

           Check if ! (E_1 & E_2 & ... & E_n) is satisfiable.

           if it is unsat, then all terms are equal.
           Otherwise, partition the terms by the equalities that are true in the current model,
           iterate.
           

           This version does not attempt to be economical on how many equalities are introduced and the 
           size of the resulting clauses. The more advanced version of this approach re-uses
           equalities from a previous iteration and also represents a binary tree of propositional variables
           that cover multiple equalities. Eg.,

                 E_12 => E_1 & E_2,   E_34 => E_3 & E_4, ...
           
           
        */

        void get_implied_equalities_eq_based(term_ids& terms) {
            expr_ref_vector eqs(m);
            if (terms.size() == 1) {
                return;
            }
            m_solver.push();
            for (unsigned i = 0; i + 1 < terms.size(); ++i) {
                expr* eq = m.mk_eq(terms[i].term, terms[i+1].term);
                expr* eq_lit = m.mk_fresh_const("E", m.mk_bool_sort());
                eqs.push_back(eq_lit);
                m_solver.assert_expr(m.mk_implies(eq_lit, eq));
            }
            m_solver.assert_expr(m.mk_not(m.mk_and(eqs.size(), eqs.c_ptr())));
            lbool is_sat = m_solver.check_sat(0,0);
            switch(is_sat) {
            case l_false:
                for (unsigned i = 0; i + 1 < terms.size(); ++i) {
                    m_uf.merge(terms[i].id, terms[i+1].id);
                }
                break;
            default: {
                term_ids tems2;
                for (unsigned i = 0; i + 1 < terms.size(); ++i) {
                    expr_ref vl(m);
                    model->eval(terms[i].term, vl);
                    if (m.is_false(vl)) {
                        
                    }
                }
                break;
            }
            }
            m_solver.pop(1);
        }

    
#endif
   

 


