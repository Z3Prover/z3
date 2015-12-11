/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxhs.cpp

Abstract:

    maxhs based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "optsmt.h"
#include "hitting_sets.h"
#include "stopwatch.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "uint_set.h"
#include "maxhs.h"
#include "opt_context.h"

namespace opt {

    class scoped_stopwatch {
        double& m_time;
        stopwatch m_watch;
    public:
        scoped_stopwatch(double& time): m_time(time) {
            m_watch.start();
        }
        ~scoped_stopwatch() {
            m_watch.stop();
            m_time += m_watch.get_seconds();
        }
    };


    // ----------------------------------
    // MaxSatHS+MSS
    // variant of MaxSAT-HS (Algorithm 9)
    // that also refines upper bound during progressive calls 
    // to the underlying optimization solver for the soft constraints.
    //

    class maxhs : public maxsmt_solver_base {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_iterations;
            unsigned m_num_core_reductions_success;
            unsigned m_num_core_reductions_failure;
            unsigned m_num_model_expansions_success;
            unsigned m_num_model_expansions_failure;
            double   m_core_reduction_time;
            double   m_model_expansion_time;
            double   m_aux_sat_time;       
            double   m_disjoint_cores_time;
        };

        hitting_sets            m_hs;
        expr_ref_vector         m_aux;        // auxiliary (indicator) variables.
        obj_map<expr, unsigned> m_aux2index;  // expr |-> index
        unsigned_vector         m_core_activity; // number of times soft constraint is used in a core.
        svector<bool>           m_seed;       // clause selected in current model.
        svector<bool>           m_aux_active; // active soft clauses.
        ptr_vector<expr>        m_asms;       // assumptions (over aux)
        stats                   m_stats;
        bool                    m_at_lower_bound;


    public:
        maxhs(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft):
            maxsmt_solver_base(c, ws, soft), 
            m_hs(m.limit()), 
            m_aux(m), 
            m_at_lower_bound(false) {
        }
        virtual ~maxhs() {}

        virtual void collect_statistics(statistics& st) const {
            maxsmt_solver_base::collect_statistics(st);
            m_hs.collect_statistics(st);
            st.update("maxhs-num-iterations", m_stats.m_num_iterations);
            st.update("maxhs-num-core-reductions-n", m_stats.m_num_core_reductions_failure);
            st.update("maxhs-num-core-reductions-y", m_stats.m_num_core_reductions_success);
            st.update("maxhs-num-model-expansions-n", m_stats.m_num_model_expansions_failure);
            st.update("maxhs-num-model-expansions-y", m_stats.m_num_model_expansions_success);
            st.update("maxhs-core-reduction-time", m_stats.m_core_reduction_time);
            st.update("maxhs-model-expansion-time", m_stats.m_model_expansion_time);
            st.update("maxhs-aux-sat-time", m_stats.m_aux_sat_time);
            st.update("maxhs-disj-core-time", m_stats.m_disjoint_cores_time);
        }

        lbool operator()() {
            ptr_vector<expr> hs;
            init();
            init_local();
            if (!disjoint_cores(hs)) {
                return l_undef;
            }
            seed2assumptions();
            while (m_lower < m_upper) {
                ++m_stats.m_num_iterations;
                trace_bounds("maxhs");
                TRACE("opt", tout << "(maxhs [" << m_lower << ":" << m_upper << "])\n";);
                if (m.canceled()) {
                    return l_undef;
                }
                
                lbool core_found = generate_cores(hs);
                switch(core_found) {
                case l_undef: 
                    return l_undef;
                case l_true: {
                    lbool is_sat = next_seed();
                    switch(is_sat) {
                    case l_true:
                        seed2hs(false, hs);
                        break;
                    case l_false:                        
                        TRACE("opt", tout << "no more seeds\n";);
                        IF_VERBOSE(1, verbose_stream() << "(opt.maxhs.no-more-seeds)\n";);
                        m_lower = m_upper;
                        return l_true;
                    case l_undef:
                        return l_undef;
                     }
                     break;
                }
                case l_false:
                    IF_VERBOSE(1, verbose_stream() << "(opt.maxhs.no-more-cores)\n";);
                    TRACE("opt", tout << "no more cores\n";);
                    m_lower = m_upper;
                    return l_true;
                }
            }
            return l_true;
        }

    private:

        unsigned num_soft() const { return m_soft.size(); }

        void init_local() {
            unsigned sz = num_soft();
            app_ref  fml(m), obj(m);
            expr_ref_vector sum(m);
            m_asms.reset();
            m_seed.reset();           
            m_aux.reset();
            m_aux_active.reset();            
            m_aux2index.reset();
            m_core_activity.reset();
            for (unsigned i = 0; i < sz; ++i) {
                bool tt = is_true(m_model, m_soft[i]);
                m_seed.push_back(tt);
                m_aux. push_back(mk_fresh(m.mk_bool_sort()));
                m_aux_active.push_back(false);
                m_core_activity.push_back(0);
                m_aux2index.insert(m_aux.back(), i);
                if (tt) {
                    m_asms.push_back(m_aux.back());
                    ensure_active(i);
                }
            }

            for (unsigned i = 0; i < m_weights.size(); ++i) {
                m_hs.add_weight(m_weights[i]);
            }
            TRACE("opt", print_seed(tout););
        }


        void hs2seed(ptr_vector<expr> const& hs) {
            for (unsigned i = 0; i < num_soft(); ++i) {
                m_seed[i] = true;
            }
            for (unsigned i = 0; i < hs.size(); ++i) {
                m_seed[m_aux2index.find(hs[i])] = false;
            }
            TRACE("opt", 
                  print_asms(tout << "hitting set: ", hs);
                  print_seed(tout););
        }

        void seed2hs(bool pos, ptr_vector<expr>& hs) {
            hs.reset();
            for (unsigned i = 0; i < num_soft(); ++i) {
                if (pos == m_seed[i]) {
                    hs.push_back(m_aux[i].get());
                }
            }
            TRACE("opt", 
                  print_asms(tout << "hitting set: ", hs);
                  print_seed(tout););
            
        }

        void seed2assumptions() {
            seed2hs(true, m_asms);
        }


        //
        // Find disjoint cores for soft constraints.
        //
        bool disjoint_cores(ptr_vector<expr>& hs) {
            scoped_stopwatch _sw(m_stats.m_disjoint_cores_time);
            m_asms.reset();
            svector<bool> active(num_soft(), true);
            rational lower(0);
            update_assumptions(active, lower, hs);
            SASSERT(lower.is_zero());
            while (true) {
                lbool is_sat = s().check_sat(m_asms.size(), m_asms.c_ptr());
                switch (is_sat) {
                case l_true:
                    if (lower > m_lower) {
                        m_lower = lower;                        
                    }
                    return true;
                case l_false:
                    if (!shrink()) return false;
                    block_up();
                    update_assumptions(active, lower, hs);
                    break;
                case l_undef:
                    return false;
                }                
            }
        }

        void update_assumptions(svector<bool>& active, rational& lower, ptr_vector<expr>& hs) {
            rational arg_min(0);
            expr* e = 0;
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                unsigned index = m_aux2index.find(m_asms[i]); 
                active[index] = false;
                if (arg_min.is_zero() || arg_min > m_weights[index]) {
                    arg_min = m_weights[index];
                    e = m_asms[i];
                }
            }
            if (e) {
                hs.push_back(e);
                lower += arg_min;
            }
            m_asms.reset();
            for (unsigned i = 0; i < num_soft(); ++i) {
                if (active[i]) {
                    m_asms.push_back(m_aux[i].get());
                    ensure_active(i);
                }
            }
        }

        //
        // Auxiliary Algorithm 10 for producing cores.
        // 
        lbool generate_cores(ptr_vector<expr>& hs) {
            bool core = !m_at_lower_bound;
            while (true) {
                hs2seed(hs);
                lbool is_sat = check_subset();
                switch(is_sat) {
                case l_undef: 
                    return l_undef;
                case l_true:
                    if (!grow()) return l_undef;
                    block_down();
                    return core?l_true:l_false;
                case l_false:
                    core = true;
                    if (!shrink()) return l_undef;
                    block_up();
                    find_non_optimal_hitting_set(hs);
                    break;
                }
            }
        }

        struct lt_activity {
            maxhs& hs;
            lt_activity(maxhs& hs):hs(hs) {}
            bool operator()(expr* a, expr* b) const {
                unsigned w1 = hs.m_core_activity[hs.m_aux2index.find(a)];
                unsigned w2 = hs.m_core_activity[hs.m_aux2index.find(b)];
                return w1 < w2;
            }
        };

        //
        // produce the non-optimal hitting set by using the 10% heuristic.
        // of most active cores constraints.
        // m_asms contains the current core.
        //
        void find_non_optimal_hitting_set(ptr_vector<expr>& hs) {
            std::sort(m_asms.begin(), m_asms.end(), lt_activity(*this));
            for (unsigned i = m_asms.size(); i > 9*m_asms.size()/10;) { 
                --i;
                hs.push_back(m_asms[i]);
            }
        }

        //
        // retrieve the next seed that satisfies state of hs.
        // state of hs must be satisfiable before optimization is called.
        // 
        lbool next_seed() {
            scoped_stopwatch _sw(m_stats.m_aux_sat_time);
            TRACE("opt", tout << "\n";);

            // min c_i*(not x_i) for x_i are soft clauses.
            // max c_i*x_i for x_i are soft clauses
            
            m_at_lower_bound = false;
            
            lbool is_sat = m_hs.compute_upper();

            if (is_sat == l_true) {
                is_sat = m_hs.compute_lower();
            }
            if (is_sat == l_true) {
                m_at_lower_bound = m_hs.get_upper() == m_hs.get_lower();
                if (m_hs.get_lower() > m_lower) {
                    m_lower = m_hs.get_lower();
                }
                for (unsigned i = 0; i < num_soft(); ++i) {
                    m_seed[i] = is_active(i) && !m_hs.get_value(i);
                }
                TRACE("opt", print_seed(tout););
            }
            return is_sat;
        }

        //
        // check assignment returned by HS with the original
        // hard constraints. 
        //
        lbool check_subset() {
            TRACE("opt", tout << "\n";);
            m_asms.reset();
            for (unsigned i = 0; i < num_soft(); ++i) {
                if (m_seed[i]) {
                    m_asms.push_back(m_aux[i].get());
                    ensure_active(i);
                }
            }
            return s().check_sat(m_asms.size(), m_asms.c_ptr());
        }

        //
        // extend the current assignment to one that 
        // satisfies as many soft constraints as possible.
        // update the upper bound based on this assignment
        // 
        bool grow() {
            scoped_stopwatch _sw(m_stats.m_model_expansion_time);
            model_ref mdl;
            s().get_model(mdl);
            for (unsigned i = 0; i < num_soft(); ++i) {
                ensure_active(i);    
                m_seed[i] = false;
            }
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                m_seed[m_aux2index.find(m_asms[i])] = true; 
            }

            for (unsigned i = 0; i < num_soft(); ++i) {
                if (m_seed[i]) {
                    // already an assumption
                }
                else if (is_true(mdl, m_soft[i])) {
                    m_seed[i] = true;                    
                    m_asms.push_back(m_aux[i].get());
                }
                else {
                    m_asms.push_back(m_aux[i].get());
                    lbool is_sat = s().check_sat(m_asms.size(), m_asms.c_ptr());
                    switch(is_sat) {
                    case l_undef: 
                        return false;
                    case l_false: 
                        ++m_stats.m_num_model_expansions_failure;
                        m_asms.pop_back(); 
                        break;
                    case l_true: 
                        ++m_stats.m_num_model_expansions_success;
                        s().get_model(mdl);
                        m_seed[i] = true; 
                        break;                     
                    }
                }
            }
            rational upper(0);
            for (unsigned i = 0; i < num_soft(); ++i) {
                if (!m_seed[i]) {
                    upper += m_weights[i];
                }
            }       
            if (upper < m_upper) {
                m_upper = upper;
                m_hs.set_upper(upper);
                m_model = mdl;
                m_assignment.reset();
                m_assignment.append(m_seed);
                TRACE("opt", 
                      tout << "new upper: " << m_upper << "\n";
                      model_smt2_pp(tout, m, *(mdl.get()), 0););
            }
            DEBUG_CODE(                
                for (unsigned i = 0; i < num_soft(); ++i) {
                    SASSERT(is_true(mdl, m_soft[i]) == m_seed[i]);
                });
            
            return true;
        }

        //
        // remove soft constraints from the current core.
        // 
        bool shrink() {
            scoped_stopwatch _sw(m_stats.m_core_reduction_time);
            m_asms.reset();
            s().get_unsat_core(m_asms);
            TRACE("opt", print_asms(tout, m_asms););
            obj_map<expr, unsigned> asm2index;
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                asm2index.insert(m_asms[i], i);
            }
            obj_map<expr, unsigned>::iterator it = asm2index.begin(), end = asm2index.end();            
            for (; it != end; ++it) {
                unsigned i = it->m_value;
                if (i < m_asms.size()) {
                    expr* tmp = m_asms[i];
                    expr* back = m_asms.back();
                    m_asms[i] = back;
                    m_asms.pop_back();
                    lbool is_sat = s().check_sat(m_asms.size(), m_asms.c_ptr());
                    TRACE("opt", tout << "checking: " << mk_pp(tmp, m) << ": " << is_sat << "\n";);
                    switch(is_sat) {
                    case l_true:
                        ++m_stats.m_num_core_reductions_failure;
                        // put back literal into core
                        m_asms.push_back(back);
                        m_asms[i] = tmp;
                        break;
                    case l_false: 
                        // update the core 
                        m_asms.reset();
                        ++m_stats.m_num_core_reductions_success;
                        s().get_unsat_core(m_asms);                        
                        TRACE("opt", print_asms(tout, m_asms););
                        update_index(asm2index);
                        break;
                    case l_undef: 
                        return false;
                    }
                }
            }
            return true;
        }

        void print_asms(std::ostream& out, ptr_vector<expr> const& asms) {
            for (unsigned j = 0; j < asms.size(); ++j) {
                out << mk_pp(asms[j], m) << " ";
            }
            out << "\n";
        }

        void print_seed(std::ostream& out) {
            out << "seed: ";
            for (unsigned i = 0; i < num_soft(); ++i) {
                out << (m_seed[i]?"1":"0");
            }
            out << "\n";
        }

        //
        // must include some literal not from asms.
        // (furthermore, update upper bound constraint in HS)
        //
        void block_down() {
            uint_set indices;
            unsigned_vector c_indices;
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                indices.insert(m_aux2index.find(m_asms[i]));
            }
            for (unsigned i = 0; i < num_soft(); ++i) {
                if (!indices.contains(i)) {
                    c_indices.push_back(i);
                }
            }
            m_hs.add_exists_false(c_indices.size(), c_indices.c_ptr());
        }

        // should exclude some literal from core.
        void block_up() {
            unsigned_vector indices;
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                unsigned index = m_aux2index.find(m_asms[i]);
                m_core_activity[index]++;
                indices.push_back(index);
            }
            m_hs.add_exists_true(indices.size(), indices.c_ptr());
        }

        void update_index(obj_map<expr, unsigned>& asm2index) {
            obj_map<expr, unsigned>::iterator it = asm2index.begin(), end = asm2index.end();            
            for (; it != end; ++it) {
                it->m_value = UINT_MAX;
            }
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                asm2index.find(m_asms[i]) = i;
            }
        }        

        app_ref mk_fresh(sort* s) {
            app_ref r(m);
            r = m.mk_fresh_const("r", s);
            m_c.fm().insert(r->get_decl());                
            return r;
        }

        bool is_true(model_ref& mdl, expr* e) {
            expr_ref val(m);
            VERIFY(mdl->eval(e, val));
            return m.is_true(val);
        }

        bool is_active(unsigned i) const {
            return m_aux_active[i];
        }

        void ensure_active(unsigned i) {
            if (!is_active(i)) {
                expr_ref fml(m);
                fml = m.mk_implies(m_aux[i].get(), m_soft[i]);
                s().assert_expr(fml);
                m_aux_active[i] = true;
            }
        }
        
    };

    maxsmt_solver_base* mk_maxhs(
        maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(maxhs, c, ws, soft);
    }

}
