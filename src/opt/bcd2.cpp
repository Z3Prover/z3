/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    bcd2.cpp

Abstract:

    bcd2 based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "bcd2.h"
#include "pb_decl_plugin.h"
#include "uint_set.h"
#include "ast_pp.h"


namespace opt {
    // ------------------------------------------------------
    // Morgado, Heras, Marques-Silva 2013
    // (initial version without model-based optimizations)
    //
    class bcd2 : public maxsmt_solver_base {
        struct wcore {
            expr*           m_r;
            unsigned_vector m_R;
            rational        m_lower;
            rational        m_mid;
            rational        m_upper;
        };
        typedef obj_hashtable<expr> expr_set;

        pb_util             pb;
        expr_ref_vector     m_soft_aux;
        obj_map<expr, unsigned> m_relax2index; // expr |-> index
        obj_map<expr, unsigned> m_soft2index;  // expr |-> index
        expr_ref_vector     m_trail;
        expr_ref_vector     m_soft_constraints;
        expr_set            m_asm_set;
        vector<wcore>       m_cores;
        vector<rational>    m_sigmas;
        rational            m_den;    // least common multiplier of original denominators 
        bool                m_enable_lazy;   // enable adding soft constraints lazily (called 'mgbcd2')
        unsigned_vector     m_lazy_soft;     // soft constraints to add lazily.

        void set2asms(expr_set const& set, expr_ref_vector & es) const {
            es.reset();
            expr_set::iterator it = set.begin(), end = set.end();
            for (; it != end; ++it) {
                es.push_back(m.mk_not(*it));
            }
        }
        void bcd2_init_soft(weights_t& weights, expr_ref_vector const& soft) {

            // normalize weights to be integral:
            m_den = rational::one();
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                m_den = lcm(m_den, denominator(m_weights[i]));
            }
            if (!m_den.is_one()) {
                for (unsigned i = 0; i < m_weights.size(); ++i) {
                    m_weights[i] = m_den*m_weights[i];
                    SASSERT(m_weights[i].is_int());
                }                
            }
        }
        void init_bcd() {
            m_trail.reset();
            m_asm_set.reset();
            m_cores.reset();
            m_sigmas.reset();
            m_lazy_soft.reset();
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                m_sigmas.push_back(m_weights[i]);
                m_soft_aux.push_back(mk_fresh());
                if (m_enable_lazy) {
                    m_lazy_soft.push_back(i);
                }
                else {
                    enable_soft_constraint(i);
                }
            }
            m_upper += rational(1);                 
        }

        void process_sat() {
            svector<bool> assignment;
            update_assignment(assignment);
            if (check_lazy_soft(assignment)) {
                update_sigmas();
            }
        }

    public:
        bcd2(maxsat_context& c,
             weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft),
            pb(m),
            m_soft_aux(m),
            m_trail(m),
            m_soft_constraints(m),
            m_enable_lazy(true) {
            bcd2_init_soft(ws, soft);
        }

        virtual ~bcd2() {}

        virtual lbool operator()() {
            expr_ref fml(m), r(m);
            lbool is_sat = l_undef;
            expr_ref_vector asms(m);
            init();
            init_bcd();
            if (m.canceled()) {
                normalize_bounds();
                return l_undef;
            }
            process_sat();
            while (m_lower < m_upper) {
                trace_bounds("bcd2");
                assert_soft();
                solver::scoped_push _scope2(s());
                TRACE("opt", display(tout););
                assert_cores();
                set2asms(m_asm_set, asms);                
                if (m.canceled()) {
                    normalize_bounds();
                    return l_undef;
                }
                is_sat = s().check_sat(asms.size(), asms.c_ptr());
                switch(is_sat) {
                case l_undef: 
                    normalize_bounds();
                    return l_undef;
                case l_true: 
                    process_sat();
                    break;                
                case l_false: {
                    ptr_vector<expr> unsat_core;
                    uint_set subC, soft;
                    s().get_unsat_core(unsat_core);
                    core2indices(unsat_core, subC, soft);
                    SASSERT(unsat_core.size() == subC.num_elems() + soft.num_elems());
                    if (soft.num_elems() == 0 && subC.num_elems() == 1) {
                        unsigned s = *subC.begin();
                        wcore& c_s = m_cores[s];
                        c_s.m_lower = refine(c_s.m_R, c_s.m_mid);
                        c_s.m_mid = div(c_s.m_lower + c_s.m_upper, rational(2));
                    }
                    else {
                        wcore c_s;
                        rational delta = min_of_delta(subC);
                        rational lower = sum_of_lower(subC);
                        union_Rs(subC, c_s.m_R);
                        r = mk_fresh();
                        relax(subC, soft, c_s.m_R, delta);
                        c_s.m_lower = refine(c_s.m_R, lower + delta - rational(1));
                        c_s.m_upper = rational::one();
                        c_s.m_upper += sum_of_sigmas(c_s.m_R);
                        c_s.m_mid = div(c_s.m_lower + c_s.m_upper, rational(2));
                        c_s.m_r = r;
                        m_asm_set.insert(r);
                        subtract(m_cores, subC);
                        m_relax2index.insert(r, m_cores.size());
                        m_cores.push_back(c_s);
                    }
                    break;
                }
                }
                m_lower = compute_lower();
            }
            normalize_bounds();
            return l_true;            
        }


    private:

        void enable_soft_constraint(unsigned i) {
            expr_ref fml(m);
            expr* r = m_soft_aux[i].get();
            m_soft2index.insert(r, i);
            fml = m.mk_or(r, m_soft[i]); 
            m_soft_constraints.push_back(fml);
            m_asm_set.insert(r);
            SASSERT(m_weights[i].is_int());     
        }

        void assert_soft() {
            for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
                s().assert_expr(m_soft_constraints[i].get()); 
            }
            m_soft_constraints.reset();
        }

        bool check_lazy_soft(svector<bool> const& assignment) {
            bool all_satisfied = true;
            for (unsigned i = 0; i < m_lazy_soft.size(); ++i) {
                unsigned j = m_lazy_soft[i];
                if (!assignment[j]) {
                    enable_soft_constraint(j);
                    m_lazy_soft[i] = m_lazy_soft.back();
                    m_lazy_soft.pop_back();
                    --i;
                    all_satisfied = false;
                }
            }
            return all_satisfied;
        }

        void normalize_bounds() {
            m_lower /= m_den;
            m_upper /= m_den;
        }

        expr* mk_fresh() {
            expr* r = mk_fresh_bool("r");
            m_trail.push_back(r);
            return r;
        }

        void update_assignment(svector<bool>& new_assignment) {
            expr_ref val(m);
            rational new_upper(0);
            model_ref model;            
            new_assignment.reset();
            s().get_model(model);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                VERIFY(model->eval(m_soft[i], val));    
                new_assignment.push_back(m.is_true(val));                            
                if (!new_assignment[i]) {
                    new_upper += m_weights[i];
                }
            }
            if (new_upper < m_upper) {
                m_upper = new_upper;
                m_model = model;
                m_assignment.reset();
                m_assignment.append(new_assignment);
            }
        }

        void update_sigmas() {
            for (unsigned i = 0; i < m_cores.size(); ++i) {
                wcore& c_i = m_cores[i];
                unsigned_vector const& R = c_i.m_R;
                c_i.m_upper.reset();
                for (unsigned j = 0; j < R.size(); ++j) {
                    unsigned r_j = R[j];
                    if (!m_assignment[r_j]) {
                        c_i.m_upper += m_weights[r_j];
                        m_sigmas[r_j] = m_weights[r_j];
                    }
                    else {
                        m_sigmas[r_j].reset();
                    }
                }
                c_i.m_mid = div(c_i.m_lower + c_i.m_upper, rational(2));
            }
        }

        /**
         * Minimum of two (positive) numbers. Zero is treated as +infinity.
         */
        rational min_z(rational const& a, rational const& b) {
            if (a.is_zero()) return b;
            if (b.is_zero()) return a;
            if (a < b) return a;
            return b;
        }

        rational min_of_delta(uint_set const& subC) {
            rational delta(0);
            for (uint_set::iterator it = subC.begin(); it != subC.end(); ++it) {
                unsigned j = *it;
                wcore const& core = m_cores[j];
                rational new_delta = rational(1) + core.m_upper - core.m_mid; 
                SASSERT(new_delta.is_pos());
                delta = min_z(delta, new_delta);                
            }
            return delta;
        }

        rational sum_of_lower(uint_set const& subC) {
            rational lower(0);
            for (uint_set::iterator it = subC.begin(); it != subC.end(); ++it) {
                lower += m_cores[*it].m_lower;
            }
            return lower;
        }

        rational sum_of_sigmas(unsigned_vector const& R) {
            rational sum(0);
            for (unsigned i = 0; i < R.size(); ++i) {
                sum += m_sigmas[R[i]];
            }
            return sum;
        }
        void union_Rs(uint_set const& subC, unsigned_vector& R) {
            for (uint_set::iterator it = subC.begin(); it != subC.end(); ++it) {
                R.append(m_cores[*it].m_R);
            }
        }
        rational compute_lower() {
            rational result(0);
            for (unsigned i = 0; i < m_cores.size(); ++i) {
                result += m_cores[i].m_lower;
            }
            return result;
        }
        void subtract(vector<wcore>& cores, uint_set const& subC) {
            unsigned j = 0;                        
            for (unsigned i = 0; i < cores.size(); ++i) {
                if (subC.contains(i)) {
                    m_asm_set.remove(cores[i].m_r);
                }
                else {
                    if (j != i) {
                        cores[j] = cores[i];
                    }
                    ++j;
                }
            }
            cores.resize(j);
            for (unsigned i = 0; i < cores.size(); ++i) {
                m_relax2index.insert(cores[i].m_r, i);
            }
        }
        void core2indices(ptr_vector<expr> const& core, uint_set& subC, uint_set& soft) {
            for (unsigned i = 0; i < core.size(); ++i) {
                unsigned j;
                expr* a;
                VERIFY(m.is_not(core[i], a));
                if (m_relax2index.find(a, j)) {
                    subC.insert(j);
                }
                else {
                    VERIFY(m_soft2index.find(a, j));
                    soft.insert(j);
                }
            }
        }            
        rational refine(unsigned_vector const& idx, rational v) {
            return v + rational(1);
        }
        void relax(uint_set& subC, uint_set& soft, unsigned_vector& R, rational& delta) {
            for (uint_set::iterator it = soft.begin(); it != soft.end(); ++it) {                
                R.push_back(*it);
                delta = min_z(delta, m_weights[*it]);
                m_asm_set.remove(m_soft_aux[*it].get());
            }
        }
        void assert_cores() {
            for (unsigned i = 0; i < m_cores.size(); ++i) {
                assert_core(m_cores[i]);
            }
        }
        void assert_core(wcore const& core) {
            expr_ref fml(m);
            vector<rational> ws;
            ptr_vector<expr> rs;
            rational w(0);
            for (unsigned j = 0; j < core.m_R.size(); ++j) {
                unsigned idx = core.m_R[j];
                ws.push_back(m_weights[idx]);
                w += ws.back();
                rs.push_back(m_soft_aux[idx].get());
            }
            w.neg();
            w += core.m_mid;
            ws.push_back(w);
            rs.push_back(core.m_r);
            fml = pb.mk_le(ws.size(), ws.c_ptr(), rs.c_ptr(), core.m_mid);
            s().assert_expr(fml);
        }
        void display(std::ostream& out) {
            out << "[" << m_lower << ":" << m_upper << "]\n";
            s().display(out);
            out << "\n";
            for (unsigned i = 0; i < m_cores.size(); ++i) {
                wcore const& c = m_cores[i];
                out << mk_pp(c.m_r, m) << ": ";
                for (unsigned j = 0; j < c.m_R.size(); ++j) {
                    out << c.m_R[j] << " (" << m_sigmas[c.m_R[j]] << ") ";
                }
                out << "[" << c.m_lower << ":" << c.m_mid << ":" << c.m_upper << "]\n";
            }
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                out << mk_pp(m_soft[i], m) << " " << m_weights[i] << "\n";
            }
        }
    };

    maxsmt_solver_base* mk_bcd2(
        maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(bcd2, c, ws, soft);
    }

}
