/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    hitting_sets.h

Abstract:
   
    Hitting set approximations.

Author:

    Nikolaj Bjorner (nbjorner) 2014-06-06

Notes:

--*/
#include "vector.h"
#include "util.h"
#include "hitting_sets.h"
#include "simplex.h"
#include "sparse_matrix_def.h"
#include "simplex_def.h"

typedef simplex::simplex<simplex::mpz_ext> Simplex;
typedef simplex::sparse_matrix<simplex::mpz_ext> sparse_matrix;


namespace opt {

    struct hitting_sets::imp {
        typedef unsigned_vector set;
        volatile bool           m_cancel;
        rational                m_lower;
        rational                m_upper;
        vector<rational>        m_weights;
        rational                m_max_weight;
        rational                m_denominator;
        vector<set>             m_S;
        svector<lbool>          m_value;
        unsigned_vector         m_value_trail;
        unsigned_vector         m_value_lim;
        vector<unsigned_vector> m_use_list;        
        unsynch_mpz_manager     m;
        Simplex                 m_simplex;
        unsigned                m_weights_var;

        imp():m_cancel(false) {}
        ~imp() {}

        void add_weight(rational const& w) {
            SASSERT(w.is_pos());
            unsigned var = m_weights.size();
            m_simplex.ensure_var(var);
            m_simplex.set_lower(var, mpq_inf(mpq(0),mpq(0)));
            m_simplex.set_upper(var, mpq_inf(mpq(1),mpq(0)));
            m_weights.push_back(w);
            m_value.push_back(l_undef);
            m_use_list.push_back(unsigned_vector());
            m_max_weight += w;
        }

        void add_set(unsigned sz, unsigned const* S) {
            if (sz == 0) {
                return;
            }
            for (unsigned i = 0; i < sz; ++i) {
                m_use_list[S[i]].push_back(m_S.size());
            }
            init_weights();
            m_S.push_back(unsigned_vector(sz, S));        
            add_simplex_row(sz, S);            
        }

        bool compute_lower() {
            m_lower.reset();
            return L1() && L2() && L3();            
        }

        bool compute_upper() {            
            m_upper = m_max_weight;
            return U1();
        }

        rational get_lower() {
            return m_lower/m_denominator;
        }

        rational get_upper() {
            return m_upper/m_denominator;
        }

        void set_cancel(bool f) {
            m_cancel = f;
            m_simplex.set_cancel(f);
        }

        void collect_statistics(::statistics& st) const {
            m_simplex.collect_statistics(st);
        }

        void reset() {
            m_lower.reset();
            m_upper = m_max_weight;
        }

        void init_weights() {
            if (m_weights_var != 0) {
                return;
            }
            m_weights_var = m_weights.size();
            unsigned_vector vars;
            scoped_mpz_vector coeffs(m);

            // normalize weights to integral.
            rational d(1);
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                d = lcm(d, denominator(m_weights[i]));
            }
            m_denominator = d;
            if (!d.is_one()) {
                for (unsigned i = 0; i < m_weights.size(); ++i) {
                    m_weights[i] *= d;
                }
            }
            // set up Simplex objective function.
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                vars.push_back(i);
                coeffs.push_back(m_weights[i].to_mpq().numerator());
            }
            m_simplex.ensure_var(m_weights_var);
            vars.push_back(m_weights_var);
            coeffs.push_back(mpz(-1));
            m_simplex.add_row(m_weights_var, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
        }

        struct scoped_select {
            imp& s;
            unsigned sz;
            scoped_select(imp& s):s(s), sz(s.m_value_trail.size()) {
            }
            ~scoped_select() {
                s.undo_select(sz);
            }
        };

        struct value_lt {
            vector<rational> const& weights;
            unsigned_vector const& scores;
            value_lt(vector<rational> const& weights, unsigned_vector const& scores):
                weights(weights), scores(scores) {}
            bool operator()(int v1, int v2) const {
                //     - score1 / w1 < - score2 / w2
                // <=> 
                //     score1 / w1 > score2 / w2
                // <=>
                //     score1*w2 > score2*w1
                unsigned score1 = scores[v1];
                unsigned score2 = scores[v2];
                rational w1 = weights[v1];
                rational w2 = weights[v2];
                return rational(score1)*w2 > rational(score2)*w1;
            }
        };


        // compute upper bound for hitting set.
        bool U1() {        
            rational w(0);
            scoped_select _sc(*this);
            
            // score each variable by the number of
            // unassigned sets they occur in.
            unsigned_vector scores;
            init_scores(scores);
            
            //
            // Sort indices.
            // The least literals are those where -score/w is minimized.
            //
            unsigned_vector indices;
            for (unsigned i = 0; i < m_value.size(); ++i) {
                indices.push_back(i);
            }        
            value_lt lt(m_weights, scores);
            while (!m_cancel) {
                std::sort(indices.begin(), indices.end(), lt);
                unsigned idx = indices[0];
                if (scores[idx] == 0) {
                    break;
                }
                update_scores(scores, idx);
                select(idx);
                w += m_weights[idx];
            }
            if (w < m_upper) {
                m_upper = w;
            }
            return !m_cancel;
        }

        void init_scores(unsigned_vector & scores) {
            scores.reset();
            for (unsigned i = 0; i < m_value.size(); ++i) {
                scores.push_back(0);
            }
            for (unsigned i = 0; i < m_S.size(); ++i) {
                set const& S = m_S[i];
                if (!has_selected(S)) {
                    for (unsigned j = 0; j < S.size(); ++j) {
                        scores[S[j]]++;
                    }
                }
            }
        }

        void update_scores(unsigned_vector& scores, unsigned v) {
            unsigned_vector const& v_uses = m_use_list[v];
            for (unsigned i = 0; i < v_uses.size(); ++i) {
                set const& S = m_S[v_uses[i]];
                if (!has_selected(S)) {
                    for (unsigned j = 0; j < S.size(); ++j) {
                        --scores[S[j]];
                    }
                }
            }
        }

        bool L1() {
            rational w(0);
            scoped_select _sc(*this);
            for (unsigned i = 0; !m_cancel && i < m_S.size(); ++i) {
                set const& S = m_S[i];
                SASSERT(!S.empty());
                if (!has_selected(S)) {
                    w += m_weights[select_min(S)];                
                    for (unsigned j = 0; j < S.size(); ++j) {
                        select(S[j]);
                    }
                }
            }
            if (m_lower < w) {
                m_lower = w;
            }
            return !m_cancel;
        }

        bool L2() {
            rational w(0);
            scoped_select _sc(*this);
            int n = 0;
            for (unsigned i = 0; i < m_S.size(); ++i) {
                if (!has_selected(m_S[i])) ++n;
            }
            unsigned_vector scores;
            init_scores(scores);
            unsigned_vector indices;
            for (unsigned i = 0; i < m_value.size(); ++i) {
                indices.push_back(i);
            }        
            value_lt lt(m_weights, scores);

            std::sort(indices.begin(), indices.end(), lt);
            for(unsigned i = 0; i < indices.size() && n > 0; ++i) {
                // deg(c) = score(c)
                // wt(c) = m_weights[c]
                unsigned idx = indices[i];
                if (scores[idx] == 0) {
                    break;
                }
                if (scores[idx] < static_cast<unsigned>(n) || m_weights[idx].is_one()) {
                    w += m_weights[idx];
                }
                else {
                    w += div((rational(n)*m_weights[idx]), rational(scores[idx]));
                }
                n -= scores[idx];
            }
            if (m_lower < w) {
                m_lower = w;
            }
            return !m_cancel;
        }

        bool L3() {        
            TRACE("simplex", m_simplex.display(tout););
            VERIFY(l_true == m_simplex.make_feasible());
            TRACE("simplex", m_simplex.display(tout););
            VERIFY(l_true == m_simplex.minimize(m_weights_var));
            mpq_inf const& val = m_simplex.get_value(m_weights_var);
            unsynch_mpq_inf_manager mg;
            unsynch_mpq_manager& mq = mg.mpq_manager();
            scoped_mpq c(mq);
            mg.ceil(val, c);
            rational w = rational(c);
            if (w > m_lower) {
                m_lower = w;
            }
            return true;
        }    

        void add_simplex_row(unsigned sz, unsigned const* S) {
            unsigned_vector vars;
            scoped_mpz_vector coeffs(m);
            for (unsigned i = 0; i < sz; ++i) {
                vars.push_back(S[i]);
                coeffs.push_back(mpz(1));
            }
            unsigned base_var = m_S.size() + m_weights.size();
            m_simplex.ensure_var(base_var);
            vars.push_back(base_var);
            coeffs.push_back(mpz(-1));
            // S - base_var = 0
            // base_var >= 1
            m_simplex.set_lower(base_var, mpq_inf(mpq(1),mpq(0)));
            m_simplex.add_row(base_var, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
        }

        void undo_select(unsigned sz) {
            for (unsigned j = sz; j < m_value_trail.size(); ++j) {
                m_value[m_value_trail[j]] = l_undef;
            }
            m_value_trail.resize(sz);
        }
        
        unsigned select_min(set const& S) {
            unsigned result = S[0];
            for (unsigned i = 1; i < S.size(); ++i) {
                if (m_weights[result] > m_weights[S[i]]) {
                    result = S[i];
                }
            }
            return result;
        }
        
        
        lbool selected(unsigned j) const { 
            return m_value[j];
        }
        
        void select(unsigned j) {
            m_value[j] = l_true;
            m_value_trail.push_back(j);
        }
        
        bool has_selected(set const& S) {
            for (unsigned i = 0; i < S.size(); ++i) {
                if (l_true == selected(S[i])) {
                    return true;
                }
            }
            return false;
        }
        
    };
    hitting_sets::hitting_sets() { m_imp = alloc(imp); }
    hitting_sets::~hitting_sets() { dealloc(m_imp); }
    void hitting_sets::add_weight(rational const& w) { m_imp->add_weight(w); }
    void hitting_sets::add_set(unsigned sz, unsigned const* elems) { m_imp->add_set(sz, elems); }
    bool hitting_sets::compute_lower() { return m_imp->compute_lower(); }
    bool hitting_sets::compute_upper() { return m_imp->compute_upper(); }
    rational hitting_sets::get_lower() { return m_imp->get_lower(); }
    rational hitting_sets::get_upper() { return m_imp->get_upper(); }
    void hitting_sets::set_cancel(bool f) { m_imp->set_cancel(f); }
    void hitting_sets::collect_statistics(::statistics& st) const { m_imp->collect_statistics(st); }
    void hitting_sets::reset() { m_imp->reset(); }


};
