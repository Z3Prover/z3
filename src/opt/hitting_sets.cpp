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
#include "sat_solver.h"

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
        vector<set>             m_T;
        svector<lbool>          m_value;
        svector<lbool>          m_value_saved;
        unsigned_vector         m_value_trail;
        unsigned_vector         m_value_lim;
        vector<unsigned_vector> m_tuse_list;        
        vector<unsigned_vector> m_fuse_list;        
        unsynch_mpz_manager     m;
        Simplex                 m_simplex;
        unsigned                m_weights_var;

        params_ref              m_params;
        sat::solver             m_solver;
        svector<sat::bool_var>  m_vars;

        imp():
            m_cancel(false), 
            m_max_weight(0), 
            m_weights_var(0),
            m_solver(m_params,0) {
            m_params.set_bool("elim_vars", false);
            m_solver.updt_params(m_params);
        }
        ~imp() {}

        void add_weight(rational const& w) {
            SASSERT(w.is_pos());
            unsigned var = m_weights.size();
            m_simplex.ensure_var(var);
            m_simplex.set_lower(var, mpq_inf(mpq(0),mpq(0)));
            m_simplex.set_upper(var, mpq_inf(mpq(1),mpq(0)));
            m_weights.push_back(w);
            m_value.push_back(l_undef);
            m_tuse_list.push_back(unsigned_vector());
            m_fuse_list.push_back(unsigned_vector());
            m_max_weight += w;
            m_vars.push_back(m_solver.mk_var());
        }

        void add_exists_false(unsigned sz, unsigned const* S) {
            SASSERT(sz > 0);
            for (unsigned i = 0; i < sz; ++i) {
                m_fuse_list[S[i]].push_back(m_T.size());
            }
            init_weights();
            m_T.push_back(unsigned_vector(sz, S));        
            add_simplex_row(false, sz, S);            
            // Add clause to SAT solver:
            svector<sat::literal> lits;
            for (unsigned i = 0; i < sz; ++i) {
                lits.push_back(sat::literal(m_vars[S[i]], true));
            }
            m_solver.mk_clause(lits.size(), lits.c_ptr());
        }

        void add_exists_true(unsigned sz, unsigned const* S) {
            SASSERT(sz > 0);
            for (unsigned i = 0; i < sz; ++i) {
                m_tuse_list[S[i]].push_back(m_S.size());
            }
            init_weights();
            m_S.push_back(unsigned_vector(sz, S));        
            add_simplex_row(true, sz, S);            
                        
            // Add clause to SAT solver
            svector<sat::literal> lits;
            for (unsigned i = 0; i < sz; ++i) {
                lits.push_back(sat::literal(m_vars[S[i]], false));
            }
            m_solver.mk_clause(lits.size(), lits.c_ptr());
        }

        lbool compute_lower() {
            m_lower.reset();
            // L3() disabled: mostly a waste of time.
            if (L1() && L2()) {
                return l_true;
            }
            else {
                return l_undef;
            }
        }

        lbool compute_upper() {            
            m_upper = m_max_weight;
            return U1();
        }

        rational get_lower() {
            return m_lower/m_denominator;
        }

        rational get_upper() {
            return m_upper/m_denominator;
        }

        void set_upper(rational const& r) {
            m_max_weight = r;
        }

        bool get_value(unsigned idx) {
            return 
                idx < m_value_saved.size() && 
                m_value_saved[idx] == l_true;
        }

        void set_cancel(bool f) {
            m_cancel = f;
            m_simplex.set_cancel(f);
            m_solver.set_cancel(f);
        }

        void collect_statistics(::statistics& st) const {
            m_simplex.collect_statistics(st);
            m_solver.collect_statistics(st);
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

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                out << i << ": "  << m_value_saved[i]<< " " << m_weights[i] << "\n";
            }
            for (unsigned i = 0; i < m_S.size(); ++i) {
                display(out << "+ ", m_S[i]);
            }
            for (unsigned i = 0; i < m_T.size(); ++i) {
                display(out << "- ", m_T[i]);
            }
        }

        void display(std::ostream& out, set const& S) const {
            for (unsigned i = 0; i < S.size(); ++i) {
                out << S[i] << " ";
            }
            out << "\n";
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

        lbool U1() {
            scoped_select _sc(*this);
            while (true) {                
                if (!compute_U1()) {
                    return l_undef;
                }
                unsigned i = 0, j = 0;
                set_undef_to_false();
                if (values_satisfy_Ts(i)) {
                    if (m_upper > m_max_weight) {
                        IF_VERBOSE(1, verbose_stream() << "(hs.bound_degradation " << m_upper << " )\n";);
                    }
                    return l_true;
                }
                
                //
                // pick some unsatisfied clause from m_T, 
                // and set the value of the most expensive 
                // literal to true.
                //

                IF_VERBOSE(1, verbose_stream() << "(hs.refining exclusion set " << i << ")\n";);
                set const& T = m_T[i];
                rational max_value(0);
                j = 0;
                for (i = 0; i < T.size(); ++i) {
                    SASSERT(m_value_saved[T[i]] == l_true);
                    if (max_value < m_weights[T[i]]) {
                        max_value = m_weights[T[i]];
                        j = T[i];
                    }
                }
                IF_VERBOSE(1, verbose_stream() << "(hs.unselect " << j << ")\n";);
                unselect(j);
                for (i = 0; i < m_S.size(); ++i) {
                    set const& S = m_S[i];
                    for (j = 0; j < S.size(); ++j) {
                        if (l_false != selected(S[j])) break;
                    }
                    if (j == S.size()) {                        
                        IF_VERBOSE(1, verbose_stream() << "(hs.fallback-to-SAT)\n";);
                        return compute_U2();
                    }
                }                
                TRACE("opt", display(tout););
            }
        }

        lbool compute_U2() {
            lbool is_sat = l_true;
            while (true) {
                is_sat = m_solver.check();
                if (is_sat == l_true) {                
                    sat::model const& model = m_solver.get_model();
                    m_value_saved.reset();
                    m_upper.reset();
                    for (unsigned i = 0; i < m_vars.size(); ++i) {
                        m_value_saved.push_back(model[m_vars[i]]);
                        if (model[m_vars[i]] == l_true) {
                            m_upper += m_weights[i];
                        }
                    }
                    IF_VERBOSE(1, verbose_stream() << "(hs.upper " << m_upper << ")\n";);
                    m_solver.pop(m_solver.scope_lvl());

                }
                break;
            }
            return is_sat;
        }

        bool block_model(sat::model const& model) {
            rational value(0);
            svector<sat::literal> lits;
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                if (value >= m_max_weight) {
                    m_solver.mk_clause(lits.size(), lits.c_ptr());
                    return true;
                }
                if (model[m_vars[i]] == l_true) {
                    value += m_weights[i];
                    lits.push_back(sat::literal(m_vars[i], true));
                }
            }
            return false;
        }

        // compute upper bound for hitting set.
        bool compute_U1() {        
            rational w(0);
            scoped_select _sc(*this);
            
            // score each variable by the number of
            // unassigned sets they occur in.
            unsigned_vector scores;
            init_scores(scores);
            
            //
            // Sort indices.
            // The least literals are those where score/w is maximized.
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
            m_upper = w;
            m_value_saved.reset();
            m_value_saved.append(m_value);
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
                        if (selected(S[j]) != l_false) {
                            scores[S[j]]++;
                        }
                    }
                }
            }
        }

        void update_scores(unsigned_vector& scores, unsigned v) {
            unsigned_vector const& v_uses = m_tuse_list[v];
            for (unsigned i = 0; i < v_uses.size(); ++i) {
                set const& S = m_S[v_uses[i]];
                if (!has_selected(S)) {
                    for (unsigned j = 0; j < S.size(); ++j) {
                        if (selected(S[j]) != l_false) {
                            --scores[S[j]];
                        }
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

        void add_simplex_row(bool is_some_true, unsigned sz, unsigned const* S) {
            unsigned_vector vars;
            scoped_mpz_vector coeffs(m);
            for (unsigned i = 0; i < sz; ++i) {
                vars.push_back(S[i]);
                coeffs.push_back(mpz(1));
            }
            unsigned base_var = m_T.size() + m_S.size() + m_weights.size();
            m_simplex.ensure_var(base_var);
            vars.push_back(base_var);
            coeffs.push_back(mpz(-1));
            // S - base_var = 0
            if (is_some_true) {
                // base_var >= 1            
                m_simplex.set_lower(base_var, mpq_inf(mpq(1),mpq(0)));
            }
            else {
                // base_var <= sz-1
                m_simplex.set_upper(base_var, mpq_inf(mpq(sz-1),mpq(0)));
            }
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

        void unselect(unsigned j) {
            m_value[j] = l_false;
            m_value_trail.push_back(j);
        }

        bool have_selected(lbool val, vector<set> const& Sets, unsigned& i) {
            for (i = 0; i < Sets.size(); ++i) {
                if (!has_selected(val, Sets[i])) return false;
            }
            return true;
        }

        void set_undef_to_false() {
            for (unsigned i = 0; i < m_value_saved.size(); ++i) {
                if (m_value_saved[i] == l_undef) {
                    m_value_saved[i] = l_false;
                }
            }
        }

        bool values_satisfy_Ts(unsigned& i) {
            unsigned j = 0;
            for (i = 0; i < m_T.size(); ++i) {
                set const& T = m_T[i];
                for (j = 0; j < T.size(); ++j) {
                    if (m_value_saved[T[j]] == l_false) {
                        break;
                    }
                }
                if (T.size() == j) {
                    break;
                }
            }
            return i == m_T.size();
        }
        
        bool has_selected(set const& S) {
            return has_selected(l_true, S);
        }

        bool has_unselected(set const& S) {
            return has_selected(l_false, S);
        }

        bool has_unset(set const& S) {
            return has_selected(l_undef, S);
        }

        bool has_selected(lbool val, set const& S) {
            for (unsigned i = 0; i < S.size(); ++i) {
                if (val == selected(S[i])) {
                    return true;
                }
            }
            return false;
        }
        
    };
    hitting_sets::hitting_sets() { m_imp = alloc(imp); }
    hitting_sets::~hitting_sets() { dealloc(m_imp); }
    void hitting_sets::add_weight(rational const& w) { m_imp->add_weight(w); }
    void hitting_sets::add_exists_true(unsigned sz, unsigned const* elems) { m_imp->add_exists_true(sz, elems); }
    void hitting_sets::add_exists_false(unsigned sz, unsigned const* elems) { m_imp->add_exists_false(sz, elems); }
    lbool hitting_sets::compute_lower() { return m_imp->compute_lower(); }
    lbool hitting_sets::compute_upper() { return m_imp->compute_upper(); }
    rational hitting_sets::get_lower() { return m_imp->get_lower(); }
    rational hitting_sets::get_upper() { return m_imp->get_upper(); }
    void hitting_sets::set_upper(rational const& r) { return m_imp->set_upper(r); }
    bool hitting_sets::get_value(unsigned idx) { return m_imp->get_value(idx); }
    void hitting_sets::set_cancel(bool f) { m_imp->set_cancel(f); }
    void hitting_sets::collect_statistics(::statistics& st) const { m_imp->collect_statistics(st); }
    void hitting_sets::reset() { m_imp->reset(); }


};
