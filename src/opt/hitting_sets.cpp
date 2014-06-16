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
        vector<set>             m_T;
        vector<set>             m_F;
        svector<lbool>          m_value;        
        svector<lbool>          m_value_saved;
        unsigned_vector         m_justification;
        vector<unsigned_vector> m_tuse_list;        
        vector<unsigned_vector> m_fuse_list;        
        vector<unsigned_vector> m_twatch;        
        vector<unsigned_vector> m_fwatch;
        unsigned_vector         m_trail;  // trail of assigned literals
        unsigned                m_qhead;  // queue head

        // simplex
        unsynch_mpz_manager     m;
        Simplex                 m_simplex;
        unsigned                m_weights_var;

        // sat solver
        params_ref              m_params;
        sat::solver             m_solver;
        svector<sat::bool_var>  m_vars;

        static unsigned const null_clause = UINT_MAX;
        static unsigned const axiom = UINT_MAX-1;

        imp():
            m_cancel(false), 
            m_max_weight(0), 
            m_denominator(1),
            m_weights_var(0),
            m_qhead(0),
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
            m_justification.push_back(null_clause);
            m_tuse_list.push_back(unsigned_vector());
            m_fuse_list.push_back(unsigned_vector());
            m_twatch.push_back(unsigned_vector());
            m_fwatch.push_back(unsigned_vector());
            m_max_weight += w;
            m_vars.push_back(m_solver.mk_var());
        }

        void add_exists_false(unsigned sz, unsigned const* S) {
            add_exists(sz, S, true);
        }

        void add_exists_true(unsigned sz, unsigned const* S) {
            add_exists(sz, S, false);
        }

        void add_exists(unsigned sz, unsigned const* S, bool sign) {
            vector<unsigned_vector>& use_list = sign?m_fuse_list:m_tuse_list;
            lbool val = sign?l_false:l_true;
            vector<set>& Sets = sign?m_F:m_T;
            vector<unsigned_vector>& watch = sign?m_fwatch:m_twatch;
            SASSERT(sz > 0);
            for (unsigned i = 0; i < sz; ++i) {
                use_list[S[i]].push_back(Sets.size());
            }
            init_weights();
            if (sz == 1) {
                assign(S[0], val, axiom);
            }
            else {
                watch[S[0]].push_back(Sets.size());
                watch[S[1]].push_back(Sets.size());
                Sets.push_back(unsigned_vector(sz, S));
            }
            add_simplex_row(!sign, sz, S);            
            // Add clause to SAT solver:
            svector<sat::literal> lits;
            for (unsigned i = 0; i < sz; ++i) {
                lits.push_back(sat::literal(m_vars[S[i]], sign));
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
            m_max_weight = r*m_denominator;
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
            for (unsigned i = 0; i < m_T.size(); ++i) {
                display(out << "+ ", m_T[i]);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                display(out << "- ", m_F[i]);
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
            scoped_select(imp& s):s(s), sz(s.m_trail.size()) {
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
                lbool is_sat = compute_U1();
                if (is_sat != l_true) {
                    return is_sat;
                }
                unsigned i = 0, j = 0;
                set_undef_to_false();
                if (values_satisfy_Fs(i)) {
                    if (m_upper > m_max_weight) {
                        IF_VERBOSE(1, verbose_stream() << "(hs.bound_degradation " << m_upper << " )\n";);
                    }
                    return l_true;
                }
                
                //
                // pick some unsatisfied clause from m_F, 
                // and set the value of the most expensive 
                // literal to true.
                //

                IF_VERBOSE(1, verbose_stream() << "(hs.refining exclusion set " << i << ")\n";);
                set const& F = m_F[i];
                rational max_value(0);
                j = 0;
                for (i = 0; i < F.size(); ++i) {
                    SASSERT(m_value_saved[F[i]] == l_true);
                    if (max_value < m_weights[F[i]]) {
                        max_value = m_weights[F[i]];
                        j = F[i];
                    }
                }
                IF_VERBOSE(1, verbose_stream() << "(hs.unselect " << j << ")\n";);
                assign(j, l_false, null_clause);
                for (i = 0; i < m_T.size(); ++i) {
                    set const& S = m_T[i];
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
        lbool compute_U1() {        
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
            while (true) {
                if (m_cancel) {
                    return l_undef;
                }
                std::sort(indices.begin(), indices.end(), lt);
                unsigned idx = indices[0];
                if (scores[idx] == 0) {
                    break;
                }
                update_scores(scores, idx);
                assign(idx, l_true, null_clause);
                w += m_weights[idx];
            }
            m_upper = w;
            m_value_saved.reset();
            m_value_saved.append(m_value);
            return l_true;
        }

        void init_scores(unsigned_vector & scores) {
            scores.reset();
            for (unsigned i = 0; i < m_value.size(); ++i) {
                scores.push_back(0);
            }
            for (unsigned i = 0; i < m_T.size(); ++i) {
                set const& S = m_T[i];
                if (!has_selected(S)) {
                    for (unsigned j = 0; j < S.size(); ++j) {
                        if (selected(S[j]) != l_false) {
                            ++scores[S[j]];
                        }
                    }
                }
            }
        }

        void update_scores(unsigned_vector& scores, unsigned v) {
            unsigned_vector const& uses = m_tuse_list[v];
            for (unsigned i = 0; i < uses.size(); ++i) {
                set const& S = m_T[uses[i]];
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
            for (unsigned i = 0; !m_cancel && i < m_T.size(); ++i) {
                set const& S = m_T[i];
                SASSERT(!S.empty());
                if (!has_selected(S)) {
                    w += m_weights[select_min(S)];                
                    for (unsigned j = 0; j < S.size(); ++j) {
                        assign(S[j], l_true, null_clause);
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
            for (unsigned i = 0; i < m_T.size(); ++i) {
                if (!has_selected(m_T[i])) ++n;
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
            unsigned base_var = m_F.size() + m_T.size() + m_weights.size();
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
            for (unsigned j = sz; j < m_trail.size(); ++j) {
                m_value[m_trail[j]] = l_undef;
            }
            m_trail.resize(sz);
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

        void assign(unsigned j, lbool val, unsigned clause_id = null_clause) {
            m_value[j] = val;
            m_justification[j] = clause_id;
            m_trail.push_back(j);
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

        bool values_satisfy_Fs(unsigned& i) {
            unsigned j = 0;
            for (i = 0; i < m_F.size(); ++i) {
                set const& F = m_F[i];
                for (j = 0; j < F.size(); ++j) {
                    if (m_value_saved[F[j]] == l_false) {
                        break;
                    }
                }
                if (F.size() == j) {
                    break;
                }
            }
            return i == m_F.size();
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

        // (simple, greedy) CDCL learner for hitting sets.

        lbool search() {
            return l_undef;
        }

        lbool propagate() {
            lbool is_sat = l_true;
            while (m_qhead < m_trail.size() && is_sat == l_true) {
                unsigned idx = m_trail[m_qhead];
                ++m_qhead;
                switch (m_value[idx]) {
                case l_undef: 
                    UNREACHABLE();
                    break;
                case l_true: 
                    is_sat = propagate(idx, l_false, m_fwatch, m_F);
                    break;
                case l_false:
                    is_sat = propagate(idx, l_true,  m_twatch, m_T);
                    break;
                }
            }
            return is_sat;
        }

        lbool propagate(unsigned idx, lbool good_val, vector<unsigned_vector>& watch, vector<set>& Fs) 
        {
            unsigned sz = watch[idx].size();
            lbool bad_val = ~good_val;
            for (unsigned i = 0; i < sz; ++i) {
                if (m_cancel) return l_undef;
                unsigned clause_id = watch[idx][i];
                set& F = Fs[clause_id];
                SASSERT(F.size() >= 2);
                unsigned k1 = (F[0] == idx)?0:1;
                unsigned k2 = 1 - k1;
                SASSERT(F[k1] == idx);
                SASSERT(m_value[F[k1]] == bad_val);
                if (m_value[F[k2]] == good_val) {
                    continue;
                }
                bool found = false;
                for (unsigned j = 2; !found && j < F.size(); ++j) {
                    unsigned idx2 = F[j];
                    if (m_value[idx2] != bad_val) {
                        found = true;
                        std::swap(F[k1], F[j]);
                        watch[idx][i] = watch[idx].back();
                        watch[idx].pop_back();
                        --i;
                        --sz;
                        watch[idx2].push_back(clause_id);
                    }
                }
                if (!found) {
                    if (m_value[F[k2]] == bad_val) {
                        return l_false;
                    }
                    SASSERT(m_value[F[k2]] == l_undef);
                    assign(F[k2], good_val, clause_id);
                }
            }
            return l_true;
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
