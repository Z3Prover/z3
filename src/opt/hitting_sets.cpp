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
        class justification {
        public:
            enum kind_t { AXIOM, DECISION, CLAUSE };
        private:
            kind_t   m_kind;
            unsigned m_value;
            bool     m_pos;
        public:
            explicit justification(kind_t k):m_kind(k), m_value(0), m_pos(false) {}
            explicit justification(unsigned v, bool pos):m_kind(CLAUSE), m_value(v), m_pos(pos) {}
            explicit justification(justification const& other): m_kind(other.m_kind), m_value(other.m_value), m_pos(other.m_pos) {}
            justification& operator=(justification const& other) {
                m_kind = other.m_kind;
                m_value = other.m_value;
                m_pos = other.m_pos;
                return *this;
            }
            unsigned clause() const { return m_value; }
            bool is_axiom() const { return m_kind == AXIOM; }
            bool is_decision() const { return m_kind == DECISION; }
            bool is_clause() const { return m_kind == CLAUSE; }
            kind_t kind() const { return m_kind; }
            bool pos() const { return m_pos; }
        };
        volatile bool           m_cancel;
        rational                m_lower;
        rational                m_upper;
        vector<rational>        m_weights;
        rational                m_max_weight;
        rational                m_denominator;
        vector<set>             m_T;
        vector<set>             m_F;
        svector<lbool>          m_value;        
        svector<lbool>          m_model;
        vector<unsigned_vector> m_tuse_list;        
        vector<unsigned_vector> m_fuse_list;        

        // Custom CDCL solver.
        svector<justification>  m_justification;
        vector<unsigned_vector> m_twatch;        
        vector<unsigned_vector> m_fwatch;
        unsigned_vector         m_level;
        unsigned_vector         m_trail;      // trail of assigned literals
        unsigned                m_qhead;      // queue head
        justification           m_conflict_j; // conflict justification
        unsigned                m_conflict_l; // conflict literal
        bool                    m_inconsistent;
        unsigned                m_scope_lvl;        
        rational                m_weight;      // current weight of assignment.
        unsigned_vector         m_indices;
        unsigned_vector         m_scores;
        svector<bool>           m_mark;
        struct scope {
            unsigned m_trail_lim;
        };
        vector<scope>           m_scopes;
        unsigned_vector         m_lemma;
        unsigned                m_conflict_lvl;

        // simplex
        unsynch_mpz_manager     m;
        Simplex                 m_simplex;
        unsigned                m_weights_var;

        // sat solver
        params_ref              m_params;
        sat::solver             m_solver;
        svector<sat::bool_var>  m_vars;

        static unsigned const null_idx = UINT_MAX;

        imp():
            m_cancel(false), 
            m_max_weight(0), 
            m_denominator(1),
            m_weights_var(0),
            m_qhead(0),
            m_scope_lvl(0),
            m_conflict_j(justification(justification::AXIOM)),
            m_inconsistent(false),
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
            m_justification.push_back(justification(justification::DECISION));
            m_tuse_list.push_back(unsigned_vector());
            m_fuse_list.push_back(unsigned_vector());
            m_twatch.push_back(unsigned_vector());
            m_fwatch.push_back(unsigned_vector());
            m_level.push_back(0);
            m_indices.push_back(var);
            m_model.push_back(l_undef);
            m_mark.push_back(false);
            m_scores.push_back(0);
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
                assign(S[0], val, justification(justification::AXIOM));
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
            return search();
            // return U1();
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
                idx < m_model.size() && 
                m_model[idx] == l_true;
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
                out << i << ": "  << m_model[i]<< " " << m_weights[i] << "\n";
            }
            for (unsigned i = 0; i < m_T.size(); ++i) {
                display(out << "+ ", m_T[i]);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                display(out << "- ", m_F[i]);
            }
            out << "inconsistent: " << m_inconsistent << "\n";
            out << "weight: " << m_weight << "\n";
            out << "use lists:\n";
            for (unsigned i = 0; i < m_fwatch.size(); ++i) {
                out << i << ": ";
                for (unsigned j = 0; j < m_twatch[i].size(); ++j) {
                    out << "+" << m_twatch[i][j] << " ";
                }
                for (unsigned j = 0; j < m_fwatch[i].size(); ++j) {
                    out << "-" << m_fwatch[i][j] << " ";
                }
                out << "\n";
            }
            out << "trail\n";
            for (unsigned i = 0; i < m_trail.size(); ++i) {
                out << m_trail[i] << " ";
            }
            out << "\n";
        }

        void display(std::ostream& out, set const& S) const {
            for (unsigned i = 0; i < S.size(); ++i) {
                out << S[i] << " ";
            }
            out << "\n";
        }

        void display(std::ostream& out, justification const& j) const {
            switch(j.kind()) {
            case justification::AXIOM: 
                out << "axiom\n"; 
                break;
            case justification::DECISION: 
                out << "decision\n"; 
                break;
            case justification::CLAUSE: {
                out << "clause: ";
                set const& S = j.pos()?m_T[j.clause()]:m_F[j.clause()];
                for (unsigned i = 0; i < S.size(); ++i) {
                    out << S[i] << " ";
                }
                out << "\n";
            }
            }
        }

        struct scoped_select {
            imp& s;
            unsigned sz;
            scoped_select(imp& s):s(s), sz(s.m_trail.size()) {
            }
            ~scoped_select() {
                s.unassign(sz);
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
                    SASSERT(m_model[F[i]] == l_true);
                    if (max_value < m_weights[F[i]]) {
                        max_value = m_weights[F[i]];
                        j = F[i];
                    }
                }
                IF_VERBOSE(1, verbose_stream() << "(hs.unselect " << j << ")\n";);
                assign(j, l_false, justification(justification::DECISION));
                for (i = 0; i < m_T.size(); ++i) {
                    set const& S = m_T[i];
                    for (j = 0; j < S.size(); ++j) {
                        if (l_false != value(S[j])) break;
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
                    m_model.reset();
                    m_upper.reset();
                    for (unsigned i = 0; i < m_vars.size(); ++i) {
                        m_model.push_back(model[m_vars[i]]);
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
            
            //
            // Sort indices.
            // The least literals are those where score/w is maximized.
            //
            value_lt lt(m_weights, m_scores);
            while (true) {
                if (canceled()) {
                    return l_undef;
                }
                init_scores();
                std::sort(m_indices.begin(), m_indices.end(), lt);
                unsigned idx = m_indices[0];
                if (m_scores[idx] == 0) {
                    break;
                }
                assign(idx, l_true, justification(justification::DECISION));
            }
            m_upper = m_weight;
            m_model.reset();
            m_model.append(m_value);
            return l_true;
        }

        void init_scores() {
            unsigned_vector & scores = m_scores;
            scores.reset();
            for (unsigned i = 0; i < m_value.size(); ++i) {
                scores.push_back(0);
            }
            for (unsigned i = 0; i < m_T.size(); ++i) {
                set const& S = m_T[i];
                if (!has_selected(S)) {
                    for (unsigned j = 0; j < S.size(); ++j) {
                        if (value(S[j]) != l_false) {
                            ++scores[S[j]];
                        }
                    }
                }
            }
        }

        bool L1() {
            rational w(0);
            scoped_select _sc(*this);
            for (unsigned i = 0; !canceled() && i < m_T.size(); ++i) {
                set const& S = m_T[i];
                SASSERT(!S.empty());
                if (!has_selected(S)) {
                    w += m_weights[select_min(S)];                
                    for (unsigned j = 0; j < S.size(); ++j) {
                        assign(S[j], l_true, justification(justification::DECISION));
                    }
                }
            }
            if (m_lower < w) {
                m_lower = w;
            }
            return !canceled();
        }

        bool L2() {
            rational w(0);
            scoped_select _sc(*this);
            int n = 0;
            for (unsigned i = 0; i < m_T.size(); ++i) {
                if (!has_selected(m_T[i])) ++n;
            }
            init_scores();
            value_lt lt(m_weights, m_scores);

            std::sort(m_indices.begin(), m_indices.end(), lt);
            for(unsigned i = 0; i < m_indices.size() && n > 0; ++i) {
                // deg(c) = score(c)
                // wt(c) = m_weights[c]
                unsigned idx = m_indices[i];
                if (m_scores[idx] == 0) {
                    break;
                }
                if (m_scores[idx] < static_cast<unsigned>(n) || m_weights[idx].is_one()) {
                    w += m_weights[idx];
                }
                else {
                    w += div((rational(n)*m_weights[idx]), rational(m_scores[idx]));
                }
                n -= m_scores[idx];
            }
            if (m_lower < w) {
                m_lower = w;
            }
            return !canceled();
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
        
        unsigned select_min(set const& S) {
            unsigned result = S[0];
            for (unsigned i = 1; i < S.size(); ++i) {
                if (m_weights[result] > m_weights[S[i]]) {
                    result = S[i];
                }
            }
            return result;
        }
                
        bool have_selected(lbool val, vector<set> const& Sets, unsigned& i) {
            for (i = 0; i < Sets.size(); ++i) {
                if (!has_selected(val, Sets[i])) return false;
            }
            return true;
        }

        void set_undef_to_false() {
            for (unsigned i = 0; i < m_model.size(); ++i) {
                if (m_model[i] == l_undef) {
                    m_model[i] = l_false;
                }
            }
        }

        bool values_satisfy_Fs(unsigned& i) {
            unsigned j = 0;
            for (i = 0; i < m_F.size(); ++i) {
                set const& F = m_F[i];
                for (j = 0; j < F.size(); ++j) {
                    if (m_model[F[j]] == l_false) {
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
                if (val == value(S[i])) {
                    return true;
                }
            }
            return false;
        }

        // (greedy) CDCL learner for hitting sets.

        inline unsigned scope_lvl() const { return m_scope_lvl; }
        inline bool inconsistent() const { return m_inconsistent; }
        inline bool canceled() const { return m_cancel; }
        inline unsigned lvl(unsigned idx) const { return m_level[idx]; }
        inline lbool value(unsigned idx) const { return m_value[idx]; }

        inline bool is_marked(unsigned v) const { return m_mark[v] != 0; }
        inline void mark(unsigned v) { SASSERT(!is_marked(v)); m_mark[v] = true; }
        inline void reset_mark(unsigned v) { SASSERT(is_marked(v)); m_mark[v] = false; }

        void push() {
            SASSERT(!inconsistent());
            ++m_scope_lvl;
            m_scopes.push_back(scope());
            scope& s = m_scopes.back();
            s.m_trail_lim = m_trail.size();
        }

        void pop(unsigned n) {
            if (n > 0) {
                m_inconsistent = false;
                m_scope_lvl = scope_lvl() - n;
                unassign(m_scopes[scope_lvl()].m_trail_lim);
                m_scopes.shrink(scope_lvl());
            }        
        }

        void assign(unsigned j, lbool val, justification const&  justification) {
            if (val == l_true) {
                m_weight += m_weights[j];
            }
            m_value[j] = val;
            m_justification[j] = justification;
            m_trail.push_back(j);
            m_level[j] = scope_lvl();
            TRACE("opt", tout << j << " := " << val << " scope: " << scope_lvl() << " w: " << m_weight << "\n";);
        }

        void unassign(unsigned sz) {
            for (unsigned j = sz; j < m_trail.size(); ++j) {
                unsigned idx = m_trail[j];                
                if (value(idx) == l_true) {
                    m_weight -= m_weights[idx];
                }
                m_value[idx] = l_undef;
            }
            TRACE("opt", tout << m_weight << "\n";);
            m_trail.shrink(sz);
            m_qhead = sz;
        }


        lbool search() {
            TRACE("opt", display(tout););
            pop(scope_lvl());
            while (true) {
                while (true) {
                    propagate();
                    if (canceled()) return l_undef;
                    if (!inconsistent()) break;
                    if (!resolve_conflict()) return l_false;
                    SASSERT(!inconsistent());
                }
                if (!decide()) {
                    m_model.reset();
                    m_model.append(m_value);
                    SASSERT(validate_model());
                    m_upper = m_weight;
                    // SASSERT(m_weight < m_max_weight);
                    return l_true;
                }
            }
        }

        bool validate_model() {
            for (unsigned i = 0; i < m_T.size(); ++i) {
                set const& S = m_T[i];
                bool found = false;
                for (unsigned j = 0; !found && j < S.size(); ++j) {
                    found = value(S[j]) == l_true;
                }
                SASSERT(found);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                set const& S = m_F[i];
                bool found = false;
                for (unsigned j = 0; !found && j < S.size(); ++j) {
                    found = value(S[j]) != l_true;
                }
                CTRACE("opt", !found, display(tout << "not found: " << i << "\n", S););
                SASSERT(found);
            }

            return true;
        }

        bool resolve_conflict() {
            while (true) {
                if (!resolve_conflict_core()) return false;
                if (!inconsistent()) return true;
            }
        }

        unsigned get_max_lvl(unsigned conflict_l, justification const& conflict_j) {
            if (scope_lvl() == 0) return 0;
            unsigned r = lvl(conflict_l);
            if (conflict_j.is_clause()) {
                unsigned clause = conflict_j.clause();
                vector<unsigned_vector> const& S = conflict_j.pos()?m_T:m_F;
                r = std::max(r, lvl(S[clause][0]));
                r = std::max(r, lvl(S[clause][1]));
            }
            return r;
        }
        
        bool resolve_conflict_core() {            
            SASSERT(inconsistent());
            TRACE("opt", display(tout););
            unsigned conflict_l = m_conflict_l;
            justification conflict_j(m_conflict_j);
            m_conflict_lvl = get_max_lvl(conflict_l, conflict_j);
            if (m_conflict_lvl == 0) {
                return false;
            }
            unsigned idx = skip_above_conflict_level();
            unsigned num_marks = 0;
            m_lemma.reset();
            m_lemma.push_back(0);
            process_antecedent(conflict_l, num_marks);
            do {
                TRACE("opt", tout << "conflict literal: " << conflict_l << "\n";
                      display(tout, conflict_j););
                if (conflict_j.is_clause()) {
                    unsigned cl = conflict_j.clause();
                    unsigned i = 0;
                    SASSERT(value(conflict_l) != l_undef);
                    set const& T = conflict_j.pos()?m_T[cl]:m_F[cl]; 
                    if (T[0] == conflict_l) {
                        i = 1;
                    }
                    else {
                        SASSERT(T[1] == conflict_l);
                        process_antecedent(T[0], num_marks);
                        i = 2;
                    }
                    unsigned sz = T.size();
                    for (; i < sz; ++i) {
                        process_antecedent(T[i], num_marks);
                    }
                }
                while (true) {
                    unsigned l = m_trail[idx];
                    if (is_marked(l)) break;
                    SASSERT(idx > 0);
                    --idx;
                }
                conflict_l = m_trail[idx];
                conflict_j = m_justification[conflict_l];
                --idx;
                --num_marks;
                reset_mark(conflict_l);
            }
            while (num_marks > 0);
            m_lemma[0] = conflict_l;

            unsigned new_scope_lvl = 0;
            TRACE("opt",
                  for (unsigned i = 0; i < m_lemma.size(); ++i) {
                      tout << m_lemma[i] << " ";
                  }
                  tout << "\n";);
            for (unsigned i = 0; i < m_lemma.size(); ++i) {
                SASSERT(l_true == value(m_lemma[i]));
                new_scope_lvl = std::max(new_scope_lvl, lvl(m_lemma[i]));
                reset_mark(m_lemma[i]);
            }
            pop(scope_lvl() - new_scope_lvl);
            add_exists_false(m_lemma.size(), m_lemma.c_ptr());
            return true;
        }

        void process_antecedent(unsigned antecedent, unsigned& num_marks) {
            unsigned alvl = lvl(antecedent);
            SASSERT(alvl <= m_conflict_lvl);
            if (!is_marked(antecedent) && alvl > 0) {
                mark(antecedent);
                if (alvl == m_conflict_lvl) {
                    ++num_marks;
                }
                else {
                    m_lemma.push_back(antecedent);
                }
            }
        }

        unsigned skip_above_conflict_level() {
            unsigned idx = m_trail.size();
            if (idx == 0) {
                return idx;
            }
            idx--;
            // skip literals from levels above the conflict level
            while (lvl(m_trail[idx]) > m_conflict_lvl) {
                SASSERT(idx > 0);
                idx--;
            }
            return idx;
        }

        void set_conflict(unsigned idx, justification const& justification) {
            if (!inconsistent()) {
                TRACE("opt", tout << "conflict: " << idx << "\n";);
                m_inconsistent = true;
                m_conflict_j = justification;
                m_conflict_l = idx;
            }
        }

        unsigned next_var() {
            value_lt lt(m_weights, m_scores);
            init_scores();
            std::sort(m_indices.begin(), m_indices.end(), lt);
            unsigned idx = m_indices[0];
            if (m_scores[idx] == 0) {
                idx = UINT_MAX;
            }
            return idx;            
        }

        bool decide() {
            unsigned idx = next_var();
            if (idx == UINT_MAX) {
                return false;
            }
            else {
                push();
                TRACE("opt", tout << "decide " << idx << "\n";);
                assign(idx, l_true, justification(justification::DECISION));
                return true;
            }
        }

        void propagate() {
            while (m_qhead < m_trail.size() && !inconsistent() && !canceled()) {
                unsigned idx = m_trail[m_qhead];
                ++m_qhead;
                switch (value(idx)) {
                case l_undef: 
                    UNREACHABLE();
                    break;
                case l_true: 
                    propagate(idx, l_false, m_fwatch, m_F);
                    break;
                case l_false:
                    propagate(idx, l_true,  m_twatch, m_T);
                    break;
                }
            }
            //prune_branch();
        }

        void propagate(unsigned idx, lbool good_val, vector<unsigned_vector>& watch, vector<set>& Fs) 
        {
            TRACE("opt", tout << idx << "\n";);
            unsigned sz = watch[idx].size();
            lbool bad_val = ~good_val;
            unsigned l = 0;
            for (unsigned i = 0; i < sz && !canceled(); ++i, ++l) {
                unsigned clause_id = watch[idx][i];
                set& F = Fs[clause_id];
                SASSERT(F.size() >= 2);
                unsigned k1 = (F[0] == idx)?0:1;
                unsigned k2 = 1 - k1;
                SASSERT(F[k1] == idx);
                SASSERT(value(F[k1]) == bad_val);
                if (value(F[k2]) == good_val) {
                    watch[idx][l] = watch[idx][i];
                    continue;
                }
                bool found = false;
                for (unsigned j = 2; !found && j < F.size(); ++j) {
                    unsigned idx2 = F[j];
                    if (value(idx2) != bad_val) {
                        found = true;
                        std::swap(F[k1], F[j]);
                        --l;
                        watch[idx2].push_back(clause_id);
                    }
                }
                if (!found) {
                    if (value(F[k2]) == bad_val) {
                        set_conflict(F[k2], justification(clause_id, good_val == l_true));
                        return;
                    }
                    SASSERT(value(F[k2]) == l_undef);
                    assign(F[k2], good_val, justification(clause_id, good_val == l_true));
                    watch[idx][l] = watch[idx][i];
                }
            }
            watch[idx].shrink(l);
        }

        void prune_branch() {
            // TBD: make this more powerful
            // by using L1, L2, L3 pruning criteria.
            if (m_weight >= m_max_weight) {
                m_inconsistent = true;
                for (unsigned i = m_trail.size(); i > 0; ) {
                    --i;
                    if (value(m_trail[i]) == l_true) {
                        m_conflict_l = m_trail[i];
                        m_conflict_j = m_justification[m_conflict_l];
                        break;
                    }
                }
            }
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
