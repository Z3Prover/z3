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
            justification(justification const& other): 
                m_kind(other.m_kind), m_value(other.m_value), m_pos(other.m_pos) {}
            justification& operator=(justification const& other) {
                m_kind  = other.m_kind;
                m_value = other.m_value;
                m_pos   = other.m_pos;
                return *this;
            }
            unsigned clause() const { return m_value; }
            bool is_axiom() const { return m_kind == AXIOM; }
            bool is_decision() const { return m_kind == DECISION; }
            bool is_clause() const { return m_kind == CLAUSE; }
            kind_t kind() const { return m_kind; }
            bool pos() const { return m_pos; }
        };

        class set {
            unsigned m_num_elems;
            unsigned m_elems[0];
            set(): m_num_elems(0) {}
        public:
            
            static set* mk(small_object_allocator& alloc, unsigned sz, unsigned const* elems) {
                unsigned size = (sz+1)*sizeof(unsigned);
                void * mem = alloc.allocate(size);
                set* result = new (mem) set();
                result->m_num_elems = sz;
                memcpy(result->m_elems, elems, sizeof(unsigned)*sz);
                return result;
            }
            
            inline unsigned operator[](unsigned idx) const {
                SASSERT(idx < m_num_elems);
                return m_elems[idx];
            }

            inline unsigned& operator[](unsigned idx) {
                SASSERT(idx < m_num_elems);
                return m_elems[idx];
            }

            unsigned size() const { return m_num_elems; }

            unsigned alloc_size() const { return (m_num_elems + 1)*sizeof(unsigned); }

            bool empty() const { return 0 == size(); }
        };

        volatile bool           m_cancel;
        rational                m_lower;
        rational                m_upper;
        vector<rational>        m_weights;
        vector<rational>        m_weights_inv;
        rational                m_max_weight;
        rational                m_denominator;
        small_object_allocator  m_alloc;
        ptr_vector<set>         m_T;
        ptr_vector<set>         m_F;
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
        vector<rational>        m_scored_weights;
        svector<bool>           m_score_updated;
        bool                    m_enable_simplex;
        struct compare_scores {
            imp* m_imp;
            compare_scores(imp* i):m_imp(i) {}
            bool operator()(int v1, int v2) const {
                return m_imp->m_scored_weights[v1] > m_imp->m_scored_weights[v2];
            }
        };
        compare_scores          m_compare_scores;
        heap<compare_scores>    m_heap;
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

        static unsigned const null_idx = UINT_MAX;

        imp():
            m_cancel(false), 
            m_max_weight(0), 
            m_denominator(1),
            m_alloc("hitting-sets"),
            m_weights_var(0),
            m_qhead(0),
            m_scope_lvl(0),
            m_conflict_j(justification(justification::AXIOM)),
            m_inconsistent(false),
            m_compare_scores(this),
            m_heap(0, m_compare_scores) {
            m_enable_simplex = true;

        }
        ~imp() {
            for (unsigned i = 0; i < m_T.size(); ++i) {
                m_alloc.deallocate(m_T[i]->alloc_size(), m_T[i]);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                m_alloc.deallocate(m_F[i]->alloc_size(), m_F[i]);
            }
        }

        void add_weight(rational const& w) {
            SASSERT(w.is_pos());
            unsigned var = m_weights.size();
            m_simplex.ensure_var(var);
            m_simplex.set_lower(var, mpq_inf(mpq(0),mpq(0)));
            m_simplex.set_upper(var, mpq_inf(mpq(1),mpq(0)));
            m_weights.push_back(w);
            m_weights_inv.push_back(rational::one());
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
            m_scored_weights.push_back(rational(0));
            m_score_updated.push_back(true);
            m_max_weight += w;
        }

        justification add_exists_false(unsigned sz, unsigned const* S) {
            return add_exists(sz, S, true);
        }

        justification add_exists_true(unsigned sz, unsigned const* S) {
            return add_exists(sz, S, false);
        }

        justification add_exists(unsigned sz, unsigned const* S, bool sign) {
            vector<unsigned_vector>& use_list = sign?m_fuse_list:m_tuse_list;
            lbool val = sign?l_false:l_true;
            justification j(justification::AXIOM);
            ptr_vector<set>& Sets = sign?m_F:m_T;
            vector<unsigned_vector>& watch = sign?m_fwatch:m_twatch;
            init_weights();            
            if (sz == 0) { 
                set_conflict(0, justification(justification::AXIOM));
            }
            else if (sz == 1) {                
                IF_VERBOSE(2, verbose_stream() << "unit literal : " << S[0] << " " << val << "\n";);
                assign(S[0], val, justification(justification::AXIOM));
            }
            else {
                unsigned clause_id = Sets.size();
                for (unsigned i = 0; i < sz; ++i) {
                    use_list[S[i]].push_back(clause_id);
                }
                j = justification(clause_id, !sign);
                watch[S[0]].push_back(clause_id);
                watch[S[1]].push_back(clause_id);
                Sets.push_back(set::mk(m_alloc, sz, S));
                if (!sign) {
                    pop(scope_lvl());
                    inc_score(clause_id);
                }
                TRACE("opt", display(tout, j););
                IF_VERBOSE(2, if (!sign) display(verbose_stream(), j););
                if (!sign && m_enable_simplex) {
                    add_simplex_row(!sign, sz, S);
                }
            }
            return j;
        }

        lbool compute_lower() {
            m_lower.reset();
            rational w1 = L1();
            rational w2 = L2();
            rational w3 = L3();
            if (w1 > m_lower) m_lower = w1;
            if (w2 > m_lower) m_lower = w2;
            if (w3 > m_lower) m_lower = w3;
            return l_true;
        }

        lbool compute_upper() {            
            m_upper = m_max_weight;
            unsigned fsz = m_F.size();
            lbool r = search();
            pop(scope_lvl());


            IF_VERBOSE(1, verbose_stream() << "(hsmax.negated-size: " << fsz << ")\n";);
#if 0
            // garbage collect agressively on exit.
            // all learned clases for negative branches are
            // pruned.
            for (unsigned i = fsz; i < m_F.size(); ++i) {
                m_alloc.deallocate(m_F[i]->alloc_size(), m_F[i]);
            }
            m_F.resize(fsz);
            for (unsigned i = 0; i < m_fuse_list.size(); ++i) {
                unsigned_vector & uses = m_fuse_list[i];
                while (!uses.empty() && uses.back() >= fsz) uses.pop_back();
                unsigned_vector & watch = m_fwatch[i];
                unsigned j = 0, k = 0;
                for (; j < watch.size(); ++j) {
                    if (watch[j] < fsz) {
                        watch[k] = watch[j];
                        ++k;
                    } 
                }
                watch.resize(k);
            }
#endif
            return r;
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
            rational lc(1);
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                lc = lcm(lc, m_weights[i]);
            }
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                m_weights_inv[i] = lc/m_weights[i];
            }            

            m_heap.set_bounds(m_weights.size());
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                m_heap.insert(i);
            }
            update_heap();

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
            out << "inconsistent: " << m_inconsistent << "\n";
            out << "weight: " << m_weight << "\n";
            for (unsigned i = 0; i < m_weights.size(); ++i) {
                out << i << ": "  << value(i) << " w: " << m_weights[i] << " s: " << m_scores[i] << "\n";
            }
            for (unsigned i = 0; i < m_T.size(); ++i) {
                display(out << "+" << i << ": ", *m_T[i]);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                display(out << "-" << i << ": ", *m_F[i]);
            }
            out << "watch lists:\n";
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
                unsigned idx = m_trail[i];
                out << (m_justification[idx].is_decision()?"d":"") << idx << " ";
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
                set const& S = j.pos()?(*m_T[j.clause()]):(*m_F[j.clause()]);
                for (unsigned i = 0; i < S.size(); ++i) {
                    out << S[i] << " ";
                }
                out << "\n";
            }
            }
        }

        void display_lemma(std::ostream& out) {
            out << "lemma: ";
            for (unsigned i = 0; i < m_lemma.size(); ++i) {
                out << m_lemma[i] << " ";
            }
            out << "\n";
        }

        struct scoped_push {
            imp& s;
            scoped_push(imp& s):s(s) { s.push(); }
            ~scoped_push() { s.pop(1); }
        };

        struct value_lt {
            vector<rational> const& weights;
            value_lt(vector<rational> const& weights):
                weights(weights) {}
            bool operator()(int v1, int v2) const {
                return weights[v1] > weights[v2];
            }
        };

        void inc_score(unsigned clause_id) {
            set const& S = *m_T[clause_id];
            if (!has_selected(S)) {
                for (unsigned j = 0; j < S.size(); ++j) {
                    ++m_scores[S[j]];
                    m_score_updated[S[j]] = true;
                }
            }
        }

        void dec_score(unsigned clause_id) {
            set const& S = *m_T[clause_id];
            if (!has_selected(S)) {
                for (unsigned j = 0; j < S.size(); ++j) {
                    SASSERT(m_scores[S[j]] > 0);
                    --m_scores[S[j]];
                    m_score_updated[S[j]] = true;
                }
            }
        }

        void update_score(unsigned idx, bool inc) {
            unsigned_vector const& uses = m_tuse_list[idx];
            for (unsigned i = 0; i < uses.size(); ++i) {
                if (inc) {
                    inc_score(uses[i]);
                }
                else {
                    dec_score(uses[i]);
                }
            }
        }

        rational L1() {
            rational w(m_weight);
            scoped_push _sc(*this);
            for (unsigned i = 0; !canceled() && i < m_T.size(); ++i) {
                set const& S = *m_T[i];
                SASSERT(!S.empty());
                if (!has_selected(S)) {
                    w += m_weights[select_min(S)];                
                    for (unsigned j = 0; j < S.size(); ++j) {
                        assign(S[j], l_true, justification(justification::DECISION));
                    }
                }
            }
            return w;
        }

        void update_heap() {
            for (unsigned i = 0; i < m_scored_weights.size(); ++i) {
                if (m_score_updated[i]) {
                    rational const& old_w = m_scored_weights[i];
                    rational new_w = rational(m_scores[i])*m_weights_inv[i];
                    if (new_w > old_w) {
                        m_scored_weights[i] = new_w;
                        //m_heap.decreased(i);
                    }
                    else if (new_w < old_w) {
                        m_scored_weights[i] = new_w;
                        //m_heap.increased(i);
                    }
                    m_score_updated[i] = false;
                }
            }
        }

        rational L2() {
            rational w(m_weight);
            scoped_push _sc(*this);
            int n = 0;
            for (unsigned i = 0; i < m_T.size(); ++i) {
                if (!has_selected(*m_T[i])) ++n;
            }

            update_heap();
            value_lt lt(m_scored_weights);
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
            return w;
        }

        rational L3() {        
            TRACE("simplex", m_simplex.display(tout););
            VERIFY(l_true == m_simplex.make_feasible());
            TRACE("simplex", m_simplex.display(tout););
            VERIFY(l_true == m_simplex.minimize(m_weights_var));
            mpq_inf const& val = m_simplex.get_value(m_weights_var);
            unsynch_mpq_inf_manager mg;
            unsynch_mpq_manager& mq = mg.get_mpq_manager();
            scoped_mpq c(mq);
            mg.ceil(val, c);
            rational w(c);
            CTRACE("simplex", 
                   w >= m_weight, tout << w << " " << m_weight << " !!!!\n";
                   display(tout););
            SASSERT(w >= m_weight);
            return w;
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
                
        bool have_selected(lbool val, ptr_vector<set> const& Sets, unsigned& i) {
            for (i = 0; i < Sets.size(); ++i) {
                if (!has_selected(val, *Sets[i])) return false;
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
                set const& F = *m_F[i];
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

        void assign(unsigned idx, lbool val, justification const&  justification) {
            if (val == l_true) {
                m_weight += m_weights[idx];
                update_score(idx, false);
                if (m_enable_simplex) {
                    m_simplex.set_lower(idx, mpq_inf(mpq(1),mpq(0)));
                }
            }
            SASSERT(val != l_true || m_scores[idx] == 0);
            m_value[idx] = val;
            m_justification[idx] = justification;
            m_trail.push_back(idx);
            m_level[idx] = scope_lvl();
            TRACE("opt", tout << idx << " := " << val << " scope: " << scope_lvl() << " w: " << m_weight << "\n";);
        }


        svector<unsigned> m_replay_idx;
        svector<lbool> m_replay_val;
        void unassign(unsigned sz) {
            for (unsigned j = sz; j < m_trail.size(); ++j) {
                unsigned idx = m_trail[j];      
                lbool val = value(idx);
                m_value[idx] = l_undef;
                if (val == l_true) {
                    m_weight -= m_weights[idx];
                    update_score(idx, true);                  
                    if (m_enable_simplex) {
                        m_simplex.set_lower(idx, mpq_inf(mpq(0),mpq(0)));
                    }
                }
                if (m_justification[idx].is_axiom()) {
                    m_replay_idx.push_back(idx);
                    m_replay_val.push_back(val);
                }
            }
            TRACE("opt", tout << m_weight << "\n";);
            m_trail.shrink(sz);
            m_qhead = sz;
            for (unsigned i = m_replay_idx.size(); i > 0; ) {
                --i;
                unsigned idx = m_replay_idx[i];
                lbool val = m_replay_val[i];
                assign(idx, val, justification(justification::AXIOM));
            }
            m_replay_idx.reset();
            m_replay_val.reset();
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
                    SASSERT(validate_model());
                    m_model.reset();
                    m_model.append(m_value);
                    m_upper = m_weight;
                    // SASSERT(m_weight < m_max_weight);
                    return l_true;
                }
            }
        }

        bool validate_model() {
            for (unsigned i = 0; i < m_T.size(); ++i) {
                set const& S = *m_T[i];
                bool found = false;
                for (unsigned j = 0; !found && j < S.size(); ++j) {
                    found = value(S[j]) == l_true;
                }
                CTRACE("opt", !found, 
                       display(tout << "not found: " << i << "\n", S);
                       display(tout););
                SASSERT(found);
            }
            for (unsigned i = 0; i < m_F.size(); ++i) {
                set const& S = *m_F[i];
                bool found = false;
                for (unsigned j = 0; !found && j < S.size(); ++j) {
                    found = value(S[j]) != l_true;
                }
                CTRACE("opt", !found, 
                       display(tout << "not found: " << i << "\n", S);
                       display(tout););
                SASSERT(found);
            }

            return true;
        }

        bool invariant() {
            for (unsigned i = 0; i < m_fwatch.size(); ++i) {
                for (unsigned j = 0; j < m_fwatch[i].size(); ++j) {
                    set const& S = *m_F[m_fwatch[i][j]];
                    SASSERT(S[0] == i || S[1] == i);
                }
            }
            for (unsigned i = 0; i < m_twatch.size(); ++i) {
                for (unsigned j = 0; j < m_twatch[i].size(); ++j) {
                    set const& S = *m_T[m_twatch[i][j]];
                    SASSERT(S[0] == i || S[1] == i);
                }
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
                ptr_vector<set> const& S = conflict_j.pos()?m_T:m_F;
                r = std::max(r, lvl((*S[clause])[0]));
                r = std::max(r, lvl((*S[clause])[1]));
            }
            return r;
        }
        
        bool resolve_conflict_core() {            
            SASSERT(inconsistent());
            TRACE("opt", display(tout););
            unsigned conflict_l = m_conflict_l;
            justification conflict_j(m_conflict_j);
            if (conflict_j.is_axiom()) {
                return false;
            }
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
                    set const& T = conflict_j.pos()?(*m_T[cl]):(*m_F[cl]); 
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
                else if (conflict_j.is_decision()) {
                    --num_marks;
                    SASSERT(num_marks == 0);
                    break;
                }
                else if (conflict_j.is_axiom()) {
                    IF_VERBOSE(0, verbose_stream() << "axiom " << conflict_l << " " << value(conflict_l) << " " << num_marks << "\n";);
                    --num_marks;
                    SASSERT(num_marks == 0);
                    break;
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
                if (num_marks == 0 && value(conflict_l) == l_false) {
                    ++num_marks;
                }
                reset_mark(conflict_l);
            }
            while (num_marks > 0);
            m_lemma[0] = conflict_l;
            TRACE("opt", display_lemma(tout););
            SASSERT(value(conflict_l) == l_true);
            unsigned new_scope_lvl = 0;
            for (unsigned i = 1; i < m_lemma.size(); ++i) {
                SASSERT(l_true == value(m_lemma[i]));
                new_scope_lvl = std::max(new_scope_lvl, lvl(m_lemma[i]));
                reset_mark(m_lemma[i]);
            }
            pop(scope_lvl() - new_scope_lvl);
            SASSERT(l_undef == value(conflict_l));
            justification j = add_exists_false(m_lemma.size(), m_lemma.c_ptr());
            if (!j.is_axiom()) assign(conflict_l, l_false, j);            
            return true;
        }


        void process_antecedent(unsigned antecedent, unsigned& num_marks) {
            unsigned alvl = lvl(antecedent);
            SASSERT(alvl <= m_conflict_lvl);
            if (!is_marked(antecedent) && alvl > 0 && !m_justification[antecedent].is_axiom()) {
                mark(antecedent);
                if (alvl == m_conflict_lvl || value(antecedent) == l_false) {
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
            update_heap();
            
            value_lt lt(m_scored_weights);
            std::sort(m_indices.begin(), m_indices.end(), lt);
            unsigned idx = m_indices[0];
            if (m_scores[idx] == 0) return UINT_MAX;
            return idx;
#if 0            
            int min_val = m_heap.min_value();
            if (min_val == -1) {
                return UINT_MAX;
            }
            SASSERT(0 <= min_val && static_cast<unsigned>(min_val) < m_weights.size());
            if (m_scores[min_val] == 0) {
                return UINT_MAX;
            }
            return static_cast<unsigned>(min_val);
#endif
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
            TRACE("opt", display(tout););
            SASSERT(invariant());
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
            prune_branch();
        }

        void propagate(unsigned idx, lbool good_val, vector<unsigned_vector>& watch, ptr_vector<set>& Fs) 
        {
            TRACE("opt", tout << idx << " " << value(idx) << "\n";);
            unsigned_vector& w = watch[idx];
            unsigned sz = w.size();
            lbool bad_val = ~good_val;
            SASSERT(value(idx) == bad_val);
            unsigned l = 0;
            for (unsigned i = 0; i < sz && !canceled(); ++i, ++l) {
                unsigned clause_id = w[i];
                set& F = *Fs[clause_id];
                SASSERT(F.size() >= 2);
                bool k1 = (F[0] != idx);
                bool k2 = !k1;
                SASSERT(F[k1] == idx);
                SASSERT(value(F[k1]) == bad_val);
                if (value(F[k2]) == good_val) {
                    w[l] = w[i];
                    continue;
                }
                bool found = false;
                unsigned sz2 = F.size();
                for (unsigned j = 2; !found && j < sz2; ++j) {
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
                        if (i == l) {
                            l = sz;                            
                        }
                        else {
                            for (; i < sz; ++i, ++l) {
                                w[l] = w[i];
                            }
                        }
                        break;
                    }
                    else {
                        SASSERT(value(F[k2]) == l_undef);
                        assign(F[k2], good_val, justification(clause_id, good_val == l_true));
                        w[l] = w[i];
                    }
                }
            }
            watch[idx].shrink(l);
            SASSERT(invariant());
            TRACE("opt", tout << idx << " " << value(idx) << "\n";);
            SASSERT(value(idx) == bad_val);
        }

        bool infeasible_lookahead() {
            if (m_enable_simplex && L3() >= m_max_weight) {
                return true;
            }
            return 
                (L1() >= m_max_weight) || 
                (L2() >= m_max_weight);
        }

        void prune_branch() {
            if (inconsistent() || !infeasible_lookahead()) {
                return;
            }
             
            IF_VERBOSE(4, verbose_stream() << "(hs.prune-branch " << m_weight << ")\n";);
            m_lemma.reset();
            unsigned i = 0;
            rational w(0);
            for (; i < m_trail.size() && w < m_max_weight; ++i) {
                unsigned idx = m_trail[i];
                if (m_justification[idx].is_decision()) {
                    SASSERT(value(idx) == l_true);
                    m_lemma.push_back(idx);
                    w += m_weights[idx];
                }                    
            }
            // undo the lower bounds.
            TRACE("opt",
                  tout << "prune branch: " << m_weight << " ";
                  display_lemma(tout);
                  display(tout);
                  );
            justification j = add_exists_false(m_lemma.size(), m_lemma.c_ptr());
            unsigned idx = m_lemma.empty()?0:m_lemma[0];
            set_conflict(idx, j);                            
        }

        // TBD: derive strong inequalities and add them to Simplex.
        // x_i1 + .. + x_ik >= k-1 for each subset k from set n:  x_1 + .. + x_n >= k         
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
