/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_lookahead.h

Abstract:
   
    Lookahead SAT solver in the style of March.
    Thanks also to the presentation in sat11.w.    

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-11

Notes:

--*/
#ifndef _SAT_LOOKAHEAD_H_
#define _SAT_LOOKAHEAD_H_

// #define OLD_NARY 0

#include "sat_elim_eqs.h"

namespace sat {

    struct pp_prefix {
        uint64_t m_prefix;
        unsigned m_depth;
        pp_prefix(uint64_t p, unsigned d) : m_prefix(p), m_depth(d) {}
    };
    
    inline std::ostream& operator<<(std::ostream& out, pp_prefix const& p) {
        unsigned d = std::min(63u, p.m_depth);
        for (unsigned i = 0; i <= d; ++i) {
            if (0 != (p.m_prefix & (1ull << i))) out << "1"; else out << "0";
        }
        if (d < p.m_depth) {
            out << " d:" << p.m_depth;
        }
        return out;
    }

    enum lookahead_mode {
        searching,         // normal search
        lookahead1,        // lookahead mode
        lookahead2         // double lookahead
    };

    inline std::ostream& operator<<(std::ostream& out, lookahead_mode m) {
        switch (m) {
        case lookahead_mode::searching:  return out << "searching";
        case lookahead_mode::lookahead1: return out << "lookahead1";
        case lookahead_mode::lookahead2: return out << "lookahead2";
        default: break;
        }
        return out;
    }

    const double dbl_max = 100000000.0;

    class lookahead {
        solver&    m_s;
        unsigned   m_num_vars;
        reslimit   m_rlimit;

        friend class ccc;
        friend class ba_solver;

        struct config {
            double   m_dl_success;
            double   m_alpha;
            double   m_max_score;
            unsigned m_max_hlevel; 
            unsigned m_min_cutoff;
            bool     m_preselect;
            unsigned m_level_cand;
            double   m_delta_rho;
            unsigned m_dl_max_iterations;
            unsigned m_tc1_limit;
            reward_t m_reward_type;
            cutoff_t m_cube_cutoff;
            unsigned m_cube_depth;
            double   m_cube_fraction;
            double   m_cube_freevars;
            double   m_cube_psat_var_exp;
            double   m_cube_psat_clause_base;
            double   m_cube_psat_trigger;

            config() {
                memset(this, 0, sizeof(*this));
                m_dl_success = 0.8;
                m_alpha = 3.5;
                m_max_score = 20.0;
                m_max_hlevel = 50;
                m_min_cutoff = 30;
                m_preselect = false;
                m_level_cand = 600;
                m_delta_rho = (double)0.7;
                m_dl_max_iterations = 2;
                m_tc1_limit = 10000000;
                m_reward_type = ternary_reward;
                m_cube_cutoff = adaptive_freevars_cutoff;
                m_cube_depth = 10;
                m_cube_fraction = 0.4;
                m_cube_freevars = 0.8;
                m_cube_psat_var_exp = 1.0;
                m_cube_psat_clause_base = 2.0;
                m_cube_psat_trigger = 5.0;
            }
        };

        struct prefix {
            unsigned m_prefix;
            unsigned m_length;
            prefix(): m_prefix(0), m_length(0) {}            
        };

        struct lit_info {
            double     m_lookahead_reward;
            unsigned  m_double_lookahead;
            lit_info(): m_lookahead_reward(0), m_double_lookahead(0) {}
        };

        struct stats {
            unsigned m_propagations;
            unsigned m_bca;
            unsigned m_add_binary;
            unsigned m_del_binary;
            unsigned m_decisions;
            unsigned m_windfall_binaries;
            unsigned m_double_lookahead_propagations;
            unsigned m_double_lookahead_rounds;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        struct binary {
            binary(literal u, literal v): m_u(u), m_v(v) {}
            literal m_u, m_v;
        };

        class nary {            
            unsigned m_size;         // number of non-false literals
            size_t   m_obj_size;     // object size (counting all literals)
            literal  m_head;         // head literal
            literal  m_literals[0];  // list of literals, put any true literal in head.
            size_t num_lits() const {
                return (m_obj_size - sizeof(nary)) / sizeof(literal);
            }
        public:
            static size_t get_obj_size(unsigned sz) { return sizeof(nary) + sz * sizeof(literal); }
            size_t obj_size() const { return m_obj_size; }
            nary(unsigned sz, literal const* lits):
                m_size(sz),
                m_obj_size(get_obj_size(sz)) {
                for (unsigned i = 0; i < sz; ++i) m_literals[i] = lits[i];
                m_head = lits[0];
            }
            unsigned size() const { return m_size; }
            unsigned dec_size() { SASSERT(m_size > 0); return --m_size; }
            void inc_size() { SASSERT(is_reduced()); ++m_size; }
            literal get_head() const { return m_head; }
            void set_head(literal l) { m_head = l; }
            bool is_reduced() const { return m_size < num_lits(); }

            literal operator[](unsigned i) { SASSERT(i < num_lits()); return m_literals[i]; }
            literal const* begin() const { return m_literals; }
            literal const* end() const { return m_literals + num_lits(); }
            // swap the true literal to the head.
            // void swap(unsigned i, unsigned j) { SASSERT(i < num_lits() && j < num_lits()); std::swap(m_literals[i], m_literals[j]); }
        };

        struct cube_state {
            bool           m_first;
            svector<bool>  m_is_decision;
            literal_vector m_cube;
            double         m_freevars_threshold;
            double         m_psat_threshold;
            unsigned       m_conflicts;
            unsigned       m_cutoffs;
            cube_state() { reset(); }
            void reset() { 
                m_first = true;
                m_is_decision.reset(); 
                m_cube.reset(); 
                m_freevars_threshold = 0;
                m_psat_threshold = dbl_max;
                reset_stats();
            }
            void reset_stats() { m_conflicts = 0; m_cutoffs = 0; }
            void inc_conflict() { ++m_conflicts; }
            void inc_cutoff() { ++m_cutoffs; }
        };

        config                 m_config;
        double                 m_delta_trigger;
        double                 m_delta_decrease;

        drat                   m_drat;
        literal_vector         m_assumptions;

        literal_vector         m_trail;         // trail of units
        unsigned_vector        m_trail_lim;
        vector<literal_vector> m_binary;        // literal: binary clauses
        unsigned_vector        m_binary_trail;  // trail of added binary clauses
        unsigned_vector        m_binary_trail_lim; 

        // specialized clause managemet uses ternary clauses and dedicated clause data-structure.
        // this replaces m_clauses below
        vector<svector<binary>> m_ternary;        // lit |-> vector of ternary clauses
        unsigned_vector         m_ternary_count;  // lit |-> current number of active ternary clauses for lit

        small_object_allocator    m_allocator;
        vector<ptr_vector<nary>>  m_nary;        // lit |-> vector of nary clauses
        ptr_vector<nary>          m_nary_clauses; // vector of all nary clauses
        unsigned_vector           m_nary_count;     // lit |-> number of valid clause_id in m_nary[lit]

        unsigned               m_num_tc1;
        unsigned_vector        m_num_tc1_lim;
        unsigned               m_qhead;         // propagation queue head
        unsigned_vector        m_qhead_lim;
        bool                   m_inconsistent;
        unsigned_vector        m_bstamp;        // literal: timestamp for binary implication
        vector<svector<double> >  m_H;           // literal: fitness score
        svector<double>*        m_heur;          // current fitness 
        svector<double>         m_rating;        // var:     pre-selection rating
        unsigned               m_bstamp_id;     // unique id for binary implication.
        unsigned               m_istamp_id;     // unique id for managing double lookaheads
        unsigned_vector        m_stamp;         // var: timestamp with truth value        
        unsigned               m_level;         // current level, = 2 * m_trail_lim.size() 
        const unsigned         c_fixed_truth = UINT_MAX - 1;
        vector<watch_list>     m_watches;       // literal: watch structure
        svector<lit_info>      m_lits;          // literal: attributes.
        double                 m_lookahead_reward; // metric associated with current lookahead1 literal.
        literal_vector         m_wstack;        // windofall stack that is populated in lookahead1 mode
        unsigned               m_last_prefix_length;
        uint64_t                 m_prefix;        // where we are in search tree
        svector<prefix>        m_vprefix;       // var:     prefix where variable participates in propagation
        unsigned               m_rating_throttle; // throttle to recompute rating
        indexed_uint_set       m_freevars;
        unsigned               m_init_freevars;
        lookahead_mode         m_search_mode;   // mode of search
        stats                  m_stats;
        model                  m_model; 
        cube_state             m_cube_state;
        //scoped_ptr<extension>  m_ext;
 
        // ---------------------------------------
        // truth values


        inline bool is_fixed_at(literal l, unsigned level) const { return m_stamp[l.var()] >= level; }
        inline bool is_fixed(literal l) const { return is_fixed_at(l, m_level); }
        inline bool is_undef(literal l) const { return !is_fixed(l); }
        inline bool is_undef(bool_var v) const { return m_stamp[v] < m_level; }
        inline bool is_false_at(literal l, unsigned level) const {
            return is_fixed_at(l, level) && (bool)((m_stamp[l.var()] & 0x1) ^ l.sign());
        } // even iff l.sign()
        inline bool is_false(literal l)  const { return is_false_at(l, m_level); }
        inline bool is_true_at(literal l, unsigned level) const {
            return is_fixed_at(l, level) && !(bool)((m_stamp[l.var()] & 0x1) ^ l.sign());
        }
        inline bool is_true(literal l) const { return is_true_at(l, m_level); }
        inline void set_true(literal l) { m_stamp[l.var()] = m_level + l.sign(); }
        inline void set_undef(literal l) { m_stamp[l.var()] = 0; }
        inline unsigned get_level(literal l) const { return m_stamp[l.var()] & ~0x1; }
        void set_level(literal d, literal s) { m_stamp[d.var()] = get_level(s) + d.sign(); }
        lbool value(literal l) const { return is_undef(l) ? l_undef : is_true(l) ? l_true : l_false; }
        
        // set the level within a scope of the search.
        class scoped_level {
            lookahead& m_parent;
            unsigned   m_save;
        public:
            scoped_level(lookahead& p, unsigned l): 
                m_parent(p), m_save(p.m_level)  {
                p.m_level = l;
            }
            ~scoped_level() {
                m_parent.m_level = m_save;
            }
        };

        class scoped_ext {
            lookahead& p;
        public:
            scoped_ext(lookahead& p);
            ~scoped_ext();
        };

        class scoped_assumptions {
            lookahead& p;
            literal_vector lits;
        public:
            scoped_assumptions(lookahead& p, literal_vector const& lits);
            ~scoped_assumptions();
        };

        // -------------------------------------
        // prefix updates. I use low order bits.
        
        void flip_prefix();
        void prune_prefix();

        /**
           length < trail_lim.size:
           - mask m_prefix and p wrt length
           - update if different.
         */
        void update_prefix(literal l);

        bool active_prefix(bool_var x);

        // ----------------------------------------

        void add_binary(literal l1, literal l2);
        void del_binary(unsigned idx);
        void validate_binary(literal l1, literal l2);

        // -------------------------------------
        // track consequences of binary clauses
        // see also 72 - 79 in sat11.w

        void inc_bstamp(); 
        void inc_istamp();
        void set_bstamp(literal l) { m_bstamp[l.index()] = m_bstamp_id; }
        void set_bstamps(literal l);
        bool is_stamped(literal l) const { return m_bstamp[l.index()] == m_bstamp_id; }
        bool add_tc1(literal u, literal v);

        /**
           \brief main routine for adding a new binary clause dynamically.
         */
        void try_add_binary(literal u, literal v);

        // -------------------------------------
        // pre-selection
        // see also 91 - 102 sat11.w

        void pre_select();

        struct candidate {
            bool_var m_var;
            double    m_rating;
            candidate(bool_var v, double r): m_var(v), m_rating(r) {}
        };
        svector<candidate> m_candidates;
        uint_set           m_select_lookahead_vars;

        double get_rating(bool_var v) const { return m_rating[v]; }
        double get_rating(literal l) const { return get_rating(l.var()); }
        bool select(unsigned level);
        void heap_sort();
        void heapify();        
        void sift_down(unsigned j, unsigned sz);
        bool validate_heap_sort();
        double init_candidates(unsigned level, bool newbies);
        std::ostream& display_candidates(std::ostream& out) const;
        bool is_unsat() const;
        bool is_sat() const;
        bool missed_propagation() const;
        bool missed_conflict() const;
        void init_pre_selection(unsigned level);
        void ensure_H(unsigned level);
        void h_scores(svector<double>& h, svector<double>& hp);
        void heule_schur_scores();
        double heule_schur_score(literal l);
        void heule_unit_scores();
        double heule_unit_score(literal l);
        void march_cu_scores();
        double march_cu_score(literal l);
        double l_score(literal l, svector<double> const& h, double factor, double sqfactor, double afactor);

        // ------------------------------------       
        // Implication graph
        // Compute implication ordering and strongly connected components.
        // sat11.w 103 - 114.
        
        struct arcs : public literal_vector {}; 
        // Knuth uses a shared pool of fixed size for arcs.
        // Should it be useful we could use this approach too 
        // by changing the arcs abstraction and associated functions.

        struct dfs_info {
            unsigned m_rank;
            unsigned m_height;
            literal  m_parent;
            arcs     m_next;
            unsigned m_nextp;
            literal  m_link;
            literal  m_min;
            literal  m_vcomp;
            dfs_info() { reset(); }
            void reset() {
                m_rank = 0;
                m_height = 0;
                m_parent = null_literal;
                m_next.reset();
                m_link = null_literal;
                m_min = null_literal;
                m_vcomp = null_literal;
                m_nextp = 0;
            }
        };
        
        literal           m_active; 
        unsigned          m_rank; 
        unsigned          m_rank_max;
        literal           m_settled;
        vector<dfs_info>  m_dfs;
        
        void get_scc();
        void init_scc();
        void init_dfs_info(literal l);
        void init_arcs(literal l);
        void add_arc(literal u, literal v);
        bool has_arc(literal v) const { return m_dfs[v.index()].m_next.size() > m_dfs[v.index()].m_nextp; } 
        arcs get_arcs(literal v) const { return m_dfs[v.index()].m_next; }
        literal pop_arc(literal u) { return m_dfs[u.index()].m_next[m_dfs[u.index()].m_nextp++]; }
        unsigned num_next(literal u) const { return m_dfs[u.index()].m_next.size(); }
        literal get_next(literal u, unsigned i) const { return m_dfs[u.index()].m_next[i]; }
        literal get_min(literal v) const { return m_dfs[v.index()].m_min; }
        unsigned get_rank(literal v) const { return m_dfs[v.index()].m_rank; }
        bool     maxed_rank(literal v) const { return get_rank(v) >= m_rank_max; }
        unsigned get_height(literal v) const { return m_dfs[v.index()].m_height; }
        literal get_parent(literal u) const { return m_dfs[u.index()].m_parent; }
        literal get_link(literal u) const { return m_dfs[u.index()].m_link; }
        literal get_vcomp(literal u) const { return m_dfs[u.index()].m_vcomp; }
        void set_link(literal v, literal u) { m_dfs[v.index()].m_link = u; }
        void set_min(literal v, literal u) { m_dfs[v.index()].m_min = u; }
        void set_rank(literal v, unsigned r) { m_dfs[v.index()].m_rank = r; }
        void set_height(literal v, unsigned h) { m_dfs[v.index()].m_height = h; }
        void set_parent(literal v, literal p) { TRACE("scc", tout << v << " <- " << p << "\n";); m_dfs[v.index()].m_parent = p; }
        void set_vcomp(literal v, literal u) { m_dfs[v.index()].m_vcomp = u; }
        void get_scc(literal v);
        void activate_scc(literal l);
        void found_scc(literal v);
        std::ostream& display_dfs(std::ostream& out) const;
        std::ostream& display_dfs(std::ostream& out, literal l) const;
        std::ostream& display_scc(std::ostream& out) const;
        std::ostream& display_scc(std::ostream& out, literal l) const;


        // ------------------------------------
        // lookahead forest
        // sat11.w 115-121

        literal m_root_child;

        literal get_child(literal u) const;
        void set_child(literal v, literal u);
        void find_heights();
        std::ostream& display_forest(std::ostream& out, literal l);

        struct literal_offset {
            literal  m_lit;
            unsigned m_offset;
            literal_offset(literal l): m_lit(l), m_offset(0) {}
        };
        svector<literal_offset> m_lookahead;
        void set_offset(unsigned idx, unsigned offset) { m_lookahead[idx].m_offset = offset; }
        void set_lookahead(literal l) { m_lookahead.push_back(literal_offset(l)); }
        void construct_lookahead_table();

        // ------------------------------------
        // clause management

        watch_list& get_wlist(literal l) { return m_watches[l.index()]; }
        watch_list const& get_wlist(literal l) const { return m_watches[l.index()]; }

        // new clause managment:
        void add_ternary(literal u, literal v, literal w);
        void propagate_ternary(literal l);
        lbool propagate_ternary(literal l1, literal l2);
        void remove_ternary(literal l, literal u, literal v);
        void restore_ternary(literal l);

        void propagate_external(literal l);
        void add_clause(clause const& c);
        void propagate_clauses_searching(literal l);
        void propagate_clauses_lookahead(literal l);
        void restore_clauses(literal l);
        void remove_clause(literal l, nary& n);
        void remove_clause_at(literal l, nary& n);
        // ------------------------------------
        // initialization
        
        void init_var(bool_var v);
        void init(bool learned);
        void copy_clauses(clause_vector const& clauses, bool learned);
        nary * copy_clause(clause const& c);

        // ------------------------------------
        // search
        
        void push(literal lit, unsigned level);
        void pop();
        bool push_lookahead2(literal lit, unsigned level);
        unsigned push_lookahead1(literal lit, unsigned level);
        void pop_lookahead1(literal lit, unsigned num_units);
        void lookahead_backtrack();
        double mix_diff(double l, double r) const;
        clause const& get_clause(watch_list::iterator it) const;
        bool is_nary_propagation(clause const& c, literal l) const;
        void propagate_clauses(literal l);
        void propagate_binary(literal l);
        void propagate();
        literal choose();
        void compute_lookahead_reward();
        literal select_literal();
        void update_binary_clause_reward(literal l1, literal l2);
        void update_nary_clause_reward(clause const& c);
 
        void set_lookahead_reward(literal l, double f) { m_lits[l.index()].m_lookahead_reward = f; }
        void inc_lookahead_reward(literal l, double f) { m_lits[l.index()].m_lookahead_reward += f; }
        double get_lookahead_reward(literal l) const { return m_lits[l.index()].m_lookahead_reward; }
            
        void reset_lookahead_reward(literal l);
        void update_lookahead_reward(literal l, unsigned level);
        bool dl_enabled(literal l) const { return m_lits[l.index()].m_double_lookahead != m_istamp_id; }
        void dl_disable(literal l) { m_lits[l.index()].m_double_lookahead = m_istamp_id; }
        bool dl_no_overflow(unsigned base) const { return base + 2 * m_lookahead.size() * static_cast<uint64_t>(m_config.m_dl_max_iterations + 1) < c_fixed_truth; }

        unsigned do_double(literal l, unsigned& base);
        unsigned double_look(literal l, unsigned& base);
        void set_conflict() { TRACE("sat", tout << "conflict\n";); m_inconsistent = true; }
        bool inconsistent() const { return m_inconsistent; }

        unsigned scope_lvl() const { return m_trail_lim.size(); }

        bool in_reduced_clause(literal l);
        bool in_reduced_clause(bool_var v);
        void validate_assign(literal l);
        void assign(literal l);
        void propagated(literal l);
        bool backtrack(literal_vector& trail);
        bool backtrack(literal_vector& trail, svector<bool> & is_decision);
        lbool search();
        void init_model();
        std::ostream& display_binary(std::ostream& out) const;
        std::ostream& display_clauses(std::ostream& out) const;
        std::ostream& display_values(std::ostream& out) const;
        std::ostream& display_lookahead(std::ostream& out) const;
        std::ostream& display_cube(std::ostream& out, literal_vector const& cube) const;
        void display_search_string();

        void init_search();
        void checkpoint();

        void init_config();

        void normalize_parents();

        void add_hyper_binary();

        double psat_heur();

        bool should_cutoff(unsigned depth);

    public:
        lookahead(solver& s) : 
            m_s(s),
            m_num_vars(s.num_vars()),
            m_drat(s),
            m_num_tc1(0),
            m_level(2),
            m_last_prefix_length(0),
            m_prefix(0),
            m_rating_throttle(0) {
            m_s.rlimit().push_child(&m_rlimit);
            init_config();
        }

        ~lookahead() {
            m_s.rlimit().pop_child();
            for (nary* n : m_nary_clauses) { 
                m_allocator.deallocate(n->obj_size(), n);
            }
        }
        

        lbool check() {
            init_search();
            return search();
        }

        /**
           \brief create cubes to std-out in DIMACS form.
           The cubes are controlled using cut-depth and cut-fraction parameters.
           If cut-depth != 0, then it is used to control thedepth of cuts.
           Otherwise, cut-fraction gives an adaptive threshold for creating cuts.
        */

        lbool cube(bool_var_vector& vars, literal_vector& lits, unsigned backtrack_level);

        void update_cube_statistics(statistics& st);

        /**
           \brief simplify set of clauses by extracting units from a lookahead at base level.
         */
        void simplify(bool learned);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_summary(std::ostream& out) const;
        model const& get_model();

        void collect_statistics(statistics& st) const;

        double literal_occs(literal l);
        double literal_big_occs(literal l);

        sat::config const& get_config() const { return m_s.get_config(); }
              
    };
}

#endif

