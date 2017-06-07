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

#include "sat_elim_eqs.h"

namespace sat {

    struct pp_prefix {
        uint64 m_prefix;
        unsigned m_depth;
        pp_prefix(uint64 p, unsigned d) : m_prefix(p), m_depth(d) {}
    };
    
    inline std::ostream& operator<<(std::ostream& out, pp_prefix const& p) {
        uint64 q = p.m_prefix;
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

    class lookahead {
        solver&    m_s;
        unsigned   m_num_vars;
        reslimit   m_rlimit;

        friend class ccc;
        friend class card_extension;

        struct config {
            double   m_dl_success;
            float    m_alpha;
            float    m_max_score;
            unsigned m_max_hlevel; 
            unsigned m_min_cutoff;
            unsigned m_level_cand;
            float    m_delta_rho;
            unsigned m_dl_max_iterations;
            unsigned m_tc1_limit;

            config() {
                m_max_hlevel = 50;
                m_alpha = 3.5;
                m_max_score = 20.0;
                m_min_cutoff = 30;
                m_level_cand = 600;
                m_delta_rho = (float)0.9995;
                m_dl_max_iterations = 32;
                m_tc1_limit = 10000000;
            }
        };

        struct prefix {
            unsigned m_prefix;
            unsigned m_length;
            prefix(): m_prefix(0), m_length(0) {}            
        };

        struct lit_info {
            float     m_wnb;
            unsigned  m_double_lookahead;
            lit_info(): m_wnb(0), m_double_lookahead(0) {}
        };

        struct stats {
            unsigned m_propagations;
            unsigned m_add_binary;
            unsigned m_del_binary;
            unsigned m_add_ternary;
            unsigned m_del_ternary;
            unsigned m_decisions;
            unsigned m_windfall_binaries;
            unsigned m_autarky_propagations;
            unsigned m_autarky_equivalences;
            unsigned m_double_lookahead_propagations;
            unsigned m_double_lookahead_rounds;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        struct ternary {
            ternary(literal u, literal v, literal w): m_u(u), m_v(v), m_w(w) {}
            literal m_u, m_v, m_w;
        };

        config                 m_config;
        double                 m_delta_trigger; 

        drat                   m_drat;
        literal_vector         m_assumptions;

        literal_vector         m_trail;         // trail of units
        unsigned_vector        m_trail_lim;
        vector<literal_vector> m_binary;        // literal: binary clauses
        unsigned_vector        m_binary_trail;  // trail of added binary clauses
        unsigned_vector        m_binary_trail_lim; 
        unsigned               m_num_tc1;
        unsigned_vector        m_num_tc1_lim;
        unsigned               m_qhead;         // propagation queue head
        unsigned_vector        m_qhead_lim;
        clause_vector          m_clauses;       // non-binary clauses
        clause_vector          m_retired_clauses; // clauses that were removed during search
        unsigned_vector        m_retired_clause_lim; 
        svector<ternary>       m_retired_ternary;  // ternary removed during search
        unsigned_vector        m_retired_ternary_lim; 
        clause_allocator       m_cls_allocator;        
        bool                   m_inconsistent;
        unsigned_vector        m_bstamp;        // literal: timestamp for binary implication
        vector<svector<float> >  m_H;           // literal: fitness score
        svector<float>*        m_heur;          // current fitness 
        svector<float>         m_rating;        // var:     pre-selection rating
        unsigned               m_bstamp_id;     // unique id for binary implication.
        unsigned               m_istamp_id;     // unique id for managing double lookaheads
        unsigned_vector        m_stamp;         // var: timestamp with truth value        
        unsigned               m_level;         // current level, = 2 * m_trail_lim.size() 
        const unsigned         c_fixed_truth = UINT_MAX - 1;
        vector<watch_list>     m_watches;       // literal: watch structure
        svector<lit_info>      m_lits;          // literal: attributes.
        vector<clause_vector>  m_full_watches;  // literal: full watch list, used to ensure that autarky reduction is sound
        float                  m_weighted_new_binaries; // metric associated with current lookahead1 literal.
        literal_vector         m_wstack;        // windofall stack that is populated in lookahead1 mode
        uint64                 m_prefix;        // where we are in search tree
        svector<prefix>        m_vprefix;       // var:     prefix where variable participates in propagation
        indexed_uint_set       m_freevars;
        lookahead_mode         m_search_mode;   // mode of search
        stats                  m_stats;
        model                  m_model; 
 
        // ---------------------------------------
        // truth values

        inline bool is_fixed(literal l) const { return m_stamp[l.var()] >= m_level; }
        inline bool is_undef(literal l) const { return !is_fixed(l); }
        inline bool is_undef(bool_var v) const { return m_stamp[v] < m_level; }
        inline bool is_false(literal l)  const { return is_fixed(l) && (bool)((m_stamp[l.var()] & 0x1) ^ l.sign()); } // even iff l.sign()
        inline bool is_true(literal l)   const { return is_fixed(l) && !(bool)((m_stamp[l.var()] & 0x1) ^ l.sign()); }
        inline void set_true(literal l) { m_stamp[l.var()] = m_level + l.sign(); }
        inline void set_undef(literal l) { m_stamp[l.var()] = 0; }
        void set_level(literal d, literal s) { m_stamp[d.var()] = (m_stamp[s.var()] & ~0x1) + d.sign(); }
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
            float    m_rating;
            candidate(bool_var v, float r): m_var(v), m_rating(r) {}
        };
        svector<candidate> m_candidates;
        uint_set           m_select_lookahead_vars;

        float get_rating(bool_var v) const { return m_rating[v]; }
        float get_rating(literal l) const { return get_rating(l.var()); }
        bool select(unsigned level);
        void sift_up(unsigned j);
        float init_candidates(unsigned level, bool newbies);
        std::ostream& display_candidates(std::ostream& out) const;
        bool is_unsat() const;
        bool is_sat() const;
        void init_pre_selection(unsigned level);
        void ensure_H(unsigned level);
        void h_scores(svector<float>& h, svector<float>& hp);
        float l_score(literal l, svector<float> const& h, float factor, float sqfactor, float afactor);

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
        literal           m_settled;
        vector<dfs_info>  m_dfs;
        
        void get_scc();
        void init_scc();
        void init_dfs_info(literal l);
        void init_arcs(literal l);
        void add_arc(literal u, literal v) { m_dfs[u.index()].m_next.push_back(v); }
        bool has_arc(literal v) const { return m_dfs[v.index()].m_next.size() > m_dfs[v.index()].m_nextp; } 
        arcs get_arcs(literal v) const { return m_dfs[v.index()].m_next; }
        literal pop_arc(literal u) { return m_dfs[u.index()].m_next[m_dfs[u.index()].m_nextp++]; }
        unsigned num_next(literal u) const { return m_dfs[u.index()].m_next.size(); }
        literal get_next(literal u, unsigned i) const { return m_dfs[u.index()].m_next[i]; }
        literal get_min(literal v) const { return m_dfs[v.index()].m_min; }
        unsigned get_rank(literal v) const { return m_dfs[v.index()].m_rank; }
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

        void attach_clause(clause& c);
        void detach_clause(clause& c);
        void del_clauses();
        void detach_ternary(literal l1, literal l2, literal l3);
        void attach_ternary(ternary const& t);
        void attach_ternary(literal l1, literal l2, literal l3);
        watch_list& get_wlist(literal l) { return m_watches[l.index()]; }

        // ------------------------------------
        // initialization
        
        void init_var(bool_var v);
        void init();
        void copy_clauses(clause_vector const& clauses);

        // ------------------------------------
        // search
        
        void push(literal lit, unsigned level);
        void pop();
        bool push_lookahead2(literal lit, unsigned level);
        void push_lookahead1(literal lit, unsigned level);
        void pop_lookahead1(literal lit);
        float mix_diff(float l, float r) const { return l + r + (1 << 10) * l * r; }
        clause const& get_clause(watch_list::iterator it) const;
        bool is_nary_propagation(clause const& c, literal l) const;
        void propagate_clauses(literal l);
        void propagate_binary(literal l);
        void propagate();
        literal choose();
        void compute_wnb();
        void init_wnb();
        void reset_wnb();
        literal select_literal();

        void set_wnb(literal l, float f) { m_lits[l.index()].m_wnb = f; }
        void inc_wnb(literal l, float f) { m_lits[l.index()].m_wnb += f; }
        float get_wnb(literal l) const { return m_lits[l.index()].m_wnb; }
            
        void reset_wnb(literal l);
        bool check_autarky(literal l, unsigned level);
        void update_wnb(literal l, unsigned level);
        bool dl_enabled(literal l) const { return m_lits[l.index()].m_double_lookahead != m_istamp_id; }
        void dl_disable(literal l) { m_lits[l.index()].m_double_lookahead = m_istamp_id; }
        bool dl_no_overflow(unsigned base) const { return base + 2 * m_lookahead.size() * static_cast<uint64>(m_config.m_dl_max_iterations + 1) < c_fixed_truth; }

        bool is_fixed_at(literal lit, unsigned level) const {
            return is_fixed(lit) && (!is_false(lit) || m_stamp[lit.var()] >= level);
        }

        void do_double(literal l, unsigned& base);
        void double_look(literal l, unsigned& base);
        void set_conflict() { TRACE("sat", tout << "conflict\n";); m_inconsistent = true; }
        bool inconsistent() { return m_inconsistent; }

        unsigned scope_lvl() const { return m_trail_lim.size(); }

        void validate_assign(literal l);
        void assign(literal l);
        void propagated(literal l);
        bool backtrack(literal_vector& trail);
        lbool search();
        void init_model();
        std::ostream& display_binary(std::ostream& out) const;
        std::ostream& display_clauses(std::ostream& out) const;
        std::ostream& display_values(std::ostream& out) const;
        std::ostream& display_lookahead(std::ostream& out) const;
        void init_search();
        void checkpoint();

    public:
        lookahead(solver& s) : 
            m_s(s),
            m_num_vars(s.num_vars()),
            m_drat(s),
            m_num_tc1(0),
            m_level(2),
            m_prefix(0) {
            m_s.rlimit().push_child(&m_rlimit);
        }

        ~lookahead() {
            del_clauses();
            m_s.rlimit().pop_child();
        }
        

        lbool check() {
            init_search();
            return search();
        }

        literal select_lookahead(bool_var_vector const& vars) {
            scoped_ext _sext(*this);
            m_search_mode = lookahead_mode::searching;
            scoped_level _sl(*this, c_fixed_truth);
            init();                
            if (inconsistent()) return null_literal;
            inc_istamp();            
            for (auto v : vars) {
                m_select_lookahead_vars.insert(v);
            }
            literal l = choose();
            m_select_lookahead_vars.reset();
            if (inconsistent()) return null_literal;

            // assign unit literals that were found during search for lookahead.
            unsigned num_assigned = 0;
            for (literal lit : m_trail) {
                if (!m_s.was_eliminated(lit.var()) && m_s.value(lit) != l_true) {
                    m_s.assign(lit, justification());
                    ++num_assigned;
                }
            }
            IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :units " << num_assigned << ")\n";);
            return l;
        }

        /**
           \brief simplify set of clauses by extracting units from a lookahead at base level.
         */
        void simplify() {
            SASSERT(m_prefix == 0);
            SASSERT(m_watches.empty());
            m_search_mode = lookahead_mode::searching;
            scoped_level _sl(*this, c_fixed_truth);
            init();                
            if (inconsistent()) return;
            inc_istamp();            
            literal l = choose();
            if (inconsistent()) return;
            SASSERT(m_trail_lim.empty());
            unsigned num_units = 0;
            for (unsigned i = 0; i < m_trail.size(); ++i) {
                literal lit = m_trail[i];
                if (m_s.value(lit) == l_undef && !m_s.was_eliminated(lit.var())) {
                    m_s.m_simplifier.propagate_unit(lit);                    
                    ++num_units;
                }
            }
            IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :units " << num_units << ")\n";);
            
            m_s.m_simplifier.subsume();
            m_lookahead.reset();
        }

        //
        // there can be two sets of equivalence classes.
        // example:
        // a -> !b
        // b -> !a
        // c -> !a
        // we pick as root the Boolean variable with the largest value.
        // 
        literal get_root(bool_var v) {
            literal lit(v, false);
            literal r1 = get_parent(lit);
            literal r2 = get_parent(literal(r1.var(), false));
            CTRACE("sat", r1 != get_parent(literal(r2.var(), false)), 
                   tout << r1 << " " << r2 << "\n";);
            SASSERT(r1.var() == get_parent(literal(r2.var(), false)).var());
            if (r1.var() >= r2.var()) {
                return r1;
            }
            else {
                return r1.sign() ? ~r2 : r2;
            }
        }

        /**
           \brief extract equivalence classes of variables and simplify clauses using these.
        */
        void scc() {
            SASSERT(m_prefix == 0);
            SASSERT(m_watches.empty());
            m_search_mode = lookahead_mode::searching;
            scoped_level _sl(*this, c_fixed_truth);
            init();                
            if (inconsistent()) return;
            inc_istamp();
            m_lookahead.reset();
            if (select(0)) {
                // extract equivalences
                get_scc();
                if (inconsistent()) return;
                literal_vector roots;
                bool_var_vector to_elim;
                for (unsigned i = 0; i < m_num_vars; ++i) {
                    roots.push_back(literal(i, false));
                }
                for (unsigned i = 0; i < m_candidates.size(); ++i) {
                    bool_var v = m_candidates[i].m_var;
                    literal p = get_root(v);
                    if (p != null_literal && p.var() != v && !m_s.is_external(v) && 
                        !m_s.was_eliminated(v) && !m_s.was_eliminated(p.var())) {
                        to_elim.push_back(v);
                        roots[v] = p;
                        SASSERT(get_parent(p) == p);
                        set_parent(~p, ~p);
                        SASSERT(get_parent(~p) == ~p);
                    }
                }
                IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :equivalences " << to_elim.size() << ")\n";);
                elim_eqs elim(m_s);
                elim(roots, to_elim);
            }
            m_lookahead.reset();
        }

        std::ostream& display(std::ostream& out) const {
            out << "Prefix: " << pp_prefix(m_prefix, m_trail_lim.size()) << "\n";
            out << "Level: " << m_level << "\n";
            display_values(out);
            display_binary(out);
            display_clauses(out);
            out << "free vars: ";
            for (bool_var const* it = m_freevars.begin(), * end = m_freevars.end(); it != end; ++it) {
                out << *it << " ";
            }
            out << "\n";
            for (unsigned i = 0; i < m_watches.size(); ++i) {
                watch_list const& wl = m_watches[i];
                if (!wl.empty()) {
                    sat::display_watch_list(out << to_literal(i) << " -> ", m_cls_allocator, wl);
                    out << "\n";
                }
            }
            return out;
        }

        model const& get_model() {
            if (m_model.empty()) {
                init_model();
            }
            return m_model;
        }

        void collect_statistics(statistics& st) const {
            st.update("lh bool var", m_vprefix.size());
            st.update("lh clauses",  m_clauses.size());
            st.update("lh add binary", m_stats.m_add_binary);
            st.update("lh del binary", m_stats.m_del_binary);
            st.update("lh add ternary", m_stats.m_add_ternary);
            st.update("lh del ternary", m_stats.m_del_ternary);
            st.update("lh propagations", m_stats.m_propagations);
            st.update("lh decisions", m_stats.m_decisions);
            st.update("lh windfalls", m_stats.m_windfall_binaries);
            st.update("lh autarky propagations", m_stats.m_autarky_propagations);
            st.update("lh autarky equivalences", m_stats.m_autarky_equivalences); 
            st.update("lh double lookahead propagations", m_stats.m_double_lookahead_propagations);
            st.update("lh double lookahead rounds", m_stats.m_double_lookahead_rounds);
        }
              
    };
}

#endif

