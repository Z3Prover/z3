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

        // -------------------------------------
        // prefix updates. I use low order bits.
        
        void flip_prefix() {
            if (m_trail_lim.size() < 64) {
                uint64 mask = (1ull << m_trail_lim.size());
                m_prefix = mask | (m_prefix & (mask - 1));
            }
        }

        void prune_prefix() {
            if (m_trail_lim.size() < 64) {
                m_prefix &= (1ull << m_trail_lim.size()) - 1;
            }
        }

        /**
           length < trail_lim.size:
           - mask m_prefix and p wrt length
           - update if different.
         */
        void update_prefix(literal l) {
            bool_var x = l.var();
            unsigned p = m_vprefix[x].m_prefix;
            unsigned pl = m_vprefix[x].m_length;
            unsigned mask = (1 << std::min(31u, pl)) - 1; 
            if (pl >= m_trail_lim.size() || (p & mask) != (m_prefix & mask)) {
                m_vprefix[x].m_length = m_trail_lim.size();
                m_vprefix[x].m_prefix = static_cast<unsigned>(m_prefix);
            }
        }

        bool active_prefix(bool_var x) {
            unsigned lvl = m_trail_lim.size();
            unsigned p = m_vprefix[x].m_prefix;
            unsigned l = m_vprefix[x].m_length;
            if (l > lvl) return false;
            if (l == lvl || l >= 31) return m_prefix == p;
            unsigned mask = ((1 << std::min(l,31u)) - 1);
            return (m_prefix & mask) == (p & mask);
        }

        // ----------------------------------------

        void add_binary(literal l1, literal l2) {
            TRACE("sat", tout << "binary: " << l1 << " " << l2 << "\n";);
            SASSERT(l1 != l2);
            // don't add tautologies and don't add already added binaries
            if (~l1 == l2) return;
            if (!m_binary[(~l1).index()].empty() && m_binary[(~l1).index()].back() == l2) return;
            m_binary[(~l1).index()].push_back(l2);
            m_binary[(~l2).index()].push_back(l1);
            m_binary_trail.push_back((~l1).index());
            ++m_stats.m_add_binary;
            if (m_s.m_config.m_drat) validate_binary(l1, l2);
        }

        void del_binary(unsigned idx) {
            // TRACE("sat", display(tout << "Delete " << to_literal(idx) << "\n"););
            literal_vector & lits = m_binary[idx];
            SASSERT(!lits.empty());
            literal l = lits.back();			
            lits.pop_back();            
            SASSERT(!m_binary[(~l).index()].empty());
            IF_VERBOSE(0, if (m_binary[(~l).index()].back() != ~to_literal(idx)) verbose_stream() << "pop bad literal: " << idx << " " << (~l).index() << "\n";);
            SASSERT(m_binary[(~l).index()].back() == ~to_literal(idx));
            m_binary[(~l).index()].pop_back();
            ++m_stats.m_del_binary;
        }

        void validate_binary(literal l1, literal l2) {
            if (m_search_mode == lookahead_mode::searching) {
                m_assumptions.push_back(l1);
                m_assumptions.push_back(l2);
                m_drat.add(m_assumptions);
                m_assumptions.pop_back();
                m_assumptions.pop_back();
            }
        }

        // -------------------------------------
        // track consequences of binary clauses
        // see also 72 - 79 in sat11.w

        void inc_bstamp() {
            ++m_bstamp_id;
            if (m_bstamp_id == 0) {
                ++m_bstamp_id;
                m_bstamp.fill(0);
            }
        }
        void inc_istamp() {
            ++m_istamp_id;
            if (m_istamp_id == 0) {
                ++m_istamp_id;
                for (unsigned i = 0; i < m_lits.size(); ++i) {
                    m_lits[i].m_double_lookahead = 0;
                }
            }
        }
        void set_bstamp(literal l) {
            m_bstamp[l.index()] = m_bstamp_id;
        }
        void set_bstamps(literal l) {
            inc_bstamp();
            set_bstamp(l);
            literal_vector const& conseq = m_binary[l.index()];
            literal_vector::const_iterator it = conseq.begin(); 
            literal_vector::const_iterator end = conseq.end();
            for (; it != end; ++it) {
                set_bstamp(*it);
            }
        }
        bool is_stamped(literal l) const { return m_bstamp[l.index()] == m_bstamp_id; }

        /**
           \brief add one-step transitive closure of binary implications
                  return false if we learn a unit literal.
           \pre all implicants of ~u are stamped.
                u \/ v is true
        **/

        bool add_tc1(literal u, literal v) {
            unsigned sz = m_binary[v.index()].size();
            for (unsigned i = 0; i < sz; ++i) {
                literal w = m_binary[v.index()][i];
                // ~v \/ w
                if (!is_fixed(w)) {
                    if (is_stamped(~w)) {
                        // u \/ v, ~v \/ w, u \/ ~w => u is unit
                        TRACE("sat", tout << "tc1: " << u << "\n";);
                        assign(u);        
                        return false;
                    }
                    if (m_num_tc1 < m_config.m_tc1_limit) {
                        ++m_num_tc1;
                        IF_VERBOSE(3, verbose_stream() << "tc1: " << u << " " << w << "\n";);
                        add_binary(u, w);
                    }
                }
            }
            return true;
        }

        /**
           \brief main routine for adding a new binary clause dynamically.
         */
        void try_add_binary(literal u, literal v) {
            SASSERT(m_search_mode == lookahead_mode::searching);
            SASSERT(u.var() != v.var());
            if (!is_undef(u) || !is_undef(v)) {
                IF_VERBOSE(0, verbose_stream() << "adding assigned binary " << v << " " << u << "\n";);
            }
            set_bstamps(~u);
            if (is_stamped(~v)) {         
                TRACE("sat", tout << "try_add_binary: " << u << "\n";);       
                assign(u);        // u \/ ~v, u \/ v => u is a unit literal
            }
            else if (!is_stamped(v) && add_tc1(u, v)) {
                // u \/ v is not in index
                set_bstamps(~v);
                if (is_stamped(~u)) {
                    TRACE("sat", tout << "try_add_binary: " << v << "\n";);       
                    assign(v);    // v \/ ~u, u \/ v => v is a unit literal
                }
                else if (add_tc1(v, u)) {
                    update_prefix(u);
                    update_prefix(v);
                    add_binary(u, v);
                }
            }
        }

        // -------------------------------------
        // pre-selection
        // see also 91 - 102 sat11.w

        void pre_select() {
            m_lookahead.reset();
            if (select(scope_lvl())) {
                get_scc();
                if (inconsistent()) return;
                find_heights();
                construct_lookahead_table();
            }
        }

        struct candidate {
            bool_var m_var;
            float    m_rating;
            candidate(bool_var v, float r): m_var(v), m_rating(r) {}
        };
        svector<candidate> m_candidates;

        float get_rating(bool_var v) const { return m_rating[v]; }
        float get_rating(literal l) const { return get_rating(l.var()); }

        bool select(unsigned level) {
            init_pre_selection(level);
            unsigned level_cand = std::max(m_config.m_level_cand, m_freevars.size() / 50);
            unsigned max_num_cand = level == 0 ? m_freevars.size() : level_cand / level; 
            max_num_cand = std::max(m_config.m_min_cutoff, max_num_cand);

            float sum = 0;
            for (bool newbies = false; ; newbies = true) {
                sum = init_candidates(level, newbies);
                if (!m_candidates.empty()) break;
                if (is_sat()) {
                    return false;
                }         
                if (newbies) {
                    enable_trace("sat");
                    TRACE("sat", display(tout););
                    TRACE("sat", tout << sum << "\n";);
                }
            }
            SASSERT(!m_candidates.empty());
            // cut number of candidates down to max_num_cand.
            // step 1. cut it to at most 2*max_num_cand.
            // step 2. use a heap to sift through the rest.
            bool progress = true;
            while (progress && m_candidates.size() >= max_num_cand * 2) {
                progress = false;
                float mean = sum / (float)(m_candidates.size() + 0.0001);
                sum = 0;
                for (unsigned i = 0; i < m_candidates.size() && m_candidates.size() >= max_num_cand * 2; ++i) {
                    if (m_candidates[i].m_rating >= mean) {
                        sum += m_candidates[i].m_rating;
                    }
                    else {
                        m_candidates[i] = m_candidates.back();
                        m_candidates.pop_back();
                        --i;
                        progress = true;
                    }
                }                
            }
            TRACE("sat", display_candidates(tout););
            SASSERT(!m_candidates.empty());
            if (m_candidates.size() > max_num_cand) {
                unsigned j = m_candidates.size()/2;
                while (j > 0) {
                    --j;
                    sift_up(j);
                }
                while (true) {
                    m_candidates[0] = m_candidates.back();
                    m_candidates.pop_back();
                    if (m_candidates.size() == max_num_cand) break;
                    sift_up(0);
                }
            }
            SASSERT(!m_candidates.empty() && m_candidates.size() <= max_num_cand);
            TRACE("sat", display_candidates(tout););
            return true;
        }

        void sift_up(unsigned j) {
            unsigned i = j;
            candidate c = m_candidates[j];
            for (unsigned k = 2*j + 1; k < m_candidates.size(); i = k, k = 2*k + 1) {
                // pick largest parent
                if (k + 1 < m_candidates.size() && m_candidates[k].m_rating < m_candidates[k+1].m_rating) {
                    ++k;
                }
                if (c.m_rating <= m_candidates[k].m_rating) break;
                m_candidates[i] = m_candidates[k];
            }
            if (i > j) m_candidates[i] = c;
        }

        float init_candidates(unsigned level, bool newbies) {
            m_candidates.reset();
            float sum = 0;
            for (bool_var const* it = m_freevars.begin(), * end = m_freevars.end(); it != end; ++it) {
                SASSERT(is_undef(*it));
                bool_var x = *it;
                if (newbies || active_prefix(x)) {
                    m_candidates.push_back(candidate(x, m_rating[x]));
                    sum += m_rating[x];                
                }           
            } 
            TRACE("sat", display_candidates(tout << "sum: " << sum << "\n"););
            return sum;
        }

        std::ostream& display_candidates(std::ostream& out) const {
            for (unsigned i = 0; i < m_candidates.size(); ++i) {
                out << "var: " << m_candidates[i].m_var << " rating: " << m_candidates[i].m_rating << "\n";
            }          
            return out;
        }

        bool is_unsat() const {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                clause& c = *m_clauses[i];
                unsigned j = 0;
                for (; j < c.size() && is_false(c[j]); ++j) {}
                if (j == c.size()) {
                    TRACE("sat", tout << c << "\n";);
                    TRACE("sat", display(tout););
                    return true;
                }
            }
            return false;
        }

        bool is_sat() const {
            for (bool_var const* it = m_freevars.begin(), * end = m_freevars.end(); it != end; ++it) {
                literal l(*it, false);
                literal_vector const& lits1 = m_binary[l.index()];
                for (unsigned i = 0; i < lits1.size(); ++i) {
                    if (!is_true(lits1[i])) {
                        TRACE("sat", tout << l << " " << lits1[i] << "\n";);
                        return false;
                    }
                }
                l.neg();
                literal_vector const& lits2 = m_binary[l.index()];
                for (unsigned i = 0; i < lits2.size(); ++i) {
                    if (!is_true(lits2[i])) {
                        TRACE("sat", tout << l << " " << lits2[i] << "\n";);
                        return false;
                    }
                }
            }
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                clause& c = *m_clauses[i];
                unsigned j = 0;
                for (; j < c.size() && !is_true(c[j]); ++j) {}
                if (j == c.size()) {
                    return false;
                }
            }
            return true;
        }

        void init_pre_selection(unsigned level) {
            unsigned max_level = m_config.m_max_hlevel;
            if (level <= 1) {
                ensure_H(2);
                h_scores(m_H[0], m_H[1]);
                for (unsigned j = 0; j < 2; ++j) {
                    for (unsigned i = 0; i < 2; ++i) {
                        h_scores(m_H[i + 1], m_H[(i + 2) % 3]);
                    }
                }
                m_heur = &m_H[1];
            }
            else if (level < max_level) {
                ensure_H(level);
                h_scores(m_H[level-1], m_H[level]);
                m_heur = &m_H[level];
            }
            else {
                ensure_H(max_level);
                h_scores(m_H[max_level-1], m_H[max_level]);
                m_heur = &m_H[max_level];
            }
        }

        void ensure_H(unsigned level) {
            while (m_H.size() <= level) {
                m_H.push_back(svector<float>());
                m_H.back().resize(m_num_vars * 2, 0);
            }
        }

        void h_scores(svector<float>& h, svector<float>& hp) {
            float sum = 0;
            for (bool_var const* it = m_freevars.begin(), * end = m_freevars.end(); it != end; ++it) {
                literal l(*it, false);
                sum += h[l.index()] + h[(~l).index()];
            }
            float factor = 2 * m_freevars.size() / sum;
            float sqfactor = factor * factor;
            float afactor = factor * m_config.m_alpha;
            for (bool_var const* it = m_freevars.begin(), * end = m_freevars.end(); it != end; ++it) {
                literal l(*it, false);
                float pos = l_score(l,  h, factor, sqfactor, afactor);
                float neg = l_score(~l, h, factor, sqfactor, afactor);
                hp[l.index()] = pos;
                hp[(~l).index()] = neg;
                m_rating[l.var()] = pos * neg;
            }
        }

        float l_score(literal l, svector<float> const& h, float factor, float sqfactor, float afactor) {
            float sum = 0, tsum = 0;
            literal_vector::iterator it = m_binary[l.index()].begin(), end = m_binary[l.index()].end();
            for (; it != end; ++it) {
                bool_var v = it->var();
                if (it->index() >= h.size())
                    IF_VERBOSE(0, verbose_stream() << l << " " << *it << " " << h.size() << "\n";);
                if (is_undef(*it)) sum += h[it->index()]; 
                // if (m_freevars.contains(it->var())) sum += h[it->index()]; 
            }
            watch_list& wlist = m_watches[l.index()];
            watch_list::iterator wit = wlist.begin(), wend = wlist.end();
            for (; wit != wend; ++wit) {
                switch (wit->get_kind()) {
                case watched::BINARY: 
                    UNREACHABLE(); 
                    break;
                case watched::TERNARY: {
                    literal l1 = wit->get_literal1();
                    literal l2 = wit->get_literal2();
                    // if (is_undef(l1) && is_undef(l2)) 
                    tsum += h[l1.index()] * h[l2.index()]; 
                    break;
                }
                case watched::CLAUSE: {
                    clause_offset cls_off = wit->get_clause_offset();
                    clause & c = *(m_cls_allocator.get_clause(cls_off));
                    // approximation compared to ternary clause case: 
                    // we pick two other literals from the clause.
                    if (c[0] == ~l) {
                        tsum += h[c[1].index()] * h[c[2].index()];
                    }
                    else {
                        SASSERT(c[1] == ~l);
                        tsum += h[c[0].index()] * h[c[2].index()];
                    }
                    break;
                }
                }
            }
            sum = (float)(0.1 + afactor*sum + sqfactor*tsum);
            return std::min(m_config.m_max_score, sum);
        }

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
        
        void get_scc() {
            unsigned num_candidates = m_candidates.size();
            init_scc();
            for (unsigned i = 0; i < num_candidates && !inconsistent(); ++i) {
                literal lit(m_candidates[i].m_var, false);
                if (get_rank(lit) == 0) get_scc(lit);
                if (get_rank(~lit) == 0) get_scc(~lit);
            }
            TRACE("sat", display_scc(tout););
        }
        void init_scc() {
            inc_bstamp();
            for (unsigned i = 0; i < m_candidates.size(); ++i) {
                literal lit(m_candidates[i].m_var, false);
                init_dfs_info(lit);
                init_dfs_info(~lit);
            }
            for (unsigned i = 0; i < m_candidates.size(); ++i) {
                literal lit(m_candidates[i].m_var, false);
                init_arcs(lit);
                init_arcs(~lit);
            }
            m_rank = 0; 
            m_active = null_literal;
            m_settled = null_literal;
            TRACE("sat", display_dfs(tout););
        }
        void init_dfs_info(literal l) {
            unsigned idx = l.index();
            m_dfs[idx].reset();
            set_bstamp(l);
        }
        // arcs are added in the opposite direction of implications.
        // So for implications l => u we add arcs u -> l
        void init_arcs(literal l) {
            literal_vector const& succ = m_binary[l.index()];
            for (unsigned i = 0; i < succ.size(); ++i) {
                literal u = succ[i];
                SASSERT(u != l);
                if (u.index() > l.index() && is_stamped(u)) {
                    add_arc(~l, ~u);
                    add_arc( u,  l);
                }
            }
        }
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
        void get_scc(literal v) {
            TRACE("scc", tout << v << "\n";);
            set_parent(v, null_literal);
            activate_scc(v);
            do {
                literal ll = get_min(v);
                if (has_arc(v)) {
                    literal u = pop_arc(v);
                    unsigned r = get_rank(u);
                    if (r > 0) {
                        // u was processed before ll                        
                        if (r < get_rank(ll)) set_min(v, u);
                    }
                    else {
                        // process u in dfs order, add v to dfs stack for u
                        set_parent(u, v);
                        v = u;
                        activate_scc(v);
                    }
                }
                else {
                    literal u = get_parent(v);
                    if (v == ll) {                        
                        found_scc(v);
                    }
                    else if (get_rank(ll) < get_rank(get_min(u))) {
                        set_min(u, ll);
                    }
                    // walk back in the dfs stack
                    v = u;
                }                
            }
            while (v != null_literal && !inconsistent());
        }
        void activate_scc(literal l) {
            SASSERT(get_rank(l) == 0);
            set_rank(l, ++m_rank);
            set_link(l, m_active);
            set_min(l, l);
            m_active = l;
        }
        // make v root of the scc equivalence class
        // set vcomp to be the highest rated literal
        void found_scc(literal v) {
            literal t = m_active; 
            m_active = get_link(v);
            literal best = v;
            float best_rating = get_rating(v);
            set_rank(v, UINT_MAX);
            set_link(v, m_settled); m_settled = t; 
            while (t != v) {
                if (t == ~v) {
                    TRACE("sat", display_scc(tout << "found contradiction during scc search\n"););
                    set_conflict();
                    break;
                }
                set_rank(t, UINT_MAX);
                set_parent(t, v);
                float t_rating = get_rating(t);
                if (t_rating > best_rating) {
                    best = t;
                    best_rating = t_rating;
                }
                t = get_link(t);
            }
            set_parent(v, v);
            set_vcomp(v, best);
            if (get_rank(~v) == UINT_MAX) {
                set_vcomp(v, ~get_vcomp(get_parent(~v)));
            }
        } 

        std::ostream& display_dfs(std::ostream& out) const {
            for (unsigned i = 0; i < m_candidates.size(); ++i) {
                literal l(m_candidates[i].m_var, false);
                display_dfs(out, l);
                display_dfs(out, ~l);
            }
            return out;
        }

        std::ostream& display_dfs(std::ostream& out, literal l) const {
            arcs const& a1 = get_arcs(l);
            if (!a1.empty()) {
                out << l << " -> " << a1 << "\n";
            }
            return out;
        }

        std::ostream& display_scc(std::ostream& out) const {
            display_dfs(out);
            for (unsigned i = 0; i < m_candidates.size(); ++i) {
                literal l(m_candidates[i].m_var, false);
                display_scc(out, l);
                display_scc(out, ~l);
            }
            return out;
        }

        std::ostream& display_scc(std::ostream& out, literal l) const {
            out << l << " := " << get_parent(l) 
                << " min: " << get_min(l) 
                << " rank: " << get_rank(l) 
                << " height: " << get_height(l) 
                << " link: " << get_link(l)
                << " child: " << get_child(l)
                << " vcomp: " << get_vcomp(l) << "\n";            
            return out;
        }


        // ------------------------------------
        // lookahead forest
        // sat11.w 115-121

        literal m_root_child;

        literal get_child(literal u) const { 
            if (u == null_literal) return m_root_child; 
            return m_dfs[u.index()].m_min; 
        }
        void set_child(literal v, literal u) { 
            if (v == null_literal) m_root_child = u; 
            else m_dfs[v.index()].m_min = u; 
        }

        /*
          \brief Assign heights to the nodes.
          Nodes within the same strongly connected component are given the same height.
          The code assumes that m_settled is topologically sorted such that
          1. nodes in the same equivalence class come together
          2. the equivalence class representative is last

        */
        void find_heights() {
            m_root_child = null_literal;
            literal pp = null_literal;
            unsigned h = 0;
            literal w, uu;
            TRACE("sat", 
                  for (literal u = m_settled; u != null_literal; u = get_link(u)) {
                      tout << u << " ";
                  }
                  tout << "\n";);
            for (literal u = m_settled; u != null_literal; u = uu) {
                TRACE("sat", tout << "process: " << u << "\n";);
                uu = get_link(u);
                literal p = get_parent(u);
                if (p != pp) { 
                    // new equivalence class
                    h = 0; 
                    w = null_literal; 
                    pp = p; 
                }
                // traverse nodes in order of implication
                unsigned sz = num_next(~u);
                for (unsigned j = 0; j < sz; ++j) {
                    literal v = ~get_next(~u, j);
                    TRACE("sat", tout << "child " << v << " link: " << get_link(v) << "\n";);
                    literal pv = get_parent(v);
                    // skip nodes in same equivalence, they will all be processed
                    if (pv == p) continue; 
                    unsigned hh = get_height(pv);
                    // update the maximal height descendant
                    if (hh >= h) {
                        h = hh + 1; 
                        w = pv;
                    }
                }
                if (p == u) { 
                    // u is an equivalence class representative
                    // it is processed last
                    literal v = get_child(w);
                    set_height(u, h);
                    set_child(u, null_literal);
                    set_link(u, v);
                    set_child(w, u);
                    TRACE("sat", tout << "child(" << w << ") = " << u << " link(" << u << ") = " << v << "\n";);
                }
            }
            TRACE("sat", 
                  display_forest(tout << "forest: ", get_child(null_literal));
                  tout << "\n";
                  display_scc(tout); );
        }
        std::ostream& display_forest(std::ostream& out, literal l) {
            for (literal u = l; u != null_literal; u = get_link(u)) {
                out << u << " ";
                l = get_child(u);
                if (l != null_literal) {
                    out << "(";
                    display_forest(out, l);
                    out << ") ";
                }
            }
            return out;
        }

        struct literal_offset {
            literal  m_lit;
            unsigned m_offset;
            literal_offset(literal l): m_lit(l), m_offset(0) {}
        };
        svector<literal_offset> m_lookahead;
        void set_offset(unsigned idx, unsigned offset) {
            m_lookahead[idx].m_offset = offset;
        }
        void set_lookahead(literal l) {
            m_lookahead.push_back(literal_offset(l));
        }
        void construct_lookahead_table() {
            literal u = get_child(null_literal), v = null_literal;
            unsigned offset = 0;
            SASSERT(m_lookahead.empty());
            while (u != null_literal) {  
                set_rank(u, m_lookahead.size());
                set_lookahead(get_vcomp(u));
                if (null_literal != get_child(u)) {
                    set_parent(u, v);
                    v = u;
                    u = get_child(u);
                }
                else {
                    while (true) {
                        set_offset(get_rank(u), offset);
                        offset += 2;
                        set_parent(u, v == null_literal ? v : get_vcomp(v));
                        u = get_link(u);
                        if (u == null_literal && v != null_literal) {
                            u = v;
                            v = get_parent(u);
                        }
                        else {
                            break;
                        }
                    }
                }
            }
            SASSERT(2*m_lookahead.size() == offset);
            TRACE("sat", for (unsigned i = 0; i < m_lookahead.size(); ++i) 
                             tout << m_lookahead[i].m_lit << " : " << m_lookahead[i].m_offset << "\n";);
        }

        // ------------------------------------
        // clause management

        void attach_clause(clause& c) {
            if (c.size() == 3) { 
                attach_ternary(c[0], c[1], c[2]);
            }
            else {
                literal block_lit = c[c.size() >> 2];
                clause_offset cls_off = m_cls_allocator.get_offset(&c);
                m_watches[(~c[0]).index()].push_back(watched(block_lit, cls_off));
                m_watches[(~c[1]).index()].push_back(watched(block_lit, cls_off));
                SASSERT(is_undef(c[0]));
                SASSERT(is_undef(c[1]));
            }
        }

        void detach_clause(clause& c) {
            clause_offset cls_off = m_cls_allocator.get_offset(&c);
            m_retired_clauses.push_back(&c);
            erase_clause_watch(get_wlist(~c[0]), cls_off);
            erase_clause_watch(get_wlist(~c[1]), cls_off);
        }

        void del_clauses() {
            clause * const* end = m_clauses.end();
            clause * const * it = m_clauses.begin();
            for (; it != end; ++it) {
                m_cls_allocator.del_clause(*it);
            }
        }

        void detach_ternary(literal l1, literal l2, literal l3) {
            ++m_stats.m_del_ternary;
            m_retired_ternary.push_back(ternary(l1, l2, l3));
            // implicitly erased: erase_ternary_watch(get_wlist(~l1), l2, l3);
            erase_ternary_watch(get_wlist(~l2), l1, l3);
            erase_ternary_watch(get_wlist(~l3), l1, l2);
        }

        void attach_ternary(ternary const& t) {
            attach_ternary(t.m_u, t.m_v, t.m_w);
        }

        void attach_ternary(literal l1, literal l2, literal l3) {
            ++m_stats.m_add_ternary;
            TRACE("sat", tout << l1 << " " << l2 << " " << l3 << "\n";);
            m_watches[(~l1).index()].push_back(watched(l2, l3));
            m_watches[(~l2).index()].push_back(watched(l1, l3));
            m_watches[(~l3).index()].push_back(watched(l1, l2));            
        }

        watch_list& get_wlist(literal l) { return m_watches[l.index()]; }

        // ------------------------------------
        // initialization
        
        void init_var(bool_var v) {
            m_binary.push_back(literal_vector());
            m_binary.push_back(literal_vector());
            m_watches.push_back(watch_list());
            m_watches.push_back(watch_list());
            m_full_watches.push_back(clause_vector());
            m_full_watches.push_back(clause_vector());
            m_bstamp.push_back(0);
            m_bstamp.push_back(0);
            m_stamp.push_back(0);
            m_dfs.push_back(dfs_info());
            m_dfs.push_back(dfs_info());
            m_lits.push_back(lit_info());
            m_lits.push_back(lit_info());
            m_rating.push_back(0);
            m_vprefix.push_back(prefix());
            if (!m_s.was_eliminated(v)) 
                m_freevars.insert(v);
        }

        void init() {
            m_delta_trigger = m_num_vars/10;
            m_config.m_dl_success = 0.8;
            m_inconsistent = false;
            m_qhead = 0;
            m_bstamp_id = 0;

            for (unsigned i = 0; i < m_num_vars; ++i) {
                init_var(i);
            }

            // copy binary clauses
            unsigned sz = m_s.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l = ~to_literal(l_idx);
                watch_list const & wlist = m_s.m_watches[l_idx];
                watch_list::const_iterator it  = wlist.begin();
                watch_list::const_iterator end = wlist.end();
                for (; it != end; ++it) {
                    if (!it->is_binary_non_learned_clause())
                        continue;
                    literal l2 = it->get_literal();                    
                    SASSERT(!m_s.was_eliminated(l.var()));
                    SASSERT(!m_s.was_eliminated(l2.var()));
                    if (l.index() < l2.index()) 
                        add_binary(l, l2);
                }
            }

            copy_clauses(m_s.m_clauses);
            copy_clauses(m_s.m_learned);

            // copy units
            unsigned trail_sz = m_s.init_trail_size();
            for (unsigned i = 0; i < trail_sz; ++i) {
                literal l = m_s.m_trail[i];
                if (!m_s.was_eliminated(l.var())) {
                    if (m_s.m_config.m_drat) m_drat.add(l, false);
                    assign(l);
                }
            }
            propagate();
            m_qhead = m_trail.size();
            TRACE("sat", m_s.display(tout); display(tout););
        }

        void copy_clauses(clause_vector const& clauses) {
            // copy clauses
            clause_vector::const_iterator it =  clauses.begin();
            clause_vector::const_iterator end = clauses.end();
            for (; it != end; ++it) {                
                clause& c = *(*it);
                if (c.was_removed()) continue;
                clause* c1 = m_cls_allocator.mk_clause(c.size(), c.begin(), false);
                m_clauses.push_back(c1);
                attach_clause(*c1);
                for (unsigned i = 0; i < c.size(); ++i) {
                    m_full_watches[(~c[i]).index()].push_back(c1);
                    SASSERT(!m_s.was_eliminated(c[i].var()));
                }
                if (m_s.m_config.m_drat) m_drat.add(c, false);
            }
        }

        // ------------------------------------
        // search
        
        void push(literal lit, unsigned level) { 
            SASSERT(m_search_mode == lookahead_mode::searching);
            m_binary_trail_lim.push_back(m_binary_trail.size());
            m_trail_lim.push_back(m_trail.size());
            m_num_tc1_lim.push_back(m_num_tc1);
            m_retired_clause_lim.push_back(m_retired_clauses.size());
            m_retired_ternary_lim.push_back(m_retired_ternary.size());
            m_qhead_lim.push_back(m_qhead);
            scoped_level _sl(*this, level);
            m_assumptions.push_back(~lit);
            assign(lit);
            propagate();
        }

        void pop() { 
            if (m_assumptions.empty()) IF_VERBOSE(0, verbose_stream() << "empty pop\n";);
            m_assumptions.pop_back();
            m_inconsistent = false;
            SASSERT(m_search_mode == lookahead_mode::searching);

            // m_freevars only for main search 
            // undo assignments
            unsigned old_sz = m_trail_lim.back();
            for (unsigned i = m_trail.size(); i > old_sz; ) {
                --i;
                literal l = m_trail[i];
                set_undef(l);
                TRACE("sat", tout << "inserting free var v" << l.var() << "\n";);
                m_freevars.insert(l.var());
            }
            m_trail.shrink(old_sz); // reset assignment.
            m_trail_lim.pop_back();
            
            m_num_tc1 = m_num_tc1_lim.back();
            m_num_tc1_lim.pop_back();

            // unretire clauses
            old_sz = m_retired_clause_lim.back();
            for (unsigned i = old_sz; i < m_retired_clauses.size(); ++i) {
                attach_clause(*m_retired_clauses[i]);
            }
            m_retired_clauses.resize(old_sz);
            m_retired_clause_lim.pop_back();

            old_sz = m_retired_ternary_lim.back();
            for (unsigned i = old_sz; i < m_retired_ternary.size(); ++i) {
                attach_ternary(m_retired_ternary[i]);
            }
            m_retired_ternary.shrink(old_sz);
            m_retired_ternary_lim.pop_back();
            
            // remove local binary clauses
            old_sz = m_binary_trail_lim.back();            
            for (unsigned i = m_binary_trail.size(); i > old_sz; ) {
                del_binary(m_binary_trail[--i]);
            }
            m_binary_trail.shrink(old_sz);
            m_binary_trail_lim.pop_back();
            
            // reset propagation queue
            m_qhead = m_qhead_lim.back();
            m_qhead_lim.pop_back();            
        }        

        bool push_lookahead2(literal lit, unsigned level) {
            scoped_level _sl(*this, level);
            SASSERT(m_search_mode == lookahead_mode::lookahead1);
            m_search_mode = lookahead_mode::lookahead2;
            assign(lit);
            propagate();
            bool unsat = inconsistent();
            SASSERT(m_search_mode == lookahead_mode::lookahead2);
            m_search_mode = lookahead_mode::lookahead1;
            m_inconsistent = false;
            return unsat;
        }

        void push_lookahead1(literal lit, unsigned level) {
            SASSERT(m_search_mode == lookahead_mode::searching);
            m_search_mode = lookahead_mode::lookahead1;
            scoped_level _sl(*this, level);
            assign(lit);
            propagate();
        }

        void pop_lookahead1(literal lit) {
            bool unsat = inconsistent();
            SASSERT(m_search_mode == lookahead_mode::lookahead1);
            m_inconsistent = false;
            m_search_mode = lookahead_mode::searching;
            // convert windfalls to binary clauses.
            if (!unsat) {
                literal nlit = ~lit;

                for (unsigned i = 0; i < m_wstack.size(); ++i) {
                    literal l2 = m_wstack[i];
                    //update_prefix(~lit);
                    //update_prefix(m_wstack[i]);
                    TRACE("sat", tout << "windfall: " << nlit << " " << l2 << "\n";); 
                    // if we use try_add_binary, then this may produce new assignments
                    // these assignments get put on m_trail, and they are cleared by
                    // reset_wnb. We would need to distinguish the trail that comes
                    // from lookahead levels and the main search level for this to work.
                    add_binary(nlit, l2);
                }
                m_stats.m_windfall_binaries += m_wstack.size();
            }
            m_wstack.reset();
        }

        float mix_diff(float l, float r) const { return l + r + (1 << 10) * l * r; }

        clause const& get_clause(watch_list::iterator it) const {
            clause_offset cls_off = it->get_clause_offset();
            return *(m_cls_allocator.get_clause(cls_off));
        }

        bool is_nary_propagation(clause const& c, literal l) const {
            bool r = c.size() > 2 && ((c[0] == l && is_false(c[1])) || (c[1] == l && is_false(c[0])));
            DEBUG_CODE(if (r) for (unsigned j = 2; j < c.size(); ++j) SASSERT(is_false(c[j])););
            return r;
        }

        // 
        // The current version is modeled after CDCL SAT solving data-structures.
        // It borrows from the watch list data-structure. The cost tradeoffs are somewhat
        // biased towards CDCL search overheads.
        // If we walk over the positive occurrences of l, then those clauses can be retired so 
        // that they don't interfere with calculation of H. Instead of removing clauses from the watch
        // list one can swap them to the "back" and adjust a size indicator of the watch list
        // Only the size indicator needs to be updated on backtracking.
        // 
        void propagate_clauses(literal l) {
            SASSERT(is_true(l));
            if (inconsistent()) return;
            watch_list& wlist = m_watches[l.index()];
            watch_list::iterator it = wlist.begin(), it2 = it, end = wlist.end();
            for (; it != end && !inconsistent(); ++it) {
                switch (it->get_kind()) {
                case watched::BINARY:
                    UNREACHABLE();
                    break;
                case watched::TERNARY: {
                    literal l1 = it->get_literal1();
                    literal l2 = it->get_literal2();
                    bool skip = false;
                    if (is_fixed(l1)) {
                        if (is_false(l1)) {
                            if (is_undef(l2)) {
                                propagated(l2);
                            }
                            else if (is_false(l2)) {
                                TRACE("sat", tout << l1 << " " << l2 << " " << l << "\n";);
                                set_conflict();
                            }
                        }
                        else {
                            // retire this clause
                        }
                    }
                    else if (is_fixed(l2)) {
                        if (is_false(l2)) {
                            propagated(l1);
                        }
                        else {                            
                            // retire this clause
                        }
                    }
                    else {
                        switch (m_search_mode) {
                        case lookahead_mode::searching:
                            detach_ternary(~l, l1, l2);
                            try_add_binary(l1, l2);
                            skip = true;
                            break;
                        case lookahead_mode::lookahead1:
                            m_weighted_new_binaries += (*m_heur)[l1.index()] * (*m_heur)[l2.index()];
                            break;
                        case lookahead2:
                            break;
                        }
                    }
                    if (!skip) {
                        *it2 = *it;
                        it2++;
                    }
                    break;
                }
                case watched::CLAUSE: {
                    if (is_true(it->get_blocked_literal())) {
                        *it2 = *it;
                        ++it2;
                        break;
                    }
                    clause_offset cls_off = it->get_clause_offset();
                    clause & c = *(m_cls_allocator.get_clause(cls_off));
                    if (c[0] == ~l)
                        std::swap(c[0], c[1]);
                    if (is_true(c[0])) {
                        it->set_blocked_literal(c[0]);
                        *it2 = *it;
                        it2++;
                        break;
                    }
                    literal * l_it  = c.begin() + 2;
                    literal * l_end = c.end();
                    bool found = false;
                    for (; l_it != l_end && !found; ++l_it) {
                        if (!is_false(*l_it)) {
                            found = true;
                            c[1]  = *l_it;
                            *l_it = ~l;
                            m_watches[(~c[1]).index()].push_back(watched(c[0], cls_off));
                            TRACE("sat_verbose", tout << "move watch from " << l << " to " << c[1] << " for clause " << c << "\n";);
                        }
                    }
                    if (found) {
                        found = false;
                        for (; l_it != l_end && !found; ++l_it) {
                            found = !is_false(*l_it);
                        }
                        // normal clause was converted to a binary clause.
                        if (!found && is_undef(c[1]) && is_undef(c[0])) {
                            TRACE("sat", tout << "got binary " << l << ": " << c << "\n";);
                            switch (m_search_mode) {
                            case lookahead_mode::searching:
                                detach_clause(c);
                                try_add_binary(c[0], c[1]);
                                break;
                            case lookahead_mode::lookahead1:
                                m_weighted_new_binaries += (*m_heur)[c[0].index()]* (*m_heur)[c[1].index()];
                                break;
                            case lookahead_mode::lookahead2:
                                break;
                            }
                        }
                        else if (found && m_search_mode == lookahead_mode::lookahead1 && m_weighted_new_binaries == 0) {
                            // leave a trail that some clause was reduced but potentially not an autarky
                            l_it  = c.begin() + 2;
                            found = false;
                            for (; l_it != l_end && !found; found = is_true(*l_it), ++l_it) ;
                            if (!found) {
                                m_weighted_new_binaries = (float)0.001;
                            }
                        }
                        break; 
                    }
                    if (is_false(c[0])) {
                        TRACE("sat", tout << "conflict " << l << ": " << c << "\n";);
                        set_conflict();
                        *it2 = *it;
                        ++it2;
                    }
                    else {
                        TRACE("sat", tout << "propagating " << l << ": " << c << "\n";);
                        SASSERT(is_undef(c[0]));
                        DEBUG_CODE(for (unsigned i = 2; i < c.size(); ++i) {
                                SASSERT(is_false(c[i]));
                            });
                        *it2 = *it;
                        it2++;
                        propagated(c[0]);
                    }
                    break;
                }
                case watched::EXT_CONSTRAINT:
                    UNREACHABLE();
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            for (; it != end; ++it, ++it2) {
                *it2 = *it;                         
            }
            wlist.set_end(it2);        
        }

        void propagate_binary(literal l) {
            literal_vector const& lits = m_binary[l.index()];
            TRACE("sat", tout << l << " => " << lits << "\n";);
            unsigned sz = lits.size();
            for (unsigned i = 0; !inconsistent() && i < sz; ++i) {
                assign(lits[i]);
            }
        }

        void propagate() {
            while (!inconsistent() && m_qhead < m_trail.size()) {
                unsigned i = m_qhead;
                unsigned sz = m_trail.size();
                for (; i < sz && !inconsistent(); ++i) {
                    literal l = m_trail[i];
                    TRACE("sat", tout << "propagate " << l << " @ " << m_level << "\n";);
                    propagate_binary(l);
                }
                i = m_qhead;
                for (; i < sz && !inconsistent(); ++i) {            
                    propagate_clauses(m_trail[i]);
                }
                m_qhead = sz;
            }

            TRACE("sat_verbose", display(tout << scope_lvl() << " " << (inconsistent()?"unsat":"sat") << "\n"););
        }

        literal choose() {
            literal l = null_literal;
            while (l == null_literal) {
                pre_select();
                if (m_lookahead.empty()) {
                    break;
                }
                compute_wnb();
                if (inconsistent()) {
                    break;
                }
                l = select_literal();
            }
            SASSERT(inconsistent() || !is_unsat());
            return l;
        }

        void compute_wnb() {
            init_wnb();
            TRACE("sat", display_lookahead(tout); );
            unsigned base = 2;
            bool change = true;
            bool first = true;
            while (change && !inconsistent()) {
                change = false;
                for (unsigned i = 0; !inconsistent() && i < m_lookahead.size(); ++i) {
                    checkpoint();
                    literal lit = m_lookahead[i].m_lit;
                    if (is_fixed_at(lit, c_fixed_truth)) continue;
                    unsigned level = base + m_lookahead[i].m_offset;
                    if (m_stamp[lit.var()] >= level) {
                        continue;
                    }
                    if (scope_lvl() == 1) {
                        IF_VERBOSE(3, verbose_stream() << scope_lvl() << " " << lit << " binary: " << m_binary_trail.size() << " trail: " << m_trail_lim.back() << "\n";);
                    }
                    TRACE("sat", tout << "lookahead: " << lit << " @ " << m_lookahead[i].m_offset << "\n";);
                    reset_wnb(lit);
                    push_lookahead1(lit, level);
                    if (!first) do_double(lit, base);
                    bool unsat = inconsistent();                    
                    pop_lookahead1(lit); 
                    if (unsat) {
                        TRACE("sat", tout << "backtracking and settting " << ~lit << "\n";);
                        reset_wnb();
                        assign(~lit);
                        propagate();
                        init_wnb();
                        change = true;
                    }
                    else {
                        update_wnb(lit, level);                        
                    }
                    SASSERT(inconsistent() || !is_unsat());
                }
                if (c_fixed_truth - 2 * m_lookahead.size() < base) {
                    break;
                }
                if (first && !change) {
                    first = false;
                    change = true;
                }
                reset_wnb();
                init_wnb();
                // base += 2 * m_lookahead.size();
            }
            reset_wnb();
            TRACE("sat", display_lookahead(tout); );
        }

        void init_wnb() {
            TRACE("sat", tout << "init_wnb: " << m_qhead << "\n";);
            m_qhead_lim.push_back(m_qhead);
            m_trail_lim.push_back(m_trail.size());
        }

        void reset_wnb() {
            m_qhead = m_qhead_lim.back();
            TRACE("sat", tout << "reset_wnb: " << m_qhead << "\n";);
            unsigned old_sz = m_trail_lim.back();
            for (unsigned i = old_sz; i < m_trail.size(); ++i) {
                set_undef(m_trail[i]);
            }
            m_trail.shrink(old_sz);            
            m_trail_lim.pop_back();
            m_qhead_lim.pop_back();
        }

        literal select_literal() {
            literal l = null_literal;
            float h = 0;
            unsigned count = 1;
            for (unsigned i = 0; i < m_lookahead.size(); ++i) {
                literal lit = m_lookahead[i].m_lit;
                if (lit.sign() || !is_undef(lit)) {
                    continue;
                }
                float diff1 = get_wnb(lit), diff2 = get_wnb(~lit);
                float mixd = mix_diff(diff1, diff2);

                if (mixd == h) ++count;
                if (mixd > h || (mixd == h && m_s.m_rand(count) == 0)) {
                    CTRACE("sat", l != null_literal, tout << lit << " mix diff: " << mixd << "\n";);
                    if (mixd > h) count = 1;
                    h = mixd;
                    l = diff1 < diff2 ? lit : ~lit;
                }
            }
//            if (count > 1) std::cout << count << "\n";
            TRACE("sat", tout << "selected: " << l << "\n";);
            return l;
        }


        void set_wnb(literal l, float f) { m_lits[l.index()].m_wnb = f; }
        void inc_wnb(literal l, float f) { m_lits[l.index()].m_wnb += f; }
        float get_wnb(literal l) const { return m_lits[l.index()].m_wnb; }
            
        void reset_wnb(literal l) {
            m_weighted_new_binaries = 0;

            // inherit propagation effect from parent.
            literal p = get_parent(l);
            set_wnb(l, p == null_literal ? 0 : get_wnb(p));
        }

        bool check_autarky(literal l, unsigned level) {
            return false;
            // no propagations are allowed to reduce clauses.
            clause_vector::const_iterator it  = m_full_watches[l.index()].begin();
            clause_vector::const_iterator end = m_full_watches[l.index()].end();
            for (; it != end; ++it) {
                clause& c = *(*it);
                unsigned sz = c.size();
                bool found = false;                
                for (unsigned i = 0; !found && i < sz; ++i) {
                    found = is_true(c[i]);
                    if (found) {
                        TRACE("sat", tout << c[i] << " is true in " << c << "\n";);
                    }
                }
                IF_VERBOSE(2, verbose_stream() << "skip autarky " << l << "\n";);
                if (!found) return false;
            }
            //
            // bail out if there is a pending binary propagation.
            // In general, we would have to check, recursively that 
            // a binary propagation does not create reduced clauses.
            // 
            literal_vector const& lits = m_binary[l.index()];
            TRACE("sat", tout << l << ": " << lits << "\n";);
            for (unsigned i = 0; i < lits.size(); ++i) {
                literal l2 = lits[i];
                if (is_true(l2)) continue;
                SASSERT(!is_false(l2));
                return false;
            }

            return true;
        }

        void update_wnb(literal l, unsigned level) {
            if (m_weighted_new_binaries == 0) {
                if (!check_autarky(l, level)) {
                    // skip
                }
                else if (get_wnb(l) == 0) {
                    ++m_stats.m_autarky_propagations;
                    IF_VERBOSE(1, verbose_stream() << "(sat.lookahead autarky " << l << ")\n";);
                    
                    TRACE("sat", tout << "autarky: " << l << " @ " << m_stamp[l.var()] 
                          << " " 
                          << (!m_binary[l.index()].empty() || !m_full_watches[l.index()].empty()) << "\n";);
                    reset_wnb();
                    assign(l);
                    propagate();                    
                    init_wnb();
                }
                else {
                    ++m_stats.m_autarky_equivalences;
                    // l => p is known, but p => l is possibly not. 
                    // add p => l.
                    // justification: any consequence of l
                    // that is not a consequence of p does not
                    // reduce the clauses.
                    literal p = get_parent(l);
                    SASSERT(p != null_literal);
                    if (m_stamp[p.var()] > m_stamp[l.var()]) {
                        TRACE("sat", tout << "equivalence " << l << " == " << p << "\n"; display(tout););
                        IF_VERBOSE(1, verbose_stream() << "(sat.lookahead equivalence " << l << " == " << p << ")\n";);
                        add_binary(~l, p);
                        set_level(l, p);
                    }
                }
            }
            else {
                inc_wnb(l, m_weighted_new_binaries);
            }
        }

        bool dl_enabled(literal l) const { return m_lits[l.index()].m_double_lookahead != m_istamp_id; }
        void dl_disable(literal l) { m_lits[l.index()].m_double_lookahead = m_istamp_id; }
        bool dl_no_overflow(unsigned base) const { return base + 2 * m_lookahead.size() * static_cast<uint64>(m_config.m_dl_max_iterations + 1) < c_fixed_truth; }

        bool is_fixed_at(literal lit, unsigned level) const {
            return is_fixed(lit) && (!is_false(lit) || m_stamp[lit.var()] >= level);
        }

        void do_double(literal l, unsigned& base) {
            if (!inconsistent() && scope_lvl() > 1 && dl_enabled(l)) {                
                if (get_wnb(l) > m_delta_trigger) {
                    if (dl_no_overflow(base)) {
                        ++m_stats.m_double_lookahead_rounds;
                        double_look(l, base);
                        m_delta_trigger = get_wnb(l);
                        dl_disable(l);
                    }
                }
                else {
                    m_delta_trigger *= m_config.m_delta_rho;
                }
            }
        }

        void double_look(literal l, unsigned& base) {
            SASSERT(!inconsistent());
            SASSERT(dl_no_overflow(base));
            unsigned dl_truth = base + 2 * m_lookahead.size() * (m_config.m_dl_max_iterations + 1);            
            scoped_level _sl(*this, dl_truth);
            IF_VERBOSE(2, verbose_stream() << "double: " << l << "\n";);
            init_wnb();
            assign(l);
            propagate();
            bool change = true;
            unsigned num_iterations = 0;
            while (change && num_iterations < m_config.m_dl_max_iterations && !inconsistent()) {
                change = false;
                num_iterations++;
                base += 2*m_lookahead.size();
                for (unsigned i = 0; !inconsistent() && i < m_lookahead.size(); ++i) {
                    literal lit = m_lookahead[i].m_lit;
                    if (is_fixed_at(lit, dl_truth)) continue;                    
                    if (push_lookahead2(lit, base + m_lookahead[i].m_offset)) {
                        TRACE("sat", tout << "unit: " << ~lit << "\n";);
                        ++m_stats.m_double_lookahead_propagations;
                        SASSERT(m_level == dl_truth);
                        reset_wnb();
                        assign(~lit);
                        propagate();
                        change = true;
                        init_wnb();
                    }
                }
                SASSERT(dl_truth - 2 * m_lookahead.size() > base);
            }
            reset_wnb();
            SASSERT(m_level == dl_truth);            
            base = dl_truth;
        }

        void set_conflict() { TRACE("sat", tout << "conflict\n";); m_inconsistent = true; }
        bool inconsistent() { return m_inconsistent; }

        unsigned scope_lvl() const { return m_trail_lim.size(); }

        void validate_assign(literal l) {
            if (m_s.m_config.m_drat && m_search_mode == lookahead_mode::searching) {
                m_assumptions.push_back(l);
                m_drat.add(m_assumptions);
                m_assumptions.pop_back();
            }
        }

        void assign(literal l) {
            SASSERT(m_level > 0);
            if (is_undef(l)) {
                TRACE("sat", tout << "assign: " << l << " @ " << m_level << " " << m_trail_lim.size() << " " << m_search_mode << "\n";);
                set_true(l);
                m_trail.push_back(l);
                if (m_search_mode == lookahead_mode::searching) {
                    m_stats.m_propagations++;
                    TRACE("sat", tout << "removing free var v" << l.var() << "\n";);
                    m_freevars.remove(l.var());
                    validate_assign(l);
                }
            }
            else if (is_false(l)) {
                TRACE("sat", tout << "conflict: " << l << " @ " << m_level << " " << m_search_mode << "\n";);
                SASSERT(!is_true(l));
                validate_assign(l);                
                set_conflict(); 
            }
        }

        void propagated(literal l) {
            assign(l);
            switch (m_search_mode) {
            case lookahead_mode::searching:
                break;
            case lookahead_mode::lookahead1:
                m_wstack.push_back(l);
                break;
            case lookahead_mode::lookahead2:
                break;
            }
        }

        bool backtrack(literal_vector& trail) {
            while (inconsistent()) {
                if (trail.empty()) return false;      
                pop();   
                flip_prefix();
                assign(~trail.back());
                trail.pop_back();
                propagate();
            }
            return true;
        }

        lbool search() {
            m_model.reset();
            scoped_level _sl(*this, c_fixed_truth);
            literal_vector trail;
            m_search_mode = lookahead_mode::searching;
            while (true) {
                TRACE("sat", display(tout););
                inc_istamp();
                checkpoint();
                if (inconsistent()) {
                    if (!backtrack(trail)) return l_false;
                    continue;
                }
                literal l = choose();
                if (inconsistent()) {
                    if (!backtrack(trail)) return l_false;
                    continue;
                }
                if (l == null_literal) {
                    return l_true;
                }
                TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
                ++m_stats.m_decisions;
                IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(m_prefix, m_trail_lim.size()) << ": " << l << " " << m_trail.size() << "\n";);
                push(l, c_fixed_truth);
                trail.push_back(l);
                SASSERT(inconsistent() || !is_unsat());
            }
        }

        void init_model() {
            m_model.reset();
            for (unsigned i = 0; i < m_num_vars; ++i) {
                lbool val;
                literal lit(i, false);
                if (is_undef(lit)) {
                    val = l_undef;
                }
                if (is_true(lit)) {
                    val = l_true;
                }
                else {
                    val = l_false;
                }
                m_model.push_back(val);
            }
        }

        std::ostream& display_binary(std::ostream& out) const {
            for (unsigned i = 0; i < m_binary.size(); ++i) {
                literal_vector const& lits = m_binary[i];
                if (!lits.empty()) {
                    out << to_literal(i) << " -> " << lits << "\n";
                }
            }
            return out;
        }

        std::ostream& display_clauses(std::ostream& out) const {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                out << *m_clauses[i] << "\n";
            }
            return out;
        }

        std::ostream& display_values(std::ostream& out) const {
            for (unsigned i = 0; i < m_trail.size(); ++i) {
                literal l = m_trail[i];
                out << l << "\n";
            }
            return out;
        }

        std::ostream& display_lookahead(std::ostream& out) const {
            for (unsigned i = 0; i < m_lookahead.size(); ++i) {
                literal lit = m_lookahead[i].m_lit;
                unsigned offset = m_lookahead[i].m_offset;
                out << lit << "\toffset: " << offset;
                out << (is_undef(lit)?" undef": (is_true(lit) ? " true": " false"));
                out << " wnb: " << get_wnb(lit);
                out << "\n";
            }
            return out;
        }

        void init_search() {
            m_search_mode = lookahead_mode::searching;
            scoped_level _sl(*this, c_fixed_truth);
            init();            
        }

        void checkpoint() {
            if (!m_rlimit.inc()) {
                throw solver_exception(Z3_CANCELED_MSG);
            }
            if (memory::get_allocation_size() > m_s.m_config.m_max_memory) {
                throw solver_exception(Z3_MAX_MEMORY_MSG);
            }
        }


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
                    if (p != null_literal && p.var() != v && !m_s.is_external(v) && !m_s.was_eliminated(v) && !m_s.was_eliminated(p.var())) {
                        to_elim.push_back(v);
                        roots[v] = p;
                        SASSERT(get_parent(p) == p);
                        set_parent(~p, ~p);
                        SASSERT(get_parent(~p) == ~p);
                        if (v == 5904 || v == 5903) {
                            std::cout << lit << " " << p << "\n";
                        }
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

