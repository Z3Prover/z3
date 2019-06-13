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

#include <cmath>
#include "sat/sat_solver.h"
#include "sat/sat_extension.h"
#include "sat/sat_lookahead.h"
#include "sat/sat_scc.h"
#include "util/union_find.h"

namespace sat {
    lookahead::scoped_ext::scoped_ext(lookahead& p): p(p) {
        if (p.m_s.m_ext) p.m_s.m_ext->set_lookahead(&p); 
    }
    
    lookahead::scoped_ext::~scoped_ext() {
        if (p.m_s.m_ext) p.m_s.m_ext->set_lookahead(nullptr);
    }

    lookahead::scoped_assumptions::scoped_assumptions(lookahead& p, literal_vector const& lits): p(p), lits(lits) {
        for (auto l : lits) {
            p.push(l, p.c_fixed_truth);
        }
    }
    lookahead::scoped_assumptions::~scoped_assumptions() {
        for (auto l : lits) {
            (void)l;
            p.pop();
        }
    }

    void lookahead::flip_prefix() {
        if (m_trail_lim.size() < 64) {
            uint64_t mask = (1ull << m_trail_lim.size());
            m_prefix = mask | (m_prefix & (mask - 1));
        }
    }

    void lookahead::prune_prefix() {
        if (m_trail_lim.size() < 64) {
            m_prefix &= (1ull << m_trail_lim.size()) - 1;
        }
    }

    void lookahead::update_prefix(literal l) {
        bool_var x = l.var();
        unsigned p = m_vprefix[x].m_prefix;
        unsigned pl = m_vprefix[x].m_length;
        unsigned mask = (1 << std::min(31u, pl)) - 1; 
        if (pl >= m_trail_lim.size() || (p & mask) != (m_prefix & mask)) {
            m_vprefix[x].m_length = m_trail_lim.size();
            m_vprefix[x].m_prefix = static_cast<unsigned>(m_prefix);
        }
    }

    bool lookahead::active_prefix(bool_var x) {
        unsigned lvl = m_trail_lim.size();
        unsigned p = m_vprefix[x].m_prefix;
        unsigned l = m_vprefix[x].m_length;
        if (l > lvl) return false;
        if (l == lvl || l >= 31) return m_prefix == p;
        unsigned mask = ((1 << std::min(l,31u)) - 1);
        return (m_prefix & mask) == (p & mask);
    }

    void lookahead::add_binary(literal l1, literal l2) {
        TRACE("sat", tout << "binary: " << l1 << " " << l2 << "\n";);
        SASSERT(l1 != l2);
        // don't add tautologies and don't add already added binaries
        if (~l1 == l2) return;
        if (!m_binary[(~l1).index()].empty() && m_binary[(~l1).index()].back() == l2) return;
        m_binary[(~l1).index()].push_back(l2);
        m_binary[(~l2).index()].push_back(l1);
        m_binary_trail.push_back((~l1).index());
        ++m_stats.m_add_binary;
        if (m_s.m_config.m_drat && m_search_mode == lookahead_mode::searching) validate_binary(l1, l2);
    }

    void lookahead::del_binary(unsigned idx) {
        // TRACE("sat", display(tout << "Delete " << to_literal(idx) << "\n"););
        literal_vector & lits = m_binary[idx];
        SASSERT(!lits.empty());
        literal l = lits.back();
        lits.pop_back();            
        SASSERT(!m_binary[(~l).index()].empty());
        SASSERT(m_binary[(~l).index()].back() == ~to_literal(idx));
        m_binary[(~l).index()].pop_back();
        ++m_stats.m_del_binary;
    }


    void lookahead::validate_binary(literal l1, literal l2) {
        m_assumptions.push_back(l1);
        m_assumptions.push_back(l2);
        m_s.m_drat.add(m_assumptions);
        m_assumptions.pop_back();
        m_assumptions.pop_back();
    }

    void lookahead::inc_bstamp() {
        ++m_bstamp_id;
        if (m_bstamp_id == 0) {
            ++m_bstamp_id;
            m_bstamp.fill(0);
        }
    }

    void lookahead::inc_istamp() {
        ++m_istamp_id;
        if (m_istamp_id == 0) {
            ++m_istamp_id;
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                m_lits[i].m_double_lookahead = 0;
            }
        }
    }

    void lookahead::set_bstamps(literal l) {
        inc_bstamp();
        set_bstamp(l);
        literal_vector const& conseq = m_binary[l.index()];
        for (literal l : conseq) {
            set_bstamp(l);
        }
    }

    /**
       \brief add one-step transitive closure of binary implications
       return false if we learn a unit literal.
       \pre all implicants of ~u are stamped.
       u \/ v is true
    **/

    bool lookahead::add_tc1(literal u, literal v) {
        unsigned sz = m_binary[v.index()].size();
        for (unsigned i = 0; i < sz; ++i) {
            literal w = m_binary[v.index()][i];
            // ~v \/ w
            if (!is_fixed(w)) {
                if (is_stamped(~w)) {
                    // u \/ v, ~v \/ w, u \/ ~w => u is unit
                    TRACE("sat", tout << "tc1: " << u << "\n";);
                    propagated(u);
                    return false;
                }
                if (m_num_tc1 < m_config.m_tc1_limit) {
                    ++m_num_tc1;
                    IF_VERBOSE(30, verbose_stream() << "tc1: " << u << " " << w << "\n";);
                    add_binary(u, w);
                }
            }
        }
        return true;
    }


    /**
       \brief main routine for adding a new binary clause dynamically.
    */
    void lookahead::try_add_binary(literal u, literal v) {
        SASSERT(m_search_mode == lookahead_mode::searching);
        SASSERT(u.var() != v.var());
        if (!is_undef(u) || !is_undef(v)) {
            IF_VERBOSE(0, verbose_stream() << "adding assigned binary " << v << " " << u << "\n";);
        }
        set_bstamps(~u);
        if (is_stamped(~v)) {         
            TRACE("sat", tout << "try_add_binary: " << u << "\n";);       
            propagated(u);        // u \/ ~v, u \/ v => u is a unit literal
        }
        else if (!is_stamped(v) && add_tc1(u, v)) {
            // u \/ v is not in index
            set_bstamps(~v);
            if (is_stamped(~u)) {
                TRACE("sat", tout << "try_add_binary: " << v << "\n";);
                propagated(v);    // v \/ ~u, u \/ v => v is a unit literal
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
    

    void lookahead::pre_select() {
        IF_VERBOSE(10, verbose_stream() << "(sat-lookahead :freevars " << m_freevars.size() << ")\n";);
        m_lookahead.reset();
        for (bool_var x : m_freevars) { // tree lookahead leaves literals fixed in lower truth levels
            literal l(x, false);
            set_undef(l);
            set_undef(~l);
        }
        if (select(scope_lvl())) {
            get_scc();
            if (inconsistent()) return;
            find_heights();
            construct_lookahead_table();
        }
    }


    bool lookahead::select(unsigned level) {
        init_pre_selection(level);
        unsigned level_cand = std::max(m_config.m_level_cand, m_freevars.size() / 50);
        unsigned max_num_cand = (level > 0 && m_config.m_preselect) ? level_cand / level : m_freevars.size();
        max_num_cand = std::max(m_config.m_min_cutoff, max_num_cand);

        double sum = 0;
        for (bool newbies = false; ; newbies = true) {
            sum = init_candidates(level, newbies);
            if (!m_candidates.empty()) break;
            if (is_sat()) {
                return false;
            }         
        }
        SASSERT(!m_candidates.empty());
        // cut number of candidates down to max_num_cand.
        // step 1. cut it to at most 2*max_num_cand.
        // step 2. use a heap to sift through the rest.
        bool progress = true;
        while (progress && m_candidates.size() >= max_num_cand * 2) {
            progress = false;
            double mean = sum / (double)(m_candidates.size() + 0.0001);
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
        heap_sort();
        while (m_candidates.size() > max_num_cand) {
            m_candidates.pop_back();
        }
        SASSERT(!m_candidates.empty() && m_candidates.size() <= max_num_cand);
        TRACE("sat", display_candidates(tout););
        return true;
    }

    void lookahead::heap_sort() {
        if (m_candidates.size() > 1) {
            heapify();
            for (unsigned i = m_candidates.size() - 1; i > 0; --i) {
                candidate c = m_candidates[i];
                m_candidates[i] = m_candidates[0];
                m_candidates[0] = c;
                sift_down(0, i);
            }
        }
        SASSERT(validate_heap_sort());
    }

    void lookahead::heapify() {
        unsigned i = 1 + (m_candidates.size() - 2) / 2;
        while(i > 0) {
            sift_down(--i, m_candidates.size());
        }
    }

    void lookahead::sift_down(unsigned j, unsigned sz) {
        unsigned i = j;
        candidate c = m_candidates[j];
        for (unsigned k = 2 * j + 1; k < sz; i = k, k = 2 * k + 1) {
            // pick smallest child
            if (k + 1 < sz && m_candidates[k].m_rating > m_candidates[k + 1].m_rating) {
                ++k;
            }
            if (c.m_rating <= m_candidates[k].m_rating) break;
            m_candidates[i] = m_candidates[k];
        }
        if (i > j) m_candidates[i] = c;
    }

    /**
     * \brief validate that the result of heap sort sorts the candidates
     * in descending order of their rating.
     */
    bool lookahead::validate_heap_sort() {
        for (unsigned i = 0; i + 1 < m_candidates.size(); ++i)
            if (m_candidates[i].m_rating < m_candidates[i + 1].m_rating) 
                return false;
        return true;
    }

    double lookahead::init_candidates(unsigned level, bool newbies) {
        m_candidates.reset();
        double sum = 0;
        unsigned skip_candidates = 0;
        bool autarky = get_config().m_lookahead_global_autarky;
        if (!m_select_lookahead_vars.empty()) {
            for (bool_var x : m_freevars) {
                SASSERT(is_undef(x));
                if (m_select_lookahead_vars.contains(x)) {
                    if (!autarky || newbies || in_reduced_clause(x)) {
                        m_candidates.push_back(candidate(x, m_rating[x]));
                        sum += m_rating[x];
                    }
                    else {
                        skip_candidates++;
                    }
                }                
            }
        }
        if (m_candidates.empty() && (m_select_lookahead_vars.empty() || newbies)) {
            for (bool_var x : m_freevars) {
                SASSERT(is_undef(x));
                if (newbies || active_prefix(x)) {
                    m_candidates.push_back(candidate(x, m_rating[x]));
                    sum += m_rating[x];                
                }           
            }
        } 
        TRACE("sat", display_candidates(tout << "sum: " << sum << "\n"););
        if (skip_candidates > 0) {
            IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :candidates " << m_candidates.size() << " :skipped " << skip_candidates << ")\n";);
        }
        return sum;
    }


    std::ostream& lookahead::display_candidates(std::ostream& out) const {
        for (unsigned i = 0; i < m_candidates.size(); ++i) {
            out << "var: " << m_candidates[i].m_var << " rating: " << m_candidates[i].m_rating << "\n";
        }          
        return out;
    }

    bool lookahead::is_unsat() const {
        for (unsigned idx = 0; idx < m_binary.size(); ++idx) {
            literal l = to_literal(idx);
            for (literal lit : m_binary[idx]) {
                if (is_true(l) && is_false(lit))
                    return true;
            }
        }
        // check if there is a clause whose literals are false.
        // every clause is terminated by a null-literal.
        for (nary* n : m_nary_clauses) {
            bool all_false = true;
            for (literal l : *n) {
                all_false &= is_false(l);
            }
            if (all_false) return true;
        }
        // check if there is a ternary whose literals are false.
        for (unsigned idx = 0; idx < m_ternary.size(); ++idx) {
            literal lit = to_literal(idx);
            if (is_false(lit)) {
                unsigned sz = m_ternary_count[lit.index()];
                for (binary const& b : m_ternary[lit.index()]) {
                    if (sz-- == 0) break;
                    if (is_false(b.m_u) && is_false(b.m_v)) 
                        return true;
                }
            }
        }        
        return false;
    }

    bool lookahead::is_sat() const {
        for (bool_var x : m_freevars) {
            literal l(x, false);
            literal_vector const& lits1 = m_binary[l.index()];
            for (literal lit1 : lits1) {
                if (!is_true(lit1)) {
                    TRACE("sat", tout << l << " " << lit1 << "\n";);
                    return false;
                }
            }
            l.neg();
            literal_vector const& lits2 = m_binary[l.index()];
            for (literal lit2 : lits2) {
                if (!is_true(lit2)) {
                    TRACE("sat", tout << l << " " << lit2 << "\n";);
                    return false;
                }
            }
        }
        // check if there is a clause whose literals are false.
        // every clause is terminated by a null-literal.
        for (nary * n : m_nary_clauses) {
            bool no_true = true;
            for (literal l : *n) {
                no_true &= !is_true(l);
            }
            if (no_true) return false;
        }
        // check if there is a ternary whose literals are false.
        for (unsigned idx = 0; idx < m_ternary.size(); ++idx) {
            literal lit = to_literal(idx);
            if (!is_true(lit)) {
                unsigned sz = m_ternary_count[lit.index()];
                for (binary const& b : m_ternary[lit.index()]) {
                    if (sz-- == 0) break;
                    if (!is_true(b.m_u) && !is_true(b.m_v)) 
                        return false;
                }
            }
        }        
        return true;
    }

    bool lookahead::missed_propagation() const {
        if (inconsistent()) return false;
        for (literal l1 : m_trail) {
            SASSERT(is_true(l1));
            for (literal l2 : m_binary[l1.index()]) {
                VERIFY(is_true(l2));
                if (is_undef(l2)) return true;
            }
            unsigned sz = m_ternary_count[(~l1).index()];
            for (binary b : m_ternary[(~l1).index()]) {
                if (sz-- == 0) break;
                if (!(is_true(b.m_u) || is_true(b.m_v) || (is_undef(b.m_v) && is_undef(b.m_u)))) {
                    IF_VERBOSE(0, verbose_stream() << b.m_u << " " << b.m_v << "\n"
                               << get_level(b.m_u) << " " << get_level(b.m_v) << " level: " << m_level << "\n";);
                    UNREACHABLE();
                }
                if ((is_false(b.m_u) && is_undef(b.m_v)) || (is_false(b.m_v) && is_undef(b.m_u)))
                    return true;
            }
        }
        for (nary * n : m_nary_clauses) {
            if (n->size() == 1 && !is_true(n->get_head())) {
                for (literal lit : *n) {
                    VERIFY(!is_undef(lit));
                    if (is_undef(lit)) return true;
                }
            }
        }
        return false;
    }

    bool lookahead::missed_conflict() const {
        if (inconsistent()) return false;
        for (literal l1 : m_trail) {
            for (literal l2 : m_binary[l1.index()]) {
                if (is_false(l2))
                    return true;
            }
            unsigned sz = m_ternary_count[(~l1).index()];
            for (binary b : m_ternary[(~l1).index()]) {
                if (sz-- == 0) break;
                if ((is_false(b.m_u) && is_false(b.m_v)))
                    return true;
            }
        }
        for (nary * n : m_nary_clauses) {
            if (n->size() == 0)
                return true;
        }
        return false;
    }

    void lookahead::init_pre_selection(unsigned level) {
        switch (m_config.m_reward_type) {
        case ternary_reward: {
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
            break;
        }
        case heule_schur_reward:
            heule_schur_scores();
            break;
        case heule_unit_reward:
            heule_unit_scores();
            break;
        case march_cu_reward:
            march_cu_scores();
            break;
        case unit_literal_reward:
            heule_schur_scores();
            break;
        }
    }

    void lookahead::heule_schur_scores() {
        if (m_rating_throttle++ % 10 != 0) return;
        for (bool_var x : m_freevars) {
            literal l(x, false);
            m_rating[l.var()] = heule_schur_score(l) * heule_schur_score(~l);
        }        
    }

    double lookahead::heule_schur_score(literal l) {
        double sum = 0;
        for (literal lit : m_binary[l.index()]) {
            if (is_undef(lit)) sum += literal_occs(lit) / 4.0;
        }
        unsigned sz = m_ternary_count[(~l).index()];
        for (binary const& b : m_ternary[(~l).index()]) {
            if (sz-- == 0) break;
            sum += (literal_occs(b.m_u) + literal_occs(b.m_v)) / 8.0;            
        }
        sz = m_nary_count[(~l).index()];
        for (nary * n : m_nary[(~l).index()]) {
            if (sz-- == 0) break;
            double to_add = 0;
            for (literal lit : *n) {
                if (!is_fixed(lit) && lit != ~l) {
                    to_add += literal_occs(lit);
                }
            }
            unsigned len = n->size();
            sum += pow(0.5, len) * to_add / len;            
        }
        return sum;
    } 

    void lookahead::heule_unit_scores() {
        if (m_rating_throttle++ % 10 != 0) return;
        for (bool_var x : m_freevars) {
            literal l(x, false);
            m_rating[l.var()] = heule_unit_score(l) * heule_unit_score(~l);
        }
    }

    double lookahead::heule_unit_score(literal l) {
        double sum = 0;
        for (literal lit : m_binary[l.index()]) {
            if (is_undef(lit)) sum += 0.5;
        }
        sum += 0.25 * m_ternary_count[(~l).index()];
        unsigned sz = m_nary_count[(~l).index()];
        for (nary * n : m_nary[(~l).index()]) {
            if (sz-- == 0) break;
            sum += pow(0.5, n->size());
        }
        return sum;
    }

    void lookahead::march_cu_scores() {
        for (bool_var x : m_freevars) {
            literal l(x, false);
            double pos = march_cu_score(l), neg = march_cu_score(~l);
            m_rating[l.var()] = 1024 * pos * neg + pos + neg + 1;
        }
    }

    double lookahead::march_cu_score(literal l) {
        double sum = 1.0 + literal_big_occs(~l);
        for (literal lit : m_binary[l.index()]) {
            if (is_undef(lit)) sum += literal_big_occs(lit);
        }
        return sum;
    }

    void lookahead::ensure_H(unsigned level) {
        while (m_H.size() <= level) {
            m_H.push_back(svector<double>());
            m_H.back().resize(m_num_vars * 2, 0);
        }
    }

    void lookahead::h_scores(svector<double>& h, svector<double>& hp) {
        double sum = 0;
        for (bool_var x : m_freevars) {
            literal l(x, false);
            sum += h[l.index()] + h[(~l).index()];
        }
        if (sum == 0) sum = 0.0001;
        double factor = 2 * m_freevars.size() / sum;
        double sqfactor = factor * factor;
        double afactor = factor * m_config.m_alpha;
        for (bool_var x : m_freevars) {
            literal l(x, false);
            double pos = l_score(l,  h, factor, sqfactor, afactor);
            double neg = l_score(~l, h, factor, sqfactor, afactor);
            hp[l.index()] = pos;
            hp[(~l).index()] = neg;
            m_rating[l.var()] = pos * neg;
        }
    }

    double lookahead::l_score(literal l, svector<double> const& h, double factor, double sqfactor, double afactor) {
        double sum = 0, tsum = 0;
        for (literal lit : m_binary[l.index()]) {
            if (is_undef(lit)) sum += h[lit.index()]; 
            // if (m_freevars.contains(lit.var())) sum += h[lit.index()]; 
        }
        unsigned sz = m_ternary_count[(~l).index()];
        for (binary const& b : m_ternary[(~l).index()]) {
            if (sz-- == 0) break;
            tsum += h[b.m_u.index()] * h[b.m_v.index()];
        }
        // std::cout << "sum: " << sum << " afactor " << afactor << " sqfactor " << sqfactor << " tsum " << tsum << "\n";
        sum = (double)(0.1 + afactor*sum + sqfactor*tsum);
        // std::cout << "sum: " << sum << " max score " << m_config.m_max_score << "\n";
        return std::min(m_config.m_max_score, sum);
    }

    // ------------------------------------       
    // Implication graph
    // Compute implication ordering and strongly connected components.
    // sat11.w 103 - 114.
    
    void lookahead::get_scc() {
        unsigned num_candidates = m_candidates.size();
        init_scc();
        for (unsigned i = 0; i < num_candidates && !inconsistent(); ++i) {
            literal lit(m_candidates[i].m_var, false);
            if (get_rank(lit) == 0) get_scc(lit);
            if (get_rank(~lit) == 0) get_scc(~lit);
        }
        TRACE("sat", display_scc(tout););
    }
    void lookahead::init_scc() {
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
        m_rank_max = UINT_MAX;
        m_active = null_literal;
        m_settled = null_literal;
        TRACE("sat", display_dfs(tout););
    }
    void lookahead::init_dfs_info(literal l) {
        unsigned idx = l.index();
        m_dfs[idx].reset();
        set_bstamp(l);
    }
    // arcs are added in the opposite direction of implications.
    // So for implications l => u we add arcs u -> l
    void lookahead::init_arcs(literal l) {
        literal_vector lits;
        literal_vector const& succ = m_binary[l.index()];
        for (literal u : succ) {
            SASSERT(u != l);
            // l => u
            // NB. u.index() > l.index() iff u.index() > (~l).index().
            // since indices for the same boolean variables occupy
            // two adjacent numbers.
            if (u.index() > l.index() && is_stamped(u) && ~l != u) {                
                add_arc(~l, ~u);
                add_arc( u,  l);
            }
        }
        for (auto w : m_watches[l.index()]) {
            lits.reset();
            if (w.is_ext_constraint() && m_s.m_ext->is_extended_binary(w.get_ext_constraint_idx(), lits)) { 
                for (literal u : lits) {
                    // u is positive in lits, l is negative:                    
                    if (~l != u && u.index() > l.index() && is_stamped(u)) {
                        add_arc(~l, ~u);
                        add_arc( u,  l);
                    }
                }
            }
        }
    }

    void lookahead::add_arc(literal u, literal v) {
        auto & lst = m_dfs[u.index()].m_next;
        if (lst.empty() || lst.back() != v) lst.push_back(v);
    }

    void lookahead::get_scc(literal v) {
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

    void lookahead::activate_scc(literal l) {
        SASSERT(get_rank(l) == 0);
        set_rank(l, ++m_rank);
        set_link(l, m_active);
        set_min(l, l);
        m_active = l;
    }
    // make v root of the scc equivalence class
    // set vcomp to be the highest rated literal
    void lookahead::found_scc(literal v) {
        literal t = m_active; 
        m_active = get_link(v);
        literal best = v;
        double best_rating = get_rating(v);
        set_rank(v, m_rank_max);
        set_link(v, m_settled); m_settled = t; 
        while (t != v) {
            if (t == ~v) {
                TRACE("sat", display_scc(tout << "found contradiction during scc search\n"););
                set_conflict();
                break;
            }
            set_rank(t, m_rank_max);
            set_parent(t, v);
            double t_rating = get_rating(t);
            if (t_rating > best_rating) {
                best = t;
                best_rating = t_rating;
            }
            t = get_link(t);
        }
        set_parent(v, v);
        set_vcomp(v, best);
        if (maxed_rank(~v)) {
            set_vcomp(v, ~get_vcomp(get_parent(~v)));
        }
    } 

    std::ostream& lookahead::display_dfs(std::ostream& out) const {
        for (unsigned i = 0; i < m_candidates.size(); ++i) {
            literal l(m_candidates[i].m_var, false);
            display_dfs(out, l);
            display_dfs(out, ~l);
        }
        return out;
    }

    std::ostream& lookahead::display_dfs(std::ostream& out, literal l) const {
        arcs const& a1 = get_arcs(l);
        if (!a1.empty()) {
            out << l << " -> " << a1 << "\n";
        }
        return out;
    }

    std::ostream& lookahead::display_scc(std::ostream& out) const {
        display_dfs(out);
        for (unsigned i = 0; i < m_candidates.size(); ++i) {
            literal l(m_candidates[i].m_var, false);
            display_scc(out, l);
            display_scc(out, ~l);
        }
        return out;
    }

    std::ostream& lookahead::display_scc(std::ostream& out, literal l) const {
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

    literal lookahead::get_child(literal u) const { 
        if (u == null_literal) return m_root_child; 
        return m_dfs[u.index()].m_min; 
    }
     
    void lookahead::set_child(literal v, literal u) { 
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
    void lookahead::find_heights() {
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
    std::ostream& lookahead::display_forest(std::ostream& out, literal l) {
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

    void lookahead::display_search_string() {
        printf("\r"); 
        uint64_t q = m_prefix;
        unsigned depth = m_trail_lim.size();
        unsigned d = std::min(63u, depth);
        unsigned new_prefix_length = d;
        for (unsigned i = 0; i <= d; ++i) {
            printf((0 != (q & (1ull << i)))? "1" : "0");
        }
        if (d < depth) {
            printf(" d: %d", depth);
            new_prefix_length += 10;
        }
        for (unsigned i = new_prefix_length; i < m_last_prefix_length; ++i) {
            printf(" ");
        }
        m_last_prefix_length = new_prefix_length;
        fflush(stdout);       
    }
    
    void lookahead::construct_lookahead_table() {
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
    // initialization
        
    void lookahead::init_var(bool_var v) {
        m_binary.push_back(literal_vector());
        m_binary.push_back(literal_vector());
        m_watches.push_back(watch_list());
        m_watches.push_back(watch_list());
        m_ternary.push_back(svector<binary>());
        m_ternary.push_back(svector<binary>());
        m_ternary_count.push_back(0);
        m_ternary_count.push_back(0);
        m_nary.push_back(ptr_vector<nary>());
        m_nary.push_back(ptr_vector<nary>());
        m_nary_count.push_back(0);
        m_nary_count.push_back(0);
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

    void lookahead::init(bool learned) {
        m_delta_trigger = 0.0;
        m_delta_decrease = 0.0;
        m_delta_fraction = m_s.m_config.m_lookahead_delta_fraction;
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
            if (m_s.was_eliminated(l.var())) continue;
            watch_list const & wlist = m_s.m_watches[l_idx];
            for (auto& w : wlist) {
                if (!w.is_binary_clause())
                    continue;
                if (!learned && w.is_learned())
                    continue;
                literal l2 = w.get_literal();                    
                if (l.index() < l2.index() && !m_s.was_eliminated(l2.var()))
                    add_binary(l, l2);
            }
        }

        copy_clauses(m_s.m_clauses, false);
        if (learned) copy_clauses(m_s.m_learned, true);

        // copy units
        unsigned trail_sz = m_s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            literal l = m_s.m_trail[i];
            if (!m_s.was_eliminated(l.var())) {
                if (m_s.m_config.m_drat) m_s.m_drat.add(l, false);
                assign(l);
            }
        }
        
        if (m_s.m_ext) {
            // m_ext = m_s.m_ext->copy(this, learned);
        }
        propagate();
        m_qhead = m_trail.size();
        m_init_freevars = m_freevars.size();
        TRACE("sat", m_s.display(tout); display(tout););
    }

    void lookahead::copy_clauses(clause_vector const& clauses, bool learned) {
        // copy clauses
        for (clause* cp : clauses) {
            clause& c = *cp;
            if (c.was_removed()) continue;
            // enable when there is a non-ternary reward system.
            bool was_eliminated = false;
            for (unsigned i = 0; !was_eliminated && i < c.size(); ++i) {
                was_eliminated = m_s.was_eliminated(c[i].var());
            }
            if (was_eliminated) continue;

            switch (c.size()) {
            case 0: set_conflict(); break;
            case 1: assign(c[0]); break;
            case 2: add_binary(c[0],c[1]); break;
            case 3: add_ternary(c[0],c[1],c[2]); break;
            default: if (!learned) add_clause(c); break;
            }
            // if (m_s.m_config.m_drat) m_s.m_drat.add(c, false);
        }
    }

    // ------------------------------------
    // search
    

    void lookahead::push(literal lit, unsigned level) { 
        SASSERT(m_search_mode == lookahead_mode::searching);
        m_binary_trail_lim.push_back(m_binary_trail.size());
        m_trail_lim.push_back(m_trail.size());
        m_num_tc1_lim.push_back(m_num_tc1);
        m_qhead_lim.push_back(m_qhead);
        scoped_level _sl(*this, level);
        m_assumptions.push_back(~lit);
        assign(lit);
        propagate();
    }

    void lookahead::pop() { 
        SASSERT(!m_assumptions.empty());
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
            
        m_num_tc1 = m_num_tc1_lim.back();
        m_num_tc1_lim.pop_back();

        for (unsigned i = m_qhead; i > m_qhead_lim.back(); ) {
            --i;
            restore_ternary(m_trail[i]);
            restore_clauses(m_trail[i]);
        }

        m_trail.shrink(old_sz); // reset assignment.
        m_trail_lim.pop_back();


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

    bool lookahead::push_lookahead2(literal lit, unsigned level) {
        scoped_level _sl(*this, level);
        SASSERT(m_search_mode == lookahead_mode::lookahead1);
        m_search_mode = lookahead_mode::lookahead2;
        lookahead_backtrack();
        assign(lit);
        propagate();
        bool unsat = inconsistent();
        SASSERT(m_search_mode == lookahead_mode::lookahead2);
        m_search_mode = lookahead_mode::lookahead1;
        m_inconsistent = false;
        return unsat;
    }

    unsigned lookahead::push_lookahead1(literal lit, unsigned level) {
        SASSERT(m_search_mode == lookahead_mode::searching);
        m_search_mode = lookahead_mode::lookahead1;
        scoped_level _sl(*this, level);
        lookahead_backtrack();
        unsigned old_sz = m_trail.size();
        assign(lit);
        propagate();
        return m_trail.size() - old_sz;
    }

    void lookahead::pop_lookahead1(literal lit, unsigned num_units) {
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
                // lookahead_backtrack. 
                add_binary(nlit, l2);
            }
            m_stats.m_windfall_binaries += m_wstack.size();
        }
        switch (m_config.m_reward_type) {
        case unit_literal_reward:
            m_lookahead_reward += num_units;
            break;
        case heule_unit_reward:
        case march_cu_reward:
        case heule_schur_reward:
            break;
        default:
            break;
        }
        m_wstack.reset();
    }

    void lookahead::lookahead_backtrack() {
        literal lit = null_literal;
        while (!m_trail.empty() && is_undef((lit = m_trail.back()))) {
            if (m_qhead == m_trail.size()) {
                unsigned sz = m_nary_count[(~lit).index()];
                for (nary* n : m_nary[(~lit).index()]) {
                    if (sz-- == 0) break;
                    n->inc_size();
                }
                --m_qhead;
            }
            m_trail.pop_back();
        }
        SASSERT(m_trail_lim.empty() || m_trail.size() >= m_trail_lim.back());
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

    class lookahead_literal_occs_fun : public literal_occs_fun {
        lookahead& lh;
    public:
        lookahead_literal_occs_fun(lookahead& lh): lh(lh) {}
        double operator()(literal l) override { return lh.literal_occs(l); }
    };

    // Ternary clause management:

    void lookahead::add_ternary(literal u, literal v, literal w) {
        SASSERT(u != w && u != v && v != w && ~u != w && ~u != v && ~w != v);
        m_ternary[u.index()].push_back(binary(v, w));
        m_ternary[v.index()].push_back(binary(w, u));
        m_ternary[w.index()].push_back(binary(u, v));
        m_ternary_count[u.index()]++;
        m_ternary_count[v.index()]++;
        m_ternary_count[w.index()]++;
    }

    lbool lookahead::propagate_ternary(literal l1, literal l2) {
        if (is_fixed(l1)) {
            if (is_false(l1)) {
                if (is_false(l2)) {
                    TRACE("sat", tout << l1 << " " << l2 << " " << "\n";);
                    set_conflict();
                    return l_false;
                }
                else if (is_undef(l2)) {
                    propagated(l2);
                }
                return l_true;
            }
            else {
                return l_true;
            }
        }

        if (is_fixed(l2)) {
            if (is_false(l2)) {
                propagated(l1);
                return l_false;
            }
            else {                            
                return l_true;
            }
        }
        return l_undef;
    }

    void lookahead::propagate_ternary(literal l) {
        unsigned sz = m_ternary_count[(~l).index()];

        switch (m_search_mode) {
        case lookahead_mode::searching: {

            // ternary clauses where l is negative become binary
            for (binary const& b : m_ternary[(~l).index()]) {
                if (sz-- == 0) break;
                // this could create a conflict from propagation, but we complete the transaction.
                TRACE("sat", display(tout););
                literal l1 = b.m_u;
                literal l2 = b.m_v;
                switch (propagate_ternary(l1, l2)) {
                case l_undef:
                    try_add_binary(l1, l2);
                    break;
                default:
                    // propagated or tautology or conflict
                    break;
                }
                remove_ternary(l1, l2, ~l);
                remove_ternary(l2, ~l, l1);
            }    

            sz = m_ternary_count[l.index()];        
            // ternary clauses where l is positive are tautologies
            for (binary const& b : m_ternary[l.index()]) {
                if (sz-- == 0) break;
                remove_ternary(b.m_u, b.m_v, l);
                remove_ternary(b.m_v, l, b.m_u);
            }
            break;
        }
        case lookahead_mode::lookahead1:
            // this could create a conflict from propagation, but we complete the loop.
            for (binary const& b : m_ternary[(~l).index()]) {
                if (sz-- == 0) break;
                literal l1 = b.m_u;
                literal l2 = b.m_v;
                switch (propagate_ternary(l1, l2)) {
                case l_undef:
                    update_binary_clause_reward(l1, l2);
                    break;
                default:
                    break;
                }
            }
            break;
        case lookahead2:
            // this could create a conflict from propagation, but we complete the loop.
            for (binary const& b : m_ternary[(~l).index()]) {
                if (sz-- == 0) break;
                propagate_ternary(b.m_u, b.m_v);
            }
            break;
        }
    }

    void lookahead::remove_ternary(literal l, literal u, literal v) {
        unsigned idx = l.index();
        unsigned sz = m_ternary_count[idx]--;
        auto& tv = m_ternary[idx];
        for (unsigned i = sz; i-- > 0; ) {
            binary const& b = tv[i];
            if (b.m_u == u && b.m_v == v) {
                std::swap(tv[i], tv[sz-1]);
                return;
            }
        }
        UNREACHABLE();
    }

    void lookahead::restore_ternary(literal l) {
        unsigned sz = m_ternary_count[(~l).index()];
        for (binary const& b : m_ternary[(~l).index()]) {
            if (sz-- == 0) break;            
            m_ternary_count[b.m_u.index()]++;
            m_ternary_count[b.m_v.index()]++;
        }
        sz = m_ternary_count[l.index()];
        for (binary const& b : m_ternary[l.index()]) {
            if (sz-- == 0) break;
            m_ternary_count[b.m_u.index()]++;
            m_ternary_count[b.m_v.index()]++;
        }
    }

    void lookahead::propagate_external(literal l) {
        SASSERT(is_true(l));
        if (!m_s.m_ext || inconsistent()) return;
        watch_list& wlist = m_watches[l.index()];
        watch_list::iterator it = wlist.begin(), it2 = it, end = wlist.end();
        for (; it != end && !inconsistent(); ++it) {
            SASSERT(it->get_kind() == watched::EXT_CONSTRAINT);
            bool keep = m_s.m_ext->propagate(l, it->get_ext_constraint_idx());
            if (m_search_mode == lookahead_mode::lookahead1 && !m_inconsistent) {
                lookahead_literal_occs_fun literal_occs_fn(*this);
                m_lookahead_reward += m_s.m_ext->get_reward(l, it->get_ext_constraint_idx(), literal_occs_fn);
            }
            if (inconsistent()) {
                if (!keep) ++it;
            }
            else if (keep) {
                *it2 = *it;
                it2++;
            }
        }
        for (; it != end; ++it, ++it2) {
            *it2 = *it;                         
        }
        wlist.set_end(it2);        
    }

    
    // new n-ary clause management

    void lookahead::add_clause(clause const& c) {
        SASSERT(c.size() > 3);
        void * mem = m_allocator.allocate(nary::get_obj_size(c.size()));
        nary * n = new (mem) nary(c.size(), c.begin());
        m_nary_clauses.push_back(n);
        for (literal l : c) {
            m_nary[l.index()].push_back(n);
            m_nary_count[l.index()]++;
        }
    }


    void lookahead::propagate_clauses_searching(literal l) {
        // clauses where l is negative
        unsigned sz = m_nary_count[(~l).index()];
        literal lit;
        SASSERT(m_search_mode == lookahead_mode::searching);
        for (nary* n : m_nary[(~l).index()]) {
            if (sz-- == 0) break;
            unsigned len = n->dec_size();
            if (is_true(n->get_head())) continue;
            if (inconsistent()) continue;
            if (len <= 1) continue; // already processed
            // find the two unassigned literals, if any
            if (len == 2) {
                literal l1 = null_literal;
                literal l2 = null_literal;
                bool found_true = false;
                for (literal lit : *n) {
                    if (!is_fixed(lit)) {
                        if (l1 == null_literal) {
                            l1 = lit;
                        } 
                        else {
                            SASSERT(l2 == null_literal);
                            l2 = lit;
                            break;
                        }
                    }
                    else if (is_true(lit)) {
                        n->set_head(lit);
                        found_true = true;
                        break;
                    }
                }
                if (found_true) {
                    // skip, the clause will be removed when propagating on 'lit'
                }
                else if (l1 == null_literal) {
                    set_conflict();
                }
                else if (l2 == null_literal) {
                    // clause may get revisited during propagation, when l2 is true in this clause.
                    // m_removed_clauses.push_back(std::make_pair(~l, idx)); 
                    // remove_clause_at(~l, idx); 
                    propagated(l1);
                }
                else {
                    // extract binary clause. A unary or empty clause may get revisited, 
                    // but we skip it then because it is already handled as a binary clause.
                    //                    m_removed_clauses.push_back(std::make_pair(~l, idx)); // need to restore this clause.
                    //                    remove_clause_at(~l, idx); 
                    try_add_binary(l1, l2);
                }                
            }
        }
        // clauses where l is positive:
        sz = m_nary_count[l.index()];
        for (nary* n : m_nary[l.index()]) {
            if (sz-- == 0) break;
            remove_clause_at(l, *n);
        }
    }

    void lookahead::propagate_clauses_lookahead(literal l) {
        // clauses where l is negative
        unsigned sz = m_nary_count[(~l).index()];
        SASSERT(m_search_mode == lookahead_mode::lookahead1 ||
                m_search_mode == lookahead_mode::lookahead2);
        
        for (nary* n : m_nary[(~l).index()]) {
            if (sz-- == 0) break;
            unsigned nonfixed = n->dec_size();
            // if (is_true(n->get_head())) continue;
            if (inconsistent()) continue;
            if (nonfixed <= 1 && !is_true(n->get_head())) {
                bool found_conflict = true;
                for (literal lit : *n) {
                    if (!is_fixed(lit)) {
                        propagated(lit);
                        found_conflict = false;
                        break;
                    }
                    else if (is_true(lit)) {
                        n->set_head(lit);
                        found_conflict = false;
                        break;
                    }
                }
                if (found_conflict) {
                    set_conflict();
                    continue;
                }
            }
            if (m_search_mode == lookahead_mode::lookahead1) {
                //SASSERT(nonfixed >= 2);
                switch (m_config.m_reward_type) {
                case heule_schur_reward: {
                    double to_add = 0;
                    for (literal lit : *n) {
                        if (!is_fixed(lit)) {
                            to_add += literal_occs(lit);
                        }                        
                    }
                    m_lookahead_reward += pow(0.5, nonfixed) * to_add / nonfixed;                    
                    break;
                }
                case heule_unit_reward:
                    m_lookahead_reward += pow(0.5, nonfixed);
                    break;
                case march_cu_reward:
                    m_lookahead_reward += nonfixed >= 2 ? 3.3 * pow(0.5, nonfixed - 2) : 0.0;
                    break;
                case ternary_reward:
                    UNREACHABLE();
                    break;
                case unit_literal_reward:
                    break;
                }
            }
        }
        // clauses where l is positive:
        sz = m_nary_count[l.index()];
        for (nary* n : m_nary[l.index()]) {
            if (sz-- == 0) break;
            if (get_level(l) > get_level(n->get_head())) {
                n->set_head(l);
            }
        }
    }

    void lookahead::remove_clause_at(literal l, nary& n) {
        for (literal lit : n) {
            if (lit != l) {
                remove_clause(lit, n);
            }
        }
    }

    void lookahead::remove_clause(literal l, nary& n) {
        ptr_vector<nary>& pclauses = m_nary[l.index()];
        unsigned sz = m_nary_count[l.index()]--;
        for (unsigned i = sz; i > 0; ) {
            --i;
            if (&n == pclauses[i]) {
                std::swap(pclauses[i], pclauses[sz-1]);
                return;
            }
        }
        UNREACHABLE();
    }

    void lookahead::restore_clauses(literal l) {
        SASSERT(m_search_mode == lookahead_mode::searching);
        // increase the length of clauses where l is negative
        unsigned sz = m_nary_count[(~l).index()];
        for (nary* n : m_nary[(~l).index()]) {
            if (sz-- == 0) break;
            n->inc_size();
        }
        // add idx back to clause list where l is positive
        // add them back in the same order as they were inserted
        // in this way we can check that the clauses are the same.
        sz = m_nary_count[l.index()];
        ptr_vector<nary>& pclauses = m_nary[l.index()];
        for (unsigned i = sz; i-- > 0; ) {
            for (literal lit : *pclauses[i]) {
                if (lit != l) {
                    SASSERT(m_nary[lit.index()][m_nary_count[lit.index()]] == pclauses[i]);
                    m_nary_count[lit.index()]++;
                }
            }
        }        
    }

    void lookahead::propagate_clauses(literal l) {
        SASSERT(is_true(l));
        propagate_ternary(l);
        switch (m_search_mode) {
        case lookahead_mode::searching:
            propagate_clauses_searching(l);
            break;
        default:
            propagate_clauses_lookahead(l);
            break;
        }
        propagate_external(l);
    }   

    void lookahead::update_binary_clause_reward(literal l1, literal l2) {
        SASSERT(!is_false(l1));
        SASSERT(!is_false(l2));
        switch (m_config.m_reward_type) {
        case ternary_reward:
            m_lookahead_reward += (*m_heur)[l1.index()] * (*m_heur)[l2.index()];
            break;
        case heule_schur_reward:
            m_lookahead_reward += (literal_occs(l1) + literal_occs(l2)) / 8.0;
            break;
        case heule_unit_reward:
            m_lookahead_reward += 0.25;
            break;
        case march_cu_reward:
            m_lookahead_reward += 3.3;
            break;
        case unit_literal_reward:
            break;
        }
    }

    void lookahead::update_nary_clause_reward(clause const& c) {
        if (m_config.m_reward_type == ternary_reward && m_lookahead_reward != 0) {
            return;
        }
        literal const * l_it  = c.begin() + 2, *l_end = c.end();
        unsigned sz = 0;
        for (; l_it != l_end; ++l_it) {
            if (is_true(*l_it)) return;
            if (!is_false(*l_it)) ++sz;
        }
        switch (m_config.m_reward_type) {
        case heule_schur_reward: {
            SASSERT(sz > 0);
            double to_add = 0;
            for (literal l : c) {
                if (!is_false(l)) {
                    to_add += literal_occs(l);
                } 
            }
            m_lookahead_reward += pow(0.5, sz) * to_add / sz;
            break;
        }
        case heule_unit_reward:
            m_lookahead_reward += pow(0.5, sz);
            break;
        case march_cu_reward:
            m_lookahead_reward += 3.3 * pow(0.5, sz - 2);
            break;
        case ternary_reward:
            m_lookahead_reward = (double)0.001;            
            break;
        case unit_literal_reward:
            break;
        }
    }

    // Sum_{ clause C that contains ~l } 1 
    // FIXME: counts occurrences of ~l; misleading
    double lookahead::literal_occs(literal l) {
        double result = m_binary[l.index()].size();
        result += literal_big_occs(l);
        return result;
    }

    // Sum_{ clause C that contains ~l such that |C| > 2} 1 
    // FIXME: counts occurrences of ~l; misleading
    double lookahead::literal_big_occs(literal l) {
        double result = m_nary_count[(~l).index()];
        result += m_ternary_count[(~l).index()];
        return result;
    }

    void lookahead::get_clauses(literal_vector& clauses, unsigned max_clause_size) {
        // push binary clauses
        unsigned num_lits = m_s.num_vars() * 2;
        for (unsigned idx = 0; idx < num_lits; ++idx) {
            literal u = to_literal(idx);
            if (m_s.was_eliminated(u.var()) || is_false(u) || is_true(u)) continue;
            for (literal v : m_binary[idx]) {
                if (u.index() < v.index() && !m_s.was_eliminated(v.var()) && !is_false(v) && !is_true(v)) {
                    clauses.push_back(~u);
                    clauses.push_back(v);
                    clauses.push_back(null_literal);
                }
            }
        }
        // push ternary clauses
        for (unsigned idx = 0; idx < num_lits; ++idx) {
            literal u = to_literal(idx);
            if (is_true(u) || is_false(u)) continue;
            unsigned sz = m_ternary_count[u.index()];
            for (binary const& b : m_ternary[u.index()]) {
                if (sz-- == 0) break;
                if (u.index() > b.m_v.index() || u.index() > b.m_u.index())
                    continue;
                if (is_true(b.m_u) || is_true(b.m_v)) 
                    continue;
                if (is_false(b.m_u) && is_false(b.m_v))
                    continue;
                clauses.push_back(u);
                if (!is_false(b.m_u)) clauses.push_back(b.m_u);
                if (!is_false(b.m_v)) clauses.push_back(b.m_v);
                clauses.push_back(null_literal);            
            }
        }

        // push n-ary clauses
        for (unsigned idx = 0; idx < num_lits; ++idx) {
            literal u = to_literal(idx);
            unsigned sz = m_nary_count[u.index()];
            for (nary* n : m_nary[u.index()]) {
                if (sz-- == 0) break;
                unsigned sz0 = clauses.size();
                if (n->size() > max_clause_size) continue;
                for (literal lit : *n) {
                    if (is_true(lit)) {
                        clauses.shrink(sz0);
                        break;
                    }
                    if (!is_false(lit)) { 
                        clauses.push_back(lit);
                    }
                }
                if (clauses.size() > sz0) {
                    clauses.push_back(null_literal);
                }
            }
        }

        TRACE("sat",
              for (literal lit : clauses) {
                  if (lit == null_literal) {
                      tout << "\n";
                  }
                  else {
                      tout << lit << " ";
                  }
              }
              tout << "\n";
              m_s.display(tout);
              );
    }

    void lookahead::propagate_binary(literal l) {
        literal_vector const& lits = m_binary[l.index()];
        TRACE("sat", tout << l << " => " << lits << "\n";);
        for (literal lit : lits) {
            if (inconsistent()) break;
            assign(lit);
        }
    }

    void lookahead::propagate() {
        unsigned i = m_qhead;
        for (; i < m_trail.size() && !inconsistent(); ++i) {
            literal l = m_trail[i];
            TRACE("sat", tout << "propagate " << l << " @ " << m_level << "\n";);
            propagate_binary(l);
        }
        while (m_qhead < m_trail.size() && !inconsistent()) {
            propagate_clauses(m_trail[m_qhead++]);
        }
        SASSERT(m_qhead == m_trail.size() || (inconsistent() && m_qhead < m_trail.size()));
        //SASSERT(!missed_conflict());
        //VERIFY(!missed_propagation());
        TRACE("sat_verbose", display(tout << scope_lvl() << " " << (inconsistent()?"unsat":"sat") << "\n"););
    }


    void lookahead::compute_lookahead_reward() {
        TRACE("sat", display_lookahead(tout); );
        m_delta_decrease = pow(m_config.m_delta_rho, 1.0 / (double)m_lookahead.size());
        unsigned base = 2;
        bool change = true;
        literal last_changed = null_literal;
        unsigned ops = 0;
        m_max_ops = 100000;
        while (change && !inconsistent() && ops < m_max_ops) {
            change = false;
            IF_VERBOSE(10, verbose_stream() << "(sat.lookahead :compute-reward " << m_lookahead.size() << ")\n");
            for (unsigned i = 0; !inconsistent() && i < m_lookahead.size() && ops < m_max_ops; ++i) {
                checkpoint();
                ++ops;
                literal lit = m_lookahead[i].m_lit;
                if (lit == last_changed) {
                    SASSERT(!change);
                    break;
                }
                if (scope_lvl() == 1) {
                    IF_VERBOSE(30, verbose_stream() << scope_lvl() << " " << lit << " binary: " << m_binary_trail.size() << " trail: " << m_trail_lim.back() << "\n";);
                }
                unsigned level = base + m_lookahead[i].m_offset;
                unsigned dl_lvl = level;
                if (is_fixed_at(lit, c_fixed_truth) || is_true_at(lit, level)) continue;
                bool unsat = false;
                if (is_false_at(lit, level)) {
                    unsat = true;
                }
                else {
                    TRACE("sat", tout << "lookahead: " << lit << " @ " << m_lookahead[i].m_offset << "\n";);
                    reset_lookahead_reward(lit);
                    unsigned num_units = push_lookahead1(lit, level);
                    update_lookahead_reward(lit, level);
                    num_units += do_double(lit, dl_lvl);
                    if (dl_lvl > level) {
                        base = dl_lvl;
                        SASSERT(get_level(m_trail.back()) == base);
                    }
                    unsat = inconsistent();
                    pop_lookahead1(lit, num_units);
                }
                if (unsat) {
                    TRACE("sat", tout << "backtracking and setting " << ~lit << "\n";);
                    lookahead_backtrack();
                    assign(~lit);
                    propagate();
                    change = true;
                    last_changed = lit;
                    continue;
                }
                // if l was derived from lit and ~lit -> l, then l is a necessary assignment
                literal_vector necessary_lits;
                for (literal l : m_binary[(~lit).index()]) {
                    if (is_true_at(l, dl_lvl) && !is_fixed_at(l, c_fixed_truth)) {
                        necessary_lits.push_back(l);
                    }
                }
                if (!necessary_lits.empty()) {
                    change = true;
                    last_changed = lit;
                    lookahead_backtrack();
                    for (literal l : necessary_lits) {
                        if (inconsistent()) break;
                        assign(l);
                        propagate();
                    }
                }
                SASSERT(inconsistent() || !is_unsat());
            }
            if (c_fixed_truth - 2 * m_lookahead.size() < base) {
                break;
            }
            base += 2 * m_lookahead.size();
        }
        lookahead_backtrack();
        TRACE("sat", display_lookahead(tout); );
    }

    literal lookahead::select_literal() {
        literal l = null_literal;
        double h = 0;
        unsigned count = 1;
        for (unsigned i = 0; i < m_lookahead.size(); ++i) {
            literal lit = m_lookahead[i].m_lit;
            if (lit.sign() || !is_undef(lit)) {
                continue;
            }
            double diff1 = get_lookahead_reward(lit), diff2 = get_lookahead_reward(~lit);
            double mixd = mix_diff(diff1, diff2);

            if (mixd == h) ++count;
            if (mixd > h || (mixd == h && m_s.m_rand(count) == 0)) {
                CTRACE("sat", l != null_literal, tout << lit << " mix diff: " << mixd << "\n";);
                if (mixd > h) count = 1;
                h = mixd;
                l = diff1 < diff2 ? lit : ~lit;
            }
        }
        TRACE("sat", tout << "selected: " << l << "\n";);
        return l;
    }


    double lookahead::mix_diff(double l, double r) const {
        switch (m_config.m_reward_type) {
        case ternary_reward: return l + r + (1 << 10) * l * r; 
        case heule_schur_reward: return l * r;
        case heule_unit_reward: return l * r;
        case march_cu_reward: return 1024 * (1024 * l * r + l + r);
        case unit_literal_reward: return l * r;
        default: UNREACHABLE(); return l * r;
        }
    }

    void lookahead::reset_lookahead_reward(literal l) {

        m_lookahead_reward = 0;

        // inherit propagation effect from parent.
        literal p = get_parent(l);
        set_lookahead_reward(l, (p == null_literal || is_undef(p) || is_fixed_at(p, c_fixed_truth)) ?
                                0 : get_lookahead_reward(p));
    }

    void lookahead::update_lookahead_reward(literal l, unsigned level) {        
        if (m_lookahead_reward != 0) {
            inc_lookahead_reward(l, m_lookahead_reward);
        }
    }

    unsigned lookahead::do_double(literal l, unsigned& base) {
        unsigned num_units = 0;
        if (!inconsistent() && dl_enabled(l) && get_config().m_lookahead_double) {
            if (get_lookahead_reward(l) > m_delta_trigger) {
                if (dl_no_overflow(base)) {
                    ++m_stats.m_double_lookahead_rounds;
                    num_units = double_look(l, base);
                    if (!inconsistent()) {
                        m_delta_trigger = m_delta_fraction*get_lookahead_reward(l);
                        dl_disable(l);
                    }
                }
            }
            else {
                SASSERT(m_delta_decrease > 0.0);
                m_delta_trigger *= m_delta_decrease;
            }
        }
        return num_units;
    }

    unsigned lookahead::double_look(literal l, unsigned& base) {
        SASSERT(!inconsistent());
        SASSERT(dl_no_overflow(base));
        SASSERT(is_fixed_at(l, base));
        base += m_lookahead.size();
        unsigned dl_truth = base + m_lookahead.size() * m_config.m_dl_max_iterations;
        scoped_level _sl(*this, dl_truth);
        //SASSERT(get_level(m_trail.back()) == dl_truth);
        IF_VERBOSE(3, verbose_stream() << "(sat-lookahead :double " << l << " :depth " << m_trail_lim.size() << ")\n";);
        lookahead_backtrack();
        assign(l);
        propagate();
        unsigned old_sz = m_trail.size();
        bool change = true;
        literal last_changed = null_literal;
        unsigned num_iterations = 0;
        while (change && num_iterations < m_config.m_dl_max_iterations && !inconsistent()) {
            num_iterations++;
            for (auto const& lh : m_lookahead) {
                if (inconsistent()) break;
	        
                literal lit = lh.m_lit;
                if (lit == last_changed) {
                    SASSERT(change == false);
                    break;
                }
                unsigned level = base + lh.m_offset;
                if (level + m_lookahead.size() >= dl_truth) {
                    change = false;
                    break;
                }
                bool unsat = false;
                if (is_false_at(lit, level) && !is_fixed_at(lit, dl_truth)) {
                    unsat = true;
                }
                else {
                    if (is_fixed_at(lit, level)) continue;
                    unsat = push_lookahead2(lit, level);
                }
                if (unsat) {
                    TRACE("sat", tout << "unit: " << ~lit << "\n";);
                    ++m_stats.m_double_lookahead_propagations;
                    SASSERT(m_level == dl_truth);
                    lookahead_backtrack();
		    if (m_s.m_config.m_drat) validate_binary(~l, ~lit);
                    assign(~lit);
                    propagate();
                    change = true;
                    last_changed = lit;
                    m_wstack.push_back(~lit);
                }
            }
            base += 2 * m_lookahead.size();
            SASSERT(dl_truth >= base);
        }
        lookahead_backtrack();
        SASSERT(get_level(m_trail.back()) == dl_truth);
        SASSERT(m_level == dl_truth);
        base = dl_truth;
        return m_trail.size() - old_sz;
    }

    /**
       \brief check if literal occurs in a non-tautological reduced clause.
     */
    bool lookahead::in_reduced_clause(bool_var v) {
        return 
            in_reduced_clause(literal(v, false)) ||
            in_reduced_clause(literal(v, true));
    }

    bool lookahead::in_reduced_clause(literal lit) {
        if (lit == null_literal) return true;
        if (m_trail_lim.empty()) return true;
        unsigned sz = m_nary_count[lit.index()];
        for (nary* n : m_nary[lit.index()]) {
            if (sz-- == 0) break;
            if (!n->is_reduced()) continue;
            bool has_true = false;
            for (literal l : *n) {
                if (is_true(l)) {
                    has_true = true;
                    break;
                }
            }
            if (!has_true) return true;
        }
        
        auto const& tv = m_ternary[lit.index()];
        sz = tv.size();
        unsigned i = m_ternary_count[lit.index()];
        for (; i < sz; ++i) {
            binary const& b = tv[i];
            if (!is_true(b.m_u) && !is_true(b.m_v))
                return true;
        }
        return false;
    }

    void lookahead::validate_assign(literal l) {
        if (m_s.m_config.m_drat && m_search_mode == lookahead_mode::searching) {
            m_assumptions.push_back(l);
            m_s.m_drat.add(m_assumptions);
            m_assumptions.pop_back();
        }
    }

    void lookahead::assign(literal l) {
        SASSERT(m_level > 0);
        if (is_undef(l)) {
            TRACE("sat", tout << "assign: " << l << " @ " << m_level << " " << m_trail_lim.size() << " " << m_search_mode << "\n";);
            set_true(l);
            SASSERT(m_trail.empty() || get_level(m_trail.back()) >= get_level(l));
            m_trail.push_back(l);
            if (m_search_mode == lookahead_mode::searching) {
                m_stats.m_propagations++;
                TRACE("sat", tout << "removing free var v" << l.var() << "\n";);
                if (l.var() > m_freevars.max_var()) IF_VERBOSE(0, verbose_stream() << "bigger than max-var: " << l << " " << " " << m_freevars.max_var() << "\n";);
                if (!m_freevars.contains(l.var())) IF_VERBOSE(0, verbose_stream() << "does not contain: " << l << " eliminated: " << m_s.was_eliminated(l.var()) << "\n";);
                if (m_freevars.contains(l.var())) { m_freevars.remove(l.var()); }
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

    void lookahead::propagated(literal l) {
        assign(l);
        for (unsigned i = m_trail.size()-1; i < m_trail.size() && !inconsistent(); ++i) {
            literal l = m_trail[i];
            TRACE("sat", tout << "propagate " << l << " @ " << m_level << "\n";);
            propagate_binary(l);
        }
        if (m_search_mode == lookahead_mode::lookahead1) {
            m_wstack.push_back(l);
        }
    }

    bool lookahead::backtrack(literal_vector& trail) {
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

    lbool lookahead::search() {
        m_model.reset();
        scoped_level _sl(*this, c_fixed_truth);
        literal_vector trail;
        m_search_mode = lookahead_mode::searching;
        while (true) {
            TRACE("sat", display(tout););
            inc_istamp();
            checkpoint();
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
            IF_VERBOSE(1, display_search_string(););
            push(l, c_fixed_truth);
            trail.push_back(l);
            SASSERT(inconsistent() || !is_unsat());
        }
    }

    bool lookahead::backtrack(literal_vector& trail, svector<bool> & is_decision) {
        m_cube_state.m_backtracks++;
        while (inconsistent()) {
            if (trail.empty()) return false;
            if (is_decision.back()) {
                pop();
                trail.back().neg();
                assign(trail.back());
                is_decision.back() = false;
                propagate();
            }
            else {
                trail.pop_back();
                is_decision.pop_back();
            }
        }
        return true;
    }

    void lookahead::update_cube_statistics(statistics& st) {
        st.update("lh cube cutoffs", m_cube_state.m_cutoffs);
        st.update("lh cube conflicts", m_cube_state.m_conflicts);        
        st.update("lh cube backtracks", m_cube_state.m_backtracks);        
    }

    double lookahead::psat_heur() {
        double h = 0.0;
        for (bool_var x : m_freevars) {
            literal l(x, false);
            for (literal lit : m_binary[l.index()]) {
                h += l.index() > lit.index() ? 1.0 / m_config.m_cube_psat_clause_base : 0.0;
            }
            for (literal lit : m_binary[(~l).index()]) {
                h += l.index() > lit.index() ? 1.0 / m_config.m_cube_psat_clause_base : 0.0;
            }
            for (binary b : m_ternary[l.index()]) {
                h += l.index() > b.m_u.index() && l.index() > b.m_v.index() ?
                     1.0 / pow(m_config.m_cube_psat_clause_base, 2) :
                     0.0;
            }
            for (binary b : m_ternary[(~l).index()]) {
                h += l.index() > b.m_u.index() && l.index() > b.m_v.index() ?
                     1.0 / pow(m_config.m_cube_psat_clause_base, 2) :
                     0.0;
            }
        }
        for (nary * n : m_nary_clauses) {
            h += 1.0 / pow(m_config.m_cube_psat_clause_base, n->size() - 1);
        }
        h /= pow(m_freevars.size(), m_config.m_cube_psat_var_exp);
        IF_VERBOSE(10, verbose_stream() << "(sat-cube-psat :val " << h << ")\n";);
        return h;
    }

    bool lookahead::should_cutoff(unsigned depth) {
        return depth > 0 && 
            ((m_config.m_cube_cutoff == depth_cutoff && depth == m_config.m_cube_depth) ||
             (m_config.m_cube_cutoff == freevars_cutoff && m_freevars.size() <= m_init_freevars * m_config.m_cube_freevars) ||
             (m_config.m_cube_cutoff == psat_cutoff && psat_heur() >= m_config.m_cube_psat_trigger) ||
             (m_config.m_cube_cutoff == adaptive_freevars_cutoff && m_freevars.size() < m_cube_state.m_freevars_threshold) ||
             (m_config.m_cube_cutoff == adaptive_psat_cutoff && psat_heur() >= m_cube_state.m_psat_threshold));
    }

    lbool lookahead::cube(bool_var_vector& vars, literal_vector& lits, unsigned backtrack_level) {
        scoped_ext _scoped_ext(*this);
        lits.reset();
        bool is_first = m_cube_state.m_first;
        if (is_first) {
            m_select_lookahead_vars.reset();
            for (auto v : vars) {
                m_select_lookahead_vars.insert(v);
            }
            init_search();
            m_model.reset();
            m_cube_state.m_first = false;
        }        
        scoped_level _sl(*this, c_fixed_truth);
        m_search_mode = lookahead_mode::searching;
        unsigned depth = 0;
        // unsigned init_trail = m_trail.size();
        
        m_cube_state.reset_stats();
        if (!is_first) {
            goto pick_up_work;
        }

        while (true) {
            TRACE("sat", display(tout););
            checkpoint();
            inc_istamp();
            if (inconsistent()) {
                TRACE("sat", tout << "inconsistent: " << m_cube_state.m_cube << "\n";);
                m_cube_state.m_freevars_threshold = m_freevars.size();     
                m_cube_state.m_psat_threshold = m_config.m_cube_cutoff == adaptive_psat_cutoff ? psat_heur() : dbl_max;  // MN. only compute PSAT if enabled
                m_cube_state.inc_conflict();
                if (!backtrack(m_cube_state.m_cube, m_cube_state.m_is_decision)) {
                    return l_false; 
                }               
                continue;
            }
        pick_up_work:
            if (m_cube_state.m_cube.size() >= backtrack_level) {
                IF_VERBOSE(10, verbose_stream() << "(sat-cube :cube: " << m_cube_state.m_cube.size() << " :backtrack_level " << backtrack_level << ")\n";);
                while (m_cube_state.m_cube.size() >= backtrack_level) {
                    set_conflict();
                    backtrack(m_cube_state.m_cube, m_cube_state.m_is_decision);
                }
            }
            backtrack_level = UINT_MAX;
            depth = m_cube_state.m_cube.size();
            if (should_cutoff(depth)) {
                double dec = (1.0 - pow(m_config.m_cube_fraction, depth));
                m_cube_state.m_freevars_threshold *= dec;
                m_cube_state.m_psat_threshold *= 2.0 - dec;
                set_conflict();
                m_cube_state.inc_cutoff();
                lits.append(m_cube_state.m_cube);
                vars.reset();
                for (auto v : m_freevars) if (in_reduced_clause(v)) vars.push_back(v);
                backtrack(m_cube_state.m_cube, m_cube_state.m_is_decision);
                return l_undef;
            }
            int prev_nfreevars = m_freevars.size();
            double prev_psat = m_config.m_cube_cutoff == adaptive_psat_cutoff ? psat_heur() : dbl_max;  // MN. only compute PSAT if enabled
            literal lit = choose();
            if (inconsistent()) {
                TRACE("sat", tout << "inconsistent: " << m_cube_state.m_cube << "\n";);
                m_cube_state.m_freevars_threshold = prev_nfreevars;
                m_cube_state.m_psat_threshold = prev_psat;
                m_cube_state.inc_conflict();
                if (!backtrack(m_cube_state.m_cube, m_cube_state.m_is_decision)) {
                    return l_false;
                }
                continue;
            }
            if (lit == null_literal) {
                vars.reset();
                for (auto v : m_freevars) if (in_reduced_clause(v)) vars.push_back(v);
                m_model.reset();
                init_model();
                return l_true;
            }
            TRACE("sat", tout << "choose: " << lit << " cube: " << m_cube_state.m_cube << "\n";);
            ++m_stats.m_decisions;
            push(lit, c_fixed_truth);
            m_cube_state.m_cube.push_back(lit);
            m_cube_state.m_is_decision.push_back(true);
            SASSERT(inconsistent() || !is_unsat());
        }
        m_cube_state.reset();
        return l_undef;
    }


    void lookahead::display_lookahead_scores(std::ostream& out) {
        scoped_ext _scoped_ext(*this);
        m_select_lookahead_vars.reset();
        init_search();
        scoped_level _sl(*this, c_fixed_truth);
        m_search_mode = lookahead_mode::searching;
        literal l = choose_base();        
        if (l == null_literal) {
            out << "null\n";
            return;
        }
        for (auto const& l : m_lookahead) {
            literal lit = l.m_lit;
            if (!lit.sign() && is_undef(lit)) {
                double diff1 = get_lookahead_reward(lit);
                double diff2 = get_lookahead_reward(~lit);
                out << lit << " " << diff1 << " " << diff2 << "\n";
            }       
        }
    }


    void lookahead::init_model() {
        m_model.reset();
        for (unsigned i = 0; i < m_num_vars; ++i) {
            lbool val;
            literal lit(i, false);
            if (is_undef(lit)) {
                val = l_undef;
            }
            else if (is_true(lit)) {
                val = l_true;
            }
            else {
                val = l_false;
            }
            m_model.push_back(val);
        }
    }

    std::ostream& lookahead::display_cube(std::ostream& out, literal_vector const& cube) const {
        out << "c";
        for (literal l : cube) {
            out << " " << ~l;
        }
        return out << " 0\n";
    }

    std::ostream& lookahead::display_binary(std::ostream& out) const {
        for (unsigned i = 0; i < m_binary.size(); ++i) {
            literal_vector const& lits = m_binary[i];
            if (!lits.empty()) {
                out << to_literal(i) << " -> " << lits << "\n";
            }
        }
        return out;
    }

    std::ostream& lookahead::display_clauses(std::ostream& out) const {
        for (unsigned idx = 0; idx < m_ternary.size(); ++idx) {
            literal lit = to_literal(idx);
            unsigned sz = m_ternary_count[idx];
            for (binary const& b : m_ternary[idx]) {
                if (sz-- == 0) break;
                if (idx < b.m_u.index() && idx << b.m_v.index()) {
                    out << lit << " " << b.m_u << " " << b.m_v << "\n";
                }
            }
        }

        for (nary * n : m_nary_clauses) {
            for (literal l : *n) out << l << " ";
            out << "\n";
        }

        return out;
    }

    std::ostream& lookahead::display_values(std::ostream& out) const {
        for (literal l : m_trail) {
            out << l << "\n";
        }
        return out;
    }

    std::ostream& lookahead::display_lookahead(std::ostream& out) const {
        for (unsigned i = 0; i < m_lookahead.size(); ++i) {
            literal lit = m_lookahead[i].m_lit;
            unsigned offset = m_lookahead[i].m_offset;
            out << lit << "\toffset: " << offset;
            out << (is_undef(lit)?" undef": (is_true(lit) ? " true": " false"));
            out << " lookahead_reward: " << get_lookahead_reward(lit);
            out << "\n";
        }
        return out;
    }

    void lookahead::init_search() {
        m_search_mode = lookahead_mode::searching;
        scoped_level _sl(*this, c_fixed_truth);
        init(m_s.m_config.m_lookahead_use_learned);            
    }

    void lookahead::checkpoint() {
        if (!m_rlimit.inc()) {
            throw solver_exception(Z3_CANCELED_MSG);
        }
        if (memory::get_allocation_size() > m_s.m_config.m_max_memory) {
            throw solver_exception(Z3_MAX_MEMORY_MSG);
        }
    }



    literal lookahead::choose() {
        return choose_base();
    }

    literal lookahead::choose_base() {
        literal l = null_literal;
        while (l == null_literal && !inconsistent()) {
            pre_select();
            if (m_lookahead.empty()) {
                break;
            }
            compute_lookahead_reward();
            if (inconsistent()) {
                break;
            }
            l = select_literal();
        }
        SASSERT(inconsistent() || !is_unsat());
        return l;
    }

    /**
       \brief simplify set of clauses by extracting units from a lookahead at base level.
    */
    void lookahead::simplify(bool learned) {
        scoped_ext _scoped_ext(*this);
        SASSERT(m_prefix == 0);
        SASSERT(m_watches.empty());
        m_search_mode = lookahead_mode::searching;
        scoped_level _sl(*this, c_fixed_truth);
        init(learned);                
        if (inconsistent()) return;
        inc_istamp();            
        choose_base();        
        if (inconsistent()) return;
        SASSERT(m_trail_lim.empty());
        unsigned num_units = 0;
        
        for (unsigned i = 0; i < m_trail.size() && !m_s.inconsistent(); ++i) {
            literal lit = m_trail[i];
            if (m_s.value(lit) == l_undef && !m_s.was_eliminated(lit.var())) {
                m_s.assign_scoped(lit);
                ++num_units;
            }
        }        
        IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :units " << num_units << " :propagations " << m_stats.m_propagations << ")\n";);
         
        if (m_s.inconsistent()) return;

        if (num_units > 0) {
            m_s.propagate_core(false);
            m_s.m_simplifier(false);
        }

        if (select(0)) {
            get_scc();
            if (!inconsistent()) {
                normalize_parents();
                literal_vector roots;
                bool_var_vector to_elim;
                for (unsigned i = 0; i < m_num_vars; ++i) {
                    roots.push_back(literal(i, false));
                }
                for (auto const& c : m_candidates) {
                    bool_var v = c.m_var;
                    literal q(v, false);
                    literal p = get_parent(q);
                    if (p != null_literal && p.var() != v && !m_s.is_external(v) && 
                        !m_s.was_eliminated(v) && !m_s.was_eliminated(p.var())) {
                        to_elim.push_back(v);
                        roots[v] = p;
                        VERIFY(get_parent(p) == p);
                        VERIFY(get_parent(~p) == ~p);
                    }
                }
                IF_VERBOSE(1, verbose_stream() << "(sat-lookahead :equivalences " << to_elim.size() << ")\n";);
                elim_eqs elim(m_s);
                elim(roots, to_elim);

                if (learned && get_config().m_lookahead_simplify_bca) {
                    add_hyper_binary();
                }                
            }
        }   
        m_lookahead.reset();    
    }


    /**
       \brief reduction based on binary implication graph
     */

    void lookahead::add_hyper_binary() {

        unsigned num_lits = m_s.num_vars() * 2;
        unsigned num_bins = 0;

        typedef std::pair<unsigned, unsigned> u_pair;
        hashtable<u_pair, pair_hash<unsigned_hash, unsigned_hash>, default_eq<u_pair> > imp;
        for (unsigned idx = 0; idx < num_lits; ++idx) {
            literal u = get_parent(to_literal(idx));
            if (null_literal != u) {
                for (watched const& w : m_s.m_watches[idx]) {
                    if (!w.is_binary_clause()) continue;
                    literal v = get_parent(w.get_literal());
                    if (null_literal != v) {
                        imp.insert(std::make_pair(u.index(), v.index()));
                    }
                }
            }
        }

        big big(m_s.m_rand);
        big.init(m_s, true);
        svector<std::pair<literal, literal>> candidates;

        unsigned_vector bin_size(num_lits);
        for (unsigned idx : m_binary_trail) {
            bin_size[idx]++;
        }
        for (unsigned idx = 0; idx < num_lits; ++idx) {
            literal u = to_literal(idx);
            if (u != get_parent(u)) continue;
            if (m_s.was_eliminated(u.var())) continue;
            literal_vector const& lits = m_binary[idx];
            for (unsigned sz = bin_size[idx]; sz > 0; --sz) {
                literal v = lits[lits.size() - sz];
                if (v == get_parent(v) && 
                    !m_s.was_eliminated(v.var()) && 
                    !imp.contains(std::make_pair(u.index(), v.index())) && 
                    !big.connected(u, v)) {
                    candidates.push_back(std::make_pair(u, v));
                }
            }
        }

        for (unsigned count = 0; count < 5; ++count) {
            big.init(m_s, true);
            unsigned k = 0;
            union_find_default_ctx ufctx;
            union_find<union_find_default_ctx> uf(ufctx);
            for (unsigned i = 0; i < num_lits; ++i) uf.mk_var();
            for (unsigned j = 0; j < candidates.size(); ++j) {
                literal u = candidates[j].first;
                literal v = candidates[j].second;
                if (!big.connected(u, v)) {
                    if (uf.find(u.index()) != uf.find(v.index())) {
                        ++num_bins;
                        uf.merge(u.index(), v.index());
                        uf.merge((~u).index(), (~v).index());
                        VERIFY(!m_s.was_eliminated(u.var()));
                        VERIFY(!m_s.was_eliminated(v.var()));
                        m_s.mk_clause(~u, v, true);
                    }
                    else {
                        candidates[k] = candidates[j];
                        ++k;
                    }
                }
            }
            // std::cout << candidates.size() << " -> " << k << "\n";
            if (k == candidates.size()) break;
            candidates.shrink(k);
            if (k == 0) break;
        }
        
        IF_VERBOSE(10, verbose_stream() << "(sat-lookahead :bca " << num_bins << ")\n";);
        m_stats.m_bca += num_bins;
    }

    void lookahead::normalize_parents() {
        literal_vector roots;
        for (unsigned i = 0; i < m_num_vars; ++i) {
            literal lit(i, false);
            roots.push_back(lit);
            roots.push_back(~lit);
            SASSERT(roots[lit.index()] == lit);
        }
        for (auto const& c : m_candidates) {
            bool_var v = c.m_var;
            literal p(v, false);
            literal q = get_parent(p);
            literal r = ~get_parent(~p);
            if (q != r) {
                if (q.var() < r.var()) {
                    roots[q.index()] = r;
                }
                else {
                    roots[r.index()] = q;
                }
            }
        }
        for (auto const& c : m_candidates) {
            literal p(c.m_var, false);
            literal q = roots[get_parent(p).index()];
            set_parent(p, q);
            set_parent(~p, ~q);
        }
    }

    std::ostream& lookahead::display_summary(std::ostream& out) const {
        out << "Prefix: " << pp_prefix(m_prefix, m_trail_lim.size()) << "\n";
        out << "Level: " << m_level << "\n";
        out << "Free vars: " << m_freevars.size() << "\n";
        return out;
    }

    std::ostream& lookahead::display(std::ostream& out) const {
        display_summary(out);
        display_values(out);
        display_binary(out);
        display_clauses(out);
        out << "free vars: ";
        for (bool_var b : m_freevars) out << b << " ";
        out << "\n";
        clause_allocator dummy_allocator;
        for (unsigned i = 0; i < m_watches.size(); ++i) {
            watch_list const& wl = m_watches[i];
            if (!wl.empty()) {
                sat::display_watch_list(out << to_literal(i) << " -> ", dummy_allocator, wl, nullptr);
                out << "\n";
            }
        }
        return out;
    }

    model const& lookahead::get_model() {
        if (m_model.empty()) {
            init_model();
        }
        return m_model;
    }

    void lookahead::init_config() {
        m_config.m_reward_type = m_s.m_config.m_lookahead_reward;
        m_config.m_cube_cutoff = m_s.m_config.m_lookahead_cube_cutoff;
        m_config.m_cube_fraction = m_s.m_config.m_lookahead_cube_fraction;
        m_config.m_cube_depth = m_s.m_config.m_lookahead_cube_depth;
        m_config.m_cube_freevars = m_s.m_config.m_lookahead_cube_freevars;
        m_config.m_cube_psat_var_exp = m_s.m_config.m_lookahead_cube_psat_var_exp;
        m_config.m_cube_psat_clause_base = m_s.m_config.m_lookahead_cube_psat_clause_base;
        m_config.m_cube_psat_trigger = m_s.m_config.m_lookahead_cube_psat_trigger;
    }

    void lookahead::collect_statistics(statistics& st) const {
        st.update("lh bool var", m_vprefix.size());
        // TBD: keep count of ternary and >3-ary clauses.
        st.update("lh bca", m_stats.m_bca);
        st.update("lh add binary", m_stats.m_add_binary);
        st.update("lh del binary", m_stats.m_del_binary);
        st.update("lh propagations", m_stats.m_propagations);
        st.update("lh decisions", m_stats.m_decisions);
        st.update("lh windfalls", m_stats.m_windfall_binaries);
        st.update("lh double lookahead propagations", m_stats.m_double_lookahead_propagations);
        st.update("lh double lookahead rounds", m_stats.m_double_lookahead_rounds);
    }

}
