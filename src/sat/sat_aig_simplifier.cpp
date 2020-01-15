/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_simplifier.cpp

  Abstract:
   
    extract AIG definitions from clauses
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#include "sat/sat_aig_simplifier.h"
#include "sat/sat_xor_finder.h"
#include "sat/sat_elim_eqs.h"

namespace sat {
    
    struct aig_simplifier::report {
        aig_simplifier& s;
        stopwatch       m_watch;
        unsigned        m_num_eqs, m_num_units, m_num_cuts;
        
        report(aig_simplifier& s): s(s) { 
            m_watch.start(); 
            m_num_eqs   = s.m_stats.m_num_eqs;
            m_num_units = s.m_stats.m_num_units;
            m_num_cuts  = s.m_stats.m_num_cuts;
        }
        ~report() {
            unsigned ne = s.m_stats.m_num_eqs   - m_num_eqs;
            unsigned nu = s.m_stats.m_num_units - m_num_units;
            unsigned nc = s.m_stats.m_num_cuts  - m_num_cuts;
            IF_VERBOSE(2, 
                       verbose_stream() << "(sat.aig-simplifier";
                       if (ne > 0) verbose_stream() << " :num-eqs "   << ne;
                       if (nu > 0) verbose_stream() << " :num-units " << nu;
                       if (nc > 0) verbose_stream() << " :num-cuts "  << nc;
                       verbose_stream() << " :mb " << mem_stat() << m_watch << ")\n");
        }
    };

    struct aig_simplifier::validator {
        solver& _s;
        params_ref p;
        literal_vector m_assumptions;

        validator(solver& _s, params_ref const& p): _s(_s), p(p) {
        }

        void validate(unsigned n, literal const* clause) {
            validate(literal_vector(n, clause));
        }

        void validate(literal_vector const& clause) {
            if (clause.size() == 2 && clause[0] == ~clause[1]) return;
            solver s(p, _s.rlimit());
            s.copy(_s, false);
            IF_VERBOSE(10, verbose_stream() << "validate: " << clause << "\n");
            m_assumptions.reset();
            for (literal lit : clause) m_assumptions.push_back(~lit);           
            lbool r = s.check(clause.size(), m_assumptions.c_ptr());
            if (r != l_false) {
                IF_VERBOSE(0, 
                           verbose_stream() << "not validated: " << clause << "\n";
                           s.display(verbose_stream()););
                std::string line;
                std::getline(std::cin, line);                
            }
        }
    };

    void aig_simplifier::ensure_validator() {
        if (!m_validator) {
            params_ref p;
            p.set_bool("aig", false);
            p.set_bool("drat.check_unsat", false);
            p.set_sym("drat.file", symbol());
            p.set_uint("max_conflicts", 10000);
            m_validator = alloc(validator, s, p);
        }
    }

    aig_simplifier::aig_simplifier(solver& _s):
        s(_s), 
        m_trail_size(0),
        m_validator(nullptr) {  
        if (s.get_config().m_drat) {
            std::function<void(literal_vector const& clause)> _on_add = 
                [this](literal_vector const& clause) { s.m_drat.add(clause); };
            std::function<void(literal_vector const& clause)> _on_del = 
                [this](literal_vector const& clause) { s.m_drat.del(clause); };
            m_aig_cuts.set_on_clause_add(_on_add);
            m_aig_cuts.set_on_clause_del(_on_del);
        }
        else if (m_config.m_validate_cuts) {
            ensure_validator();
            std::function<void(literal_vector const& clause)> _on_add = 
                [this](literal_vector const& clause) { 
                m_validator->validate(clause); 
            };
            m_aig_cuts.set_on_clause_add(_on_add);
        }
    }

    aig_simplifier::~aig_simplifier() {
        dealloc(m_validator);
    }

    void aig_simplifier::add_and(literal head, unsigned sz, literal const* lits) {
        m_aig_cuts.add_node(head, and_op, sz, lits);
        m_stats.m_num_ands++;
    }

    //      head == l1 or l2 or l3 
    // <=> 
    //     ~head == ~l1 and ~l2 and ~l3
    void aig_simplifier::add_or(literal head, unsigned sz, literal const* lits) {
        m_lits.reset();
        m_lits.append(sz, lits);
        for (unsigned i = 0; i < sz; ++i) m_lits[i].neg();
        m_aig_cuts.add_node(~head, and_op, sz, m_lits.c_ptr());
        m_stats.m_num_ands++;
    }

    void aig_simplifier::add_xor(literal head, unsigned sz, literal const* lits) {
        m_aig_cuts.add_node(head, xor_op, sz, lits);
        m_stats.m_num_xors++;
    }

    void aig_simplifier::add_ite(literal head, literal c, literal t, literal e) {
        literal lits[3] = { c, t, e };
        m_aig_cuts.add_node(head, ite_op, 3, lits);
        m_stats.m_num_ites++;
    }

    void aig_simplifier::add_iff(literal head, literal l1, literal l2) {
        literal lits[2] = { l1, ~l2 };
        m_aig_cuts.add_node(head, xor_op, 2, lits);
        m_stats.m_num_xors++;
    }

    void aig_simplifier::set_root(bool_var v, literal r) {
        m_aig_cuts.set_root(v, r);
    }

    void aig_simplifier::operator()() {
        report _report(*this);
        TRACE("aig_simplifier", s.display(tout););
        unsigned n = 0, i = 0;
        ++m_stats.m_num_calls;
        do {
            n = m_stats.m_num_eqs + m_stats.m_num_units;
            clauses2aig();
            aig2clauses();
            ++i;
        }
        while (i < m_stats.m_num_calls && n < m_stats.m_num_eqs + m_stats.m_num_units);
    }

    /**
       \brief extract AIG definitions from clauses
       Ensure that they are sorted and variables have unique definitions.
     */
    void aig_simplifier::clauses2aig() {

        // update units
        for (; m_config.m_enable_units && m_trail_size < s.init_trail_size(); ++m_trail_size) {
            literal lit = s.trail_literal(m_trail_size);
            m_aig_cuts.add_node(lit, and_op, 0, 0);
        }
               
        std::function<void (literal head, literal_vector const& ands)> on_and = 
            [&,this](literal head, literal_vector const& ands) {
            m_aig_cuts.add_node(head, and_op, ands.size(), ands.c_ptr());
            m_stats.m_num_ands++;
        };
        std::function<void (literal head, literal c, literal t, literal e)> on_ite = 
            [&,this](literal head, literal c, literal t, literal e) {            
            literal args[3] = { c, t, e };            
            m_aig_cuts.add_node(head, ite_op, 3, args);
            m_stats.m_num_ites++;
        };
        aig_finder af(s);
        af.set(on_and);
        af.set(on_ite);
        clause_vector clauses(s.clauses());
        if (m_config.m_learned2aig) clauses.append(s.learned());
        af(clauses);

        std::function<void (literal_vector const&)> on_xor = 
            [&,this](literal_vector const& xors) {
            SASSERT(xors.size() > 1);
            unsigned max_level = xors.back().var();
            unsigned index = xors.size() - 1;
            for (unsigned i = index; i-- > 0; ) {
                literal l = xors[i];
                if (l.var() > max_level) {
                    max_level = l.var();
                    index = i;
                }
            }
            // head + t1 + t2 + .. = 1 
            // <=> 
            // ~head = t1 + t2 + ..
            literal head = ~xors[index];
            unsigned sz = xors.size() - 1;
            for (unsigned i = xors.size(); i-- > 0; ) {
                if (i != index) 
                    m_lits.push_back(xors[i]);
            }
            m_aig_cuts.add_node(head, xor_op, sz, m_lits.c_ptr());
            m_lits.reset();
            m_stats.m_num_xors++;            
        };
        xor_finder xf(s);
        xf.set(on_xor);
        xf(clauses);       
    }

    void aig_simplifier::aig2clauses() {
        vector<cut_set> const& cuts = m_aig_cuts();
        m_stats.m_num_cuts = m_aig_cuts.num_cuts();
        add_dont_cares(cuts);
        cuts2equiv(cuts);
        cuts2implies(cuts);
    }

    void aig_simplifier::cuts2equiv(vector<cut_set> const& cuts) {
        map<cut const*, unsigned, cut::hash_proc, cut::eq_proc> cut2id;                
        bool new_eq = false;
        union_find_default_ctx ctx;
        union_find<> uf(ctx);

        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf.mk_var();
        auto add_eq = [&](literal l1, literal l2) {
            uf.merge(l1.index(), l2.index());
            uf.merge((~l1).index(), (~l2).index());
            new_eq = true;
        };

        for (unsigned i = cuts.size(); i-- > 0; ) {
            literal u(i, false);
            for (auto& c : cuts[i]) {
                unsigned j = 0;
                cut nc(c);
                nc.negate();
                if (m_config.m_enable_units && c.is_true()) {
                    assign_unit(c, u);
                }
                else if (m_config.m_enable_units && c.is_false()) {
                    assign_unit(nc, ~u);
                }
                else if (cut2id.find(&c, j)) {
                    literal v(j, false);
                    assign_equiv(c, u, v);
                    add_eq(u, v);
                }
                else if (cut2id.find(&nc, j)) {
                    literal v(j, true);
                    assign_equiv(c, u, v);
                    add_eq(u, v);
                }
                else {
                    cut2id.insert(&c, i);
                }
            }
        }        
        if (new_eq) {
            uf2equiv(uf);
        }
    }

    void aig_simplifier::assign_unit(cut const& c, literal lit) {
        if (s.value(lit) != l_undef) 
            return;
        validate_unit(lit);
        IF_VERBOSE(2, verbose_stream() << "new unit " << lit << "\n");
        s.assign_unit(lit);
        certify_unit(lit, c);
        ++m_stats.m_num_units;        
    }

    void aig_simplifier::assign_equiv(cut const& c, literal u, literal v) {
        if (u.var() == v.var()) return;
        IF_VERBOSE(10, verbose_stream() << u << " " << v << " " << c << "\n";);
        TRACE("aig_simplifier", tout << u << " == " << v << "\n";);                            
        certify_equivalence(u, v, c);                    
        validate_eq(u, v);
    }

    /**
     * Convert a union-find over literals into input for eim_eqs.
     */
    void aig_simplifier::uf2equiv(union_find<> const& uf) {
        union_find_default_ctx ctx;
        union_find<> uf2(ctx);
        bool new_eq = false;
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf2.mk_var();
        // extract equivalences over non-eliminated literals.
        for (unsigned idx = 0; idx < uf.get_num_vars(); ++idx) {
            if (!uf.is_root(idx) || 1 == uf.size(idx)) continue;
            literal root = null_literal;
            unsigned first = idx;
            do {
                literal lit = to_literal(idx);
                if (!s.was_eliminated(lit)) {
                    if (root == null_literal) {
                        root = lit;
                    }
                    else {
                        uf2.merge(lit.index(), root.index());
                        new_eq = true;
                        ++m_stats.m_num_eqs;
                    }
                }
                idx = uf.next(idx);
            }
            while (first != idx);
        }
        if (new_eq) {
            elim_eqs elim(s);
            elim(uf2);        
        }
    }

    /**
     * Extract binary clauses from cuts.
     * A bit encoding of a LUT of u 
     * that sets a subset of bits for LUT' of v establishes
     * that u implies v.
     */
    void aig_simplifier::cuts2implies(vector<cut_set> const& cuts) {
        if (!m_config.m_learn_implies) return;
        vector<vector<std::pair<unsigned, cut const*>>> var_tables;
        map<cut const*, unsigned, cut::dom_hash_proc, cut::dom_eq_proc> cut2tables;
        unsigned j = 0;
        big big(s.rand());
        big.init(s, true);
        for (auto const& cs : cuts) {
            for (auto const& c : cs) {
                if (c.is_false() || c.is_true()) 
                    continue;
                if (!cut2tables.find(&c, j)) {
                    j = var_tables.size();
                    var_tables.push_back(vector<std::pair<unsigned, cut const*>>());
                    cut2tables.insert(&c, j);
                }
                var_tables[j].push_back(std::make_pair(cs.var(), &c));
            }
        }
        for (unsigned i = 0; i < var_tables.size(); ++i) {
            auto const& vt = var_tables[i];
            for (unsigned j = 0; j < vt.size(); ++j) {
                literal u(vt[j].first, false);
                cut const& c1 = *vt[j].second;
                cut nc1(c1);
                nc1.negate();
                uint64_t t1 = c1.table();
                uint64_t n1 = nc1.table();
                for (unsigned k = j + 1; k < vt.size(); ++k) {
                    literal v(vt[k].first, false);
                    cut const& c2 = *vt[k].second;                
                    uint64_t t2 = c2.table();
                    uint64_t n2 = c2.ntable();
                    if (t1 == t2 || t1 == n2) {
                        // already handled
                    }
                    else if ((t1 | t2) == t2) {
                        learn_implies(big, c1, u, v);
                    }
                    else if ((t1 | n2) == n2) {
                        learn_implies(big, c1, u, ~v);
                    }
                    else if ((n1 | t2) == t2) {
                        learn_implies(big, nc1, ~u, v);
                    }
                    else if ((n1 | n2) == n2) {
                        learn_implies(big, nc1, ~u, ~v);
                    }
                }
            }
        }
    }

    void aig_simplifier::learn_implies(big& big, cut const& c, literal u, literal v) {
        if (u == ~v) {
            assign_unit(c, v);
            return;
        }
        if (u == v) { 
            return;
        }
        bin_rel q, p(~u, v);
        if (m_bins.find(p, q) && q.op != none) 
            return;
        if (big.connected(u, v)) 
            return;
        for (auto const& w : s.get_wlist(u))
            if (w.is_binary_clause() && v == w.get_literal())
                return;
        certify_implies(u, v, c);
        s.mk_clause(~u, v, true);
        // m_bins owns reference to ~u or v created by certify_implies
        m_bins.insert(p); 
    }

    void aig_simplifier::track_binary(bin_rel const& p) {
        if (!s.m_config.m_drat) 
            return;
        literal u, v;
        p.to_binary(u, v);
        track_binary(u, v);
    }

    void aig_simplifier::untrack_binary(bin_rel const& p) {
        if (!s.m_config.m_drat) 
            return;
        literal u, v;
        p.to_binary(u, v);
        untrack_binary(u, v);
    }

    void aig_simplifier::track_binary(literal u, literal v) {
        if (s.m_config.m_drat) {
            s.m_drat.add(u, v, true);
        }
    }

    void aig_simplifier::untrack_binary(literal u, literal v) {
        if (s.m_config.m_drat) {
            s.m_drat.del(u, v);
        }
    }

    void aig_simplifier::certify_unit(literal u, cut const& c) {
        certify_implies(~u, u, c);
    }

    /**
     * Equilvalences modulo cuts are not necessarily DRAT derivable.
     * To ensure that there is a DRAT derivation we create all resolvents
     * of the LUT clauses until deriving binary u or ~v and ~u or v.
     * each resolvent is DRAT derivable because there are two previous lemmas that
     * contain complementary literals.
     */
    void aig_simplifier::certify_equivalence(literal u, literal v, cut const& c) {
        certify_implies(u, v, c);
        certify_implies(v, u, c);
    }

    /**
     * certify that u implies v, where c is the cut for u.
     * Then every position in c where u is true, it has to be 
     * the case that v is too.
     * Where u is false, v can have any value.
     * Thus, for every clause C or u', where u' is u or ~u,
     * it follows that C or ~u or v
     */
    void aig_simplifier::certify_implies(literal u, literal v, cut const& c) {
        if (!s.m_config.m_drat) return;
        
        vector<literal_vector> clauses;
        std::function<void(literal_vector const& clause)> on_clause = 
            [&,this](literal_vector const& clause) { 
            SASSERT(clause.back().var() == u.var()); 
            clauses.push_back(clause);
            clauses.back().back() = ~u;
            if (~u != v) clauses.back().push_back(v);
            s.m_drat.add(clauses.back());
        };        
        m_aig_cuts.cut2def(on_clause, c, u);

        // create all resolvents over C. C is assumed to 
        // contain all combinations of some set of literals.
        unsigned i = 0, sz = clauses.size();
        while (sz - i > 1) {
            SASSERT((sz & (sz - 1)) == 0 && "sz is a power of 2");
            for (; i < sz; ++i) {
                auto const& clause = clauses[i];
                if (clause[0].sign()) {
                    literal_vector cl(clause.size() - 1, clause.c_ptr() + 1);
                    clauses.push_back(cl);
                    s.m_drat.add(cl);
                }
            }
            i = sz;
            sz = clauses.size();
        }

        IF_VERBOSE(10, for (auto const& clause : clauses) verbose_stream() << clause << "\n";);

        // once we established equivalence, don't need auxiliary clauses for DRAT.
        clauses.pop_back();
        for (auto const& clause : clauses) {
            s.m_drat.del(clause);            
        }                      
    }

    void aig_simplifier::add_dont_cares(vector<cut_set> const& cuts) {
        if (!m_config.m_enable_dont_cares) 
            return;
        cuts2bins(cuts);
        bins2dont_cares();
        dont_cares2cuts(cuts);        
    }

    /**
     * Collect binary relations between variables that occur in cut sets.
     */
    void aig_simplifier::cuts2bins(vector<cut_set> const& cuts) {
        svector<bin_rel> dcs;
        for (auto const& p : m_bins) {
            if (p.op != none) 
                dcs.push_back(p);
        }
        m_bins.reset();
        for (auto const& cs : cuts) {
            for (auto const& c : cs) {
                for (unsigned i = c.size(); i-- > 0; ) {
                    for (unsigned j = i; j-- > 0; ) {
                        m_bins.insert(bin_rel(c[j],c[i]));
                    }
                }
            }
        }
        // don't lose previous don't cares
        for (auto const& p : dcs) {
            if (m_bins.contains(p)) {
                m_bins.insert(p);
            }
            else {
                untrack_binary(p);
            }
        }
    }
    
    /**
     * Compute masks for binary relations.
     */
    void aig_simplifier::bins2dont_cares() {
        big b(s.rand());
        b.init(s, true);
        for (auto& p : m_bins) {
            if (p.op != none) continue;
            literal u(p.u, false), v(p.v, false);
            // u -> v, then u & ~v is impossible
            if (b.connected(u, v)) {
                p.op = pn;
            }
            else if (b.connected(u, ~v)) {                
                p.op = pp;
            }
            else if (b.connected(~u, v)) {
                p.op = nn;
            }
            else if (b.connected(~u, ~v)) {
                p.op = np;
            }
            if (p.op != none) {
                track_binary(p);
            }
        }
        IF_VERBOSE(2, {
                unsigned n = 0; for (auto const& p : m_bins) if (p.op != none) ++n;
                verbose_stream() << n << " / " << m_bins.size() << " don't cares\n";
            });
    }

    /**
     * Loop over cuts, if it is possible to add a new don't care combination 
     * to a cut, then ensure that the variable is "touched" so that it participates
     * in the next propagation.
     */
    void aig_simplifier::dont_cares2cuts(vector<cut_set> const& cuts) {
        for (auto& cs : cuts) {
            for (auto const& c : cs) {
                if (add_dont_care(c)) {
                    m_aig_cuts.touch(cs.var());
                    m_stats.m_num_dont_care_reductions++;
                }
            }
        }
    }

    /**
     * compute masks for position i, j and op-code p.op
     * For the don't care combination false, false, the first don't care
     * position is 0. If it is true, false, the first don't care position
     * is the position that encodes the first occurrence where i is true.
     * It is 2^i. Cases for false, true and true, true are similar.
     * Don't care positions are spaced apart by 2^{j+1}, 
     * where j is the second variable position.
     */ 
    uint64_t aig_simplifier::op2dont_care(unsigned i, unsigned j, bin_rel const& p) {
        SASSERT(i < j && j < 6);
        if (p.op == none) return 0ull;
        // first position of mask is offset into output bits contributed by i and j
        bool i_is_0 = (p.op == np || p.op == nn);
        bool j_is_0 = (p.op == pn || p.op == nn);
        uint64_t first = (i_is_0 ? 0 : (1 << i)) + (j_is_0 ? 0 : (1 << j));
        uint64_t inc = 1ull << (j + 1);
        uint64_t r = 1ull << first; 
        while (inc < 64ull) { r |= (r << inc); inc *= 2; }
        return r;
    }

    /**
     * Apply obtained dont_cares to cut sets.
     * The don't care bits are added to the LUT, so that the
     * output is always 1 on don't care combinations.
     */
    bool aig_simplifier::add_dont_care(cut const & c) {
        uint64_t dc = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            for (unsigned j = i + 1; j < c.size(); ++j) {
                bin_rel p(c[i], c[j]);
                if (m_bins.find(p, p) && p.op != none) {
                    dc |= op2dont_care(i, j, p);
                }
            }
        }        
        return (dc != c.dont_care()) && (c.add_dont_care(dc), true);
    }

    void aig_simplifier::collect_statistics(statistics& st) const {
        st.update("sat-aig.eqs",  m_stats.m_num_eqs);
        st.update("sat-aig.cuts", m_stats.m_num_cuts);
        st.update("sat-aig.ands", m_stats.m_num_ands);
        st.update("sat-aig.ites", m_stats.m_num_ites);
        st.update("sat-aig.xors", m_stats.m_num_xors);
        st.update("sat-aig.dc-reduce", m_stats.m_num_dont_care_reductions);
    }

    void aig_simplifier::validate_unit(literal lit) {
        if (!m_config.m_validate_lemmas) return;
        ensure_validator();
        m_validator->validate(1, &lit);
    }

    void aig_simplifier::validate_eq(literal a, literal b) {
        if (!m_config.m_validate_lemmas) return;
        ensure_validator();
        literal lits1[2] = { a, ~b };
        literal lits2[2] = { ~a, b };
        m_validator->validate(2, lits1);
        m_validator->validate(2, lits2);
    }

    
}

