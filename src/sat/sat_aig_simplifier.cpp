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

#include "util/union_find.h"
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
                std::cout << "not validated: " << clause << "\n";
                s.display(std::cout);
                std::string line;
                std::getline(std::cin, line);                
            }
        }
    };

    void aig_simplifier::ensure_validator() {
        if (!m_validator) {
            std::cout << "init validator\n";
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
        if (false) {
            ensure_validator();
            std::function<void(literal_vector const& clause)> _on_add = 
                [this](literal_vector const& clause) { 
                std::cout << "add " << clause << "\n"; m_validator->validate(clause); 
            };
            m_aig_cuts.set_on_clause_add(_on_add);
        }
        else if (s.get_config().m_drat) {
            std::function<void(literal_vector const& clause)> _on_add = 
                [this](literal_vector const& clause) { s.m_drat.add(clause); };
            std::function<void(literal_vector const& clause)> _on_del = 
                [this](literal_vector const& clause) { s.m_drat.del(clause); };
            m_aig_cuts.set_on_clause_add(_on_add);
            m_aig_cuts.set_on_clause_del(_on_del);
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
            if (m_config.m_full || true) clauses2aig();
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
        for (; m_config.m_full && m_trail_size < s.init_trail_size(); ++m_trail_size) {
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
        if (m_config.m_full || true) clauses.append(s.learned());
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

        map<cut const*, unsigned, cut::hash_proc, cut::eq_proc> cut2id;
                
        union_find_default_ctx ctx;
        union_find<> uf(ctx), uf2(ctx);
        for (unsigned i = 2*s.num_vars(); i--> 0; ) uf.mk_var();
        auto add_eq = [&](literal l1, literal l2) {
            uf.merge(l1.index(), l2.index());
            uf.merge((~l1).index(), (~l2).index());
        };
        bool new_eq = false;
        for (unsigned i = cuts.size(); i-- > 0; ) {
            for (auto& c : cuts[i]) {
                unsigned j = 0;
                if (m_config.m_full && c.is_true()) {
                    if (s.value(i) == l_undef) {
                        literal lit(i, false);
                        validate_unit(lit);
                        IF_VERBOSE(2, verbose_stream() << "new unit " << lit << "\n");
                        s.assign_unit(lit);
                        ++m_stats.m_num_units;
                    }
                    break;
                }
                if (m_config.m_full && c.is_false()) {
                    if (s.value(i) == l_undef) {
                        literal lit(i, true);
                        validate_unit(lit);
                        IF_VERBOSE(2, verbose_stream() << "new unit " << lit << "\n");
                        s.assign_unit(lit);
                        ++m_stats.m_num_units;
                    }
                    break;
                }
                if (cut2id.find(&c, j)) {
                    VERIFY(i != j);
                    literal u(i, false);
                    literal v(j, false);
                    IF_VERBOSE(0,
                               verbose_stream() << u << " " << c << "\n";
                               verbose_stream() << v << ": ";
                               for (cut const& d : cuts[v.var()]) verbose_stream() << d << "\n";);

                    certify_equivalence(u, v, c);                    
                    //validate_eq(u, v);
                    add_eq(u, v);
                    TRACE("aig_simplifier", tout << u << " == " << v << "\n";);                    
                    new_eq = true;
                    break;
                }
                if (true || m_config.m_full) {
                    cut nc(c);
                    nc.negate();
                    if (cut2id.find(&nc, j)) {
                        VERIFY(i != j); // maybe possible with don't cares
                        literal u(i, false);
                        literal v(j, true);
                        certify_equivalence(u, v, c);
                        // validate_eq(u, v);
                        add_eq(u, v);
                        TRACE("aig_simplifier", tout << u << " == " << v << "\n";);
                        new_eq = true;
                        break;
                    }
                }
                cut2id.insert(&c, i);                
            }
        }        
        if (!new_eq) {
            return;
        }
        new_eq = false;
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
        if (!new_eq) {
            return;
        }
        elim_eqs elim(s);
        elim(uf2);        
    }

    /**
     * Equilvalences modulo cuts are not necessarily DRAT derivable.
     * To ensure that there is a DRAT derivation we create all resolvents
     * of the LUT clauses until deriving binary u or ~v and ~u or v.
     * each resolvent is DRAT derivable because there are two previous lemmas that
     * contain complementary literals.
     */
    void aig_simplifier::certify_equivalence(literal u, literal v, cut const& c) {
        if (!s.m_config.m_drat) return;
        
        vector<literal_vector> clauses;
        std::function<void(literal_vector const& clause)> on_clause = 
            [&](literal_vector const& clause) { SASSERT(clause.back().var() == u.var()); clauses.push_back(clause); };        
        m_aig_cuts.cut2def(on_clause, c, u);

        // create C or u or ~v for each clause C or u
        // create C or ~u or v for each clause C or ~u
        for (auto& clause : clauses) { 
            literal w = clause.back();
            SASSERT(w.var() == u.var());
            clause.push_back(w == u ? ~v : v); 
            s.m_drat.add(clause);
        }
        // create C or ~u or v for each clause 
        unsigned i = 0, sz = clauses.size();
        for (; i < sz; ++i) {
            literal_vector clause(clauses[i]);
            clause[clause.size()-2] = ~clause[clause.size()-2];
            clause[clause.size()-1] = ~clause[clause.size()-1];
            clauses.push_back(clause);
            s.m_drat.add(clause);
        }
        
        // create all resolvents over C. C is assumed to 
        // contain all combinations of some set of literals.
        i = 0; sz = clauses.size();
        while (sz - i > 2) {
            SASSERT((sz & (sz - 1)) == 0);
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
        for (auto const& clause : clauses) {
            if (clause.size() > 2) {
                s.m_drat.del(clause);
            }
        }                
    }

    /**
     * collect pairs of variables that occur in cut sets.
     */
    void aig_simplifier::collect_pairs(vector<cut_set> const& cuts) {
        m_pairs.reset();
        for (unsigned k = cuts.size(); k-- > 0; ) {
            for (auto const& c : cuts[k]) {
                for (unsigned i = c.size(); i-- > 0; ) {
                    for (unsigned j = i; j-- > 0; ) {
                        m_pairs.insert(var_pair(c[i],c[j]));
                    }
                }
            }
        }
    }
    
    /**
     * compute masks for pairs.
     */
    void aig_simplifier::add_masks_to_pairs() {
        big b(s.rand());
        b.init(s, true);
        for (auto& p : m_pairs) {
            literal u(p.u, false), v(p.v, false);
            // u -> v, then u & ~v is impossible
            if (b.connected(u, v)) {
                add_mask(u, ~v, p);
            }
            else if (b.connected(u, ~v)) {                
                add_mask(u, v, p);
            }
            else if (b.connected(~u, v)) {
                add_mask(~u, ~v, p);
            }
            else if (b.connected(~u, ~v)) {
                add_mask(~u, v, p);
            }
            else {
                memset(p.masks, 0xFF, var_pair::size());
            }
        }
    }

    /*
     * compute masks for each possible occurrence of u, v within 2-6 elements.
     * combinaions relative to u.sign(), v.sign() are impossible.
     */ 
    void aig_simplifier::add_mask(literal u, literal v, var_pair& p) {
        unsigned offset = 0;
        bool su = u.sign(), sv = v.sign();
        for (unsigned k = 2; k <= 6; ++k) {
            for (unsigned i = 0; i < k; ++i) {
                for (unsigned j = i + 1; j < k; ++j) {
                    // convert su, sv, k, i, j into a mask for 2^k bits.
                    // for outputs 
                    p.masks[offset++] = 0;
                }
            }
        }
    }

    /**
     * apply obtained masks to cut sets.
     */
    void aig_simplifier::apply_masks() {
        
    }

    void aig_simplifier::collect_statistics(statistics& st) const {
        st.update("sat-aig.eqs",  m_stats.m_num_eqs);
        st.update("sat-aig.cuts", m_stats.m_num_cuts);
        st.update("sat-aig.ands", m_stats.m_num_ands);
        st.update("sat-aig.ites", m_stats.m_num_ites);
        st.update("sat-aig.xors", m_stats.m_num_xors);
    }

    void aig_simplifier::validate_unit(literal lit) {
        ensure_validator();
        m_validator->validate(1, &lit);
    }

    void aig_simplifier::validate_eq(literal a, literal b) {
        ensure_validator();
        literal lits1[2] = { a, ~b };
        literal lits2[2] = { ~a, b };
        m_validator->validate(2, lits1);
        m_validator->validate(2, lits1);
    }

    
}

