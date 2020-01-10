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
            unsigned ne = s.m_stats.m_num_eqs - m_num_eqs;
            unsigned nu = s.m_stats.m_num_units - m_num_units;
            unsigned nc = s.m_stats.m_num_cuts - m_num_cuts;
            IF_VERBOSE(2, 
                       verbose_stream() << "(sat.aig-simplifier";
                       if (ne > 0) verbose_stream() << " :num-eqs "   << ne;
                       if (nu > 0) verbose_stream() << " :num-units " << nu;
                       if (nc > 0) verbose_stream() << " :num-cuts "  << nc;
                       verbose_stream() << " :mb " << mem_stat() << m_watch << ")\n");
        }
    };

    aig_simplifier::aig_simplifier(solver& s):
        s(s), 
        m_trail_size(0) {        
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
        for (; m_trail_size < s.init_trail_size(); ++m_trail_size) {
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
        clauses.append(s.learned());
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
            m_stats.m_num_cuts += cuts[i].size();

            for (auto& cut : cuts[i]) {
                unsigned j = 0;
                if (cut.is_true()) {
                    if (s.value(i) == l_undef) {
                        IF_VERBOSE(2, verbose_stream() << "!!!new unit " << literal(i, false) << "\n");
                        s.assign_unit(literal(i, false));
                        ++m_stats.m_num_units;
                    }
                    break;
                }
                if (cut.is_false()) {
                    if (s.value(i) == l_undef) {
                        IF_VERBOSE(2, verbose_stream() << "!!!new unit " << literal(i, true) << "\n");
                        s.assign_unit(literal(i, true));
                        ++m_stats.m_num_units;
                    }
                    break;
                }
                if (cut2id.find(&cut, j)) {
                    if (i == j) std::cout << "dup: " << i << "\n";
                    VERIFY(i != j);
                    literal v(i, false);
                    literal w(j, false);
                    add_eq(v, w);
                    TRACE("aig_simplifier", tout << v << " == " << ~w << "\n";);
                    new_eq = true;
                    break;
                }
                cut.negate();
                if (cut2id.find(&cut, j)) {
                    literal v(i, false);
                    literal w(j, true);
                    add_eq(v, w);
                    TRACE("aig_simplifier", tout << v << " == " << w << "\n";);
                    new_eq = true;
                    break;
                }
                cut.negate();
                cut2id.insert(&cut, i);                
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

    void aig_simplifier::collect_statistics(statistics& st) const {
        st.update("sat-aig.eqs",  m_stats.m_num_eqs);
        st.update("sat-aig.cuts", m_stats.m_num_cuts);
        st.update("sat-aig.ands", m_stats.m_num_ands);
        st.update("sat-aig.ites", m_stats.m_num_ites);
        st.update("sat-aig.xors", m_stats.m_num_xors);
    }
    
}

