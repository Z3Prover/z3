/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_bceq.cpp

Abstract:

    Find equivalent literals based on blocked clause decomposition.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-27.


Revision History:

--*/
#include"sat_bceq.h"
#include"sat_solver.h"
#include"trace.h"
#include"bit_vector.h"
#include"map.h"
#include"sat_elim_eqs.h"

namespace sat {
    
    bceq::bceq(solver & s):
        m_solver(s) {
    }

    void bceq::register_clause(clause* cls) {
        m_clauses.setx(cls->id(), cls, 0);
    }

    void bceq::unregister_clause(clause* cls) {
        m_clauses.setx(cls->id(), 0, 0);
    }

    void bceq::init() {
        m_clauses.reset();
        m_bin_clauses.reset();
        m_L.reset();
        m_R.reset();
        m_L_blits.reset();
        m_R_blits.reset();
        clause * const* it = m_solver.begin_clauses();
        clause * const* end = m_solver.end_clauses();
        for (; it != end; ++it) {
            clause* cls = *it;
            if (!cls->was_removed()) {
                m_use_list->insert(*cls);
                register_clause(cls);
            }
        }
        bin_clauses bc;
        m_solver.collect_bin_clauses(bc, false); // exclude roots.
        literal lits[2];
        for (unsigned i = 0; i < bc.size(); ++i) {
            lits[0] = bc[i].first;
            lits[1] = bc[i].second;
            clause* cls = m_solver.m_cls_allocator.mk_clause(2, lits, false);
            m_use_list->insert(*cls);
            m_bin_clauses.push_back(cls);
            register_clause(cls);
        }
        TRACE("sat",
              for (unsigned i = 0; i < m_clauses.size(); ++i) {
                  clause const* cls = m_clauses[i];
                  if (cls) tout << *cls << "\n";
              });
    }

    void bceq::pure_decompose() {
        // while F != empty
        //   pick a clause and variable x in clause.
        //   get use list U1 of x and U2 of ~x
        //   assume |U1| >= |U2|
        //   add U1 to clause set.
        for (unsigned i = 0; i < m_clauses.size(); ++i) {
            clause* cls = m_clauses[i];
            if (cls) {
                SASSERT(i == cls->id()); 
                pure_decompose((*cls)[0]);
                SASSERT(!m_clauses[i]);
            }
        }
        m_L.reverse();
        m_L_blits.reverse();
    }

    void bceq::pure_decompose(literal lit) {
        clause_use_list& pos = m_use_list->get(lit);
        clause_use_list& neg = m_use_list->get(~lit); 
        unsigned sz1 = m_L.size();
        unsigned sz2 = m_R.size();
        pure_decompose(pos, m_L);
        pure_decompose(neg, m_R);
        unsigned delta1 = m_L.size() - sz1;
        unsigned delta2 = m_R.size() - sz2;
        if (delta1 < delta2) {
            m_L_blits.resize(sz1+delta2, ~lit);
            m_R_blits.resize(sz2+delta1,  lit);
            for (unsigned i = 0; i < delta1; ++i) {
                std::swap(m_L[sz1 + i], m_R[sz2 + i]);
            }
            for (unsigned i = delta1; i < delta2; ++i) {
                m_L.push_back(m_R[sz2 + i]);
            }
            m_R.resize(sz2 + delta1);
            std::swap(delta1, delta2);
        }
        else {
            m_L_blits.resize(sz1+delta1,  lit);
            m_R_blits.resize(sz2+delta2, ~lit);
        }
        TRACE("bceq", tout << lit << " " << "pos: " << delta1 << " " << "neg: " << delta2 << "\n";);
    }
    
    void bceq::pure_decompose(clause_use_list& uses, svector<clause*>& clauses) {
        clause_use_list::iterator it = uses.mk_iterator();
        while (!it.at_end()) {
            clause& cls = it.curr();
            if (!cls.was_removed() && m_clauses[cls.id()]) {
                clauses.push_back(&cls);
                m_clauses[cls.id()] = 0;
            }
            it.next();
        }
    }

    void bceq::post_decompose() {
        m_marked.reset();
        m_marked.resize(2*m_solver.num_vars(), false);
        use_list ul;
        use_list* save = m_use_list;
        m_use_list = &ul;
        ul.init(m_solver.num_vars());
        for (unsigned i = 0; i < m_L.size(); ++i) {
            ul.insert(*m_L[i]);
        }
#define MOVE_R_TO_L                             \

        // cheap pass: add clauses from R in order
        // such that they are blocked with respect to
        // predecessors.
        m_removed.reset();
        for (unsigned i = 0; i < m_R.size(); ++i) {
            literal lit = find_blocked(*m_R[i]);
            if (lit != null_literal) {
                m_L.push_back(m_R[i]);                  
                m_L_blits.push_back(lit);               
                ul.insert(*m_R[i]);                     
                m_R[i] = m_R.back();                    
                m_R_blits[i] = m_R_blits.back();        
                m_R.pop_back();                         
                m_R_blits.pop_back();                   
                --i;                                    
            }
        }
        // expensive pass: add clauses from R as long
        // as BCE produces the empty set of clauses.
        for (unsigned i = 0; i < m_R.size(); ++i) {
            if (bce(*m_R[i])) {
                m_R[i] = m_R.back();
                m_R_blits[i] = m_R_blits.back();
                m_R.pop_back();
                m_R_blits.pop_back();
                --i;
            }
        }        
        m_use_list = save;
    }

    bool bceq::bce(clause& cls) {
        svector<bool> live_clauses;
        use_list ul;
        use_list* save = m_use_list;
        m_use_list = &ul;
        ul.init(m_solver.num_vars());
        for (unsigned i = 0; i < m_L.size(); ++i) {
            ul.insert(*m_L[i]);
        }
        ul.insert(cls);
        svector<clause*> clauses(m_L), new_clauses;
        literal_vector blits(m_L_blits), new_blits;
        clauses.push_back(&cls);
        blits.push_back(null_literal);
        bool removed = false;
        m_removed.reset();
        do {
            removed = false;
            for (unsigned i = 0; i < clauses.size(); ++i) {
                clause& cls = *clauses[i];
                literal lit = find_blocked(cls);
                if (lit != null_literal) {
                    m_removed.setx(cls.id(), true, false);
                    new_clauses.push_back(&cls);
                    new_blits.push_back(lit);
                    removed = true;
                    clauses[i] = clauses.back();
                    blits[i] = blits.back();
                    clauses.pop_back();
                    blits.pop_back();                    
                    --i;
                }
            }
        }
        while (removed);
        if (clauses.empty()) {
            m_L.reset();
            m_L_blits.reset();
            new_clauses.reverse();
            new_blits.reverse();
            m_L.append(new_clauses);
            m_L_blits.append(new_blits);
        }
        if (!clauses.empty()) std::cout << "Number left after BCE: " << clauses.size() << "\n";
        return clauses.empty();
    }

    literal bceq::find_blocked(clause const& cls) {
        TRACE("bceq", tout << cls << "\n";);

        unsigned sz = cls.size();
        for (unsigned i = 0; i < sz; ++i) {
            m_marked[(~cls[i]).index()] = true;
        }
        literal result = null_literal;
        for (unsigned i = 0; i < sz; ++i) {
            literal lit = cls[i];
            if (is_blocked(lit)) {
                TRACE("bceq", tout << "is blocked " << lit << " : " << cls << "\n";);
                result = lit;
                break;
            }
        }
        for (unsigned i = 0; i < sz; ++i) {
            m_marked[(~cls[i]).index()] = false;
        }
        return result;
    }

    bool bceq::is_blocked(literal lit) const {
        clause_use_list& uses = m_use_list->get(~lit);
        clause_use_list::iterator it = uses.mk_iterator();
        while (!it.at_end()) {
            clause const& cls = it.curr();
            unsigned sz = cls.size();
            bool is_axiom = m_removed.get(cls.id(), false);
            for (unsigned i = 0; !is_axiom && i < sz; ++i) {
                is_axiom = m_marked[cls[i].index()] && cls[i] != ~lit;
            }

            TRACE("bceq", tout << "resolvent " << lit << " : " << cls << " " << (is_axiom?"axiom":"non-axiom") << "\n";);
            if (!is_axiom) {
                return false;
            }
            it.next();
        }
        return true;
    }


    void bceq::init_rbits() {
        m_rbits.reset();        
        for (unsigned i = 0; i < m_solver.num_vars(); ++i) {
            uint64 lo = m_rand() + (m_rand() << 16);
            uint64 hi = m_rand() + (m_rand() << 16);
            m_rbits.push_back(lo + (hi << 32ULL));
        }
    }

    void bceq::init_reconstruction_stack() {
        m_rstack.reset();
        m_bstack.reset();
        // decomposition already creates a blocked stack in the proper order.
        m_rstack.append(m_L);
        m_bstack.append(m_L_blits);
    }
    
    uint64 bceq::eval_clause(clause const& cls) const {
        uint64 b = 0;
        unsigned sz = cls.size();
        for (unsigned i = 0; i < sz; ++i) {
            literal lit = cls[i];
            uint64 val = m_rbits[lit.var()];                
            if (lit.sign()) {
                val = ~val;
            }
            b |= val;
        }
        return b;
    }

    void bceq::sat_sweep() {
        init_rbits();
        init_reconstruction_stack();
        for (unsigned i = 0; i < m_rstack.size(); ++i) {
            clause const& cls = *m_rstack[i];
            literal block_lit = m_bstack[i];
            uint64 b = eval_clause(cls);
            // v = 0, b = 0 -> v := 1
            // v = 0, b = 1 -> v := 0
            // v = 1, b = 0 -> v := 0
            // v = 1, b = 1 -> v := 1
            m_rbits[block_lit.var()] ^= ~b;

        }
        DEBUG_CODE(verify_sweep(););
    }

    void bceq::verify_sweep() {
        for (unsigned i = 0; i < m_L.size(); ++i) {
            uint64 b = eval_clause(*m_L[i]);
            SASSERT((~b) == 0);
        }
    }

    struct u64_hash { unsigned operator()(uint64 u) const { return (unsigned)u; } };
    
    struct u64_eq { bool operator()(uint64 u1, uint64 u2) const { return u1 == u2; } };

    void bceq::extract_partition() {
        unsigned num_vars = m_solver.num_vars();
        map<uint64, unsigned, u64_hash, u64_eq> table;
        union_find<> union_find(m_union_find_ctx);
        for (unsigned i = 0; i < num_vars; ++i) {
            m_s->mk_var(true, true);
            union_find.mk_var();
        }
        for (unsigned i = 0; i < m_L.size(); ++i) {
            m_s->mk_clause(m_L[i]->size(), m_L[i]->begin());
        }
        for (unsigned i = 0; i < num_vars; ++i) {
            uint64 val = m_rbits[i];
            unsigned index;
            if (table.find(val, index)) {
                union_find.merge(i, index);
            }
            else if (table.find(~val, index)) {
                union_find.merge(i, index);
            }
            else {
                table.insert(val, i);
            }
        }
        TRACE("sat", union_find.display(tout););

        //
        // Preliminary version:
        // A more appropriate is to walk each pair, 
        // and refine partition based on SAT results.
        // 
        for (unsigned i = 0; i < num_vars; ++i) {
            if (!union_find.is_root(i)) continue;
            unsigned v = union_find.next(i);
            unsigned last_v = UINT_MAX;
            if (!m_solver.was_eliminated(i)) {
                last_v = i;
            }
            while (v != i) {
                if (!m_solver.was_eliminated(v)) {
                    if (last_v != UINT_MAX) {
                        if (check_equality(v, last_v)) {
                            // last_v was eliminated.
                            
                        }
                        else {
                            // TBD: refine partition.
                        }
                    }
                    last_v = v;
                }
                v = union_find.next(v);
            }
        }
    }

    bool bceq::check_equality(unsigned v1, unsigned v2) {
        TRACE("sat", tout << "check: " << v1 << " = " << v2 << "\n";);
        uint64 val1 = m_rbits[v1];
        uint64 val2 = m_rbits[v2];
        literal l1 = literal(v1, false);
        literal l2 = literal(v2, false);
        if (val1 != val2) {
            SASSERT(val1 == ~val2);
            l2.neg();
        }
        if (is_already_equiv(l1, l2)) {
            TRACE("sat", tout << "Already equivalent: " << l1 << " " << l2 << "\n";);
            return false;
        }

        literal lits[2];
        lits[0] = l1;
        lits[1] = ~l2;
        lbool is_sat = m_s->check(2, lits);
        if (is_sat == l_false) {
            lits[0] = ~l1;
            lits[1] = l2;
            is_sat = m_s->check(2, lits);
        }
        if (is_sat == l_false) {
            TRACE("sat", tout << "Found equivalent: " << l1 << " " << l2 << "\n";);
            assert_equality(l1, l2);
        }
        else {
            TRACE("sat", tout << "Not equivalent: " << l1 << " " << l2 << "\n";);
            // TBD: if is_sat == l_true, then refine partition.
        }
        return is_sat == l_false;
    }

    bool bceq::is_already_equiv(literal l1, literal l2) {
        watch_list const& w1 = m_solver.get_wlist(l1);
        bool found = false;
        for (unsigned i = 0; !found && i < w1.size(); ++i) {
            watched const& w = w1[i];            
            found = w.is_binary_clause() && w.get_literal() == ~l2;
        }
        if (!found) return false;
        found = false;
        watch_list const& w2 = m_solver.get_wlist(~l1);
        for (unsigned i = 0; !found && i < w2.size(); ++i) {
            watched const& w = w2[i];            
            found = w.is_binary_clause() && w.get_literal() == l2;
        }
        return found;
    }

    void bceq::assert_equality(literal l1, literal l2) {
        if (l2.sign()) {
            l1.neg();
            l2.neg();
        }
        literal_vector roots;
        bool_var_vector vars;
        for (unsigned i = 0; i < m_solver.num_vars(); ++i) {
            roots.push_back(literal(i, false));
        }
        roots[l2.var()] = l1;
        vars.push_back(l2.var());
        elim_eqs elim(m_solver);
        for (unsigned i = 0; i < vars.size(); ++i) {
            std::cout << "var: " << vars[i] << " root: " << roots[vars[i]] << "\n";
        }
        elim(roots, vars);
    }

    void bceq::cleanup() {
        m_solver.del_clauses(m_bin_clauses.begin(), m_bin_clauses.end());
        m_bin_clauses.reset();
    }


    void bceq::operator()() {
        if (!m_solver.m_config.m_bcd) return;
        flet<bool> _disable_bcd(m_solver.m_config.m_bcd, false);
        flet<bool> _disable_min(m_solver.m_config.m_minimize_core, false);
        flet<bool> _disable_opt(m_solver.m_config.m_optimize_model, false);
        flet<unsigned> _bound_maxc(m_solver.m_config.m_max_conflicts, 1500);

        use_list     ul;        
        solver       s(m_solver.m_params, 0);
        s.m_config.m_bcd            = false;
        s.m_config.m_minimize_core  = false;
        s.m_config.m_optimize_model = false;
        s.m_config.m_max_conflicts  = 1500;
        m_use_list = &ul;
        m_s = &s;
        ul.init(m_solver.num_vars());
        init();
        pure_decompose();
        post_decompose();
        std::cout << "Decomposed set " << m_L.size() << " rest: " << m_R.size() << "\n";

        TRACE("sat",
              tout << "Decomposed set " << m_L.size() << "\n";
              for (unsigned i = 0; i < m_L.size(); ++i) {
                  clause const* cls = m_L[i];
                  if (cls) tout << *cls << "\n";
              }
              tout << "remainder " << m_R.size() << "\n";
              for (unsigned i = 0; i < m_R.size(); ++i) {
                  clause const* cls = m_R[i];
                  if (cls) tout << *cls << "\n";
              }
              );
        sat_sweep();
        extract_partition();
        cleanup();
    }
};
