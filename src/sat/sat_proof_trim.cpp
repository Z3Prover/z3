/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_proof_trim.cpp

  Abstract:
   
    The proof is trimmed by re-running the proof steps and collecting justified literals
    at level 0. The proof is obtained by back-tracing the justificiations attached to literals.

  Author:

    Nikolaj Bjorner 2023-10-04

--*/

#include "sat/sat_proof_trim.h"

namespace sat {


    /**
       Pseudo-code from Gurfinkel, Vizel, FMCAD 2014
       Input: trail (a0,d0), ..., (an,dn) = ({},bot)
       Output: reduced trail - result                                                                           
    */        

    vector<std::pair<unsigned, unsigned_vector>> proof_trim::trim() {
        m_result.reset();
        m_propagated.resize(num_vars(), false);


        IF_VERBOSE(10, s.display(verbose_stream() << "trim\n"));

        auto const& [id, cl, clp, is_add, is_initial] = m_trail.back();
        SASSERT(cl.empty());
        m_result.push_back({id, unsigned_vector()});
        conflict_analysis_core(m_conflict, m_conflict_clause);
        m_trail.pop_back();
        
        for (unsigned i = m_trail.size(); i-- > 0; ) {            
            auto const& [id, cl, clp, is_add, is_initial] = m_trail[i];
            if (!is_add) {
                revive(cl, clp);
                continue;
            }            
            IF_VERBOSE(10, s.display(verbose_stream()));
            prune_trail(cl, clp);
            IF_VERBOSE(10, s.display(verbose_stream() << "\n"));
            del(cl, clp);
            if (!in_core(cl)) 
                continue;
            IF_VERBOSE(4, verbose_stream() << cl << " in-core " << in_core(cl) << ": "; for (auto const& [k,v] : m_clauses) verbose_stream() << "{" << v.m_clauses << "} "; verbose_stream() << "\n");

            m_result.push_back({id, unsigned_vector()});
            m_in_deps.reset();
            if (is_initial)
                continue;
            conflict_analysis_core(cl, clp);            
        }
        m_result.reverse();
        return m_result;
    }
    
    void proof_trim::del(literal_vector const& cl, clause* cp) {
        CTRACE("sat", cp, tout << "del " << *cp << "\n");
        if (cp) 
            s.detach_clause(*cp);
        else 
            del(cl);
    }

    /**
     * cl is on the trail if there is some literal l that is implied by cl
     * Remove all clauses after cl that are in the cone of influence of cl.
     * The coi is defined inductively: C is in coi of cl if it contains ~l
     * or it contains ~l' where l' is implied by a clause in the coi of cl.
     * Possible optimization: 
     * - check if clause contains a literal that is on implied on the trail
     *   if it doesn't contain any such literal, bypass the trail adjustment.
     */

    void proof_trim::prune_trail(literal_vector const& cl, clause* cp) {
        m_in_clause.reset();
        m_in_coi.reset();

        // verbose_stream() << "prune trail " << cl << "\n";
        
        if (cl.empty())
            return;

        for (literal lit : cl) 
            m_in_clause.insert(lit.index());

        auto unassign_literal = [&](literal l) {
            m_in_coi.insert((~l).index());
            s.m_assignment[l.index()] = l_undef;
            s.m_assignment[(~l).index()] = l_undef;
        };
        
        bool on_trail = false;
        unsigned j = 0;
        for (unsigned i = 0; i < s.trail_size(); ++i) {
            literal l = s.trail_literal(i);
            if (m_in_clause.contains(l.index())) {
                SASSERT(!on_trail);
                on_trail = true;
                unassign_literal(l);
                continue;
            }
            if (!on_trail) {
                s.m_trail[j++] = s.m_trail[i];
                continue;
            }
            
            auto js = s.get_justification(l);
            bool in_coi = false;
            if (js.is_clause())
                for (literal lit : s.get_clause(js))
                    in_coi |= m_in_coi.contains(lit.index());                
            else if (js.is_binary_clause())
                in_coi = m_in_coi.contains(js.get_literal().index());
            else if (js.is_none()) {                
                verbose_stream() << "none " << js << "\n";
            }
            else if (js.is_ext_justification()) {
                verbose_stream() << js << "\n";
                UNREACHABLE(); // approach does not work for external justifications
            }
            else {
                verbose_stream() << js << "\n";
                UNREACHABLE(); // approach does not work for external justifications
            }
            
            if (in_coi) 
                unassign_literal(l);
            else
                s.m_trail[j++] = s.m_trail[i];
        }            
        s.m_trail.shrink(j);
        // verbose_stream() << "trail after " << s.m_trail << "\n";
        s.m_inconsistent = false; 
        s.m_qhead = s.m_trail.size();
        s.propagate(false);
    }


    /**
       The current state is in conflict.
       Chase justifications for conflict to extract clauses that are in coi of conflict.


       Assume:
       F | G, ~C |- []
       Let T (trail) be the extension of G, ~C that derives the empty clause.
       T := G, ~C, l1:j1, l2:j2, ..., lk:jk
       The goal is to extract clauses in T that are used to derive C.
       This is achieved by collecting all literals from j1, j2, ... jk 
       and the conflict clause that are at level below ~C and using the clauses that justify those literals. 
      
             
       Example:
       C = c or d or e
       G = a
       F = { ~a or ~b, c or d or b, ... }
       T = ~b : ~a or ~b, ~c: D ~d : D , ~e : D, b : c or d or b 
       where D is a decision marker (justification::NONE)
       The conflict depends on the first two clauses in F.
             
       All literals that are are used in clauses leading to the conflict are
       queried for their explanation. Their explanation is added to the clauses.
       
    */
    void proof_trim::conflict_analysis_core(literal_vector const& cl, clause* cp) {
        IF_VERBOSE(3, verbose_stream() << "core " << cl << "\n");
        
        unsigned trail_size0 = s.m_trail.size();
        bool probe = !cl.empty() && !s.inconsistent();
        if (probe) {
            SASSERT(!s.inconsistent());
            s.push();
            unsigned lvl = s.scope_lvl();
            for (auto lit : cl)
                s.assign(~lit, justification(lvl));
            trail_size0 = s.m_trail.size();
            s.propagate(false);
            if (!s.inconsistent()) {
                s.m_qhead = 0;
                s.propagate(false);
            }
            if (!s.inconsistent())
                IF_VERBOSE(0, s.display(verbose_stream()));
            for (unsigned i = trail_size0; i < s.m_trail.size(); ++i)
                m_propagated[s.m_trail[i].var()] = true;
        }
        SASSERT(s.inconsistent());
        IF_VERBOSE(3, s.display_justification(verbose_stream() << "conflict " << s.m_not_l << " ", s.m_conflict) << "\n");
        IF_VERBOSE(3, s.display(verbose_stream()));
        sat::literal l = sat::null_literal;
        if (s.m_not_l != null_literal) {
            add_dependency(s.m_not_l);
            l = ~s.m_not_l;
        }
        add_core(l, s.m_conflict);
        add_dependency(s.m_conflict);
        
        for (unsigned i = s.m_trail.size(); i-- > trail_size0; ) {
            bool_var v = s.m_trail[i].var();
            m_propagated[v] = false;
            if (!s.is_marked(v))
                continue;
            add_core(v);
            s.reset_mark(v);            
            add_dependency(s.get_justification(v));
        }
        if (probe)
            s.pop(1);                
    }

    void proof_trim::add_dependency(literal lit) {
        IF_VERBOSE(3, verbose_stream() << "add dependency " << lit << "\n");
        bool_var v = lit.var();
        if (m_propagated[v]) { // literal was propagated after assuming ~C
            if (!s.is_marked(v))
                s.mark(v);
        }
        else if (s.lvl(v) == 0)  // literal depends on level 0, it is not assumed by ~C
            // inefficient for repeated insertions ? 
            add_core(v);                       
    }
    
    void proof_trim::add_dependency(justification j) {
        switch (j.get_kind()) {
        case justification::BINARY:
            add_dependency(j.get_literal());
            break;
        case justification::CLAUSE: 
            for (auto lit : s.get_clause(j))
                if (s.value(lit) == l_false)
                    add_dependency(lit);
            break;
        case justification::EXT_JUSTIFICATION:
            UNREACHABLE();
            break;
        default:
            break;
        }            
    }

    void proof_trim::add_core(bool_var v) {
        auto j = s.get_justification(v);
        literal lit = literal(v, s.value(v) == l_false);
        add_core(lit, j);
    }

    void proof_trim::insert_dep(unsigned dep) {
        if (m_in_deps.contains(dep))
            return;
        m_in_deps.insert(dep);
        m_result.back().second.push_back(dep);
    }

    void proof_trim::add_core(literal l, justification j) {
        m_clause.reset();
        switch (j.get_kind()) {
        case justification::NONE:
            if (l != null_literal)
                m_clause.push_back(l);
            break;                
        case justification::BINARY:
            m_clause.push_back(l);
            m_clause.push_back(j.get_literal());
            break;
        case justification::CLAUSE:
            for (auto lit : s.get_clause(j))
                m_clause.push_back(lit);
            break;
        default:
            verbose_stream() << j << "\n";
            UNREACHABLE();
            break;
        }
        std::sort(m_clause.begin(), m_clause.end());
        IF_VERBOSE(3, verbose_stream() << "add core {" << m_clause << "}\n");
        auto& [clauses, id, in_core] = m_clauses.find(m_clause);
        in_core = true;
        insert_dep(id);
        if (m_clause.size() > 1 && l != null_literal && s.lvl(l) == 0) {
            for (auto lit : m_clause) {
                if (s.lvl(lit) != 0)
                    continue;
                m_clause2.reset();
                m_clause2.push_back(s.value(lit) == l_false ? ~lit : lit);
                auto& [clauses, id, in_core] = m_clauses.insert_if_not_there(m_clause2, {{}, UINT_MAX, true });
                in_core = true;
                if (id != UINT_MAX)
                    insert_dep(id);
            }
        }
    }

    bool proof_trim::in_core(literal_vector const& cl) const {
        return m_clauses.find(cl).m_in_core;
    }

    void proof_trim::revive(literal_vector const& cl, clause* cp) {
        if (cp) 
            s.attach_clause(*cp);
        else 
            s.mk_clause(cl, status::redundant());            
    }

    clause* proof_trim::del(literal_vector const& cl) {
        clause* cp = nullptr;
        TRACE("sat", tout << "del: " << cl << "\n");
        if (cl.size() == 2) {
            s.detach_bin_clause(cl[0], cl[1], true);
            return cp;
        }
        auto* e = m_clauses.find_core(cl);            
        if (!e)
            return cp;
        auto& [clauses, id, in_core] = e->get_data().m_value;
        if (!clauses.empty()) {
            cp = clauses.back();
            TRACE("sat", tout << "del: " << *cp << "\n");
            s.detach_clause(*cp);
            clauses.pop_back();
        }
        return cp;
    }  

    proof_trim::proof_trim(params_ref const& p, reslimit& lim):
        s(p, lim) {
        s.set_trim();
    }

    void proof_trim::assume(unsigned id, bool is_initial) {
        std::sort(m_clause.begin(), m_clause.end()); 
        unsigned j = 0;
        sat::literal prev = null_literal;
        for (unsigned i = 0; i < m_clause.size(); ++i) 
            if (m_clause[i] != prev)
               prev = m_clause[j++] = m_clause[i];        
        m_clause.shrink(j);
        if (unit_or_binary_occurs())
            return;        
        if (!m_conflict.empty() && m_clause.empty()) {
            m_clauses.insert(m_clause, { {}, id, m_clause.empty() });
            m_trail.push_back({ id , m_clause, nullptr, true, is_initial });
        }
        if (!m_conflict.empty())
            return;        

        IF_VERBOSE(3, verbose_stream() << (is_initial?"assume ":"rup ") << m_clause << "\n");
        auto* cl = s.mk_clause(m_clause, status::redundant());
        auto& [clauses, id2, in_core] = m_clauses.insert_if_not_there(m_clause, { {}, id, m_clause.empty() });
        if (cl)
            clauses.push_back(cl);
        m_trail.push_back({ id, m_clause, cl, true, is_initial });

        auto is_unit2 = [&]() {
            if (s.value(m_clause[0]) == l_false) 
                std::swap(m_clause[0], m_clause[1]);            
            return s.value(m_clause[1]) == l_false;
        };

        auto is_unit = [&]() {
            unsigned undef_idx = m_clause.size();
            for (unsigned i = 0; i < m_clause.size(); ++i) {
                sat::literal lit = (*cl)[i];
                if (s.value(lit) != l_undef)
                    continue;
                if (undef_idx < m_clause.size())
                    return false;
                undef_idx = i;
            }
            if (undef_idx < m_clause.size()) {
                std::swap((*cl)[undef_idx], (*cl)[0]);
                return true;
            }
            return false;
        };

        if (all_of(m_clause, [&](sat::literal lit) { return s.value(lit) == l_false; })) {
            IF_VERBOSE(3, verbose_stream() << "false clause " << m_clause << "\n");
            set_conflict(m_clause, cl);
            return;
        }

        if (m_clause.size() == 2 && is_unit2())
            s.propagate_bin_clause(m_clause[0], m_clause[1]);
        else if (m_clause.size() > 2 && is_unit())
            s.propagate_clause(*cl, true, 0, s.cls_allocator().get_offset(cl));
        s.propagate(false);
        if (s.inconsistent()) {
            IF_VERBOSE(3, verbose_stream() << "conflict " << m_clause << "\n");
            set_conflict(m_clause, cl);
        }
    }

    /**
    * Unit clauses (and binary clause) do not have multi-set semantics in the solver.
    * So they should only be represented once.
    */
    bool proof_trim::unit_or_binary_occurs() {
        if (m_clause.size() == 1) {
            literal lit = m_clause[0];
            if (m_units.contains(lit.index()))
                return true;
            m_units.insert(lit.index());
        }
        // todo: binary?
        return false;
    }
    
    void proof_trim::del() {
        std::sort(m_clause.begin(), m_clause.end());
        clause* cp = del(m_clause);
        m_trail.push_back({ 0, m_clause, cp, false, true });
    }
    
    void proof_trim::infer(unsigned id) {
        assume(id, false);        
    }
}
