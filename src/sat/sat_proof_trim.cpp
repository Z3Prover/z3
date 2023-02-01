/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_proof_trim.cpp

  Abstract:
   
    proof replay and trim

  Author:

    Nikolaj Bjorner 2023-10-04

  Notes:
  

--*/

#include "sat/sat_proof_trim.h"

namespace sat {


    /**
       Pseudo-code from Gurfinkel, Vizel, FMCAD 2014
       Input: trail (a0,d0), ..., (an,dn) = ({},bot)
       Output: reduced trail - result                                                                           
    */        

    unsigned_vector proof_trim::trim() {
        unsigned_vector result;
        m_core_literals.reset();
        m_core_literals.insert(literal_vector());
        m_propagated.resize(num_vars(), false);
        for (unsigned i = m_trail.size(); i-- > 0; ) {
            auto const& [id, cl, clp, is_add, is_initial] = m_trail[i];
            if (!is_add) {
                revive(cl, clp);
                continue;
            }
            IF_VERBOSE(10, s.display(verbose_stream()));
            prune_trail(cl, clp);
            IF_VERBOSE(10, verbose_stream() << cl << " " << in_core(cl, clp) << ": "; for (auto const& c : m_core_literals) verbose_stream() << "{" << c << "} ");
            IF_VERBOSE(10, s.display(verbose_stream() << "\n"));
            del(cl, clp);
            if (!in_core(cl, clp))
                continue;
            result.push_back(id);
            if (is_initial)
                continue;
            conflict_analysis_core(cl, clp);            
        }
        result.reverse();
        return result;
    }
    
    void proof_trim::del(literal_vector const& cl, clause* cp) {
        if (cp) 
            s.detach_clause(*cp);
        else 
            del(cl);
    }
    
    bool proof_trim::match_clause(literal_vector const& cl, literal l1, literal l2) const {
        return cl.size() == 2 && ((l1 == cl[0] && l2 == cl[1]) || (l1 == cl[1] && l2 == cl[0]));
    }
    
    bool proof_trim::match_clause(literal_vector const& cl, literal l1, literal l2, literal l3) const {
        return cl.size() == 3 &&
            ((l1 == cl[0] && l2 == cl[1] && l3 == cl[2]) ||
             (l1 == cl[0] && l2 == cl[2] && l3 == cl[1]) ||
             (l1 == cl[1] && l2 == cl[0] && l3 == cl[2]) ||
             (l1 == cl[1] && l2 == cl[2] && l3 == cl[0]) ||
             (l1 == cl[2] && l2 == cl[1] && l3 == cl[0]) ||
             (l1 == cl[2] && l2 == cl[0] && l3 == cl[1]));
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
                for (literal lit : s.get_clause(j))
                    in_coi |= m_in_coi.contains(lit.index());                
            else if (js.is_binary_clause())
                in_coi = m_in_coi.contains(js.get_literal().index());
            else
                UNREACHABLE(); // approach does not work for external justifications
            
            if (in_coi) 
                unassign_literal(l);
            else
                s.m_trail[j++] = s.m_trail[i];
        }            
        s.m_trail.shrink(j);
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
        if (!cl.empty()) {
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
        IF_VERBOSE(3, verbose_stream() << s.m_not_l << " " << s.m_conflict << "\n");
        if (s.m_not_l != null_literal) {
            add_core(~s.m_not_l, s.m_conflict);
            add_dependency(s.m_not_l);
        }
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
        if (!cl.empty())
            s.pop(1);                
    }

    void proof_trim::add_dependency(literal lit) {
        bool_var v = lit.var();
        if (m_propagated[v]) // literal was propagated after assuming ~C
            s.mark(v);        
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


    void proof_trim::add_core(literal l, justification j) {
        m_clause.reset();
        switch (j.get_kind()) {
        case justification::NONE:
            m_clause.push_back(l);
            break;                
        case justification::BINARY:
            m_clause.push_back(l);
            m_clause.push_back(j.get_literal());
            break;
        case justification::CLAUSE:
            s.get_clause(j).mark_used();
            IF_VERBOSE(3, verbose_stream() << "add core " << s.get_clause(j) << "\n");
            return;
        default:
            UNREACHABLE();
            break;
        }
        std::sort(m_clause.begin(), m_clause.end());
        IF_VERBOSE(3, verbose_stream() << "add core " << m_clause << "\n");
        m_core_literals.insert(m_clause);
        if (s.lvl(l) == 0) {
            m_clause.reset();
            m_clause.push_back(l);
            m_core_literals.insert(m_clause);
        }
    }

    bool proof_trim::in_core(literal_vector const& cl, clause* cp) const {
        if (cp)
            return cp->was_used();
        else
            return m_core_literals.contains(cl);
    }

    void proof_trim::revive(literal_vector const& cl, clause* cp) {
        if (cp) 
            s.attach_clause(*cp);
        else 
            s.mk_clause(cl, status::redundant());            
    }

    clause* proof_trim::del(literal_vector const& cl) {
        clause* cp = nullptr;
        IF_VERBOSE(3, verbose_stream() << "del: " << cl << "\n");
        if (cl.size() == 2) {
            s.detach_bin_clause(cl[0], cl[1], true);
            return cp;
        }
        auto* e = m_clauses.find_core(cl);            
        if (!e)
            return cp;
        auto& v = e->get_data().m_value;
        if (!v.empty()) {
            cp = v.back();
            IF_VERBOSE(3, verbose_stream() << "del: " << *cp << "\n");
            s.detach_clause(*cp);
            v.pop_back();
        }
        return cp;
    }

    void proof_trim::save(literal_vector const& lits, clause* cl) {
        if (!cl)                
            return;
        IF_VERBOSE(3, verbose_stream() << "add: " << *cl << "\n");
        auto& v = m_clauses.insert_if_not_there(lits, clause_vector());            
        v.push_back(cl);
    }    

    proof_trim::proof_trim(params_ref const& p, reslimit& lim):
        s(p, lim) {
        s.set_trim();
    }

    void proof_trim::assume(unsigned id, bool is_initial) {
        std::sort(m_clause.begin(), m_clause.end());
        if (unit_or_binary_occurs())
            return;
        IF_VERBOSE(3, verbose_stream() << (is_initial?"assume ":"rup ") << m_clause << "\n");
        auto* cl = s.mk_clause(m_clause, status::redundant());
        m_trail.push_back({ id, m_clause, cl, true, is_initial });
        s.propagate(false);
        save(m_clause, cl);
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
