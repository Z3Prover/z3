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
       result = []
       C = { an }
       for i = n to 0 do
           if s.is_deleted(ai) then s.revive(ai)
           else 
              if s.isontrail(ai) then
                  s.undotrailcore(ai,C)
              s.delete(ai)
              if ai in C then 
                  if ai is not initial then
                      s.savetrail()
                      s.enqueue(not ai)
                      c = s.propagate()
                      s.conflictanalysiscore(c, C)
                      s.restoretrail()
                   result += [ai]
       reverse(result)
            
       is_deleted(ai):
          clause was detached
       revive(ai):
          attach clause ai
       isontrail(ai):
          some literal on the current trail in s is justified by ai
       undotrailcore(ai, C):
          pop the trail until dependencies on ai are gone
       savetrail:
          store current trail so it can be restored
       enqueue(not ai):
          assert negations of ai at a new decision level
       conflictanalysiscore(c, C):
          ?
       restoretrail:
          restore the trail to the position before enqueue
                                                                          
    */        

    void proof_trim::trim() {
        vector<literal_vector> result, clauses;
        clauses.push_back(literal_vector());
        for (unsigned i = m_trail.size(); i-- > 0; ) {
            auto const& [cl, clp, is_add, is_initial] = m_trail[i];
            if (!is_add) {
                revive(cl, clp);
                continue;
            }
            prune_trail(cl, clp);
            del(cl, clp);
            if (!clauses.contains(cl))
                continue;
            result.push_back(cl);
            if (is_initial)
                continue;
            s.push();
            unsigned init_sz = s.m_trail.size();
            unsigned lvl = s.scope_lvl();
            for (auto lit : cl)
                s.assign(~lit, justification(lvl));
            s.propagate(false);
            SASSERT(s.inconsistent());
            conflict_analysis_core(init_sz, clauses);
            s.pop(1);                
        }
        result.reverse();
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
        
        for (literal lit : cl) 
            m_in_clause.insert(lit.index());
        
        bool on_trail = false;
        unsigned j = 0;
        for (unsigned i = 0; i < s.trail_size(); ++i) {
            literal l = s.trail_literal(i);
            if (m_in_clause.contains(l.index())) {
                SASSERT(!on_trail);
                on_trail = true;
                m_in_coi.insert((~l).index());
                s.m_assignment[l.index()] = l_undef;
                s.m_assignment[(~l).index()] = l_undef;
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
            else if (js.is_ternary_clause())
                in_coi = m_in_coi.contains(js.get_literal1().index()) || m_in_coi.contains(js.get_literal2().index());
            else
                UNREACHABLE(); // approach does not work for external justifications
            
            if (in_coi) {
                m_in_coi.insert((~l).index());
                s.m_assignment[l.index()] = l_undef;
                s.m_assignment[(~l).index()] = l_undef;
            }
            else
                s.m_trail[j++] = s.m_trail[i];
        }            
        s.m_trail.shrink(j);
    }


    /**
       The current state is in conflict.
       Chase justifications for conflict to extract clauses that are in coi of conflict.

       Assume:
       F | G, ~C |- []
       Let T (trail) be the extension of G, ~C that derives the empty clause.
       T := G, ~C, l1:j1, l2:j2, ..., lk:jk
       The goal is to extract clauses in T that are used to derive C.
       - some of the literals in ~C that are not set to true already (they must be unassigned relative)
       are used to derive the empty clause.
       - some literals in ~C that are assigned to true may also be used to derive the empty clause.
             
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
    void proof_trim::conflict_analysis_core(unsigned init_sz, vector<literal_vector>& clauses) {
        justification j = s.m_conflict;
        literal consequent = null_literal;
        unsigned idx = s.m_trail.size() - 1;
        unsigned old_sz = s.m_unmark.size();
        bool_var c_var;
        auto add_dependency = [&](bool_var v) {
            auto j = s.m_justification[v];
            literal lit = literal(v, s.value(v) == l_false);
            add_core(lit, j, clauses);            
        };
        
        if (s.m_not_l != null_literal) {
            s.process_antecedent_for_unsat_core(s.m_not_l);
            add_core(s.m_not_l, s.m_justification[s.m_not_l.var()], clauses);
            add_core(~s.m_not_l, j, clauses);
            consequent = ~s.m_not_l;                
        }
        while (true) {
            s.process_consequent_for_unsat_core(consequent, j);
            while (idx >= init_sz) {
                consequent = s.m_trail[idx];
                c_var = consequent.var();
                if (s.is_marked(c_var))
                    break;
                --idx;
            }
            if (idx < init_sz)
                break;
            j = s.m_justification[c_var];
            --idx;
        }
        for (unsigned i = s.m_mark.size(); i-- > old_sz; ) 
            add_dependency(s.m_unmark[i]);
        s.reset_unmark(old_sz);
    }

    void proof_trim::add_core(literal l, justification j, vector<literal_vector>& clauses) {
        m_clause.reset();
        switch (j.get_kind()) {
        case justification::NONE:
            return;                
        case justification::BINARY:
            m_clause.push_back(l);
            m_clause.push_back(j.get_literal());
            break;
        case justification::TERNARY:
            m_clause.push_back(l);
            m_clause.push_back(j.get_literal1());
            m_clause.push_back(j.get_literal2());
            break;
        case justification::CLAUSE: 
            for (auto lit : s.get_clause(j))
                m_clause.push_back(lit);
            break;
        default:
            UNREACHABLE();
            break;
        }
        std::sort(m_clause.begin(), m_clause.end());
        clauses.insert(m_clause);            
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
        if (m_clause.size() == 2) {
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
        s(p, lim)
    {}

    void proof_trim::assume(bool is_initial) {
        std::sort(m_clause.begin(), m_clause.end());
        IF_VERBOSE(3, verbose_stream() << "add: " << m_clause << "\n");
        auto* cl = s.mk_clause(m_clause, status::redundant());
        m_trail.push_back({ m_clause, cl, true, is_initial });
        s.propagate(false);
        save(m_clause, cl);
    }
    
    void proof_trim::del() {
        std::sort(m_clause.begin(), m_clause.end());
        clause* cp = del(m_clause);
        m_trail.push_back({ m_clause, cp, false, true });
    }
    
    void proof_trim::infer() {
        assume(false);        
    }


}
