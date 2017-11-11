/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_watched.cpp

Abstract:

    Element of the SAT solver watchlist.

Author:

    Leonardo de Moura (leonardo) 2011-05-24.

Revision History:

--*/
#include "sat/sat_watched.h"
#include "sat/sat_clause.h"

namespace sat {

    bool erase_clause_watch(watch_list & wlist, clause_offset c) {
        watch_list::iterator it  = wlist.begin();              
        watch_list::iterator end = wlist.end();                
        for (; it != end; ++it) {                              
            if (it->is_clause() && it->get_clause_offset() == c) {                                        
                watch_list::iterator it2 = it;                 
                ++it;                                        
                for (; it != end; ++it) {                      
                    SASSERT(!((it->is_clause() && it->get_clause_offset() == c)));
                    *it2 = *it;                                
                    ++it2;
                }                    
                wlist.set_end(it2);
                return true;                                  
            }                                                  
        }                                                      
        return false;                                           
    }

    std::ostream& display_watch_list(std::ostream & out, clause_allocator const & ca, watch_list const & wlist) {
        bool first = true;
        for (watched const& w : wlist) {
            if (first)
                first = false;
            else
                out << " ";
            switch (w.get_kind()) {
            case watched::BINARY:
                out << w.get_literal();
                if (w.is_learned())
                    out << "*";
                break;
            case watched::TERNARY:
                out << "(" << w.get_literal1() << " " << w.get_literal2() << ")";
                break;
            case watched::CLAUSE:
                out << "(" << w.get_blocked_literal() << " " << *(ca.get_clause(w.get_clause_offset())) << ")";
                break;
            case watched::EXT_CONSTRAINT:
                out << "ext: " << w.get_ext_constraint_idx();
                break;
            default: 
                UNREACHABLE();
            }
        }
        return out;
    }

};
