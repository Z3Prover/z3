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
#include"sat_watched.h"
#include"sat_clause.h"

namespace sat {

    bool erase_clause_watch(watch_list & wlist, clause_offset c) {
        watch_list::iterator it  = wlist.begin();              
        watch_list::iterator end = wlist.end();                
        for (; it != end; ++it) {                              
            if (it->is_clause() && it->get_clause_offset() == c) {                                        
                watch_list::iterator it2 = it;                 
                ++it;                                          
                for (; it != end; ++it) {                      
                    *it2 = *it;                                
                    ++it2;
                }                    
                wlist.set_end(it2);
                return true;                                  
            }                                                  
        }                                                      
        return false;                                           
    }

    void display(std::ostream & out, clause_allocator const & ca, watch_list const & wlist) {
        watch_list::const_iterator it  = wlist.begin();
        watch_list::const_iterator end = wlist.end();
        for (bool first = true; it != end; ++it) {
            if (first)
                first = false;
            else
                out << " ";
            switch (it->get_kind()) {
            case watched::BINARY:
                out << it->get_literal();
                if (it->is_learned())
                    out << "*";
                break;
            case watched::TERNARY:
                out << "(" << it->get_literal1() << " " << it->get_literal2() << ")";
                break;
            case watched::CLAUSE:
                out << "(" << it->get_blocked_literal() << " " << *(ca.get_clause(it->get_clause_offset())) << ")";
                break;
            case watched::EXT_CONSTRAINT:
                out << it->get_ext_constraint_idx();
                break;
            default: 
                UNREACHABLE();
            }
        }
    }

};
