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
#include "sat/sat_extension.h"

namespace sat {

    bool erase_clause_watch(watch_list & wlist, clause_offset c) {
        watch_list::iterator it  = wlist.begin();              
        watch_list::iterator end = wlist.end();                
        for (; it != end; ++it) {                              
            if (it->is_clause() && it->get_clause_offset() == c) {                                        
                watch_list::iterator it2 = it;                 
                ++it;    
                for (; it != end; ++it, ++it2) {                      
                    SASSERT(!((it->is_clause() && it->get_clause_offset() == c)));
                    *it2 = *it;                                
                }                    
                wlist.set_end(it2);
                return true;                                  
            }                                                  
        }                                                      
        return false;                                           
    }

    watched* find_binary_watch(watch_list & wlist, literal l) {
        for (watched& w : wlist) {
            if (w.is_binary_clause() && w.get_literal() == l) return &w;
        }
        return nullptr;
    }

    watched const* find_binary_watch(watch_list const& wlist, literal l) {
        for (watched const& w : wlist) {
            if (w.is_binary_clause() && w.get_literal() == l) return &w;
        }
        return nullptr;
    }
    
    void erase_binary_watch(watch_list& wlist, literal l) {
        watch_list::iterator it = wlist.begin(), end = wlist.end();
        watch_list::iterator it2 = it;
        bool found = false;
        for (; it != end; ++it) {
            if (it->is_binary_clause() && it->get_literal() == l && !found) {
                found = true;
            }
            else {
                *it2 = *it;
                ++it2;
            }
        }
        wlist.set_end(it2);
        VERIFY(found);
    }

    void erase_ternary_watch(watch_list& wlist, literal l1, literal l2) {
        watched w(l1, l2);
        watch_list::iterator it = wlist.begin(), end = wlist.end();
        watch_list::iterator it2 = it;
        bool found = false;
        for (; it != end; ++it) {
            if (!found && w == *it) {
                found = true;
            }
            else {
                *it2 = *it;
                ++it2;    
            }    
        }
        wlist.set_end(it2);
#if 0
        VERIFY(found);
        for (watched const& w2 : wlist) {
            if (w2 == w) {
                std::cout << l1 << " " << l2 << "\n";
            }
            //VERIFY(w2 != w);
        }
#endif
    }

    void conflict_cleanup(watch_list::iterator it, watch_list::iterator it2, watch_list& wlist) {
        watch_list::iterator end = wlist.end();
        for (; it != end; ++it, ++it2) 
            *it2 = *it; 
        wlist.set_end(it2);
    }


    std::ostream& display_watch_list(std::ostream & out, clause_allocator const & ca, watch_list const & wlist, extension* ext) {
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
                if (ext) {
                    ext->display_constraint(out, w.get_ext_constraint_idx());
                }
                else  {
                    out << "ext: " << w.get_ext_constraint_idx();
                }
                break;
            default: 
                UNREACHABLE();
            }
        }
        return out;
    }

};
