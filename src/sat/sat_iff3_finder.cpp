/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_iff3_finder.cpp

Abstract:

    Find constraints of the form   x = l1 = l2
    That is, search for clauses of the form
      ~x \/ l1  \/ ~l2
      ~x \/ ~l1 \/ l2
       x \/ l1  \/ l2
       x \/ ~l1 \/ ~l2
       
    The basic idea is to sort the watch lists.
    
    This information can be used to propagate equivalences
    during probing (and search).

    The initial experiments were disappointing.
    Not using it on the solver.

Author:

    Leonardo de Moura (leonardo) 2011-06-04.

Revision History:

--*/
#include "sat/sat_iff3_finder.h"
#include "sat/sat_solver.h"

namespace sat {

    struct iff3_lt {
        bool operator()(watched const & w1, watched const & w2) const {
            // keep th binary clauses in the beginning
            if (w2.is_binary_clause()) return false;
            if (w1.is_binary_clause()) return true;
            //
            if (w2.is_ternary_clause()) {
                if (w1.is_ternary_clause()) {
                    literal l1_1 = w1.get_literal1();
                    literal l1_2 = w1.get_literal2();
                    literal l2_1 = w2.get_literal1();
                    literal l2_2 = w2.get_literal2();
                    if (l1_1.index() < l2_1.index()) return true;
                    if (l1_1.index() > l2_1.index()) return false;
                    return l1_2.index() < l2_2.index();
                }
                return false;
            }
            if (w1.is_ternary_clause()) return true;
            return false;
        }
    };

    static void unmark(svector<bool> & marks, literal_vector & to_unmark) {
        literal_vector::const_iterator it  = to_unmark.begin();
        literal_vector::const_iterator end = to_unmark.end();
        for (; it != end; ++it) {
            marks[it->index()] = false;
        }
        to_unmark.reset();
    }

#define SMALL_WLIST 16

    /**
       \brief Return true if wlist contains (l1, l2)
       It assumes wlist have been sorted using iff3_lt
    */
    static bool contains(watch_list const & wlist, literal l1, literal l2) {
        watched k(l1, l2);
        if (wlist.size() < SMALL_WLIST)
            return wlist.contains(k);
        iff3_lt lt;
        int low  = 0;
        int high = wlist.size(); 
        while (true) {
            int mid = low + ((high - low) / 2);
            watched const & m = wlist[mid];
            if (m == k)
                return true;
            if (lt(m, k)) {
                low = mid + 1;
            }
            else {
                SASSERT(lt(k, m));
                high = mid - 1;
            }
            if (low > high)
                return false;
        }
    }

    iff3_finder::iff3_finder(solver & _s):
        s(_s) {
    }

    void iff3_finder::sort_watches() {
        vector<watch_list>::iterator it  = s.m_watches.begin();
        vector<watch_list>::iterator end = s.m_watches.end();
        for (; it != end; ++it) {
            watch_list & wlist = *it;
            std::stable_sort(wlist.begin(), wlist.end(), iff3_lt());
        }
    }

    void iff3_finder::mk_eq(literal l1, literal l2) {
        s.mk_clause(l1, ~l2);
        s.mk_clause(~l1, l2);
    }

    void iff3_finder::operator()() {
        TRACE("iff3_finder", tout << "starting iff3_finder\n";);
        sort_watches();
        
        unsigned counter = 0;

        svector<bool>   found;
        found.resize(s.num_vars()*2, false);
        literal_vector to_unmark;

        typedef std::pair<literal, literal> lit_pair;
        svector<lit_pair> pairs;

        for (bool_var x = 0; x < s.num_vars(); x++) {
            literal pos_x(x, false);
            literal neg_x(x, true);
            watch_list & pos_wlist = s.get_wlist(neg_x);
            watch_list & neg_wlist = s.get_wlist(pos_x);
            // 
            TRACE("iff3_finder", 
                  tout << "visiting: " << x << "\n";
                  tout << "pos:\n";
                  s.display_watch_list(tout,  pos_wlist);
                  tout << "\nneg:\n";
                  s.display_watch_list(tout, neg_wlist);
                  tout << "\n--------------\n";);
            // traverse the ternary clauses x \/ l1 \/ l2
            bool_var curr_v1 = null_bool_var;
            watch_list::iterator it  = pos_wlist.begin();
            watch_list::iterator end = pos_wlist.end();
            for (; it != end; ++it) {
                if (it->is_binary_clause())
                    continue;
                if (it->is_ternary_clause()) {
                    literal l1  = it->get_literal1();
                    if (l1.index() < pos_x.index())
                        break; // stop
                    literal l2  = it->get_literal2();
                    bool_var v1 = l1.var();
                    if (v1 != curr_v1) {
                        curr_v1 = v1;
                        unmark(found, to_unmark);
                        pairs.reset();
                    }
                    if (!l1.sign()) {
                        if (!found[l2.index()]) {
                            found[l2.index()] = true;
                            to_unmark.push_back(l2);
                        }
                    }
                    else {
                        l2.neg();
                        if (found[l2.index()]) {
                            // Found clauses x \/ v1 \/ l2 and x \/ ~v1 \/ ~l2
                            // So, I have to find the clauses
                            // ~x \/  v1 \/ ~l2
                            // ~x \/ ~v1 \/ l2
                            if (contains(neg_wlist, literal(v1, false), ~l2) &&
                                contains(neg_wlist, literal(v1, true),  l2)) {
                                // found new iff3
                                // x = v1 = l2
                                counter++;
                                // verbose_stream() << counter << ": " << x << " = " << v1 << " = " << l2 << "\n";
                                TRACE("iff3_finder", tout << counter << ": " << x << " = " << v1 << " = " << l2 << "\n";);
                                l1.neg();
                                svector<lit_pair>::iterator it2  = pairs.begin();
                                svector<lit_pair>::iterator end2 = pairs.end();
                                for (; it2 != end2; ++it2) {
                                    if (it2->first == l1) {
                                        // l2 == it2->second
                                        mk_eq(l2, it2->second);
                                    }
                                    else if (it2->second == l1) {
                                        // l2 == it2->first
                                        mk_eq(l2, it2->first);
                                    }
                                    else if (it2->first == l2) {
                                        // l1 == it2->second
                                        mk_eq(l1, it2->second);
                                    }
                                    else if (it2->second == l2) {
                                        // l1 == it2->first
                                        mk_eq(l1, it2->first);
                                    }
                                }
                                pairs.push_back(lit_pair(l1, l2));
                            }
                        }
                    }
                }
                else {
                    break; // stop, no more ternary clauses from this point
                }
            }
        }
    }
    
};
