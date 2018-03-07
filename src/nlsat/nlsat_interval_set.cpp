/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_interval_set.cpp

Abstract:

    Sets of disjoint infeasible intervals.

Author:

    Leonardo de Moura (leonardo) 2012-01-11.

Revision History:

--*/
#include "nlsat/nlsat_interval_set.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/buffer.h"

namespace nlsat {

    struct interval {
        unsigned  m_lower_open:1;
        unsigned  m_upper_open:1;
        unsigned  m_lower_inf:1;
        unsigned  m_upper_inf:1;
        literal   m_justification;
        anum      m_lower;
        anum      m_upper;
    };

    class interval_set {
    public:
        static unsigned get_obj_size(unsigned num) { return sizeof(interval_set) + num*sizeof(interval); }
        unsigned  m_num_intervals;
        unsigned  m_ref_count:31;
        unsigned  m_full:1;
        interval  m_intervals[0];
    };

    void display(std::ostream & out, anum_manager & am, interval const & curr) {
        if (curr.m_lower_inf) {
            out << "(-oo, ";
        }
        else {
            if (curr.m_lower_open)
                    out << "(";
            else
                out << "[";
            am.display_decimal(out, curr.m_lower);
            out << ", ";
        }
        if (curr.m_justification.sign())
            out << "~";
        out << "p";
        out << curr.m_justification.var() << ", ";
        if (curr.m_upper_inf) {
            out << "oo)";
        }
        else {
            am.display_decimal(out, curr.m_upper);
            if (curr.m_upper_open)
                out << ")";
            else
                out << "]";
        }
    }

    bool check_interval(anum_manager & am, interval const & i) {
        if (i.m_lower_inf) {
            SASSERT(i.m_lower_open);
        }
        if (i.m_upper_inf) {
            SASSERT(i.m_upper_open);
        }
        if (!i.m_lower_inf && !i.m_upper_inf) {
            int s = am.compare(i.m_lower, i.m_upper);
            TRACE("nlsat_interval", tout << "lower: "; am.display_decimal(tout, i.m_lower); tout << ", upper: "; am.display_decimal(tout, i.m_upper);
                  tout << "\ns: " << s << "\n";);
            SASSERT(s <= 0);
            if (s == 0) {
                SASSERT(!i.m_lower_open && !i.m_upper_open);
            }
        }
        return true;
    }

    bool check_no_overlap(anum_manager & am, interval const & curr, interval const & next) {
        SASSERT(!curr.m_upper_inf);
        SASSERT(!next.m_lower_inf);
        int sign = am.compare(curr.m_upper, next.m_lower);
        CTRACE("nlsat", sign > 0, display(tout, am, curr); tout << "  "; display(tout, am, next); tout << "\n";);
        SASSERT(sign <= 0);
        if (sign == 0) {
            SASSERT(curr.m_upper_open || next.m_lower_open);
        }
        return true;
    }
    
    // Check if the intervals are valid, ordered, and are disjoint.
    bool check_interval_set(anum_manager & am, unsigned sz, interval const * ints) {
        DEBUG_CODE(
            for (unsigned i = 0; i < sz; i++) {
                interval const & curr = ints[i];
                SASSERT(check_interval(am, curr));
                if (i < sz - 1) {
                    SASSERT(check_no_overlap(am, curr, ints[i+1]));
                }
            });
        return true;
    }

    interval_set_manager::interval_set_manager(anum_manager & m, small_object_allocator & a):
        m_am(m),
        m_allocator(a) {
    }
     
    interval_set_manager::~interval_set_manager() {
    }
    
    void interval_set_manager::del(interval_set * s) {
        if (s == nullptr)
            return;
        unsigned num    = s->m_num_intervals;
        unsigned obj_sz = interval_set::get_obj_size(num);
        for (unsigned i = 0; i < num; i++) {
            m_am.del(s->m_intervals[i].m_lower);
            m_am.del(s->m_intervals[i].m_upper);
        }
        s->~interval_set();
        m_allocator.deallocate(obj_sz, s);
    }

    void interval_set_manager::dec_ref(interval_set * s) {
        SASSERT(s->m_ref_count > 0);
        s->m_ref_count--;
        if (s->m_ref_count == 0)
            del(s);
    }

    void interval_set_manager::inc_ref(interval_set * s) {
        s->m_ref_count++;
    }
    
    interval_set * interval_set_manager::mk(bool lower_open, bool lower_inf, anum const & lower, 
                                            bool upper_open, bool upper_inf, anum const & upper,
                                            literal justification) {
        void * mem = m_allocator.allocate(interval_set::get_obj_size(1));
        interval_set * new_set = new (mem) interval_set();
        new_set->m_num_intervals = 1;
        new_set->m_ref_count  = 0;
        new_set->m_full       = lower_inf && upper_inf;
        interval * i = new (new_set->m_intervals) interval();
        i->m_lower_open = lower_open;
        i->m_lower_inf  = lower_inf;
        i->m_upper_open = upper_open;
        i->m_upper_inf  = upper_inf;
        i->m_justification = justification;
        if (!lower_inf)
            m_am.set(i->m_lower, lower);
        if (!upper_inf)
            m_am.set(i->m_upper, upper);
        SASSERT(check_interval_set(m_am, 1, new_set->m_intervals));
        return new_set;
    }

    inline int compare_lower_lower(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_lower_inf && i2.m_lower_inf)
            return 0;
        if (i1.m_lower_inf)
            return -1;
        if (i2.m_lower_inf)
            return 1;
        SASSERT(!i1.m_lower_inf && !i2.m_lower_inf);
        int s = am.compare(i1.m_lower, i2.m_lower);
        if (s != 0)
            return s;
        if (i1.m_lower_open == i2.m_lower_open)
            return 0;
        if (i1.m_lower_open)
            return 1;
        else
            return -1;
    }

    inline int compare_upper_upper(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_upper_inf && i2.m_upper_inf)
            return 0;
        if (i1.m_upper_inf)
            return 1;
        if (i2.m_upper_inf)
            return -1;
        SASSERT(!i1.m_upper_inf && !i2.m_upper_inf);
        int s = am.compare(i1.m_upper, i2.m_upper);
        if (s != 0)
            return s;
        if (i1.m_upper_open == i2.m_upper_open)
            return 0;
        if (i1.m_upper_open)
            return -1;
        else
            return 1;
    }

    inline int compare_upper_lower(anum_manager & am, interval const & i1, interval const & i2) {
        if (i1.m_upper_inf || i2.m_lower_inf)
            return 1;
        SASSERT(!i1.m_upper_inf && !i2.m_lower_inf);
        int s = am.compare(i1.m_upper, i2.m_lower);
        if (s != 0)
            return s;
        if (!i1.m_upper_open && !i2.m_lower_open)
            return 0;
        return -1;
    }
    
    typedef sbuffer<interval, 128> interval_buffer;

    // Given two interval in an interval set s.t. curr occurs before next.
    // We say curr and next are "adjacent" iff
    //      there is no "space" between them.
    bool adjacent(anum_manager & am, interval const & curr, interval const & next) {
        SASSERT(!curr.m_upper_inf);
        SASSERT(!next.m_lower_inf);
        int sign = am.compare(curr.m_upper, next.m_lower);
        SASSERT(sign <= 0);
        if (sign == 0) {
            SASSERT(curr.m_upper_open || next.m_lower_open);
            return !curr.m_upper_open || !next.m_lower_open;
        }
        return false;
    }

    inline void push_back(anum_manager & am, interval_buffer & buf, 
                          bool lower_open, bool lower_inf, anum const & lower, 
                          bool upper_open, bool upper_inf, anum const & upper,
                          literal justification) {
        buf.push_back(interval());
        interval & i = buf.back();
        i.m_lower_open = lower_open;
        i.m_lower_inf  = lower_inf;
        am.set(i.m_lower, lower);
        i.m_upper_open = upper_open;
        i.m_upper_inf  = upper_inf;
        am.set(i.m_upper, upper);
        i.m_justification = justification;
        SASSERT(check_interval(am, i));
    }

    inline void push_back(anum_manager & am, interval_buffer & buf, interval const & i) {
        push_back(am, buf,
                  i.m_lower_open, i.m_lower_inf, i.m_lower,
                  i.m_upper_open, i.m_upper_inf, i.m_upper,
                  i.m_justification);
    }

    inline interval_set * mk_interval(small_object_allocator & allocator, interval_buffer & buf, bool full) {
        unsigned sz = buf.size();
        void * mem = allocator.allocate(interval_set::get_obj_size(sz));
        interval_set * new_set = new (mem) interval_set();
        new_set->m_full = full;
        new_set->m_ref_count  = 0;
        new_set->m_num_intervals = sz;
        memcpy(new_set->m_intervals, buf.c_ptr(), sizeof(interval)*sz);
        return new_set;
    }

    interval_set * interval_set_manager::mk_union(interval_set const * s1, interval_set const * s2) {
        TRACE("nlsat_interval", tout << "mk_union\ns1: "; display(tout, s1); tout << "\ns2: "; display(tout, s2); tout << "\n";);
        if (s1 == nullptr || s1 == s2)
            return const_cast<interval_set*>(s2);
        if (s2 == nullptr)
            return const_cast<interval_set*>(s1);
        if (s1->m_full)
            return const_cast<interval_set*>(s1);
        if (s2->m_full)
            return const_cast<interval_set*>(s2);
        interval_buffer result;
        unsigned sz1 = s1->m_num_intervals;
        unsigned sz2 = s2->m_num_intervals;
        unsigned i1  = 0;
        unsigned i2  = 0;
        while (true) {
            if (i1 >= sz1) {
                while (i2 < sz2) {
                    TRACE("nlsat_interval", tout << "adding remaining intervals from s2: "; nlsat::display(tout, m_am, s2->m_intervals[i2]); tout << "\n";);
                    push_back(m_am, result, s2->m_intervals[i2]);
                    i2++;
                }
                break;
            }
            if (i2 >= sz2) {
                while (i1 < sz1) {
                    TRACE("nlsat_interval", tout << "adding remaining intervals from s1: "; nlsat::display(tout, m_am, s1->m_intervals[i1]); tout << "\n";);
                    push_back(m_am, result, s1->m_intervals[i1]);
                    i1++;
                }
                break;
            }
            interval const & int1 = s1->m_intervals[i1];
            interval const & int2 = s2->m_intervals[i2];
            int l1_l2_sign = compare_lower_lower(m_am, int1, int2);
            int u1_u2_sign = compare_upper_upper(m_am, int1, int2);
            TRACE("nlsat_interval", 
                  tout << "i1: " << i1 << ", i2: " << i2 << "\n";
                  tout << "int1: "; nlsat::display(tout, m_am, int1); tout << "\n";
                  tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
            if (l1_l2_sign <= 0) {
                if (u1_u2_sign == 0) {
                    // Cases:
                    // 1)  [     ]
                    //     [     ]
                    //
                    // 2) [     ]
                    //      [   ]
                    //
                    TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign == 0\n";);
                    push_back(m_am, result, int1);
                    i1++;
                    i2++;
                }
                else if (u1_u2_sign > 0) {
                    // Cases:
                    //
                    // 1) [        ]
                    //    [     ]
                    //
                    // 2) [        ]
                    //      [   ]
                    i2++;
                    TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign > 0\n";);
                    // i1 may consume other intervals of s2
                }
                else {
                    SASSERT(u1_u2_sign < 0);
                    int u1_l2_sign = compare_upper_lower(m_am, int1, int2);
                    if (u1_l2_sign < 0) {
                        SASSERT(l1_l2_sign < 0);
                        // Cases:
                        // 1)   [      ]
                        //                [     ]
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign < 0\n";);
                        push_back(m_am, result, int1);
                        i1++;
                    }
                    else if (u1_l2_sign == 0) {
                        SASSERT(l1_l2_sign <= 0);
                        SASSERT(!int1.m_upper_open && !int2.m_lower_open);
                        SASSERT(!int2.m_lower_inf);
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign == 0\n";);
                        // Cases:
                        if (l1_l2_sign != 0) {
                            SASSERT(l1_l2_sign < 0);
                            // 1)   [   ]
                            //          [    ]
                            SASSERT(!int2.m_lower_open);
                            push_back(m_am, result, 
                                      int1.m_lower_open, int1.m_lower_inf,  int1.m_lower,
                                      true /* open */, false /* not +oo */, int1.m_upper, 
                                      int1.m_justification); 
                            i1++;
                        }
                        else {
                            SASSERT(l1_l2_sign == 0);
                            // 2)   u          <<< int1 is a singleton
                            //      [     ]
                            // just consume int1
                            i1++;
                        }
                    }
                    else {
                        SASSERT(l1_l2_sign <= 0);
                        SASSERT(u1_u2_sign < 0);
                        SASSERT(u1_l2_sign > 0);
                        TRACE("nlsat_interval", tout << "l1_l2_sign <= 0, u1_u2_sign < 0, u1_l2_sign > 0\n";);
                        if (l1_l2_sign == 0) {
                            // Case:
                            // 1)   [      ]
                            //      [          ]
                            // just consume int1
                            i1++;
                        }
                        else {
                            SASSERT(l1_l2_sign < 0);
                            SASSERT(u1_u2_sign < 0);
                            SASSERT(u1_l2_sign > 0);
                            // 2) [        ]
                            //         [        ]
                            push_back(m_am, result, 
                                      int1.m_lower_open,     int1.m_lower_inf, int1.m_lower,
                                      !int2.m_lower_open, false /* not +oo */, int2.m_lower,
                                      int1.m_justification); 
                            i1++;
                        }
                    }
                }
            }
            else {
                SASSERT(l1_l2_sign > 0);
                if (u1_u2_sign == 0) {
                    TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign == 0\n";);
                    // Case:
                    // 1)    [  ]
                    //    [     ]
                    //
                    push_back(m_am, result, int2);
                    i1++;
                    i2++;
                }
                else if (u1_u2_sign < 0) {
                    TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign > 0\n";);
                    // Case:
                    // 1)   [   ]
                    //    [       ]
                    i1++;
                    // i2 may consume other intervals of s1
                }
                else {
                    int u2_l1_sign = compare_upper_lower(m_am, int2, int1);
                    if (u2_l1_sign < 0) {
                        TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign > 0, u2_l1_sign < 0\n";);
                        // Case:
                        // 1)           [      ]
                        //     [     ]
                        push_back(m_am, result, int2);
                        i2++;
                    }
                    else if (u2_l1_sign == 0) {
                        TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign > 0, u2_l1_sign == 0\n";);
                        SASSERT(!int1.m_lower_open && !int2.m_upper_open);
                        SASSERT(!int1.m_lower_inf);
                        // Case:
                        //      [    ]   
                        //  [   ]
                        push_back(m_am, result, 
                                  int2.m_lower_open,     int2.m_lower_inf, int2.m_lower,
                                  true /* open */,    false /* not +oo */, int2.m_upper, 
                                  int2.m_justification); 
                        i2++;
                    }
                    else {
                        TRACE("nlsat_interval", tout << "l1_l2_sign > 0, u1_u2_sign > 0, u2_l1_sign > 0\n";);
                        SASSERT(l1_l2_sign > 0);
                        SASSERT(u1_u2_sign > 0);
                        SASSERT(u2_l1_sign > 0);
                        // Case:
                        //     [        ]
                        // [        ]
                        push_back(m_am, result, 
                                  int2.m_lower_open,     int2.m_lower_inf, int2.m_lower,
                                  !int1.m_lower_open, false /* not +oo */, int1.m_lower,
                                  int2.m_justification); 
                        i2++;
                    }
                }
            }
            SASSERT(result.size() <= 1 ||
                    check_no_overlap(m_am, result[result.size() - 2], result[result.size() - 1]));
        }

        SASSERT(!result.empty());
        SASSERT(check_interval_set(m_am, result.size(), result.c_ptr()));
        // Compress
        // Remark: we only combine adjacent intervals when they have the same justification
        unsigned j  = 0;
        unsigned sz = result.size(); 
        for (unsigned i = 1; i < sz; i++) {
            interval & curr = result[j];
            interval & next = result[i];
            if (curr.m_justification == next.m_justification && 
                adjacent(m_am, curr, next)) {
                // merge them
                curr.m_upper_inf  = next.m_upper_inf;
                curr.m_upper_open = next.m_upper_open;
                m_am.swap(curr.m_upper, next.m_upper);
            }
            else {
                j++;
                if (i != j) {
                    interval & next_curr = result[j];
                    next_curr.m_lower_inf = next.m_lower_inf;
                    next_curr.m_lower_open = next.m_lower_open;
                    m_am.swap(next_curr.m_lower, next.m_lower);
                    next_curr.m_upper_inf = next.m_upper_inf;
                    next_curr.m_upper_open = next.m_upper_open;
                    m_am.swap(next_curr.m_upper, next.m_upper);
                    next_curr.m_justification = next.m_justification;
                }
            }
        }
        j++;
        for (unsigned i = j; i < sz; i++) {
            interval & curr = result[i];
            m_am.del(curr.m_lower);
            m_am.del(curr.m_upper);
        }
        result.shrink(j);
        SASSERT(check_interval_set(m_am, result.size(), result.c_ptr()));
        sz = j;
        SASSERT(sz >= 1);
        bool found_slack  = !result[0].m_lower_inf || !result[sz-1].m_upper_inf;
        // Check if full
        for (unsigned i = 0; i < sz - 1 && !found_slack; i++) {
            if (!adjacent(m_am, result[i], result[i+1]))
                found_slack = true;
        }
        // Create new interval set
        interval_set * new_set = mk_interval(m_allocator, result, !found_slack);
        SASSERT(check_interval_set(m_am, sz, new_set->m_intervals));
        return new_set;
    }

    bool interval_set_manager::is_full(interval_set const * s) {
        if (s == nullptr)
            return false;
        return s->m_full == 1;
    }

    unsigned interval_set_manager::num_intervals(interval_set const * s) const {
        if (s == nullptr) return 0;
        return s->m_num_intervals;
    }
    
    bool interval_set_manager::subset(interval_set const * s1, interval_set const * s2) {
        if (s1 == s2)
            return true;
        if (s1 == nullptr)
            return true;
        if (s2 == nullptr)
            return false;
        if (s2->m_full)
            return true;
        if (s1->m_full)
            return false;
        unsigned sz1 = s1->m_num_intervals;
        unsigned sz2 = s2->m_num_intervals;
        SASSERT(sz1 > 0 && sz2 > 0);
        unsigned i1  = 0;
        unsigned i2  = 0;
        while (i1 < sz1 && i2 < sz2) {
            interval const & int1 = s1->m_intervals[i1];
            interval const & int2 = s2->m_intervals[i2];
            TRACE("nlsat_interval", tout << "subset main loop, i1: " << i1 << ", i2: " << i2 << "\n";
                  tout << "int1: "; nlsat::display(tout, m_am, int1); tout << "\n";
                  tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
            if (compare_lower_lower(m_am, int1, int2) < 0) {
                TRACE("nlsat_interval", tout << "done\n";);
                // interval [int1.lower1, int2.lower2] is not in s2
                // s1: [ ...
                // s2:    [ ...
                return false;
            }
            while (i2 < sz2) {
                interval const & int2 = s2->m_intervals[i2];
                TRACE("nlsat_interval", tout << "inner loop, i2: " << i2 << "\n";
                      tout << "int2: "; nlsat::display(tout, m_am, int2); tout << "\n";);
                int u1_u2_sign = compare_upper_upper(m_am, int1, int2);
                if (u1_u2_sign == 0) {
                    TRACE("nlsat_interval", tout << "case 1, break\n";);
                    // consume both
                    // s1: ... ]
                    // s2: ... ]
                    i1++;
                    i2++;
                    break;
                }
                else if (u1_u2_sign < 0) {
                    TRACE("nlsat_interval", tout << "case 2, break\n";);
                    // consume only int1, int2 may cover other intervals of s1 
                    // s1:  ... ]
                    // s2:    ... ]
                    i1++;
                    break;
                }
                else {
                    SASSERT(u1_u2_sign > 0);
                    int u2_l1_sign = compare_upper_lower(m_am, int2, int1);
                    TRACE("nlsat_interval", tout << "subset, u2_l1_sign: " << u2_l1_sign << "\n";);
                    if (u2_l1_sign < 0) {
                        TRACE("nlsat_interval", tout << "case 3, break\n";);
                        // s1:           [ ...
                        // s2: [ ... ]  ...
                        i2++;
                        break;
                    }
                    SASSERT(u2_l1_sign >= 0);
                    // s1:      [ ...  ]
                    // s2: [ ...    ]
                    if (i2 == sz2 - 1) {
                        TRACE("nlsat_interval", tout << "case 4, done\n";);
                        // s1:   ... ]
                        // s2: ...]
                        // the interval [int2.upper, int1.upper] is not in s2
                        return false; // last interval of s2
                    }
                    interval const & next2 = s2->m_intervals[i2+1];
                    if (!adjacent(m_am, int2, next2)) {
                        TRACE("nlsat_interval", tout << "not adjacent, done\n";);
                        // s1:   ... ]
                        // s2: ... ]   [
                        // the interval [int2.upper, min(int1.upper, next2.lower)] is not in s2
                        return false;
                    }
                    TRACE("nlsat_interval", tout << "continue..\n";);
                    // continue with adjacent interval of s2
                    // s1:    ...  ]
                    // s2:  ..][ ...
                    i2++;
                }
            }
        }
        return i1 == sz1;
    }

    bool interval_set_manager::set_eq(interval_set const * s1, interval_set const * s2) {
        if (s1 == nullptr || s2 == nullptr)
            return s1 == s2;
        if (s1->m_full || s2->m_full)
            return s1->m_full == s2->m_full;
        // TODO: check if bottleneck, then replace simple implementation
        return subset(s1, s2) && subset(s2, s1);
    }
        
    bool interval_set_manager::eq(interval_set const * s1, interval_set const * s2) {
        if (s1 == nullptr || s2 == nullptr)
            return s1 == s2;
        if (s1->m_num_intervals != s2->m_num_intervals)
            return false;
        for (unsigned i = 0; i < s1->m_num_intervals; i++) {
            interval const & int1 = s1->m_intervals[i];
            interval const & int2 = s2->m_intervals[i]; 
            if (int1.m_lower_inf  != int2.m_lower_inf ||
                int1.m_lower_open != int2.m_lower_open ||
                int1.m_upper_inf  != int2.m_upper_inf ||
                int1.m_upper_open != int2.m_upper_open ||
                int1.m_justification != int2.m_justification ||
                !m_am.eq(int1.m_lower, int2.m_lower) ||
                !m_am.eq(int1.m_upper, int2.m_upper))
                return false;
        }
        return true;
    }

    void interval_set_manager::get_justifications(interval_set const * s, literal_vector & js) {
        js.reset();
        unsigned num = num_intervals(s);
        for (unsigned i = 0; i < num; i++) {
            literal l     = s->m_intervals[i].m_justification;
            unsigned lidx = l.index();
            if (m_already_visited.get(lidx, false))
                continue;
            m_already_visited.setx(lidx, true, false);
            js.push_back(l);
        }
        for (unsigned i = 0; i < num; i++) {
            literal l     = s->m_intervals[i].m_justification;
            unsigned lidx = l.index();
            m_already_visited[lidx] = false;
        }
    }
    
    interval_set * interval_set_manager::get_interval(interval_set const * s, unsigned idx) const {
        SASSERT(idx < num_intervals(s));
        interval_buffer result;
        push_back(m_am, result, s->m_intervals[idx]);
        bool found_slack  = !result[0].m_lower_inf || !result[0].m_upper_inf;
        interval_set * new_set = mk_interval(m_allocator, result, !found_slack);
        SASSERT(check_interval_set(m_am, result.size(), new_set->m_intervals));
        return new_set;
    }

    void interval_set_manager::peek_in_complement(interval_set const * s, bool is_int, anum & w, bool randomize) {
        SASSERT(!is_full(s));
        if (s == nullptr) {
            if (randomize) {
                int num = m_rand() % 2 == 0 ? 1 : -1;
#define MAX_RANDOM_DEN_K 4
                int den_k = (m_rand() % MAX_RANDOM_DEN_K);
                int den   = is_int ? 1 : (1 << den_k);
                scoped_mpq _w(m_am.qm());
                m_am.qm().set(_w, num, den);
                m_am.set(w, _w);
                return;
            }
            else {
                m_am.set(w, 0);
                return;
            }
        }
        
        unsigned n = 0;
        
        unsigned num = num_intervals(s);
        if (!s->m_intervals[0].m_lower_inf) {
            // lower is not -oo
            n++;
            m_am.int_lt(s->m_intervals[0].m_lower, w);
            if (!randomize)
                return;
        }
        if (!s->m_intervals[num-1].m_upper_inf) {
            // upper is not oo
            n++;
            if (n == 1 || m_rand()%n == 0)
                m_am.int_gt(s->m_intervals[num-1].m_upper, w);
            if (!randomize)
                return;
        }
        
        // Try to find a gap that is not an unit.
        for (unsigned i = 1; i < num; i++) {
            if (m_am.lt(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower)) {
                n++;
                if (n == 1 || m_rand()%n == 0)
                    m_am.select(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower, w);
                if (!randomize)
                    return;
            }
        }
        
        if (n > 0)
            return;
        
        // Try to find a rational
        unsigned irrational_i = UINT_MAX;
        for (unsigned i = 1; i < num; i++) {
            if (s->m_intervals[i-1].m_upper_open && s->m_intervals[i].m_lower_open) {
                SASSERT(m_am.eq(s->m_intervals[i-1].m_upper, s->m_intervals[i].m_lower)); // otherwise we would have found it in the previous step
                if (m_am.is_rational(s->m_intervals[i-1].m_upper)) {
                    m_am.set(w, s->m_intervals[i-1].m_upper);
                    return;
                }
                if (irrational_i == UINT_MAX)
                    irrational_i = i-1;
            }
        }
        SASSERT(irrational_i != UINT_MAX);
        // Last option: peek irrational witness :-(
        SASSERT(s->m_intervals[irrational_i].m_upper_open && s->m_intervals[irrational_i+1].m_lower_open);
        m_am.set(w, s->m_intervals[irrational_i].m_upper);
    }

    void interval_set_manager::display(std::ostream & out, interval_set const * s) const {
        if (s == nullptr) {
            out << "{}";
            return;
        }
        out << "{";
        for (unsigned i = 0; i < s->m_num_intervals; i++) {
            if (i > 0)
                out << ", ";
            nlsat::display(out, m_am, s->m_intervals[i]);
        }
        out << "}";
        if (s->m_full)
            out << "*";
    }

};
