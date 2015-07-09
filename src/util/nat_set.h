/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    nat_set.h

Abstract:

    Set of natural number with fast reset method.

Author:

    Leonardo de Moura (leonardo) 2007-03-27.

Revision History:

--*/
#ifndef NAT_SET_H_
#define NAT_SET_H_

#include<limits.h>
#include"vector.h"

class nat_set {
    unsigned          m_curr_timestamp;
    svector<unsigned> m_timestamps;

public:
    nat_set(unsigned s = 0):
        m_curr_timestamp(0),
        m_timestamps() {
        if (s > 0) {
            m_timestamps.resize(s, 0);
        }
    }

    // A nat_set is a function from [0..s-1] -> boolean.
    // This method sets the domain of this function.
    void set_domain(unsigned s) {
        m_timestamps.resize(s, 0);
    }

    unsigned get_domain() const {
        return m_timestamps.size();
    }

    // Assure that v is in the domain of the set.
    void assure_domain(unsigned v) {
        if (v >= get_domain()) {
            set_domain(v+1);
        }
    }

    bool contains(unsigned v) const {
        return m_timestamps[v] > m_curr_timestamp;
    }

    void insert(unsigned v) {
        m_timestamps[v] = m_curr_timestamp + 1;
    }

    void remove(unsigned v) {
        m_timestamps[v] = m_curr_timestamp;
    }

    void reset() {
        m_curr_timestamp++;
        if (m_curr_timestamp == UINT_MAX) {
            m_timestamps.fill(0);
            m_curr_timestamp = 0;
        }
    }

    bool empty() const {
        svector<unsigned>::const_iterator it  = m_timestamps.begin();
        svector<unsigned>::const_iterator end = m_timestamps.end();
        for (; it != end; ++it) {
            if (*it > m_curr_timestamp) {
                return false;
            }
        }
        return true;
    }
};

#endif /* NAT_SET_H_ */

