/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    critical flet.cpp

Abstract:

    Version of flet using "omp critical" directive.
    
    Warning: it uses omp critical section "critical_flet"

Author:

    Leonardo de Moura (leonardo) 2011-05-12

Revision History:

--*/
#ifndef _CRITICAL_FLET_H_
#define _CRITICAL_FLET_H_

template<typename T>
class critical_flet {
    T & m_ref;
    T   m_old_value;
public:
    critical_flet(T & ref, const T & new_value):
        m_ref(ref),
        m_old_value(ref) {
        #pragma omp critical (critical_flet)
        {
            m_ref = new_value;
        }
    }
    ~critical_flet() {
        #pragma omp critical (critical_flet)
        {
            m_ref = m_old_value;
        }
    }
};

#endif
