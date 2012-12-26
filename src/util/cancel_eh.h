/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cancel_eh.h

Abstract:

    Template for implementing simple event handler that just invokes cancel method.

Author:

    Leonardo de Moura (leonardo) 2011-04-27.

Revision History:

--*/
#ifndef _CANCEL_EH_H_
#define _CANCEL_EH_H_

#include"event_handler.h"

/**
   \brief Generic event handler for invoking cancel method.
*/
template<typename T>
class cancel_eh : public event_handler {
    T & m_obj;
public:
    cancel_eh(T & o):m_obj(o) {}
    ~cancel_eh() { m_obj.reset_cancel(); }
    virtual void operator()() { 
        m_obj.cancel(); 
    }
};

#endif
