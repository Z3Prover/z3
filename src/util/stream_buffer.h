/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    stream_buffer.h

Abstract:

    Simple stream buffer interface.
    In the future we should be able to read different kinds of stream (e.g., compressed files used
    in the SAT competitions).

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

--*/
#ifndef STREAM_BUFFER_H_
#define STREAM_BUFFER_H_

#include<iostream>

class stream_buffer {
    std::istream & m_stream;
    int            m_val;
public:
    
    stream_buffer(std::istream & s):
        m_stream(s) {
        m_val = m_stream.get();
    }

    int  operator *() const { 
        return m_val;
    }

    void operator ++() { 
        m_val = m_stream.get();
    }
};

#endif /* STREAM_BUFFER_H_ */

