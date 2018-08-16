/*++
  Copyright (c) 2006 Microsoft Corporation

  Module Name:

  string_buffer.h

  Abstract:

  Simple string buffer

  Author:

  Leonardo de Moura (leonardo) 2006-10-14.

  Revision History:

  --*/
#ifndef STRING_BUFFER_H_
#define STRING_BUFFER_H_

#include<cstdio>
#include<string>
#include<string.h>
#include "util/util.h"
#include "util/memory_manager.h"

// This string buffer will not use the heap if the data consumes less than INITIAL_SIZE bytes. 
template<unsigned INITIAL_SIZE=64>
class string_buffer {
    char   m_initial_buffer[INITIAL_SIZE];
    char * m_buffer;
    size_t m_pos;
    size_t m_capacity;

    void expand() {
        size_t new_capacity = m_capacity << 1;
        char * new_buffer   = alloc_svect(char, new_capacity);
        memcpy(new_buffer, m_buffer, m_pos);
        if (m_capacity > INITIAL_SIZE) {
            dealloc_svect(m_buffer);
        }
        m_capacity = new_capacity;
        m_buffer   = new_buffer;
    }

    static const unsigned c_buffer_size = 24;

public:  
    string_buffer():
        m_buffer(m_initial_buffer),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
    }

    ~string_buffer() {
        if (m_capacity > INITIAL_SIZE) {
            dealloc_svect(m_buffer);
        }
    }

    void reset() {
        m_pos = 0;
    }

    void append(char c) {
        if (m_pos >= m_capacity) {
            expand();
        }
        m_buffer[m_pos] = c;
        m_pos++;
    }

    void append(const char * str) {
        size_t len       = strlen(str);
        size_t new_pos = m_pos + len;
        while (new_pos > m_capacity) {
            expand();
        }
        memcpy(m_buffer + m_pos, str, len);
        m_pos += len;
    }

    void append(int n) {
        char buffer[c_buffer_size]; 
        SPRINTF_D(buffer, n);
        append(buffer);
    }

    void append(unsigned n) {
        char buffer[c_buffer_size]; 
        SPRINTF_U(buffer, n);
        append(buffer);
    }

    void append(long n) {
        char buffer[c_buffer_size]; 
#ifdef _WINDOWS
        sprintf_s(buffer, Z3_ARRAYSIZE(buffer), "%ld", n);
#else
        sprintf(buffer, "%ld", n);
#endif
        append(buffer);
    }

    void append(bool b) {
        if (b) {
            append("true");
        }
        else {
            append("false");
        }
    }

    unsigned size() const {
        return m_pos;
    }

    bool empty() const { 
        return m_pos == 0;
    }
    
    const char * c_str() const {
        if (m_pos >= m_capacity) {
            const_cast<string_buffer * const>(this)->expand();
        }
        const_cast<string_buffer * const>(this)->m_buffer[m_pos] = 0;
        return m_buffer;
    }
};


template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, const char * str) {
    buffer.append(str);
    return buffer;
}

template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, char c) {
    buffer.append(c);
    return buffer;
}

template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, int i) {
    buffer.append(i);
    return buffer;
}

template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, unsigned i) {
    buffer.append(i);
    return buffer;
}

template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, bool b) {
    buffer.append(b);
    return buffer;
}

template<unsigned SZ>
inline string_buffer<SZ> & operator<<(string_buffer<SZ> & buffer, long l) {
    buffer.append(l);
    return buffer;
}

template<unsigned SZ1, unsigned SZ2>
inline string_buffer<SZ1> & operator<<(string_buffer<SZ1> & buffer1, const string_buffer<SZ2> & buffer2) {
    buffer1.append(buffer2.c_str());
    return buffer1;
}

#endif
