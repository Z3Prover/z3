/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    warning.h

Abstract:

    Support for warning messages.

Author:

    Leonardo de Moura (leonardo) 2006-12-01.

Revision History:

--*/
#ifndef _WARNING_H_
#define _WARNING_H_
#include<iostream>
#include<stdarg.h>

void send_warnings_to_stdout(bool flag);

void enable_warning_messages(bool flag);

void set_error_stream(std::ostream* strm);

void set_warning_stream(std::ostream* strm);

void warning_msg(const char * msg, ...);

void disable_error_msg_prefix();

void format2ostream(std::ostream& out, char const* fmt, va_list args);

class warning_displayer {
    const char * m_msg;
    bool         m_displayed;
public:
    warning_displayer(const char * msg):
        m_msg(msg),
        m_displayed(false) {
    }

    void sign() {
        if (!m_displayed) {
            warning_msg(m_msg);
            m_displayed = true;
        }
    }

    void reset() {
        m_displayed = false;
    }
};

#endif /* _WARNING_H_ */

