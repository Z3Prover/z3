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
#ifndef WARNING_H_
#define WARNING_H_
#include<iostream>
#include<stdarg.h>

void send_warnings_to_stdout(bool flag);

void enable_warning_messages(bool flag);

void set_error_stream(std::ostream* strm);

void set_warning_stream(std::ostream* strm);

void warning_msg(const char * msg, ...);

void format2ostream(std::ostream& out, char const* fmt, va_list args);

#endif /* WARNING_H_ */

