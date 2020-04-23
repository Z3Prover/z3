/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    warning.cpp

Abstract:

    Support for warning messages.

Author:

    Leonardo de Moura (leonardo) 2006-12-01.

Revision History:

--*/
#include <stdio.h>
#include <stdarg.h>

#include "util/error_codes.h"
#include "util/util.h"
#include "util/buffer.h"
#include "util/vector.h"

#ifdef _WINDOWS
#if defined( __MINGW32__ ) && ( defined( __GNUG__ ) || defined( __clang__ ) )
#include <crtdbg.h>
#endif

#define VPRF vsprintf_s

void STD_CALL myInvalidParameterHandler(
    const wchar_t* expression,
    const wchar_t* function, 
    const wchar_t* file, 
    unsigned int line, 
    uintptr_t pReserved)
{
    // no-op
}

#define BEGIN_ERR_HANDLER() \
    _invalid_parameter_handler oldHandler, newHandler;  \
    newHandler = myInvalidParameterHandler; \
    oldHandler = _set_invalid_parameter_handler(newHandler); \
    _CrtSetReportMode(_CRT_ASSERT, 0); \

#define END_ERR_HANDLER() \
    _set_invalid_parameter_handler(oldHandler);

//   _invalid_parameter_handler oldHandler, newHandler;
//   newHandler = myInvalidParameterHandler;
//   oldHandler = _set_invalid_parameter_handler(newHandler);
// Disable the message box for assertions.


#else
#define VPRF vsnprintf
#define BEGIN_ERR_HANDLER() {}
#define END_ERR_HANDLER() {}
#endif

static bool g_warning_msgs   = true;
static bool g_use_std_stdout = false;
static std::ostream* g_error_stream = nullptr;
static std::ostream* g_warning_stream = nullptr;

void send_warnings_to_stdout(bool flag) {
    g_use_std_stdout = flag;
}

void enable_warning_messages(bool flag) {
    g_warning_msgs = flag;
}

void set_error_stream(std::ostream* strm) {
    g_error_stream = strm;
}

void set_warning_stream(std::ostream* strm) {
    g_warning_stream = strm;
}

void format2ostream(std::ostream & out, char const* msg, va_list args) {
    svector<char>  buff;
    BEGIN_ERR_HANDLER();

    va_list args_copy;
    va_copy(args_copy, args);
#ifdef _WINDOWS
    size_t msg_len = _vscprintf(msg, args_copy);
#else
    size_t msg_len = vsnprintf(nullptr, 0, msg, args_copy);
#endif
    va_end(args_copy);

    // +1 is for NUL termination.
    buff.resize(static_cast<unsigned>(msg_len + 1));

    VPRF(buff.c_ptr(), buff.size(), msg, args);

    END_ERR_HANDLER();
    out << buff.c_ptr();
}



void print_msg(std::ostream * out, const char* prefix, const char* msg, va_list args) {
    if (out) {
        *out << prefix;
        format2ostream(*out, msg, args);
        *out << "\n";
        out->flush();
    }
    else {
        FILE * f = g_use_std_stdout ? stdout : stderr;
        fprintf(f, "%s", prefix);
        vfprintf(f, msg, args);
        fprintf(f, "\n");
        fflush(f);
    };
}

void warning_msg(const char * msg, ...) {
    if (g_warning_msgs) {
        va_list args;
        va_start(args, msg);
        print_msg(g_warning_stream, "WARNING: ", msg, args);
        va_end(args);
    }
}
