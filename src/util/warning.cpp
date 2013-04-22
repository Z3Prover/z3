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
#include<stdio.h>
#include<stdarg.h>

#include "error_codes.h"
#include "util.h"
#include "buffer.h"
#include "vector.h"

#ifdef _WINDOWS
#define PRF sprintf_s
#define VPRF vsprintf_s

void myInvalidParameterHandler(
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
#define PRF snprintf
#define VPRF vsnprintf
#define BEGIN_ERR_HANDLER() {}
#define END_ERR_HANDLER() {}
#endif

static bool g_warning_msgs   = true;
static bool g_use_std_stdout = false;
static std::ostream* g_error_stream = 0;
static std::ostream* g_warning_stream = 0;
static bool g_show_error_msg_prefix = true;

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

void disable_error_msg_prefix() {
    g_show_error_msg_prefix = false;
}

#if 0
// [Leo]: Do we need this?
static void string2ostream(std::ostream& out, char const* msg) {
    svector<char>  buff;
    buff.resize(10);
    BEGIN_ERR_HANDLER();                            
    while (true) {
        int nc = PRF(buff.c_ptr(), buff.size(), msg);                                                
        if (nc >= 0 && nc < static_cast<int>(buff.size()))
            break; // success
        buff.resize(buff.size()*2 + 1);             
    }         
    END_ERR_HANDLER();
    out << buff.c_ptr();
}
#endif

void format2ostream(std::ostream & out, char const* msg, va_list args) {
    svector<char>  buff;
#if !defined(_WINDOWS) && defined(_AMD64_)
    // see comment below.
    buff.resize(1024);
#else
    buff.resize(128);
#endif
    BEGIN_ERR_HANDLER();
    while (true) {
        int nc = VPRF(buff.c_ptr(), buff.size(), msg, args);                                                
#if !defined(_WINDOWS) && defined(_AMD64_)
	// For some strange reason, on Linux 64-bit version, va_list args is reset by vsnprintf.
	// Z3 crashes when trying to use va_list args again.
        // Hack: I truncate the message instead of expanding the buffer to make sure that
        // va_list args is only used once.
	END_ERR_HANDLER();
	if (nc < 0) {
	  // vsnprintf didn't work, so we just print the msg
	  out << msg; 
	  return;
	}
	if (nc >= static_cast<int>(buff.size())) {
          // truncate the message
          buff[buff.size() - 1] = 0;
	}
        out << buff.c_ptr();
	return;
#else
        if (nc >= 0 && nc < static_cast<int>(buff.size()))
            break; // success
        buff.resize(buff.size()*2 + 1);             
#endif
    }                   
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

