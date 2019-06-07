/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_exception.cpp

Abstract:

    Generic Z3 exception

Author:

    Leonardo (leonardo) 2012-04-12

Notes:

--*/
#include<stdarg.h>
#include<sstream>
#include "util/z3_exception.h"
#include "util/warning.h"
#include "util/error_codes.h"
#include "util/debug.h"

unsigned z3_exception::error_code() const { 
    return ERR_OK; 
}

bool z3_exception::has_error_code() const { 
    return error_code() != ERR_OK; 
}

z3_error::z3_error(unsigned error_code):m_error_code(error_code) { 
    SASSERT(error_code != 0); 
}

char const * z3_error::msg() const {
    switch (m_error_code) {
    case ERR_MEMOUT: return "out of memory";
    case ERR_TIMEOUT: return "timeout";
    case ERR_PARSER: return "parser error"; 
    case ERR_UNSOUNDNESS: return "unsoundess";
    case ERR_INCOMPLETENESS: return "incompleteness";
    case ERR_INI_FILE: return "invalid INI file";
    case ERR_NOT_IMPLEMENTED_YET: return "not implemented yet";
    case ERR_OPEN_FILE: return "open file";
    case ERR_CMD_LINE: return "invalid command line";
    case ERR_INTERNAL_FATAL: return "internal error";
    case ERR_TYPE_CHECK: return "type error";
    case ERR_ALLOC_EXCEEDED: return "number of configured allocations exceeded";
    default: return "unknown error";
    }
}

unsigned z3_error::error_code() const { 
    return m_error_code; 
}

default_exception::default_exception(fmt, char const* msg, ...) {
    std::stringstream out;
    va_list args;
    va_start(args, msg);
    format2ostream(out, msg, args);
    va_end(args);
    m_msg = out.str();
}

char const * default_exception::msg() const { 
    return m_msg.c_str(); 
}
