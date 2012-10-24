/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_exception.h

Abstract:

    Generic Z3 exception

Author:

    Leonardo (leonardo) 2011-04-28

Notes:

--*/
#ifndef _Z3_EXCEPTION_H_
#define _Z3_EXCEPTION_H_

#include<string>

class z3_exception {
public:
    virtual ~z3_exception() {}
    virtual char const * msg() const = 0;
    virtual unsigned error_code() const;
    bool has_error_code() const;
};

class z3_error : public z3_exception {
    unsigned m_error_code;
public:
    z3_error(unsigned error_code);
    virtual char const * msg() const;
    virtual unsigned error_code() const;
};

class default_exception : public z3_exception {
    std::string m_msg;
public:
    default_exception(std::string const& msg);
    default_exception(char const* msg, ...);
    virtual ~default_exception() {}
    virtual char const * msg() const;
};

#endif
