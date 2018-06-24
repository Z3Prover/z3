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
#ifndef Z3_EXCEPTION_H_
#define Z3_EXCEPTION_H_

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
    char const * msg() const override;
    unsigned error_code() const override;
};

class default_exception : public z3_exception {
    std::string m_msg;
public:
    struct fmt {};
    default_exception(std::string const& msg);
    default_exception(fmt, char const* msg, ...);
    ~default_exception() override {}
    char const * msg() const override;
};

#endif
