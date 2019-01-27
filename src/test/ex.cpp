/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ex.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-28

Revision History:

--*/
#include<iostream>
#include "util/z3_exception.h"

class ex {
public:
    virtual ~ex() {}
    virtual char const * msg() const = 0;
};

class ex1 : public ex {
    char const * m_msg;
public:
    ex1(char const * m):m_msg(m) {}
    char const * msg() const override { return m_msg; }
};

class ex2 : public ex {
    std::string m_msg;
public:
    ex2(char const * m):m_msg(m) {}
    char const * msg() const override { return m_msg.c_str(); }
};

static void th() {
    throw ex2("testing exception");
}

static void tst1() {
    try {
        th();
    }
    catch (ex & e) {
        std::cerr << e.msg() << "\n";
    }
}

static void tst2() {
    try {
        throw default_exception(default_exception::fmt(), "Format %d %s", 12, "twelve");
    }
    catch (z3_exception& ex) {
        std::cerr << ex.msg() << "\n";
    }
}

void tst_ex() {
    tst1();
    tst2();
}
