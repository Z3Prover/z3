/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_types.h

Abstract:

    Subpaving auxiliary types.

Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#pragma once

namespace subpaving {

class ineq;

typedef unsigned var;

const var null_var = UINT_MAX;

class exception {
};

class power : public std::pair<var, unsigned> {
public:
    power() = default;
    power(var v, unsigned d):std::pair<var, unsigned>(v, d) {}
    var x() const { return first; }
    var get_var() const { return first; }
    unsigned degree() const { return second; }
    unsigned & degree() { return second; }
    void set_var(var x) { first = x; }
    struct lt_proc { bool operator()(power const & p1, power const & p2) { return p1.get_var() < p2.get_var(); } };
};

struct display_var_proc {
    virtual void operator()(std::ostream & out, var x) const { out << "x" << x; }
};

}
