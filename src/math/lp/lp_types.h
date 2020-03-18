/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
namespace lp {
typedef unsigned var_index;
typedef unsigned constraint_index;
typedef unsigned row_index;
enum lconstraint_kind { LE = -2, LT = -1 , GE = 2, GT = 1, EQ = 0, NE = 3 };


// index that comes from term or variable.
class tv {
    unsigned m_index;
    static const unsigned EF = UINT_MAX >> 1;
    tv(unsigned i): m_index(i) {}
public:
    static tv term(unsigned i) { SASSERT(0 == (i & left_most_bit)); return tv(mask_term(i)); }
    static tv var(unsigned i) { SASSERT(0 == (i & left_most_bit)); return tv(i); }
    static tv raw(unsigned i) { return tv(i); }

    // retrieve the identifier associated with tv
    unsigned id() const { return unmask_term(m_index); }

    // retrieve the raw index.
    unsigned index() const { return m_index; }

    bool is_term() const { return 0 != (m_index & left_most_bit); }
    bool is_var() const { return 0 == (m_index & left_most_bit); }

    // utilities useful where tv isn't already encapsulating id's.
    static inline unsigned unmask_term(unsigned j) { return j & EF; }
    static inline bool is_term(unsigned j) { return j & left_most_bit; }
    static inline unsigned mask_term(unsigned j) { return j | left_most_bit; }

    // used by var_register. could we encapsulate even this?
    static const unsigned left_most_bit  = ~EF;

};
}
