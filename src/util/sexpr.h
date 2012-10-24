/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sexpr.h

Abstract:

    Generic sexpr
    
Author:

    Leonardo (leonardo) 2011-07-28

Notes:

--*/
#ifndef _SEXPR_H_
#define _SEXPR_H_

#include"rational.h"
#include"symbol.h"
#include"obj_ref.h"
#include"ref_vector.h"

class sexpr_manager;

class sexpr {
public:
    enum kind_t {
        COMPOSITE, NUMERAL, BV_NUMERAL, STRING, KEYWORD, SYMBOL
    };
protected:
    kind_t   m_kind;
    unsigned m_ref_count;
    unsigned m_line;
    unsigned m_pos;
    sexpr(kind_t k, unsigned line, unsigned pos);
    void display_atom(std::ostream & out) const;
    friend class sexpr_manager;
public:
    void inc_ref() { m_ref_count++; }
    unsigned get_ref_count() const { return m_ref_count; }
    unsigned get_line() const { return m_line; }
    unsigned get_pos() const { return m_pos; }
    kind_t get_kind() const { return m_kind; }
    bool is_composite() const { return get_kind() == COMPOSITE; }
    bool is_numeral() const { return get_kind() == NUMERAL; }
    bool is_bv_numeral() const { return get_kind() == BV_NUMERAL; }
    bool is_string() const { return get_kind() == STRING; }
    bool is_keyword() const { return get_kind() == KEYWORD; }
    bool is_symbol() const { return get_kind() == SYMBOL; }
    rational const & get_numeral() const;
    unsigned get_bv_size() const;
    symbol get_symbol() const;
    std::string const & get_string() const;
    unsigned get_num_children() const;
    sexpr * get_child(unsigned idx) const;
    sexpr * const * get_children() const;
    void display(std::ostream & out) const;
};

class sexpr_manager {
    small_object_allocator m_allocator;
    ptr_vector<sexpr>      m_to_delete;
    void del(sexpr * n);
public:
    sexpr_manager();
    sexpr * mk_composite(unsigned num_children, sexpr * const * children, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_numeral(rational const & val, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_bv_numeral(rational const & val, unsigned bv_size, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_string(std::string const & val, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_string(char const * val, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_keyword(symbol const & val, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    sexpr * mk_symbol(symbol const & val, unsigned line = UINT_MAX, unsigned pos = UINT_MAX);
    void inc_ref(sexpr * n) { n->inc_ref(); }
    void dec_ref(sexpr * n) { SASSERT(n->m_ref_count > 0); n->m_ref_count--; if (n->m_ref_count == 0) del(n); }
};

typedef obj_ref<sexpr, sexpr_manager> sexpr_ref;
typedef ref_vector<sexpr, sexpr_manager> sexpr_ref_vector;

#endif
