/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    kbo.h

Abstract:

    Knuth-Bendix ordering.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#ifndef _KBO_H_
#define _KBO_H_

#include"order.h"

class kbo : public order {
    struct entry {
        expr_offset m_t1;
        expr_offset m_t2;
        unsigned    m_idx;
        entry():m_idx(UINT_MAX) {}
        entry(expr_offset const & t1, expr_offset const & t2, unsigned idx):
            m_t1(t1), m_t2(t2), m_idx(idx) {}
    };

    unsigned              m_var_weight;
    int                   m_weight_balance;
    var_offset_map<int>   m_deltas;
    unsigned              m_num_pos;
    unsigned              m_num_neg;
    svector<expr_offset>  m_vwbc_todo;
    svector<entry>        m_compare_todo;

    unsigned f_weight(func_decl * f) const;
    unsigned var_weight() const;
    
    void reset();
    void inc(expr_offset v);
    void dec(expr_offset v);

    template<bool pos>
    bool VWBc(expr_offset t, expr_offset target_var);

    template<bool pos>
    void VWB(expr_offset t, unsigned idx);
    
    result no_neg() const;
    result no_pos() const;

public:
    kbo(ast_manager & m, precedence * p, unsigned var_weight = 1):order(m, p), m_var_weight(var_weight) {}
    virtual ~kbo() {}
    virtual void reserve(unsigned num_offsets, unsigned num_vars) { m_deltas.reserve(num_offsets, num_vars); }
    virtual void reserve_offsets(unsigned num_offsets) { m_deltas.reserve_offsets(num_offsets); }
    virtual void reserve_vars(unsigned num_vars) { m_deltas.reserve_vars(num_vars); }
    virtual result compare(expr_offset const & t1, expr_offset const & t2, substitution * s);
    result compare(expr * t1, expr * t2) { return compare(expr_offset(t1, 0), expr_offset(t2, 0), 0); }
    virtual bool greater(expr_offset const & t1, expr_offset const & t2, substitution * s);
    virtual int compare_ge(expr_offset const & t1, expr_offset const & t2, substitution * s);
};

#endif /* _KBO_H_ */
