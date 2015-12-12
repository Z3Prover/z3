/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aig.h

Abstract:

    And-inverted graphs

Author:

    Leonardo (leonardo) 2011-05-13

Notes:

--*/
#ifndef AIG_H_
#define AIG_H_

#include"ast.h"
#include"tactic_exception.h"

class goal;
class aig_lit;
class aig_manager;

class aig_exception : public tactic_exception {
public:                                                
    aig_exception(char const * msg):tactic_exception(msg) {}
};

class aig_ref {
    friend class aig_lit;
    friend class aig_manager;
    aig_manager * m_manager;
    void *        m_ref;
    aig_ref(aig_manager & m, aig_lit const & l);
public:
    aig_ref();
    ~aig_ref();
    aig_ref & operator=(aig_ref const & r);
    bool operator==(aig_ref const & r) const { return m_ref == r.m_ref; }
    bool operator!=(aig_ref const & r) const { return m_ref != r.m_ref; }
};

class aig_manager {
    struct imp;
    imp *  m_imp;
    friend class aig_ref;
public:
    // If default_gate_encoding == true, then
    // ite(a, b, c) is encoded as (NOT a OR b) AND (a OR c)
    // iff(a, b)    is encoded as (NOT a OR b) AND (a OR NOT b)
    //
    // If default_gate_encoding == false, then
    // ite(a, b, c) is encoded as (a AND b) OR (NOT a AND c)
    // iff(a, b)    is encoded as (a AND b) OR (NOT a AND NOT b)
    aig_manager(ast_manager & m, unsigned long long max_memory = UINT64_MAX, bool default_gate_encoding = true);
    ~aig_manager();
    void set_max_memory(unsigned long long max);
    aig_ref mk_aig(expr * n);
    aig_ref mk_aig(goal const & g); 
    aig_ref mk_not(aig_ref const & r);
    aig_ref mk_and(aig_ref const & r1, aig_ref const & r2);
    aig_ref mk_or(aig_ref const & r1, aig_ref const & r2);
    aig_ref mk_iff(aig_ref const & r1, aig_ref const & r2);
    aig_ref mk_ite(aig_ref const & r1, aig_ref const & r2, aig_ref const & r3);
    void max_sharing(aig_ref & r);
    void to_formula(aig_ref const & r, expr_ref & result);
    void to_formula(aig_ref const & r, goal & result);
    void display(std::ostream & out, aig_ref const & r) const;
    void display_smt2(std::ostream & out, aig_ref const & r) const;
    unsigned get_num_aigs() const;
};

#endif
