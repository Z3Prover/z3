/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set_util.h

Abstract:

    Assertion set goodies

Author:

    Leonardo de Moura (leonardo) 2011-04-28

Revision History:

--*/
#ifndef _ASSERTION_SET_UTIL_H_
#define _ASSERTION_SET_UTIL_H_

#include"assertion_set.h"
#include"shared_occs.h"

/**
   \brief Functor for computing the set of shared occurrences in an assertion set.
   
   It is essentially a wrapper for shared_occs functor.
*/
class as_shared_occs {
    shared_occs m_occs;
public:
    as_shared_occs(ast_manager & m, bool track_atomic = false, bool visit_quantifiers = true, bool visit_patterns = false):
        m_occs(m, track_atomic, visit_quantifiers, visit_patterns) {
    }
    void operator()(assertion_set const & s);
    bool is_shared(expr * t) { return m_occs.is_shared(t); }
    unsigned num_shared() const { return m_occs.num_shared(); }
    void reset() { return m_occs.reset(); }
    void cleanup() { return m_occs.cleanup(); }
    void display(std::ostream & out, ast_manager & m) const { m_occs.display(out, m); }
};

bool is_well_sorted(assertion_set const & s);

// Return true if the assertion set is propositional logic
bool is_propositional(assertion_set const & s);

// Return true if the assertion set is in QF_BV
bool is_qfbv(assertion_set const & s);

// Return true if the assertion set is in QF_LIA
bool is_qflia(assertion_set const & s);

// Return true if the assertion set is in QF_LRA
bool is_qflra(assertion_set const & s);

// Return true if the assertion set is in QF_LIRA
bool is_qflira(assertion_set const & s);

// Return true if the assertion set is in ILP problem (that is QF_LIA without boolean structure)
bool is_ilp(assertion_set const & s);

// Return true if the assertion set is in MIP problem (that is QF_LIRA without boolean structure)
bool is_mip(assertion_set const & s);
    
bool has_term_ite(assertion_set const & s);

inline bool is_decided(assertion_set const & s) { return s.size() == 0 || s.inconsistent(); }

template<typename Predicate>
bool test(assertion_set const & s, Predicate & proc) {
    expr_fast_mark1 visited;
    try {
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++)
            quick_for_each_expr(proc, visited, s.form(i));
    }
    catch (typename Predicate::found) {
        return true;
    }
    return false;
}

template<typename Predicate>
bool test(assertion_set const & s) {
    Predicate proc(s.m());
    return test(s, proc);
}

#endif
