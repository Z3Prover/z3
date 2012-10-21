/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set_rewriter.h

Abstract:

    Apply rewriting rules in an assertion set.

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#ifndef _ASSERTION_SET_REWRITER_H_
#define _ASSERTION_SET_REWRITER_H_

#include"assertion_set_strategy.h"

class assertion_set_rewriter : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    assertion_set_rewriter(ast_manager & m, params_ref const & ref = params_ref());
    virtual ~assertion_set_rewriter();

    virtual void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    /**
       \brief Apply rewriting/simplification rules on the assertion set \c s.
    */
    void operator()(assertion_set & s);
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        operator()(s);
        mc = 0;
    }

    virtual void cleanup();

    unsigned get_num_steps() const;
    virtual void set_cancel(bool f);
};

inline as_st * mk_simplifier(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(assertion_set_rewriter, m, p));
}

#endif
