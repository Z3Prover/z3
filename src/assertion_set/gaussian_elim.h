/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    gaussian_elim.h

Abstract:

    (extended) Gaussian elimination for assertion sets.
    It also supports other theories besides arithmetic.

Author:

    Leonardo (leonardo) 2011-04-21

Notes:

--*/
#ifndef _GAUSSIAN_ELIM_H_
#define _GAUSSIAN_ELIM_H_

#include"assertion_set_strategy.h"

class expr_replacer;

MK_ST_EXCEPTION(gaussian_elim_exception);

class gaussian_elim : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    gaussian_elim(ast_manager & m, params_ref const & p = params_ref(), expr_replacer * r = 0, bool owner = false);
    virtual ~gaussian_elim();

    ast_manager & m () const;
    
    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    /**
       \brief Apply gaussian elimination on the assertion set \c s.
       Return a model_converter that converts any model for the updated set into a model for the old set.
    */
    virtual void operator()(assertion_set & s, model_converter_ref & mc);

    virtual void cleanup();
    
    unsigned get_num_steps() const;
    unsigned get_num_eliminated_vars() const;

    virtual void collect_statistics(statistics & st) const;
    virtual void reset_statistics();
protected:
    virtual void set_cancel(bool f);
};

as_st * mk_gaussian(ast_manager & m, params_ref const & p = params_ref());

inline as_st * mk_eq_solver(ast_manager & m, params_ref const & p = params_ref()) {
    return mk_gaussian(m, p);
}

#endif
