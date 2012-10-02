/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    nnf_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#ifndef _NNF_PARAMS_H_
#define _NNF_PARAMS_H_

#include"ini_file.h"

/**
   \brief NNF translation mode.  The cheapest mode is NNF_SKOLEM, and
   the most expensive is NNF_FULL.
*/
enum nnf_mode {
    NNF_SKOLEM, /* A subformula is put into NNF only if it contains
                   quantifiers or labels. The result of the
                   transformation will be in skolem normal form.
                   If a formula is too expensive to be put into NNF,
                   then nested quantifiers and labels are renamed.

                   This mode is sufficient when using E-matching.
                */
    NNF_QUANT, /* A subformula is put into NNF if it contains
                  quantifiers, labels, or is in the scope of a
                  quantifier. The result of the transformation will be
                  in skolem normal form, and the body of quantifiers
                  will be in NNF. If a ground formula is too expensive to
                  be put into NNF, then nested quantifiers and labels 
                  are renamed.

                  This mode is sufficient when using Superposition
                  Calculus.

                  Remark: If the problem does not contain quantifiers,
                  then NNF_QUANT is identical to NNF_SKOLEM.
               */
    NNF_OPPORTUNISTIC, /* Similar to NNF_QUANT, but a subformula is
                          also put into NNF, if it is
                          cheap. Otherwise, the nested quantifiers and
                          labels are renamed. */
    NNF_FULL /* Everything is put into NNF. */
};

struct nnf_params {
    nnf_mode m_nnf_mode;
    unsigned m_nnf_factor;
    bool     m_nnf_ignore_labels;
    bool     m_nnf_sk_hack;
    nnf_params():
        m_nnf_mode(NNF_SKOLEM),
        m_nnf_factor(4),
        m_nnf_ignore_labels(false),
        m_nnf_sk_hack(false) {
    }
    
    void register_params(ini_params & p);
};
    
#endif /* _NNF_PARAMS_H_ */

