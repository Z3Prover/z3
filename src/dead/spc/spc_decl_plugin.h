/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_decl_plugin.h

Abstract:

    Proof declarations for Superposition Calculus Engine.

Author:

    Leonardo de Moura (leonardo) 2008-02-12.

Revision History:

--*/
#ifndef _SPC_DECL_PLUGIN_H_
#define _SPC_DECL_PLUGIN_H_

#include"ast.h"

enum spc_op_kind {
    PR_DEMODULATION,
    PR_SPC_REWRITE,
    PR_SPC_RESOLUTION,
    PR_SUPERPOSITION,
    PR_EQUALITY_RESOLUTION,
    PR_FACTORING,
    PR_SPC_DER,
    PR_SPC_ASSERTED,
    PR_SPC_LAST_ID
};

std::ostream & operator<<(std::ostream & out, spc_op_kind k);
  
class spc_decl_plugin : public decl_plugin {
    symbol m_demodulation;
    symbol m_spc_rewrite;
    symbol m_spc_resolution;
    symbol m_superposition;
    symbol m_equality_resolution;
    symbol m_factoring;
    symbol m_spc_der;

public:
    spc_decl_plugin();
    
    virtual ~spc_decl_plugin();

    virtual decl_plugin * mk_fresh() { return alloc(spc_decl_plugin); }
    
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters);
    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
};

#endif /* _SPC_DECL_PLUGIN_H_ */

