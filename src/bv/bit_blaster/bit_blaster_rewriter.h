/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_rewriter.h

Abstract:

    Bit-blasting rewriter

Author:

    Leonardo (leonardo) 2012-10-04

Notes:

--*/
#ifndef _BIT_BLASTER_REWRITER_H_
#define _BIT_BLASTER_REWRITER_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"params.h"

class bit_blaster_rewriter {
    struct imp;
    imp * m_imp;
public:
    bit_blaster_rewriter(ast_manager & m, params_ref const & p);
    ~bit_blaster_rewriter();
    void updt_params(params_ref const & p);
    void set_cancel(bool f);
    ast_manager & m() const;
    unsigned get_num_steps() const;
    void cleanup();
    obj_map<func_decl, expr*> const& const2bits() const; 
    void operator()(expr * e, expr_ref & result, proof_ref & result_proof);
};

#endif

