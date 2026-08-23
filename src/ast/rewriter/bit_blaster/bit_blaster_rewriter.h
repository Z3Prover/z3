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
#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/params.h"

class bit_blaster_rewriter {
    struct imp;
    imp * m_imp;
public:
    bit_blaster_rewriter(ast_manager & m, params_ref const & p);
    ~bit_blaster_rewriter();
    void updt_params(params_ref const & p);
    ast_manager & m() const;
    unsigned get_num_steps() const;
    void cleanup();
    void start_rewrite();
    void end_rewrite(obj_map<func_decl, expr*>& const2bits, ptr_vector<func_decl> & newbits);
    void get_translation(obj_map<func_decl, expr*>& const2bits, ptr_vector<func_decl> & newbits);
    void operator()(expr * e, expr_ref & result, proof_ref & result_proof);
    void push();
    void pop(unsigned num_scopes);
    unsigned get_num_scopes() const;
private:
    obj_map<func_decl, expr*> const& const2bits() const;     

};


