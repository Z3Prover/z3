/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    enum2bv_rewriter.h

Abstract:

    Conversion from enumeration types to bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-18

Notes:

--*/
#ifndef ENUM_REWRITER_H_
#define ENUM_REWRITER_H_

#include"datatype_decl_plugin.h"
#include"rewriter_types.h"
#include"expr_functors.h"

class enum2bv_rewriter {
    struct imp;
    imp* m_imp;
public:
    enum2bv_rewriter(ast_manager & m, params_ref const& p);
    ~enum2bv_rewriter();

    void updt_params(params_ref const & p);
    ast_manager & m() const;
    unsigned get_num_steps() const;
    void cleanup();
    obj_map<func_decl, func_decl*> const& enum2bv() const;
    obj_map<func_decl, func_decl*> const& bv2enum() const;
    obj_map<func_decl, expr*> const& enum2def() const;
    void operator()(expr * e, expr_ref & result, proof_ref & result_proof);
    void push();
    void pop(unsigned num_scopes);
    void flush_side_constraints(expr_ref_vector& side_constraints);
    unsigned num_translated() const;
    void set_is_fd(i_sort_pred* sp) const;
};

#endif
