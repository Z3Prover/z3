/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_rewriter.h

Abstract:

    Conversion from pseudo-booleans to bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:

--*/
#ifndef PB2BV_REWRITER_H_
#define PB2BV_REWRITER_H_

#include "ast/pb_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/expr_functors.h"

class pb2bv_rewriter {
    struct imp;
    imp* m_imp;
public:
    pb2bv_rewriter(ast_manager & m, params_ref const& p);
    ~pb2bv_rewriter();

    void updt_params(params_ref const & p);
    void collect_param_descrs(param_descrs& r) const;
    ast_manager & m() const;
    unsigned get_num_steps() const;
    void cleanup();
    func_decl_ref_vector const& fresh_constants() const;
    void operator()(bool full, expr * e, expr_ref & result, proof_ref & result_proof);
    void push();
    void pop(unsigned num_scopes);
    void flush_side_constraints(expr_ref_vector& side_constraints);
    unsigned num_translated() const;
    void collect_statistics(statistics & st) const;
};

#endif
