/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster.h

Abstract:

    Apply bit-blasting

Author:

    Leonardo (leonardo) 2011-10-25

--*/
#include "ast/rewriter/bit_blaster/bit_blaster_rewriter.h"
#include "ast/ast_pp.h"
#include "model/model_pp.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/simplifiers/dependent_expr_state.h"


class bit_blaster_simplifier : public dependent_expr_simplifier {

    bit_blaster_rewriter   m_rewriter;
    unsigned               m_num_steps = 0;
    params_ref             m_params;

public:
    bit_blaster_simplifier(ast_manager & m, params_ref const & p, dependent_expr_state& s):
        dependent_expr_simplifier(m, s),
        m_rewriter(m, p) {
        updt_params(p);
    }
    char const* name() const override { return "bit-blast"; }
    void updt_params(params_ref const & p) override;
    void collect_param_descrs(param_descrs & r) override;
    void reduce() override;
    void collect_statistics(statistics& st) const override;
    void push() override;
    void pop(unsigned n) override;

    /*
    * Expose the bit-blaster rewriter so that assumptions and implied bit-vectors can be reconstructed
    * after bit-blasting.
    */
    bit_blaster_rewriter& rewriter() { return m_rewriter; }

};

/*
  ADD_SIMPLIFIER("bit-blast", "reduce bit-vector expressions into SAT.", "alloc(bit_blaster_simplifier, m, p, s)")
*/
