/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_generalizers.h

Abstract:

    Generalizer plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-22.
    Arie Gurfinkel
Revision History:

--*/

#ifndef _SPACER_GENERALIZERS_H_
#define _SPACER_GENERALIZERS_H_

#include "muz/spacer/spacer_context.h"
#include "ast/arith_decl_plugin.h"

namespace spacer {

// can be used to check whether produced core is really implied by
// frame and therefore valid TODO: or negation?
class lemma_sanity_checker : public lemma_generalizer {
public:
    lemma_sanity_checker(context& ctx) : lemma_generalizer(ctx) {}
    ~lemma_sanity_checker() override {}
    void operator()(lemma_ref &lemma) override;
};

/**
 * Boolean inductive generalization by dropping literals
 */
class lemma_bool_inductive_generalizer : public lemma_generalizer {

    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() {reset();}
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    unsigned m_failure_limit;
    bool m_array_only;
    stats m_st;

public:
    lemma_bool_inductive_generalizer(context& ctx, unsigned failure_limit,
                                     bool array_only = false) :
        lemma_generalizer(ctx), m_failure_limit(failure_limit),
        m_array_only(array_only) {}
    ~lemma_bool_inductive_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics& st) const override;
    void reset_statistics() override {m_st.reset();}
};

class unsat_core_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    stats m_st;
public:
    unsat_core_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~unsat_core_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override {m_st.reset();}
};

class lemma_array_eq_generalizer : public lemma_generalizer {
private:
    bool is_array_eq(ast_manager &m, expr *e);
public:
    lemma_array_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_array_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

};

class lemma_eq_generalizer : public lemma_generalizer {
public:
    lemma_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
};

class lemma_quantifier_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() {reset();}
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    ast_manager &m;
    arith_util m_arith;
    stats m_st;
    expr_ref_vector m_cube;

    bool m_normalize_cube;
    int m_offset;
public:
    lemma_quantifier_generalizer(context &ctx, bool normalize_cube = true);
    ~lemma_quantifier_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics& st) const override;
    void reset_statistics() override {m_st.reset();}
private:
    bool generalize(lemma_ref &lemma, app *term);

    void find_candidates(expr *e, app_ref_vector &candidate);
    bool is_ub(var *var, expr *e);
    bool is_lb(var *var, expr *e);
    void mk_abs_cube (lemma_ref &lemma, app *term, var *var,
                      expr_ref_vector &gnd_cube,
                      expr_ref_vector &abs_cube,
                      expr *&lb, expr *&ub, unsigned &stride);

    bool match_sk_idx(expr *e, app_ref_vector const &zks, expr *&idx, app *&sk);
    void cleanup(expr_ref_vector& cube, app_ref_vector const &zks, expr_ref &bind);

    bool find_stride(expr_ref_vector &c, expr_ref &pattern, unsigned &stride);
};
}

#endif
