/*++

  Module Name:

    qel.cpp

Abstract:
    Light weight quantifier elimination (QEL) based on term graph.

    The implementation is based on the following paper:

    Isabel Garcia-Contreras, Hari Govind V. K., Sharon Shoham, Arie Gurfinkel:
    Fast Approximations of Quantifier Elimination. Computer-Aided Verification
    (CAV). 2023. URL: https://arxiv.org/abs/2306.10009

Author:

    Hari Govind V K (hgvk94)
    Isabel Garcia (igcontreras)


--*/
#include "qe/lite/qel.h"
#include "qe/mbp/mbp_term_graph.h"

class qel::impl {
private:
    ast_manager &m;

public:
    impl(ast_manager &m, params_ref const &p) : m(m) {}

    void operator()(app_ref_vector &vars, expr_ref &fml) {
        if (vars.empty()) return;

        mbp::term_graph tg(m);
        tg.set_vars(vars);

        expr_ref_vector lits(m);
        flatten_and(fml, lits);
        tg.add_lits(lits);
        tg.qel(vars, fml);
    }
};

qel::qel(ast_manager &m, params_ref const &p) { m_impl = alloc(impl, m, p); }

qel::~qel() { dealloc(m_impl); }

void qel::operator()(app_ref_vector &vars, expr_ref &fml) {
    (*m_impl)(vars, fml);
}
