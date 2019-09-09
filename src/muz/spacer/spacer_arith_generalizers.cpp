/*++
  Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

  Module Name:

  spacer_arith_generalizers.cpp

  Abstract:

  Arithmetic-related generalizers

  Author:

  Arie Gurfinkel

  Revision History:

  --*/

#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "muz/spacer/spacer_generalizers.h"

namespace spacer {

namespace {
/* Rewrite all denominators to be no larger than a given limit */
struct limit_denominator_rewriter_cfg : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_arith;
    rational m_limit;

    limit_denominator_rewriter_cfg(ast_manager &manager, rational limit)
        : m(manager), m_arith(m), m_limit(limit) {}

    bool is_numeral(func_decl *f, rational &val, bool &is_int) {
        if (f->get_family_id() == m_arith.get_family_id() &&
            f->get_decl_kind() == OP_NUM) {
            val = f->get_parameter(0).get_rational();
            is_int = f->get_parameter(1).get_int() != 0;
            return true;
        }
        return false;
    }

    bool limit_denominator(rational &num) {
        rational n, d;
        n = numerator(num);
        d = denominator(num);
        if (d < m_limit) return false;

        /*
          Iteratively computes approximation using continuous fraction
          decomposition

          p(-1) = 0, p(0) = 1
          p(j) = t(j)*p(j-1) + p(j-2)

          q(-1) = 1, q(0) = 0
          q(j) = t(j)*q(j-1) + q(j-2)

          cf[t1; t2, ..., tr] =  p(r) / q(r) for r >= 1
          reference: https://www.math.u-bordeaux.fr/~pjaming/M1/exposes/MA2.pdf
        */

        rational p0(0), p1(1);
        rational q0(1), q1(0);

        while (d != rational(0)) {
            rational tj(0), rem(0);
            rational p2(0), q2(0);
            tj = div(n, d);

            q2 = tj * q1 + q0;
            p2 = tj * p1 + p0;
            if (q2 >= m_limit) {
                num = p2/q2;
                return true;
            }
            rem = n - tj * d;
            p0 = p1;
            p1 = p2;
            q0 = q1;
            q1 = q2;
            n = d;
            d = rem;
        }
        return false;
    }

    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        bool is_int;
        rational val;

        if (is_numeral(f, val, is_int) && !is_int) {
            if (limit_denominator(val)) {
                result = m_arith.mk_numeral(val, false);
                return BR_DONE;
            }
        }
        return BR_FAILED;
    }
};
} // namespace
limit_num_generalizer::limit_num_generalizer(context &ctx,
                                                   unsigned failure_limit)
    : lemma_generalizer(ctx), m_failure_limit(failure_limit) {}

bool limit_num_generalizer::limit_denominators(expr_ref_vector &lits,
                                                  rational &limit) {
    ast_manager &m = m_ctx.get_ast_manager();
    limit_denominator_rewriter_cfg rw_cfg(m, limit);
    rewriter_tpl<limit_denominator_rewriter_cfg> rw(m, false, rw_cfg);

    expr_ref lit(m);
    bool dirty = false;
    for (unsigned i = 0, sz = lits.size(); i < sz; ++i) {
        rw(lits.get(i), lit);
        dirty |= (lits.get(i) != lit.get());
        lits[i] = lit;
    }
    return dirty;
}

void limit_num_generalizer::operator()(lemma_ref &lemma) {
    if (lemma->get_cube().empty()) return;

    m_st.count++;
    scoped_watch _w_(m_st.watch);

    unsigned uses_level;
    pred_transformer &pt = lemma->get_pob()->pt();
    ast_manager &m = pt.get_ast_manager();

    expr_ref_vector cube(m);

    unsigned weakness = lemma->weakness();
    rational limit(100);
    for (unsigned num_failures = 0; num_failures < m_failure_limit;
         ++num_failures) {
        cube.reset();
        cube.append(lemma->get_cube());
        // try to limit denominators
        if (!limit_denominators(cube, limit)) return;
        // check that the result is inductive
        if (pt.check_inductive(lemma->level(), cube, uses_level, weakness)) {
            lemma->update_cube(lemma->get_pob(), cube);
            lemma->set_level(uses_level);
            // done
            return;
        }
        ++m_st.num_failures;
        // increase limit
        limit = limit * 10;
    }
}

void limit_num_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.lim_num", m_st.watch.get_seconds());
    st.update("limitted num gen", m_st.count);
    st.update("limitted num gen failures", m_st.num_failures);
}
} // namespace spacer
