#pragma once
/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_expand_bnd_generalizer.h

  Abstract:

  Strengthen lemmas by changing numeral constants inside arithmetic literals

  Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "muz/spacer/spacer_context.h"

namespace spacer {

class lemma_expand_bnd_generalizer : public lemma_generalizer {
    struct stats {
        unsigned atmpts;
        unsigned success;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            watch.reset();
            atmpts = 0;
            success = 0;
        }
    };
    stats m_st;
    ast_manager &m;
    arith_util m_arith;

    /// A set of numeral values that can be used to expand bound
    vector<rational> m_values;

  public:
    lemma_expand_bnd_generalizer(context &ctx);

    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }

  private:

    /// Check whether lit ==> lit[val |--> n] (barring special cases). That is,
    /// whether \p lit becomes weaker if \p val is replaced with \p n
    ///
    /// \p lit has to be of the form t <= v where v is a numeral.
    /// Special cases:
    /// In the trivial case in which \p val == \p n, return false.
    /// if lit is an equality or the negation of an equality, return true.
    bool is_interesting(const expr *lit, rational val, rational n);

    /// check whether \p conj is a possible generalization for \p lemma.
    /// update \p lemma if it is.
    bool check_inductive(lemma_ref &lemma, expr_ref_vector &candiate);
};
} // namespace spacer
