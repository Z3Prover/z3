#include "util/lp/emonomials.h"

static void display_mons(nla::emonomials const& em) {
    std::cout << em << "\n";
    for (auto const& m1 : em) {
        std::cout << "factors: " << m1 << ": \n";
        for (auto const& m2 : em.get_factors_of(m1)) {
            std::cout << m2 << "\n";
        }
    }
}

void tst_emonomials() {
    nla::var_eqs ve;
    nla::emonomials em(ve);

    unsigned x = 1;
    unsigned y = 2;
    unsigned z = 3;
    unsigned u = 4;
    unsigned v1 = 5;
    unsigned v2 = 6;
    unsigned v3 = 7;
    em.add(v1, x, x);
    em.add(v2, x, z);
    em.add(v3, x, y, x);
    display_mons(em);
    em.push();
    ve.merge_plus(x, y, nla::eq_justification({}));
    display_mons(em);
    em.push();
    ve.merge_plus(x, z, nla::eq_justification({}));
    display_mons(em);
    em.pop(1);
    display_mons(em);
}
