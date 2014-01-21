#include "sparse_matrix.h"
#include "sparse_matrix_def.h"
#include "simplex.h"
#include "simplex_def.h"

typedef simplex::simplex<simplex::mpz_ext> Simplex;

void tst_simplex() {
    simplex::sparse_matrix<simplex::mpz_ext> M;
    Simplex S;

    S.make_feasible();

    unsynch_mpz_manager m;
    scoped_mpz_vector coeffs(m);
    svector<unsigned> vars;
    for (unsigned i = 0; i < 5; ++i) {
        S.ensure_var(i);
        vars.push_back(i);
        coeffs.push_back(mpz(i+1));
    }

    Simplex::row r = S.add_row(1, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
}
