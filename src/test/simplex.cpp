#include "sparse_matrix.h"
#include "sparse_matrix_def.h"
#include "simplex.h"
#include "simplex_def.h"
#include "mpq_inf.h"

typedef simplex::simplex<simplex::mpz_ext> Simplex;

void tst_simplex() {
    simplex::sparse_matrix<simplex::mpz_ext> M;
    Simplex S;

    std::cout << "simplex\n";

    lbool is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";

    unsynch_mpz_manager m;
    unsynch_mpq_inf_manager em;
    scoped_mpz_vector coeffs(m);
    svector<unsigned> vars;
    for (unsigned i = 0; i < 5; ++i) {
        S.ensure_var(i);
        vars.push_back(i);
        coeffs.push_back(mpz(i+1));
    }

    Simplex::row r = S.add_row(1, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
    is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";
    S.display(std::cout);
    _scoped_numeral<unsynch_mpq_inf_manager> num(em); 
    num = std::make_pair(mpq(1), mpq(0));
    S.set_lower(0, num);
    S.set_upper(0, num);

    is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";
    S.display(std::cout);
}
