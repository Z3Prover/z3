
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/arith_eq_solver.h"
#include "smt/params/smt_params.h"

typedef rational numeral;
typedef vector<numeral> row;

static void test_solve_integer_equations(
    arith_eq_solver& asimp, 
    vector<row>& rows
    ) 
{
    row r_unsat;
 
    if (asimp.solve_integer_equations(rows, r_unsat)) {
        std::cout << "solved\n";
    }
    else {
        std::cout << "not solved\n";
        for (unsigned i = 0; i < r_unsat.size(); ++i) {
            std::cout << " " << r_unsat[i];
        }
        std::cout << "\n";
    }
}
               
void tst_arith_simplifier_plugin() {
    smt_params params;
    ast_manager m;
    arith_eq_solver asimp(m);
    
    row r1;
    row r2;

    r1.push_back(numeral(1));
    r1.push_back(numeral(2));
    r1.push_back(numeral(1));
    r1.push_back(numeral(2));

    r2.push_back(numeral(1));
    r2.push_back(numeral(2));
    r2.push_back(numeral(1));
    r2.push_back(numeral(2));

    vector<row> rows;
    rows.push_back(r1);
    rows.push_back(r2);

#if 0
    test_solve_integer_equations(asimp, rows);

    rows[1][3] = numeral(3);
    test_solve_integer_equations(asimp, rows);
#endif

    rows[0][0] = numeral(1);
    rows[0][1] = numeral(3);
    rows[0][2] = numeral(0);
    rows[0][3] = numeral(0);

    rows[1][0] = numeral(1);
    rows[1][1] = numeral(0);
    rows[1][2] = numeral(3);
    rows[1][3] = numeral(1);

    test_solve_integer_equations(asimp, rows);
    
}
