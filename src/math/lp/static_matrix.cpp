/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:

  Lev Nachmanson (levnach)

  Revision History:


  --*/
#include <memory>
#include "util/vector.h"
#include <set>
#include <utility>
#include "math/lp/static_matrix_def.h"
#include "math/lp/lp_core_solver_base.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/lar_solver.h"
namespace lp {
    
    template std::set<std::pair<unsigned, unsigned>> static_matrix<mpq, mpq>::get_domain();
    template std::set<std::pair<unsigned, unsigned>> static_matrix<mpq, numeric_pair<mpq> >::get_domain();
    template void static_matrix<mpq, mpq>::add_column_to_vector(mpq const&, unsigned int, mpq*) const;
    template bool static_matrix<mpq, mpq>::is_correct() const;

    template mpq static_matrix<mpq, mpq>::get_balance() const;
    template mpq static_matrix<mpq, mpq>::get_elem(unsigned int, unsigned int) const;
    template mpq static_matrix<mpq, mpq>::get_max_abs_in_column(unsigned int) const;
    template mpq static_matrix<mpq, mpq>::get_max_abs_in_row(unsigned int) const;
    template mpq static_matrix<mpq, mpq>::get_min_abs_in_column(unsigned int) const;
    template mpq static_matrix<mpq, mpq>::get_min_abs_in_row(unsigned int) const;
    template void static_matrix<mpq, mpq>::init_row_columns(unsigned int, unsigned int);
    template static_matrix<mpq, mpq>::ref& static_matrix<mpq, mpq>::ref::operator=(mpq const&);
    template void static_matrix<mpq, mpq>::set(unsigned int, unsigned int, mpq const&);

    template static_matrix<mpq, mpq>::static_matrix(unsigned int, unsigned int);
#ifdef Z3DEBUG
    template bool static_matrix<mpq, numeric_pair<mpq> >::is_correct() const;
#endif
    template mpq static_matrix<mpq, numeric_pair<mpq> >::get_elem(unsigned int, unsigned int) const;
    template void static_matrix<mpq, numeric_pair<mpq> >::init_empty_matrix(unsigned int, unsigned int);
    template void static_matrix<mpq, numeric_pair<mpq> >::set(unsigned int, unsigned int, mpq const&);


    template bool static_matrix<mpq, mpq>::pivot_row_to_row_given_cell(unsigned int, column_cell& , unsigned int);
    template bool static_matrix<mpq, numeric_pair<mpq> >::pivot_row_to_row_given_cell(unsigned int, column_cell&, unsigned int);
    template void static_matrix<mpq, numeric_pair<mpq> >::pivot_row_to_row_given_cell_with_sign(unsigned int, column_cell&, unsigned int, int);
    template void static_matrix<mpq, mpq>::pivot_row_to_row_given_cell_with_sign(unsigned int, row_cell<empty_struct>&, unsigned int, int);
    template void static_matrix<mpq, numeric_pair<mpq> >::add_rows(mpq const&, unsigned int, unsigned int);
    template void static_matrix<mpq,mpq>::add_rows(mpq const &,unsigned int,unsigned int);
    template void static_matrix<mpq, mpq>:: pivot_term_to_row_given_cell<lar_term>(lar_term const & term, column_cell&c, unsigned j, int j_sign);
    template void static_matrix<mpq, mpq>::add_term_to_row<lar_term>(const mpq& alpha, lar_term const & term, unsigned ii);
    template void static_matrix<mpq, numeric_pair<mpq> >::remove_element(std::vector<row_cell<mpq>, std_allocator<row_cell<mpq> > >&, row_cell<mpq>&);
}
