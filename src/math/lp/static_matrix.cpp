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
#include "math/lp/lp_dual_core_solver.h"
#include "math/lp/lp_dual_simplex.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/scaler.h"
#include "math/lp/lar_solver.h"
namespace lp {
template void static_matrix<double, double>::add_columns_at_the_end(unsigned int);
template void static_matrix<double, double>::clear();
#ifdef Z3DEBUG
template bool static_matrix<double, double>::is_correct() const;
#endif
template void static_matrix<double, double>::copy_column_to_indexed_vector(unsigned int, indexed_vector<double>&) const;

template double static_matrix<double, double>::get_balance() const;
template std::set<std::pair<unsigned, unsigned>> static_matrix<double, double>::get_domain();
template std::set<std::pair<unsigned, unsigned>> lp::static_matrix<lp::mpq, lp::mpq>::get_domain();
template std::set<std::pair<unsigned, unsigned>> lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::get_domain();
template double static_matrix<double, double>::get_elem(unsigned int, unsigned int) const;
template double static_matrix<double, double>::get_max_abs_in_column(unsigned int) const;
template double static_matrix<double, double>::get_min_abs_in_column(unsigned int) const;
template double static_matrix<double, double>::get_min_abs_in_row(unsigned int) const;
template void static_matrix<double, double>::init_empty_matrix(unsigned int, unsigned int);
template void static_matrix<double, double>::init_row_columns(unsigned int, unsigned int);
template static_matrix<double, double>::ref & static_matrix<double, double>::ref::operator=(double const&);
template void static_matrix<double, double>::set(unsigned int, unsigned int, double const&);
template static_matrix<double, double>::static_matrix(unsigned int, unsigned int);
template void static_matrix<mpq, mpq>::add_column_to_vector(mpq const&, unsigned int, mpq*) const;
template void static_matrix<mpq, mpq>::add_columns_at_the_end(unsigned int);
template bool static_matrix<mpq, mpq>::is_correct() const;
template void static_matrix<mpq, mpq>::copy_column_to_indexed_vector(unsigned int, indexed_vector<mpq>&) const;

template mpq static_matrix<mpq, mpq>::get_balance() const;
template mpq static_matrix<mpq, mpq>::get_elem(unsigned int, unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_max_abs_in_column(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_max_abs_in_row(unsigned int) const;
template double static_matrix<double, double>::get_max_abs_in_row(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_min_abs_in_column(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_min_abs_in_row(unsigned int) const;
template void static_matrix<mpq, mpq>::init_row_columns(unsigned int, unsigned int);
template static_matrix<mpq, mpq>::ref& static_matrix<mpq, mpq>::ref::operator=(mpq const&);
template void static_matrix<mpq, mpq>::set(unsigned int, unsigned int, mpq const&);

template static_matrix<mpq, mpq>::static_matrix(unsigned int, unsigned int);
#ifdef Z3DEBUG
template bool static_matrix<mpq, numeric_pair<mpq> >::is_correct() const;
#endif
template void static_matrix<mpq, numeric_pair<mpq> >::copy_column_to_indexed_vector(unsigned int, indexed_vector<mpq>&) const;
template mpq static_matrix<mpq, numeric_pair<mpq> >::get_elem(unsigned int, unsigned int) const;
template void static_matrix<mpq, numeric_pair<mpq> >::init_empty_matrix(unsigned int, unsigned int);
template void static_matrix<mpq, numeric_pair<mpq> >::set(unsigned int, unsigned int, mpq const&);


template bool lp::static_matrix<double, double>::pivot_row_to_row_given_cell(unsigned int, column_cell &, unsigned int);
template bool lp::static_matrix<lp::mpq, lp::mpq>::pivot_row_to_row_given_cell(unsigned int, column_cell& , unsigned int);
template bool lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::pivot_row_to_row_given_cell(unsigned int, column_cell&, unsigned int);
template void lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::remove_element(vector<lp::row_cell<lp::mpq>, true, unsigned int>&, lp::row_cell<lp::mpq>&);

}

