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

#include <limits>
#if _LINUX_
#include <dirent.h>
#endif
#include <algorithm>
#include <string>
#include <set>
#include <iostream>
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <ctime>
#include <stdlib.h>
#include <utility>
#include "util/lp/lp_utils.h"
#include "util/lp/lp_primal_simplex.h"
#include "util/lp/mps_reader.h"
#include "test/smt_reader.h"
#include "util/lp/binary_heap_priority_queue.h"
#include "test/argument_parser.h"
#include "test/test_file_reader.h"
#include "util/lp/indexed_value.h"
#include "util/lp/lar_solver.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/binary_heap_upair_queue.h"
#include "util/lp/stacked_value.h"
#include "util/lp/stacked_unordered_set.h"
#include "util/lp/int_set.h"
#include "util/stopwatch.h"

namespace lp {
    unsigned seed = 1;

    random_gen g_rand;
    static unsigned my_random() {
        return g_rand();
    }
struct simple_column_namer:public column_namer
{
    std::string get_column_name(unsigned j) const override {
        return std::string("x") + T_to_string(j); 
    }
};


template <typename T, typename X>
void test_matrix(sparse_matrix<T, X> & a) {
    auto m = a.dimension();

// copy a to b in the reversed order
    sparse_matrix<T, X> b(m);
    std::cout << "copy b to a"<< std::endl;
    for (int row = m - 1; row >= 0; row--)
        for (int col = m - 1; col >= 0; col --) {
            b(row, col) = (T const&) a(row, col);
        }


    std::cout << "zeroing b in the reverse order"<< std::endl;
    for (int row = m - 1; row >= 0; row--)
        for (int col = m - 1; col >= 0; col --)
            b.set(row, col, T(0));



    for (unsigned row = 0; row < m; row ++)
        for (unsigned col = 0; col < m; col ++)
            a.set(row, col, T(0));


    unsigned i = my_random() % m;
    unsigned j = my_random() % m;

    auto t = T(1);

    a.set(i, j, t);

    SASSERT(a.get(i, j) == t);

    unsigned j1;
    if (j < m - 1) {
        j1 = m - 1;
        a.set(i, j1, T(2));
    }
}

void tst1() {
    std::cout << "testing the minimial matrix with 1 row and 1 column" << std::endl;
    sparse_matrix<double, double> m0(1);
    m0.set(0, 0, 1);
    // print_matrix(m0);
    m0.set(0, 0, 0);
    // print_matrix(m0);
    test_matrix(m0);

    unsigned rows = 2;
    sparse_matrix<double, double> m(rows);
    std::cout << "setting m(0,1)=" << std::endl;

    m.set(0, 1,  11);
    m.set(0, 0,  12);

    // print_matrix<double>(m);

    test_matrix(m);

    sparse_matrix<double, double> m1(2);
    m1.set(0, 0, 2);
    m1.set(1, 0, 3);
    // print_matrix(m1);
    std::cout << " zeroing matrix 2 by 2" << std::endl;
    m1.set(0, 0, 0);
    m1.set(1, 0, 0);
    // print_matrix(m1);

    test_matrix(m1);


    std::cout << "printing zero matrix 3 by 1" << std::endl;
    sparse_matrix<double, double> m2(3);
    // print_matrix(m2);

    m2.set(0, 0, 1);
    m2.set(2, 0, 2);
    std::cout << "printing  matrix 3 by 1 with a gap" << std::endl;
    // print_matrix(m2);

    test_matrix(m2);

    sparse_matrix<double, double> m10by9(10);
    m10by9.set(0, 1, 1);

    m10by9(0, 1) = 4;

    double test = m10by9(0, 1);

    std::cout << "got " << test << std::endl;


    m10by9.set(0, 8, 8);
    m10by9.set(3, 4, 7);
    m10by9.set(3, 2, 5);
    m10by9.set(3, 8, 99);
    m10by9.set(3, 2, 6);
    m10by9.set(1, 8, 9);
    m10by9.set(4, 0, 40);
    m10by9.set(0, 0, 10);

    std::cout << "printing  matrix 10 by 9" << std::endl;
    // print_matrix(m10by9);


    test_matrix(m10by9);
    std::cout <<"zeroing m10by9\n";
#ifdef Z3DEBUG
    for (unsigned int i = 0; i < m10by9.dimension(); i++)
        for (unsigned int j = 0; j < m10by9.column_count(); j++)
            m10by9.set(i, j, 0);
#endif
    // print_matrix(m10by9);
}

vector<int> allocate_basis_heading(unsigned count) { // the rest of initilization will be handled by lu_QR
    vector<int> basis_heading(count, -1);
    return basis_heading;
}


void init_basic_part_of_basis_heading(vector<unsigned> & basis, vector<int> & basis_heading) {
    SASSERT(basis_heading.size() >= basis.size());
    unsigned m = basis.size();
    for (unsigned i = 0; i < m; i++) {
        unsigned column = basis[i];
        basis_heading[column] = i;
    }
}

void init_non_basic_part_of_basis_heading(vector<int> & basis_heading, vector<unsigned> & non_basic_columns) {
    non_basic_columns.clear();
    for (int j = basis_heading.size(); j--;){
        if (basis_heading[j] < 0) {
                non_basic_columns.push_back(j);
                // the index of column j in m_nbasis is (- basis_heading[j] - 1)
                basis_heading[j] = - static_cast<int>(non_basic_columns.size());
        }
    }
}
void init_basis_heading_and_non_basic_columns_vector(vector<unsigned> & basis,
                                                     vector<int> & basis_heading,
                                                     vector<unsigned> & non_basic_columns) {
    init_basic_part_of_basis_heading(basis, basis_heading);
    init_non_basic_part_of_basis_heading(basis_heading, non_basic_columns);
}

void change_basis(unsigned entering, unsigned leaving, vector<unsigned>& basis, vector<unsigned>& nbasis, vector<int> & basis_heading) {
    int place_in_basis =  basis_heading[leaving];
    int place_in_non_basis = - basis_heading[entering] - 1;
    basis_heading[entering] = place_in_basis;
    basis_heading[leaving] = -place_in_non_basis - 1;
    basis[place_in_basis] = entering;
    nbasis[place_in_non_basis] = leaving;
}


#ifdef Z3DEBUG
void test_small_lu(lp_settings & settings) {
    std::cout << " test_small_lu" << std::endl;
    static_matrix<double, double> m(3, 6);
    vector<unsigned> basis(3);
    basis[0] = 0;
    basis[1] = 1;
    basis[2] = 3;

    m(0, 0) = 1; m(0, 2)= 3.9; m(2, 3) = 11; m(0, 5) = -3;
    m(1, 1) = 4; m(1, 4) = 7;
    m(2, 0) = 1.8; m(2, 2) = 5; m(2, 4) = 2; m(2, 5) = 8;

#ifdef Z3DEBUG
    print_matrix(m, std::cout);
#endif
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, heading, non_basic_columns);
    lu<double, double> l(m, basis, settings);
    SASSERT(l.is_correct(basis));
    indexed_vector<double> w(m.row_count());
    std::cout << "entering 2, leaving 0" << std::endl;
    l.prepare_entering(2, w); // to init vector w
    l.replace_column(0, w, heading[0]);
    change_basis(2, 0, basis, non_basic_columns, heading);
    // #ifdef Z3DEBUG
    // std::cout << "we were factoring " << std::endl;
    // print_matrix(get_B(l));
    // #endif
    SASSERT(l.is_correct(basis));
    std::cout << "entering 4, leaving 3" << std::endl;
    l.prepare_entering(4, w); // to init vector w
    l.replace_column(0, w, heading[3]);
    change_basis(4, 3, basis, non_basic_columns, heading);
    std::cout << "we were factoring " << std::endl;
#ifdef Z3DEBUG
    {
        auto bl = get_B(l, basis);
        print_matrix(&bl, std::cout);
    }
#endif
    SASSERT(l.is_correct(basis));

    std::cout << "entering 5, leaving 1" << std::endl;
    l.prepare_entering(5, w); // to init vector w
    l.replace_column(0, w, heading[1]);
    change_basis(5, 1, basis, non_basic_columns, heading);
    std::cout << "we were factoring " << std::endl;
#ifdef Z3DEBUG
    {
        auto bl = get_B(l, basis);
        print_matrix(&bl, std::cout);
    }
#endif
    SASSERT(l.is_correct(basis));
    std::cout << "entering 3, leaving 2" << std::endl;
    l.prepare_entering(3, w); // to init vector w
    l.replace_column(0, w, heading[2]);
    change_basis(3, 2, basis, non_basic_columns, heading);
    std::cout << "we were factoring " << std::endl;
#ifdef Z3DEBUG
    {
        auto bl = get_B(l, basis);
        print_matrix(&bl, std::cout);
    }
#endif
    SASSERT(l.is_correct(basis));

    m.add_row();
    m.add_column();
    m.add_row();
    m.add_column();
    for (unsigned i = 0; i < m.column_count(); i++) {
        m(3, i) = i;
        m(4, i) = i * i; // to make the rows linearly independent
    }
    unsigned j = m.column_count() ;
    basis.push_back(j-2);
    heading.push_back(basis.size() - 1);
    basis.push_back(j-1);
    heading.push_back(basis.size() - 1);
    
    auto columns_to_replace = l.get_set_of_columns_to_replace_for_add_last_rows(heading);
    l.add_last_rows_to_B(heading, columns_to_replace);
    std::cout << "here" << std::endl;
    SASSERT(l.is_correct(basis));
}

#endif

void fill_long_row(sparse_matrix<double, double> &m, int i) {
    int n = m.dimension();
    for (int j = 0; j < n; j ++) {
        m (i, (j + i) % n) = j * j;
    }
}

void fill_long_row(static_matrix<double, double> &m, int i) {
    int n = m.column_count();
    for (int j = 0; j < n; j ++) {
        m (i, (j + i) % n) = j * j;
    }
}


void fill_long_row_exp(sparse_matrix<double, double> &m, int i) {
    int n = m.dimension();

    for (int j = 0; j < n; j ++) {
        m(i, j) = my_random() % 20;
    }
}

void fill_long_row_exp(static_matrix<double, double> &m, int i) {
    int n = m.column_count();

    for (int j = 0; j < n; j ++) {
        m(i, j) = my_random() % 20;
    }
}

void fill_larger_sparse_matrix_exp(sparse_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.dimension(); i++ )
        fill_long_row_exp(m, i);
}

void fill_larger_sparse_matrix_exp(static_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.row_count(); i++ )
        fill_long_row_exp(m, i);
}


void fill_larger_sparse_matrix(sparse_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.dimension(); i++ )
        fill_long_row(m, i);
}

void fill_larger_sparse_matrix(static_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.row_count(); i++ )
        fill_long_row(m, i);
}


int perm_id = 0;

#ifdef Z3DEBUG
void test_larger_lu_exp(lp_settings & settings) {
    std::cout << " test_larger_lu_exp" << std::endl;
    static_matrix<double, double> m(6, 12);
    vector<unsigned> basis(6);
    basis[0] = 1;
    basis[1] = 3;
    basis[2] = 0;
    basis[3] = 4;
    basis[4] = 5;
    basis[5] = 6;


    fill_larger_sparse_matrix_exp(m);
    // print_matrix(m);
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, heading, non_basic_columns);
    lu<double, double> l(m, basis, settings);

    dense_matrix<double, double> left_side = l.get_left_side(basis);
    dense_matrix<double, double> right_side = l.get_right_side();
    SASSERT(left_side == right_side);
    int leaving = 3;
    int entering = 8;
    for (unsigned i = 0; i < m.row_count(); i++) {
        std::cout << static_cast<double>(m(i, entering)) << std::endl;
    }

    indexed_vector<double> w(m.row_count());

    l.prepare_entering(entering, w);
    l.replace_column(0, w, heading[leaving]);
    change_basis(entering, leaving, basis, non_basic_columns, heading);
    SASSERT(l.is_correct(basis));

    l.prepare_entering(11, w); // to init vector w
    l.replace_column(0, w, heading[0]);
    change_basis(11, 0, basis, non_basic_columns, heading);
    SASSERT(l.is_correct(basis));
}

void test_larger_lu_with_holes(lp_settings & settings) {
    std::cout << " test_larger_lu_with_holes" << std::endl;
    static_matrix<double, double> m(8, 9);
    vector<unsigned> basis(8);
    for (unsigned i = 0; i < m.row_count(); i++) {
        basis[i] = i;
    }
    m(0, 0) = 1; m(0, 1) = 2; m(0, 2) = 3; m(0, 3) = 4; m(0, 4) = 5; m(0, 8) = 99;
    /*        */ m(1, 1) =- 6; m(1, 2) = 7; m(1, 3) = 8; m(1, 4) = 9;
    /*                     */ m(2, 2) = 10;
    /*                     */ m(3, 2) = 11; m(3, 3) = -12;
    /*                     */ m(4, 2) = 13; m(4, 3) = 14; m(4, 4) = 15;
    // the rest of the matrix is denser
    m(5, 4) = 28; m(5, 5) = -18; m(5, 6) = 19; m(5, 7) = 25;
    /*        */  m(6, 5) = 20; m(6, 6) = -21;
    /*        */  m(7, 5) = 22; m(7, 6) = 23; m(7, 7) = 24; m(7, 8) = 88;
    print_matrix(m, std::cout);
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, heading, non_basic_columns);
    lu<double, double> l(m, basis, settings);
    std::cout << "printing factorization" << std::endl;
    for (int i = l.tail_size() - 1; i >=0; i--) {
        auto lp = l.get_lp_matrix(i);
        lp->set_number_of_columns(m.row_count());
        lp->set_number_of_rows(m.row_count());
        print_matrix( lp, std::cout);
    }

    dense_matrix<double, double> left_side = l.get_left_side(basis);
    dense_matrix<double, double> right_side = l.get_right_side();
    if (!(left_side == right_side)) {
        std::cout << "different sides" << std::endl;
    }

    indexed_vector<double> w(m.row_count());
    l.prepare_entering(8, w); // to init vector w
    l.replace_column(0, w, heading[0]);
    change_basis(8, 0, basis, non_basic_columns, heading);
    SASSERT(l.is_correct(basis));
}


void test_larger_lu(lp_settings& settings) {
    std::cout << " test_larger_lu" << std::endl;
    static_matrix<double, double> m(6, 12);
    vector<unsigned> basis(6);
    basis[0] = 1;
    basis[1] = 3;
    basis[2] = 0;
    basis[3] = 4;
    basis[4] = 5;
    basis[5] = 6;


    fill_larger_sparse_matrix(m);
    print_matrix(m, std::cout);

    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, heading, non_basic_columns);
    auto l = lu<double, double> (m, basis, settings);
    // std::cout << "printing factorization" << std::endl;
    // for (int i = lu.tail_size() - 1; i >=0; i--) {
    //     auto lp = lu.get_lp_matrix(i);
    //     lp->set_number_of_columns(m.row_count());
    //     lp->set_number_of_rows(m.row_count());
    //     print_matrix(* lp);
    // }

    dense_matrix<double, double> left_side = l.get_left_side(basis);
    dense_matrix<double, double> right_side = l.get_right_side();
    if (!(left_side == right_side)) {
        std::cout << "left side" << std::endl;
        print_matrix(&left_side, std::cout);
        std::cout << "right side" << std::endl;
        print_matrix(&right_side, std::cout);

        std::cout << "different sides" << std::endl;
        std::cout << "initial factorization is incorrect" << std::endl;
        exit(1);
    }
    indexed_vector<double> w(m.row_count());
    l.prepare_entering(9, w); // to init vector w
    l.replace_column(0, w, heading[0]);
    change_basis(9, 0, basis, non_basic_columns, heading);
    SASSERT(l.is_correct(basis));
}


void test_lu(lp_settings & settings) {
    test_small_lu(settings);
    test_larger_lu(settings);
    test_larger_lu_with_holes(settings);
    test_larger_lu_exp(settings);
}
#endif






void init_b(vector<double> & b, sparse_matrix<double, double> & m, vector<double>& x) {
    for (unsigned i = 0; i < m.dimension(); i++) {
        b.push_back(m.dot_product_with_row(i, x));
    }
}

void init_b(vector<double> & b, static_matrix<double, double> & m, vector<double> & x) {
    for (unsigned i = 0; i < m.row_count(); i++) {
        b.push_back(m.dot_product_with_row(i, x));
    }
}


void test_lp_0() {
    std::cout << " test_lp_0 " << std::endl;
    static_matrix<double, double> m_(3, 7);
    m_(0, 0) = 3; m_(0, 1) = 2; m_(0, 2) = 1; m_(0, 3) = 2; m_(0, 4) = 1;
    m_(1, 0) = 1; m_(1, 1) = 1; m_(1, 2) = 1; m_(1, 3) = 1; m_(1, 5) = 1;
    m_(2, 0) = 4; m_(2, 1) = 3; m_(2, 2) = 3; m_(2, 3) = 4; m_(2, 6) = 1;
    vector<double> x_star(7);
    x_star[0] = 225; x_star[1] = 117; x_star[2] = 420;
    x_star[3] = x_star[4] = x_star[5] = x_star[6] = 0;
    vector<double> b;
    init_b(b, m_, x_star);
    vector<unsigned> basis(3);
    basis[0] = 0; basis[1] = 1; basis[2] = 2;
    vector<double> costs(7);
    costs[0] = 19;
    costs[1] = 13;
    costs[2] = 12;
    costs[3] = 17;
    costs[4] = 0;
    costs[5] = 0;
    costs[6] = 0;
    
    vector<column_type> column_types(7, column_type::low_bound);
    vector<double>  upper_bound_values;
    lp_settings settings;
    simple_column_namer cn;
    vector<unsigned> nbasis;
    vector<int>  heading;

        lp_primal_core_solver<double, double> lpsolver(m_, b, x_star, basis, nbasis, heading, costs, column_types, upper_bound_values, settings, cn);

    lpsolver.solve();
}

void test_lp_1() {
    std::cout << " test_lp_1 " << std::endl;
    static_matrix<double, double> m(4, 7);
    m(0, 0) =  1;  m(0, 1) = 3;  m(0, 2) = 1;  m(0, 3) = 1;
    m(1, 0) = -1;                m(1, 2) = 3;  m(1, 4) = 1;
    m(2, 0) =  2;  m(2, 1) = -1; m(2, 2) = 2;  m(2, 5) = 1;
    m(3, 0) =  2;  m(3, 1) =  3; m(3, 2) = -1; m(3, 6) = 1;
#ifdef Z3DEBUG
    print_matrix(m, std::cout);
#endif
    vector<double> x_star(7);
    x_star[0] = 0; x_star[1] = 0; x_star[2] = 0;
    x_star[3] = 3; x_star[4] = 2; x_star[5] = 4; x_star[6] = 2;

    vector<unsigned> basis(4);
    basis[0] = 3; basis[1] = 4; basis[2] = 5; basis[3] = 6;

    vector<double> b;
    b.push_back(3);
    b.push_back(2);
    b.push_back(4);
    b.push_back(2);

    vector<double> costs(7);
    costs[0] = 5;
    costs[1] = 5;
    costs[2] = 3;
    costs[3] = 0;
    costs[4] = 0;
    costs[5] = 0;
    costs[6] = 0;



    vector<column_type> column_types(7, column_type::low_bound);
    vector<double>  upper_bound_values;

    std::cout << "calling lp\n";
    lp_settings settings;
    simple_column_namer cn;

    vector<unsigned> nbasis;
    vector<int>  heading;

    lp_primal_core_solver<double, double> lpsolver(m, b,
                                                   x_star,
                                                   basis,
                                                   nbasis, heading,
                                                   costs,
                                                   column_types, upper_bound_values, settings, cn);
    
    lpsolver.solve();
}


void test_lp_primal_core_solver() {
    test_lp_0();
    test_lp_1();
}


#ifdef Z3DEBUG
template <typename T, typename X>
void test_swap_rows_with_permutation(sparse_matrix<T, X>& m){
    std::cout << "testing swaps" << std::endl;
    unsigned dim = m.row_count();
    dense_matrix<double, double> original(&m);
    permutation_matrix<double, double> q(dim);
    print_matrix(m, std::cout);
    SASSERT(original == q * m);
    for (int i = 0; i < 100; i++) {
        unsigned row1 = my_random() % dim;
        unsigned row2 = my_random() % dim;
        if (row1 == row2) continue;
        std::cout << "swap " << row1 << " " << row2 << std::endl;
        m.swap_rows(row1, row2);
        q.transpose_from_left(row1, row2);
        SASSERT(original == q * m);
        print_matrix(m, std::cout);
        std::cout << std::endl;
    }
}
#endif
template <typename T, typename X>
void fill_matrix(sparse_matrix<T, X>& m); // forward definition
#ifdef Z3DEBUG
template <typename T, typename X>
void test_swap_cols_with_permutation(sparse_matrix<T, X>& m){
    std::cout << "testing swaps" << std::endl;
    unsigned dim = m.row_count();
    dense_matrix<double, double> original(&m);
    permutation_matrix<double, double> q(dim);
    print_matrix(m, std::cout);
    SASSERT(original == q * m);
    for (int i = 0; i < 100; i++) {
        unsigned row1 = my_random() % dim;
        unsigned row2 = my_random() % dim;
        if (row1 == row2) continue;
        std::cout << "swap " << row1 << " " << row2 << std::endl;
        m.swap_rows(row1, row2);
        q.transpose_from_right(row1, row2);
        SASSERT(original == q * m);
        print_matrix(m, std::cout);
        std::cout << std::endl;
    }
}


template <typename T, typename X>
void test_swap_rows(sparse_matrix<T, X>& m, unsigned i0, unsigned i1){
    std::cout << "test_swap_rows(" << i0 << "," << i1 << ")" << std::endl;
    sparse_matrix<T, X> mcopy(m.dimension());
    for (unsigned i = 0; i  < m.dimension(); i++)
        for (unsigned j = 0; j < m.dimension(); j++) {
            mcopy(i, j)= m(i, j);
    }
    std::cout << "swapping rows "<< i0 << "," << i1 << std::endl;
    m.swap_rows(i0, i1);

    for (unsigned j = 0; j < m.dimension(); j++) {
        SASSERT(mcopy(i0, j) == m(i1, j));
        SASSERT(mcopy(i1, j) == m(i0, j));
    }
}
template <typename T, typename X>
void test_swap_columns(sparse_matrix<T, X>& m, unsigned i0, unsigned i1){
    std::cout << "test_swap_columns(" << i0 << "," << i1 << ")" << std::endl;
    sparse_matrix<T, X> mcopy(m.dimension());
    for (unsigned i = 0; i  < m.dimension(); i++)
        for (unsigned j = 0; j < m.dimension(); j++) {
            mcopy(i, j)= m(i, j);
    }
    m.swap_columns(i0, i1);

    for (unsigned j = 0; j < m.dimension(); j++) {
        SASSERT(mcopy(j, i0) == m(j, i1));
        SASSERT(mcopy(j, i1) == m(j, i0));
    }

    for (unsigned i = 0; i  < m.dimension(); i++) {
        if (i == i0 || i == i1)
            continue;
        for (unsigned j = 0; j < m.dimension(); j++) {
            SASSERT(mcopy(j, i)== m(j, i));
        }
    }
}
#endif

template <typename T, typename X>
void fill_matrix(sparse_matrix<T, X>& m){
    int v = 0;
    for (int i = m.dimension() - 1; i >= 0; i--) {
        for (int j = m.dimension() - 1; j >=0; j--){
            m(i, j) = v++;
        }
    }
}

void test_pivot_like_swaps_and_pivot(){
    sparse_matrix<double, double> m(10);
    fill_matrix(m);
    // print_matrix(m);
// pivot at 2,7
    m.swap_columns(0, 7);
    // print_matrix(m);
    m.swap_rows(2, 0);
    // print_matrix(m);
    for (unsigned i = 1; i < m.dimension(); i++) {
        m(i, 0) = 0;
    }
    // print_matrix(m);

// say pivot at 3,4
    m.swap_columns(1, 4);
    // print_matrix(m);
    m.swap_rows(1, 3);
    // print_matrix(m);

    vector<double> row;
    double alpha = 2.33;
    unsigned pivot_row = 1;
    unsigned target_row = 2;
    unsigned pivot_row_0 = 3;
    double beta = 3.1;
    m(target_row, 3) = 0;
    m(target_row, 5) = 0;
    m(pivot_row, 6) = 0;
#ifdef Z3DEBUG
    print_matrix(m, std::cout);
#endif

    for (unsigned j = 0; j < m.dimension(); j++) {
        row.push_back(m(target_row, j) + alpha * m(pivot_row, j) + beta * m(pivot_row_0, j));
    }

    for (auto & t : row) {
        std::cout << t << ",";
    }
    std::cout << std::endl;
    lp_settings settings;
    m.pivot_row_to_row(pivot_row, alpha, target_row, settings);
    m.pivot_row_to_row(pivot_row_0, beta, target_row, settings);
    //  print_matrix(m);
    for (unsigned j = 0; j < m.dimension(); j++) {
        SASSERT(abs(row[j] - m(target_row, j)) < 0.00000001);
    }
}

#ifdef Z3DEBUG
void test_swap_rows() {
    sparse_matrix<double, double> m(10);
    fill_matrix(m);
    // print_matrix(m);
    test_swap_rows(m, 3, 5);

    test_swap_rows(m, 1, 3);


    test_swap_rows(m, 1, 3);

    test_swap_rows(m, 1, 7);

    test_swap_rows(m, 3, 7);

    test_swap_rows(m, 0, 7);

    m(0, 4) = 1;
    // print_matrix(m);
    test_swap_rows(m, 0, 7);

// go over some corner cases
    sparse_matrix<double, double> m0(2);
    test_swap_rows(m0, 0, 1);
    m0(0, 0) = 3;
    test_swap_rows(m0, 0, 1);
    m0(1, 0) = 3;
    test_swap_rows(m0, 0, 1);


    sparse_matrix<double, double> m1(10);
    test_swap_rows(m1, 0, 1);
    m1(0, 0) = 3;
    test_swap_rows(m1, 0, 1);
    m1(1, 0) = 3;
    m1(0, 3) = 5;
    m1(1, 3) = 4;
    m1(1, 8) = 8;
    m1(1, 9) = 8;

    test_swap_rows(m1, 0, 1);

    sparse_matrix<double, double> m2(3);
    test_swap_rows(m2, 0, 1);
    m2(0, 0) = 3;
    test_swap_rows(m2, 0, 1);
    m2(2, 0) = 3;
    test_swap_rows(m2, 0, 2);
}

void fill_uniformly(sparse_matrix<double, double> & m, unsigned dim) {
    int v = 0;
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            m(i, j) = v++;
        }
    }
}

void fill_uniformly(dense_matrix<double, double> & m, unsigned dim) {
    int v = 0;
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            m.set_elem(i, j, v++);
        }
    }
}

void sparse_matrix_with_permutaions_test() {
    unsigned dim = 4;
    sparse_matrix<double, double> m(dim);
    fill_uniformly(m, dim);
    dense_matrix<double, double> dm(dim, dim);
    fill_uniformly(dm, dim);
    dense_matrix<double, double> dm0(dim, dim);
    fill_uniformly(dm0, dim);
    permutation_matrix<double, double> q0(dim);
    q0[0] = 1;
    q0[1] = 0;
    q0[2] = 3;
    q0[3] = 2;
    permutation_matrix<double, double> q1(dim);
    q1[0] = 1;
    q1[1] = 2;
    q1[2] = 3;
    q1[3] = 0;
    permutation_matrix<double, double> p0(dim);
    p0[0] = 1;
    p0[1] = 0;
    p0[2] = 3;
    p0[3] = 2;
    permutation_matrix<double, double> p1(dim);
    p1[0] = 1;
    p1[1] = 2;
    p1[2] = 3;
    p1[3] = 0;

    m.multiply_from_left(q0);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            SASSERT(m(i, j) == dm0.get_elem(q0[i], j));
        }
    }

    auto q0_dm = q0 * dm;
    SASSERT(m == q0_dm);

    m.multiply_from_left(q1);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            SASSERT(m(i, j) == dm0.get_elem(q0[q1[i]], j));
        }
    }


    auto q1_q0_dm = q1 * q0_dm;

    SASSERT(m == q1_q0_dm);

    m.multiply_from_right(p0);

    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            SASSERT(m(i, j) == dm0.get_elem(q0[q1[i]], p0[j]));
        }
    }

    auto q1_q0_dm_p0 = q1_q0_dm * p0;

    SASSERT(m == q1_q0_dm_p0);

    m.multiply_from_right(p1);

    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            SASSERT(m(i, j) == dm0.get_elem(q0[q1[i]], p1[p0[j]]));
        }
    }

    auto q1_q0_dm_p0_p1 = q1_q0_dm_p0 * p1;
    SASSERT(m == q1_q0_dm_p0_p1);

    m.multiply_from_right(p1);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            SASSERT(m(i, j) == dm0.get_elem(q0[q1[i]], p1[p1[p0[j]]]));
        }
    }
    auto q1_q0_dm_p0_p1_p1 = q1_q0_dm_p0_p1 * p1;

    SASSERT(m == q1_q0_dm_p0_p1_p1);
}

void test_swap_columns() {
    sparse_matrix<double, double> m(10);
    fill_matrix(m);
    // print_matrix(m);

    test_swap_columns(m, 3, 5);

    test_swap_columns(m, 1, 3);

    test_swap_columns(m, 1, 3);

    // print_matrix(m);
    test_swap_columns(m, 1, 7);

    test_swap_columns(m, 3, 7);

    test_swap_columns(m, 0, 7);

    test_swap_columns(m, 0, 7);

// go over some corner cases
    sparse_matrix<double, double> m0(2);
    test_swap_columns(m0, 0, 1);
    m0(0, 0) = 3;
    test_swap_columns(m0, 0, 1);
    m0(0, 1) = 3;
    test_swap_columns(m0, 0, 1);


    sparse_matrix<double, double> m1(10);
    test_swap_columns(m1, 0, 1);
    m1(0, 0) = 3;
    test_swap_columns(m1, 0, 1);
    m1(0, 1) = 3;
    m1(3, 0) = 5;
    m1(3, 1) = 4;
    m1(8, 1) = 8;
    m1(9, 1) = 8;

    test_swap_columns(m1, 0, 1);

    sparse_matrix<double, double> m2(3);
    test_swap_columns(m2, 0, 1);
    m2(0, 0) = 3;
    test_swap_columns(m2, 0, 1);
    m2(0, 2) = 3;
    test_swap_columns(m2, 0, 2);
}



void test_swap_operations() {
    test_swap_rows();
    test_swap_columns();
}

void test_dense_matrix() {
    dense_matrix<double, double> d(3, 2);
    d.set_elem(0, 0, 1);
    d.set_elem(1, 1, 2);
    d.set_elem(2, 0, 3);
    // print_matrix(d);

    dense_matrix<double, double> unit(2, 2);
    d.set_elem(0, 0, 1);
    d.set_elem(1, 1, 1);

    dense_matrix<double, double> c = d * unit;

    // print_matrix(d);

    dense_matrix<double, double> perm(3, 3);
    perm.set_elem(0, 1, 1);
    perm.set_elem(1, 0, 1);
    perm.set_elem(2, 2, 1);
    auto c1 = perm * d;
    // print_matrix(c1);


    dense_matrix<double, double> p2(2, 2);
    p2.set_elem(0, 1, 1);
    p2.set_elem(1, 0, 1);
    auto c2 = d * p2;
}
#endif



vector<permutation_matrix<double, double>> vector_of_permutaions() {
    vector<permutation_matrix<double, double>> ret;
    {
        permutation_matrix<double, double> p0(5);
        p0[0] = 1; p0[1] = 2; p0[2] = 3; p0[3] = 4;
        p0[4] = 0;
        ret.push_back(p0);
    }
    {
        permutation_matrix<double, double> p0(5);
        p0[0] = 2; p0[1] = 0; p0[2] = 1; p0[3] = 4;
        p0[4] = 3;
        ret.push_back(p0);
    }
    return ret;
}

void test_apply_reverse_from_right_to_perm(permutation_matrix<double, double> & l) {
    permutation_matrix<double, double> p(5);
    p[0] = 4; p[1] = 2; p[2] = 0; p[3] = 3;
    p[4] = 1;

    permutation_matrix<double, double> pclone(5);
    pclone[0] = 4; pclone[1] = 2; pclone[2] = 0; pclone[3] = 3;
    pclone[4] = 1;

    p.multiply_by_reverse_from_right(l);
#ifdef Z3DEBUG
    auto rev = l.get_inverse();
    auto rs = pclone * rev;
    SASSERT(p == rs);
#endif
}

void test_apply_reverse_from_right() {
    auto vec = vector_of_permutaions();
    for (unsigned i = 0; i < vec.size(); i++) {
        test_apply_reverse_from_right_to_perm(vec[i]);
    }
}

void test_permutations() {
    std::cout << "test permutations" << std::endl;
    test_apply_reverse_from_right();
    vector<double> v; v.resize(5, 0);
    v[1] = 1;
    v[3] = 3;
    permutation_matrix<double, double> p(5);
    p[0] = 4; p[1] = 2; p[2] = 0; p[3] = 3;
    p[4] = 1;

    indexed_vector<double> vi(5);
    vi.set_value(1, 1);
    vi.set_value(3, 3);

    p.apply_reverse_from_right_to_T(v);
    p.apply_reverse_from_right_to_T(vi);
    SASSERT(vectors_are_equal(v, vi.m_data));
    SASSERT(vi.is_OK());
}

void lp_solver_test() {
    // lp_revised_solver<double> lp_revised;
    // lp_revised.get_minimal_solution();
}

bool get_int_from_args_parser(const char * option, argument_parser & args_parser, unsigned & n) {
    std::string s = args_parser.get_option_value(option);
    if (s.size() > 0) {
        n = atoi(s.c_str());
        return true;
    }
    return false;
}

bool get_double_from_args_parser(const char * option, argument_parser & args_parser, double & n) {
    std::string s = args_parser.get_option_value(option);
    if (s.size() > 0) {
        n = atof(s.c_str());
        return true;
    }
    return false;
}


void update_settings(argument_parser & args_parser, lp_settings& settings) {
    unsigned n;
    settings.m_simplex_strategy = simplex_strategy_enum::lu;
    if (get_int_from_args_parser("--rep_frq", args_parser, n))
        settings.report_frequency = n;
    else
        settings.report_frequency = args_parser.option_is_used("--mpq")? 80: 1000;

    settings.print_statistics = true;

    if (get_int_from_args_parser("--percent_for_enter", args_parser, n))
        settings.percent_of_entering_to_check = n;
    if (get_int_from_args_parser("--partial_pivot", args_parser, n)) {
        std::cout << "setting partial pivot constant to " << n << std::endl;
        settings.c_partial_pivoting = n;
    }
    if (get_int_from_args_parser("--density", args_parser, n)) {
        double density = static_cast<double>(n) / 100.0;
        std::cout << "setting density to " << density << std::endl;
        settings.density_threshold = density;
    }
    if (get_int_from_args_parser("--maxng", args_parser, n))
        settings.max_number_of_iterations_with_no_improvements = n;
    double d;
    if (get_double_from_args_parser("--harris_toler", args_parser, d)) {
        std::cout << "setting harris_feasibility_tolerance to " << d << std::endl;
        settings.harris_feasibility_tolerance = d;
    }
    if (get_int_from_args_parser("--random_seed", args_parser, n)) {
        settings.random_seed(n);
    }
    if (get_int_from_args_parser("--simplex_strategy", args_parser, n)) {
        settings.simplex_strategy() = static_cast<simplex_strategy_enum>(n);
    }
}

template <typename T, typename X>
void setup_solver(unsigned max_iterations, unsigned time_limit, bool look_for_min, argument_parser & args_parser, lp_solver<T, X> * solver) {
    if (max_iterations > 0)
        solver->set_max_iterations_per_stage(max_iterations);

    if (time_limit > 0)
        solver->set_time_limit(time_limit);

    if (look_for_min)
        solver->flip_costs();

    update_settings(args_parser, solver->settings());
}

bool values_are_one_percent_close(double a, double b);

void print_x(mps_reader<double, double> & reader, lp_solver<double, double> * solver) {
    for (auto name : reader.column_names()) {
        std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
    }
    std::cout << std::endl;
}

void compare_solutions(mps_reader<double, double> & reader, lp_solver<double, double> * solver, lp_solver<double, double> * solver0) {
    for (auto name : reader.column_names()) {
        double a = solver->get_column_value_by_name(name);
        double b = solver0->get_column_value_by_name(name);
        if (!values_are_one_percent_close(a, b)) {
            std::cout << "different values for " << name << ":" << a << " and "  << b << std::endl;
        }
    }
}


void solve_mps_double(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool dual, bool compare_with_primal, argument_parser & args_parser) {
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (!reader.is_ok()) {
        std::cout << "cannot process " << file_name << std::endl;
        return;
    }
    
    lp_solver<double, double> * solver =  reader.create_solver(dual);
    setup_solver(max_iterations, time_limit, look_for_min, args_parser, solver);
    stopwatch sw;
    sw.start();
    if (dual) {
        std::cout << "solving for dual" << std::endl;
    }
    solver->find_maximal_solution();
    sw.stop();
    double span = sw.get_seconds(); 
    std::cout << "Status: " << lp_status_to_string(solver->get_status()) << std::endl;
    if (solver->get_status() == lp_status::OPTIMAL) {
        if (reader.column_names().size() < 20) {
            print_x(reader, solver);
        }
        double cost = solver->get_current_cost();
        if (look_for_min) {
            cost = -cost;
        }
        std::cout << "cost = " << cost << std::endl;
    }
    std::cout << "processed in " << span / 1000.0  << " seconds, running for " << solver->m_total_iterations << " iterations" << "  one iter for " << (double)span/solver->m_total_iterations << " ms" << std::endl;
    if (compare_with_primal) {
        auto * primal_solver = reader.create_solver(false);
        setup_solver(max_iterations, time_limit, look_for_min, args_parser, primal_solver);
        primal_solver->find_maximal_solution();
        if (solver->get_status() != primal_solver->get_status()) {
            std::cout << "statuses are different: dual " << lp_status_to_string(solver->get_status()) << " primal = " << lp_status_to_string(primal_solver->get_status()) << std::endl;
        } else {
            if (solver->get_status() == lp_status::OPTIMAL) {
                double cost = solver->get_current_cost();
                if (look_for_min) {
                    cost = -cost;
                }
                double primal_cost = primal_solver->get_current_cost();
                if (look_for_min) {
                    primal_cost = -primal_cost;
                }
                std::cout << "primal cost = " << primal_cost << std::endl;
                if (!values_are_one_percent_close(cost, primal_cost)) {
                    compare_solutions(reader, primal_solver, solver);
                    print_x(reader, primal_solver);
                    std::cout << "dual cost is " << cost << ", but primal cost is " << primal_cost << std::endl;
                    SASSERT(false);
                }
            }
        }
        delete primal_solver;
    }
    delete solver;
}

void solve_mps_rational(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool dual, argument_parser & args_parser) {
    mps_reader<lp::mpq, lp::mpq> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        setup_solver(max_iterations, time_limit, look_for_min, args_parser, solver);
        stopwatch sw;
        sw.start();
        solver->find_maximal_solution();
        std::cout << "Status: " << lp_status_to_string(solver->get_status()) << std::endl;

        if (solver->get_status() == lp_status::OPTIMAL) {
            // for (auto name: reader.column_names()) {
            //  std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
            // }
            lp::mpq cost = solver->get_current_cost();
            if (look_for_min) {
                cost = -cost;
            }
            std::cout << "cost = " << cost.get_double() << std::endl;
        }
        std::cout << "processed in " << sw.get_current_seconds() / 1000.0 << " seconds, running for " << solver->m_total_iterations << " iterations" << std::endl;
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}
void get_time_limit_and_max_iters_from_parser(argument_parser & args_parser, unsigned & time_limit, unsigned & max_iters); // forward definition

void solve_mps(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool solve_for_rational, bool dual, bool compare_with_primal, argument_parser & args_parser) {
    if (!solve_for_rational) {
        std::cout << "solving " << file_name << std::endl;
        solve_mps_double(file_name, look_for_min, max_iterations, time_limit, dual, compare_with_primal, args_parser);
    }
    else {
        std::cout << "solving " << file_name << " in rationals " << std::endl;
        solve_mps_rational(file_name, look_for_min, max_iterations, time_limit, dual, args_parser);
    }
}

void solve_mps(std::string file_name, argument_parser & args_parser) {
    bool look_for_min = args_parser.option_is_used("--min");
    unsigned max_iterations, time_limit;
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    bool dual = args_parser.option_is_used("--dual");
    bool compare_with_primal = args_parser.option_is_used("--compare_with_primal");
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iterations);
    solve_mps(file_name, look_for_min, max_iterations, time_limit, solve_for_rational, dual, compare_with_primal, args_parser);
}

void solve_mps_in_rational(std::string file_name, bool dual, argument_parser & /*args_parser*/) {
    std::cout << "solving " << file_name << std::endl;

    mps_reader<lp::mpq, lp::mpq> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        solver->find_maximal_solution();
        std::cout << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
        if (solver->get_status() == lp_status::OPTIMAL) {
            if (reader.column_names().size() < 20) {
                for (auto name : reader.column_names()) {
                    std::cout << name << "=" << solver->get_column_value_by_name(name).get_double() << ' ';
                }
            }
            std::cout << std::endl << "cost = " << numeric_traits<lp::mpq>::get_double(solver->get_current_cost()) << std::endl;
        }
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}

void test_upair_queue() {
    int n = 10;
    binary_heap_upair_queue<int> q(2);
    std::unordered_map<upair, int> m;
    for (int k = 0; k < 100; k++) {
        int i = my_random()%n;
        int j = my_random()%n;
        q.enqueue(i, j, my_random()%n);
    }

    q.remove(5, 5);

    while (!q.is_empty()) {
        unsigned i, j;
        q.dequeue(i, j);
    }
}

void test_binary_priority_queue() {
    std::cout << "testing binary_heap_priority_queue...";
    auto q = binary_heap_priority_queue<int>(10);
    q.enqueue(2, 2);
    q.enqueue(1, 1);
    q.enqueue(9, 9);
    q.enqueue(8, 8);
    q.enqueue(5, 25);
    q.enqueue(3, 3);
    q.enqueue(4, 4);
    q.enqueue(7, 30);
    q.enqueue(6, 6);
    q.enqueue(0, 0);
    q.enqueue(5, 5);
    q.enqueue(7, 7);

    for (unsigned i = 0; i < 10; i++) {
        unsigned de = q.dequeue();
        SASSERT(i == de);
        std::cout << de << std::endl;
    }
    q.enqueue(2, 2);
    q.enqueue(1, 1);
    q.enqueue(9, 9);
    q.enqueue(8, 8);
    q.enqueue(5, 5);
    q.enqueue(3, 3);
    q.enqueue(4, 4);
    q.enqueue(7, 2);
    q.enqueue(0, 1);
    q.enqueue(6, 6);
    q.enqueue(7, 7);
    q.enqueue(33, 1000);
    q.enqueue(20, 0);
    q.dequeue();
    q.remove(33);
    q.enqueue(0, 0);
#ifdef Z3DEBUG
    unsigned t = 0;
    while (q.size() > 0) {
        unsigned d =q.dequeue();
        SASSERT(t++ == d);
        std::cout << d << std::endl;
    }
#endif
    test_upair_queue();
    std::cout << " done" << std::endl;
}

bool solution_is_feasible(std::string file_name, const std::unordered_map<std::string, double> & solution) {
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        lp_primal_simplex<double, double> * solver = static_cast<lp_primal_simplex<double, double> *>(reader.create_solver(false));
        return solver->solution_is_feasible(solution);
    }
    return false;
}


void solve_mps_with_known_solution(std::string file_name, std::unordered_map<std::string, double> * solution, lp_status status, bool dual) {
    std::cout << "solving " << file_name << std::endl;
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        solver->find_maximal_solution();
        std::cout << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
        if (status != solver->get_status()){
            std::cout << "status should be " << lp_status_to_string(status) << std::endl;
            SASSERT(status == solver->get_status());
            throw "status is wrong";
        }
        if (solver->get_status() == lp_status::OPTIMAL) {
            std::cout << "cost = " << solver->get_current_cost() << std::endl;
            if (solution != nullptr) {
                for (auto it : *solution) {
                    if (fabs(it.second - solver->get_column_value_by_name(it.first)) >= 0.000001) {
                        std::cout << "expected:" << it.first << "=" <<
                            it.second <<", got " << solver->get_column_value_by_name(it.first) << std::endl;
                    }
                    SASSERT(fabs(it.second - solver->get_column_value_by_name(it.first)) < 0.000001);
                }
            }
            if (reader.column_names().size() < 20) {
                for (auto name : reader.column_names()) {
                    std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
                }
                std::cout << std::endl;
            }
        }
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}

int get_random_rows() {
    return 5 + my_random() % 2;
}

int get_random_columns() {
    return 5 + my_random() % 3;
}

int get_random_int() {
    return -1 + my_random() % 2; // (1.0 + RAND_MAX);
}

void add_random_row(lp_primal_simplex<double, double> * solver, int cols, int row) {
    solver->add_constraint(lp_relation::Greater_or_equal, 1, row);
    for (int i = 0; i < cols; i++) {
        solver->set_row_column_coefficient(row, i, get_random_int());
    }
}

void add_random_cost(lp_primal_simplex<double, double> * solver, int cols) {
    for (int i = 0; i < cols; i++) {
        solver->set_cost_for_column(i, get_random_int());
    }
}

lp_primal_simplex<double, double> * generate_random_solver() {
    int rows = get_random_rows();
    int cols = get_random_columns();
    auto * solver = new lp_primal_simplex<double, double>();
    for (int i = 0; i < rows; i++) {
        add_random_row(solver, cols, i);
    }
    add_random_cost(solver, cols);
    return solver;
}



void random_test_on_i(unsigned i) {
    if (i % 1000 == 0) {
        std::cout << ".";
    }
    srand(i);
    auto *solver = generate_random_solver();
    solver->find_maximal_solution();
    //    std::cout << lp_status_to_string(solver->get_status()) << std::endl;
    delete solver;
}

void random_test() {
    for (unsigned i = 0; i < std::numeric_limits<unsigned>::max(); i++) {
        try {
            random_test_on_i(i);
        }
        catch (const char * error) {
            std::cout << "i = " << i << ", throwing at ' " << error << "'" << std::endl;
            break;
        }
    }
}

#if _LINUX_
void fill_file_names(vector<std::string> &file_names,  std::set<std::string> & minimums) {
    char *home_dir = getenv("HOME");
    if (home_dir == nullptr) {
        std::cout << "cannot find home directory, don't know how to find the files";
        return;
    }
    std::string home_dir_str(home_dir);
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l0redund.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l1.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l2.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l3.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l4.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l4fix.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/plan.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/samp2.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/murtagh.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l0.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AFIRO.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC50B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC50A.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/KB2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC105.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ADLITTLE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BLEND.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCAGR7.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC205.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHARE2B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/RECIPELP.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/LOTFI.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/VTP-BASE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHARE1B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BOEING2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BORE3D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCORPION.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CAPRI.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BRANDY.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCAGR25.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ISRAEL.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BANDM.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/E226.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW7.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ETAMACRO.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FINNIS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDATA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDGUB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BEACONFD.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STAIR.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDMPS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GFRD-PNC.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCRS8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BOEING1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MODSZK1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DEGEN2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FORPLAN.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHELL.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT4.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD6.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP04S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SEBA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW15.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FFFFF800.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BNL1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PEROLD.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP04L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GANGES.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW22.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT-WE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MAROS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/25FV47.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP12S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT1P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SIERRA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOTNOV.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CZPROB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT1D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT-JA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BNL2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/NESM.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CYCLE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/acc-tight5.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP12L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DEGEN3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/80BAU3B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/TRUSS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/D2Q06C.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/WOODW.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP12.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/D6CUBE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DFL001.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/WOOD1P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT2P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT87.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP15.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT2D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MAROS-R7.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/FIT2P.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/DFL001.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/D2Q06C.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/80BAU3B.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEB.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEA.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/BNL2.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08L.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/FIT1D.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP3.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCSD8.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCSD6.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/MAROS-R7.SIF");
}

void test_out_dir(std::string out_dir) {
    auto *out_dir_p = opendir(out_dir.c_str());
    if (out_dir_p == nullptr) {
        std::cout << "creating directory " << out_dir << std::endl;
#ifdef LEAN_WINDOWS
        int res = mkdir(out_dir.c_str());
#else
        int res = mkdir(out_dir.c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
#endif
        if (res) {
            std::cout << "Cannot open output directory \"" << out_dir << "\"" << std::endl;
        }
        return;
    }
    closedir(out_dir_p);
}

void find_dir_and_file_name(std::string a, std::string & dir, std::string& fn) {
    // todo: make it system independent
    size_t last_slash_pos = a.find_last_of("/");
    if (last_slash_pos >= a.size()) {
        std::cout << "cannot find file name in " << a << std::endl;
        throw;
    }
    dir = a.substr(0, last_slash_pos);
    // std::cout << "dir = " << dir << std::endl;
    fn = a.substr(last_slash_pos + 1);
    //    std::cout << "fn = " << fn << std::endl;
}

void process_test_file(std::string test_dir, std::string test_file_name, argument_parser & args_parser, std::string out_dir, unsigned max_iters, unsigned time_limit, unsigned & successes, unsigned & failures, unsigned & inconclusives);

void solve_some_mps(argument_parser & args_parser) {
    unsigned max_iters, time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    unsigned successes = 0;
    unsigned failures = 0;
    unsigned inconclusives = 0;
    std::set<std::string> minimums;
    vector<std::string> file_names;
    fill_file_names(file_names, minimums);
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    bool dual = args_parser.option_is_used("--dual");
    bool compare_with_primal = args_parser.option_is_used("--compare_with_primal");
    bool compare_with_glpk = args_parser.option_is_used("--compare_with_glpk");
    if (compare_with_glpk) {
        std::string out_dir = args_parser.get_option_value("--out_dir");
        if (out_dir.size() == 0) {
            out_dir = "/tmp/test";
        }
        test_out_dir(out_dir);
        for (auto& a : file_names) {
            try {
                std::string file_dir;
                std::string file_name;
                find_dir_and_file_name(a, file_dir, file_name);
                process_test_file(file_dir, file_name, args_parser, out_dir, max_iters, time_limit, successes, failures, inconclusives);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
        std::cout << "comparing with glpk: successes " << successes << ", failures " << failures << ", inconclusives " << inconclusives << std::endl;
        return;
    }
    if (!solve_for_rational) {
        solve_mps(file_names[6], false, 0, time_limit, false, dual, compare_with_primal, args_parser);
        solve_mps_with_known_solution(file_names[3], nullptr, INFEASIBLE, dual); // chvatal: 135(d)
        std::unordered_map<std::string, double> sol;
        sol["X1"] = 0;
        sol["X2"] = 6;
        sol["X3"] = 0;
        sol["X4"] = 15;
        sol["X5"] = 2;
        sol["X6"] = 1;
        sol["X7"] = 1;
        sol["X8"] = 0;
        solve_mps_with_known_solution(file_names[9], &sol, OPTIMAL, dual);
        solve_mps_with_known_solution(file_names[0], &sol, OPTIMAL, dual);
        sol.clear();
        sol["X1"] = 25.0/14.0;
        // sol["X2"] = 0;
        // sol["X3"] = 0;
        // sol["X4"] = 0;
        // sol["X5"] = 0;
        // sol["X6"] = 0;
        // sol["X7"] = 9.0/14.0;
        solve_mps_with_known_solution(file_names[5], &sol, OPTIMAL, dual); // chvatal: 135(e)
        solve_mps_with_known_solution(file_names[4], &sol, OPTIMAL, dual); // chvatal: 135(e)
        solve_mps_with_known_solution(file_names[2], nullptr, UNBOUNDED, dual); // chvatal: 135(c)
        solve_mps_with_known_solution(file_names[1], nullptr, UNBOUNDED, dual); // chvatal: 135(b)
        solve_mps(file_names[8], false, 0, time_limit, false, dual, compare_with_primal, args_parser);
        // return;
        for (auto& s : file_names) {
            try {
                solve_mps(s, minimums.find(s) != minimums.end(), max_iters, time_limit, false, dual, compare_with_primal, args_parser);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
    } else {
        //        unsigned i = 0;
        for (auto& s : file_names) {
            // if (i++ > 9) return;
            try {
                solve_mps_in_rational(s, dual, args_parser);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
    }
}
#endif

void solve_rational() {
    lp_primal_simplex<lp::mpq, lp::mpq> solver;
    solver.add_constraint(lp_relation::Equal, lp::mpq(7), 0);
    solver.add_constraint(lp_relation::Equal, lp::mpq(-3), 1);

    // setting the cost
    int cost[] = {-3, -1, -1, 2, -1, 1, 1, -4};
    std::string var_names[8] = {"x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"};

    for (unsigned i = 0; i < 8; i++) {
        solver.set_cost_for_column(i, lp::mpq(cost[i]));
        solver.give_symbolic_name_to_column(var_names[i], i);
    }

    int row0[] = {1, 0, 3, 1, -5, -2 , 4, -6};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_row_column_coefficient(0, i, lp::mpq(row0[i]));
    }

    int row1[] = {0, 1, -2, -1, 4, 1, -3, 5};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_row_column_coefficient(1, i, lp::mpq(row1[i]));
    }

    int bounds[] = {8, 6, 4, 15, 2, 10, 10, 3};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_low_bound(i, lp::mpq(0));
        solver.set_upper_bound(i, lp::mpq(bounds[i]));
    }

    std::unordered_map<std::string, lp::mpq>  expected_sol;
    expected_sol["x1"] = lp::mpq(0);
    expected_sol["x2"] = lp::mpq(6);
    expected_sol["x3"] = lp::mpq(0);
    expected_sol["x4"] = lp::mpq(15);
    expected_sol["x5"] = lp::mpq(2);
    expected_sol["x6"] = lp::mpq(1);
    expected_sol["x7"] = lp::mpq(1);
    expected_sol["x8"] = lp::mpq(0);
    solver.find_maximal_solution();
    SASSERT(solver.get_status() == OPTIMAL);
    for (auto it : expected_sol) {
        SASSERT(it.second == solver.get_column_value_by_name(it.first));
    }
}


std::string read_line(bool & end, std::ifstream & file) {
    std::string s;
    if (!getline(file, s)) {
        end = true;
        return std::string();
    }
    end = false;
    return s;
}

bool contains(std::string const & s, char const * pattern) {
    return s.find(pattern) != std::string::npos;
}


std::unordered_map<std::string, double> * get_solution_from_glpsol_output(std::string & file_name) {
    std::ifstream file(file_name);
    if (!file.is_open()){
        std::cerr << "cannot  open " << file_name << std::endl;
        return nullptr;
    }
    std::string s;
    bool end;
    do {
        s = read_line(end, file);
        if (end) {
            std::cerr << "unexpected file end " << file_name << std::endl;
            return nullptr;
        }
        if (contains(s, "Column name")){
            break;
        }
    } while (true);

    read_line(end, file);
    if (end) {
        std::cerr << "unexpected file end " << file_name << std::endl;
        return nullptr;
    }

    auto ret = new std::unordered_map<std::string, double>();

    do {
        s = read_line(end, file);
        if (end) {
            std::cerr << "unexpected file end " << file_name << std::endl;
            return nullptr;
        }
        auto split = string_split(s, " \t", false);
        if (split.size() == 0) {
           return ret;
        }

        SASSERT(split.size() > 3);
        (*ret)[split[1]] = atof(split[3].c_str());
    } while (true);
}



void test_init_U() {
    static_matrix<double, double> m(3, 7);
    m(0, 0) = 10; m(0, 1) = 11; m(0, 2) = 12; m(0, 3) = 13; m(0, 4) = 14;
    m(1, 0) = 20; m(1, 1) = 21; m(1, 2) = 22; m(1, 3) = 23; m(1, 5) = 24;
    m(2, 0) = 30; m(2, 1) = 31; m(2, 2) = 32; m(2, 3) = 33; m(2, 6) = 34;
#ifdef Z3DEBUG
    print_matrix(m, std::cout);
#endif
    vector<unsigned> basis(3);
    basis[0] = 1;
    basis[1] = 2;
    basis[2] = 4;

    sparse_matrix<double, double> u(m, basis);

    for (unsigned i = 0; i < 3; i++) {
        for (unsigned j = 0; j < 3; j ++) {
            SASSERT(m(i, basis[j]) == u(i, j));
        }
    }

    // print_matrix(m);
    // print_matrix(u);
}

void test_replace_column() {
    sparse_matrix<double, double> m(10);
    fill_matrix(m);
    m.swap_columns(0, 7);
    m.swap_columns(6, 3);
    m.swap_rows(2, 0);
    for (unsigned i = 1; i < m.dimension(); i++) {
        m(i, 0) = 0;
    }

    indexed_vector<double> w(m.dimension());
    for (unsigned i = 0; i < m.dimension(); i++) {
        w.set_value(i % 3, i);
    }

    lp_settings settings;

    for (unsigned column_to_replace = 0;  column_to_replace < m.dimension(); column_to_replace ++) {
        m.replace_column(column_to_replace, w, settings);
        for (unsigned i = 0; i < m.dimension(); i++) {
            SASSERT(abs(w[i] - m(i, column_to_replace)) < 0.00000001);
        }
    }
}


void setup_args_parser(argument_parser & parser) {
    parser.add_option_with_help_string("-xyz_sample", "run a small interactive scenario");
    parser.add_option_with_after_string_with_help("--density", "the percentage of non-zeroes in the matrix below which it is not dense");
    parser.add_option_with_after_string_with_help("--harris_toler", "harris tolerance");
    parser.add_option_with_help_string("--test_swaps", "test row swaps with a permutation");
    parser.add_option_with_help_string("--test_perm", "test permutaions");
    parser.add_option_with_after_string_with_help("--checklu", "the file name for lu checking");
    parser.add_option_with_after_string_with_help("--partial_pivot", "the partial pivot constant, a number somewhere between 10 and 100");
    parser.add_option_with_after_string_with_help("--percent_for_enter", "which percent of columns check for entering column");
    parser.add_option_with_help_string("--totalinf", "minimizes the total infeasibility  instead of diminishin infeasibility of the rows");
    parser.add_option_with_after_string_with_help("--rep_frq", "the report frequency, in how many iterations print the cost and other info ");
    parser.add_option_with_help_string("--smt", "smt file format");
    parser.add_option_with_after_string_with_help("--filelist", "the file containing the list of files");
    parser.add_option_with_after_string_with_help("--file", "the input file name"); 
    parser.add_option_with_after_string_with_help("--random_seed", "random seed");
    parser.add_option_with_help_string("--bp", "bound propogation");
    parser.add_option_with_help_string("--min", "will look for the minimum for the given file if --file is used; the default is looking for the max");
    parser.add_option_with_help_string("--max", "will look for the maximum for the given file if --file is used; it is the default behavior");
    parser.add_option_with_after_string_with_help("--max_iters", "maximum total iterations in a core solver stage");
    parser.add_option_with_after_string_with_help("--time_limit", "time limit in seconds");
    parser.add_option_with_help_string("--mpq", "solve for rational numbers");
    parser.add_option_with_after_string_with_help("--simplex_strategy", "sets simplex strategy for rational number");
    parser.add_option_with_help_string("--test_lu", "test the work of the factorization");
    parser.add_option_with_help_string("--test_small_lu", "test the work of the factorization on a smallish matrix");
    parser.add_option_with_help_string("--test_larger_lu", "test the work of the factorization");
    parser.add_option_with_help_string("--test_larger_lu_with_holes", "test the work of the factorization");
    parser.add_option_with_help_string("--test_lp_0", "solve a small lp");
    parser.add_option_with_help_string("--solve_some_mps", "solves a list of mps problems");
    parser.add_option_with_after_string_with_help("--test_file_directory", "loads files from the directory for testing");
    parser.add_option_with_help_string("--compare_with_glpk", "compares the results by running glpsol");
    parser.add_option_with_after_string_with_help("--out_dir", "setting the output directory for tests, if not set /tmp is used");
    parser.add_option_with_help_string("--dual", "using the dual simplex solver");
    parser.add_option_with_help_string("--compare_with_primal", "using the primal simplex solver for comparison");
    parser.add_option_with_help_string("--lar", "test lar_solver");
    parser.add_option_with_after_string_with_help("--maxng", "max iterations without progress");
    parser.add_option_with_help_string("-tbq", "test binary queue");
    parser.add_option_with_help_string("--randomize_lar", "test randomize funclionality");
    parser.add_option_with_help_string("--smap", "test stacked_map");
    parser.add_option_with_help_string("--term", "simple term test");
    parser.add_option_with_help_string("--eti"," run a small evidence test for total infeasibility scenario");
    parser.add_option_with_help_string("--row_inf", "forces row infeasibility search");
    parser.add_option_with_help_string("-pd", "presolve with double solver");
    parser.add_option_with_help_string("--test_int_set", "test int_set");
    parser.add_option_with_help_string("--test_mpq", "test rationals");
    parser.add_option_with_help_string("--test_mpq_np", "test rationals");
    parser.add_option_with_help_string("--test_mpq_np_plus", "test rationals using plus instead of +=");
}

struct fff { int a; int b;};

void test_stacked_map_itself() {
    vector<int> v(3,0);
    for(auto u : v)
        std::cout << u << std::endl;    
    
    std::unordered_map<int, fff> foo;
    fff l;
    l.a = 0;
    l.b =1;
    foo[1] = l;
    int r = 1;
    int k = foo[r].a;
    std::cout << k << std::endl;
    
    stacked_map<int, double> m;
    m[0] = 3;
    m[1] = 4;
    m.push();
    m[1] = 5;
    m[2] = 2;
    m.pop();
    m.erase(2);
    m[2] = 3;
    m.erase(1);
    m.push();
    m[3] = 100;
    m[4] = 200;
    m.erase(1);
    m.push();
    m[5] = 300;
    m[6] = 400;
    m[5] = 301;
    m.erase(5);
    m[3] = 122;

    m.pop(2);
    m.pop();
}

void test_stacked_unsigned() {
    std::cout << "test stacked unsigned" << std::endl;
    stacked_value<unsigned> v(0);
    v = 1;
    v = 2;
    v.push();
    v = 3;
    v = 4;
    v.pop();
    SASSERT(v == 2);
    v ++;
    v++;
    std::cout << "before push v=" << v << std::endl;
    v.push();
    v++;
    v.push();
    v+=1;
    std::cout << "v = " << v << std::endl;
    v.pop(2);
    SASSERT(v == 4);
    const unsigned & rr = v;
    std::cout << rr << std:: endl;
    
}

void test_stacked_value() {
    test_stacked_unsigned();
}

void test_stacked_vector() {
    std::cout << "test_stacked_vector" << std::endl;
    stacked_vector<int> v;
    v.push();
    v.push_back(0);
    v.push_back(1);
    v.push();
    v[0] = 3;
    v[0] = 0;
    v.push_back(2);
    v.push_back(3);
    v.push_back(34);
    v.push();
    v[1]=3;
    v[2] = 3;
    v.push();
    v[0]= 7;
    v[1] = 9;
    v.pop(2);
    if (v.size())
        v[v.size() -1 ] = 7;
    v.push();
    v.push_back(33);
    v[0] = 13;
    v.pop();
        
}

void test_stacked_set() {
#ifdef Z3DEBUG
    std::cout << "test_stacked_set" << std::endl;
    stacked_unordered_set<int> s;
    s.insert(1);
    s.insert(2);
    s.insert(3);
    std::unordered_set<int> scopy = s();
    s.push();
    s.insert(4);
    s.pop();
    SASSERT(s() == scopy);
    s.push();
    s.push();
    s.insert(4);
    s.insert(5);
    s.push();
    s.insert(4);
    s.pop(3);
    SASSERT(s() == scopy);
#endif
}

void test_stacked() {
    std::cout << "test_stacked_map()" << std::endl;
    test_stacked_map_itself();
    test_stacked_value();
    test_stacked_vector();
    test_stacked_set();
    
}

char * find_home_dir() {
    #ifdef _WINDOWS
    #else
    char * home_dir =   getenv("HOME");
  if (home_dir == nullptr) {
        std::cout << "cannot find home directory" << std::endl;
        return nullptr;
    }
    #endif
  return nullptr;
}


template <typename T>
void print_chunk(T * arr, unsigned len) {
    for (unsigned i = 0; i < len; i++) {
        std::cout << arr[i] << ", ";
    }
    std::cout << std::endl;
}

struct mem_cpy_place_holder {
    static void mem_copy_hook(int * destination, unsigned num) {
        if (destination == nullptr || num == 0) {
            throw "bad parameters";
        }
    }
};

void finalize(unsigned ret) {
    /*
    finalize_util_module();
    finalize_numerics_module();
    */
    //    return ret;
}

void get_time_limit_and_max_iters_from_parser(argument_parser & args_parser, unsigned & time_limit, unsigned & max_iters) {
    std::string s = args_parser.get_option_value("--max_iters");
    if (s.size() > 0) {
        max_iters = atoi(s.c_str());
    } else {
        max_iters = 0;
    }

    std::string time_limit_string = args_parser.get_option_value("--time_limit");
    if (time_limit_string.size() > 0) {
        time_limit = atoi(time_limit_string.c_str());
    } else {
        time_limit = 0;
    }
}


std::string create_output_file_name(bool minimize, std::string file_name, bool use_mpq) {
    std::string ret = file_name + "_lp_tst_" +  (minimize?"min":"max");
    if (use_mpq) return ret + "_mpq.out";
    return ret + ".out";
}

std::string create_output_file_name_for_glpsol(bool minimize, std::string file_name){
    return file_name + (minimize?"_min":"_max") + "_glpk_out";
}

int run_glpk(std::string file_name, std::string glpk_out_file_name, bool minimize, unsigned time_limit) {
    std::string minmax(minimize?"--min":"--max");
    std::string tmlim = time_limit > 0 ? std::string(" --tmlim ")  + std::to_string(time_limit)+ " ":std::string();
    std::string command_line =  std::string("glpsol --nointopt --nomip ") +  minmax + tmlim +  + " -o " + glpk_out_file_name +" " + file_name + " > /dev/null";
    return system(command_line.c_str());
}

std::string get_status(std::string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        std::cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    std::string str;
    while (getline(f, str)) {
        if (str.find("Status") != std::string::npos) {
            vector<std::string> tokens = split_and_trim(str);
            if (tokens.size() != 2) {
                std::cout << "unexpected Status string " << str << std::endl;
                throw 0;
            }
            return tokens[1];
        }
    }
    std::cout << "cannot find the status line in " << file_name << std::endl;
    throw 0;
}

// returns true if the costs should be compared too
bool compare_statuses(std::string glpk_out_file_name, std::string lp_out_file_name, unsigned & successes, unsigned & failures) {
    std::string glpk_status = get_status(glpk_out_file_name);
    std::string lp_tst_status = get_status(lp_out_file_name);

    if (glpk_status != lp_tst_status) {
        if (glpk_status == "UNDEFINED"  && (lp_tst_status == "UNBOUNDED" || lp_tst_status == "INFEASIBLE")) {
            successes++;
            return false;
        } else {
            std::cout << "glpsol and lp_tst disagree: glpsol status is " << glpk_status;
            std::cout << " but lp_tst status is " << lp_tst_status << std::endl;
            failures++;
            return false;
        }
    }
    return lp_tst_status == "OPTIMAL";
}

double get_glpk_cost(std::string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        std::cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    std::string str;
    while (getline(f, str)) {
        if (str.find("Objective") != std::string::npos) {
            vector<std::string> tokens = split_and_trim(str);
            if (tokens.size() != 5) {
                std::cout << "unexpected Objective std::string " << str << std::endl;
                throw 0;
            }
            return atof(tokens[3].c_str());
        }
    }
    std::cout << "cannot find the Objective line in " << file_name << std::endl;
    throw 0;
}

double get_lp_tst_cost(std::string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        std::cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    std::string str;
    std::string cost_string;
    while (getline(f, str)) {
        if (str.find("cost") != std::string::npos) {
            cost_string = str;
        }
    }
    if (cost_string.size() == 0) {
        std::cout << "cannot find the cost line in " << file_name << std::endl;
        throw 0;
    }

    vector<std::string> tokens = split_and_trim(cost_string);
    if (tokens.size() != 3) {
        std::cout << "unexpected cost string " << cost_string << std::endl;
        throw 0;
    }
    return atof(tokens[2].c_str());
}

bool values_are_one_percent_close(double a, double b) {
    double maxval = std::max(fabs(a), fabs(b));
    if (maxval < 0.000001) {
        return true;
    }

    double one_percent = maxval / 100;
    return fabs(a - b) <= one_percent;
}

// returns true if both are optimal
void compare_costs(std::string glpk_out_file_name,
                    std::string lp_out_file_name,
                   unsigned & successes,
                   unsigned & failures) {
    double a = get_glpk_cost(glpk_out_file_name);
    double b = get_lp_tst_cost(lp_out_file_name);

    if (values_are_one_percent_close(a, b)) {
        successes++;
    } else {
        failures++;
        std::cout << "glpsol cost is " << a << " lp_tst cost is " << b << std::endl;
    }
}



void compare_with_glpk(std::string glpk_out_file_name, std::string lp_out_file_name, unsigned & successes, unsigned & failures, std::string /*lp_file_name*/) {
#ifdef CHECK_GLPK_SOLUTION
    std::unordered_map<std::string, double> * solution_table =  get_solution_from_glpsol_output(glpk_out_file_name);
    if (solution_is_feasible(lp_file_name, *solution_table)) {
        std::cout << "glpk solution is feasible" << std::endl;
    } else {
        std::cout << "glpk solution is infeasible" << std::endl;
    }
    delete solution_table;
#endif
    if (compare_statuses(glpk_out_file_name, lp_out_file_name, successes, failures)) {
        compare_costs(glpk_out_file_name, lp_out_file_name, successes, failures);
    }
}
void test_lar_on_file(std::string file_name, argument_parser & args_parser);

void process_test_file(std::string test_dir, std::string test_file_name, argument_parser & args_parser, std::string out_dir, unsigned max_iters, unsigned time_limit, unsigned & successes, unsigned & failures, unsigned & inconclusives) {
    bool use_mpq = args_parser.option_is_used("--mpq");
    bool minimize = args_parser.option_is_used("--min");
    std::string full_lp_tst_out_name = out_dir + "/" + create_output_file_name(minimize, test_file_name, use_mpq);

    std::string input_file_name = test_dir + "/" + test_file_name;
    if (input_file_name[input_file_name.size() - 1] == '~') {
        //        std::cout << "ignoring " << input_file_name << std::endl;
        return;
    }
    std::cout <<"processing " <<  input_file_name << std::endl;

    std::ofstream out(full_lp_tst_out_name);
    if (!out.is_open()) {
        std::cout << "cannot open file " << full_lp_tst_out_name << std::endl;
        throw 0;
    }
    std::streambuf *coutbuf = std::cout.rdbuf(); // save old buffer
    std::cout.rdbuf(out.rdbuf()); // redirect std::cout to dir_entry->d_name!
    bool dual = args_parser.option_is_used("--dual");
    try {
        if (args_parser.option_is_used("--lar"))
            test_lar_on_file(input_file_name, args_parser);
        else
            solve_mps(input_file_name, minimize, max_iters, time_limit, use_mpq, dual, false, args_parser);
    }
    catch(...) {
        std::cout << "catching the failure" << std::endl;
        failures++;
        std::cout.rdbuf(coutbuf); // reset to standard output again
        return;
    }
    std::cout.rdbuf(coutbuf); // reset to standard output again

    if (args_parser.option_is_used("--compare_with_glpk")) {
        std::string glpk_out_file_name =  out_dir + "/" + create_output_file_name_for_glpsol(minimize, std::string(test_file_name));
        int glpk_exit_code = run_glpk(input_file_name, glpk_out_file_name, minimize, time_limit);
        if (glpk_exit_code != 0) {
            std::cout << "glpk failed" << std::endl;
            inconclusives++;
        } else {
            compare_with_glpk(glpk_out_file_name, full_lp_tst_out_name, successes, failures, input_file_name);
        }
    }
}
/*
  int my_readdir(DIR *dirp, struct dirent *
#ifndef LEAN_WINDOWS
               entry
#endif
               , struct dirent **result) {
#ifdef LEAN_WINDOWS
    *result = readdir(dirp); // NOLINT
    return *result != nullptr? 0 : 1;
#else
    return readdir_r(dirp, entry, result);
#endif
}
*/
/*
vector<std::pair<std::string, int>> get_file_list_of_dir(std::string test_file_dir) {
    DIR *dir;
    if ((dir  = opendir(test_file_dir.c_str())) == nullptr) {
        std::cout << "Cannot open directory " << test_file_dir << std::endl;
        throw 0;
    }
    vector<std::pair<std::string, int>> ret;
    struct dirent entry;
    struct dirent* result;
    int return_code;
    for (return_code = my_readdir(dir, &entry, &result);
#ifndef LEAN_WINDOWS
         result != nullptr &&
#endif
         return_code == 0;
         return_code = my_readdir(dir, &entry, &result)) {
      DIR *tmp_dp = opendir(result->d_name);
        struct stat file_record;
        if (tmp_dp == nullptr) {
            std::string s = test_file_dir+ "/" + result->d_name;
            int stat_ret = stat(s.c_str(), & file_record);
            if (stat_ret!= -1) {
                ret.push_back(make_pair(result->d_name, file_record.st_size));
            } else {
                perror("stat");
                exit(1);
            }
        } else  {
            closedir(tmp_dp);
        }
    }
    closedir(dir);
    return ret;
}
*/
/*
struct file_size_comp {
    unordered_map<std::string, int>& m_file_sizes;
    file_size_comp(unordered_map<std::string, int>& fs) :m_file_sizes(fs) {}
    int operator()(std::string a, std::string b) {
        std::cout << m_file_sizes.size() << std::endl;
        std::cout << a << std::endl;
        std::cout << b << std::endl;

        auto ls = m_file_sizes.find(a);
        std::cout << "fa" << std::endl;
        auto rs = m_file_sizes.find(b);
        std::cout << "fb" << std::endl;
        if (ls != m_file_sizes.end() && rs != m_file_sizes.end()) {
            std::cout << "fc " << std::endl;
            int r = (*ls < *rs? -1: (*ls > *rs)? 1 : 0);
            std::cout << "calc r " << std::endl;
            return r;
        } else {
            std::cout << "sc " << std::endl;
            return 0;
        }
    }
};

*/
struct sort_pred {
    bool operator()(const std::pair<std::string, int> &left, const std::pair<std::string, int> &right) {
        return left.second < right.second;
    }
};


void test_files_from_directory(std::string test_file_dir, argument_parser & args_parser) {
    /*
    std::cout << "loading files from directory \"" << test_file_dir << "\"" << std::endl;
    std::string out_dir = args_parser.get_option_value("--out_dir");
    if (out_dir.size() == 0) {
        out_dir = "/tmp/test";
    }
    DIR *out_dir_p = opendir(out_dir.c_str());
    if (out_dir_p == nullptr) {
        std::cout << "Cannot open output directory \"" << out_dir << "\"" << std::endl;
        return;
    }
    closedir(out_dir_p);
    vector<std::pair<std::string, int>> files = get_file_list_of_dir(test_file_dir);
    std::sort(files.begin(), files.end(), sort_pred());
    unsigned max_iters, time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    unsigned successes = 0, failures = 0, inconclusives = 0;
    for  (auto & t : files) {
        process_test_file(test_file_dir, t.first, args_parser, out_dir, max_iters, time_limit, successes, failures, inconclusives);
    }
    std::cout << "comparing with glpk: successes " << successes << ", failures " << failures << ", inconclusives " << inconclusives << std::endl;
    */
}


std::unordered_map<std::string, lp::mpq> get_solution_map(lp_solver<lp::mpq, lp::mpq> * lps, mps_reader<lp::mpq, lp::mpq> & reader) {
    std::unordered_map<std::string, lp::mpq> ret;
    for (auto it : reader.column_names()) {
        ret[it] = lps->get_column_value_by_name(it);
    }
    return ret;
}

void run_lar_solver(argument_parser & args_parser, lar_solver * solver, mps_reader<lp::mpq, lp::mpq> * reader) {
    std::string maxng = args_parser.get_option_value("--maxng");
    if (maxng.size() > 0) {
        solver->settings().max_number_of_iterations_with_no_improvements = atoi(maxng.c_str());
    }
    if (args_parser.option_is_used("-pd")){
        solver->settings().presolve_with_double_solver_for_lar = true;
    }
    
    std::string iter = args_parser.get_option_value("--max_iters");
    if (iter.size() > 0) {
        solver->settings().max_total_number_of_iterations = atoi(iter.c_str());
    }
    if (args_parser.option_is_used("--compare_with_primal")){
        if (reader == nullptr) {
            std::cout << "cannot compare with primal, the reader is null " << std::endl;
            return;
        }
        auto * lps = reader->create_solver(false);
        lps->find_maximal_solution();
        std::unordered_map<std::string, lp::mpq> sol = get_solution_map(lps, *reader);
        std::cout << "status = " << lp_status_to_string(solver->get_status()) <<  std::endl;
        return;
    }
    stopwatch sw;
    sw.start();
    lp_status status = solver->solve();
    std::cout << "status is " <<  lp_status_to_string(status) << ", processed for " << sw.get_current_seconds() <<" seconds, and " << solver->get_total_iterations() << " iterations" << std::endl;
    if (solver->get_status() == INFEASIBLE) {
        vector<std::pair<lp::mpq, constraint_index>> evidence;
        solver->get_infeasibility_explanation(evidence);
    }
    if (args_parser.option_is_used("--randomize_lar")) {
        if (solver->get_status() != OPTIMAL) {
            std::cout << "cannot check randomize on an infeazible  problem" << std::endl;
            return;
        }
        std::cout << "checking randomize" << std::endl;
        vector<var_index> all_vars = solver->get_list_of_all_var_indices();
        unsigned m = all_vars.size();
        if (m > 100)
            m = 100;
        
        var_index *vars = new var_index[m];
        for (unsigned i = 0; i < m; i++)
            vars[i]=all_vars[i];
        
        solver->random_update(m, vars);
        delete []vars;
    }
}

lar_solver * create_lar_solver_from_file(std::string file_name, argument_parser & args_parser) {
    if (args_parser.option_is_used("--smt")) {
        smt_reader reader(file_name);
        reader.read();
        if (!reader.is_ok()){
            std::cout << "cannot process " << file_name << std::endl;
            return nullptr;
        }
        return reader.create_lar_solver();
    }
    mps_reader<lp::mpq, lp::mpq> reader(file_name);
    reader.read();
    if (!reader.is_ok()) {
        std::cout << "cannot process " << file_name << std::endl;
        return nullptr;
    }
    return reader.create_lar_solver();
}

void test_lar_on_file(std::string file_name, argument_parser & args_parser) {
    lar_solver * solver = create_lar_solver_from_file(file_name, args_parser);
    mps_reader<lp::mpq, lp::mpq> reader(file_name);
    mps_reader<lp::mpq, lp::mpq> * mps_reader = nullptr;
    reader.read();
    if (reader.is_ok()) {
        mps_reader = & reader;
        run_lar_solver(args_parser, solver, mps_reader);
    }
    delete solver;
}

vector<std::string> get_file_names_from_file_list(std::string filelist) {
    std::ifstream file(filelist);
    if (!file.is_open()) {
        std::cout << "cannot open " << filelist << std::endl;
        return vector<std::string>();
    }
    vector<std::string> ret;
    bool end;
    do {
        std::string s = read_line(end, file);
        if (end)
            break;
        if (s.size() == 0)
            break;
        ret.push_back(s);
    } while (true);
    return ret;
}

void test_lar_solver(argument_parser & args_parser) {

    std::string file_name = args_parser.get_option_value("--file");
    if (file_name.size() > 0) {
        test_lar_on_file(file_name, args_parser);
        return;
    }

    std::string file_list = args_parser.get_option_value("--filelist");
    if (file_list.size() > 0) {
        for (std::string fn : get_file_names_from_file_list(file_list))
            test_lar_on_file(fn, args_parser);
        return;
    }
}

void test_numeric_pair() {
    numeric_pair<lp::mpq> a;
    numeric_pair<lp::mpq> b(2, lp::mpq(6, 2));
    a = b;
    numeric_pair<lp::mpq> c(0.1, 0.5);
    a += 2*c;
    a -= c;
    SASSERT (a == b + c);
    numeric_pair<lp::mpq> d = a * 2;
    std::cout << a  << std::endl;
    SASSERT(b == b);
    SASSERT(b < a);
    SASSERT(b <= a);
    SASSERT(a > b);
    SASSERT(a != b);
    SASSERT(a >= b);
    SASSERT(-a < b);
    SASSERT(a < 2 * b);
    SASSERT(b + b > a);
    SASSERT(lp::mpq(2.1) * b + b > a);
    SASSERT(-b * lp::mpq(2.1) - b < lp::mpq(0.99)  * a);
    std::cout << - b * lp::mpq(2.1) - b << std::endl;
    SASSERT(-b *(lp::mpq(2.1) + 1) == - b * lp::mpq(2.1) - b);
}

void get_matrix_dimensions(std::ifstream & f, unsigned & m, unsigned & n) {
    std::string line;
    getline(f, line);
    getline(f, line);
    vector<std::string> r = split_and_trim(line);
    m = atoi(r[1].c_str());
    getline(f, line);
    r = split_and_trim(line);
    n = atoi(r[1].c_str());
}

void read_row_cols(unsigned i, static_matrix<double, double>& A, std::ifstream & f) {
    do {
        std::string line;
        getline(f, line);
        if (line== "row_end")
            break;
        auto r = split_and_trim(line);
        SASSERT(r.size() == 4);
        unsigned j = atoi(r[1].c_str());
        double v = atof(r[3].c_str());
        A.set(i, j, v);
    } while (true);
}

bool read_row(static_matrix<double, double> & A, std::ifstream & f) {
    std::string line;
    getline(f, line);
    if (static_cast<int>(line.find("row")) == -1)
        return false;
    auto r = split_and_trim(line);
    if (r[0] != "row")
        std::cout << "wrong row line" << line << std::endl;
    unsigned i = atoi(r[1].c_str());
    read_row_cols(i, A, f);
    return true;
}

void read_rows(static_matrix<double, double>& A, std::ifstream & f) {
    while (read_row(A, f)) {}
}

void read_basis(vector<unsigned> & basis, std::ifstream & f) {
    std::cout << "reading basis" << std::endl;
    std::string line;
    getline(f, line);
    SASSERT(line == "basis_start");
    do {
        getline(f, line);
        if (line == "basis_end")
            break;
        unsigned j = atoi(line.c_str());
        basis.push_back(j);
    } while (true);
}

void read_indexed_vector(indexed_vector<double> & v, std::ifstream & f) {
    std::string line;
    getline(f, line);
    SASSERT(line == "vector_start");
    do {
        getline(f, line);
        if (line == "vector_end") break;
        auto r = split_and_trim(line);
        unsigned i = atoi(r[0].c_str());
        double val = atof(r[1].c_str());
        v.set_value(val, i);
        std::cout << "setting value " << i << " = " << val << std::endl;
    } while (true);
}

void check_lu_from_file(std::string lufile_name) {
    std::ifstream f(lufile_name);
    if (!f.is_open()) {
        std::cout << "cannot open file " << lufile_name << std::endl;
    }
    unsigned m, n;
    get_matrix_dimensions(f, m, n);
    std::cout << "init matrix " << m << " by " << n << std::endl;
    static_matrix<double, double> A(m, n);
    read_rows(A, f);
    vector<unsigned> basis;
    read_basis(basis, f);
    indexed_vector<double> v(m);
    //    read_indexed_vector(v, f);
    f.close();
    vector<int> basis_heading;
    lp_settings settings;
    vector<unsigned> non_basic_columns;
    lu<double, double> lsuhl(A, basis, settings);
     indexed_vector<double>  d(A.row_count());
    unsigned entering = 26;
    lsuhl.solve_Bd(entering, d, v);
#ifdef Z3DEBUG
    auto B = get_B(lsuhl, basis);
    vector<double>  a(m);
    A.copy_column_to_vector(entering, a);
    indexed_vector<double> cd(d);
    B.apply_from_left(cd.m_data, settings);
    SASSERT(vectors_are_equal(cd.m_data , a));
#endif
}

void test_square_dense_submatrix() {
    std::cout << "testing square_dense_submatrix" << std::endl;
    unsigned parent_dim = 7;
    sparse_matrix<double, double> parent(parent_dim);
    fill_matrix(parent);
    unsigned index_start = 3;
    square_dense_submatrix<double, double> d;
    d.init(&parent, index_start);
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            d[i][j] = i*3+j*2;
#ifdef Z3DEBUG
    unsigned dim = parent_dim - index_start;
    dense_matrix<double, double> m(dim, dim);
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            m[i-index_start][j-index_start] = d[i][j];
    print_matrix(&m, std::cout);
#endif
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            d[i][j] = d[j][i];
#ifdef Z3DEBUG
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            m[i-index_start][j-index_start] = d[i][j];

    print_matrix(&m, std::cout);
    std::cout << std::endl;
#endif
}



void print_st(lp_status status) {
    std::cout << lp_status_to_string(status) << std::endl;
}



void test_term() {
    lar_solver solver;
    unsigned _x = 0;
    unsigned _y = 1;
    var_index x = solver.add_var(_x);
    var_index y = solver.add_var(_y);

    vector<std::pair<mpq, var_index>> term_ls;
    term_ls.push_back(std::pair<mpq, var_index>((int)1, x));
    term_ls.push_back(std::pair<mpq, var_index>((int)1, y));
    var_index z = solver.add_term(term_ls, mpq(3));

    vector<std::pair<mpq, var_index>> ls;
    ls.push_back(std::pair<mpq, var_index>((int)1, x));
    ls.push_back(std::pair<mpq, var_index>((int)1, y));
    ls.push_back(std::pair<mpq, var_index>((int)1, z));
    
    solver.add_constraint(ls, lconstraint_kind::EQ, mpq(0));
    auto status = solver.solve();
    std::cout << lp_status_to_string(status) << std::endl;
    std::unordered_map<var_index, mpq> model;
    solver.get_model(model);
    
    for (auto & t : model) {
        std::cout << solver.get_variable_name(t.first) << " = " << t.second.get_double() << ",";
    }
    std::cout << std::endl;
    
}

void test_evidence_for_total_inf_simple(argument_parser & args_parser) {
    lar_solver solver;
    var_index x = solver.add_var(0);
    var_index y = solver.add_var(1);
    solver.add_var_bound(x, LE, -mpq(1));
    solver.add_var_bound(y, GE, mpq(0));
    vector<std::pair<mpq, var_index>> ls;
    
    ls.push_back(std::pair<mpq, var_index>((int)1, x));
    ls.push_back(std::pair<mpq, var_index>((int)1, y));
    solver.add_constraint(ls, GE, mpq(1));
    ls.pop_back();
    ls.push_back(std::pair<mpq, var_index>(-(int)1, y));
    solver.add_constraint(ls, lconstraint_kind::GE, mpq(0));
    auto status = solver.solve();
    std::cout << lp_status_to_string(status) << std::endl;
    std::unordered_map<var_index, mpq> model;
    SASSERT(solver.get_status() == INFEASIBLE);
}
void test_bound_propagation_one_small_sample1() {
    /*
(<= (+ a (* (- 1.0) b)) 0.0)
(<= (+ b (* (- 1.0) x_13)) 0.0)
--> (<= (+ a (* (- 1.0) c)) 0.0)

the inequality on (<= a c) is obtained from a triangle inequality (<= a b) (<= b c).
If b becomes basic variable, then it is likely the old solver ends up with a row that implies (<= a c).
 a - b <= 0.0
 b  - c <= 0.0

 got to get a <= c
    */
    std::function<bool (unsigned, bool, bool, const mpq & )> bound_is_relevant =
        [&](unsigned j, bool is_low_bound, bool strict, const rational& bound_val) {
            return true; 
        };   
    lar_solver ls;
    unsigned a = ls.add_var(0);
    unsigned b = ls.add_var(1);
    unsigned c = ls.add_var(2);
    vector<std::pair<mpq, var_index>> coeffs;
    coeffs.push_back(std::pair<mpq, var_index>(1, a));
    coeffs.push_back(std::pair<mpq, var_index>(-1, c));
    ls.add_term(coeffs, zero_of_type<mpq>());
    coeffs.pop_back();
    coeffs.push_back(std::pair<mpq, var_index>(-1, b));
    ls.add_term(coeffs, zero_of_type<mpq>());
    coeffs.clear();
    coeffs.push_back(std::pair<mpq, var_index>(1, a));
    coeffs.push_back(std::pair<mpq, var_index>(-1, b));
    ls.add_constraint(coeffs, LE, zero_of_type<mpq>());
    coeffs.clear();
    coeffs.push_back(std::pair<mpq, var_index>(1, b));
    coeffs.push_back(std::pair<mpq, var_index>(-1, c));
    ls.add_constraint(coeffs, LE, zero_of_type<mpq>());
    vector<implied_bound> ev;
    ls.add_var_bound(a, LE, mpq(1));
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
    std::cout << " bound ev from test_bound_propagation_one_small_sample1" << std::endl;
    for (auto & be : bp.m_ibounds)  {
        std::cout << "bound\n";
        ls.print_implied_bound(be, std::cout);
    }
}

void test_bound_propagation_one_small_samples() {
    test_bound_propagation_one_small_sample1();
    /*
      (>= x_46 0.0)
(<= x_29 0.0)
(not (<= x_68 0.0))
(<= (+ (* (/ 1001.0 1998.0) x_10) (* (- 1.0) x_151) x_68) (- (/ 1001.0 999.0)))
(<= (+ (* (/ 1001.0 999.0) x_9)
       (* (- 1.0) x_152)
       (* (/ 1001.0 999.0) x_151)
       (* (/ 1001.0 999.0) x_68))
    (- (/ 1502501.0 999000.0)))
(not (<= (+ (* (/ 999.0 2.0) x_10) (* (- 1.0) x_152) (* (- (/ 999.0 2.0)) x_151))
    (/ 1001.0 2.0)))
(not (<= x_153 0.0))z
(>= (+ x_9 (* (- (/ 1001.0 999.0)) x_10) (* (- 1.0) x_153) (* (- 1.0) x_68))
    (/ 5003.0 1998.0))
--> (not (<= (+ x_10 x_46 (* (- 1.0) x_29)) 0.0))

and 

(<= (+ a (* (- 1.0) b)) 0.0)
(<= (+ b (* (- 1.0) x_13)) 0.0)
--> (<= (+ a (* (- 1.0) x_13)) 0.0)

In the first case, there typically are no atomic formulas for bounding x_10. So there is never some
basic lemma of the form (>= x46 0), (<= x29 0), (>= x10 0) -> (not (<= (+ x10 x46 (- x29)) 0)).
Instead the bound on x_10 falls out from a bigger blob of constraints. 

In the second case, the inequality on (<= x19 x13) is obtained from a triangle inequality (<= x19 x9) (<= x9 x13).
If x9 becomes basic variable, then it is likely the old solver ends up with a row that implies (<= x19 x13).
     */
}
void test_bound_propagation_one_row() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0);
    unsigned x1 = ls.add_var(1);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x0));
    c.push_back(std::pair<mpq, var_index>(-1, x1));
    ls.add_constraint(c, EQ, one_of_type<mpq>());
    vector<implied_bound> ev;
    ls.add_var_bound(x0, LE, mpq(1));
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
} 
void test_bound_propagation_one_row_with_bounded_vars() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0);
    unsigned x1 = ls.add_var(1);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x0));
    c.push_back(std::pair<mpq, var_index>(-1, x1));
    ls.add_constraint(c, EQ, one_of_type<mpq>());
    vector<implied_bound> ev;
    ls.add_var_bound(x0, GE, mpq(-3));
    ls.add_var_bound(x0, LE, mpq(3));
    ls.add_var_bound(x0, LE, mpq(1));
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
}
void test_bound_propagation_one_row_mixed() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0);
    unsigned x1 = ls.add_var(1);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x0));
    c.push_back(std::pair<mpq, var_index>(-1, x1));
    ls.add_constraint(c, EQ, one_of_type<mpq>());
    vector<implied_bound> ev;
    ls.add_var_bound(x1, LE, mpq(1));
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
} 

void test_bound_propagation_two_rows() {
    lar_solver ls;
    unsigned x = ls.add_var(0);
    unsigned y = ls.add_var(1);
    unsigned z = ls.add_var(2);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x));
    c.push_back(std::pair<mpq, var_index>(2, y));
    c.push_back(std::pair<mpq, var_index>(3, z));
    ls.add_constraint(c, GE, one_of_type<mpq>());
    c.clear();
    c.push_back(std::pair<mpq, var_index>(3, x));
    c.push_back(std::pair<mpq, var_index>(2, y));
    c.push_back(std::pair<mpq, var_index>(1, z));
    ls.add_constraint(c, GE, one_of_type<mpq>());
    ls.add_var_bound(x, LE, mpq(2));
    vector<implied_bound> ev;
    ls.add_var_bound(y, LE, mpq(1));
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
} 

void test_total_case_u() {
    std::cout << "test_total_case_u\n";
    lar_solver ls;
    unsigned x = ls.add_var(0);
    unsigned y = ls.add_var(1);
    unsigned z = ls.add_var(2);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x));
    c.push_back(std::pair<mpq, var_index>(2, y));
    c.push_back(std::pair<mpq, var_index>(3, z));
    ls.add_constraint(c, LE, one_of_type<mpq>());
    ls.add_var_bound(x, GE, zero_of_type<mpq>());
    ls.add_var_bound(y, GE, zero_of_type<mpq>());
    vector<implied_bound> ev;
    ls.add_var_bound(z, GE, zero_of_type<mpq>());
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
}
bool contains_j_kind(unsigned j, lconstraint_kind kind, const mpq & rs, const vector<implied_bound> & ev) {
    for (auto & e : ev) {
        if (e.m_j == j && e.m_bound == rs && e.kind() == kind)
            return true;
    }
    return false;
}
void test_total_case_l(){
    std::cout << "test_total_case_l\n";
    lar_solver ls;
    unsigned x = ls.add_var(0);
    unsigned y = ls.add_var(1);
    unsigned z = ls.add_var(2);
    vector<std::pair<mpq, var_index>> c;
    c.push_back(std::pair<mpq, var_index>(1, x));
    c.push_back(std::pair<mpq, var_index>(2, y));
    c.push_back(std::pair<mpq, var_index>(3, z));
    ls.add_constraint(c, GE, one_of_type<mpq>());
    ls.add_var_bound(x, LE, one_of_type<mpq>());
    ls.add_var_bound(y, LE, one_of_type<mpq>());
    ls.settings().presolve_with_double_solver_for_lar = true;
    vector<implied_bound> ev;
    ls.add_var_bound(z, LE, zero_of_type<mpq>());
    ls.solve();
    lp_bound_propagator bp(ls);
    ls.propagate_bounds_for_touched_rows(bp);
    SASSERT(ev.size() == 4);
    SASSERT(contains_j_kind(x, GE, - one_of_type<mpq>(), ev));
}
void test_bound_propagation() {
    test_total_case_u();
    test_bound_propagation_one_small_samples();
    test_bound_propagation_one_row();
    test_bound_propagation_one_row_with_bounded_vars();
    test_bound_propagation_two_rows();
    test_bound_propagation_one_row_mixed();
    test_total_case_l();
    
}

void test_int_set() {
    int_set s(4);
    s.insert(2);
    s.print(std::cout);
    s.insert(1);
    s.insert(2);
    s.print(std::cout);
    SASSERT(s.contains(2));
    SASSERT(s.size() == 2);
    s.erase(2);
    SASSERT(s.size() == 1);
    s.erase(2);
    SASSERT(s.size() == 1);
    s.print(std::cout);
    s.insert(3);
    s.insert(2);
    s.clear();
    SASSERT(s.size() == 0);
    
    
}

void test_rationals_no_numeric_pairs() {
    stopwatch sw;

    vector<mpq> c;
    for (unsigned j = 0; j < 10; j ++)
        c.push_back(mpq(my_random()%100, 1 + my_random()%100 )); 
    
    vector<mpq> x;
    for (unsigned j = 0; j < 10; j ++)
        x.push_back(mpq(my_random()%100, 1 + my_random()%100 )); 

    unsigned k = 500000;
    mpq r=zero_of_type<mpq>();
    sw.start();
    
    for (unsigned j = 0; j < k; j++){
        mpq val = zero_of_type<mpq>();
        for (unsigned j=0;j< c.size(); j++){
            val += c[j]*x[j];
        }
        
        r += val;
    }
            
    sw.stop();
    std::cout << "operation with rationals no pairs " << sw.get_seconds() << std::endl;
    std::cout << T_to_string(r) << std::endl;
}

void test_rationals_no_numeric_pairs_plus() {
    stopwatch sw;

    vector<mpq> c;
    for (unsigned j = 0; j < 10; j ++)
        c.push_back(mpq(my_random()%100, 1 + my_random()%100 )); 
    
    vector<mpq> x;
    for (unsigned j = 0; j < 10; j ++)
        x.push_back(mpq(my_random()%100, 1 + my_random()%100 )); 

    unsigned k = 500000;
    mpq r=zero_of_type<mpq>();
    sw.start();
    
    for (unsigned j = 0; j < k; j++){
        mpq val = zero_of_type<mpq>();
        for (unsigned j=0;j< c.size(); j++){
            val = val + c[j]*x[j];
        }
        
        r = r + val;
    }
            
    sw.stop();
    std::cout << "operation with rationals no pairs " << sw.get_seconds() << std::endl;
    std::cout << T_to_string(r) << std::endl;
}



void test_rationals() {
    stopwatch sw;

    vector<mpq> c;
    for (unsigned j = 0; j < 10; j ++)
        c.push_back(mpq(my_random()%100, 1 + my_random()%100)); 

    
    
    vector<numeric_pair<mpq>> x;
    for (unsigned j = 0; j < 10; j ++)
        x.push_back(mpq(my_random()%100, 1 + my_random()%100 )); 

    std::cout << "x = ";
    print_vector(x, std::cout);
    
    unsigned k = 1000000;
    numeric_pair<mpq> r=zero_of_type<numeric_pair<mpq>>();
    sw.start();
    
    for (unsigned j = 0; j < k; j++) {
        for (unsigned i = 0; i < c.size(); i++) {
            r+= c[i] * x[i];
        }
    }   
    sw.stop();
    std::cout << "operation with rationals " << sw.get_seconds() << std::endl;
    std::cout << T_to_string(r) << std::endl;
}

void test_lp_local(int argn, char**argv) {
        std::cout << "resize\n";
    vector<mpq> r;
    r.resize(1);

    // initialize_util_module();
    // initialize_numerics_module();
    int ret;
    argument_parser args_parser(argn, argv);
    setup_args_parser(args_parser);
    if (!args_parser.parse()) {
        std::cout << args_parser.m_error_message << std::endl;
        std::cout << args_parser.usage_string();
        ret = 1;
        return finalize(ret);
    }

    args_parser.print();

    if (args_parser.option_is_used("--test_mpq")) {
        test_rationals();
        return finalize(0);
    }

    if (args_parser.option_is_used("--test_mpq_np")) {
        test_rationals_no_numeric_pairs();
        return finalize(0);
    }

  if (args_parser.option_is_used("--test_mpq_np_plus")) {
        test_rationals_no_numeric_pairs_plus();
        return finalize(0);
    }

  
    
    if (args_parser.option_is_used("--test_int_set")) {
        test_int_set();
        return finalize(0);
    }
    if (args_parser.option_is_used("--bp")) {
        test_bound_propagation();
        return finalize(0);
    }
        
    
    std::string lufile = args_parser.get_option_value("--checklu");
    if (lufile.size()) {
        check_lu_from_file(lufile);
        return finalize(0);
    }

#ifdef Z3DEBUG
    if (args_parser.option_is_used("--test_swaps")) {
        sparse_matrix<double, double> m(10);
        fill_matrix(m);
        test_swap_rows_with_permutation(m);
        test_swap_cols_with_permutation(m);
        return finalize(0);
    }
#endif
    if (args_parser.option_is_used("--test_perm")) {
        test_permutations();
        return finalize(0);
    }
    if (args_parser.option_is_used("--test_file_directory")) {
        test_files_from_directory(args_parser.get_option_value("--test_file_directory"), args_parser);
        return finalize(0);
    }
    std::string file_list = args_parser.get_option_value("--filelist");
    if (file_list.size() > 0) {
        for (std::string fn : get_file_names_from_file_list(file_list))
            solve_mps(fn, args_parser);
        return finalize(0);
    }

    if (args_parser.option_is_used("-tbq")) {
        test_binary_priority_queue();
        ret = 0;
        return finalize(ret);
    }

#ifdef Z3DEBUG
    lp_settings settings;
    update_settings(args_parser, settings);
    if (args_parser.option_is_used("--test_lu")) {
        test_lu(settings);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--test_small_lu")) {
        test_small_lu(settings);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--lar")){
        std::cout <<"calling test_lar_solver" << std::endl;
        test_lar_solver(args_parser);
        return finalize(0);
    }


    
    if (args_parser.option_is_used("--test_larger_lu")) {
        test_larger_lu(settings);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--test_larger_lu_with_holes")) {
        test_larger_lu_with_holes(settings);
        ret = 0;
        return finalize(ret);
    }
#endif
    if (args_parser.option_is_used("--eti")) {
        test_evidence_for_total_inf_simple(args_parser);
        ret = 0;
        return finalize(ret);
    }
        
    
    if (args_parser.option_is_used("--test_lp_0")) {
        test_lp_0();
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--smap")) {
        test_stacked();
        ret = 0;
        return finalize(ret);
    }
    if (args_parser.option_is_used("--term")) {
        test_term();
        ret = 0;
        return finalize(ret);
    }
    unsigned max_iters;
    unsigned time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    bool dual = args_parser.option_is_used("--dual");
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    std::string file_name = args_parser.get_option_value("--file");
    if (file_name.size() > 0) {
        solve_mps(file_name, args_parser.option_is_used("--min"), max_iters, time_limit, solve_for_rational, dual, args_parser.option_is_used("--compare_with_primal"), args_parser);
        ret = 0;
        return finalize(ret);
    }
    
    if (args_parser.option_is_used("--solve_some_mps")) {
#if _LINUX_
        solve_some_mps(args_parser);
#endif
        ret = 0;
        return finalize(ret);
    }
    //  lp::ccc = 0;
    return finalize(0);
    test_init_U();
    test_replace_column();
#ifdef Z3DEBUG
    sparse_matrix_with_permutaions_test();
    test_dense_matrix();
    test_swap_operations();
    test_permutations();
    test_pivot_like_swaps_and_pivot();
#endif
    tst1();
    std::cout << "done with LP tests\n";
    return finalize(0); // has_violations() ? 1 : 0);
}
}
void tst_lp(char ** argv, int argc, int& i) {
    lp::test_lp_local(argc - 2, argv + 2);
}
