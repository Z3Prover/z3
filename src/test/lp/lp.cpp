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

#include "util/rational.h"
#ifndef _WINDOWS
#include <dirent.h>
#endif
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <set>
#include <string>
#include <utility>

#include "math/lp/cross_nested.h"
#include "math/lp/emonics.h"
#include "math/lp/general_matrix.h"
#include "math/lp/hnf.h"
#include "math/lp/horner.h"
#include "math/lp/indexed_value.h"
#include "math/lp/int_cube.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_bound_propagator.h"
#include "math/lp/lp_utils.h"
#include "math/lp/matrix.h"
#include "math/lp/nla_solver.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/static_matrix.h"
#include "util/uint_set.h"
#include "test/lp/argument_parser.h"
#include "test/lp/gomory_test.h"
#include "test/lp/smt_reader.h"
#include "test/lp/test_file_reader.h"
#include "util/stacked_value.h"
#include "util/stopwatch.h"
void test_patching();
bool my_white_space(const char &a) { return a == ' ' || a == '\t'; }
size_t number_of_whites(const std::string &s) {
    size_t i = 0;
    for (; i < s.size(); i++)
        if (!my_white_space(s[i]))
            return i;
    return i;
}
size_t number_of_whites_from_end(const std::string &s) {
    size_t ret = 0;
    for (int i = static_cast<int>(s.size()) - 1; i >= 0; i--)
        if (my_white_space(s[i]))
            ret++;
        else
            break;

    return ret;
}

std::string &ltrim(std::string &s) {
    s.erase(0, number_of_whites(s));
    return s;
}

// trim from end
inline std::string &rtrim(std::string &s) {
    //       s.erase(std::find_if(s.rbegin(), s.rend(),
    //       std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
    s.erase(s.end() - number_of_whites_from_end(s), s.end());
    return s;
}
// trim from both ends
inline std::string &trim(std::string &s) { return ltrim(rtrim(s)); }

vector<std::string> string_split(const std::string &source,
                                 const char *delimiter, bool keep_empty) {
    vector<std::string> results;
    size_t prev = 0;
    size_t next = 0;
    while ((next = source.find_first_of(delimiter, prev)) != std::string::npos) {
        if (keep_empty || (next - prev != 0)) {
            results.push_back(source.substr(prev, next - prev));
        }
        prev = next + 1;
    }
    if (prev < source.size()) {
        results.push_back(source.substr(prev));
    }
    return results;
}

vector<std::string> split_and_trim(const std::string &line) {
    auto split = string_split(line, " \t", false);
    vector<std::string> ret;
    for (auto s : split) {
        ret.push_back(trim(s));
    }
    return ret;
}

namespace nla {
void test_horner();
void test_monics();
void test_order_lemma();
void test_monotone_lemma();
void test_basic_sign_lemma();
void test_tangent_lemma();
void test_basic_lemma_for_mon_zero_from_monomial_to_factors();
void test_basic_lemma_for_mon_zero_from_factors_to_monomial();
void test_basic_lemma_for_mon_neutral_from_monomial_to_factors();
void test_basic_lemma_for_mon_neutral_from_factors_to_monomial();

void test_cn_on_expr(nex_sum *t, cross_nested &cn) {
    t = to_sum(cn.get_nex_creator().simplify(t));
    TRACE("nla_test", tout << "t=" << *t << '\n';);
    cn.run(t);
}

void test_nex_order() {
#if Z3DEBUG
    enable_trace("nla_cn");
    enable_trace("nla_cn_details");
    // enable_trace("nla_cn_details_");
    enable_trace("nla_test");
    nex_creator r;
    r.set_number_of_vars(3);
    for (unsigned j = 0; j < r.get_number_of_vars(); j++)
        r.set_var_weight(j, 10 - j);
    nex_var *a = r.mk_var(0);
    nex_var *b = r.mk_var(1);
    nex_var *c = r.mk_var(2);
    ENSURE(r.gt(a, b));
    ENSURE(r.gt(b, c));
    ENSURE(r.gt(a, c));

    nex *ab = r.mk_mul(a, b);
    nex *ba = r.mk_mul(b, a);
    nex *ac = r.mk_mul(a, c);
    ENSURE(r.gt(ab, ac));
    ENSURE(!r.gt(ac, ab));
    nex *_3ac = r.mk_mul(rational(3), a, c);
    nex *_2ab = r.mk_mul(rational(2), a, b);
    ENSURE(r.gt(ab, _3ac));
    ENSURE(!r.gt(_3ac, ab));
    ENSURE(!r.gt(a, ab));
    ENSURE(r.gt(ab, a));
    ENSURE(r.gt(_2ab, _3ac));
    ENSURE(!r.gt(_3ac, _2ab));
    nex *_2a = r.mk_mul(rational(2), a);
    ENSURE(!r.gt(_2a, _2ab));
    ENSURE(r.gt(_2ab, _2a));
    ENSURE(nex_creator::equal(ab, ba));
    nex_sum *five_a_pl_one =
        r.mk_sum(r.mk_mul(rational(5), a), r.mk_scalar(rational(1)));
    nex_mul *poly = r.mk_mul(five_a_pl_one, b);
    nex *p = r.simplify(poly);
    std::cout << "poly = " << *poly << " , p = " << *p << "\n";
#endif
}

void test_simplify() {
#ifdef Z3DEBUG
    nex_creator r;
    cross_nested cn(
        [](const nex *n) {
            TRACE("nla_cn_test", tout << *n << "\n";);
            return false;
        },
        [](unsigned) { return false; }, []() { return 1; },  // for random
        r);
    enable_trace("nla_cn");
    enable_trace("nla_cn_details");
    // enable_trace("nla_cn_details_");
    enable_trace("nla_test");

    r.set_number_of_vars(3);
    for (unsigned j = 0; j < r.get_number_of_vars(); j++)
        r.set_var_weight(j, j);
    nex_var *a = r.mk_var(0);
    nex_var *b = r.mk_var(1);
    nex_var *c = r.mk_var(2);
    auto bc = r.mk_mul(b, c);
    auto a_plus_bc = r.mk_sum(a, bc);
    auto two_a_plus_bc = r.mk_mul(r.mk_scalar(rational(2)), a_plus_bc);
    auto simp_two_a_plus_bc = r.simplify(two_a_plus_bc);
    TRACE("nla_test", tout << *simp_two_a_plus_bc << "\n";);
    ENSURE(nex_creator::equal(simp_two_a_plus_bc, two_a_plus_bc));
    auto simp_a_plus_bc = r.simplify(a_plus_bc);
    ENSURE(to_sum(simp_a_plus_bc)->size() > 1);

    auto three_ab = r.mk_mul(r.mk_scalar(rational(3)), a, b);
    auto three_ab_square = r.mk_mul(three_ab, three_ab, three_ab);

    TRACE("nla_test", tout << "before simplify " << *three_ab_square << "\n";);
    three_ab_square = to_mul(r.simplify(three_ab_square));
    TRACE("nla_test", tout << *three_ab_square << "\n";);
    const rational &s = three_ab_square->coeff();
    ENSURE(s == rational(27));
    auto m = r.mk_mul(a, a);
    TRACE("nla_test_", tout << "m = " << *m << "\n";);
    /*
  auto n = r.mk_mul(b, b, b, b, b, b, b);
  n->add_child_in_power(b, 7);
  n->add_child(r.mk_scalar(rational(3)));
  n->add_child_in_power(r.mk_scalar(rational(2)), 2);
  n->add_child(r.mk_scalar(rational(1)));
  TRACE("nla_test_", tout << "n = " << *n << "\n";);
  m->add_child_in_power(n, 3);
  n->add_child_in_power(r.mk_scalar(rational(1, 3)), 2);
  TRACE("nla_test_", tout << "m = " << *m << "\n";);

  nex_sum * e = r.mk_sum(a, r.mk_sum(b, m));
  TRACE("nla_test", tout << "before simplify e = " << *e << "\n";);
  e = to_sum(r.simplify(e));
  TRACE("nla_test", tout << "simplified e = " << *e << "\n";);
  ENSURE(e->children().size() > 2);
  nex_sum * e_m = r.mk_sum();
  for (const nex* ex: to_sum(e)->children()) {
      nex* ce = r.mk_mul(r.clone(ex), r.mk_scalar(rational(3)));
      TRACE("nla_test", tout << "before simpl ce = " << *ce << "\n";);
      ce = r.simplify(ce);
      TRACE("nla_test", tout << "simplified ce = " << *ce << "\n";);
      e_m->add_child(ce);
  }
  e->add_child(e_m);
  TRACE("nla_test", tout << "before simplify sum e = " << *e << "\n";);
  e = to_sum(r.simplify(e));
  TRACE("nla_test", tout << "simplified sum e = " << *e << "\n";);

  nex * pr = r.mk_mul(a, b, b);
  TRACE("nla_test", tout << "before simplify pr = " << *pr << "\n";);
  r.simplify(pr);
  TRACE("nla_test", tout << "simplified sum e = " << *pr << "\n";);
  */
#endif
}

void test_cn_shorter() {
    //     nex_sum *clone;
    //     nex_creator cr;
    //     cross_nested cn(
    //         [](const nex* n) {
    //             TRACE("nla_test", tout <<"cn form = " <<  *n << "\n";

    // );
    //             return false;
    //         } ,
    //         [](unsigned) { return false; },
    //         []{ return 1; }, cr);
    //     enable_trace("nla_test");
    //     enable_trace("nla_cn");
    //     enable_trace("nla_cn_test");
    //     enable_trace("nla_cn_details");
    //     //    enable_trace("nla_cn_details_");
    //     enable_trace("nla_test_details");
    //     cr.set_number_of_vars(20);
    //     for (unsigned j = 0; j < cr.get_number_of_vars(); j++)
    //         cr.set_var_weight(j,j);

    //     nex_var* a = cr.mk_var(0);
    //     nex_var* b = cr.mk_var(1);
    //     nex_var* c = cr.mk_var(2);
    //     nex_var* d = cr.mk_var(3);
    //     nex_var* e = cr.mk_var(4);
    //     nex_var* g = cr.mk_var(6);

    //     nex* min_1 = cr.mk_scalar(rational(-1));
    //     // test_cn_on_expr(min_1*c*e + min_1*b*d + min_1*a*b + a*c);
    //     nex_mul* bcg = cr.mk_mul(b, c, g);
    //     /*
    //     bcg->add_child(min_1);
    //     nex* abcd = cr.mk_mul(a, b, c, d);
    //     nex* eae = cr.mk_mul(e, a, e);
    //     nex* three_eac = cr.mk_mul(e, a, c); to_mul(three_eac)->coeff() =
    //     rational(3); nex* _6aad = cr.mk_mul(cr.mk_scalar(rational(6)), a, a,
    //     d); clone = to_sum(cr.clone(cr.mk_sum(_6aad, abcd, eae, three_eac)));
    //     clone = to_sum(cr.simplify(clone));
    //     TRACE("nla_test", tout << "clone = " << *clone << "\n";);
    //     //    test_cn_on_expr(cr.mk_sum(aad,  abcd, aaccd, add, eae, eac, ed),
    //     cn); test_cn_on_expr(clone, cn);
    //     */
}

void test_cn() {
    // #ifdef Z3DEBUG
    //     test_cn_shorter();
    //     nex_creator cr;
    //     cross_nested cn(
    //         [](const nex* n) {
    //             TRACE("nla_test", tout <<"cn form = " <<  *n << "\n";);
    //             return false;
    //         } ,
    //         [](unsigned) { return false; },
    //         []{ return 1; }, cr);
    //     enable_trace("nla_test");
    //     enable_trace("nla_cn_test");
    //     //    enable_trace("nla_cn");
    //     //   enable_trace("nla_test_details");
    //     cr.set_number_of_vars(20);
    //     for (unsigned j = 0; j < cr.get_number_of_vars(); j++)
    //         cr.set_var_weight(j, j);

    //     nex_var* a = cr.mk_var(0);
    //     nex_var* b = cr.mk_var(1);
    //     nex_var* c = cr.mk_var(2);
    //     nex_var* d = cr.mk_var(3);
    //     nex_var* e = cr.mk_var(4);
    //     nex_var* g = cr.mk_var(6);
    //     nex_sum * a_p_ae_sq = cr.mk_sum(a, cr.mk_mul(a, e, e));
    //     a_p_ae_sq = to_sum(cr.simplify(a_p_ae_sq));
    //     test_cn_on_expr(a_p_ae_sq, cn);

    //     nex* min_1 = cr.mk_scalar(rational(-1));
    //     // test_cn_on_expr(min_1*c*e + min_1*b*d + min_1*a*b + a*c);
    //     nex* bcd = cr.mk_mul(b, c, d);
    //     nex_mul* bcg = cr.mk_mul(b, c, g);
    //     /*
    //     bcg->add_child(min_1);
    //     nex_sum* t = cr.mk_sum(bcd, bcg);
    //     test_cn_on_expr(t, cn);
    //     nex* abd = cr.mk_mul(a, b, d);
    //     nex* abc = cr.mk_mul(a, b, c);
    //     nex* abcd = cr.mk_mul(a, b, c, d);
    //     nex* aaccd = cr.mk_mul(a, a, c, c, d);
    //     nex* add = cr.mk_mul(a, d, d);
    //     nex* eae = cr.mk_mul(e, a, e);
    //     nex* eac = cr.mk_mul(e, a, c);
    //     nex* ed = cr.mk_mul(e, d);
    //     nex* cbd = cr.mk_mul(c, b, d);
    //     nex* acd = cr.mk_mul(a, c, d);

    //     nex* _6aad = cr.mk_mul(cr.mk_scalar(rational(6)), a, a, d);
    //     nex * clone = cr.clone(cr.mk_sum(_6aad, abcd, aaccd, add, eae, eac,
    //     ed)); clone = cr.simplify(clone); ENSURE(cr.is_simplified(clone));
    //     TRACE("nla_test", tout << "clone = " << *clone << "\n";);
    //     //    test_cn_on_expr(cr.mk_sum(aad,  abcd, aaccd, add, eae, eac, ed),
    //     cn); test_cn_on_expr(to_sum(clone), cn); TRACE("nla_test", tout <<
    //     "done\n";); test_cn_on_expr(cr.mk_sum(abd,  abc, cbd, acd), cn);
    //     TRACE("nla_test", tout << "done\n";);*/
    // #endif
    //     // test_cn_on_expr(a*b*b*d*d + a*b*b*c*d + c*b*b*d);
    //     // TRACE("nla_test", tout << "done\n";);
    //     // test_cn_on_expr(a*b*d + a*b*c + c*b*d);
}

}  // end of namespace nla

namespace lp {
unsigned seed = 1;

random_gen g_rand;
static unsigned my_random() { return g_rand(); }
struct simple_column_namer : public column_namer {
    std::string get_variable_name(unsigned j) const override {
        return std::string("x") + T_to_string(j);
    }
};

vector<int> allocate_basis_heading(
    unsigned count) {  // the rest of initialization will be handled by lu_QR
    vector<int> basis_heading(count, -1);
    return basis_heading;
}

void init_basic_part_of_basis_heading(vector<unsigned> &basis,
                                      vector<int> &basis_heading) {
    SASSERT(basis_heading.size() >= basis.size());
    unsigned m = basis.size();
    for (unsigned i = 0; i < m; i++) {
        unsigned column = basis[i];
        basis_heading[column] = i;
    }
}

void init_non_basic_part_of_basis_heading(vector<int> &basis_heading,
                                          vector<unsigned> &non_basic_columns) {
    non_basic_columns.clear();
    for (int j = basis_heading.size(); j--;) {
        if (basis_heading[j] < 0) {
            non_basic_columns.push_back(j);
            // the index of column j in m_nbasis is (- basis_heading[j] - 1)
            basis_heading[j] = -static_cast<int>(non_basic_columns.size());
        }
    }
}
void init_basis_heading_and_non_basic_columns_vector(
    vector<unsigned> &basis, vector<int> &basis_heading,
    vector<unsigned> &non_basic_columns) {
    init_basic_part_of_basis_heading(basis, basis_heading);
    init_non_basic_part_of_basis_heading(basis_heading, non_basic_columns);
}

void change_basis(unsigned entering, unsigned leaving, vector<unsigned> &basis,
                  vector<unsigned> &nbasis, vector<int> &basis_heading) {
    int place_in_basis = basis_heading[leaving];
    int place_in_non_basis = -basis_heading[entering] - 1;
    basis_heading[entering] = place_in_basis;
    basis_heading[leaving] = -place_in_non_basis - 1;
    basis[place_in_basis] = entering;
    nbasis[place_in_non_basis] = leaving;
}

int perm_id = 0;

bool get_int_from_args_parser(const char *option, argument_parser &args_parser,
                              unsigned &n) {
    std::string s = args_parser.get_option_value(option);
    if (!s.empty()) {
        n = atoi(s.c_str());
        return true;
    }
    return false;
}

bool get_double_from_args_parser(const char *option,
                                 argument_parser &args_parser, double &n) {
    std::string s = args_parser.get_option_value(option);
    if (!s.empty()) {
        n = atof(s.c_str());
        return true;
    }
    return false;
}

void get_time_limit_and_max_iters_from_parser(
    argument_parser &args_parser, unsigned &time_limit);  // forward definition

int get_random_rows() { return 5 + my_random() % 2; }

int get_random_columns() { return 5 + my_random() % 3; }

int get_random_int() {
    return -1 + my_random() % 2;  // (1.0 + RAND_MAX);
}

std::string read_line(bool &end, std::ifstream &file) {
    std::string s;
    if (!getline(file, s)) {
        end = true;
        return std::string();
    }
    end = false;
    return s;
}

bool contains(std::string const &s, char const *pattern) {
    return s.find(pattern) != std::string::npos;
}

void setup_args_parser(argument_parser &parser) {
    parser.add_option_with_help_string("-add_rows", "test add_rows of static matrix");
    parser.add_option_with_help_string("-monics", "test emonics");
    parser.add_option_with_help_string("-nex_order", "test nex order");
    parser.add_option_with_help_string("-nla_cn", "test cross nornmal form");
    parser.add_option_with_help_string("-nla_sim", "test nex simplify");
    parser.add_option_with_help_string(
        "-nla_blfmz_mf", "test_basic_lemma_for_mon_zero_from_factor_to_monomial");
    parser.add_option_with_help_string(
        "-nla_blfmz_fm",
        "test_basic_lemma_for_mon_zero_from_monomials_to_factor");
    parser.add_option_with_help_string("-nla_order",
                                       "test nla_solver order lemma");
    parser.add_option_with_help_string("-nla_monot",
                                       "test nla_solver order lemma");
    parser.add_option_with_help_string("-nla_tan", "test_tangent_lemma");
    parser.add_option_with_help_string("-nla_bsl", "test_basic_sign_lemma");
    parser.add_option_with_help_string("-horner", "test horner's heuristic");
    parser.add_option_with_help_string(
        "-nla_blnt_mf",
        "test_basic_lemma_for_mon_neutral_from_monomial_to_factors");
    parser.add_option_with_help_string(
        "-nla_blnt_fm",
        "test_basic_lemma_for_mon_neutral_from_factors_to_monomial");
    parser.add_option_with_help_string("-hnf", "test hermite normal form");
    parser.add_option_with_help_string("-dio", "dioph equalities");
    parser.add_option_with_help_string("-gomory", "gomory");
    parser.add_option_with_help_string("-intd", "test integer_domain");
    parser.add_option_with_help_string("-xyz_sample",
                                       "run a small interactive scenario");
    parser.add_option_with_after_string_with_help(
        "--percent_for_enter",
        "which percent of columns check for entering column");
    parser.add_option_with_help_string(
        "--totalinf",
        "minimizes the total infeasibility  instead of diminishing "
        "infeasibility of the rows");
    parser.add_option_with_after_string_with_help(
        "--rep_frq",
        "the report frequency, in how many iterations print the "
        "cost and other info ");
    parser.add_option_with_help_string("--smt", "smt file format");
    parser.add_option_with_after_string_with_help(
        "--filelist", "the file containing the list of files");
    parser.add_option_with_after_string_with_help("--file",
                                                  "the input file name");
    parser.add_option_with_after_string_with_help("--random_seed", "random seed");
    parser.add_option_with_help_string("--bp", "bound propagation");
    parser.add_option_with_help_string(
        "--min",
        "will look for the minimum for the given file if --file is "
        "used; the default is looking for the max");
    parser.add_option_with_help_string(
        "--max",
        "will look for the maximum for the given file if --file is "
        "used; it is the default behavior");
    parser.add_option_with_after_string_with_help(
        "--max_iters", "maximum total iterations in a core solver stage");
    parser.add_option_with_after_string_with_help("--time_limit",
                                                  "time limit in seconds");
    parser.add_option_with_help_string("--mpq", "solve for rational numbers");
    parser.add_option_with_after_string_with_help(
        "--simplex_strategy", "sets simplex strategy for rational number");
    parser.add_option_with_help_string("--test_lp_0", "solve a small lp");
    parser.add_option_with_help_string("--solve_some_mps",
                                       "solves a list of mps problems");
    parser.add_option_with_after_string_with_help(
        "--test_file_directory", "loads files from the directory for testing");
    parser.add_option_with_after_string_with_help(
        "--out_dir",
        "setting the output directory for tests, if not set /tmp is used");
    parser.add_option_with_help_string("--dual", "using the dual simplex solver");
    parser.add_option_with_help_string(
        "--compare_with_primal",
        "using the primal simplex solver for comparison");
    parser.add_option_with_help_string("--lar", "test lar_solver");
    parser.add_option_with_after_string_with_help(
        "--maxng", "max iterations without progress");
    parser.add_option_with_help_string("--randomize_lar",
                                       "test randomize functionality");
    parser.add_option_with_help_string("--smap", "test stacked_map");
    parser.add_option_with_help_string("--term", "simple term test");
    parser.add_option_with_help_string(
        "--eti", " run a small evidence test for total infeasibility scenario");
    parser.add_option_with_help_string("--row_inf",
                                       "forces row infeasibility search");
    parser.add_option_with_help_string("-pd", "presolve with double solver");
    parser.add_option_with_help_string("--test_int_set", "test int_set");
    parser.add_option_with_help_string("--test_mpq", "test rationals");
    parser.add_option_with_help_string("--test_mpq_np", "test rationals");
    parser.add_option_with_help_string("--test_mpq_np_plus",
                                       "test rationals using plus instead of +=");
    parser.add_option_with_help_string("--maximize_term", "test maximize_term()");
    parser.add_option_with_help_string("--patching", "test patching");
}

struct fff {
    int a;
    int b;
};

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
    v++;
    v++;
    std::cout << "before push v=" << v << std::endl;
    v.push();
    v++;
    v.push();
    v += 1;
    std::cout << "v = " << v << std::endl;
    v.pop(2);
    SASSERT(v == 4);
    const unsigned &rr = v;
    std::cout << rr << std::endl;
}

void test_stacked_value() { test_stacked_unsigned(); }

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
    v[1] = 3;
    v[2] = 3;
    v.push();
    v[0] = 7;
    v[1] = 9;
    v.pop(2);
    if (v.size())
        v[v.size() - 1] = 7;
    v.push();
    v.push_back(33);
    v[0] = 13;
    v.pop();
}

void test_stacked() {
    test_stacked_value();
    test_stacked_vector();
}

char *find_home_dir() {
#ifdef _WINDOWS
#else
    char *home_dir = getenv("HOME");
    if (home_dir == nullptr) {
        std::cout << "cannot find home directory" << std::endl;
        return nullptr;
    }
#endif
    return nullptr;
}

template <typename T>
void print_chunk(T *arr, unsigned len) {
    for (unsigned i = 0; i < len; i++) {
        std::cout << arr[i] << ", ";
    }
    std::cout << std::endl;
}

struct mem_cpy_place_holder {
    static void mem_copy_hook(int *destination, unsigned num) {
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

void get_time_limit_and_max_iters_from_parser(argument_parser &args_parser,
                                              unsigned &time_limit) {
    std::string time_limit_string = args_parser.get_option_value("--time_limit");
    if (!time_limit_string.empty()) {
        time_limit = atoi(time_limit_string.c_str());
    } else {
        time_limit = 0;
    }
}

std::string create_output_file_name(bool minimize, std::string file_name,
                                    bool use_mpq) {
    std::string ret = file_name + "_lp_tst_" + (minimize ? "min" : "max");
    if (use_mpq)
        return ret + "_mpq.out";
    return ret + ".out";
}

std::string create_output_file_name_for_glpsol(bool minimize,
                                               std::string file_name) {
    return file_name + (minimize ? "_min" : "_max") + "_glpk_out";
}

int run_glpk(std::string file_name, std::string glpk_out_file_name,
             bool minimize, unsigned time_limit) {
    std::string minmax(minimize ? "--min" : "--max");
    std::string tmlim = time_limit > 0 ? std::string(" --tmlim ") +
                                             std::to_string(time_limit) + " "
                                       : std::string();
    std::string command_line = std::string("glpsol --nointopt --nomip ") +
                               minmax + tmlim + +" -o " + glpk_out_file_name +
                               " " + file_name + " > /dev/null";
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

struct sort_pred {
    bool operator()(const std::pair<std::string, int> &left,
                    const std::pair<std::string, int> &right) {
        return left.second < right.second;
    }
};

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
        if (s.empty())
            break;
        ret.push_back(s);
    } while (true);
    return ret;
}

void test_numeric_pair() {
    numeric_pair<lp::mpq> a;
    numeric_pair<lp::mpq> b(2, lp::mpq(6, 2));
    a = b;
    numeric_pair<lp::mpq> c(0.1, 0.5);
    a += 2 * c;
    a -= c;
    SASSERT(a == b + c);
    numeric_pair<lp::mpq> d = a * 2;
    std::cout << a << std::endl;
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
    SASSERT(-b * lp::mpq(2.1) - b < lp::mpq(0.99) * a);
    std::cout << -b * lp::mpq(2.1) - b << std::endl;
    SASSERT(-b * (lp::mpq(2.1) + 1) == -b * lp::mpq(2.1) - b);
    std::cout << -b * (lp::mpq(2.1) + 1) << std::endl;
}

void get_matrix_dimensions(std::ifstream &f, unsigned &m, unsigned &n) {
    std::string line;
    getline(f, line);
    getline(f, line);
    vector<std::string> r = split_and_trim(line);
    m = atoi(r[1].c_str());
    getline(f, line);
    r = split_and_trim(line);
    n = atoi(r[1].c_str());
}

void print_st(lp_status status) {
    std::cout << lp_status_to_string(status) << std::endl;
}

void test_term() {
    lar_solver solver;
    unsigned _x = 0;
    unsigned _y = 1;
    lpvar x = solver.add_named_var(_x, true, "x");
    lpvar y = solver.add_named_var(_y, true, "y");
    enable_trace("lar_solver");
    enable_trace("cube");
    vector<std::pair<mpq, lpvar>> pairs;
    pairs.push_back(std::pair<mpq, lpvar>(mpq(2), x));
    pairs.push_back(std::pair<mpq, lpvar>(mpq(1), y));
    int ti = 0;
    unsigned x_plus_y = solver.add_term(pairs, ti++);
    solver.add_var_bound(x_plus_y, lconstraint_kind::GE, mpq(5, 3));
    solver.add_var_bound(x_plus_y, lconstraint_kind::LE, mpq(14, 3));
    pairs.pop_back();
    pairs.push_back(std::pair<mpq, lpvar>(mpq(-1), y));
    unsigned x_minus_y = solver.add_term(pairs, ti++);
    solver.add_var_bound(x_minus_y, lconstraint_kind::GE, mpq(5, 3));
    solver.add_var_bound(x_minus_y, lconstraint_kind::LE, mpq(14, 3));
    auto status = solver.solve();
    std::cout << lp_status_to_string(status) << std::endl;
    std::unordered_map<lpvar, mpq> model;
    if (status != lp_status::OPTIMAL) {
        std::cout << "non optimal" << std::endl;
        return;
    }
    std::cout << solver.constraints();
    std::cout << "\ntableau before cube\n";
    solver.pp(std::cout).print();
    std::cout << "\n";
    int_solver i_s(solver);
    solver.set_int_solver(&i_s);
    int_cube cuber(i_s);
    lia_move m = cuber();

    std::cout << "\n"
              << lia_move_to_string(m) << std::endl;
    model.clear();
    solver.get_model(model);
    for (auto &t : model) {
        std::cout << solver.get_variable_name(t.first) << " = "
                  << t.second.get_double() << ",";
    }

    std::cout << "\ntableau after cube\n";
    solver.pp(std::cout).print();
    std::cout << "Ax_is_correct = " << solver.ax_is_correct() << "\n";
}

void test_evidence_for_total_inf_simple(argument_parser &args_parser) {
    lar_solver solver;
    lpvar x = solver.add_var(0, false);
    lpvar y = solver.add_var(1, false);
    solver.add_var_bound(x, LE, mpq(-1));
    solver.add_var_bound(y, GE, mpq(0));
    vector<std::pair<mpq, lpvar>> ls;

    ls.push_back(std::pair<mpq, lpvar>(mpq(1), x));
    ls.push_back(std::pair<mpq, lpvar>(mpq(1), y));

    unsigned j = solver.add_term(ls, 1);
    solver.add_var_bound(j, GE, mpq(1));
    ls.pop_back();
    ls.push_back(std::pair<mpq, lpvar>(-mpq(1), y));
    j = solver.add_term(ls, 2);
    solver.add_var_bound(j, GE, mpq(0));
    auto status = solver.solve();
    std::cout << lp_status_to_string(status) << std::endl;
    std::unordered_map<lpvar, mpq> model;
    SASSERT(solver.get_status() == lp_status::INFEASIBLE);
}
void test_bound_propagation_one_small_sample1() {
    /*
    (<= (+ a (* (- 1.0) b)) 0.0)
    (<= (+ b (* (- 1.0) x_13)) 0.0)
    --> (<= (+ a (* (- 1.0) c)) 0.0)

    the inequality on (<= a c) is obtained from a triangle inequality (<= a b)
    (<= b c). If b becomes basic variable, then it is likely the old solver ends
    up with a row that implies (<= a c). a - b <= 0.0 b  - c <= 0.0

    got to get a <= c
  */
    std::function<bool(unsigned, bool, bool, const mpq &)> bound_is_relevant =
        [&](unsigned j, bool is_lower_bound, bool strict,
            const rational &bound_val) { return true; };
    lar_solver ls;
    unsigned a = ls.add_var(0, false);
    unsigned b = ls.add_var(1, false);
    unsigned c = ls.add_var(2, false);
    vector<std::pair<mpq, lpvar>> coeffs;
    coeffs.push_back(std::pair<mpq, lpvar>(mpq(1), a));
    coeffs.push_back(std::pair<mpq, lpvar>(mpq(-1), c));
    ls.add_term(coeffs, -1);
    coeffs.pop_back();
    coeffs.push_back(std::pair<mpq, lpvar>(mpq(-1), b));
    ls.add_term(coeffs, -1);
    coeffs.clear();
    coeffs.push_back(std::pair<mpq, lpvar>(mpq(1), a));
    coeffs.push_back(std::pair<mpq, lpvar>(mpq(-1), b));
    // ls.add_constraint(coeffs, LE, zero_of_type<mpq>());
    // coeffs.clear();
    // coeffs.push_back(std::pair<mpq, lpvar>(mpq(1), b));
    // coeffs.push_back(std::pair<mpq, lpvar>(mpq(-1), c));
    // ls.add_constraint(coeffs, LE, zero_of_type<mpq>());
    // vector<implied_bound> ev;
    // ls.add_var_bound(a, LE, mpq(1));
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
    // std::cout << " bound ev from test_bound_propagation_one_small_sample1" <<
    // std::endl; for (auto & be : bp.m_ibounds)  {
    //     std::cout << "bound\n";
    //     ls.print_implied_bound(be, std::cout);
    // } // todo: restore test
}

void test_bound_propagation_one_small_samples() {
    test_bound_propagation_one_small_sample1();
    /*
    (>= x_46 0.0)
    (<= x_29 0.0)
    (not (<= x_68 0.0))
    (<= (+ (* (/ 1001.0 1998.0) x_10) (* (- 1.0) x_151) x_68) (- (/ 1001.0
    999.0)))
    (<= (+ (* (/ 1001.0 999.0) x_9)
    (* (- 1.0) x_152)
    (* (/ 1001.0 999.0) x_151)
    (* (/ 1001.0 999.0) x_68))
    (- (/ 1502501.0 999000.0)))
    (not (<= (+ (* (/ 999.0 2.0) x_10) (* (- 1.0) x_152) (* (- (/ 999.0 2.0))
    x_151))
    (/ 1001.0 2.0)))
    (not (<= x_153 0.0))z
    (>= (+ x_9 (* (- (/ 1001.0 999.0)) x_10) (* (- 1.0) x_153) (* (- 1.0) x_68))
    (/ 5003.0 1998.0))
    --> (not (<= (+ x_10 x_46 (* (- 1.0) x_29)) 0.0))

    and

    (<= (+ a (* (- 1.0) b)) 0.0)
    (<= (+ b (* (- 1.0) x_13)) 0.0)
    --> (<= (+ a (* (- 1.0) x_13)) 0.0)

    In the first case, there typically are no atomic formulas for bounding x_10.
    So there is never some basic lemma of the form (>= x46 0), (<= x29 0), (>=
    x10 0) -> (not (<= (+ x10 x46 (- x29)) 0)). Instead the bound on x_10 falls
    out from a bigger blob of constraints.

    In the second case, the inequality on (<= x19 x13) is obtained from a
    triangle inequality (<= x19 x9) (<= x9 x13). If x9 becomes basic variable,
    then it is likely the old solver ends up with a row that implies (<= x19
    x13).
  */
}
void test_bound_propagation_one_row() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0, false);
    unsigned x1 = ls.add_var(1, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x0));
    c.push_back(std::pair<mpq, lpvar>(mpq(-1), x1));
    // todo : restore test
    // ls.add_constraint(c, EQ, one_of_type<mpq>());
    // vector<implied_bound> ev;
    // ls.add_var_bound(x0, LE, mpq(1));
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
}
void test_bound_propagation_one_row_with_bounded_vars() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0, false);
    unsigned x1 = ls.add_var(1, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x0));
    c.push_back(std::pair<mpq, lpvar>(mpq(-1), x1));
    // todo: restore test
    // ls.add_constraint(c, EQ, one_of_type<mpq>());
    // vector<implied_bound> ev;
    // ls.add_var_bound(x0, GE, mpq(-3));
    // ls.add_var_bound(x0, LE, mpq(3));
    // ls.add_var_bound(x0, LE, mpq(1));
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
}
void test_bound_propagation_one_row_mixed() {
    lar_solver ls;
    unsigned x0 = ls.add_var(0, false);
    unsigned x1 = ls.add_var(1, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x0));
    c.push_back(std::pair<mpq, lpvar>(mpq(-1), x1));
    // todo: restore test
    // ls.add_constraint(c, EQ, one_of_type<mpq>());
    // vector<implied_bound> ev;
    // ls.add_var_bound(x1, LE, mpq(1));
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
}

void test_bound_propagation_two_rows() {
    lar_solver ls;
    unsigned x = ls.add_var(0, false);
    unsigned y = ls.add_var(1, false);
    unsigned z = ls.add_var(2, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x));
    c.push_back(std::pair<mpq, lpvar>(mpq(2), y));
    c.push_back(std::pair<mpq, lpvar>(mpq(3), z));
    // todo: restore test
    // ls.add_constraint(c, GE, one_of_type<mpq>());
    // c.clear();
    // c.push_back(std::pair<mpq, lpvar>(mpq(3), x));
    // c.push_back(std::pair<mpq, lpvar>(mpq(2), y));
    // c.push_back(std::pair<mpq, lpvar>(mpq(y), z));
    // ls.add_constraint(c, GE, one_of_type<mpq>());
    // ls.add_var_bound(x, LE, mpq(2));
    // vector<implied_bound> ev;
    // ls.add_var_bound(y, LE, mpq(1));
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
}

void test_total_case_u() {
    std::cout << "test_total_case_u\n";
    lar_solver ls;
    unsigned x = ls.add_var(0, false);
    unsigned y = ls.add_var(1, false);
    unsigned z = ls.add_var(2, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x));
    c.push_back(std::pair<mpq, lpvar>(mpq(2), y));
    c.push_back(std::pair<mpq, lpvar>(mpq(3), z));
    // todo: restore test
    // ls.add_constraint(c, LE, one_of_type<mpq>());
    // ls.add_var_bound(x, GE, zero_of_type<mpq>());
    // ls.add_var_bound(y, GE, zero_of_type<mpq>());
    // vector<implied_bound> ev;
    // ls.add_var_bound(z, GE, zero_of_type<mpq>());
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
}
bool contains_j_kind(unsigned j, lconstraint_kind kind, const mpq &rs,
                     const vector<implied_bound> &ev) {
    for (auto &e : ev) {
        if (e.m_j == j && e.m_bound == rs && e.kind() == kind)
            return true;
    }
    return false;
}
void test_total_case_l() {
    std::cout << "test_total_case_l\n";
    lar_solver ls;
    unsigned x = ls.add_var(0, false);
    unsigned y = ls.add_var(1, false);
    unsigned z = ls.add_var(2, false);
    vector<std::pair<mpq, lpvar>> c;
    c.push_back(std::pair<mpq, lpvar>(mpq(1), x));
    c.push_back(std::pair<mpq, lpvar>(mpq(2), y));
    c.push_back(std::pair<mpq, lpvar>(mpq(3), z));
    // todo: restore test
    // ls.add_constraint(c, GE, one_of_type<mpq>());
    // ls.add_var_bound(x, LE, one_of_type<mpq>());
    // ls.add_var_bound(y, LE, one_of_type<mpq>());
    // ls.settings().presolve_with_double_solver_for_lar = true;
    // vector<implied_bound> ev;
    // ls.add_var_bound(z, LE, zero_of_type<mpq>());
    // ls.solve();
    // my_bound_propagator bp(ls);
    // ls.propagate_bounds_for_touched_rows(bp);
    // SASSERT(ev.size() == 4);
    // SASSERT(contains_j_kind(x, GE, - one_of_type<mpq>(), ev));
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
    indexed_uint_set s;
    s.insert(1);
    s.insert(2);
    SASSERT(s.contains(2));
    SASSERT(s.size() == 2);
    s.remove(2);
    SASSERT(s.size() == 1);
    s.insert(3);
    s.insert(2);
    s.reset();
    SASSERT(s.size() == 0);
    std::cout << "done test_int_set\n";
}

void test_rationals_no_numeric_pairs() {
    stopwatch sw;

    vector<mpq> c;
    for (unsigned j = 0; j < 10; j++)
        c.push_back(mpq(my_random() % 100, 1 + my_random() % 100));

    vector<mpq> x;
    for (unsigned j = 0; j < 10; j++)
        x.push_back(mpq(my_random() % 100, 1 + my_random() % 100));

    unsigned k = 500000;
    mpq r = zero_of_type<mpq>();
    sw.start();

    for (unsigned j = 0; j < k; j++) {
        mpq val = zero_of_type<mpq>();
        for (unsigned j = 0; j < c.size(); j++) {
            val += c[j] * x[j];
        }

        r += val;
    }

    sw.stop();
    std::cout << "operation with rationals no pairs " << sw.get_seconds()
              << std::endl;
    std::cout << T_to_string(r) << std::endl;
}

void test_rationals_no_numeric_pairs_plus() {
    stopwatch sw;

    vector<mpq> c;
    for (unsigned j = 0; j < 10; j++)
        c.push_back(mpq(my_random() % 100, 1 + my_random() % 100));

    vector<mpq> x;
    for (unsigned j = 0; j < 10; j++)
        x.push_back(mpq(my_random() % 100, 1 + my_random() % 100));

    unsigned k = 500000;
    mpq r = zero_of_type<mpq>();
    sw.start();

    for (unsigned j = 0; j < k; j++) {
        mpq val = zero_of_type<mpq>();
        for (unsigned j = 0; j < c.size(); j++) {
            val = val + c[j] * x[j];
        }

        r = r + val;
    }

    sw.stop();
    std::cout << "operation with rationals no pairs " << sw.get_seconds()
              << std::endl;
    std::cout << T_to_string(r) << std::endl;
}

void test_rationals() {
    stopwatch sw;

    vector<rational> c;
    for (unsigned j = 0; j < 10; j++)
        c.push_back(rational(my_random() % 100, 1 + my_random() % 100));

    vector<numeric_pair<rational>> x;
    for (unsigned j = 0; j < 10; j++)
        x.push_back(numeric_pair<rational>(
            rational(my_random() % 100, 1 + my_random() % 100)));

    std::cout << "x = ";
    print_vector(x, std::cout);

    unsigned k = 1000000;
    numeric_pair<rational> r = zero_of_type<numeric_pair<rational>>();
    sw.start();

    for (unsigned j = 0; j < k; j++) {
        for (unsigned i = 0; i < c.size(); i++) {
            r += c[i] * x[i];
        }
    }
    sw.stop();
    std::cout << "operation with rationals " << sw.get_seconds() << std::endl;
    std::cout << T_to_string(r) << std::endl;
}

void get_random_interval(bool &neg_inf, bool &pos_inf, int &x, int &y) {
    int i = my_random() % 10;
    if (i == 0) {
        neg_inf = true;
    } else {
        neg_inf = false;
        x = my_random() % 100;
    }
    i = my_random() % 10;
    if (i == 0) {
        pos_inf = true;
    } else {
        pos_inf = false;
        if (!neg_inf) {
            y = x + my_random() % (101 - x);
            SASSERT(y >= x);
        } else {
            y = my_random() % 100;
        }
    }
    SASSERT((neg_inf || (0 <= x && x <= 100)) &&
            (pos_inf || (0 <= y && y <= 100)));
}

void test_gomory_cut_0() {
    gomory_test g(
        [](unsigned j) { return "v" + T_to_string(j); }  // name_function_p
        ,
        [](unsigned j) {  // get_value_p
            if (j == 1)
                return mpq(2730, 1727);
            if (j == 2)
                return zero_of_type<mpq>();
            if (j == 3)
                return mpq(3);
            UNREACHABLE();
            return zero_of_type<mpq>();
        },
        [](unsigned j) {  // at_low_p
            if (j == 1)
                return false;
            if (j == 2)
                return true;
            if (j == 3)
                return true;
            UNREACHABLE();
            return false;
        },
        [](unsigned j) {  // at_upper
            if (j == 1)
                return false;
            if (j == 2)
                return true;
            if (j == 3)
                return false;
            UNREACHABLE();
            return false;
        },
        [](unsigned j) {  // lower_bound
            if (j == 1) {
                UNREACHABLE();  // unlimited from below
                return impq(0);
            }
            if (j == 2)
                return impq(0);
            if (j == 3)
                return impq(3);
            UNREACHABLE();
            return impq(0);
        },
        [](unsigned j) {  // upper
            if (j == 1) {
                UNREACHABLE();  // unlimited from above
                return impq(0);
            }
            if (j == 2)
                return impq(0);
            if (j == 3)
                return impq(10);
            UNREACHABLE();
            return impq(0);
        },
        [](unsigned) { return 0; }, [](unsigned) { return 0; });
    lar_term t;
    mpq k;
    explanation expl;
    unsigned inf_col = 1;
    vector<std::pair<mpq, unsigned>> row;
    row.push_back(std::make_pair(mpq(1), 1));
    row.push_back(std::make_pair(mpq(2731, 1727), 2));
    row.push_back(std::make_pair(mpq(-910, 1727), 3));
    g.mk_gomory_cut(t, k, expl, inf_col, row);
}

void test_gomory_cut_1() {
    gomory_test g(
        [](unsigned j) { return "v" + T_to_string(j); }  // name_function_p
        ,
        [](unsigned j) {  // get_value_p
            if (j == 1)
                return mpq(-2);
            if (j == 2)
                return mpq(4363334, 2730001);
            if (j == 3)
                return mpq(1);
            UNREACHABLE();
            return zero_of_type<mpq>();
        },
        [](unsigned j) {  // at_low_p
            if (j == 1)
                return false;
            if (j == 2)
                return false;
            if (j == 3)
                return true;
            UNREACHABLE();
            return false;
        },
        [](unsigned j) {  // at_upper
            if (j == 1)
                return true;
            if (j == 2)
                return false;
            if (j == 3)
                return true;
            UNREACHABLE();
            return false;
        },
        [](unsigned j) {  // lower_bound
            if (j == 1) {
                UNREACHABLE();  // unlimited from below
                return impq(0);
            }
            if (j == 2)
                return impq(1);
            if (j == 3)
                return impq(1);
            UNREACHABLE();
            return impq(0);
        },
        [](unsigned j) {  // upper
            if (j == 1) {
                return impq(-2);
            }
            if (j == 2)
                return impq(3333);
            if (j == 3)
                return impq(10000);
            UNREACHABLE();
            return impq(0);
        },
        [](unsigned) { return 0; }, [](unsigned) { return 0; });
    lar_term t;
    mpq k;
    explanation expl;
    unsigned inf_col = 2;
    vector<std::pair<mpq, unsigned>> row;
    row.push_back(std::make_pair(mpq(1726667, 2730001), 1));
    row.push_back(std::make_pair(mpq(-910000, 2730001), 3));
    row.push_back(std::make_pair(mpq(1), 2));
    g.mk_gomory_cut(t, k, expl, inf_col, row);
}

void call_hnf(general_matrix &A);

void test_hnf_m_less_than_n() {
#ifdef Z3DEBUG
    general_matrix A;
    vector<mpq> v;
    // example 4.3 from Nemhauser, Wolsey
    v.push_back(mpq(2));
    v.push_back(mpq(6));
    v.push_back(mpq(1));
    v.push_back(mpq(3));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(4));
    v.push_back(mpq(7));
    v.push_back(mpq(7));
    v.push_back(mpq(3));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(0));
    v.push_back(mpq(0));
    v.push_back(mpq(1));
    v.push_back(mpq(5));
    A.push_row(v);
    call_hnf(A);
#endif
}
void test_hnf_m_greater_than_n() {
#ifdef Z3DEBUG
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(2));
    v.push_back(mpq(6));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(4));
    v.push_back(mpq(7));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(0));
    v.push_back(mpq(0));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(12));
    v.push_back(mpq(55));
    A.push_row(v);
    call_hnf(A);
#endif
}

void cutting_the_mix_example_1() {
    mpq sev(7);
    mpq nine(9);
    mpq d, u, vv;
    hnf_calc::extended_gcd_minimal_uv(sev, nine, d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;
    hnf_calc::extended_gcd_minimal_uv(sev, -nine, d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;

    hnf_calc::extended_gcd_minimal_uv(-nine, -nine, d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;

    hnf_calc::extended_gcd_minimal_uv(-sev * 2, sev, d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;

    hnf_calc::extended_gcd_minimal_uv(mpq(24), mpq(-7), d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;
    hnf_calc::extended_gcd_minimal_uv(-mpq(24), mpq(7), d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;
    hnf_calc::extended_gcd_minimal_uv(mpq(24), mpq(7), d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;
    hnf_calc::extended_gcd_minimal_uv(-mpq(21), mpq(7), d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;

    hnf_calc::extended_gcd_minimal_uv(mpq(21), -mpq(7), d, u, vv);
    std::cout << "d = " << d << ", u = " << u << ", vv = " << vv << std::endl;
}

#ifdef Z3DEBUG

void fill_general_matrix(general_matrix &M) {
    unsigned m = M.row_count();
    unsigned n = M.column_count();
    for (unsigned i = 0; i < m; i++)
        for (unsigned j = 0; j < n; j++)
            M[i][j] = mpq(static_cast<int>(my_random() % 13) - 6);
}

void call_hnf(general_matrix &A) {
    svector<unsigned> r;
    mpq d =
        hnf_calc::determinant_of_rectangular_matrix(A, r, mpq((int)1000000000));
    A.shrink_to_rank(r);
    hnf<general_matrix> h(A, d);
}

void test_hnf_for_dim(int m) {
    general_matrix M(m, m + my_random() % m);
    fill_general_matrix(M);
    call_hnf(M);
}
void test_hnf_1_2() {
    std::cout << "test_hnf_1_2" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(5));
    v.push_back(mpq(26));
    A.push_row(v);
    call_hnf(A);
    std::cout << "test_hnf_1_2 passed" << std::endl;
}
void test_hnf_2_2() {
    std::cout << "test_hnf_2_2" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(5));
    v.push_back(mpq(26));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(2));
    v.push_back(mpq(11));
    A.push_row(v);
    call_hnf(A);

    std::cout << "test_hnf_2_2 passed" << std::endl;
}

void test_hnf_3_3() {
    std::cout << "test_hnf_3_3" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(-3));
    v.push_back(mpq(0));
    v.push_back(mpq(-1));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(-1));
    v.push_back(mpq(0));
    v.push_back(mpq(-6));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(-2));
    v.push_back(mpq(-4));
    v.push_back(mpq(-3));
    A.push_row(v);

    call_hnf(A);
    std::cout << "test_hnf_3_3 passed" << std::endl;
}
void test_hnf_4_4() {
    std::cout << "test_hnf_4_4" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(4));
    v.push_back(mpq(3));
    v.push_back(mpq(-5));
    v.push_back(mpq(6));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(1));
    v.push_back(mpq(-3));
    v.push_back(mpq(1));
    v.push_back(mpq(-4));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(4));
    v.push_back(mpq(4));
    v.push_back(mpq(4));
    v.push_back(mpq(4));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(2));
    v.push_back(mpq(-2));
    v.push_back(mpq(-5));
    v.push_back(mpq(6));
    A.push_row(v);
    call_hnf(A);
    std::cout << "test_hnf_4_4 passed" << std::endl;
}
void test_hnf_5_5() {
    std::cout << "test_hnf_5_5" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(-4));
    v.push_back(mpq(5));
    v.push_back(mpq(-5));
    v.push_back(mpq(1));
    v.push_back(mpq(-3));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(3));
    v.push_back(mpq(-1));
    v.push_back(mpq(2));
    v.push_back(mpq(3));
    v.push_back(mpq(-5));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(0));
    v.push_back(mpq(6));
    v.push_back(mpq(-5));
    v.push_back(mpq(-6));
    v.push_back(mpq(-2));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(1));
    v.push_back(mpq(0));
    v.push_back(mpq(-4));
    v.push_back(mpq(-4));
    v.push_back(mpq(4));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(-2));
    v.push_back(mpq(3));
    v.push_back(mpq(6));
    v.push_back(mpq(-5));
    v.push_back(mpq(-1));
    A.push_row(v);
    call_hnf(A);
    std::cout << "test_hnf_5_5 passed" << std::endl;
}

void test_small_generated_hnf() {
    std::cout << "test_small_rank_hnf" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.push_back(mpq(5));
    v.push_back(mpq(26));
    A.push_row(v);
    v.clear();
    v.push_back(zero_of_type<mpq>());
    v.push_back(zero_of_type<mpq>());
    A.push_row(v);
    call_hnf(A);
    std::cout << "test_small_rank_hnf passed" << std::endl;
}
void test_larger_generated_hnf() {
    std::cout << "test_larger_generated_rank_hnf" << std::endl;
    general_matrix A;
    vector<mpq> v;
    v.clear();
    v.push_back(mpq(5));
    v.push_back(mpq(6));
    v.push_back(mpq(3));
    v.push_back(mpq(1));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(5));
    v.push_back(mpq(2));
    v.push_back(mpq(3));
    v.push_back(mpq(7));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(5));
    v.push_back(mpq(6));
    v.push_back(mpq(3));
    v.push_back(mpq(1));
    A.push_row(v);
    v.clear();
    v.push_back(mpq(5));
    v.push_back(mpq(2));
    v.push_back(mpq(3));
    v.push_back(mpq(7));
    A.push_row(v);
    call_hnf(A);
    std::cout << "test_larger_generated_rank_hnf passed" << std::endl;
}
#endif

void test_maximize_term() {
    std::cout << "test_maximize_term\n";
    lar_solver solver;
    int_solver i_solver(solver);  // have to create it too
    unsigned _x = 0;
    unsigned _y = 1;
    lpvar x = solver.add_var(_x, false);
    lpvar y = solver.add_var(_y, true);
    vector<std::pair<mpq, lpvar>> term_ls;
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(1), x));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(-1), y));
    unsigned term_x_min_y = solver.add_term(term_ls, -1);
    term_ls.clear();
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(2), x));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(2), y));

    unsigned term_2x_pl_2y = solver.add_term(term_ls, -1);
    solver.add_var_bound(term_x_min_y, LE, zero_of_type<mpq>());
    solver.add_var_bound(term_2x_pl_2y, LE, mpq(5));
    solver.find_feasible_solution();
    SASSERT(solver.get_status() == lp_status::OPTIMAL);
    std::cout << solver.constraints();
    std::unordered_map<lpvar, mpq> model;
    solver.get_model(model);
    for (auto p : model) {
        std::cout << "v[" << p.first << "] = " << p.second << std::endl;
    }
    std::cout << "calling int_solver\n";
    explanation ex;
    lia_move lm = i_solver.check(&ex);
    VERIFY(lm == lia_move::sat);
    impq term_max;
    lp_status st = solver.maximize_term(term_2x_pl_2y, term_max);

    std::cout << "status = " << lp_status_to_string(st) << std::endl;
    std::cout << "term_max = " << term_max << std::endl;
    solver.get_model(model);
    for (auto p : model) {
        std::cout << "v[" << p.first << "] = " << p.second << std::endl;
    }
}

void test_dio() {
    std::cout << "test dio\n";
    lar_solver solver;
    int_solver i_solver(solver); 
    lp::explanation exp;
    i_solver.set_expl(&exp);
    unsigned _x1 = 0;
    unsigned _x2 = 1;
    unsigned _x3 = 2;
    unsigned _fx_7 = 3;
    unsigned _fx_17 = 4;
/*
    3x1 + 3x2 + 14x3 − 7 = 0
    7x1 + 12x2 + 31x3 − 17 = 0
*/
    lpvar x1 = solver.add_var(_x1, true);
    lpvar x2 = solver.add_var(_x2, true);
    lpvar x3 = solver.add_var(_x3, true);
    lpvar fx_7 = solver.add_var(_fx_7, true);
    lpvar fx_17 = solver.add_var(_fx_17, true);
    vector<std::pair<mpq, lpvar>> term_ls;
    /* 3x1 + 3x2 +```cpp
    14x3 − 7 */
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(3), x1));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(3), x2));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(14), x3));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(-1), fx_7));
    for (auto & p: term_ls) {
        p.first = -p.first;
    }
    unsigned t0 = solver.add_term(term_ls, 10);
    term_ls.clear();
    /* 7x1 + 12x2 + 31x3 − 17 = 0*/
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(7), x1));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(12), x2));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(31), x3));
    term_ls.push_back(std::pair<mpq, lpvar>(mpq(-1), fx_17));
    
    for (auto & p: term_ls) {
        p.first = -p.first;
    }
    unsigned t1 = solver.add_term(term_ls, 11);

    solver.add_var_bound(fx_7, LE, mpq(-7));
    solver.add_var_bound(fx_7, GE, mpq(-7));
    solver.add_var_bound(fx_17, LE, mpq(-17));
    solver.add_var_bound(fx_17, GE, mpq(-17));
    solver.add_var_bound(t0, LE, mpq(0));
    solver.add_var_bound(t0, GE, mpq(0));
    solver.add_var_bound(t1, LE, mpq(0));
    solver.add_var_bound(t1, GE, mpq(0));
//    solver.find_feasible_solution();
    //SASSERT(solver.get_status() == lp_status::OPTIMAL);
    enable_trace("dioph_eq");
    enable_trace("dioph_eq_fresh");
#ifdef Z3DEBUG     
    auto r = i_solver.dio_test();
#endif    
    
}
#ifdef Z3DEBUG
void test_hnf() {
    test_larger_generated_hnf();
    test_small_generated_hnf();
    test_hnf_1_2();
    test_hnf_3_3();
    test_hnf_4_4();
    test_hnf_5_5();
    test_hnf_2_2();
    for (unsigned k = 1000; k > 0; k--)
        for (int i = 1; i < 8; i++)
            test_hnf_for_dim(i);
    cutting_the_mix_example_1();
    //    test_hnf_m_less_than_n();
    //    test_hnf_m_greater_than_n();
}
#endif
void test_gomory_cut() {
    test_gomory_cut_0();
    test_gomory_cut_1();
}

    void test_add_rows() {
// Create a static_matrix object
        lp::static_matrix<mpq, impq> matrix;
        matrix.init_empty_matrix(3, 3);

        // Populate the matrix with initial values
        matrix.set(0, 0, mpq(1));
        matrix.set(0, 1, mpq(2));
        matrix.set(1, 0, mpq(3));
        matrix.set(1, 2, mpq(4));
        matrix.set(2, 1, mpq(5));
        matrix.set(2, 2, mpq(6));

        // Perform add_rows operation
        matrix.add_rows(mpq(2), 0, 1); // row 1 = row 1 + 2 * row 0

        // Verify the results
        SASSERT(matrix.get_elem(1, 0) == 5); // 3 + 2*1
        SASSERT(matrix.get_elem(1, 1) == 4); // 0 + 2*2
        SASSERT(matrix.get_elem(1, 2) == 4); // unchanged

        matrix.add_rows(mpq(-2), 0, 1);
        SASSERT(matrix.get_elem(1, 0) == 3); // 5 - 2*1
        SASSERT(matrix.get_elem(1, 1) == 0); // 4 - 2*2
        SASSERT(matrix.get_elem(1, 2) == 4); // unchanged
    }
    
void test_nla_order_lemma() { nla::test_order_lemma(); }

void test_lp_local(int argn, char **argv) {
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
    if (args_parser.option_is_used("-add_rows")) {
        test_add_rows();
        return finalize(0);
    }
    if (args_parser.option_is_used("-monics")) {
        nla::test_monics();
        return finalize(0);
    }

    if (args_parser.option_is_used("--patching")) {
        test_patching();
        return finalize(0);
    }
    if (args_parser.option_is_used("-nla_cn")) {
#ifdef Z3DEBUG
        nla::test_cn();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_sim")) {
#ifdef Z3DEBUG
        nla::test_simplify();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nex_order")) {
        nla::test_nex_order();
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_order")) {
#ifdef Z3DEBUG
        test_nla_order_lemma();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_monot")) {
#ifdef Z3DEBUG
        nla::test_monotone_lemma();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_bsl")) {
#ifdef Z3DEBUG
        nla::test_basic_sign_lemma();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_horner")) {
#ifdef Z3DEBUG
        nla::test_horner();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_tan")) {
#ifdef Z3DEBUG
        nla::test_tangent_lemma();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_blfmz_mf")) {
#ifdef Z3DEBUG
        nla::test_basic_lemma_for_mon_zero_from_monomial_to_factors();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_blfmz_fm")) {
#ifdef Z3DEBUG
        nla::test_basic_lemma_for_mon_zero_from_factors_to_monomial();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_blnt_mf")) {
#ifdef Z3DEBUG
        nla::test_basic_lemma_for_mon_neutral_from_monomial_to_factors();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-nla_blnt_fm")) {
#ifdef Z3DEBUG
        nla::test_basic_lemma_for_mon_neutral_from_factors_to_monomial();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-hnf")) {
#ifdef Z3DEBUG
        test_hnf();
#endif
        return finalize(0);
    }

    if (args_parser.option_is_used("-gomory")) {
        test_gomory_cut();
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

    return finalize(0);  // has_violations() ? 1 : 0);
}
}  // namespace lp
void tst_lp(char **argv, int argc, int &i) {
    lp::test_lp_local(argc - 2, argv + 2);
}
// clang-format on
bool coprime(int a, int b) {
    return gcd(rational(a), rational(b)).is_one();
}
bool coprime(rational &a, rational &b) {
    return gcd(a, b).is_one();
}
void asserts_on_patching(const rational &x, const rational &alpha) {
    auto a1 = numerator(alpha);
    auto a2 = denominator(alpha);
    auto x1 = numerator(x);
    auto x2 = denominator(x);
    SASSERT(a1.is_pos());
    SASSERT(abs(a1) < abs(a2));
    SASSERT(coprime(a1, a2));
    SASSERT(x1.is_pos());
    SASSERT(x1 < x2);
    SASSERT(coprime(x1, x2));
    SASSERT((a2 / x2).is_int());
}
void get_patching_deltas(const rational &x, const rational &alpha, rational &delta_0, rational &delta_1) {
    std::cout << "get_patching_deltas(" << x << ", " << alpha << ")" << std::endl;
    auto a1 = numerator(alpha);
    auto a2 = denominator(alpha);
    auto x1 = numerator(x);
    auto x2 = denominator(x);
    SASSERT(divides(x2, a2));
    // delta has to be integral.
    // We need to find delta such that x1/x2 + (a1/a2)*delta is integral.
    // Then a2*x1/x2 + a1*delta is integral, that means that t = a2/x2 is integral.
    // We established that a2 = x2*t
    // Then x1 + a1*delta*(x2/a2)  = x1 + a1*(delta/t)  is integral. Taking into account
    // that t and a1 are coprime we have delta = t*k, where k is an integer.
    rational t = a2 / x2;
    std::cout << "t = " << t << std::endl;
    // Now we have x1/x2 + (a1/x2)*k is integral, or (x1 + a1*k)/x2 is integral.
    // It is equivalent to x1 + a1*k = x2*m, where m is an integer
    // We know that a2 and a1 are coprime, and x2 divides a2, so x2 and a1 are coprime.
    rational u, v;
    auto g = gcd(a1, x2, u, v);
    SASSERT(g.is_one() && u.is_int() && v.is_int() && g == u * a1 + v * x2);
    std::cout << "u = " << u << ", v = " << v << std::endl;
    std::cout << "x= " << (x1 / x2) << std::endl;
    std::cout << "x + (a1 / a2) * (-u * t) * x1 = " << x + (a1 / a2) * (-u * t) * x1 << std::endl;
    SASSERT((x + (a1 / a2) * (-u * t) * x1).is_int());
    // 1 = (u- l*x2 ) * a1 + (v + l*a1)*x2, for every integer l.
    rational d = u * t * x1;
    delta_0 = mod(d, a2);
    SASSERT(delta_0 > 0);
    delta_1 = delta_0 - a2;
    SASSERT(delta_1 < 0);
    std::cout << "delta_0 = " << delta_0 << std::endl;
    std::cout << "delta_1 = " << delta_1 << std::endl;
}

void try_find_smaller_delta(const rational &x, const rational &alpha, rational &delta_0, rational &delta_1) {
    auto a1 = numerator(alpha);
    auto a2 = denominator(alpha);
    auto x1 = numerator(x);
    auto x2 = denominator(x);
    rational delta_minus, delta_plus;
    auto del_min = delta_0 < delta_1 ? delta_0 : delta_1;
    auto del_plus = delta_0 < delta_1 ? delta_1 : delta_0;
    for (auto i = del_min + rational(1); i < del_plus; i += 1) {
        if ((x - alpha * i).is_int()) {
            std::cout << "found smaller delta = " << i << std::endl;
            std::cout << "i - del_min = " << i - del_min << std::endl;
            std::cout << "x - alpha*i = " << x - alpha * i << std::endl;
        }
    }
}

void test_patching_alpha(const rational &x, const rational &alpha) {
    std::cout << "\nstart patching x = " << x << ", alpha = " << alpha << "\n";
    asserts_on_patching(x, alpha);
    rational delta_0, delta_1;
    get_patching_deltas(x, alpha, delta_0, delta_1);

    SASSERT(delta_0 * delta_1 < 0);

    SASSERT((x - alpha * delta_0).is_int());
    SASSERT((x - alpha * delta_1).is_int());
    try_find_smaller_delta(x, alpha, delta_0, delta_1);
    // std::cout << "delta_minus = " << delta_minus << ", delta_1 = " << delta_1 << "\n";
    // std::cout << "x + alpha*delta_minus = " << x + alpha * delta_minus << "\n";
    // std::cout << "x + alpha*delta_1 = " << x + alpha * delta_1 << "\n";
}

void find_a1_x1_x2_and_fix_a2(int &x1, int &x2, int &a1, int &a2) {
    x2 = (rand() % a2) + (int)(a2 / 3);
    auto g = gcd(rational(a2), rational(x2));
    a2 *= (x2 / numerator(g).get_int32());
    SASSERT(rational(a2, x2).is_int());
    do {
        x1 = rand() % (unsigned)x2 + 1;
    } while (!coprime(x1, x2));

    do {
        a1 = rand() % (unsigned)a2 + 1;
    } while (!coprime(a1, a2));
}


void test_patching() {
    srand(1);
    // repeat the test 100 times

    int range = 40;
    for (int i = 0; i < 100; i++) {
        int a1;
        int a2 = std::max((int)rand() % range, (int)range / 3);

        int x1, x2;
        find_a1_x1_x2_and_fix_a2(x1, x2, a1, a2);

        test_patching_alpha(rational(x1, x2), rational(a1, a2));
    }
}
