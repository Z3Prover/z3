/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include <utility>
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include "math/lp/monic.h"
#include "math/lp/gomory.h"
#include "math/lp/int_branch.h"
#include "math/lp/int_cube.h"

namespace lp {

int_solver::patcher::patcher(int_solver& lia): 
    lia(lia), 
    lra(lia.lra),
    lrac(lia.lrac),
    m_num_nbasic_patches(0),
    m_patch_cost(0),
    m_next_patch(0),
    m_delay(0)
{}
    
bool int_solver::patcher::should_apply() {
#if 1
    return true;
#else
    if (m_delay == 0) {
        return true;
    }
    --m_delay;
    return false;
#endif
}
    
lia_move int_solver::patcher::operator()() {
    return patch_nbasic_columns();
}

lia_move int_solver::patcher::patch_nbasic_columns() {
    lia.settings().stats().m_patches++;
    lp_assert(lia.is_feasible());
    m_num_nbasic_patches = 0;
    m_patch_cost = 0;
    for (unsigned j : lia.lrac.m_r_nbasis) {
        patch_nbasic_column(j);
    }
    lp_assert(lia.is_feasible());
    if (!lia.has_inf_int()) {
        lia.settings().stats().m_patches_success++;
        m_delay = 0;
        m_next_patch = 0;
        return lia_move::sat;
    }
    if (m_patch_cost > 0 && m_num_nbasic_patches * 10 < m_patch_cost) {
        m_delay = std::min(20u, m_next_patch++);
    }
    else {
        m_delay = 0;
        m_next_patch = 0;
    }
    return lia_move::undef;
}

void int_solver::patcher::patch_nbasic_column(unsigned j) {
    impq & val = lrac.m_r_x[j];
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    bool has_free = lia.get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m);    
    m_patch_cost += lra.A_r().number_of_non_zeroes_in_column(j);
    if (!has_free) {
        return;
    }
    bool m_is_one = m.is_one();
    bool val_is_int = lia.value_is_int(j);

    // check whether value of j is already a multiple of m.
    if (val_is_int && (m_is_one || (val.x / m).is_int())) {
        return;
    }
    TRACE("patch_int",
          tout << "TARGET j" << j << " -> [";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << ", ";
          if (inf_u) tout << "oo"; else tout << u;
          tout << "]";
          tout << ", m: " << m << ", val: " << val << ", is_int: " << lra.column_is_int(j) << "\n";);
    if (!inf_l) {
        l = impq(m_is_one ? ceil(l) : m * ceil(l / m));
        if (inf_u || l <= u) {
            TRACE("patch_int",    tout << "patching with l: " << l << '\n';);
            lra.set_value_for_nbasic_column(j, l);
        }
        else {
            --m_num_nbasic_patches;
            TRACE("patch_int", tout << "not patching " << l << "\n";);
        }
    }
    else if (!inf_u) {
        u = impq(m_is_one ? floor(u) : m * floor(u / m));
        lra.set_value_for_nbasic_column(j, u);
        TRACE("patch_int", tout << "patching with u: " << u << '\n';);
    }
    else {
        lra.set_value_for_nbasic_column(j, impq(0));
        TRACE("patch_int", tout << "patching with 0\n";);
    }
    ++m_num_nbasic_patches;
}    

int_solver::int_solver(lar_solver& lar_slv) :
    lra(lar_slv),
    lrac(lra.m_mpq_lar_core_solver),
    m_gcd(*this),
    m_patcher(*this),
    m_number_of_calls(0),
    m_hnf_cutter(*this),
    m_hnf_cut_period(settings().hnf_cut_period()) {
    lra.set_int_solver(this);
}

// this will allow to enable and disable tracking of the pivot rows
struct check_return_helper {
    lar_solver&      lra;
    lar_core_solver& lrac;
    bool             m_track_pivoted_rows;
    check_return_helper(lar_solver& ls) :
        lra(ls),
        lrac(ls.m_mpq_lar_core_solver),
        m_track_pivoted_rows(lra.get_track_pivoted_rows()) {
        TRACE("pivoted_rows", tout << "pivoted rows = " << lrac.m_r_solver.m_pivoted_rows->size() << std::endl;);
        lra.set_track_pivoted_rows(false);
    }
    ~check_return_helper() {
        TRACE("pivoted_rows", tout << "pivoted rows = " << lrac.m_r_solver.m_pivoted_rows->size() << std::endl;);
        lra.set_track_pivoted_rows(m_track_pivoted_rows);
    }
};

lia_move int_solver::check(lp::explanation * e) {
    SASSERT(lra.ax_is_correct());
    if (!has_inf_int()) return lia_move::sat;

    m_t.clear();
    m_k.reset();
    m_ex = e;
    m_ex->clear();
    m_upper = false;
    lia_move r = lia_move::undef;

    gomory       gc(*this);
    int_cube     cube(*this);
    int_branch   branch(*this);

    if (m_gcd.should_apply()) r = m_gcd();

    check_return_helper pc(lra);

    if (settings().m_int_pivot_fixed_vars_from_basis)
        lra.pivot_fixed_vars_from_basis();

    ++m_number_of_calls;
    if (r == lia_move::undef && m_patcher.should_apply()) r = m_patcher();
    if (r == lia_move::undef && should_find_cube()) r = cube();
    if (r == lia_move::undef && should_hnf_cut()) r = hnf_cut();
    if (r == lia_move::undef && should_gomory_cut()) r = gc();
    if (r == lia_move::undef) r = branch();
    return r;
}

std::ostream& int_solver::display_inf_rows(std::ostream& out) const {
    unsigned num = lra.A_r().column_count();
    for (unsigned v = 0; v < num; v++) {
        if (column_is_int(v) && !get_value(v).is_int()) {
            display_column(out, v);
        }
    }
    
    num = 0;
    for (unsigned i = 0; i < lra.A_r().row_count(); i++) {
        unsigned j = lrac.m_r_basis[i];
        if (column_is_int_inf(j)) {
            num++;
            lra.print_row(lra.A_r().m_rows[i], out);
            out << "\n";
        }
    }
    out << "num of int infeasible: " << num << "\n";
    return out;
}

bool int_solver::current_solution_is_inf_on_cut() const {
    const auto & x = lrac.m_r_x;
    impq v = m_t.apply(x);
    mpq sign = m_upper ? one_of_type<mpq>()  : -one_of_type<mpq>();
    CTRACE("current_solution_is_inf_on_cut", v * sign <= impq(m_k) * sign,
           tout << "m_upper = " << m_upper << std::endl;
           tout << "v = " << v << ", k = " << m_k << std::endl;
          );
    return v * sign > impq(m_k) * sign;
}

bool int_solver::has_inf_int() const {
    return lra.has_inf_int();
}

constraint_index int_solver::column_upper_bound_constraint(unsigned j) const {
    return lra.get_column_upper_bound_witness(j);
}

constraint_index int_solver::column_lower_bound_constraint(unsigned j) const {
    return lra.get_column_lower_bound_witness(j);
}

unsigned int_solver::row_of_basic_column(unsigned j) const {
    return lra.row_of_basic_column(j);
}

lp_settings& int_solver::settings() {  
    return lra.settings(); 
}

const lp_settings& int_solver::settings() const { 
    return lra.settings(); 
}

bool int_solver::column_is_int(unsigned j) const {
    return lra.column_is_int(j);
}

bool int_solver::is_real(unsigned j) const {
    return !column_is_int(j);
}

bool int_solver::value_is_int(unsigned j) const {
    return lra.column_value_is_int(j);
}    

unsigned int_solver::random() {
    return settings().random_next();
}

const impq& int_solver::upper_bound(unsigned j) const {
    return lra.column_upper_bound(j);
}

const impq& int_solver::lower_bound(unsigned j) const {
    return lra.column_lower_bound(j);
}

bool int_solver::is_term(unsigned j) const {
    return lra.column_corresponds_to_term(j);
}

unsigned int_solver::column_count() const  { 
    return lra.column_count(); 
}

bool int_solver::should_find_cube() {
    return m_number_of_calls % settings().m_int_find_cube_period == 0;
}


bool int_solver::should_gomory_cut() {
    return m_number_of_calls % settings().m_int_gomory_cut_period == 0;
}

bool int_solver::should_hnf_cut() {
    return settings().m_enable_hnf && m_number_of_calls % m_hnf_cut_period == 0;
}

lia_move int_solver::hnf_cut() {
    lia_move r = m_hnf_cutter.make_hnf_cut();
    if (r == lia_move::undef) {
        m_hnf_cut_period *= 2;
    }
    else {
        m_hnf_cut_period = settings().hnf_cut_period();
    }
    return r;
}

void int_solver::set_value_for_nbasic_column_ignore_old_values(unsigned j, const impq & new_val) {
    lp_assert(!is_base(j));
    auto & x = lrac.m_r_x[j];
    auto delta = new_val - x;
    x = new_val;
    TRACE("int_solver", tout << "x[" << j << "] = " << x << "\n";);
    lra.change_basic_columns_dependend_on_a_given_nb_column(j, delta);
}





bool int_solver::has_lower(unsigned j) const {
    switch (lrac.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::lower_bound:
        return true;
    default:
        return false;
    }
}

bool int_solver::has_upper(unsigned j) const {
    switch (lrac.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return true;
    default:
        return false;
    }
}

static void set_lower(impq & l, bool & inf_l, impq const & v ) {
    if (inf_l || v > l) {
        l = v;
        inf_l = false;
    }
}

static void set_upper(impq & u, bool & inf_u, impq const & v) {
    if (inf_u || v < u) {
        u = v;
        inf_u = false;
    }
}

bool int_solver::get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m) {
    if (lrac.m_r_heading[j] >= 0) // the basic var 
        return false;

    TRACE("random_update", display_column(tout, j) << ", is_int = " << column_is_int(j) << "\n";);
    impq const & xj = get_value(j);
    
    inf_l = true;
    inf_u = true;
    l = u = zero_of_type<impq>();
    m = mpq(1);

    if (has_lower(j)) {
        set_lower(l, inf_l, lower_bound(j) - xj);
    }
    if (has_upper(j)) {
        set_upper(u, inf_u, upper_bound(j) - xj);
    }

    unsigned row_index;
    lp_assert(settings().use_tableau());
    const auto & A = lra.A_r();
    unsigned rounds = 0;
    for (const auto &c : A.column(j)) {
        row_index = c.var();
        const mpq & a = c.coeff();        
        unsigned i = lrac.m_r_basis[row_index];
        TRACE("random_update", tout << "i = " << i << ", a = " << a << "\n";); 
        if (column_is_int(i) && !a.is_int())
            m = lcm(m, denominator(a));
    }
    TRACE("random_update", tout <<  "m = " << m << "\n";);
    
    for (const auto &c : A.column(j)) {
        if (!inf_l && !inf_u && l >= u) break;       
        row_index = c.var();
        const mpq & a = c.coeff();        
        unsigned i = lrac.m_r_basis[row_index];
        impq const & xi = get_value(i);

#define SET_BOUND(_fn_, a, b, x, y, z)                                  \
        if (x.is_one())                                                 \
            _fn_(a, b, y - z);                                          \
        else if (x.is_minus_one())                                      \
            _fn_(a, b, z - y);                                          \
        else if (z == y)                                                \
            _fn_(a, b, zero_of_type<impq>());                           \
        else                                                            \
            {  _fn_(a, b, (y - z)/x);  }   \

        
        if (a.is_neg()) {
            if (has_lower(i)) {
                SET_BOUND(set_lower, l, inf_l, a, xi, lrac.m_r_lower_bounds()[i]);
            }
            if (has_upper(i)) {
                SET_BOUND(set_upper, u, inf_u, a, xi, lrac.m_r_upper_bounds()[i]);
            }
        }
        else {
            if (has_upper(i)) {
                SET_BOUND(set_lower, l, inf_l, a, xi, lrac.m_r_upper_bounds()[i]);
            }
            if (has_lower(i)) {
                SET_BOUND(set_upper, u, inf_u, a, xi, lrac.m_r_lower_bounds()[i]);
            }
        }
        ++rounds;
    }

    l += xj;
    u += xj;

    TRACE("freedom_interval",
          tout << "freedom variable for:\n";
          tout << lra.get_variable_name(j);
          tout << "[";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << "; ";
          if (inf_u) tout << "oo";  else tout << u;
          tout << "]\n";
          tout << "val = " << get_value(j) << "\n";
          tout << "return " << (inf_l || inf_u || l <= u);
          );
    return (inf_l || inf_u || l <= u);
}


bool int_solver::is_feasible() const {
    lp_assert(
        lrac.m_r_solver.calc_current_x_is_feasible_include_non_basis() ==
        lrac.m_r_solver.current_x_is_feasible());
    return lrac.m_r_solver.current_x_is_feasible();
}

const impq & int_solver::get_value(unsigned j) const {
    return lrac.m_r_x[j];
}

std::ostream& int_solver::display_column(std::ostream & out, unsigned j) const {
    return lrac.m_r_solver.print_column_info(j, out);
    return out;
}

bool int_solver::column_is_int_inf(unsigned j) const {
    return column_is_int(j) && (!value_is_int(j));
}

bool int_solver::is_base(unsigned j) const {
    return lrac.m_r_heading[j] >= 0;
}

bool int_solver::is_boxed(unsigned j) const {
    return lrac.m_column_types[j] == column_type::boxed;
}

bool int_solver::is_fixed(unsigned j) const {
    return lrac.m_column_types[j] == column_type::fixed;
}

bool int_solver::is_free(unsigned j) const {
    return lrac.m_column_types[j] == column_type::free_column;
}

bool int_solver::at_bound(unsigned j) const {
    auto & mpq_solver = lrac.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
        return
            mpq_solver.m_lower_bounds[j] == get_value(j) ||
            mpq_solver.m_upper_bounds[j] == get_value(j);
    case column_type::lower_bound:
        return mpq_solver.m_lower_bounds[j] == get_value(j);
    case column_type::upper_bound:
        return  mpq_solver.m_upper_bounds[j] == get_value(j);
    default:
        return false;
    }
}

bool int_solver::at_lower(unsigned j) const {
    auto & mpq_solver = lrac.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::lower_bound:
        return mpq_solver.m_lower_bounds[j] == get_value(j);
    default:
        return false;
    }
}

bool int_solver::at_upper(unsigned j) const {
    auto & mpq_solver = lrac.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return mpq_solver.m_upper_bounds[j] == get_value(j);
    default:
        return false;
    }
}

void int_solver::display_row_info(std::ostream & out, unsigned row_index) const  {
    auto & rslv = lrac.m_r_solver;
    for (const auto &c: rslv.m_A.m_rows[row_index]) {
        if (numeric_traits<mpq>::is_pos(c.coeff()))
            out << "+";
        out << c.coeff() << rslv.column_name(c.var()) << " ";
    }

    for (const auto& c: rslv.m_A.m_rows[row_index]) {
        rslv.print_column_bound_info(c.var(), out);
    }
    rslv.print_column_bound_info(rslv.m_basis[row_index], out);
}

bool int_solver::shift_var(unsigned j, unsigned range) {
    if (is_fixed(j) || is_base(j))
        return false;
       
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m);
    const impq & x = get_value(j);
    // x, the value of j column, might be shifted on a multiple of m
    if (inf_l && inf_u) {
        impq new_val = m * impq(random() % (range + 1)) + x;
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (column_is_int(j)) {
        if (!inf_l) {
            l = impq(ceil(l));
        }
        if (!inf_u) {
            u = impq(floor(u));
        }
    }
    if (!inf_l && !inf_u && l >= u)
        return false;

    if (inf_u) {
        SASSERT(!inf_l);
        impq new_val = x + m * impq(random() % (range + 1));
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }

    if (inf_l) {
        SASSERT(!inf_u);
        impq new_val = x - m * impq(random() % (range + 1));
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }

    SASSERT(!inf_l && !inf_u);
    // The shift has to be a multiple of m: let us look for s, such that the shift is m*s.
    // We have new_val = x+m*s <= u, so m*s <= u-x and, finally, s <= floor((u- x)/m) = a
    // The symmetric reasoning gives us s >= ceil((l-x)/m) = b
    // We randomly pick s in the segment [b, a]
    mpq a = floor((u - x) / m);
    mpq b = ceil((l - x) / m);
    mpq r = a - b;
    if (!r.is_pos())
        return false;
    TRACE("int_solver", tout << "a = " << a << ", b = " << b << ", r = " << r<< ", m = " << m << "\n";);
    if (r < mpq(range))
        range = static_cast<unsigned>(r.get_uint64());
    
    mpq s = b + mpq(random() % (range + 1));
    impq new_val = x + m * impq(s);
    TRACE("int_solver", tout << "new_val = " << new_val << "\n";);
    SASSERT(l <= new_val && new_val <= u);
    set_value_for_nbasic_column_ignore_old_values(j, new_val);
    return true;
}

// not used:
bool int_solver::non_basic_columns_are_at_bounds() const {
    for (unsigned j : lrac.m_r_nbasis) {
        auto & val = lrac.m_r_x[j];
        switch (lrac.m_column_types()[j]) {
        case column_type::boxed:
            if (val != lrac.m_r_lower_bounds()[j] && val != lrac.m_r_upper_bounds()[j])
                return false;
            break;
        case column_type::lower_bound:
            if (val != lrac.m_r_lower_bounds()[j])
                return false;
            break;
        case column_type::upper_bound:
            if (val != lrac.m_r_upper_bounds()[j])
                return false;
            break;
        default:
            if (column_is_int(j) && !val.is_int()) {
                return false;
            }
        }
    }
    return true;
}

}
