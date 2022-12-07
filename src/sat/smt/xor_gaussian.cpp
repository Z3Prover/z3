/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    xor_gaussian.cpp

Abstract:

    A roughly 1:1 port of CryptoMiniSAT's gaussian elimination datastructures/algorithms

--*/


#include <algorithm>
#include <iomanip>
#include <iostream>
#include <set>
#include <iterator>

#include "sat/smt/xor_solver.h"

using std::ostream;
using std::set;

using namespace xr;

///returns popcnt
unsigned PackedRow::population_cnt(
    literal_vector &tmp_clause,
    const unsigned_vector& column_to_var,
    const bool_vector &var_has_resp_row,
    unsigned& non_resp_var) {
    
    unsigned popcnt = 0;
    non_resp_var = UINT_MAX;
    tmp_clause.clear();

    for (int i = 0; i < size * 64; i++) {
        if ((*this)[i]) {
            popcnt++;
            bool_var v = column_to_var[i];
            tmp_clause.push_back(literal(v, false));

            if (!var_has_resp_row[v])
                non_resp_var = v;
            else
                std::swap(tmp_clause[0], tmp_clause.back());
        }
    }
    SASSERT(tmp_clause.size() == popcnt);
    SASSERT(popcnt == 0 || var_has_resp_row[tmp_clause[0].var()]) ;
    return popcnt;
}

// Gets the reason why the literal "prop" was propagated
void PackedRow::get_reason(literal_vector& antecedents, const unsigned_vector& column_to_var, PackedRow& cols_vals, PackedRow& tmp_col2, literal prop) {

    tmp_col2.set_and(*this, cols_vals);
    for (int i = 0; i < size; i++) {
        if (!mp[i])
            continue;
        int64_t tmp = mp[i];
        int at;
        at = scan_fwd_64b(tmp);
        int extra = 0;
        while (at != 0) {
            unsigned col = extra + (at - 1) + i * 64;
            SASSERT((*this)[col] == 1);
            unsigned var = column_to_var[col];
            if (var == prop.var()) {
                antecedents.push_back(prop); 
                std::swap(antecedents[0], antecedents.back());
            }
            else 
                antecedents.push_back(literal(var, !tmp_col2[col]));

            extra += at;
            if (extra == 64)
                break;

            tmp >>= at;
            at = scan_fwd_64b(tmp);
        }
    }
}

gret PackedRow::propGause(
    const unsigned_vector& column_to_var,
    bool_vector &var_has_resp_row,
    unsigned& new_resp_var,
    PackedRow& tmp_col,
    PackedRow& tmp_col2,
    PackedRow& cols_vals,
    PackedRow& cols_unset,
    literal& ret_lit_prop) {
    
    unsigned pop = tmp_col.set_and_until_popcnt_atleast2(*this, cols_unset);
    
    // There are still at least 2 unassigned elements in the matrix row
    // Find new watch ==> a variable not yet having a row responsible for it
    if (pop >= 2) {
        for (int i = 0; i < size; i++) {
            if (!tmp_col.mp[i]) 
                continue;
            int64_t tmp = tmp_col.mp[i];
            int at;
            at = scan_fwd_64b(tmp);
            int extra = 0;
            while (at != 0) {
                unsigned col = extra + (at - 1) + i * 64;
                unsigned var = column_to_var[col];
                // found new non-basic variable, let's watch it
                if (!var_has_resp_row[var]) {
                    new_resp_var = var;
                    return gret::nothing_fnewwatch;
                }
    
                extra += at;
                if (extra == 64)
                    break;
    
                tmp >>= at;
                at = scan_fwd_64b(tmp);
            }
        }
    }

    // Calc value of row by bitwise-anding the current model and the row
    tmp_col2.set_and(*this, cols_vals);
    unsigned pop_t = tmp_col2.popcnt() + (unsigned)rhs();

    SASSERT(pop == 1 || pop == 0);

    if (pop == 0) {
        if (pop_t % 2 == 0)
            return gret::nothing_satisfied;
        else
            return gret::confl;
    }

    for (int i = 0; i < size; i++) { 
        if (!tmp_col.mp[i])
            continue;
        
        int at = scan_fwd_64b(tmp_col.mp[i]);
        
        // found prop
        unsigned col = (at - 1) + i * 64;
        SASSERT(tmp_col[col] == 1);
        unsigned var = column_to_var[col];
        ret_lit_prop = literal(var, !(pop_t % 2));
        return gret::prop;
    }

    UNREACHABLE();
    return gret::nothing_satisfied;
}

EGaussian::EGaussian(xr::solver& _solver, unsigned _matrix_no, const vector<xor_clause>& _xorclauses) : 
    m_xorclauses(_xorclauses), m_solver(_solver), matrix_no(_matrix_no) { }

EGaussian::~EGaussian() {
    delete_gauss_watch_this_matrix();
    for (auto& x: tofree) 
        memory::deallocate(x);
    tofree.clear();

    delete cols_unset;
    delete cols_vals;
    delete tmp_col;
    delete tmp_col2;
}

struct ColSorter {
    sat::solver* m_solver;
    explicit ColSorter(sat::solver* _solver) : m_solver(_solver) { }
    // a < b
    bool operator()(bool_var a, bool_var b) {
        return !m_solver->is_assumption(a) && m_solver->is_assumption(b);
    }
};

// Populates the mapping from variables to columns and vice-versa
// The order has assumption variables at the end (otw. probably ordered by index)
void EGaussian::select_column_order() {
    m_var_to_column.clear();
    m_var_to_column.resize(m_solver.s().num_vars(), UINT32_MAX);
    bool_var_vector vars_needed;
    unsigned largest_used_var = 0;

    for (const xor_clause& x : m_xorclauses) {
        for (bool_var v : x) {
            SASSERT(m_solver.s().value(v) == l_undef);
            if (m_var_to_column[v] == UINT32_MAX) {
                vars_needed.push_back(v);
                m_var_to_column[v] = UINT32_MAX - 1;
                largest_used_var = std::max(largest_used_var, v);
            }
        }
    }

    if (vars_needed.size() >= UINT32_MAX / 2 - 1) 
        throw default_exception("Matrix has too many rows");
    
    if (m_xorclauses.size() >= UINT32_MAX / 2 - 1) 
        throw default_exception("Matrix has too many rows");
    
    m_var_to_column.resize(largest_used_var + 1);


    // Sort assumption variables to the end
    ColSorter c(&m_solver.s());
    std::sort(vars_needed.begin(), vars_needed.end(), c);

    m_column_to_var.clear();
    for (bool_var v : vars_needed) {
        SASSERT(m_var_to_column[v] == UINT32_MAX - 1);
        m_var_to_column[v] = m_column_to_var.size();
        m_column_to_var.push_back(v);
    }

    // for the ones that were not in the order_heap, but are marked in var_to_col
    for (unsigned v = 0; v < m_var_to_column.size(); v++) {
        if (m_var_to_column[v] == UINT32_MAX - 1) {
            m_var_to_column[v] = m_column_to_var.size();
            m_column_to_var.push_back(v);
        }
    }
}

// Sets up some of the required datastructures to apply initial elimination (e.g., like the matrix itself and an empty list of gaussian watchlist)
void EGaussian::fill_matrix() {
    m_var_to_column.clear();

    // decide which variable in matrix column and the number of rows
    select_column_order();
    m_num_rows = m_xorclauses.size();
    m_num_cols = m_column_to_var.size();
    if (m_num_rows == 0 || m_num_cols == 0)
        return;
    
    m_mat.resize(m_num_rows, m_num_cols); // initial gaussian matrix

    for (unsigned row = 0; row < m_num_rows; row++) {
        const xor_clause& c = m_xorclauses[row];
        m_mat[row].set(c, m_var_to_column, m_num_cols);
        char_vector line;
        line.resize(m_num_rows, 0);
        line[row] = 1;
    }

    // reset
    var_has_resp_row.clear();
    var_has_resp_row.resize(m_solver.s().num_vars(), 0);
    row_to_var_non_resp.clear();

    delete_gauss_watch_this_matrix();

    //reset satisfied_xor state
    SASSERT(m_solver.s().at_search_lvl());
    satisfied_xors.clear();
    satisfied_xors.resize(m_num_rows, false);
}

// deletes all gaussian watches from the matrix for all variables
void EGaussian::delete_gauss_watch_this_matrix() {
    for (unsigned i = 0; i < m_solver.m_gwatches.size(); i++) 
        clear_gwatches(i);    
}

// deletes all gaussian watches from the matrix for the given variable
void EGaussian::clear_gwatches(bool_var var) {
    //if there is only one matrix, don't check, just empty it
    if (m_solver.m_gmatrices.empty()) {
        m_solver.m_gwatches[var].clear();
        return;
    }
    
    unsigned j = 0;
    for (auto& w : m_solver.m_gwatches[var]) 
        if (w.matrix_num != matrix_no) 
            m_solver.m_gwatches[var][j++] = w;

    m_solver.m_gwatches[var].shrink(j);
}

// Simplify matrix by applying gaussian elimination
// This is only done at search level. We therefore can safely remove/replace "redundant" xor-clauses by unit/binary-clauses
// Furthermore, initializes additional datastructures (e.g., for doing variable lookup)
bool EGaussian::full_init(bool& created) {
    SASSERT(!inconsistent());
    SASSERT(m_solver.s().at_search_lvl());
    SASSERT(initialized == false);
    created = true;

    unsigned trail_before;
    do {
        trail_before = m_solver.s().trail_size();
        m_solver.clean_xor_clauses(m_xorclauses);

        fill_matrix();

        if (m_num_rows == 0 || m_num_cols == 0) {
            created = false;
            return !inconsistent();
        }

        eliminate();

        // find some row already true false, and insert watch list
        gret ret = init_adjust_matrix();

        switch (ret) {
            case gret::confl:
                return false;
            case gret::prop:
                m_solver.s().propagate(false);
                if (inconsistent()) {
                    TRACE("xor", tout << "eliminate & adjust matrix during init lead to UNSAT\n";);
                    return false;
                }
                break;
            default:
                break;
        }

    } while (m_solver.s().trail_size() != trail_before); // Exit if nothing new happened

    DEBUG_CODE(check_watchlist_sanity(););
    TRACE("xor", tout << "initialised matrix " << matrix_no << "\n");

    xor_reasons.resize(m_num_rows);
    unsigned num_64b = m_num_cols / 64 + (bool)(m_num_cols % 64);
    
    for (auto& x: tofree) 
        memory::deallocate(x);
    
    tofree.clear();

    auto add_packed_row = [&](PackedRow*& p) {
        int64_t* x = (int64_t*)memory::allocate(sizeof(int64_t) * (num_64b + 1));
        tofree.push_back(x);
        dealloc(p);
        p = alloc(PackedRow, num_64b, x);
        p->rhs() = 0;
    };

    add_packed_row(cols_unset);
    add_packed_row(cols_vals);
    add_packed_row(tmp_col);
    add_packed_row(tmp_col2);

    initialized = true;
    update_cols_vals_set(true);
    DEBUG_CODE(check_invariants(););
    
    return !inconsistent();
}

std::ostream& PackedMatrix::display_dense(std::ostream& out) const {
    for (unsigned rowIdx = 0; rowIdx < num_rows(); rowIdx++) {
        const PackedRow& row = (*this)[rowIdx];
        for(int i = 0; i < row.get_size() * 64; i++) 
            out << (int)row[i];
        out << " -- rhs: " << row.rhs() << " -- row: " << rowIdx << "\n";
    }
    return out;
}

std::ostream& PackedMatrix::display_sparse(std::ostream& out) const {
    for (auto const& row : *this) {
        bool first = true;
        for (int i = 0; i < row.get_size() * 64; ++i) {
            if (row[i]) {
                if (first && row.rhs())
                    out << -i-1 << " ";
                else
                    out << i+1 << " ";
                first = false;
            }
        }
        out << "\n";
    }
    return out;
}


// Applies Gaussian-Jordan elimination (search level). This function does not add conflicts/propagate/... Just reduces the matrix
void EGaussian::eliminate() {
    SASSERT(m_solver.s().at_search_lvl());
    
    unsigned end_row = m_num_rows;
    unsigned row_i = 0;
    unsigned col = 0;

    m_mat.display_dense(std::cout) << std::endl;
    TRACE("xor", m_mat.display_dense(tout) << "\n");
    
    // Gauss-Jordan Elimination
    while (row_i != m_num_rows && col != m_num_cols) {
        unsigned row_with_1_in_col = row_i;
        unsigned row_with_1_in_col_n = row_i;

        // Find first "1" in column.
        for (; row_with_1_in_col < end_row; row_with_1_in_col++, row_with_1_in_col_n++) {
            if (m_mat[row_with_1_in_col][col])
                break;            
        }

        // We have found a "1" in this column
        if (row_with_1_in_col < end_row) {
            var_has_resp_row[m_column_to_var[col]] = true;

            // swap row row_with_1_in_col and rowIt
            if (row_with_1_in_col != row_i)
                m_mat[row_i].swapBoth(m_mat[row_with_1_in_col]);

            // XOR into *all* rows that have a "1" in column COL
            // Since we XOR into *all*, this is Gauss-Jordan (and not just Gauss)
            for (unsigned k_row = 0; k_row < end_row; k_row++) {
                // xor rows K and I
                if (k_row != row_i && m_mat[k_row][col])
                    m_mat[k_row].xor_in(m_mat[row_i]);
            }
            row_i++;
        }
        col++;
        TRACE("xor", m_mat.display_dense(tout) << "\n");
        m_mat.display_dense(std::cout) << "\n";        
    }
    std::cout << "-------------" << std::endl;
}

literal_vector& EGaussian::get_reason(unsigned row, int& out_ID) {
    if (!xor_reasons[row].m_must_recalc) {
        out_ID = xor_reasons[row].m_ID;
        return xor_reasons[row].m_reason;
    }

    // Clean up previous one
    
    literal_vector& to_fill = xor_reasons[row].m_reason;
    to_fill.clear();

    m_mat[row].get_reason(
        to_fill,
        m_column_to_var,
        *cols_vals,
        *tmp_col2,
        xor_reasons[row].m_propagated);
    
    xor_reasons[row].m_must_recalc = false;
    xor_reasons[row].m_ID = out_ID;
    return to_fill;
}

// Creates binary clauses, assigns variables, adds conflicts based on the (reduced) gaussian-matrix. Also sets up the gaussian watchlist
gret EGaussian::init_adjust_matrix() {
    SASSERT(m_solver.s().at_search_lvl());
    SASSERT(row_to_var_non_resp.empty());
    SASSERT(satisfied_xors.size() >= m_num_rows);
    TRACE("xor", tout << "mat[" << matrix_no << "] init adjusting matrix";);

    unsigned row_i = 0;       // row index
    unsigned adjust_zero = 0; //  elimination row
    for (PackedRow row : m_mat) {
        if (row_i >= m_num_rows)
            break;
        unsigned non_resp_var;
        unsigned popcnt = row.population_cnt(tmp_clause, m_column_to_var, var_has_resp_row, non_resp_var);

        switch (popcnt) {

            //Conflict or satisfied
            case 0:
                TRACE("xor", tout << "Empty XOR during init_adjust_matrix, rhs: " << row.rhs() << "\n");
                adjust_zero++;

                // conflict
                if (row.rhs()) {
                    m_solver.s().set_conflict();
                    TRACE("xor", tout << "-> empty clause during init_adjust_matrix";);
                    TRACE("xor", tout << "-> conflict on row: " << row_i;);
                    return gret::confl;
                }
                TRACE("xor", tout << "-> empty on row: " << row_i;);
                TRACE("xor", tout << "-> Satisfied XORs set for row: " << row_i;);
                satisfied_xors[row_i] = true;
                break;

            //Unit (i.e. toplevel unit)
            case 1:
            {
                TRACE("xor", tout << "Unit XOR during init_adjust_matrix, vars: " << tmp_clause;);
                bool xorEqualFalse = !m_mat[row_i].rhs();
                tmp_clause[0] = literal(tmp_clause[0].var(), xorEqualFalse);
                SASSERT(m_solver.s().value(tmp_clause[0].var()) == l_undef);
                
                m_solver.s().assign_scoped(tmp_clause[0]);

                TRACE("xor", tout << "-> UNIT during adjust: " << tmp_clause[0];);
                TRACE("xor", tout << "-> Satisfied XORs set for row: " << row_i;);
                satisfied_xors[row_i] = true;
                SASSERT(check_row_satisfied(row_i));

                //adjusting
                row.setZero(); // reset this row all zero
                row_to_var_non_resp.push_back(UINT32_MAX);
                var_has_resp_row[tmp_clause[0].var()] = false;
                return gret::prop;
            }

            //Binary XOR (i.e. toplevel binary XOR)
            case 2: 
            {
                TRACE("xor", tout << "Binary XOR during init_adjust_matrix, vars: " << tmp_clause;);
                bool xorEqualFalse = !m_mat[row_i].rhs();

                tmp_clause[0] = tmp_clause[0].unsign();
                tmp_clause[1] = tmp_clause[1].unsign();
                
                m_solver.add_xor_clause(tmp_clause, !xorEqualFalse, true);
                TRACE("xor", tout << "-> toplevel bin-xor on row: " << row_i << " cl2: " << tmp_clause;);

                // reset this row all zero, no need for this row
                row.rhs() = 0; // TODO: The RHS is copied by value (unlike the content of the matrix) Bug?
                row.setZero();

                row_to_var_non_resp.push_back(UINT32_MAX); // delete non-basic value in this row
                var_has_resp_row[tmp_clause[0].var()] = false; // delete basic value in this row
                break;
            }

            default: // need to update watch list
                SASSERT(non_resp_var != UINT32_MAX);

                // insert watch list
                TRACE("xor", tout << "-> watch 1: resp var " << tmp_clause[0].var()+1 << " for row " << row_i << "\n";);
                TRACE("xor", tout << "-> watch 2: non-resp var " << non_resp_var+1 << " for row " << row_i << "\n";);
                m_solver.m_gwatches[tmp_clause[0].var()].push_back(
                    gauss_watched(row_i, matrix_no)); // insert basic variable
                m_solver.m_gwatches[non_resp_var].push_back(
                    gauss_watched(row_i, matrix_no)); // insert non-basic variable
                row_to_var_non_resp.push_back(non_resp_var); // record in this row non-basic variable
                break;
        }
        row_i++;
    }
    SASSERT(row_to_var_non_resp.size() == row_i - adjust_zero);

    m_mat.resizeNumRows(row_i - adjust_zero);
    m_num_rows = row_i - adjust_zero;

    return gret::nothing_satisfied;
}

// Delete this row because we have already add to xor clause, nothing to do anymore
void EGaussian::delete_gausswatch(unsigned row_n) {
    // clear nonbasic value watch list
    svector<gauss_watched>& ws_t = m_solver.m_gwatches[row_to_var_non_resp[row_n]];

    for (unsigned i = ws_t.size(); i-- > 0;) {
        if (ws_t[i].row_n == row_n && ws_t[i].matrix_num == matrix_no) {
            ws_t[i] = *ws_t.end();
            ws_t.shrink(1);
            return;
        }
    }
    UNREACHABLE();
}

unsigned EGaussian::get_max_level(const gauss_data& gqd, unsigned row_n) {
    int ID;
    literal_vector& ante = get_reason(row_n, ID);
    unsigned nMaxLevel = gqd.currLevel;
    unsigned nMaxInd = 1;

    for (unsigned i = ante.size(); i-- > 0; ) {
        literal l = ante[i];
        unsigned nLevel = m_solver.s().lvl(l);
        if (nLevel > nMaxLevel) {
            nMaxLevel = nLevel;
            nMaxInd = i;
        }
    }

    //should we??
    if (nMaxInd != 1) 
        std::swap(ante[1], ante[nMaxInd]);
    
    return nMaxLevel;
}

bool EGaussian::find_truths(
    svector<gauss_watched>& ws,
    unsigned& i,
    unsigned& j,
    bool_var var,
    unsigned row_n,
    gauss_data& gqd) {
    
    SASSERT(gqd.status != gauss_res::confl);
    SASSERT(initialized);

    // printf("dd Watch variable : %d  ,  Wathch row num %d    n", p , row_n);

    TRACE("xor", tout 
          << "mat[" << matrix_no << "] find_truths\n"
          << "-> row: " << row_n << "\n"
          << "-> var: " << var+1 << "\n"
          << "-> dec lev:" << m_solver.s().scope_lvl() << "\n");
    SASSERT(row_n < m_num_rows);
    SASSERT(satisfied_xors.size() > row_n);

    // this XOR is already satisfied
    if (satisfied_xors[row_n]) {
        TRACE("xor", tout << "-> xor satisfied as per satisfied_xors[row_n]";);
        SASSERT(check_row_satisfied(row_n));
        ws[j++] = ws[i];
        find_truth_ret_satisfied_precheck++;
        return true;
    }

    // swap resp and non-resp variable
    bool was_resp_var = false;
    if (var_has_resp_row[var] == 1) {
        //var has a responsible row, so THIS row must be it!
        //since if a var has a responsible row, only ONE row can have a 1 there
        was_resp_var = true;
        var_has_resp_row[row_to_var_non_resp[row_n]] = true;
        var_has_resp_row[var] = false;
    }

    unsigned new_resp_var;
    literal ret_lit_prop;
    gret ret = m_mat[row_n].propGause(
        m_column_to_var,
        var_has_resp_row,
        new_resp_var,
        *tmp_col,
        *tmp_col2,
        *cols_vals,
        *cols_unset,
        ret_lit_prop);
    find_truth_called_propgause++;

    switch (ret) {
        case gret::confl: {
            find_truth_ret_confl++;
            ws[j++] = ws[i];

            xor_reasons[row_n].m_must_recalc = true;
            xor_reasons[row_n].m_propagated = sat::null_literal;
            gqd.conflict = m_solver.mk_justification(m_solver.s().scope_lvl(), matrix_no, row_n);
            gqd.status = gauss_res::confl;
            TRACE("xor", tout << "--> conflict\n");
            
            if (was_resp_var) { // recover
                var_has_resp_row[row_to_var_non_resp[row_n]] = false;
                var_has_resp_row[var] = true;
            }

            return false;
        }

        case gret::prop: {
            find_truth_ret_prop++;
            TRACE("xor", tout << "--> propagation";);
            ws[j++] = ws[i];

            xor_reasons[row_n].m_must_recalc = true;
            xor_reasons[row_n].m_propagated = ret_lit_prop;
            SASSERT(m_solver.s().value(ret_lit_prop.var()) == l_undef);
            prop_lit(gqd, row_n, ret_lit_prop);

            update_cols_vals_set(ret_lit_prop);
            gqd.status = gauss_res::prop;

            if (was_resp_var) { // recover
                var_has_resp_row[row_to_var_non_resp[row_n]] = false;
                var_has_resp_row[var] = true;
            }

            TRACE("xor", tout << "--> Satisfied XORs set for row: " << row_n;);
            satisfied_xors[row_n] = true;
            SASSERT(check_row_satisfied(row_n));
            return true;
        }

        // find new watch list
        case gret::nothing_fnewwatch:
            TRACE("xor", tout << "--> found new watch: " << new_resp_var+1;);

            find_truth_ret_fnewwatch++;

            if (was_resp_var) {
                /// clear watchlist, because only one responsible value in watchlist
                SASSERT(new_resp_var != var);
                clear_gwatches(new_resp_var);
                TRACE("xor", tout << "Cleared watchlist for new resp var: " << new_resp_var+1;);
                TRACE("xor", tout << "After clear...";);
            }
            SASSERT(new_resp_var != var);
            DEBUG_CODE(check_row_not_in_watch(new_resp_var, row_n););
            m_solver.m_gwatches[new_resp_var].push_back(gauss_watched(row_n, matrix_no));

            if (was_resp_var) {
                //it was the responsible one, so the newly watched var
                //is the new column it's responsible for
                //so elimination will be needed

                //clear old one, add new resp
                var_has_resp_row[row_to_var_non_resp[row_n]] = false;
                var_has_resp_row[new_resp_var] = true;

                // store the eliminate variable & row
                gqd.new_resp_var = new_resp_var;
                gqd.new_resp_row = row_n;
                if (m_solver.m_gmatrices.size() == 1) {
                    SASSERT(m_solver.m_gwatches[gqd.new_resp_var].size() == 1);
                }
                gqd.do_eliminate = true;
                return true;
            } else {
                row_to_var_non_resp[row_n] = new_resp_var;
                return true;
            }

        // this row already true
        case gret::nothing_satisfied:
            TRACE("xor", tout << "--> satisfied";);

            find_truth_ret_satisfied++;
            ws[j++] = ws[i];
            if (was_resp_var) { // recover
                var_has_resp_row[row_to_var_non_resp[row_n]] = false;
                var_has_resp_row[var] = true;
            }

            TRACE("xor", tout << "--> Satisfied XORs set for row: " << row_n;);
            satisfied_xors[row_n] = true;
            SASSERT(check_row_satisfied(row_n));
            return true;

        //error here
        default:
            UNREACHABLE(); // cannot be here
            return true;
    }

    UNREACHABLE();
    return true;
}

inline void EGaussian::update_cols_vals_set(literal lit) {
    cols_unset->clearBit(m_var_to_column[lit.var()]);
    if (!lit.sign())
        cols_vals->setBit(m_var_to_column[lit.var()]);
}

void EGaussian::update_cols_vals_set(bool force) {
    SASSERT(initialized);

    if (cancelled_since_val_update || force) {
        cols_vals->setZero();
        cols_unset->setOne();

        for (unsigned col = 0; col < m_column_to_var.size(); col++) {
            unsigned var = m_column_to_var[col];
            if (m_solver.s().value(var) != l_undef) {
                cols_unset->clearBit(col);
                if (m_solver.s().value(var) == l_true)
                    cols_vals->setBit(col);
            }
        }
        last_val_update = m_solver.s().trail_size();
        cancelled_since_val_update = false;
        TRACE("xor", tout << "last val update set to " << last_val_update << "\n");         
        return;
    }

    TRACE("xor", tout << last_val_update << " " << m_solver.s().trail_size() << "\n");
    SASSERT(m_solver.s().trail_size() >= last_val_update);
    for (unsigned i = last_val_update; i < m_solver.s().trail_size(); i++) {
        bool_var var = m_solver.s().trail_literal(i).var();
        if (m_var_to_column.size() <= var)
            continue;
        unsigned col = m_var_to_column[var];
        if (col != UINT32_MAX) {
            SASSERT(m_solver.s().value(var) != l_undef);
            cols_unset->clearBit(col);
            if (m_solver.s().value(var) == l_true)
                cols_vals->setBit(col);
        }
    }
    last_val_update = m_solver.s().trail_size();

    std::cout << "Col-Unassigned: ";
    for (int i = 0; i < 64 * cols_unset->size; ++i) {
        std::cout << (*cols_unset)[i];
    }
    std::cout << "\n";
    std::cout << "Col-Values:     ";
    for (int i = 0; i < 64 * cols_vals->size; ++i) {
        std::cout << (*cols_vals)[i];
    }
    std::cout << std::endl;
}

void EGaussian::prop_lit(const gauss_data& gqd, unsigned row_i, literal ret_lit_prop) {
    unsigned level;
    if (gqd.currLevel == m_solver.s().scope_lvl()) 
        level = gqd.currLevel;
    else 
        level = get_max_level(gqd, row_i);
    
    m_solver.s().assign(ret_lit_prop, m_solver.mk_justification(level, matrix_no, row_i));
}

bool EGaussian::inconsistent() const {
    return m_solver.s().inconsistent();
}

void EGaussian::eliminate_column(unsigned p, gauss_data& gqd) {
    unsigned new_resp_row_n = gqd.new_resp_row;
    unsigned new_resp_col = m_var_to_column[gqd.new_resp_var];
    unsigned row_size = m_mat.num_rows();
    unsigned row_i = 0;

    elim_called++;


    m_mat.display_dense(std::cout) << "\n";
    TRACE("xor", m_mat.display_dense(tout) << "\n");
    
    while (row_i < row_size) {
        //Row has a '1' in eliminating column, and it's not the row responsible
        PackedRow row = m_mat[row_i];
        if (new_resp_row_n != row_i && row[new_resp_col]) {

            // detect orignal non-basic watch list change or not
            unsigned orig_non_resp_var = row_to_var_non_resp[row_i];
            unsigned orig_non_resp_col = m_var_to_column[orig_non_resp_var];
            SASSERT(row[orig_non_resp_col]);
            TRACE("xor", tout << "--> This row " << row_i
                << " is being watched on var: " << orig_non_resp_var + 1
                << " i.e. it must contain '1' for this var's column";);

            SASSERT(!satisfied_xors[row_i]);
            row.xor_in(*(m_mat.begin() + new_resp_row_n));

            elim_xored_rows++;

            //NOTE: responsible variable cannot be eliminated of course
            //      (it's the only '1' in that column).
            //      But non-responsible can be eliminated. So let's check that
            //      and then deal with it if we have to
            if (!row[orig_non_resp_col]) {

                // Delete orignal non-responsible var from watch list
                if (orig_non_resp_var != gqd.new_resp_var) {
                    delete_gausswatch(row_i);
                } else {
                     //this does not need a delete, because during
                     //find_truths, we already did clear_gwatches of the
                     //orig_non_resp_var, so there is nothing to delete here
                 }

                literal ret_lit_prop;
                unsigned new_non_resp_var = 0;
                const gret ret = row.propGause(
                    m_column_to_var,
                    var_has_resp_row,
                    new_non_resp_var,
                    *tmp_col,
                    *tmp_col2,
                    *cols_vals,
                    *cols_unset,
                    ret_lit_prop
                );
                elim_called_propgause++;

                switch (ret) {
                    case gret::confl: {
                        elim_ret_confl++;
                        TRACE("xor", tout << "---> conflict during eliminate_column's fixup";);
                        m_solver.m_gwatches[p].push_back(gauss_watched(row_i, matrix_no));

                        // update in this row non-basic variable
                        row_to_var_non_resp[row_i] = p;

                        xor_reasons[row_i].m_must_recalc = true;
                        xor_reasons[row_i].m_propagated = sat::null_literal;
                        gqd.conflict = m_solver.mk_justification(m_solver.s().scope_lvl(), matrix_no, row_i);
                        gqd.status = gauss_res::confl;

                        break;
                    }
                    case gret::prop: {
                        elim_ret_prop++;
                        TRACE("xor", tout << "---> propagation during eliminate_column's fixup";);

                        // if conflicted already, just update non-basic variable
                        if (gqd.status == gauss_res::confl) {
                            DEBUG_CODE(check_row_not_in_watch(p, row_i););
                            m_solver.m_gwatches[p].push_back(gauss_watched(row_i, matrix_no));
                            row_to_var_non_resp[row_i] = p;
                            break;
                        }

                        // update no_basic information
                        DEBUG_CODE(check_row_not_in_watch(p, row_i););
                        m_solver.m_gwatches[p].push_back(gauss_watched(row_i, matrix_no));
                        row_to_var_non_resp[row_i] = p;

                        xor_reasons[row_i].m_must_recalc = true;
                        xor_reasons[row_i].m_propagated = ret_lit_prop;
                        SASSERT(m_solver.s().value(ret_lit_prop.var()) == l_undef);
                        prop_lit(gqd, row_i, ret_lit_prop);

                        update_cols_vals_set(ret_lit_prop);
                        gqd.status = gauss_res::prop;

                        TRACE("xor", tout << "---> Satisfied XORs set for row: " << row_i;);
                        satisfied_xors[row_i] = true;
                        SASSERT(check_row_satisfied(row_i));
                        break;
                    }

                    // find new watch list
                    case gret::nothing_fnewwatch:
                        elim_ret_fnewwatch++;
                        
                        DEBUG_CODE(check_row_not_in_watch(new_non_resp_var, row_i););
                        m_solver.m_gwatches[new_non_resp_var].push_back(gauss_watched(row_i, matrix_no));
                        row_to_var_non_resp[row_i] = new_non_resp_var;
                        break;

                    // this row already satisfied
                    case gret::nothing_satisfied:
                        elim_ret_satisfied++;
                        TRACE("xor", tout << "---> Nothing to do, already satisfied , pushing in " << p+1 << " as non-responsible var ( " << row_i << " row)\n");

                        // printf("%d:This row is nothing( maybe already true) in eliminate col
                        // n",num_row);

                        DEBUG_CODE(check_row_not_in_watch(p, row_i););
                        m_solver.m_gwatches[p].push_back(gauss_watched(row_i, matrix_no));
                        row_to_var_non_resp[row_i] = p;

                        TRACE("xor", tout << "---> Satisfied XORs set for row: " << row_i;);
                        satisfied_xors[row_i] = true;
                        SASSERT(check_row_satisfied(row_i));
                        break;
                    default:
                        // can not here
                        SASSERT(false);
                        break;
                }
            } else {
                TRACE("xor", tout << "--> OK, this row " << row_i << " still contains '1', can still be responsible";);
            }
        }
        row_i++;

        m_mat.display_dense(std::cout) << "\n";
        TRACE("xor", m_mat.display_dense(tout) << "\n");        
    }

}

//////////////////
// Checking functions below
//////////////////

void EGaussian::check_row_not_in_watch(unsigned v, unsigned row_num) const {
    for (const auto& x: m_solver.m_gwatches[v]) 
        SASSERT(!(x.matrix_num == matrix_no && x.row_n == row_num));    
}


void EGaussian::check_no_prop_or_unsat_rows() {
    TRACE("xor", tout << "mat[" << matrix_no << "] checking invariants...";);

    for (unsigned row = 0; row < m_num_rows; row++) {
        unsigned bits_unset = 0;
        bool val = m_mat[row].rhs();
        for (unsigned col = 0; col < m_num_cols; col++) {
            if (m_mat[row][col]) {
                unsigned var = m_column_to_var[col];
                if (m_solver.s().value(var) == l_undef) 
                    bits_unset++;
                else 
                    val ^= (m_solver.s().value(var) == l_true);                
            }
        }

        CTRACE("xor", bits_unset == 1, tout << "ERROR: row " << row << " is PROP but did not propagate!!!\n");

        CTRACE("xor", (bits_unset == 0 && val),
            tout << "ERROR: row " << row << " is UNSAT but did not conflict!\n";
            tout << "       matrix no: " << matrix_no << "\n"
                 << "       row: " << row << "\n"
                 << "       non-resp var: " << row_to_var_non_resp[row] + 1 << "\n"
                 << "       dec level: " << m_solver.s().scope_lvl() << "\n";
            for (unsigned var = 0; var < m_solver.s().num_vars(); var++) 
                for (const auto& w : m_solver.m_gwatches[var])
                    if (w.matrix_num == matrix_no && w.row_n == row) 
                        tout << "       gauss watched at var: " << var + 1 << " val: " << m_solver.s().value(var) << "\n";);
        
        SASSERT(bits_unset > 1 || (bits_unset == 0 && val == 0));
    }
}

void EGaussian::check_watchlist_sanity() {
    for (unsigned i = 0; i < m_solver.s().num_vars(); i++) 
        for (auto w: m_solver.m_gwatches[i]) 
            VERIFY(w.matrix_num != matrix_no || i < m_var_to_column.size());
}

void EGaussian::check_tracked_cols_only_one_set() {
    unsigned_vector row_resp_for_var(m_num_rows, l_undef);
    for (unsigned col = 0; col < m_num_cols; col++) {
        unsigned var = m_column_to_var[col];
        if (!var_has_resp_row[var])
            continue;

        unsigned num_ones = 0;
        unsigned found_row = l_undef;
        for (unsigned row = 0; row < m_num_rows; row++) {
            if (m_mat[row][col]) {
                num_ones++;
                found_row = row;
            }
        }
        CTRACE("xor", num_ones == 0, tout
            << "mat[" << matrix_no << "] "
            << "WARNING: Tracked col " << col
            << " var: " << var + 1
            << " has 0 rows' bit set to 1..."
            << "\n";);

        CTRACE("xor", num_ones > 1, tout << "mat[" << matrix_no << "] "
            << "ERROR: Tracked col " << col
            << " var: " << var + 1
            << " has " << num_ones << " rows' bit set to 1!!\n";);

        CTRACE("xor", (num_ones == 1) && (row_resp_for_var[found_row] != l_undef),
            tout << "ERROR One row can only be responsible for one col"
            << " but row " << found_row << " is responsible for"
            << " var: " << row_resp_for_var[found_row] + 1
            << " and var: " << var + 1 << "\n";);

        if (num_ones == 1) {
            VERIFY(row_resp_for_var[found_row] == l_undef);
            row_resp_for_var[found_row] = var;
        }
    }
}

void EGaussian::check_invariants() {
    if (!initialized) return;
    check_tracked_cols_only_one_set();
    check_no_prop_or_unsat_rows();
    TRACE("xor", tout << "mat[" << matrix_no << "] " << "Checked invariants. Dec level: " << m_solver.s().scope_lvl() << "\n";);
}

bool EGaussian::check_row_satisfied(unsigned row) {
    bool fin = m_mat[row].rhs();
    for (unsigned i = 0; i < m_num_cols; i++) {
        if (m_mat[row][i]) {
            bool_var var = m_column_to_var[i];
            auto val = m_solver.s().value(var);
            if (val == l_undef) {
                TRACE("xor", tout << "Var " << var+1 << " col: " << i << " is undef!\n";);
                return false;
            }
            fin ^= val == l_true;
        }
    }
    return !fin;
}

bool EGaussian::must_disable(gauss_data& gqd) {
    SASSERT(initialized);
    gqd.disable_checks++;
    if ((gqd.disable_checks & 0x3ff) == 0x3ff) {
        uint64_t egcalled = elim_called + find_truth_ret_satisfied_precheck + find_truth_called_propgause;
        unsigned limit = (unsigned)((double)egcalled * m_solver.s().get_config().m_xor_gauss_min_usefulness_cutoff);
        unsigned useful = find_truth_ret_prop+find_truth_ret_confl+elim_ret_prop+elim_ret_confl;
        if (egcalled > 200 && useful < limit)
            return true;
    }
    return false;
}

void EGaussian::move_back_xor_clauses() {
    for (const auto& x: m_xorclauses) 
        m_solver.m_xorclauses.push_back(std::move(x));    
}


