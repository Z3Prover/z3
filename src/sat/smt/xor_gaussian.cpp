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

// if variable is not in Gaussian matrix, assign unknown column
static const unsigned unassigned_col = UINT32_MAX;

///returns popcnt
unsigned PackedRow::find_watchVar(
    literal_vector& tmp_clause,
    const unsigned_vector& col_to_var,
    bool_vector &var_has_resp_row,
    unsigned& non_resp_var) {
    unsigned popcnt = 0;
    non_resp_var = UINT_MAX;
    tmp_clause.clear();

    for(int i = 0; i < size*64; i++) {
        if ((*this)[i]) {
            popcnt++;
            unsigned var = col_to_var[i];
            tmp_clause.push_back(sat::literal(var, false));

            if (!var_has_resp_row[var]) {
                non_resp_var = var;
            } else {
                //What??? WARNING
                //This var already has a responsible for it...
                //How can it be 1???
                std::swap(tmp_clause[0], tmp_clause.back());
            }
        }
    }
    SASSERT(tmp_clause.size() == popcnt);
    SASSERT(popcnt == 0 || var_has_resp_row[ tmp_clause[0].var() ]) ;
    return popcnt;
}

void PackedRow::get_reason(
    sat::literal_vector& tmp_clause,
    const unsigned_vector& col_to_var,
    PackedRow& cols_vals,
    PackedRow& tmp_col2,
    literal prop) {
    tmp_col2.set_and(*this, cols_vals);
    for (int i = 0; i < size; i++) {
        if (!mp[i])
            continue;
        int64_t tmp = mp[i];
        unsigned long at;
        at = scan_fwd_64b(tmp);
        int extra = 0;
        while (at != 0) {
            unsigned col = extra + at - 1 + i * 64;
            SASSERT(operator[](col) == 1);
            unsigned var = col_to_var[col];
            if (var == prop.var()) {
                tmp_clause.push_back(prop);
                std::swap(tmp_clause[0], tmp_clause.back());
            }
            else {
                bool val_bool = tmp_col2[col]; // NSB: double check if z3 use of sign is compatible
                tmp_clause.push_back(sat::literal(var, val_bool));
            }

            extra += at;
            if (extra == 64)
                break;

            tmp >>= at;
            at = scan_fwd_64b(tmp);
        }
    }
}

gret PackedRow::propGause(
    const unsigned_vector& col_to_var,
    bool_vector &var_has_resp_row,
    unsigned& new_resp_var,
    PackedRow& tmp_col,
    PackedRow& tmp_col2,
    PackedRow& cols_vals,
    PackedRow& cols_unset,
    sat::literal& ret_lit_prop) {
    
    unsigned pop = tmp_col.set_and_until_popcnt_atleast2(*this, cols_unset);
    
    //Find new watch
    if (pop >= 2) {
        for (int i = 0; i < size; i++) if (tmp_col.mp[i]) {
            int64_t tmp = tmp_col.mp[i];
            unsigned long at;
            at = scan_fwd_64b(tmp);
            int extra = 0;
            while (at != 0) {
                unsigned col = extra + at-1 + i*64;
                unsigned var = col_to_var[col];
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

    //Calc value of row
    tmp_col2.set_and(*this, cols_vals);
    unsigned pop_t = tmp_col2.popcnt() + (unsigned)rhs();

    SASSERT(pop == 1 || pop == 0);

    if (pop == 0) {
        if (pop_t % 2 == 0)
            return gret::nothing_satisfied;
        else
            return gret::confl;
    }

    for (int i = 0; i < size; i++) if (tmp_col.mp[i]) {
        int at = scan_fwd_64b(tmp_col.mp[i]);

        // found prop
        unsigned col = at - 1 + i * 64;
        SASSERT(tmp_col[col] == 1);
        unsigned var = col_to_var[col];
        ret_lit_prop = sat::literal(var, 1 == pop_t % 2);
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

/*class ColSorter {
    
    xr::solver* m_solver;
    
public:
        
    explicit ColSorter(xr::solver* _solver) : m_solver(_solver) {
        for (const auto& ass: m_solver.assumptions) {
            literal p = m_solver.map_outer_to_inter(ass.lit_outer);
            if (p.var() < m_solver.s().num_vars()) {
                assert(m_solver.seen.size() > p.var());
                m_solver.seen[p.var()] = 1;
            }
        }
    }

    void finishup() {
        for (const auto& ass: m_solver.assumptions) {
            literal p = m_solver.map_outer_to_inter(ass.lit_outer);
            if (p.var() < m_solver.s().num_vars())
                m_solver.seen[p.var()] = 0;
        }
    }

    bool operator()(unsigned a, unsigned b) {
        SASSERT(m_solver.seen.size() > a);
        SASSERT(m_solver.seen.size() > b);
        if (m_solver.seen[b] && !m_solver.seen[a])
            return true;

        if (!m_solver.seen[b] && m_solver.seen[a])
            return false;

        return false;
    }
};*/

void EGaussian::select_columnorder() {
    var_to_col.clear();
    var_to_col.resize(m_solver.s().num_vars(), unassigned_col);
    unsigned_vector vars_needed;
    unsigned largest_used_var = 0;

    for (const xor_clause& x : m_xorclauses) {
        for (unsigned v : x) {
            SASSERT(m_solver.s().value(v) == l_undef);
            if (var_to_col[v] == unassigned_col) {
                vars_needed.push_back(v);
                var_to_col[v] = unassigned_col - 1;
                largest_used_var = std::max(largest_used_var, v);
            }
        }
    }

    if (vars_needed.size() >= UINT32_MAX / 2 - 1) 
        throw default_exception("Matrix has too many rows");
    
    if (m_xorclauses.size() >= UINT32_MAX / 2 - 1) 
        throw default_exception("Matrix has too many rows");
    
    var_to_col.resize(largest_used_var + 1);


    /*TODO: for assumption variables; ignored right now
    ColSorter c(m_solver);
    std::sort(vars_needed.begin(), vars_needed.end(), c);
    c.finishup();*/

    col_to_var.clear();
    for (unsigned v : vars_needed) {
        SASSERT(var_to_col[v] == unassigned_col - 1);
        var_to_col[v] = col_to_var.size();
        col_to_var.push_back(v);
    }

    // for the ones that were not in the order_heap, but are marked in var_to_col
    for (unsigned v = 0; v < var_to_col.size(); v++) {
        if (var_to_col[v] == unassigned_col - 1) {
            var_to_col[v] = col_to_var.size();
            col_to_var.push_back(v);
        }
    }
}

void EGaussian::fill_matrix() {
    var_to_col.clear();

    // decide which variable in matrix column and the number of rows
    select_columnorder();
    num_rows = m_xorclauses.size();
    num_cols = col_to_var.size();
    if (num_rows == 0 || num_cols == 0) {
        return;
    }
    mat.resize(num_rows, num_cols); // initial gaussian matrix

    for (unsigned row = 0; row < num_rows; row++) {
        const xor_clause& c = m_xorclauses[row];
        mat[row].set(c, var_to_col, num_cols);
        char_vector line;
        line.resize(num_rows, 0);
        line[row] = 1;
    }

    // reset
    var_has_resp_row.clear();
    var_has_resp_row.resize(m_solver.s().num_vars(), 0);
    row_to_var_non_resp.clear();

    delete_gauss_watch_this_matrix();

    //reset satisfied_xor state
    SASSERT(m_solver.m_num_scopes == 0);
    satisfied_xors.clear();
    satisfied_xors.resize(num_rows, false);
}

void EGaussian::delete_gauss_watch_this_matrix() {
    for (unsigned i = 0; i < m_solver.m_gwatches.size(); i++) 
        clear_gwatches(i);    
}

void EGaussian::clear_gwatches(unsigned var) {
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

bool EGaussian::full_init(bool& created) {
    SASSERT(!inconsistent());
    SASSERT(m_solver.m_num_scopes == 0);
    SASSERT(initialized == false);
    created = true;

    unsigned trail_before;
    while (true) {
        trail_before = m_solver.s().trail_size();
        m_solver.clean_xor_clauses(m_xorclauses);

        fill_matrix();
        before_init_density = get_density();
        if (num_rows == 0 || num_cols == 0) {
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
                SASSERT(m_solver.m_num_scopes == 0);
                m_solver.s().propagate(false); // TODO: Can we really do this here?
                if (inconsistent()) {
                    TRACE("xor", tout << "eliminate & adjust matrix during init lead to UNSAT\n";);
                    return false;
                }
                break;
            default:
                break;
        }
        
        //Let's exit if nothing new happened
        if (m_solver.s().trail_size() == trail_before)
            break;
    }
    DEBUG_CODE(check_watchlist_sanity(););
    TRACE("xor", tout << "initialised matrix " << matrix_no << "\n");

    xor_reasons.resize(num_rows);
    unsigned num_64b = num_cols/64+(bool)(num_cols%64);
    
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

    after_init_density = get_density();

    initialized = true;
    update_cols_vals_set(true);
    DEBUG_CODE(check_invariants(););
    
    return !inconsistent();
}

void EGaussian::eliminate() {
    // TODO: Why twice? gauss_jordan_elim
    unsigned end_row = num_rows;
    unsigned rowI = 0;
    unsigned row_i = 0;
    unsigned col = 0;

    // Gauss-Jordan Elimination
    while (row_i != num_rows && col != num_cols) {
        unsigned row_with_1_in_col = rowI;
        unsigned row_with_1_in_col_n = row_i;

        // Find first "1" in column.
        for (; row_with_1_in_col < end_row; ++row_with_1_in_col, row_with_1_in_col_n++) {
            if (mat[row_with_1_in_col][col])
                break;            
        }

        // We have found a "1" in this column
        if (row_with_1_in_col < end_row) {
            var_has_resp_row[col_to_var[col]] = true;

            // swap row row_with_1_in_col and rowIt
            if (row_with_1_in_col != rowI)
                mat[rowI].swapBoth(mat[row_with_1_in_col]);

            // XOR into *all* rows that have a "1" in column COL
            // Since we XOR into *all*, this is Gauss-Jordan (and not just Gauss)
            unsigned k = 0;
            for (unsigned k_row = 0; k_row < end_row; ++k_row, k++) {
                // xor rows K and I
                if (k_row != rowI && mat[k_row][col]) {
                    mat[k_row].xor_in(mat[rowI]);
                }
            }
            row_i++;
            ++rowI;
        }
        col++;
    }
}

literal_vector* EGaussian::get_reason(unsigned row, int& out_ID) {
    if (!xor_reasons[row].m_must_recalc) {
        out_ID = xor_reasons[row].m_ID;
        return &(xor_reasons[row].m_reason);
    }

    // Clean up previous one
    
    literal_vector& to_fill = xor_reasons[row].m_reason;
    to_fill.clear();

    mat[row].get_reason(
        to_fill,
        col_to_var,
        *cols_vals,
        *tmp_col2,
        xor_reasons[row].m_propagated);
    
    xor_reasons[row].m_must_recalc = false;
    xor_reasons[row].m_ID = out_ID;
    return &to_fill;
}

gret EGaussian::init_adjust_matrix() {
    SASSERT(m_solver.s().at_search_lvl());
    SASSERT(row_to_var_non_resp.empty());
    SASSERT(satisfied_xors.size() >= num_rows);
    TRACE("xor", tout << "mat[" << matrix_no << "] init adjusting matrix";);

    unsigned row_i = 0;       // row index
    unsigned adjust_zero = 0; //  elimination row
    for (PackedRow row : mat) {
        if (row_i >= num_rows)
            break;
        unsigned non_resp_var;
        unsigned popcnt = row.find_watchVar(tmp_clause, col_to_var, var_has_resp_row, non_resp_var);

        switch (popcnt) {

            //Conflict or satisfied
            case 0:
                TRACE("xor", tout << "Empty XOR during init_adjust_matrix, rhs: " << row.rhs() << "\n");
                adjust_zero++;

                // conflict
                if (row.rhs()) {
                    // TODO: Is this enough? What's the justification?
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
                bool xorEqualFalse = !mat[row_i].rhs();
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
                bool xorEqualFalse = !mat[row_i].rhs();

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

    mat.resizeNumRows(row_i - adjust_zero);
    num_rows = row_i - adjust_zero;

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
    literal_vector* cl = get_reason(row_n, ID);
    unsigned nMaxLevel = gqd.currLevel;
    unsigned nMaxInd = 1;

    for (unsigned i = 1; i < cl->size(); i++) {
        literal l = (*cl)[i];
        unsigned nLevel = m_solver.s().lvl(l);
        if (nLevel > nMaxLevel) {
            nMaxLevel = nLevel;
            nMaxInd = i;
        }
    }

    //should we??
    if (nMaxInd != 1) 
        std::swap((*cl)[1], (*cl)[nMaxInd]);
    
    return nMaxLevel;
}

bool EGaussian::find_truths(
    svector<gauss_watched>& ws,
    unsigned& i,
    unsigned& j,
    unsigned var,
    unsigned row_n,
    gauss_data& gqd) {
    SASSERT(gqd.status != gauss_res::confl);
    SASSERT(initialized);

    // printf("dd Watch variable : %d  ,  Wathch row num %d    n", p , row_n);

    TRACE("xor", tout 
        << "mat[" << matrix_no << "] find_truths\n"
        << "-> row: " << row_n << "\n"
        << "-> var: " << var+1 << "\n"
        << "-> dec lev:" << m_solver.m_num_scopes);
    SASSERT(row_n < num_rows);
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
    const gret ret = mat[row_n].propGause(
        col_to_var,
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
            gqd.conflict = m_solver.mk_justification(m_solver.s().search_lvl(), matrix_no, row_n);
            gqd.status = gauss_res::confl;
            TRACE("xor", tout << "--> conflict";);
            
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
            // printf("%d:This row is find new watch:%d => orig %d p:%d    n",row_n ,
            // new_resp_var,orig_basic , p);

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

inline void EGaussian::update_cols_vals_set(const literal lit1) {
    cols_unset->clearBit(var_to_col[lit1.var()]);
    if (!lit1.sign()) {
        cols_vals->setBit(var_to_col[lit1.var()]);
    }
}

void EGaussian::update_cols_vals_set(bool force) {
    SASSERT(initialized);

    //cancelled_since_val_update = true;
    if (cancelled_since_val_update || force) {
        cols_vals->setZero();
        cols_unset->setOne();

        for (unsigned col = 0; col < col_to_var.size(); col++) {
            unsigned var = col_to_var[col];
            if (m_solver.s().value(var) != l_undef) {
                cols_unset->clearBit(col);
                if (m_solver.s().value(var) == l_true) {
                    cols_vals->setBit(col);
                }
            }
        }
        last_val_update = m_solver.s().trail_size();
        cancelled_since_val_update = false;
        return;
    }

    SASSERT(m_solver.s().trail_size() >= last_val_update);
    for(unsigned i = last_val_update; i < m_solver.s().trail_size(); i++) {
        sat::bool_var var = m_solver.s().trail_literal(i).var();
        if (var_to_col.size() <= var) {
            continue;
        }
        unsigned col = var_to_col[var];
        if (col != unassigned_col) {
            SASSERT(m_solver.s().value(var) != l_undef);
            cols_unset->clearBit(col);
            if (m_solver.s().value(var) == l_true) {
                cols_vals->setBit(col);
            }
        }
    }
    last_val_update = m_solver.s().trail_size();
}

void EGaussian::prop_lit(const gauss_data& gqd, unsigned row_i, const literal ret_lit_prop) {
    unsigned level;
    if (gqd.currLevel == m_solver.m_num_scopes) 
        level = gqd.currLevel;
    else 
        level = get_max_level(gqd, row_i);
    
    m_solver.s().assign(ret_lit_prop, m_solver.mk_justification(level, matrix_no, row_i));
}

bool EGaussian::inconsistent() const {
    return m_solver.s().inconsistent();
}

void EGaussian::eliminate_col(unsigned p, gauss_data& gqd) {
    unsigned new_resp_row_n = gqd.new_resp_row;
    PackedMatrix::iterator rowI = mat.begin();
    PackedMatrix::iterator end = mat.end();
    unsigned new_resp_col = var_to_col[gqd.new_resp_var];
    unsigned row_i = 0;

    elim_called++;

    // NSB code review: can't we use mat[row_i]
    // and for (unsigned row_i = 0; row_i < mat.size(); ++row_i)
    // replace occurrences of *rowI by mat[row_i]
    // 
    while (rowI != end) {
        //Row has a '1' in eliminating column, and it's not the row responsible
        if (new_resp_row_n != row_i && (*rowI)[new_resp_col]) {

            // detect orignal non-basic watch list change or not
            unsigned orig_non_resp_var = row_to_var_non_resp[row_i];
            unsigned orig_non_resp_col = var_to_col[orig_non_resp_var];
            SASSERT((*rowI)[orig_non_resp_col]);
            TRACE("xor", tout << "--> This row " << row_i
                << " is being watched on var: " << orig_non_resp_var + 1
                << " i.e. it must contain '1' for this var's column";);

            SASSERT(!satisfied_xors[row_i]);
            (*rowI).xor_in(*(mat.begin() + new_resp_row_n));

            elim_xored_rows++;

            //NOTE: responsible variable cannot be eliminated of course
            //      (it's the only '1' in that column).
            //      But non-responsible can be eliminated. So let's check that
            //      and then deal with it if we have to
            if (!(*rowI)[orig_non_resp_col]) {

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
                const gret ret = (*rowI).propGause(
                    col_to_var,
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
                        TRACE("xor", tout << "---> conflict during eliminate_col's fixup";);
                        m_solver.m_gwatches[p].push_back(gauss_watched(row_i, matrix_no));

                        // update in this row non-basic variable
                        row_to_var_non_resp[row_i] = p;

                        xor_reasons[row_i].m_must_recalc = true;
                        xor_reasons[row_i].m_propagated = sat::null_literal;
                        gqd.conflict = m_solver.mk_justification(m_solver.s().search_lvl(), matrix_no, row_i);
                        gqd.status = gauss_res::confl;

                        break;
                    }
                    case gret::prop: {
                        elim_ret_prop++;
                        TRACE("xor", tout << "---> propagation during eliminate_col's fixup";);

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
        ++rowI;
        row_i++;
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

    for (unsigned row = 0; row < num_rows; row++) {
        unsigned bits_unset = 0;
        bool val = mat[row].rhs();
        for (unsigned col = 0; col < num_cols; col++) {
            if (mat[row][col]) {
                unsigned var = col_to_var[col];
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
                 << "       dec level: " << m_solver.m_num_scopes << "\n";
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
            VERIFY(w.matrix_num != matrix_no || i < var_to_col.size());
}

void EGaussian::check_tracked_cols_only_one_set() {
    unsigned_vector row_resp_for_var(num_rows, l_undef);
    for (unsigned col = 0; col < num_cols; col++) {
        unsigned var = col_to_var[col];
        if (!var_has_resp_row[var])
            continue;

        unsigned num_ones = 0;
        unsigned found_row = l_undef;
        for (unsigned row = 0; row < num_rows; row++) {
            if (mat[row][col]) {
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
    TRACE("xor", tout << "mat[" << matrix_no << "] " << "Checked invariants. Dec level: " << m_solver.m_num_scopes << "\n";);
}

bool EGaussian::check_row_satisfied(unsigned row) {
    bool fin = mat[row].rhs();
    for (unsigned i = 0; i < num_cols; i++) {
        if (mat[row][i]) {
            unsigned var = col_to_var[i];
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
