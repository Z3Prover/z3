/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    lu.cpp

Abstract:

    Simple LU factorization module based on the paper:
    
    "Maintaining LU factors of a General Sparse Matrix"
    P. E. Gill, W. Murray, M. Saunders, M. Wright

Author:

    Leonardo de Moura (leonardo) 2011-06-09

Revision History:

--*/
#include"lu.h"

template<typename NM>
void lu<NM>::todo::init(unsigned capacity) {
    m_elem2len.reset();
    m_elem2pos.reset();
    m_elems_per_len.reset();
    m_elem2len.resize(capacity, UINT_MAX);
    m_elem2pos.resize(capacity, UINT_MAX);
    m_elems_per_len.resize(capacity+1);
    m_size = 0;
}

template<typename NM>
void lu<NM>::todo::display(std::ostream & out) const {
    vector<unsigned_vector>::const_iterator it  = m_elems_per_len.begin();
    vector<unsigned_vector>::const_iterator end = m_elems_per_len.end();
    for (unsigned idx = 0; it != end; ++it, ++idx) {
        unsigned_vector const & v = *it;
        if (!v.empty()) {
            out << idx << ": [";
            unsigned_vector::const_iterator it2  = v.begin();
            unsigned_vector::const_iterator end2 = v.end();
            for (bool first = true; it2 != end2; ++it2) {
                if (first) first = false; else out << " ";
                out << *it2;
            }
            out << "] ";
        }
    }
}

template<typename NM>
void lu<NM>::todo::updt_len(unsigned elem, unsigned len) {
    erase(elem);
    m_elem2len[elem] = len;
    unsigned pos = m_elems_per_len[len].size();
    m_elems_per_len[len].push_back(elem);
    m_elem2pos[elem] = pos;
    m_size++;
}

template<typename NM>
void lu<NM>::todo::erase(unsigned elem) {
    if (!contains(elem))
        return;
    unsigned len = m_elem2len[elem];
    unsigned pos = m_elem2pos[elem];
    unsigned_vector & v = m_elems_per_len[len];
    SASSERT(v[pos] == elem);
    if (pos != v.size() - 1) {
        unsigned last_elem = v.back();
        m_elem2pos[last_elem] = pos;
        v[pos] = last_elem;
    }
    v.pop_back();
    m_elem2pos[elem] = UINT_MAX;
    m_size--;
}

template<typename NM>
void lu<NM>::todo::iterator::find_next() {
    unsigned sz = m_todo.m_elems_per_len.size();
    while (m_i < sz) {
        if (m_j < m_todo.m_elems_per_len[m_i].size())
            return;
        m_j = 0;
        m_i++;
    }
}

// -----------------------
//
// Main
//
// -----------------------
template<typename NM>
lu<NM>::lu(manager & m, params_ref const & p):
    m_manager(m),
    m_tmp_xU_vector(m, 0),
    m_tmp_replace_column_vector(m, 0),
    m_tmp_vector(m, 0),
    m_tmp_row(m, 0),
    m_tmp_col(m, 0) {
    m_sz = 0;
    CASSERT("lu", check_invariant());
    ini = false;
    updt_params(p);
}

template<typename NM>
lu<NM>::~lu() {
    m().del(m_mu);
    
    // temporary values
    m().del(tol);
    m().del(C_max);
    m().del(A_ij);
    m().del(A_best);
    m().del(A_aux);
    m().del(tmp);
    m().del(mu_best);
    m().del(mu_1);

    del_nums(L.A);
    del_nums(U.A);
    del_nums(T.A);
}

template<typename NM>
void lu<NM>::updt_params(params_ref const & p) {
    unsigned mu = p.get_uint(":lu-mu", 100); // it was 10...
    m().set(m_mu, mu); 
    m_selection_cutoff = p.get_uint(":lu-selection-cutoff", 10);
}

/**
   \brief Delete the numerals in the given vector, and reset it.
*/
template<typename NM>
void lu<NM>::del_nums(numeral_vector & nums) {
    typename numeral_vector::iterator it  = nums.begin();
    typename numeral_vector::iterator end = nums.end();
    for (; it != end; ++it) {
        m().del(*it);
    }
    nums.reset();
}

template<typename NM>
void lu<NM>::reset() {
    m_sz = 0;

    P.reset(m_sz);
    Q.reset(m_sz);

    del_nums(L.A);
    L.indc.reset();
    L.indr.reset();

    del_nums(U.A);
    U.indr.reset();
    U.begr.reset();
    U.endr.reset();
    U.num_entries = 0;

    T.indr.reset();
    T.begr.reset();
    T.endr.reset();
    del_nums(T.A);
    T.indc.reset();
    T.begc.reset();
    T.endc.reset();
    T.num_entries = 0;

    locw.reset();
}

// -----------------------
//
// Initialization
//
// -----------------------
#define INI_COL_SZ 16
#define INV_FILLIN_FACTOR 5
#define COMPRESSION_FACTOR 4

template<typename NM>
inline unsigned lu<NM>::fillin_for(unsigned sz) {
    return (sz / INV_FILLIN_FACTOR) + 1;
}

template<typename NM>
void lu<NM>::init(unsigned size) { 
    reset();

    m_num_replacements = 0;

    m_sz = size;

    m_todo_rows.init(size);
    m_todo_cols.init(size);
    m_enabled_rows.reset();
    m_enabled_cols.reset();
    m_enabled_rows.resize(m_sz, true);
    m_enabled_cols.resize(m_sz, true);

    P.reset(m_sz);
    Q.reset(m_sz);

    locw.reset(); // force it to be reinitialized, it may contain unintended content if LU was interrupted due to floating point imprecision.
    locw.resize(m_sz, UINT_MAX);
    
    ini       = size > 0;
    ini_irow  = 0;
    T.begr.push_back(0);
    T.endr.push_back(0);
    T.num_entries = 0;

    SASSERT(T.begc.empty());
    SASSERT(T.endc.empty());

    T.A.resize(m_sz * INI_COL_SZ);
    T.indc.resize(m_sz * INI_COL_SZ, UINT_MAX);
    unsigned locc = 0;
    for (unsigned i = 0; i < m_sz; i++) {
        T.begc.push_back(locc);
        T.endc.push_back(locc);
        locc += INI_COL_SZ;
    }

    SASSERT(T.begc.size() == m_sz);
    SASSERT(T.endc.size() == m_sz);

    m_tmp_vector.reset(m_sz);
    m_tmp_col.reset(m_sz);
    m_tmp_xU_vector.reset(m_sz);
    m_tmp_replace_column_vector.reset(m_sz);
}

template<typename NM>
void lu<NM>::add_entry(numeral const & a, unsigned x) {
    SASSERT(T.endc[x] >= T.begc[x]);
    SASSERT(T.endc[x] - T.begc[x] + 1 <= m_sz); // has space for another element in column x
    SASSERT(ini);
    SASSERT(x < m_sz);
    TRACE("lu", tout << "add_entry(" << m().to_string(a) << ", " << x << ")\n";);
    if (T.endc[x] == T.indc.size()) {
        // expand last column
        T.A.push_back(numeral());
        m().set(T.A.back(), a);
        T.indc.push_back(ini_irow);
        T.endc[x]++;
        SASSERT(T.endc[x] == T.indc.size());
    }
    else {
        if (T.indc[T.endc[x]] != UINT_MAX) {
            TRACE("lu", tout << "moving column to the end: " << x << "\n";);
            move_col_to_end(x);
        }
        SASSERT(T.indc[T.endc[x]] == UINT_MAX);
        // use free space
        unsigned pos = T.endc[x];
        m().set(T.A[pos], a);
        T.indc[pos] = ini_irow;
        T.endc[x]++;
    }
    T.indr.push_back(x);
    T.endr.back()++;
    T.num_entries++;
    SASSERT(T.endc[x] >= T.begc[x]);
    SASSERT(T.endc[x] - T.begc[x] <= m_sz);
}

template<typename NM>
void lu<NM>::move_col_to_end(unsigned c) {
    SASSERT(T.endc[c] >= T.begc[c]);
    SASSERT(T.endc[c] - T.begc[c] <= m_sz);
    unsigned begin = T.begc[c];
    unsigned end   = T.endc[c];
    T.begc[c] = T.indc.size();
    T.endc[c] = T.begc[c] + end - begin;
    for (unsigned j = begin; j < end; j++) {
        T.A.push_back(numeral());
        m().swap(T.A.back(), T.A[j]);
        unsigned r = T.indc[j];
        T.indc.push_back(r);
        T.indc[j] = UINT_MAX; // mark as free
    }
    unsigned sz = end - begin;
    unsigned fillin = fillin_for(sz);
    for (unsigned i = 0; i < fillin; i++) {
        T.indc.push_back(UINT_MAX); // leave space
        T.A.push_back(numeral());
    }
    SASSERT(T.endc[c] >= T.begc[c]);
    SASSERT(T.endc[c] - T.begc[c] <= m_sz);
}

template<typename NM>
void lu<NM>::move_row_to_end(unsigned r) {
    unsigned begin = T.begr[r];
    unsigned end   = T.endr[r];
    T.begr[r]  = T.indr.size();
    T.endr[r]  = T.begr[r] + end - begin;
    for (unsigned j = begin; j < end; j++) {
        unsigned c = T.indr[j];
        T.indr.push_back(c);
        T.indr[j] = UINT_MAX; // mark as free
    }
    unsigned sz = end - begin;
    unsigned fillin = fillin_for(sz);
    for (unsigned i = 0; i < fillin; i++)
        T.indr.push_back(UINT_MAX);
}

template<typename NM>
void lu<NM>::end_row() {
    TRACE("lu", tout << "end_row()\n";);
    SASSERT(ini);
    ini_irow++;
    if (ini_irow == m_sz) {
        // completed initialization
        ini = false;
        CASSERT("lu", check_T());
    }
    else {
        unsigned sz = T.endr.back() - T.begr.back();
        unsigned fillin = fillin_for(sz);
        for (unsigned i = 0; i < fillin; i++)
            T.indr.push_back(UINT_MAX); // leave space
        T.begr.push_back(T.indr.size());
        T.endr.push_back(T.indr.size());
    }
}

// -----------------------
//
// Factorization
//
// -----------------------

// Initialize the todo vectors: todo_rows and todo_cols.
// The auxiliary vectors iplocr and iplocc are also initialized.
template<typename NM>
void lu<NM>::init_fact() {
    for (unsigned i = 0; i < m_sz; i++) {
        SASSERT(T.endr[i] >= T.begr[i]);
        SASSERT(T.endc[i] >= T.begc[i]);
        SASSERT(T.endr[i] - T.begr[i] <= m_sz);
        SASSERT(T.endc[i] - T.begc[i] <= m_sz);
        m_todo_rows.updt_len(i, T.endr[i] - T.begr[i]);
        m_todo_cols.updt_len(i, T.endc[i] - T.begc[i]);
    }
    m_marked_rows.reset();
    m_marked_rows.resize(m_sz, false);
}

template<typename NM>
bool lu<NM>::stability_test(unsigned rin, unsigned cin, bool improvingM) {
    if (NM::precise()) {
        if (improvingM) {
            // must save coefficient of rin, cin in A_best
            unsigned begin = T.begc[cin];
            unsigned end   = T.endc[cin];
            for (unsigned j = begin; j < end; j++) {
                unsigned r    = T.indc[j];
                if (rin == r) {
                    m().set(A_best, T.A[j]);
                    break;
                }
            }
            return true;
        }
        else {
            return false;
        }
    }
    // Stability test for imprecise numerals
    // See section 5.3 of "Maintaining LU factors of a General Sparse Matrix"
    m().set(C_max, 0);
    m().set(tol, 0);
    m().set(A_ij, 0);
    bool C_max_init = false;
    unsigned begin  = T.begc[cin];
    unsigned end    = T.endc[cin];
#if 0
    static unsigned stability_test_counter = 0;
    static unsigned stability_test_cost    = 0;
    stability_test_counter++;
    stability_test_cost += end - begin;
    if (stability_test_counter % 1000000 == 0) {
        verbose_stream() << "[stability-test] cost: " << stability_test_cost << " num-calls: " << stability_test_counter
                  << " selection-cutoff: " << m_selection_cutoff << " sz: " << m_sz 
                  << " avg-col-sz: " << stability_test_cost / stability_test_counter << "\n";
    }
#endif
    for (unsigned j = begin; j < end; j++) {
        unsigned r    = T.indc[j];
        if (rin == r) {
            m().set(A_ij, T.A[j]);
            m().set(tol, A_ij);
            m().abs(tol);
            if (improvingM) {
                // tol = |A_ij| / mu
                m().mul(tol, m_mu, tol); 
            }
            else {
                // tol = |A_ij| / mu_best
                m().mul(tol, mu_best, tol);
            }
            if (C_max_init && m().ge(C_max, tol)) {
                TRACE("stability", tout << "failure 1. C_max: " << m().to_string(C_max) << ", tol: " << m().to_string(tol) 
                      << ", A_ij: " << m().to_string(A_ij) << ", m_mu: " << m().to_string(m_mu) 
                      << ", mu_best: " << m().to_string(mu_best) << ", improvingM: " << improvingM << "\n";); 
                return false;
            }
            continue;
        }
        if (!enabled_row(r))
            continue;
        m().set(A_aux, T.A[j]);
        m().abs(A_aux);
        if (m().gt(A_aux, C_max)) {
            m().set(C_max, A_aux);
            C_max_init = true;
            if (m().is_pos(tol)) {
                // if tol was already set test, then reject if C_max >= tol
                if (m().ge(C_max, tol)) {
                    TRACE("stability", tout << "failure 2. C_max: " << m().to_string(C_max) << ", tol: " << m().to_string(tol) 
                          << ", A_ij: " << m().to_string(A_ij) << ", m_mu: " << m().to_string(m_mu) 
                          << ", mu_best: " << m().to_string(mu_best) << "\n";); 
                    return false;
                }
            }
        }
    }
    
    m().set(A_best, A_ij);
    m().set(mu_best, C_max);
    m().abs(A_ij);
    m().div(mu_best, A_ij, mu_best);
    CTRACE("stability", m().is_zero(mu_best), tout << "found: A_ij: " << m().to_string(A_ij) << " mu_best: " << m().to_string(mu_best) 
           << " C_max: " << m().to_string(C_max) << "\n";);
    return true;
}

/**
   \brief Select the next pivot and store in (r_out, c_out)
   The coefficient is stored in A_best.
*/
template<typename NM>
void lu<NM>::select_pivot(unsigned & r_out, unsigned & c_out) {
    unsigned M_best  = UINT_MAX;
    unsigned M2_best = UINT_MAX;
    m().set(mu_best, 0);

    SASSERT(m_todo_rows.size() == m_todo_cols.size());
    TRACE("lu_todo", 
          tout << "rows: "; m_todo_rows.display(tout); tout << "\n";
          tout << "cols: "; m_todo_cols.display(tout); tout << "\n";);

    typename todo::iterator it(m_todo_rows);
    unsigned counter = 0;
    while (!it.at_end()) {
        unsigned r = it.curr();
        it.next();
        counter++;
        TRACE("lu_todo", tout << "row r: " << r << ", r_out: " << r_out << ", c_out: " << c_out << "\n";);
        SASSERT(enabled_row(r));
        if (counter >= m_selection_cutoff && M_best != UINT_MAX) 
            break;
        CTRACE("stability", counter > m_selection_cutoff, 
               tout << "counter: " << counter << " mu_best: " << m().to_string(mu_best) << " M_best: " << M_best << "\n";);
        unsigned lenr  = m_todo_rows.len(r);
        unsigned begin = T.begr[r];
        unsigned end   = T.endr[r];
#if 0
        // -----------------------------------
        // enable this block of code to simulate singular matrix exception after a couple of pivoting steps...
#define NUM_STEPS_UNTIL_EXCEPTION 10
        static unsigned g_num_pivots = 0;
        if (!m().precise()) {
            g_num_pivots++;
            if (g_num_pivots == NUM_STEPS_UNTIL_EXCEPTION) {
                g_num_pivots = 0;
                throw lu_exception("singular matrix");
            }
        }
        //------------------------------------
#endif        
        if (lenr == 0)
            throw lu_exception("singular matrix");
        for (unsigned j = begin; j < end; j++) {
            unsigned c  = T.indr[j];
            if (!enabled_col(c))
                continue;
            unsigned lenc = m_todo_cols.len(c);
            unsigned M    = (lenc - 1) * (lenr - 1);
            TRACE("lu_todo", tout << "c: " << c << ", M: " << M << ", M_best: " << M_best << "\n";);
            if (M > M_best)
                continue;
            bool improving;
            if (NM::precise()) 
                improving = M_best == UINT_MAX || M < M_best || (M == M_best && lenc < M2_best);
            else
                improving = M_best == UINT_MAX || M < M_best;
            if (stability_test(r, c, improving)) {
                M_best  = M;
                M2_best = lenc;
                r_out   = r;
                c_out   = c;
                CTRACE("stability", !m().precise(), tout << "mu_best: " << m().to_string(mu_best) << "\n";);
            }
            else {
                CTRACE("stability", !m().precise(), 
                       tout << "failed stability, improving: " << improving << " mu_best: " << m().to_string(mu_best) << "\n";);
            }
        }
    }

    if (M_best == UINT_MAX)
        throw lu_exception("failed stability test");

    typename todo::iterator it2(m_todo_cols);
    counter = 0;
    while (!it2.at_end()) {
        unsigned c = it2.curr();
        it2.next();
        counter++;
        TRACE("lu_todo", tout << "col c: " << c << ", r_out: " << r_out << ", c_out: " << c_out << "\n";);
        SASSERT(enabled_col(c));
        if (counter >= m_selection_cutoff)
            break;
        unsigned lenc  = m_todo_cols.len(c);
        unsigned begin = T.begc[c];
        unsigned end   = T.endc[c];
        for (unsigned j = begin; j < end; j++) {
            unsigned r    = T.indc[j];
            if (!enabled_row(r))
                continue;
            unsigned lenr = m_todo_rows.len(r);
            unsigned M    = (lenc - 1) * (lenr - 1);
            TRACE("lu_todo", tout << "r: " << r << ", M: " << M << ", M_best: " << M_best << "\n";);
            if (M > M_best)
                continue;
            bool improving;
            if (NM::precise()) 
                improving = M < M_best || (M == M_best && lenc < M2_best);
            else
                improving = M < M_best;
            if (stability_test(r, c, M < M_best)) {
                M_best  = M;
                M2_best = lenc;
                r_out   = r;
                c_out   = c;
            }
        }
    }
}

/**
   \brief For debugging: checks whether all position in locw are UINT_MAX.
*/
template<typename NM>
bool lu<NM>::check_locw() const {
    for (unsigned i = 0; i < m_sz; i++) {
        SASSERT(locw[i] == UINT_MAX);
    }
    return true;
}

template<typename NM>
inline void lu<NM>::dec_lenr(unsigned r) {
    SASSERT(m_todo_rows.len(r) > 0);
    SASSERT(enabled_row(r));
    m_todo_rows.updt_len(r, m_todo_rows.len(r) - 1);
}

template<typename NM>
inline void lu<NM>::inc_lenr(unsigned r) {
    SASSERT(enabled_row(r));
    m_todo_rows.updt_len(r, m_todo_rows.len(r) + 1);
}

template<typename NM>
inline void lu<NM>::dec_lenc(unsigned c) {
    SASSERT(m_todo_cols.len(c) > 0);
    SASSERT(enabled_col(c));
    m_todo_cols.updt_len(c, m_todo_cols.len(c) - 1);
}

template<typename NM>
inline void lu<NM>::inc_lenc(unsigned c) {
    SASSERT(enabled_col(c));
    m_todo_cols.updt_len(c, m_todo_cols.len(c) + 1);
}

/**
   \brief Remove the disabled columns from the row r.
*/
template<typename NM>
void lu<NM>::del_disabled_cols(unsigned r) {
    unsigned begin = T.begr[r];
    unsigned end   = T.endr[r];
    unsigned j     = begin;
    for (unsigned i = begin; i < end; i++) {
        unsigned c = T.indr[i];
        if (!enabled_col(c))
            continue;
        T.indr[j] = c;
        j++;
    }
    T.endr[r] = j;
    for (; j < end; j++) 
        T.indr[j] = UINT_MAX;
}

/**
   \brief Remove colum c from row r. 
   It also removes any disabled column. 
*/
template<typename NM>
void lu<NM>::del_row_entry(unsigned r, unsigned c) {
    unsigned begin = T.begr[r];
    unsigned end   = T.endr[r];
    TRACE("del_row_entry", tout << "del_row_entry, r: " << r << ", c: " << c << ", begin: " << begin << ", end: " << end << "\n";);
    unsigned j     = begin;
    for (unsigned i = begin; i < end; i++) {
        unsigned c_prime = T.indr[i];
        if (c_prime == c || !enabled_col(c_prime))
            continue;
        T.indr[j] = c_prime;
        j++;
    }
    SASSERT(j < end);
    T.endr[r] = j;
    for (; j < end; j++) 
        T.indr[j] = UINT_MAX;
    TRACE("del_row_entry", tout << "after del_row_entry, begin: " << T.begr[r] << ", end: " << T.endr[r] << "\n";);
}

/**
   \brief Compress T rows
*/
template<typename NM>
void lu<NM>::compress_rows() {
    unsigned_vector new_indr;
    for (unsigned r = 0; r < m_sz; r++) {
        unsigned begin = T.begr[r];
        unsigned end   = T.endr[r];
        T.begr[r] = new_indr.size();
        for (unsigned i = begin; i < end; i++) {
            new_indr.push_back(T.indr[i]);
        }
        T.endr[r] = new_indr.size();
        unsigned fillin = T.endr[r] - T.begr[r];
        for (unsigned i = 0; i < fillin; i++)
            T.indr.push_back(UINT_MAX);
    }
    T.indr.swap(new_indr);
    TRACE("lu_bug", tout << "compressed rows\n";);
    CASSERT("lu", check_T());
}

/**
   \brief Compress T columns
*/
template<typename NM>
void lu<NM>::compress_columns() {
    CASSERT("lu", check_T());
    unsigned_vector new_indc; 
    numeral_vector  new_A;
    for (unsigned c = 0; c < m_sz; c++) {
        unsigned begin = T.begc[c];
        unsigned end   = T.endc[c];
        T.begc[c] = new_indc.size();
        for (unsigned i = begin; i < end; i++) {
            new_A.push_back(numeral());
            m().swap(new_A.back(), T.A[i]);
            new_indc.push_back(T.indc[i]);
        }
        T.endc[c] = new_indc.size();
        unsigned fillin = T.endc[c] - T.begc[c];
        for (unsigned i = 0; i < fillin; i++)
            T.indc.push_back(UINT_MAX);
    }
    T.indc.swap(new_indc);
    T.A.swap(new_A);
    // I don't need to delete the elements of new_A, since I did not use m().set, but m().swap.
    TRACE("lu_bug", tout << "compressed columns\n";);
    CASSERT("lu", check_T());
}

template<typename NM>
void lu<NM>::compress_if_needed() {
    if (T.indr.size() > COMPRESSION_FACTOR * T.num_entries)
        compress_rows();
    if (T.indc.size() > COMPRESSION_FACTOR * T.num_entries)
        compress_columns();
    CASSERT("lu", check_lenr() && check_lenc());
}

template<typename NM>
void lu<NM>::add_row_entry(unsigned r, unsigned c) {
    if (T.endr[r] == T.indr.size()) {
        // expand last row
        T.indr.push_back(c);
        T.endr[r]++;
        SASSERT(T.endr[r] == T.indr.size());
    }
    else {
        if (T.indr[T.endr[r]] != UINT_MAX)
            move_row_to_end(r);
        // use free space
        SASSERT(T.indr[T.endr[r]] == UINT_MAX);
        T.indr[T.endr[r]] = c;
        T.endr[r]++;
    }
}

template<typename NM>
void lu<NM>::add_col_entry(unsigned r, unsigned c, numeral const & a) {
    if (T.endc[c] == T.indc.size()) {
        // expand last column
        T.A.push_back(numeral());
        m().set(T.A.back(), a);
        T.indc.push_back(r);
        T.endc[c]++;
        SASSERT(T.endc[c] == T.indc.size());
    }
    else {
        if (T.indc[T.endc[c]] != UINT_MAX)
            move_col_to_end(c);
        SASSERT(T.indc[T.endc[c]] == UINT_MAX);
        // use free space
        unsigned pos = T.endc[c];
        m().set(T.A[pos], a);
        T.indc[pos] = r;
        T.endc[c]++;
    }
}

template<typename NM>
void lu<NM>::process_pivot_core(unsigned r, unsigned c) {
    SASSERT(m_todo_cols.len(c) > 0);
    if (m_todo_cols.len(c) == 1) {
        // simple case... just update lenc for every c_prime != c in r.
        unsigned begin = T.begr[r];
        unsigned end   = T.endr[r];
        for (unsigned k = begin; k < end; k++) {
            unsigned c_prime = T.indr[k];
            if (c_prime != c) {
                SASSERT(enabled_col(c_prime));
                dec_lenc(c_prime); 
            }
        }
        return;
    }

#ifdef Z3DEBUG
    unsigned num_set_locw = 0;
#endif
    // Compute multipliers and update L
    m_toadd_rows.reset();
    unsigned begin = T.begc[c];
    unsigned end   = T.endc[c];
    for (unsigned k = begin; k < end; k++) {
        unsigned r_prime = T.indc[k];
        if (r_prime == r) {
            SASSERT(m().eq(A_best, T.A[k]));
            continue;
        }

        if (!enabled_row(r_prime))
            continue;
        
        // mu_1 = - A_(r_prime, c) / A_(r,c)
        m().set(mu_1, T.A[k]);
        m().div(mu_1, A_best, mu_1);
        // hack: mu_1 contains A_(r_prime, c) / A_(r,c) at this point
        // since we have to store -mu_1 in L
        // store (- mu_1, r_prime, r) in L
        L.A.push_back(numeral());
        m().set(L.A.back(), mu_1);
        // r_prime is the row being updated
        // with r_prime += mu_1 * r
        L.indc.push_back(r_prime);
        L.indr.push_back(r);
        
        m().neg(mu_1);
        // Now, mu_1 contains -A_(r_prime, c) / A_(r,c)

        // little hack: temporarily store mu_1 at T.A[k] and save position at locw
        m().set(T.A[k], mu_1);
        locw[r_prime] = k;
        DEBUG_CODE(num_set_locw++;);
        m_toadd_rows.push_back(r_prime);

        SASSERT(T_row_contains(r_prime, c));
        // decrement the length of the row since column c will be removed.
        dec_lenr(r_prime);

        // the row entry (r_prime, c) is actually removed by del_disabled_cols
        T.num_entries--;
    }
    
    // Update every non-zero column of r different from c.
    begin = T.begr[r];
    end   = T.endr[r];
    TRACE("dec_len_bug", tout << "row r: " << r << ", begin: " << begin << ", end: " << end << "\n";);
    for (unsigned k = begin; k < end; k++) {
        unsigned c_prime = T.indr[k];
        TRACE("dec_len_bug", tout << "processing c_prime: " << c_prime << ", c: " << c << "\n";);
        if (c_prime == c)
            continue;
        // The row is going to be disabled, so decrementing length of c_prime from r.
        // Remark: don't need to do that for c, since it will be disabled.
        dec_lenc(c_prime); 
        TRACE("dec_len_bug", tout << "c_prime: " << c_prime << ", lenc[c_prime] : " << m_todo_cols.len(c_prime) << "\n";);
        
        SASSERT(enabled_col(c_prime));
        unsigned begin2 = T.begc[c_prime];
        unsigned end2   = T.endc[c_prime];
        // Find coefficient of (r, c_prime) and store it in A_aux
        for (unsigned i = begin2; true; i++) {
            SASSERT(i < end2);
            if (T.indc[i] == r) {
                m().set(A_aux, T.A[i]);
                break;
            }
        }
        
        // Update column
        unsigned j      = begin2;
        for (unsigned i = begin2; i < end2; i++) {
            unsigned r_prime = T.indc[i];
            if (r_prime == r  // row r is not going to be modified
                || !enabled_row(r_prime)  // row was already processed (i.e., it is already in the triangular part)
                || locw[r_prime] == UINT_MAX // row is not being updated
                ) {
                if (i != j) {
                    T.indc[j] = T.indc[i];
                    m().set(T.A[j], T.A[i]);
                    T.indc[i] = UINT_MAX;
                }
                j++;
                continue;
            }
            // mark row as visited
            m_marked_rows[r_prime] = true;
            // update T.A[j] with T.A[i] + mu_1 * A_aux, 
            // where mu_1 is stored at T.A[locw[r_prime]]
            m().addmul(T.A[i], T.A[locw[r_prime]], A_aux, T.A[j]);
            T.indc[j] = T.indc[i];
            if (i != j) 
                T.indc[i] = UINT_MAX;
            if (m().is_zero(T.A[j])) {
                // entry was canceled
                dec_lenr(r_prime);
                dec_lenc(c_prime);
                T.indc[j] = UINT_MAX;
                del_row_entry(r_prime, c_prime);
                T.num_entries--;
            }
            else {
                j++;
            }
        }
        
        T.endc[c_prime] = j;
        // Process rows that were not visited.
        unsigned num = m_toadd_rows.size();
        for (unsigned i = 0; i < num; i++) {
            unsigned r_prime = m_toadd_rows[i];
            if (m_marked_rows[r_prime]) {
                // row was already added
                m_marked_rows[r_prime] = false;
                continue;
            }
            // add entry (r_prime, c_prime) with coefficient mu_1 * A_aux
            // where mu_1 is stored at T.A[locw[r_prime]]
            add_row_entry(r_prime, c_prime);
            m().mul(T.A[locw[r_prime]], A_aux, tmp);
            add_col_entry(r_prime, c_prime, tmp);
            inc_lenr(r_prime);
            inc_lenc(c_prime);
            T.num_entries++;
        }
    }
    
    // Reset column c
    begin = T.begc[c];
    end   = T.endc[c];
    unsigned j = begin;
    for (unsigned k = begin; k < end; k++) {
        unsigned r_prime = T.indc[k];
        if (r_prime == r || !enabled_row(r_prime)) {
            if (j != k) {
                T.indc[j] = T.indc[k];
                m().set(T.A[j], T.A[k]);
                T.indc[k] = UINT_MAX;
            }
            j++;
            continue;
        }
        SASSERT(locw[r_prime] != UINT_MAX);
        locw[r_prime] = UINT_MAX;
        DEBUG_CODE(num_set_locw--;);
    }
    SASSERT(num_set_locw == 0);
    T.endc[c] = j;
}    

template<typename NM>
void lu<NM>::process_pivot(unsigned i, unsigned r, unsigned c) {
    CASSERT("lu", check_locw());
    del_disabled_cols(r);
    SASSERT(T.begr[r] < T.endr[r]);
    process_pivot_core(r, c);
    
    m_todo_rows.erase(r);
    m_todo_cols.erase(c);
    m_enabled_rows[r] = false;
    m_enabled_cols[c] = false;

    P.swap(i, P.inv(r));
    Q.swap(i, Q.inv(c));
    CASSERT("lu", check_locw());
}

template<typename NM>
void lu<NM>::copy_T_to_U() {
    U.num_entries = T.num_entries;
    U.begr.resize(m_sz);
    U.endr.resize(m_sz);
    // reserve space for each row
    unsigned pos = 0;
    for (unsigned r = 0; r < m_sz; r++) {
        U.begr[r] = pos;
        U.endr[r] = pos;
        unsigned r_sz = T.endr[r] - T.begr[r];
        pos += r_sz;
        pos += fillin_for(r_sz);
    }
    U.A.resize(pos);
    U.indr.resize(pos, UINT_MAX);

    // fill rows
    for (unsigned c = 0; c < m_sz; c++) {
        unsigned c_prime = Q(c);  // make sure the first element in each row is the pivot;
        unsigned begin   = T.begc[c_prime];
        unsigned end     = T.endc[c_prime];
        CTRACE("lu_bug", end < begin + 1 || end > begin + c + 1,
               tout << "begin: " << begin << ", end: " << end << ", c: " << c << ", c_prime: " << c_prime << "\n";
               display_T(tout); tout << "P: " << P << "\nQ: " << Q << "\n";); 
        SASSERT(end >= begin + 1);
        SASSERT(end <= begin + c + 1);
        for (unsigned t_idx = begin; t_idx < end; t_idx++) {
            unsigned r     = T.indc[t_idx];
            unsigned u_idx = U.endr[r];
            SASSERT(U.indr[u_idx] == UINT_MAX);
            m().swap(U.A[u_idx], T.A[t_idx]);
            U.indr[u_idx] = c_prime;
            U.endr[r]++;
        }
    }
    
    SASSERT(check_U());
}

template<typename NM>
void lu<NM>::fact() {
    SASSERT(!ini);
    TRACE("fact", display_T(tout););
    init_fact();
    
    CASSERT("lu", check_lenr() && check_lenc());
    unsigned r, c;
    for (unsigned i = 0; i < m_sz; i++) {
        select_pivot(r, c);

        TRACE("lu_pivot", tout << "pivot: " << r << " " << c << "\n";);

        process_pivot(i, r, c);

        TRACE("lu_pivot", tout << "P: " << P << "\nQ: " << Q << "\n";);
        CASSERT("lu", check_lenr() && check_lenc());

        TRACE("lu_pivot_detail", display_T(tout););
        compress_if_needed();
    }
    copy_T_to_U();
}

// During factorization, the following invariant must hold.
// For every row r,  enabled_row(r) => m_todo_rows.len(r) == number of enabled columns in r.
// For every column c, enabled_col(c) => m_todo_cols.len(c) == number of enabled rows in c.

template<typename NM>
bool lu<NM>::check_lenr() const {
    for (unsigned r = 0; r < m_sz; r++) {
        if (enabled_row(r)) {
            unsigned len = 0;
            unsigned begin = T.begr[r];
            unsigned end   = T.endr[r];
            for (unsigned k = begin; k < end; k++) {
                unsigned c = T.indr[k];
                CTRACE("lu_bug", c == UINT_MAX, tout << "r: " << r << ", c: " << c << "\n";);
                if (enabled_col(c))
                    len++;
            }
            CTRACE("lu_bug", m_todo_rows.len(r) != len, tout << "failed for row: " << r << " len: " << len << " lenr[r]: " << m_todo_rows.len(r) << "\n"; 
                   display_T(tout);); 
            SASSERT(m_todo_rows.len(r) == len);
        }
    }
    return true;
}

template<typename NM>
bool lu<NM>::check_lenc() const {
    for (unsigned c = 0; c < m_sz; c++) {
        if (enabled_col(c)) {
            unsigned len = 0;
            unsigned begin = T.begc[c];
            unsigned end   = T.endc[c];
            for (unsigned k = begin; k < end; k++) {
                unsigned r = T.indc[k];
                if (enabled_row(r))
                    len++;
            }
            CTRACE("lu_bug", m_todo_cols.len(c) != len, tout << "failed for column: " << c << " len: " << len << " lenc[c]: " 
                   << m_todo_cols.len(c) << "\n"; display_T(tout);); 
            SASSERT(m_todo_cols.len(c) == len);
        }
    }
    return true;
}

// -----------------------
//
// Invariants
//
// -----------------------

template<typename NM>
bool lu<NM>::check_P() const {
    SASSERT(P.check_invariant());
    return true;
}

template<typename NM>
bool lu<NM>::check_Q() const {
    SASSERT(Q.check_invariant());
    return true;
}
    
template<typename NM>
bool lu<NM>::check_L() const {
    SASSERT(L.A.size() == L.indc.size());
    SASSERT(L.A.size() == L.indr.size());
    for (unsigned i = 0; i < L.A.size(); i++) {
        SASSERT(L.indc[i] < m_sz);
        SASSERT(L.indr[i] < m_sz);
    }
    return true;
}

template<typename NM>
bool lu<NM>::check_U() const {
    unsigned num_entries = 0;
    SASSERT(U.begr.size() == m_sz); 
    SASSERT(U.endr.size() == m_sz);
    for (unsigned r = 0; r < m_sz; r++) {
        SASSERT(U.begr[r] <= U.endr[r]);
        SASSERT(U.endr[r] <= U.A.size());
        for (unsigned j = U.begr[r]; j < U.endr[r]; j++) {
            num_entries++;
            unsigned c = U.indr[j];
            SASSERT(c < m_sz); // valid variable/column
            // it is really upper triangular
            CTRACE("lu_bug", Q.inv(c) < P.inv(r), 
                   tout << "c: " << c << ", r: " << r << ", Q.inv(c): " << Q.inv(c) << ", P.inv(r): " << P.inv(r) << "\n"; display_U(tout););
            SASSERT(Q.inv(c) >= P.inv(r));
        }
    }
    SASSERT(num_entries == U.num_entries);
    return true;
}

/**
   \brief Return true if the T column c contains a reference to row r.
*/
template<typename NM>
bool lu<NM>::T_col_contains(unsigned c, unsigned r) const {
    for (unsigned i = T.begc[c]; i < T.endc[c]; i++)
        if (T.indc[i] == r)
            return true;
    return false;
}

/**
   \brief Return true if the T row r contains a reference to column c.
*/
template<typename NM>
bool lu<NM>::T_row_contains(unsigned r, unsigned c) const {
    for (unsigned i = T.begr[r]; i < T.endr[r]; i++)
        if (T.indr[i] == c)
            return true;
    return false;
}

template<typename NM>
bool lu<NM>::check_T() const {
    SASSERT(T.begr.size() == m_sz);
    SASSERT(T.endr.size() == m_sz);

    SASSERT(T.A.size() == T.indc.size());
    SASSERT(T.begc.size() == m_sz);
    SASSERT(T.endc.size() == m_sz);

    for (unsigned i = 0; i < m_sz; i++) {
        SASSERT(T.begr[i] <= T.endr[i]);
        SASSERT(T.endr[i] <= T.indr.size());
        for (unsigned j = T.begr[i]; j < T.endr[i]; j++) {
            if (enabled_col(T.indr[j])) {
                SASSERT(T.indr[j] < m_sz);
                SASSERT(T_col_contains(T.indr[j], i));
            }
        }

        SASSERT(T.begc[i] <= T.endc[i]);
        SASSERT(T.endc[i] <= T.indc.size());
        for (unsigned j = T.begc[i]; j < T.endc[i]; j++) {
            if (enabled_row(T.indc[j])) {
                SASSERT(T.indc[j] < m_sz);
                CTRACE("lu_bug", !T_row_contains(T.indc[j], i), tout << "T.indc[j]: " << T.indc[j] << ", i: " << i << "\n"; display_T(tout););
                SASSERT(T_row_contains(T.indc[j], i));
            }
        }
    }
    return true;
}

template<typename NM>
bool lu<NM>::check_invariant() const {
    SASSERT(check_P());
    SASSERT(check_Q());
    if (!ini) {
        SASSERT(check_L());
        SASSERT(check_U());
    }
    SASSERT(locw.size() == m_sz);
    return true;
}

template<typename NM>
void lu<NM>::display_T(std::ostream & out) const {
    for (unsigned r = 0; r < m_sz; r++) {
        unsigned begin_r = T.begr[r];
        unsigned end_r   = T.endr[r];
        for (unsigned j = begin_r; j < end_r; j++) {
            unsigned c = T.indr[j];
            if (j > begin_r)
                out << " ";
            unsigned begin_c = T.begc[c];
            unsigned end_c   = T.endc[c];
            unsigned i;
            for (i = begin_c; i < end_c; i++) {
                if (T.indc[i] == r) {
                    // found coeff
                    out << m().to_string(T.A[i]) << "*x" << c;
                    break;
                }
            }
            if (i == end_c) {
                out << "<deleted>*x" << c;
            }
        }
        out << "\n";
    }
}

template<typename NM>
void lu<NM>::display_U(std::ostream & out, unsigned_vector const * var_ids) const {
    out << "U:\n";
    for (unsigned i = 0; i < m_sz; i++) {
        unsigned begin = U.begr[i];
        unsigned end   = U.endr[i];
        for (unsigned j = begin; j < end; j++) {
            if (j > begin)
                out << " ";
            out << m().to_string(U.A[j]) << "*x";
            if (var_ids) 
                out << (*var_ids)[U.indr[j]];
            else
                out << U.indr[j];
        }
        out << "\n";
    }
}

template<typename NM>
void lu<NM>::display_L(std::ostream & out) const {
    out << "L: ";
    unsigned sz = L.A.size();
    for (unsigned i = 0; i < sz; i++) {
        out << "(" << L.indc[i] << ", " << L.indr[i] << ", " << m().to_string(L.A[i]) << ")";
    }
    out << "\n";
}

template<typename NM>
void lu<NM>::display(std::ostream & out, unsigned_vector const * var_ids) const {
    out << "P: " << P << "\n";
    out << "Q: " << Q << "\n";
    display_U(out, var_ids);
    display_L(out);
}

template<typename NM>
lu<NM>::dense_vector::dense_vector(manager & m, unsigned sz):
    m_manager(m) {
    m_in_non_zeros.resize(sz, false);
    m_values.resize(sz);
}

template<typename NM>
lu<NM>::dense_vector::~dense_vector() {
    reset();
}

template<typename NM>
void lu<NM>::dense_vector::reset() {
    iterator it  = begin_non_zeros();
    iterator end = end_non_zeros();
    for (; it != end; ++it) {
        m().reset(m_values[*it]);
        m_in_non_zeros[*it] = false;
    }
    m_non_zeros.reset();
}

template<typename NM>
void lu<NM>::dense_vector::reset(unsigned new_sz) {
    reset();
    m_in_non_zeros.resize(new_sz, false);
    m_values.resize(new_sz);
}

template<typename NM>
void lu<NM>::solve_Lx_eq_y(dense_vector & y) {
    TRACE("lu_solve", tout << "before: Lx = y\n"; y.display(tout); tout << "\n";);
    SASSERT(y.size() == m_sz); // compatible size
    SASSERT(&(y.m()) == &(m())); // same manager
    unsigned sz = L.A.size();
    unsigned k  = 0;
    while (k < sz) {
        TRACE("Lx_eq_y", tout << "(" << L.indc[k] << " " << L.indr[k] << " " << m().to_string(L.A[k]) << ")\n"; y.display(tout); tout << "\n";);
        unsigned j_k = L.indr[k]; // L.indr contains column numbers. 
        numeral const & y_j = y[j_k];
        if (m().is_zero(y_j)) {
            for (; k < sz && L.indr[k] == j_k; k++) 
                ;
            continue;
        }
        numeral const & mu_k = L.A[k];
        unsigned i_k = L.indc[k]; // L.indc contains row numbers
        numeral & y_i = y.get(i_k);
        m().submul(y_i, mu_k, y_j, y_i);
        k++;
    }
    TRACE("lu_solve", tout << "after Lx = y\n"; y.display(tout); tout << "\n";);
}

template<typename NM>
void lu<NM>::solve_Ux_eq_y(dense_vector & y) {
    TRACE("lu_solve", tout << "before: Ux = y\n"; y.display(tout); tout << "\n";);
    TRACE("lu_solve_PQ", tout << "P: " << P << "\nQ: " << Q << "\n";);
    // TODO: super-sparse case, where the number of zeros in y is much smaller than m_sz
    SASSERT(y.size() == m_sz); // compatible size
    SASSERT(&(y.m()) == &(m())); // same manager
    numeral delta;
    unsigned i = m_sz;
    dense_vector & x = m_tmp_xU_vector;
    x.reset();
    while (i > 0) {
        --i;
        unsigned i_prime = P(i);
        unsigned j_prime = Q(i);
        unsigned begin   = U.begr[i_prime];
        unsigned end     = U.endr[i_prime];
        TRACE("lu_solve_bug", tout << "i_prime: " << i_prime << ", j_prime: " << j_prime << "\n";
              tout << "y: "; y.display(tout); tout << "\n";
              tout << "x: "; x.display(tout); tout << "\n";);
        SASSERT(end >= begin + 1); // row must be non empty
        CTRACE("lu_bug", U.indr[begin] != j_prime, tout << "i: " << i << ", i_prime: " << i_prime << ", j_prime: " << j_prime 
               << ", U.indr[begin]: " << U.indr[begin] << "\n"; display_U(tout););
        SASSERT(U.indr[begin] == j_prime);  // j_prime must be in the first position
        if (end == begin + 1) {
            // row of size one
            if (m().is_zero(y[i_prime]))
                continue;
            numeral & x_j = x.get(j_prime);
            m().div(y[i_prime], U.A[begin], x_j);
        }
        else {
            // row has at least two elements.
            SASSERT(end > begin + 1);
            numeral const & a = U.A[begin];
            m().reset(delta);
            for (unsigned k = begin+1; k < end; k++) {
                unsigned c   = U.indr[k];
                TRACE("lu_solve_bug", tout << "c: " << c << ", x[c]: " << m().to_string(x[c]) << ", delta: " << m().to_string(delta) << "\n";);
                m().addmul(delta, U.A[k], x[c], delta);
            }
            if (m().is_zero(delta) && m().is_zero(y[i_prime]))
                continue;
            numeral & x_j = x.get(j_prime);
            m().sub(y[i_prime], delta, x_j);
            m().div(x_j, a, x_j);
        }
    }
    y.swap(x);
    m().del(delta);
    TRACE("lu_solve", tout << "after: Ux = y\n"; y.display(tout); tout << "\n";);
}

template<typename NM>
void lu<NM>::solve_xL_eq_y(dense_vector & y) {
    TRACE("lu_solve", tout << "before: xL = y\n"; y.display(tout); tout << "\n";);
    SASSERT(y.size() == m_sz); // compatible size
    SASSERT(&(y.m()) == &(m())); // same manager
    unsigned k = L.A.size();
    while (k > 0) {
        --k;
        unsigned i_k = L.indc[k];
        numeral const & y_i = y[i_k];
        if (m().is_zero(y_i))
            continue;
        numeral const & mu_k = L.A[k];
        unsigned j_k = L.indr[k];
        numeral & y_j = y.get(j_k);
        m().submul(y_j, mu_k, y_i, y_j);
    }
    TRACE("lu_solve", tout << "after: xL = y\n"; y.display(tout); tout << "\n";);
}
    
template<typename NM>
void lu<NM>::solve_xU_eq_y(dense_vector & y) {
    // TODO: super-sparse case, where the number of zeros in y is much smaller than m_sz
    TRACE("lu_solve", tout << "before: xU = y\n"; y.display(tout); tout << "\n";);
    TRACE("lu_solve_PQ", tout << "P: " << P << "\nQ: " << Q << "\n";);
    SASSERT(y.size() == m_sz); // compatible size
    SASSERT(&(y.m()) == &(m())); // same manager
    dense_vector & x = m_tmp_xU_vector;
    x.reset();
    for (unsigned i = 0; i < m_sz; i++) {
        unsigned i_prime = P(i);
        unsigned j_prime = Q(i);
        TRACE("lu_solve_step", tout << "i: " << i << ", P(i): " << P(i) << ", Q(i): " << Q(i) << ", x: "; x.display(tout); 
              tout << ", y[j_prime]: " << m().to_string(y[j_prime]) << "\n";);
        if (!m().is_zero(y[j_prime])) {
            numeral & x_i    = x.get(i_prime);
            m().add(x_i, y[j_prime], x_i);
        }
        if (m().is_zero(x[i_prime]))
            continue;
        numeral & x_i    = x.get(i_prime);
        unsigned begin   = U.begr[i_prime];
        unsigned end     = U.endr[i_prime];
        SASSERT(end >= begin + 1); // row must be non empty
        SASSERT(U.indr[begin] == j_prime);
        numeral const & a = U.A[begin];
        m().div(x_i, a, x_i);
        for (unsigned k = begin+1; k < end; k++) {
            // propagate x_i
            unsigned c    = U.indr[k];
            numeral & x_j = x.get(P(Q.inv(c)));
            m().submul(x_j, U.A[k], x_i, x_j);
        }
    }
    TRACE("lu_solve_step", tout << "x: "; x.display(tout); tout << "\n";);
    y.swap(x);
    TRACE("lu_solve", tout << "after: xU = y\n"; y.display(tout); tout << "\n";);
}

// -----------------------
//
// Column replacement
//
// -----------------------

/**
   \brief Remove colum c from U row r. 
*/
template<typename NM>
void lu<NM>::del_U_row_entry(unsigned r, unsigned c) {
    unsigned begin = U.begr[r];
    unsigned end   = U.endr[r];
    TRACE("del_row_entry", tout << "del_U_row_entry, r: " << r << ", c: " << c << ", begin: " << begin << ", end: " << end << "\n";);
    for (unsigned i = begin; i < end; i++) {
        unsigned c_prime = U.indr[i];
        if (c_prime == c) {
            U.num_entries--;
            i++;
            for (; i < end; i++) {
                U.indr[i-1] = U.indr[i];
                m().swap(U.A[i-1], U.A[i]);
            }
            U.indr[end-1] = UINT_MAX; // mark as free
            U.endr[r] = end-1;
            return;
        }
    }
}

/**
   \brief Compress U rows
*/
template<typename NM>
void lu<NM>::compress_U_rows() {
    unsigned_vector new_indr;
    numeral_vector  new_A;
    for (unsigned r = 0; r < m_sz; r++) {
        unsigned begin = U.begr[r];
        unsigned end   = U.endr[r];
        U.begr[r] = new_indr.size();
        for (unsigned i = begin; i < end; i++) {
            new_A.push_back(numeral());
            m().swap(new_A.back(), U.A[i]);
            new_indr.push_back(U.indr[i]);
        }
        U.endr[r] = new_indr.size();
        unsigned fillin = U.endr[r] - U.begr[r];
        for (unsigned i = 0; i < fillin; i++)
            U.indr.push_back(UINT_MAX);
    }
    U.indr.swap(new_indr);
    U.A.swap(new_A);
    TRACE("lu_bug", tout << "compressed U rows\n";);
    CASSERT("lu", check_U());
}

template<typename NM>
void lu<NM>::compress_U_if_needed() {
    if (U.indr.size() > COMPRESSION_FACTOR * U.num_entries) {
        compress_U_rows();
        CASSERT("lu", check_U());
    }
}

template<typename NM>
void lu<NM>::move_U_row_to_end(unsigned r) {
    unsigned begin = U.begr[r];
    unsigned end   = U.endr[r];
    U.begr[r]  = U.indr.size();
    U.endr[r]  = U.begr[r] + end - begin;
    for (unsigned j = begin; j < end; j++) {
        U.A.push_back(numeral());
        m().swap(U.A.back(), U.A[j]);
        unsigned c = U.indr[j];
        U.indr.push_back(c);
        U.indr[j] = UINT_MAX; // mark as free
    }
    unsigned sz = end - begin;
    unsigned fillin = fillin_for(sz);
    for (unsigned i = 0; i < fillin; i++) {
        U.A.push_back(numeral());
        U.indr.push_back(UINT_MAX);
    }
}

template<typename NM>
void lu<NM>::add_U_row_entry(unsigned r, unsigned c, numeral const & a) {
    TRACE("add_U_row_entry", tout << "r: " << r << ", c: " << c << ", a: " << m().to_string(a) << " row:\n";
          for (unsigned i = U.begr[r]; i < U.endr[r]; i++) tout << m().to_string(U.A[i]) << "*x" << U.indr[i] << " "; tout << "\n";);
    U.num_entries++;
    if (U.endr[r] == U.indr.size()) {
        // expand last row
        U.A.push_back(numeral());
        m().set(U.A.back(), a);
        U.indr.push_back(c);
        U.endr[r]++;
        SASSERT(U.endr[r] == U.indr.size());
    }
    else {
        if (U.indr[U.endr[r]] != UINT_MAX)
            move_U_row_to_end(r);
        // use free space
        SASSERT(U.indr[U.endr[r]] == UINT_MAX);
        unsigned pos = U.endr[r];
        m().set(U.A[pos], a);
        U.indr[pos] = c;
        U.endr[r]++;
    }
}

/**
   \brief Remove colum c from U row r. 
*/
template<typename NM>
void lu<NM>::add_replace_U_row_entry(unsigned r, unsigned c, numeral const & a) {
    unsigned begin = U.begr[r];
    unsigned end   = U.endr[r];
    TRACE("del_row_entry", tout << "replace_U_row_entry, r: " << r << ", c: " << c << ", begin: " << begin << ", end: " << end << "\n";);
    for (unsigned i = begin; i < end; i++) {
        unsigned c_prime = U.indr[i];
        if (c_prime == c) {
            m().set(U.A[i], a);
            return;
        }
    }
    add_U_row_entry(r, c, a);
}

/**
   \brief Just replace the column. After the replacement PUQ is not triangular anymore.
*/
template<typename NM>
unsigned lu<NM>::replace_U_column_core(unsigned j, dense_vector & new_col) {
    unsigned max = 0;
    // Traverse rows in pivotal order, removing/updating entries.
    // We can stop at Q.inv(j) because:
    //   For every entry (r,c) in U  Q.inv(c) >= P.inv(r)
    //   Thus j does not occur in any r' such that Q.inv(j) < P.inv(r')
    unsigned stop_at = Q.inv(j);
    for (unsigned i = 0; i <= stop_at; i++) {
        unsigned r = P(i);
        if (m().is_zero(new_col[r])) {
            del_U_row_entry(r, j);
        }
        else {
            max = i;
            // replace/add
            add_replace_U_row_entry(r, j, new_col[r]);
            // reset entry in new_col
            numeral & v = new_col.get(r);
            m().reset(v);
        }
    }

    // Add remaining rows of new_col to U
    unsigned_vector::const_iterator it  = new_col.begin_non_zeros();
    unsigned_vector::const_iterator end = new_col.m_non_zeros.end();
    for (; it != end; ++it) {
        unsigned r = *it;
        if (m().is_zero(new_col[r]))
            continue;
        if (P.inv(r) > max)
            max = P.inv(r);
        add_U_row_entry(r, j, new_col[r]);
    }
    return max;
}

/**
   \brief Return true if PUQ is triangular with the exception of column c_prime.
*/
template<typename NM>
bool lu<NM>::check_U_except_col(unsigned c_prime) const {
    for (unsigned r = 0; r < m_sz; r++) {
        for (unsigned j = U.begr[r]; j < U.endr[r]; j++) {
            unsigned c = U.indr[j];
            if (c == c_prime)
                continue;
            SASSERT(Q.inv(c) >= P.inv(r));
        }
    }
    return true;
}

/**
   \brief Return true if PUQ is triangular with the exception of row r_prime.
*/
template<typename NM>
bool lu<NM>::check_U_except_row(unsigned r_prime) const {
    for (unsigned r = 0; r < m_sz; r++) {
        if (r == r_prime)
            continue;
        for (unsigned j = U.begr[r]; j < U.endr[r]; j++) {
            unsigned c = U.indr[j];
            SASSERT(Q.inv(c) >= P.inv(r));
        }
    }
    return true;
}

template<typename NM>
void lu<NM>::replace_U_column(unsigned j, dense_vector & new_col) {
    TRACE("lu_replace", tout << "replacing U column j: " << j << " with\n"; new_col.display_non_zeros(tout); tout << "\n";);
    unsigned k = replace_U_column_core(j, new_col);
    if (k <= Q.inv(j)) {
        TRACE("lu_replace", tout << "result 1:\n"; display(tout););
        CASSERT("lu", check_U());
        if (m().is_zero(U.A[U.begr[P(Q.inv(j))]]))
            throw lu_exception("bad new column"); // column does not have the pivot.
        return; 
    }

    TRACE("lu_replace", tout << "after replace_core:\n"; display_U(tout);
          tout << "P: " << P << "\n"; tout << "Q: " << Q << "\n";
          tout << "Q.inv(j): " << Q.inv(j) << ", k: " << k << "\n";);

    // fix spike at j
    CASSERT("lu", check_U_except_col(j));
    P.move_after(Q.inv(j), k);
    Q.move_after(Q.inv(j), k);

    TRACE("lu_replace", tout << "P: " << P << "\n"; tout << "Q: " << Q << "\n";);

    // fix row P_k
    unsigned P_k = P(k);
    unsigned Q_k = Q(k);
    CASSERT("lu", check_U_except_row(P_k));
    
    // 1. search for smallest bad column
    unsigned smallest = k;
    unsigned begin    = U.begr[P_k];
    unsigned end      = U.endr[P_k];
    for (unsigned i = begin; i < end; i++) {
        unsigned c = U.indr[i];
        unsigned inv_c = Q.inv(c);
        if (inv_c < smallest)
            smallest = inv_c;
    }

    if (smallest == k) {
        // nothing to be done
        TRACE("lu_replace", tout << "result 2:\n"; display(tout););
        if (m().is_zero(U.A[U.begr[P_k]]))
            throw lu_exception("bad new column"); // column does not have the pivot.
        CASSERT("lu", check_U());
        return; 
    } 

    // 2. eliminate bad columns using other rows.
    // 2.a. save coefficients in tmp dense vector
    dense_vector & row_k = m_tmp_replace_column_vector;
    row_k.reset();
    begin = U.begr[P_k];
    end   = U.endr[P_k];
    for (unsigned i = begin; i < end; i++) {
        unsigned c = U.indr[i];
        U.indr[i] = UINT_MAX; // mark as free
        numeral & a = row_k.get(c);
        m().swap(a, U.A[i]);
    }
    U.num_entries -= end - begin;
    U.endr[P_k] = begin;
    
    // 2.b eliminate columns in m_to_fix from P_k
    for (; smallest < k; smallest++) {
        unsigned c  = Q(smallest);
        numeral const & a_k = row_k[c];
        if (m().is_zero(a_k))
            continue;
        
        // use row r to eliminate c
        unsigned r  = P(Q.inv(c));
        SASSERT(U.indr[U.begr[r]] == c);
        numeral const & a_r = U.A[U.begr[r]];
        
        // to eliminate c from k, we must add (-a_k/a_r * r) to row_k
        // Save transformation at L
        m().set(mu_1, a_k);
        m().div(mu_1, a_r, mu_1);
        L.A.push_back(numeral());
        m().set(L.A.back(), mu_1);
        L.indc.push_back(P_k);
        L.indr.push_back(r);
        m().neg(mu_1);
        // k += mu_1 * r
        begin = U.begr[r];
        end   = U.endr[r];
        for (unsigned i = begin; i < end; i++) {
            unsigned c_prime = U.indr[i];
            numeral & a_prime  = row_k.get(c_prime);
            if (c_prime == c)
                m().reset(a_prime);
            else
                m().addmul(a_prime, mu_1, U.A[i], a_prime);
        }
    }

    CTRACE("lu_bug", m().is_zero(row_k[Q_k]), row_k.display_non_zeros(tout); tout << "\n";); 

    // 2.c Copy row_k back to U
    SASSERT(!NM::precise() || !m().is_zero(row_k[Q_k]));
    if (m().is_zero(row_k[Q_k]))
        throw lu_exception("singular matrix");
    
    // Add pivot first
    SASSERT(U.begr[P_k] == U.endr[P_k]); // the row k in U is empty
    add_U_row_entry(P_k, Q_k, row_k[Q_k]);
    
    // Copy remaining elements
    typename dense_vector::iterator it3  = row_k.begin_non_zeros();
    typename dense_vector::iterator end3 = row_k.end_non_zeros();
    for (; it3 != end3; ++it3) {
        unsigned c = *it3;
        if (c == Q_k)
            continue; // already added
        if (m().is_zero(row_k[c]))
            continue;
        add_U_row_entry(P_k, c, row_k[c]);
    }
    
    TRACE("lu_replace", tout << "result 3:\n"; display(tout););
    CASSERT("lu", check_U());
    compress_U_if_needed();
}

template<typename NM>
void lu<NM>::replace_column(unsigned j, dense_vector & new_col) {
    TRACE("lu_replace", tout << "replacing column j: " << j << " with\n"; new_col.display_non_zeros(tout); tout << "\n";);
    SASSERT(j < m_sz);
    solve_Lx_eq_y(new_col);
    replace_U_column(j, new_col);
    m_num_replacements++;
}

// -----------------------
//
// Dense vector
//
// -----------------------

// Make sure that every position in m_non_zeros really contains a non-zero value.
template<typename NM>
void lu<NM>::dense_vector::elim_zeros() {
    unsigned_vector::iterator it  = m_non_zeros.begin();
    unsigned_vector::iterator end = m_non_zeros.end();
    unsigned_vector::iterator it2 = it;
    for (; it != end; ++it) {
        unsigned idx = *it;
        SASSERT(m_in_non_zeros[idx]);
        if (m().is_zero(m_values[idx])) {
            m().reset(m_values[idx]);
            m_in_non_zeros[idx] = false;
            continue;
        }
        *it2 = idx;
        ++it2;
    }
    m_non_zeros.set_end(it2);
}


template<typename NM>
void lu<NM>::dense_vector::display(std::ostream & out) const {
    out << "(";
    unsigned sz = m_values.size();
    for (unsigned i = 0; i < sz; i++) {
        if (i > 0) out << " ";
        out << m().to_string(m_values[i]);
    }
    out << ")";
}

template<typename NM>
void lu<NM>::dense_vector::display_non_zeros(std::ostream & out) const {
    out << "(";
    bool first = true;
    for (unsigned i = 0; i < m_non_zeros.size(); i++) {
        unsigned pos = m_non_zeros[i];
        if (m().is_zero(m_values[pos]))
            continue;
        if (first) first = false; else out << " ";
        out << m().to_string(m_values[pos]) << ":" << pos;
    }
    out << ")";
}

template<typename NM>
void lu<NM>::dense_vector::display_pol(std::ostream & out) const {
    bool first = true;
    for (unsigned i = 0; i < m_non_zeros.size(); i++) {
        unsigned pos = m_non_zeros[i];
        if (m().is_zero(m_values[pos]))
            continue;
        if (first) first = false; else out << " + ";
        out << m().to_string(m_values[pos]) << "*x" << pos;
    }
}


template class lu<unsynch_mpq_manager>;
template class lu<double_manager>;

