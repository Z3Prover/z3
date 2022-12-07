/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    xor_gaussian.h

Abstract:

    A roughly 1:1 port of CryptoMiniSAT's gaussian elimination datastructures/algorithms

--*/

#pragma once

#include "util/debug.h"
#include "util/sat_literal.h"
#include "util/trace.h"
#include "sat/smt/euf_solver.h"

namespace xr {
    
    typedef sat::literal literal;
    typedef sat::bool_var bool_var;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var_vector bool_var_vector;


    class solver;
    
#ifdef _MSC_VER
    inline int scan_fwd_64b(int64_t value) {
        unsigned long at;
        unsigned char ret = _BitScanForward64(&at, value);
        at++;
        if (!ret) at = 0;
        return at;
    }
#else
    inline int scan_fwd_64b(uint64_t value) {
        return  __builtin_ffsll(value);
    }
#endif

    class justification {
        
        friend class solver;
        
        unsigned m_matrix_idx;
        unsigned m_row_idx;
    
        //XOR
        justification(unsigned matrix_idx, unsigned row_idx):
            m_matrix_idx(matrix_idx),
            m_row_idx(row_idx) {
            SASSERT(matrix_idx != -1);
            SASSERT(row_idx != -1);
        }
        
    public:
        justification() : m_matrix_idx(-1), m_row_idx(-1) {}
        
        void deallocate(small_object_allocator& a) { a.deallocate(get_obj_size(), sat::constraint_base::mem2base_ptr(this)); }
        sat::ext_constraint_idx to_index() const { return sat::constraint_base::mem2base(this); }
        static justification& from_index(size_t idx) { 
            return *reinterpret_cast<justification*>(sat::constraint_base::from_index(idx)->mem());
        }
        static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(justification)); }
    
        unsigned get_matrix_idx() const {
            return m_matrix_idx;
        }
    
        unsigned get_row_idx() const {
            return m_row_idx;
        }
    
        bool isNull() const {
            return m_matrix_idx == -1;
        }
    
        bool operator==(const justification other) const {
            return m_matrix_idx == other.m_matrix_idx && m_row_idx == other.m_row_idx;
        }
    
        bool operator!=(const justification other) const {
            return !(*this == other);
        }
    };
    
    inline std::ostream& operator<<(std::ostream& os, const justification& pb) {
        if (!pb.isNull()) {
            return os << " xor reason, matrix= " << pb.get_matrix_idx() << " row: " << pb.get_row_idx();
        }
        return os << " NULL";
    }
    
    enum class gret : unsigned { confl, prop, nothing_satisfied, nothing_fnewwatch };
    enum class gauss_res : unsigned { none, confl, prop };
    
    struct gauss_watched {
        gauss_watched(unsigned r, unsigned m) : row_n(r) , matrix_num(m) { }
    
        unsigned row_n;        // watch row
        unsigned matrix_num;   // watch matrix
    
        bool operator<(const gauss_watched& other) const {
            if (matrix_num < other.matrix_num)
                return true;
            if (matrix_num > other.matrix_num)
                return false;
            return row_n < other.row_n;
        }
    };
    
    struct gauss_data {
        bool do_eliminate;                                      // we do elimination when basic variable is invoked
        unsigned new_resp_var;                                  // do elimination variable
        unsigned new_resp_row ;                                 // do elimination row
        sat::justification conflict = sat::justification(0);    // returning conflict
        gauss_res status;                                       // status
        unsigned currLevel;                                     // level at which the variable was decided on

        unsigned num_props = 0;                                 // total gauss propagation time for DPLL
        unsigned num_conflicts = 0;                             // total gauss conflict time for DPLL
        unsigned disable_checks = 0;
        bool disabled = false;                                  // decide to do gaussian elimination

        void reset() {
            do_eliminate = false;
            status = gauss_res::none;
        }
    };
    
    struct reason {
        bool m_must_recalc = true;
        literal m_propagated = sat::null_literal;
        unsigned m_ID = 0;
        literal_vector m_reason;
    };
    
    struct xor_clause {
        
        bool m_rhs = false;
        bool_var_vector m_clash_vars;
        bool m_detached = false;
        bool_var_vector m_vars; // inherit from bool_var_vector?
        
        xor_clause() = default;
        xor_clause(const xor_clause& c) = default;        
        xor_clause(xor_clause&& c)  noexcept : m_rhs(c.m_rhs), m_clash_vars(std::move(c.m_clash_vars)), m_detached(c.m_detached), m_vars(std::move(c.m_vars)) { }
        
        ~xor_clause() = default;
        
        xor_clause& operator=(const xor_clause& c) = default;
    
        explicit xor_clause(const unsigned_vector& cl, bool _rhs, bool_var_vector const& _clash_vars) : m_rhs(_rhs), m_clash_vars(_clash_vars) {
            for (auto v : cl)
                m_vars.push_back(v);
        }
    
        template<typename T>
        explicit xor_clause(const T& cl, bool _rhs, bool_var_vector const& _clash_vars) : m_rhs(_rhs), m_clash_vars(_clash_vars) {
            for (auto const& l : cl)
                m_vars.push_back(l.var());
        }
    
        explicit xor_clause(const bool_var_vector& cl, const bool _rhs, unsigned clash_var) : m_rhs(_rhs) {
            m_clash_vars.push_back(clash_var);
            for (auto v : cl)
                m_vars.push_back(v);
        }
        
        unsigned_vector::const_iterator begin() const {
            return m_vars.begin();
        }
    
        unsigned_vector::const_iterator end() const {
            return m_vars.end();
        }
    
        unsigned_vector::iterator begin() {
            return m_vars.begin();
        }
    
        unsigned_vector::iterator end() {
            return m_vars.end();
        }
    
        bool operator<(const xor_clause& other) const {
            for (unsigned i = 0; i < other.size() && i < size(); ++i) 
                if (other[i] != m_vars[i])
                    return m_vars[i] < other[i];
    
            if (other.size() != size()) 
                return size() < other.size();
            
            return false;
        }
    
        const unsigned& operator[](unsigned at) const {
            return m_vars[at];
        }
    
        unsigned& operator[](unsigned at) {
            return m_vars[at];
        }
    
        void shrink(unsigned newsize) {
            m_vars.shrink(newsize);
        }
    
        bool_var_vector& get_vars() {
            return m_vars;
        }
    
        const bool_var_vector& get_vars() const {
            return m_vars;
        }
    
        unsigned size() const {
            return m_vars.size();
        }
    
        bool empty() const {
            if (!m_vars.empty())
                return false;
            if (!m_clash_vars.empty())
                return false;
            return !m_rhs;
        }

        bool is_true() const {
            return empty() && !m_rhs;
        }

        bool is_false() const {
            return empty() && m_rhs;
        }

        // add all elements in other.m_clash_vars that are not yet in m_clash_vars:
        void merge_clash(const xor_clause& other, visit_helper& visited, unsigned num_vars) {
            visited.init_visited(num_vars);
            for (const bool_var& v: m_clash_vars) 
                visited.mark_visited(v);            
    
            for (const auto& v: other.m_clash_vars) {
                if (!visited.is_visited(v)) {
                    visited.mark_visited(v);
                    m_clash_vars.push_back(v);
                }
            }
        }
    };
    
    inline std::ostream& operator<<(std::ostream& os, const xor_clause& thisXor) {
        for (unsigned i = 0; i < thisXor.size(); i++) {
            os << literal(thisXor[i], false);
    
            if (i + 1 < thisXor.size())
                os << " + ";
        }
        os << " =  " << std::boolalpha << thisXor.m_rhs << std::noboolalpha;
    
        os << " -- clash: ";
        for (const auto& c: thisXor.m_clash_vars) 
            os << c + 1 << ", ";        
    
        return os;
    }
    
    class PackedRow {
        
        friend class PackedMatrix;
        friend class EGaussian;

        PackedRow(unsigned _size, int64_t* const _mp) :
            mp(_mp + 1),
            rhs_internal(*_mp), 
            size(_size) {}
       
        int64_t* __restrict const mp;
        int64_t& rhs_internal;
        const int size;
        
    public:
        
        PackedRow() = delete;
        
        PackedRow& operator=(const PackedRow& b) {
            //start from -1, because that's where RHS is
            for (int i = -1; i < size; i++) 
                *(mp + i) = *(b.mp + i);
                
            return *this;
        }
    
        PackedRow& operator^=(const PackedRow& b) {
            //start from -1, because that's where RHS is
            for (int i = -1; i < size; i++) 
                *(mp + i) ^= *(b.mp + i);            
    
            return *this;
        }

        int get_size() const {
            return size;
        }
        
        void set_and(const PackedRow& a, const PackedRow& b) {
            for (int i = 0; i < size; i++) 
                *(mp + i) = *(a.mp + i) & *(b.mp + i);            
        }
    
        unsigned set_and_until_popcnt_atleast2(const PackedRow& a, const PackedRow& b) {
            unsigned pop = 0;
            for (int i = 0; i < size && pop < 2; i++) {
                *(mp + i) = *(a.mp + i) & *(b.mp + i);
                pop += get_num_1bits((uint64_t)*(mp + i));
            }
    
            return pop;
        }
    
        void xor_in(const PackedRow& b) {
            rhs_internal ^= b.rhs_internal;
            for (int i = 0; i < size; i++) 
                *(mp + i) ^= *(b.mp + i);            
        }
    
        const int64_t& rhs() const {
            return rhs_internal;
        }
    
        int64_t& rhs() {
            return rhs_internal;
        }
    
        bool isZero() const {
            for (int i = 0; i < size; i++) 
                if (mp[i]) return false;            
            return true;
        }
    
        void setZero() {
            memset(mp, 0, sizeof(int64_t)*size);
        }
    
        void setOne() {
            memset(mp, 0xff, sizeof(int64_t)*size);
        }
    
        void clearBit(unsigned i) {
            mp[i / 64] &= ~(1LL << (i % 64));
        }
    
        void setBit(unsigned i) {
            mp[i / 64] |= (1LL << (i % 64));
        }
    
        void invert_rhs(bool b = true) {
            rhs_internal ^= (int)b;
        }
    
        void swapBoth(PackedRow b) {
            int64_t* __restrict mp1 = mp - 1;
            int64_t* __restrict mp2 = b.mp - 1;
    
            unsigned i = size + 1;
            while (i != 0) {
                std::swap(*mp1, *mp2);
                mp1++;
                mp2++;
                i--;
            }
        }
    
        inline bool operator[](unsigned i) const {
            return (mp[i / 64] >> (i % 64)) & 1;
        }
    
        template<class T>
        void set(const T& v, const unsigned_vector& var_to_column, unsigned num_cols) {
            
            SASSERT(size == ((int)num_cols/64) + ((bool)(num_cols % 64)));
    
            setZero();
            for (unsigned i = 0; i != v.size(); i++) {
                SASSERT(var_to_column[v[i]] != UINT32_MAX);
                setBit(var_to_column[v[i]]);
            }
    
            rhs_internal = v.m_rhs;
        }
    
        // using find nonbasic and basic value
        unsigned population_cnt(
            literal_vector& tmp_clause,
            const unsigned_vector& column_to_var,
            const bool_vector &var_has_resp_row,
            unsigned& non_resp_var);
    
        // using find nonbasic value after watch list is enter
        gret propGause(
            const unsigned_vector& column_to_var,
            bool_vector &var_has_resp_row,
            unsigned& new_resp_var,
            PackedRow& tmp_col,
            PackedRow& tmp_col2,
            PackedRow& cols_vals,
            PackedRow& cols_unset,
            literal& ret_lit_prop
        );
    
        void get_reason(
            literal_vector& tmp_clause,
            const unsigned_vector& column_to_var,
            PackedRow& cols_vals,
            PackedRow& tmp_col2,
            literal prop
        );
    
        unsigned popcnt() const {
            unsigned ret = 0;
            for (int i = 0; i < size; i++) 
                ret += get_num_1bits((uint64_t)mp[i]);            
            return ret;
        }
    };
    
    // A gaussian matrix (only the very basic data)
    class PackedMatrix {
    public:
        PackedMatrix() { }
    
        ~PackedMatrix() {
            #ifdef _WIN32
            _aligned_free((void*)mp);
            #else
            free(mp);
            #endif
        }
    
        void resize(unsigned num_rows, unsigned num_cols) {
            num_cols = num_cols / 64 + (bool)(num_cols % 64);
            if (numRows * (numCols + 1) < (int)num_rows * ((int)num_cols + 1)) {
                size_t size = sizeof(int64_t) * num_rows*(num_cols+1);
                #ifdef _WIN32
                _aligned_free((void*)mp);
                mp =  (int64_t*)_aligned_malloc(size, 16);
                #else
                free(mp);
                posix_memalign((void**)&mp, 16,  size);
                #endif
            }
    
            numRows = num_rows;
            numCols = num_cols;
        }
    
        void resizeNumRows(unsigned num_rows) {
            SASSERT((int)num_rows <= numRows);
            numRows = num_rows;
        }
    
        PackedMatrix& operator=(const PackedMatrix& b) {
            if (numRows*(numCols+1) < b.numRows*(b.numCols+1)) {
                unsigned size = sizeof(int64_t) * b.numRows * (b.numCols + 1);
                #ifdef _WIN32
                _aligned_free((void*)mp);
                mp =  (int64_t*)_aligned_malloc(size, 16);
                #else
                free(mp);
                posix_memalign((void**)&mp, 16,  size);
                #endif
            }
            numRows = b.numRows;
            numCols = b.numCols;
            memcpy(mp, b.mp, sizeof(int) * numRows * (numCols + 1));
    
            return *this;
        }
    
        PackedRow operator[](unsigned i) {
            return PackedRow(numCols, mp + i * (numCols + 1));
        }
    
        PackedRow operator[](unsigned i) const {
            return PackedRow(numCols, mp + i * (numCols + 1));
        }
    
        class iterator {
            int64_t* mp;
            const unsigned numCols;
            
            iterator(int64_t* _mp, unsigned _numCols) : mp(_mp), numCols(_numCols) { }
                
        public:
            friend class PackedMatrix;
    
            PackedRow operator*() {
                return PackedRow(numCols, mp);
            }
    
            iterator& operator++() {
                mp += numCols + 1;
                return *this;
            }
    
            iterator operator+(unsigned num) const {
                iterator ret(*this);
                ret.mp += (numCols + 1) * num;
                return ret;
            }
    
            unsigned operator-(const iterator& b) const {
                return (unsigned)(mp - b.mp) / (numCols + 1);
            }
    
            void operator+=(unsigned num) {
                mp += (numCols + 1) * num;  // add by f4
            }
    
            bool operator!=(const iterator& it) const {
                return mp != it.mp;
            }
    
            bool operator==(const iterator& it) const {
                return mp == it.mp;
            }
        };
    
        iterator begin() {
            return iterator(mp, numCols);
        }
    
        iterator end() {
            return iterator(mp + numRows * (numCols + 1), numCols);
        }
        
        unsigned num_rows() const {
            return numRows;
        }
    
        unsigned num_cols() const {
            return numCols;
        }
        
    private:
    
        int64_t* mp = nullptr;
        int numRows = 0;
        int numCols = 0;
    };
    
    // A single gaussian matrix
    class EGaussian {
    public:
        EGaussian(
            solver& solver,
            unsigned matrix_no,
            const vector<xor_clause>& xorclauses
        );
        ~EGaussian();
        bool is_initialized() const;
    
        // returns FALSE in case of conflict
        bool find_truths(
            svector<gauss_watched>& ws,
            unsigned& i,
            unsigned& j,
            bool_var var,
            unsigned row_n,
            gauss_data& gqd
        );
    
        literal_vector* get_reason(unsigned row, int& out_ID);
    
        // when basic variable is touched , eliminate one col
        void eliminate_column(
            unsigned p,
            gauss_data& gqd
        );
        void canceling();
        bool full_init(bool& created);
        void update_cols_vals_set(bool force = false);
        bool must_disable(gauss_data& gqd);
        void check_invariants();
        void update_matrix_no(unsigned n);
        void check_watchlist_sanity();
        void move_back_xor_clauses();

        void output_variable_assignment(std::ostream& out, sat::solver* s) {
            for (unsigned i = 0; i < m_num_cols; i++) {
                out << "v" << m_column_to_var[i] << "=" << (s->value(m_column_to_var[i]) == l_undef ? "?" : (s->value(m_column_to_var[i]) == l_true ? "1" : "0")) << " ";
            }
            out << std::endl;
            for (unsigned i = 0; i < m_num_cols; i++) {
                out << "v" << m_column_to_var[i] << "=";
                if (s->get_justification(m_column_to_var[i]).is_none())
                    out << "d";
                else if (s->get_justification(m_column_to_var[i]).is_binary_clause())
                    out << "b";
                else if (s->get_justification(m_column_to_var[i]).is_clause())
                    out << "c";
                else
                    out << "j" << s->get_justification(m_column_to_var[i]).get_ext_justification_idx();
                out << " ";
            }
            out << std::endl;
        }
    
    private:
        xr::solver& m_solver;   // original sat solver
    
        //Cleanup
        void clear_gwatches(bool_var var);
        void delete_gauss_watch_this_matrix();
        void delete_gausswatch(unsigned row_n);
    
        //Invariant checks, debug
        void check_no_prop_or_unsat_rows();
        void check_tracked_cols_only_one_set();
        bool check_row_satisfied(unsigned row);
        void check_row_not_in_watch(unsigned v, unsigned row_num) const;
    
        //Reason generation
        vector<reason> xor_reasons;
        sat::literal_vector tmp_clause;
        unsigned get_max_level(const gauss_data& gqd, unsigned row_n);
    
        //Initialisation
        void eliminate();
        void fill_matrix();
        void select_column_order();
        gret init_adjust_matrix(); // adjust matrix, include watch, check row is zero, etc.
    
        //Helper functions
        void prop_lit(const gauss_data& gqd, unsigned row_i, literal ret_lit_prop);
        bool inconsistent() const;

        ///////////////
        // stats
        ///////////////
        unsigned find_truth_ret_satisfied_precheck = 0;
        unsigned find_truth_called_propgause = 0;
        unsigned find_truth_ret_fnewwatch = 0;
        unsigned find_truth_ret_confl = 0;
        unsigned find_truth_ret_satisfied = 0;
        unsigned find_truth_ret_prop = 0;
    
        unsigned elim_called = 0;
        unsigned elim_xored_rows = 0;
        unsigned elim_called_propgause = 0;
        unsigned elim_ret_prop = 0;
        unsigned elim_ret_confl = 0;
        unsigned elim_ret_satisfied = 0;
        unsigned elim_ret_fnewwatch = 0;
        
        ///////////////
        // Internal data
        ///////////////
        unsigned matrix_no;
        bool initialized = false;
        bool cancelled_since_val_update = true;
        unsigned last_val_update = 0;

        vector<xor_clause> m_xorclauses;

        // Is the clause at this ROW satisfied already?
        // satisfied_xors[row] tells me that
        // TODO: Maybe compress further
        bool_vector satisfied_xors;
    
        // Someone is responsible for this column if the respective entry is true
        // we always WATCH this variable
        // A variable is responsible if there is only one row that has a 1 there
        // v1 v2 v3
        // 1  0  1
        // 0  1  1
        // "row 0" is responsible for v1, "row 1" is responsible for v2
        bool_vector var_has_resp_row;
    
        // row_to_var_non_resp[ROW] gives VAR it's NOT responsible for
        // we always WATCH this variable
        unsigned_vector row_to_var_non_resp;
    
    
        PackedMatrix m_mat;
        unsigned_vector m_var_to_column; // which column represents which variable in the matrix?
        bool_var_vector m_column_to_var; // which variable is in each column of the matrix?
        unsigned m_num_rows = 0;
        unsigned m_num_cols = 0;
    
        //quick lookup
        PackedRow* cols_vals = nullptr; // the current model for the variable in the respective column. Only correct if the respective element in cols_unset is 0 (lazily -> update_cols_vals_set)
        PackedRow* cols_unset = nullptr; // initially a sequence of 1. If the variable at the respective colum in the matrix is assigned it is set to 0 (lazily -> update_cols_vals_set) 
        PackedRow* tmp_col = nullptr;
        PackedRow* tmp_col2 = nullptr;
        
        void update_cols_vals_set(literal lit);
    
        //Data to free (with delete[] x)
        // TODO: This are always 4 equally sized elements; merge them into one block  
        svector<int64_t*> tofree;
    };
    
    inline void EGaussian::canceling() {
        cancelled_since_val_update = true;
        memset(satisfied_xors.data(), false, satisfied_xors.size());
    }

    inline void EGaussian::update_matrix_no(unsigned n) {
        matrix_no = n;
    }
    
    inline bool EGaussian::is_initialized() const {
        return initialized;
    }
}
