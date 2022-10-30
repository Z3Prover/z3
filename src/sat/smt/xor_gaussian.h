/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    xor_gaussian.h

Abstract:

    A roughly 1:1 port of CryptoMiniSAT's gaussian elimination datastructures/algorithms

--*/

#pragma once

#include "sat/smt/euf_solver.h"

#include "util/debug.h"
#include "util/sat_literal.h"
#include "util/trace.h"

namespace xr {
    
    typedef sat::literal literal;

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
    
    /*class constraint {
        unsigned        m_size;
        bool            m_detached = false;
        size_t          m_obj_size;
        bool            m_rhs;
        sat::bool_var   m_vars[0];
        
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(constraint) + num_lits * sizeof(sat::bool_var)); }
        
        constraint(const svector<sat::bool_var>& ids, bool expected_result) : m_size(ids.size()), m_obj_size(get_obj_size(ids.size())), m_rhs(expected_result) {
            unsigned i = 0;
            for (auto v : ids)
                m_vars[i++] = v;
        }
        sat::ext_constraint_idx cindex() const { return sat::constraint_base::mem2base(this); }
        void deallocate(small_object_allocator& a) { a.deallocate(m_obj_size, sat::constraint_base::mem2base_ptr(this)); }
        sat::bool_var operator[](unsigned i) const { return m_vars[i]; }
        bool is_detached() const { return m_detached; }
        unsigned get_size() const { return m_size; }
        bool get_rhs() const { return m_rhs; }
        sat::bool_var const* begin() const { return m_vars; }
        sat::bool_var const* end() const { return m_vars + m_size; }
        std::ostream& display(std::ostream& out) const {
            bool first = true;
            for (auto v : *this)
                out << (first ? "" : " ^ ") << v, first = false;
            return out << " = " << m_rhs;
        }
    };*/
    
    struct justification {
        unsigned m_propagation_index { 0 };

        justification(unsigned prop_index): m_propagation_index(prop_index) {}

        static justification get_null() { return justification(UINT_MAX); }
        bool is_null() const { return m_propagation_index == UINT_MAX; }
        sat::ext_constraint_idx to_index() const { return sat::constraint_base::mem2base(this); }
        static justification& from_index(size_t idx) { 
            return *reinterpret_cast<justification*>(sat::constraint_base::from_index(idx)->mem());
        }
        static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(justification)); }
    };
    
    enum PropByType {
        null_clause_t = 0, clause_t = 1, binary_t = 2,
        xor_t = 3, bnn_t = 4
    };
        
    class PropBy {
        unsigned red_step : 1;
        unsigned data1 : 31;
        unsigned type : 3;
        //0: clause, NULL
        //1: clause, non-null
        //2: binary
        //3: xor
        //4: bnn
        unsigned data2 : 29;
        int ID;
    
    public:
        PropBy() :
            red_step(0)
            , data1(0)
            , type(null_clause_t)
            , data2(0) {}
    
        //Normal clause prop
        explicit PropBy(const ClOffset offset) :
            red_step(0)
            , data1(offset)
            , type(clause_t)
            , data2(0) { }
    
        //XOR
        PropBy(const unsigned matrix_num, const unsigned row_num):
            data1(matrix_num)
            , type(xor_t)
            , data2(row_num) { }
            
        //Binary prop
        PropBy(const sat::literal lit, const bool redStep, int _ID) :
            red_step(redStep)
            , data1(lit.index())
            , type(binary_t)
            , data2(0)
            , ID(_ID) { }
    
        //For hyper-bin, etc.
        PropBy(
            const sat::literal lit
            , bool redStep //Step that lead here from ancestor is redundant
            , bool hyperBin //It's a hyper-binary clause
            , bool hyperBinNotAdded //It's a hyper-binary clause, but was never added because all the rest was zero-level
            , int _ID) :
            red_step(redStep)
            , data1(lit.index())
            , type(binary_t)
            , data2(0)
            , ID(_ID)
        {
            //HACK: if we are doing seamless hyper-bin and transitive reduction
            //then if we are at toplevel, .getAncestor()
            //must work, and return lit_Undef, but at the same time, .isNULL()
            //must also work, for conflict generation. So this is a hack to
            //achieve that. What an awful hack.
            if (lit == ~sat::null_literal)
                type = null_clause_t;
    
            data2 = ((unsigned)hyperBin) << 1
                | ((unsigned)hyperBinNotAdded) << 2;
        }
    
        void set_bnn_reason(unsigned idx) {
            SASSERT(isBNN());
            data1 = idx;
        }
    
        bool bnn_reason_set() const {
            SASSERT(isBNN());
            return data1 != 0xfffffff;
        }
    
        unsigned get_bnn_reason() const {
            SASSERT(bnn_reason_set());
            return data1;
        }
    
        unsigned isBNN() const {
            return type == bnn_t;
        }
    
        unsigned getBNNidx() const {
            SASSERT(isBNN());
            return data2;
        }
    
        bool isRedStep() const {
            return red_step;
        }
    
        unsigned getID() const {
            return ID;
        }
    
        bool getHyperbin() const {
            return data2 & 2U;
        }
    
        void setHyperbin(bool toSet) {
            data2 &= ~2U;
            data2 |= (unsigned)toSet << 1;
        }
    
        bool getHyperbinNotAdded() const {
            return data2 & 4U;
        }
    
        void setHyperbinNotAdded(bool toSet) {
            data2 &= ~4U;
            data2 |= (unsigned )toSet << 2;
        }
    
        sat::literal getAncestor() const {
            return ~sat::to_literal(data1);
        }
    
        bool isClause() const {
            return type == clause_t;
        }
    
        PropByType getType() const {
            return (PropByType)type;
        }
    
        sat::literal lit2() const {
            return sat::to_literal(data1);
        }
    
        unsigned get_matrix_num() const {
            return data1;
        }
    
        unsigned get_row_num() const {
            return data2;
        }
    
        ClOffset get_offset() const {
            return data1;
        }
    
        bool isNULL() const {
            return type == null_clause_t;
        }
    
        bool operator==(const PropBy other) const {
            return (type == other.type
                    && red_step == other.red_step
                    && data1 == other.data1
                    && data2 == other.data2
                   );
        }
    
        bool operator!=(const PropBy other) const {
            return !(*this == other);
        }
    };
    
    enum class gret { confl, prop, nothing_satisfied, nothing_fnewwatch };
    enum class gauss_res { none, confl, prop };
    
    struct GaussWatched {
        GaussWatched(unsigned r, unsigned m):
            row_n(r) , matrix_num(m) {}
    
        unsigned row_n;        // watch row
        unsigned matrix_num;   // watch matrix
    
        bool operator<(const GaussWatched& other) const {
            if (matrix_num < other.matrix_num) {
                return true;
            }
    
            if (matrix_num > other.matrix_num) {
                return false;
            }
    
            return row_n < other.row_n;
        }
    };
    
    struct gauss_data {
        bool do_eliminate; // we do elimination when basic variable is invoked
        unsigned new_resp_var;                     // do elimination variable
        unsigned new_resp_row ;         // do elimination row
        PropBy confl;              // returning conflict
        gauss_res ret; //final return value to Searcher
        unsigned currLevel; //level at which the variable was decided on
    
    
        unsigned num_props = 0;  // total gauss propagation time for DPLL
        unsigned num_conflicts = 0;   // total gauss conflict    time for DPLL
        unsigned engaus_disable_checks = 0;
        bool disabled = false;     // decide to do gaussian elimination
    
        void reset() {
            do_eliminate = false;
            ret = gauss_res::none;
        }
    };
    
    struct XorReason {
        bool must_recalc = true;
        literal propagated = sat::null_literal;
        unsigned ID = 0;
        sat::literal_vector reason;
    };
    
    struct Xor {
        
        bool rhs = false;
        unsigned_vector clash_vars;
        bool detached = false;
        unsigned_vector vars;
        
        Xor() = default;
    
        explicit Xor(const unsigned_vector& cl, const bool _rhs, const unsigned_vector& _clash_vars) : rhs(_rhs), clash_vars(_clash_vars) {
            for (unsigned i = 0; i < cl.size(); i++) {
                vars.push_back(cl[i]);
            }
        }
    
        template<typename T>
        explicit Xor(const T& cl, const bool _rhs, const unsigned_vector& _clash_vars) : rhs(_rhs), clash_vars(_clash_vars) {
            for (unsigned i = 0; i < cl.size(); i++) {
                vars.push_back(cl[i].var());
            }
        }
    
        explicit Xor(const unsigned_vector& cl, const bool _rhs, const unsigned clash_var) : rhs(_rhs) {
            clash_vars.push_back(clash_var);
            for (unsigned i = 0; i < cl.size(); i++) {
                vars.push_back(cl[i]);
            }
        }
    
        ~Xor() { }
        
        unsigned_vector::const_iterator begin() const {
            return vars.begin();
        }
    
        unsigned_vector::const_iterator end() const {
            return vars.end();
        }
    
        unsigned_vector::iterator begin() {
            return vars.begin();
        }
    
        unsigned_vector::iterator end() {
            return vars.end();
        }
    
        bool operator<(const Xor& other) const {
            uint64_t i = 0;
            while(i < other.size() && i < size()) {
                if (other[i] != vars[i])
                    return (vars[i] < other[i]);
                i++;
            }
    
            if (other.size() != size()) {
                return size() < other.size();
            }
            return false;
        }
    
        const unsigned& operator[](const unsigned at) const {
            return vars[at];
        }
    
        unsigned& operator[](const unsigned at) {
            return vars[at];
        }
    
        void shrink(const unsigned newsize) {
            vars.shrink(newsize);
        }
    
        unsigned_vector& get_vars() {
            return vars;
        }
    
        const unsigned_vector& get_vars() const {
            return vars;
        }
    
        unsigned size() const {
            return vars.size();
        }
    
        bool empty() const {
            if (!vars.empty())
                return false;
            if (!clash_vars.empty())
                return false;
            return !rhs;
        }
    
        void merge_clash(const Xor& other, unsigned_vector& seen) {
            for (const auto& v: clash_vars) {
                seen[v] = 1;
            }
    
            for (const auto& v: other.clash_vars) {
                if (!seen[v]) {
                    seen[v] = 1;
                    clash_vars.push_back(v);
                }
            }
    
            for (const auto& v: clash_vars) {
                seen[v] = 0;
            }
        }
    };
    
    struct PackedRow {
        PackedRow() = delete;
        
        PackedRow& operator=(const PackedRow& b) {
            //start from -1, because that's wher RHS is
            for (int i = -1; i < size; i++) {
                *(mp + i) = *(b.mp + i);
            }
    
            return *this;
        }
    
        PackedRow& operator^=(const PackedRow& b) {
            //start from -1, because that's wher RHS is
            for (int i = -1; i < size; i++) {
                *(mp + i) ^= *(b.mp + i);
            }
    
            return *this;
        }
        
        void set_and(const PackedRow& a, const PackedRow& b) {
            for (int i = 0; i < size; i++) {
                *(mp + i) = *(a.mp + i) & *(b.mp + i);
            }
        }
    
        unsigned set_and_until_popcnt_atleast2(const PackedRow& a, const PackedRow& b) {
            unsigned pop = 0;
            for (int i = 0; i < size && pop < 2; i++) {
                *(mp + i) = *(a.mp + i) & *(b.mp + i);
                pop += __builtin_popcountll((uint64_t)*(mp + i));
            }
    
            return pop;
        }
    
        void xor_in(const PackedRow& b) {
            rhs_internal ^= b.rhs_internal;
            for (int i = 0; i < size; i++) {
                *(mp + i) ^= *(b.mp + i);
            }
        }
    
        inline const int64_t& rhs() const {
            return rhs_internal;
        }
    
        inline int64_t& rhs() {
            return rhs_internal;
        }
    
        inline bool isZero() const {
            for (int i = 0; i < size; i++) {
                if (mp[i]) return false;
            }
            return true;
        }
    
        inline void setZero() {
            memset(mp, 0, sizeof(int64_t)*size);
        }
    
        inline void setOne() {
            memset(mp, 0xff, sizeof(int64_t)*size);
        }
    
        inline void clearBit(const unsigned i) {
            mp[i/64] &= ~(1LL << (i%64));
        }
    
        inline void setBit(const unsigned i) {
            mp[i / 64] |= (1LL << (i % 64));
        }
    
        inline void invert_rhs(const bool b = true) {
            rhs_internal ^= (int)b;
        }
    
        void swapBoth(PackedRow b) {
            int64_t* __restrict mp1 = mp - 1;
            int64_t* __restrict mp2 = b.mp - 1;
    
            unsigned i = size+1;
            while(i != 0) {
                std::swap(*mp1, *mp2);
                mp1++;
                mp2++;
                i--;
            }
        }
    
        inline bool operator[](const unsigned i) const {
            return (mp[i / 64] >> (i % 64)) & 1;
        }
    
        template<class T>
        void set(
            const T& v,
            const unsigned_vector& var_to_col,
            const unsigned num_cols) {
            SASSERT(size == ((int)num_cols/64) + ((bool)(num_cols % 64)));
    
            setZero();
            for (unsigned i = 0; i != v.size(); i++) {
                const unsigned toset_var = var_to_col[v[i]];
                SASSERT(toset_var != UINT32_MAX);
    
                setBit(toset_var);
            }
    
            rhs_internal = v.rhs;
        }
    
        // using find nonbasic and basic value
        unsigned find_watchVar(
            sat::literal_vector& tmp_clause,
            const unsigned_vector& col_to_var,
            char_vector &var_has_resp_row,
            unsigned& non_resp_var);
    
        // using find nonbasic value after watch list is enter
        gret propGause(
            const unsigned_vector& col_to_var,
            char_vector &var_has_resp_row,
            unsigned& new_resp_var,
            PackedRow& tmp_col,
            PackedRow& tmp_col2,
            PackedRow& cols_vals,
            PackedRow& cols_unset,
            literal& ret_lit_prop
        );
    
        void get_reason(
            sat::literal_vector& tmp_clause,
            const unsigned_vector& col_to_var,
            PackedRow& cols_vals,
            PackedRow& tmp_col2,
            literal prop
        );
    
        unsigned popcnt() const {
            unsigned ret = 0;
            for (int i = 0; i < size; i++) {
                ret += __builtin_popcountll((uint64_t)mp[i]);
            }
            return ret;
        }
    
    private:
        friend class PackedMatrix;
        friend class EGaussian;
        friend std::ostream& operator << (std::ostream& os, const PackedRow& m);
    
        PackedRow(const unsigned _size, int64_t*  const _mp) :
            mp(_mp+1)
            , rhs_internal(*_mp)
            , size(_size) {}
    
        //int __attribute__ ((aligned (16))) *const mp;
        int64_t *__restrict const mp;
        int64_t& rhs_internal;
        const int size;
    };
    
    struct PackedMatrix {
        PackedMatrix() : mp(NULL), numRows(0), numCols(0) { }
    
        ~PackedMatrix() {
            #ifdef _WIN32
            _aligned_free((void*)mp);
            #else
            free(mp);
            #endif
        }
    
        void resize(const unsigned num_rows, unsigned num_cols) {
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
    
        void resizeNumRows(const unsigned num_rows) {
            SASSERT((int)num_rows <= numRows);
            numRows = num_rows;
        }
    
        PackedMatrix& operator=(const PackedMatrix& b) {
            if (numRows*(numCols+1) < b.numRows*(b.numCols+1)) {
                size_t size = sizeof(int64_t) * b.numRows*(b.numCols+1);
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
            memcpy(mp, b.mp, sizeof(int)*numRows*(numCols+1));
    
            return *this;
        }
    
        inline PackedRow operator[](const unsigned i) {
            return PackedRow(numCols, mp+i*(numCols+1));
        }
    
        inline PackedRow operator[](const unsigned i) const {
            return PackedRow(numCols, mp+i*(numCols+1));
        }
    
        class iterator {
            int64_t* mp;
            const unsigned numCols;
            
            iterator(int64_t* _mp, const unsigned _numCols) : mp(_mp), numCols(_numCols) { }
                
        public:
            friend class PackedMatrix;
    
            PackedRow operator*() {
                return PackedRow(numCols, mp);
            }
    
            iterator& operator++() {
                mp += (numCols+1);
                return *this;
            }
    
            iterator operator+(const unsigned num) const {
                iterator ret(*this);
                ret.mp += (numCols+1)*num;
                return ret;
            }
    
            unsigned operator-(const iterator& b) const {
                return (mp - b.mp)/((numCols+1));
            }
    
            void operator+=(const unsigned num) {
                mp += (numCols+1)*num;  // add by f4
            }
    
            bool operator!=(const iterator& it) const {
                return mp != it.mp;
            }
    
            bool operator==(const iterator& it) const {
                return mp == it.mp;
            }
        };
    
        inline iterator begin() {
            return iterator(mp, numCols);
        }
    
        inline iterator end() {
            return iterator(mp+numRows*(numCols+1), numCols);
        }
    
        inline unsigned getSize() const {
            return numRows;
        }
    
    private:
    
        int64_t *mp;
        int numRows;
        int numCols;
    };
    
    class EGaussian {
    public:
        EGaussian(
            solver* solver,
            const unsigned matrix_no,
            const vector<Xor>& xorclauses
        );
        ~EGaussian();
        bool is_initialized() const;
    
        ///returns FALSE in case of conflict
        bool find_truths(
            GaussWatched*& i,
            GaussWatched*& j,
            const unsigned var,
            const unsigned row_n,
            gauss_data& gqd
        );
    
        sat::literal_vector* get_reason(const unsigned row, int& out_ID);
    
        // when basic variable is touched , eliminate one col
        void eliminate_col(
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
        unsigned get_matrix_no();
        void move_back_xor_clauses();
        bool clean_xor_clauses(vector<Xor>& xors);
        bool clean_one_xor(Xor& x);
    
        vector<Xor> m_xorclauses;
    
    private:
        xr::solver* m_solver;   // original sat solver
    
        //Cleanup
        void clear_gwatches(const unsigned var);
        void delete_gauss_watch_this_matrix();
        void delete_gausswatch(const unsigned  row_n);
    
        //Invariant checks, debug
        void check_no_prop_or_unsat_rows();
        void check_tracked_cols_only_one_set();
        bool check_row_satisfied(const unsigned row);
        void check_row_not_in_watch(const unsigned v, const unsigned row_num) const;
    
        //Reason generation
        svector<XorReason> xor_reasons;
        sat::literal_vector tmp_clause;
        unsigned get_max_level(const gauss_data& gqd, const unsigned row_n);
    
        //Initialisation
        void eliminate();
        void fill_matrix();
        void select_columnorder();
        gret init_adjust_matrix(); // adjust matrix, include watch, check row is zero, etc.
        double get_density();
    
        //Helper functions
        void prop_lit(const gauss_data& gqd, const unsigned row_i, const sat::literal ret_lit_prop);
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
        double before_init_density = 0;
        double after_init_density = 0;
        
        ///////////////
        // Internal data
        ///////////////
        unsigned matrix_no;
        bool initialized = false;
        bool cancelled_since_val_update = true;
        unsigned last_val_update = 0;
    
        //Is the clause at this ROW satisfied already?
        //satisfied_xors[decision_level][row] tells me that
        char_vector satisfied_xors;
    
        // Someone is responsible for this column if TRUE
        ///we always WATCH this variable
        char_vector var_has_resp_row;
    
        ///row_to_var_non_resp[ROW] gives VAR it's NOT responsible for
        ///we always WATCH this variable
        unsigned_vector row_to_var_non_resp;
    
    
        PackedMatrix mat;
        svector<char_vector> bdd_matrix;
        unsigned_vector  var_to_col; ///var->col mapping. Index with VAR
        unsigned_vector col_to_var; ///col->var mapping. Index with COL
        unsigned num_rows = 0;
        unsigned num_cols = 0;
    
        //quick lookup
        PackedRow* cols_vals = NULL;
        PackedRow* cols_unset = NULL;
        PackedRow* tmp_col = NULL;
        PackedRow* tmp_col2 = NULL;
        void update_cols_vals_set(const sat::literal lit1);
    
        //Data to free (with delete[] x)
        svector<int64_t*> tofree;
    };
    
    inline void EGaussian::canceling() {
        cancelled_since_val_update = true;
    
        //TODO this is an overstatement, could be improved
        memset(satisfied_xors.data(), 0, satisfied_xors.size());
    }
    
    inline double EGaussian::get_density() {
        if (num_rows*num_cols == 0)
            return 0;
    
        unsigned pop = 0;
        for (const auto& row: mat) {
            pop += row.popcnt();
        }
        return (double)pop/(double)(num_rows*num_cols);
    }
    
    inline void EGaussian::update_matrix_no(unsigned n) {
        matrix_no = n;
    }
    
    inline unsigned EGaussian::get_matrix_no() {
        return matrix_no;
    }
    
    inline bool EGaussian::is_initialized() const {
        return initialized;
    }
}