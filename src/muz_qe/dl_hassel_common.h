/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_common.h

Abstract:

    <abstract>

Revision History:

--*/

#ifndef _DL_HASSEL_COMMON_H_
#define _DL_HASSEL_COMMON_H_

#include "bit_vector.h"
#include "dl_base.h"
#include "bv_decl_plugin.h"
#include "union_find.h"
#include <list>
#include <set>

#define BIT_0 ((0<<1)|1)
#define BIT_1 ((1<<1)|0)
#define BIT_x ((1<<1)|1)

namespace datalog {

    expr_ref formula_to_dnf(expr_ref f);

    class bit_vector : public ::bit_vector {
    public:
        bit_vector() : ::bit_vector() {}
        bit_vector(unsigned bits) : ::bit_vector(bits) {}

        bool contains(const bit_vector & other) const;
        bool contains(const bit_vector & other, unsigned idx) const;
        bool contains_consecutive_zeros() const;

        bit_vector slice(unsigned idx, unsigned length) const;
        void append(const bit_vector & other);

        uint64 to_number(unsigned idx, unsigned length) const;

        // for std::less operations
        bool operator<(bit_vector const & other) const;
    };


    class table_information {
        unsigned_vector m_column_info;
        bv_util m_bv_util;
        dl_decl_util m_decl_util;

    public:
        table_information(table_plugin & p, const table_signature& sig);

        unsigned get_num_bits() const {
            return m_column_info.back();
        }

        unsigned get_num_cols() const {
            return m_column_info.size()-1;
        }

        unsigned column_idx(unsigned col) const {
            return m_column_info[col];
        }

        unsigned column_num_bits(unsigned col) const {
            return m_column_info[col+1] - m_column_info[col];
        }

        void expand_column_vector(unsigned_vector& v, const table_information *other = 0) const;

        void display(std::ostream & out) const;

        const bv_util& get_bv_util() const { return m_bv_util; }
        const dl_decl_util& get_decl_util() const { return m_decl_util; }
    };


    template<class T> class union_ternary_bitvector;


    class ternary_bitvector : private bit_vector {
    public:
        ternary_bitvector() : bit_vector() {}
        ternary_bitvector(unsigned size) : bit_vector(2 * size) {}

        ternary_bitvector(unsigned size, bool full);
        ternary_bitvector(uint64 n, unsigned num_bits);
        ternary_bitvector(const table_fact& f, const table_information& t);

        void swap(ternary_bitvector& other) {
            SASSERT(size() == other.size());
            bit_vector::swap(other);
        }

        void resize(unsigned new_size, bool val = false) {
            bit_vector::resize(2 * new_size, val);
        }

        void reset() {
            m_num_bits = 0;
        }

        unsigned size() const {
            SASSERT((m_num_bits % 2) == 0);
            return m_num_bits/2;
        }

        void fill1();

        void append(const ternary_bitvector & other) { bit_vector::append(other); }
        bool contains(const ternary_bitvector & other) const { return bit_vector::contains(other); }

        bool is_empty() const { return contains_consecutive_zeros(); }

        unsigned get(unsigned idx) const;
        void set(unsigned idx, unsigned val);
        void push_back(unsigned val);
        void append_number(uint64 n, unsigned num_bits);
        void mk_idx_eq(unsigned idx, ternary_bitvector& val);

        ternary_bitvector and(const ternary_bitvector& other) const;
        void neg(union_ternary_bitvector<ternary_bitvector>& result) const;

        void join(const ternary_bitvector& other, const unsigned_vector& cols1,
            const unsigned_vector& cols2, union_ternary_bitvector<ternary_bitvector>& result) const;

        bool project(const unsigned_vector& delcols, ternary_bitvector& result) const;

        void rename(const unsigned_vector& cyclecols, const unsigned_vector& out_of_cycle_cols,
            const table_information& src_table, const table_information& dst_table,
            ternary_bitvector& result) const;

        static bool has_subtract() { return false; }
        void subtract(const union_ternary_bitvector<ternary_bitvector>& other,
            union_ternary_bitvector<ternary_bitvector>& result) const { UNREACHABLE(); }

        void display(std::ostream & out) const;
        unsigned size_in_bytes() const;

#if Z3DEBUG
        void expand(std::set<bit_vector> & BVs) const;
#endif

    private:
#if Z3DEBUG
        void expand(std::set<bit_vector> & BVs, bit_vector &BV, unsigned idx) const;
#endif
    };


    template<class T>
    class union_ternary_bitvector {
        typedef std::list<T> union_t;

        union_t m_bitvectors;
        unsigned m_bv_size; //!< number of ternary bits

    public:
        union_ternary_bitvector(unsigned bv_size) : m_bv_size(bv_size) {}

        union_ternary_bitvector(unsigned bv_size, bool full) : m_bv_size(bv_size) {
            if (full)
                mk_full();
        }

        union_ternary_bitvector and(const union_ternary_bitvector & Other) const {
            if (empty())
                return *this;
            if (Other.empty())
                return Other;

            union_ternary_bitvector Ret(m_bv_size);

            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                for (const_iterator II = Other.begin(), EE = Other.end(); II != EE; ++II) {
                    T row(I->and(*II));
                    if (!row.is_empty())
                        Ret.add_fact(row);
                }
            }
            return Ret;
        }

        union_ternary_bitvector or(const union_ternary_bitvector & Other) const {
            if (empty())
                return Other;
            if (Other.empty())
                return *this;

            union_ternary_bitvector Ret(*this);
            Ret.add_facts(Other);
            return Ret;
        }

        union_ternary_bitvector neg() const {
            union_ternary_bitvector Ret(m_bv_size);
            Ret.mk_full();

            union_ternary_bitvector negated(m_bv_size);
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                negated.reset();
                I->neg(negated);
                Ret.swap(Ret.and(negated));
            }
            return Ret;
        }

        void subtract(const union_ternary_bitvector& other) {
            if (!T::has_subtract()) {
                swap(this->and(other.neg()));
                return;
            }

            union_ternary_bitvector subtracted(m_bv_size);
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                I->subtract(other, subtracted);
            }
            swap(subtracted);
        }

#if 0
        union_ternary_bitvector gc() const {
            // Simple subsumption-based cleaning.
            union_ternary_bitvector Ret(m_bv_size);
            for (union_t::const_reverse_iterator I = m_bitvectors.rbegin(), E = m_bitvectors.rend(); I != E; ++I) {
                Ret.add_fact(*I);
            }
            return Ret;
        }
#endif

        void join(const union_ternary_bitvector& other, const unsigned_vector& cols1,
                  const unsigned_vector& cols2, union_ternary_bitvector& result) const {
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                for (const_iterator II = other.begin(), EE = other.end(); II != EE; ++II) {
                    I->join(*II, cols1, cols2, result);
                }
            }
        }

        void rename(const unsigned_vector& cyclecols, const unsigned_vector& out_of_cycle_cols,
                    const table_information& src_table, const table_information& dst_table,
                    union_ternary_bitvector& result) const {
            T row(m_bv_size);
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                row.reset();
                I->rename(cyclecols, out_of_cycle_cols, src_table, dst_table, row);
                result.add_new_fact(row);
            }
        }

        void project(const unsigned_vector& delcols, union_ternary_bitvector& result) const {
            unsigned new_size = m_bv_size - (delcols.size()-1);
            T row(new_size);

            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                row.reset();
                if (I->project(delcols, row)) {
                    SASSERT(!row.is_empty());
                    result.add_fact(row);
                }
            }
        }

    private:
        typedef union_find<> subset_ints;

        // returns 1 if row should be removed, 0 otherwise
        static int fix_single_bit(T & BV, unsigned idx, unsigned value, const subset_ints& equalities) {
            unsigned root = equalities.find(idx);
            idx = root;
            do {
                unsigned bitval = BV.get(idx);
                if (bitval == BIT_x) {
                    BV.set(idx, value);    
                } else if (bitval != value) {
                    return 1;
                }
                idx = equalities.next(idx);
            } while (idx != root);
            return 0;
        }

        static int fix_single_bit(T & BV1, unsigned idx1, T & BV2, unsigned idx2,
                                  subset_ints& equalities, bool discard_col) {
            unsigned A = BV1.get(idx1);
            unsigned B = BV2.get(idx2);

            if (A == BIT_x) {
                if (B == BIT_x) {
                    // Both are don't cares.
                    /////// FIXME::: don't duplicate rows with diff table
                    if (!discard_col)
                        return 2; // duplicate row
                    equalities.merge(idx1, idx2);
                    return 0;
                } else {
                    // only A is don't care.
                    return fix_single_bit(BV1, idx1, B, equalities);
                }
            } else if (B == BIT_x) {
                // Only B is don't care.
                return fix_single_bit(BV2, idx2, A, equalities);
            } else if (A == B) {
                return 0;
            } else {
                return 1; // remove row
            }
        }

        void fix_eq_bits(unsigned idx1, const T *BV, unsigned idx2, unsigned length,
                         subset_ints& equalities, const bit_vector& discard_cols) {
            for (unsigned i = 0; i < length; ++i) {
                for (union_t::iterator I = m_bitvectors.begin(), E = m_bitvectors.end(); I != E; ) {
                    T *eqBV = BV ? const_cast<T*>(BV) : &*I;
                    bool discard_col = discard_cols.get(idx1+i) || (!BV && discard_cols.get(idx2+i));

                    switch (fix_single_bit(*I, idx1+i, *eqBV, idx2+i, equalities, discard_col)) {
                    case 1:
                        // remove row
                        I = m_bitvectors.erase(I);
                        break;

                    case 2: {
                        // duplicate row
                        T BV2(*I);
                        I->set(idx1+i, BIT_0);
                        I->set(idx2+i, BIT_0);

                        BV2.set(idx1+i, BIT_1);
                        BV2.set(idx2+i, BIT_1);
                        m_bitvectors.insert(I, BV2);
                        ++I;
                        break;}

                    default:
                        // bits fixed
                        ++I;
                    }
                }
            }
        }

        /// make bits of table [idx,idx+max_length]  equal to e sliced starting at idx2
        unsigned fix_eq_bits(unsigned idx, const expr *e, unsigned idx2, unsigned max_length,
                             const table_information& t, subset_ints& equalities,
                             const bit_vector & discard_cols) {
            const bv_util& bvu = t.get_bv_util();
            const dl_decl_util& dutil = t.get_decl_util();

            rational n;
            unsigned bv_size;
            if (bvu.is_numeral(e, n, bv_size)) {
                T num(n.get_int64(), bv_size);
                SASSERT(idx2 < bv_size);
                max_length = std::min(max_length, bv_size - idx2);
                fix_eq_bits(idx, &num, idx2, max_length, equalities, discard_cols);
                return idx + max_length;
            }

            uint64 num;
            if (dutil.is_numeral(e, num)) {
                T num_bv(num, max_length);
                fix_eq_bits(idx, &num_bv, idx2, max_length, equalities, discard_cols);
                return idx + max_length;
            }

            if (bvu.is_concat(e)) {
                const app *a = to_app(e);

                // skip the first elements of the concat if e.g. we have a top level extract
                unsigned i = 0;
                for (; i < a->get_num_args(); ++i) {
                    unsigned arg_size = bvu.get_bv_size(a->get_arg(i));
                    if (idx2 < arg_size)
                        break;
                    idx2 -= arg_size;
                }

                SASSERT(i < a->get_num_args());
                for (; max_length > 0 && i < a->get_num_args(); ++i) {
                    unsigned idx0 = idx;
                    idx = fix_eq_bits(idx, a->get_arg(i), idx2, max_length, t, equalities, discard_cols);
                    idx2 = 0;
                    SASSERT((idx - idx0) <= max_length);
                    max_length = max_length - (idx - idx0);
                }
                return idx;
            }

            unsigned low, high;
            expr *e2;
            if (bvu.is_extract(e, low, high, e2)) {
                SASSERT(low <= high);
                unsigned size = bvu.get_bv_size(e2);
                unsigned offset = size - (high+1) + idx2;
                SASSERT(idx2 < (high-low+1));
                max_length = std::min(max_length, high - low + 1 - idx2);
                return fix_eq_bits(idx, e2, offset, max_length, t, equalities, discard_cols);
            }

            if (e->get_kind() == AST_VAR) {
                unsigned idx_var = idx2 + t.column_idx(to_var(e)->get_idx());
                SASSERT(idx2 < t.column_num_bits(to_var(e)->get_idx()));
                max_length = std::min(max_length, t.column_num_bits(to_var(e)->get_idx()) - idx2);
                fix_eq_bits(idx, 0, idx_var, max_length, equalities, discard_cols);
                return idx + max_length;
            }

            NOT_IMPLEMENTED_YET();
            return 0;
        }

        void filter(const expr *e, subset_ints& equalities, const bit_vector& discard_cols,
                    const table_information& t) {
            switch (e->get_kind()) {
            case AST_APP: {
                const app *app = to_app(e);
                switch (app->get_decl_kind()) {
                case OP_AND:
                    for (unsigned i = 0; i < app->get_num_args(); ++i) {
                        filter(app->get_arg(i), equalities, discard_cols, t);
                    }
                    return;

                case OP_EQ: {
                    const expr *a = app->get_arg(0);
                    const var *v;
                    unsigned vidx = 0;
                    unsigned length;

                    unsigned low, high;
                    expr *e2;
                    if (is_var(a)) {
                        v = to_var(a);
                        length = t.column_num_bits(v->get_idx());
                    } else if (t.get_bv_util().is_extract(a, low, high, e2)) {
                        vidx = t.get_bv_util().get_bv_size(e2) - high - 1;
                        length = high - low + 1;
                        SASSERT(is_var(e2));
                        v = to_var(e2);
                    } else {
                        NOT_IMPLEMENTED_YET();
                    }
                    vidx += t.column_idx(v->get_idx());

                    unsigned final_idx = fix_eq_bits(vidx, app->get_arg(1), 0, length, t, equalities, discard_cols);
                    SASSERT(final_idx == vidx + length);
                    (void)final_idx;
                    return;}

                case OP_FALSE:
                    reset();
                    return;

                case OP_NOT: {
                    union_ternary_bitvector sub(m_bv_size, true);
                    sub.filter(app->get_arg(0), equalities, discard_cols, t);
                    this->subtract(sub);
                    return;}

                case OP_OR: {
                    union_ternary_bitvector orig(m_bv_size);
                    swap(orig);
                    for (unsigned i = 0; i < app->get_num_args(); ++i) {
                        union_ternary_bitvector tmp(orig);
                        subset_ints eqs(equalities);
                        tmp.filter(app->get_arg(i), eqs, discard_cols, t);
                        add_facts(tmp);
                    }
                    return;}

                case OP_TRUE:
                    return;

                default:
                    std::cerr << "app decl: " << app->get_decl()->get_name() << " (" << app->get_decl_kind() << ")\n";
                    NOT_IMPLEMENTED_YET();
                }
                break;}

            case AST_VAR: {
                // boolean var must be true (10)
                SASSERT(t.column_num_bits(to_var(e)->get_idx()) == 1);
                unsigned idx = t.column_idx(to_var(e)->get_idx());
                ternary_bitvector BV(1);
                BV.push_back(BIT_1);
                T BV2(BV);
                fix_eq_bits(idx, &BV2, 0, 2, equalities, discard_cols);
                return;}

            default:
                break;
            }
            std::cerr << "expr kind: " << get_ast_kind_name(e->get_kind()) << '\n';
            NOT_IMPLEMENTED_YET();
        }

    public:
        void filter(const expr *cond, const bit_vector& discard_cols, const table_information& table) {
            // datastructure to store equalities with columns that will be projected out
            union_find_default_ctx union_ctx;
            subset_ints equalities(union_ctx);
            for (unsigned i = 0, e = discard_cols.size(); i < e; ++i) {
                equalities.mk_var();
            }

            filter(cond, equalities, discard_cols, table);
        }
        
        bool contains(const T & fact) const {
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                if (I->contains(fact))
                    return true;
            }
            return false;
        }

        bool contains(const union_ternary_bitvector & other) const {
            for (const_iterator I = other.begin(), E = other.end(); I != E; ++I) {
                for (const_iterator II = begin(), EE = end(); II != EE; ++II) {
                    if (II->contains(*I))
                        goto next_iter;
                }
                return false;
next_iter:      ;
            }
            return true;
        }

        unsigned num_disjs() const {
            return (unsigned)m_bitvectors.size();
        }

        unsigned num_bytes() const {
            unsigned size = sizeof(*this);
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                size += I->size_in_bytes();
            }
            return size;
        }

#if Z3DEBUG
        void expand(std::set<bit_vector> & BVs) const {
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                I->expand(BVs);
            }
        }
#endif

        void add_facts(const union_ternary_bitvector & Other, union_ternary_bitvector *Delta = 0) {
            for (const_iterator I = Other.begin(), E = Other.end(); I != E; ++I) {
                if (add_fact(*I) && Delta)
                    Delta->add_fact(*I);
            }
        }

        bool add_fact(const T & fact) {
            if (contains(fact))
                return false;
            add_new_fact(fact);
            return true;
        }

        void add_new_fact(const T & fact) {
            SASSERT(m_bv_size == fact.size());

            // TODO: optimize sequence (karnaugh maps??)
            // At least join 1-bit different BVs
            m_bitvectors.push_back(fact);
        }

        void mk_full() {
            reset();
            add_new_fact(T(m_bv_size, true));
        }

        typedef typename union_t::const_iterator const_iterator;

        const_iterator begin() const { return m_bitvectors.begin(); }
        const_iterator end() const { return m_bitvectors.end(); }

        bool empty() const { return m_bitvectors.empty(); }
        void reset() { m_bitvectors.clear(); }

        void swap(union_ternary_bitvector& other) {
            SASSERT(m_bv_size == other.m_bv_size);
            m_bitvectors.swap(other.m_bitvectors);
        }

        void display(std::ostream & out) const {
            out << '#' << num_disjs() << " (bv" << m_bv_size << ") ";

            bool first = true;
            for (const_iterator I = begin(), E = end(); I != E; ++I) {
                if (!first)
                    out << " \\/ ";
                first = false;
                I->display(out);
            }
            out << '\n';
        }
    };


    template<class T>
	class common_hassel_table_plugin : public table_plugin {
    public:
        common_hassel_table_plugin(symbol &s, relation_manager & manager) :
            table_plugin(s, manager) { }

        virtual table_base * mk_empty(const table_signature & s) {
            return alloc(T, *this, s);
        }

        virtual table_base * mk_full(func_decl* p, const table_signature & s) {
            T *t = static_cast<T*>(mk_empty(s));
            t->mk_full();
            return t;
        }

        virtual bool can_handle_signature(const table_signature & s) {
            return s.functional_columns() == 0;
        }

    private:
        ast_manager& get_ast_manager() { return get_context().get_manager(); }

        class join_fn : public convenient_table_join_fn {
        public:
            join_fn(const T & t1, const T & t2, unsigned col_cnt, const unsigned *cols1, const unsigned *cols2) 
                : convenient_table_join_fn(t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2) {
                t1.expand_column_vector(m_cols1);
                t2.expand_column_vector(m_cols2);
            }

            virtual table_base * operator()(const table_base & tb1, const table_base & tb2) {
                const T & T1 = static_cast<const T &>(tb1);
                const T & T2 = static_cast<const T &>(tb2);
                T * Res = static_cast<T *>(T1.get_plugin().mk_empty(get_result_signature()));
                T1.m_bitsets.join(T2.m_bitsets, m_cols1, m_cols2, Res->m_bitsets);
                TRACE("dl_hassel", tout << "final size: " << Res->get_size_estimate_rows() << '\n';);
                return Res;
            }
        };

    public:
        virtual table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
            if (!check_kind(t1) || !check_kind(t2))
                return 0;
            return alloc(join_fn, static_cast<const T &>(t1), static_cast<const T &>(t2), col_cnt, cols1, cols2);
        }

    private:
        class union_fn : public table_union_fn {
        public:
            virtual void operator()(table_base & tgt0, const table_base & src0, table_base * delta0) {
                T & tgt = static_cast<T &>(tgt0);
                const T & src = static_cast<const T &>(src0);
                T * delta = static_cast<T *>(delta0);
                tgt.m_bitsets.add_facts(src.m_bitsets, delta ? &delta->m_bitsets : 0);
                TRACE("dl_hassel", tout << "final size: " << tgt.get_size_estimate_rows() << '\n';);
            }
        };

    public:
        virtual table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta) {
            if (!check_kind(tgt) || !check_kind(src))
                return 0;
            return alloc(union_fn);
        }

    private:
        class project_fn : public convenient_table_project_fn {
        public:
            project_fn(const T & t, unsigned removed_col_cnt, const unsigned * removed_cols) 
                : convenient_table_project_fn(t.get_signature(), removed_col_cnt, removed_cols) {
                t.expand_column_vector(m_removed_cols);
                m_removed_cols.push_back(UINT_MAX);
            }

            virtual table_base * operator()(const table_base & tb) {
                const T & t = static_cast<const T &>(tb);
                T * res = static_cast<T *>(t.get_plugin().mk_empty(get_result_signature()));
                t.m_bitsets.project(m_removed_cols, res->m_bitsets);
                TRACE("dl_hassel", tout << "final size: " << res->get_size_estimate_rows() << '\n';);
                return res;
            }
        };

    public:
        virtual table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols) {
            if (!check_kind(t))
                return 0;
            return alloc(project_fn, static_cast<const T &>(t), col_cnt, removed_cols);
        }

    private:
        class rename_fn : public convenient_table_rename_fn {
            unsigned_vector m_out_of_cycle;
        public:
            rename_fn(const table_signature & orig_sig, unsigned permutation_cycle_len, const unsigned * permutation_cycle) 
                : convenient_table_rename_fn(orig_sig, permutation_cycle_len, permutation_cycle) {
                SASSERT(permutation_cycle_len >= 2);
                idx_set cycle_cols;
                for (unsigned i = 0; i < permutation_cycle_len; ++i) {
                    cycle_cols.insert(permutation_cycle[i]);
                }
                for (unsigned i = 0; i < orig_sig.size(); ++i) {
                    if (!cycle_cols.contains(i))
                        m_out_of_cycle.push_back(i);
                }
            }

            virtual table_base * operator()(const table_base & tb) {
                const T & t = static_cast<const T &>(tb);
                T * res = static_cast<T *>(t.get_plugin().mk_empty(get_result_signature()));
                t.m_bitsets.rename(m_cycle, m_out_of_cycle, t, *res, res->m_bitsets);
                TRACE("dl_hassel", tout << "final size: " << res->get_size_estimate_rows() << '\n';);
                return res;
            }
        };

    public:
        virtual table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) {
            if (!check_kind(t))
                return 0;
            return alloc(rename_fn, t.get_signature(), permutation_cycle_len, permutation_cycle);
        }

    private:
        class filter_equal_fn : public table_mutator_fn {
            typename T::bitset_t m_filter;
        public:
            filter_equal_fn(const T & t, const table_element val, unsigned col) :
                m_filter(t.get_num_bits()) {
                ternary_bitvector filter_row(t.get_num_bits(), true);
                ternary_bitvector column(val, t.column_num_bits(col));
                filter_row.mk_idx_eq(t.column_idx(col), column);
                m_filter.add_new_fact(filter_row);
            }

            virtual void operator()(table_base & tb) {
                T & t = static_cast<T &>(tb);
                t.m_bitsets.swap(m_filter.and(t.m_bitsets));
                TRACE("dl_hassel", tout << "final size: " << t.get_size_estimate_rows() << '\n';);
            }
        };

    public:
        virtual table_mutator_fn * mk_filter_equal_fn(const table_base & t, const table_element & value, 
            unsigned col) {
            if (!check_kind(t))
                return 0;
            return alloc(filter_equal_fn, static_cast<const T &>(t), value, col);
        }

    private:
        static bool cond_is_guard(const expr *e, const table_information& t) {
            switch (e->get_kind()) {
            case AST_APP: {
                const app *app = to_app(e);
                switch (app->get_decl_kind()) {
                case OP_AND:
                case OP_OR:
                case OP_NOT:
                    for (unsigned i = 0; i < app->get_num_args(); ++i) {
                        if (!cond_is_guard(app->get_arg(i), t))
                            return false;
                    }
                    return true;

                case OP_EQ: {
                    const expr *a = app->get_arg(0), *b = app->get_arg(1);

                    // column equality is not succinctly representable with TBVs
                    if (is_var(a) && is_var(b))
                        return false;

                    // (= var (concat var foo))
                    if (t.get_bv_util().is_concat(b))
                        return false;

                    return true;}

                case OP_FALSE:
                case OP_TRUE:
                    return true;

                default:
                    return false;
                }
                break;}

            case AST_VAR:
                return true;

            default:
                break;
            }
            return false;
        }

        static void split_cond_guard(app *cond, expr_ref& guard, expr_ref& leftover, const table_information& t) {
            expr_ref_vector guards(guard.m());
            expr_ref_vector leftovers(leftover.m());
            
            if (is_app(cond) && to_app(cond)->get_decl_kind() == OP_AND) {
                app *a = to_app(cond);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr *arg = a->get_arg(i);
                    if (cond_is_guard(arg, t)) {
                        guards.push_back(arg);
                    } else {
                        leftovers.push_back(arg);
                    }
                }
            } else if (cond_is_guard(cond, t)) {
                guard = cond;
                return;
            } else {
                leftover = cond;
                return;
            }

            if (guards.size() > 1) {
                guard = formula_to_dnf(expr_ref(guard.m().mk_and(guards.size(), guards.c_ptr()), guard.m()));
            } else if (guards.size() == 1) {
                guard = guards.get(0);
            }

            if (leftovers.size() > 1) {
                leftover = formula_to_dnf(expr_ref(leftover.m().mk_and(leftovers.size(), leftovers.c_ptr()), leftover.m()));
            } else if (leftovers.size() == 1) {
                leftover = leftovers.get(0);
            }
        }

        class filter_fn : public table_mutator_fn {
            expr_ref m_condition;
            typename T::bitset_t m_filter;
            bit_vector m_empty_bv;
        public:
            filter_fn(const T & t, ast_manager& m, app *condition) :
                m_condition(m), m_filter(t.get_num_bits(), true) {
                m_empty_bv.resize(t.get_num_bits(), false);

                expr_ref guard(m);
                split_cond_guard(condition, guard, m_condition, t);
                if (guard)
                    m_filter.filter(guard, m_empty_bv, t);
            }

            virtual void operator()(table_base & tb) {
                T & t = static_cast<T &>(tb);
                // first apply guard and then run the interpreter on the leftover
                t.m_bitsets.swap(m_filter.and(t.m_bitsets));
                if (m_condition)
                    t.m_bitsets.filter(m_condition, m_empty_bv, t);
                TRACE("dl_hassel", tout << "final size: " << t.get_size_estimate_rows() << '\n';);
            }
        };

    public:
        virtual table_mutator_fn * mk_filter_interpreted_fn(const table_base & t, app * condition) {
            if (!check_kind(t))
                return 0;
            TRACE("dl_hassel", tout << mk_pp(condition, get_ast_manager()) << '\n';);
            return alloc(filter_fn, static_cast<const T &>(t), get_ast_manager(), condition);
        }

    private:
        class filter_proj_fn : public convenient_table_project_fn {
            expr_ref m_condition;
            typename T::bitset_t m_filter;
            bit_vector m_col_list;  // map: col idx -> bool (whether the column is to be removed)
        public:
            filter_proj_fn(const T & t, ast_manager& m, app *condition,
                unsigned col_cnt, const unsigned * removed_cols) :
                convenient_table_project_fn(t.get_signature(), col_cnt, removed_cols),
                m_condition(m), m_filter(t.get_num_bits(), true) {
                t.expand_column_vector(m_removed_cols);

                m_col_list.resize(t.get_num_bits(), false);
                for (unsigned i = 0; i < m_removed_cols.size(); ++i) {
                    m_col_list.set(m_removed_cols[i]);
                }
                m_removed_cols.push_back(UINT_MAX);

                expr_ref guard(m);
                split_cond_guard(condition, guard, m_condition, t);
                if (guard)
                    m_filter.filter(guard, m_col_list, t);
            }

            virtual table_base* operator()(const table_base & tb) {
                const T & t = static_cast<const T &>(tb);
                // first apply guard and then run the interpreter on the leftover
                typename T::bitset_t filtered(t.get_num_bits());
                filtered.swap(m_filter.and(t.m_bitsets));
                if (m_condition)
                    filtered.filter(m_condition, m_col_list, t);

                T * res = static_cast<T *>(t.get_plugin().mk_empty(get_result_signature()));
                filtered.project(m_removed_cols, res->m_bitsets);
                TRACE("dl_hassel", tout << "final size: " << res->get_size_estimate_rows() << '\n';);
                return res;
            }
        };

    public:
        virtual table_transformer_fn * mk_filter_interpreted_and_project_fn(const table_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols) {
            if (!check_kind(t))
                return 0;
            TRACE("dl_hassel", tout << mk_pp(condition, get_ast_manager()) << '\n';);
            return alloc(filter_proj_fn, static_cast<const T &>(t), get_ast_manager(),
                condition, removed_col_cnt, removed_cols);
        }


        virtual table_intersection_filter_fn * mk_filter_by_negation_fn(const table_base & t, 
            const table_base & negated_obj, unsigned joined_col_cnt, const unsigned * t_cols,
            const unsigned * negated_cols) {
            NOT_IMPLEMENTED_YET();
        }
	};

    template<class T>
	class common_hassel_table : public table_base, public table_information {
    public:
        typedef T bitset_t;

        common_hassel_table(table_plugin & p, const table_signature & sig) :
            table_base(p, sig), table_information(p, sig), m_bitsets(get_num_bits()) { }

        virtual table_base * complement(func_decl* p, const table_element * func_columns = 0) const {
            SASSERT(!func_columns);

            if (empty())
                return get_plugin().mk_full(p, get_signature());

            common_hassel_table *res = static_cast<common_hassel_table*>(get_plugin().mk_empty(get_signature()));
            res->m_bitsets.swap(m_bitsets.neg());
            return res;
        }

        virtual void add_fact(const table_fact & f) {
            m_bitsets.add_fact(ternary_bitvector(f, *this));
        }

        virtual void add_new_fact(const table_fact & f) {
            m_bitsets.add_new_fact(ternary_bitvector(f, *this));
        }

        virtual void remove_fact(table_element const* fact) {
            NOT_IMPLEMENTED_YET();
        }

        virtual void reset() {
            m_bitsets.reset();
        }

        void mk_full() {
            m_bitsets.mk_full();
        }

        virtual table_base * clone() const {
            common_hassel_table *res = static_cast<common_hassel_table*>(get_plugin().mk_empty(get_signature()));
            res->m_bitsets = m_bitsets;
            return res;
        }

        virtual bool contains_fact(const table_fact & f) {
            return m_bitsets.contains(ternary_bitvector(f, *this));
        }

        virtual bool empty() const {
            return m_bitsets.empty();
        }

#if Z3DEBUG
        class our_iterator_core : public iterator_core {
            class our_row : public row_interface {
                const our_iterator_core & m_parent;
                const table_information& m_table;
            public:
                our_row(const common_hassel_table & t, const our_iterator_core & parent) : 
                row_interface(t), m_parent(parent), m_table(t) {}

                virtual table_element operator[](unsigned col) const {
                    return m_parent.it->to_number(m_table.column_idx(col), m_table.column_num_bits(col));
                }
            };

            our_row m_row_obj;
            std::set<bit_vector> BVs;
            std::set<bit_vector>::iterator it;

        public:
            our_iterator_core(const common_hassel_table & t, bool finished) :
                m_row_obj(t, *this) {
                if (finished) {
                    it = BVs.end();
                    return;
                }
                t.m_bitsets.expand(BVs);
                it = BVs.begin();
            }

            virtual bool is_finished() const {
                return it == BVs.end();
            }

            virtual row_interface & operator*() {
                SASSERT(!is_finished());
                return m_row_obj;
            }

            virtual void operator++() {
                SASSERT(!is_finished());
                ++it;
            }
    };
#endif

        virtual iterator begin() const {
#if Z3DEBUG
        return mk_iterator(alloc(our_iterator_core, *this, false));
#else
        SASSERT(0 && "begin() disabled");
        return mk_iterator(0);
#endif
        }

        virtual iterator end() const {
#if Z3DEBUG
        return mk_iterator(alloc(our_iterator_core, *this, true));
#else
        SASSERT(0 && "end() disabled");
        return mk_iterator(0);
#endif
        }

        virtual void display(std::ostream & out) const {
            table_information::display(out);
            m_bitsets.display(out);
        }

        virtual void to_formula(relation_signature const& sig, expr_ref& fml) const {
            // TODO
        }

        virtual unsigned get_size_estimate_rows() const {
            return m_bitsets.num_disjs();
        }

        virtual unsigned get_size_estimate_bytes() const {
            return m_bitsets.num_bytes();
        }

        T m_bitsets;
	};

}

#endif
