/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-01.

Revision History:

--*/

#ifndef DL_SPARSE_TABLE_H_
#define DL_SPARSE_TABLE_H_

#include<iostream>
#include<list>
#include<utility>

#include "ast/ast.h"
#include "util/bit_vector.h"
#include "util/buffer.h"
#include "util/hashtable.h"
#include "util/map.h"
#include "util/ref_vector.h"
#include "util/vector.h"

#include "muz/rel/dl_base.h"


namespace datalog {
    class sparse_table;

    class sparse_table_plugin : public table_plugin {
        friend class sparse_table;
    protected:
        class join_project_fn;
        class union_fn;
        class transformer_fn;
        class rename_fn;
        class project_fn;
        class negation_filter_fn;
        class select_equal_and_project_fn;
        class negated_join_fn;

        typedef ptr_vector<sparse_table> sp_table_vector;
        typedef map<table_signature, sp_table_vector *, 
            table_signature::hash, table_signature::eq > table_pool;

        table_pool m_pool;

        void recycle(sparse_table * t);

        void garbage_collect();

        void reset();

        static bool join_involves_functional(const table_signature & s1, const table_signature & s2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);

    public:
        typedef sparse_table table;

        sparse_table_plugin(relation_manager & manager);
        ~sparse_table_plugin() override;

        bool can_handle_signature(const table_signature & s) override
        { return s.size()>0; }

        table_base * mk_empty(const table_signature & s) override;
        sparse_table * mk_clone(const sparse_table & t);

    protected:
        table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        table_join_fn * mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt,
            const unsigned * removed_cols) override;
        table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src,
            const table_base * delta) override;
        table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        table_transformer_fn * mk_select_equal_and_project_fn(const table_base & t,
            const table_element & value, unsigned col) override;
        table_intersection_filter_fn * mk_filter_by_negation_fn(const table_base & t,
                const table_base & negated_obj, unsigned joined_col_cnt,
                const unsigned * t_cols, const unsigned * negated_cols) override;
        table_intersection_join_filter_fn* mk_filter_by_negated_join_fn(
            const table_base & t,
            const table_base & src1,
            const table_base & src2,
            unsigned_vector const& t_cols,
            unsigned_vector const& src_cols,
            unsigned_vector const& src1_cols,
            unsigned_vector const& src2_cols) override;

        static sparse_table const& get(table_base const&);
        static sparse_table& get(table_base&);
        static sparse_table const* get(table_base const*);
        static sparse_table* get(table_base*);

    };

    class entry_storage {
    public:
        typedef size_t store_offset;
    private:
        typedef svector<char, size_t> storage;

        class offset_hash_proc {
            storage & m_storage;
            unsigned m_unique_entry_size;
        public:
            offset_hash_proc(storage & s, unsigned unique_entry_sz) 
                : m_storage(s), m_unique_entry_size(unique_entry_sz) {}
            unsigned operator()(store_offset ofs) const {
                return string_hash(m_storage.c_ptr()+ofs, m_unique_entry_size, 0);
            } 
        };

        class offset_eq_proc {
            storage & m_storage;
            unsigned m_unique_entry_size;
        public:
            offset_eq_proc(storage & s, unsigned unique_entry_sz) 
                : m_storage(s), m_unique_entry_size(unique_entry_sz) {}
            bool operator()(store_offset o1, store_offset o2) const {
                const char * base = m_storage.c_ptr();
                return memcmp(base+o1, base+o2, m_unique_entry_size)==0;
            }
        };

        typedef hashtable<store_offset, offset_hash_proc, offset_eq_proc> storage_indexer;

        static const store_offset NO_RESERVE = UINT_MAX;

        unsigned m_entry_size;
        unsigned m_unique_part_size;
        size_t m_data_size;
        /**
           Invariant: Every or all but one blocks of length \c m_entry_size in the \c m_data vector
           are unique sequences of bytes and have their offset stored in the \c m_data_indexer hashtable. 
           If the offset of the last block is not stored in the hashtable, it is stored in the \c m_reserve
           variable. Otherwise \c m_reserve==NO_RESERVE.

           The size of m_data is actually 8 bytes larger than stated in m_data_size, so that we may 
           deref an uint64_t pointer at the end of the array.
        */
        storage m_data;
        storage_indexer m_data_indexer;
        store_offset m_reserve;
    public:
        entry_storage(unsigned entry_size, unsigned functional_size = 0, unsigned init_size = 0)
            :   m_entry_size(entry_size),
                m_unique_part_size(entry_size-functional_size),
                m_data_indexer(next_power_of_two(std::max(8u,init_size)), 
                    offset_hash_proc(m_data, m_unique_part_size), offset_eq_proc(m_data, m_unique_part_size)),
                m_reserve(NO_RESERVE) {
            SASSERT(entry_size>0);
            SASSERT(functional_size<=entry_size);
            resize_data(init_size);
            resize_data(0);
        }
        entry_storage(const entry_storage &s)
            :   m_entry_size(s.m_entry_size),
                m_unique_part_size(s.m_unique_part_size),
                m_data_size(s.m_data_size),
                m_data(s.m_data), 
                m_data_indexer(next_power_of_two(std::max(8u,s.entry_count())), 
                    offset_hash_proc(m_data, m_unique_part_size), offset_eq_proc(m_data, m_unique_part_size)), 
                m_reserve(s.m_reserve) {
            store_offset after_last=after_last_offset();
            for(store_offset i=0; i<after_last; i+=m_entry_size) {
                m_data_indexer.insert(i);
            }
        }
        
        entry_storage & operator=(const entry_storage & o) {
            m_data_indexer.reset();
            m_entry_size = o.m_entry_size;
            m_unique_part_size = o.m_unique_part_size;
            m_data_size = o.m_data_size;
            m_data = o.m_data;
            m_reserve = o.m_reserve;
            store_offset after_last=after_last_offset();
            for(store_offset i=0; i<after_last; i+=m_entry_size) {
                m_data_indexer.insert(i);
            }
            return *this;
        }

        void reset() {
            resize_data(0);
            m_data_indexer.reset();
            m_reserve = NO_RESERVE;
        }

        unsigned entry_size() const { return m_entry_size; }
        unsigned get_size_estimate_bytes() const;
        char * get(store_offset ofs) { return m_data.begin()+ofs; }
        const char * get(store_offset ofs) const 
        { return const_cast<entry_storage *>(this)->get(ofs); }

        unsigned entry_count() const { return m_data_indexer.size(); }

        store_offset after_last_offset() const { 
            return (m_reserve==NO_RESERVE) ? m_data_size : m_reserve;
        }

        char * begin() { return get(0); }
        const char * begin() const { return get(0); }
        const char * after_last() const { return get(after_last_offset()); }


        bool has_reserve() const { return m_reserve!=NO_RESERVE; }
        store_offset reserve() const { SASSERT(has_reserve()); return m_reserve; }

        void ensure_reserve() {
            if(has_reserve()) {
                SASSERT(m_reserve==m_data_size-m_entry_size);
                return;
            }
            m_reserve = m_data_size;
            resize_data(m_data_size+m_entry_size);
        }

        /**
           \brief Return pointer to the reserve.

           The reserve must exist when the function is called.
        */
        char * get_reserve_ptr() {
            SASSERT(has_reserve());
            return &m_data.get(reserve());
        }

        bool reserve_content_already_present() const {
            SASSERT(has_reserve());
            return m_data_indexer.contains(reserve());
        }

        bool find_reserve_content(store_offset & result) const {
            SASSERT(has_reserve());
            storage_indexer::entry * indexer_entry = m_data_indexer.find_core(reserve());
            if(!indexer_entry) {
                return false;
            }
            result = indexer_entry->get_data();
            return true;
        }

        /**
           \brief Write fact \c f into the reserve at the end of the \c m_data storage.

           If the reserve does not exist, this function creates it.
        */
        void write_into_reserve(const char * data) {
            ensure_reserve();
            memcpy(get_reserve_ptr(), data, m_entry_size);
        }

        /**
           \brief If the fact in reserve is not in the table, insert it there and return true;
           otherwise return false.

           When a fact is inserted into the table, the reserve becomes part of the table and
           is no longer a reserve.
        */
        bool insert_reserve_content();
        store_offset insert_or_get_reserve_content();
        bool remove_reserve_content();
        /**
           Remove data at the offset \c ofs.

           Data with offset lower than \c ofs are not be modified by this function, data with 
           higher offset may be moved.
        */
        void remove_offset(store_offset ofs);


        //the following two operations allow breaking of the object invariant!
        void resize_data(size_t sz) {
            m_data_size = sz;
            if (sz + sizeof(uint64_t) < sz) {
                throw default_exception("overflow resizing data section for sparse table");
            }
            m_data.resize(sz + sizeof(uint64_t));
        }

        bool insert_offset(store_offset ofs) {
            return m_data_indexer.insert_if_not_there(ofs)==ofs;
        }
    };

    class sparse_table : public table_base {
        friend class sparse_table_plugin;
        friend class sparse_table_plugin::join_project_fn;
        friend class sparse_table_plugin::union_fn;
        friend class sparse_table_plugin::transformer_fn;
        friend class sparse_table_plugin::rename_fn;
        friend class sparse_table_plugin::project_fn;
        friend class sparse_table_plugin::negation_filter_fn;
        friend class sparse_table_plugin::select_equal_and_project_fn;

        class our_iterator_core;
        class key_indexer;
        class general_key_indexer;
        class full_signature_key_indexer;
        typedef entry_storage::store_offset store_offset;

        
        class column_info {
            unsigned m_big_offset;
            unsigned m_small_offset;
            uint64_t m_mask;
            uint64_t m_write_mask;
        public:
            unsigned m_offset; //!< in bits
            unsigned m_length; //!< in bits

            column_info(unsigned offset, unsigned length) \
                    : m_big_offset(offset/8), 
                    m_small_offset(offset%8),
                    m_mask( length==64 ? ULLONG_MAX : (static_cast<uint64_t>(1)<<length)-1 ),
                    m_write_mask( ~(m_mask<<m_small_offset) ),
                    m_offset(offset), 
                    m_length(length) {
                SASSERT(length<=64);
                SASSERT(length+m_small_offset<=64);
            }
            table_element get(const char * rec) const {
                const uint64_t * ptr = reinterpret_cast<const uint64_t*>(rec+m_big_offset);
                uint64_t res = *ptr;
                res>>=m_small_offset;
                res&=m_mask;
                return res;
            }
            void set(char * rec, table_element val) const {
                SASSERT( (val&~m_mask)==0 ); //the value fits into the column
                uint64_t * ptr = reinterpret_cast<uint64_t*>(rec+m_big_offset);
                *ptr&=m_write_mask;
                *ptr|=val<<m_small_offset;
            }
            unsigned next_ofs() const { return m_offset+m_length; }
        };
        class column_layout : public svector<column_info> {

            void make_byte_aligned_end(unsigned col_index);
        public:

            unsigned m_entry_size;
            /**
                Number of last bytes which correspond to functional columns in the signature.
            */
            unsigned m_functional_part_size;
            unsigned m_functional_col_cnt;

            column_layout(const table_signature & sig);

            table_element get(const char * rec, unsigned col) const {
                return (*this)[col].get(rec);
            }
            void set(char * rec, unsigned col, table_element val) const {
                return (*this)[col].set(rec, val);
            }
        };
        

        typedef svector<unsigned> key_spec;        //sequence of columns in a key
        typedef svector<table_element> key_value;  //values of key columns
        typedef map<key_spec, key_indexer*, svector_hash_proc<unsigned_hash>,
            vector_eq_proc<key_spec> > key_index_map;

        static const store_offset NO_RESERVE = UINT_MAX;

        column_layout m_column_layout;
        unsigned m_fact_size;
        entry_storage m_data;
        mutable key_index_map m_key_indexes;


        const char * get_at_offset(store_offset i) const {
            return m_data.get(i);
        }

        table_element get_cell(store_offset ofs, unsigned column) const {
            return m_column_layout.get(m_data.get(ofs), column);
        }

        void set_cell(store_offset ofs, unsigned column, table_element val) {
            m_column_layout.set(m_data.get(ofs), column, val);
        }

        void write_into_reserve(const table_element* f);

        /**
           \brief Return reference to an indexer over columns in \c key_cols.
           
           An indexer can retrieve a sequence of offsets that with \c key_cols columns equal to
           the specified key. Indexers are populated lazily -- they remember the position of the
           last fact they contain, and when an indexer is retrieved by the \c get_key_indexer function,
           all the new facts are added into the indexer.

           When a fact is removed from the table, all indexers are destroyed. This is not an extra 
           expense in the current use scenario, because we first perform all fact removals and do the 
           joins only after that (joins are the only operations that lead to index construction).
        */
        key_indexer& get_key_indexer(unsigned key_len, const unsigned * key_cols) const;

        void reset_indexes();

        static void copy_columns(const column_layout & src_layout, const column_layout & dest_layout, 
            unsigned start_index, unsigned after_last, const char * src, char * dest, 
            unsigned & dest_idx, unsigned & pre_projection_idx, const unsigned * & next_removed);

        /**
            \c array \c removed_cols contains column indexes to be removed in ascending order and
            is terminated by a number greater than the highest column index of a join the two tables.
            This is to simplify the traversal of the array when building facts.
         */
        static void concatenate_rows(const column_layout & layout1, const column_layout & layout2,
            const column_layout & layout_res, const char * ptr1, const char * ptr2, char * res,
            const unsigned * removed_cols);

        /**
           \brief Perform join-project between t1 and t2 iterating through t1 and retrieving relevant
           columns from t2 using indexing.

           \c array \c removed_cols contains column indexes to be removed in ascending order and
           is terminated by a number greater than the highest column index of a join the two tables.
           This is to simplify the traversal of the array when building facts.

           \c tables_swapped value means that the resulting facts should contain facts from t2 first,
           instead of the default behavior that would concatenate the two facts as \c (t1,t2).

           \remark The function is called \c self_agnostic_join since, unlike the virtual method
           \c join, it is static and therefore allows to easily swap the roles of the two joined
           tables (the indexed and iterated one) in a way that is expected to give better performance.
        */
        static void self_agnostic_join_project(const sparse_table & t1, const sparse_table & t2,
            unsigned joined_col_cnt, const unsigned * t1_joined_cols, const unsigned * t2_joined_cols,
            const unsigned * removed_cols, bool tables_swapped, sparse_table & result);


        /**
           If the fact at \c data (in table's native representation) is not in the table,
           add it and return true. Otherwise return false.
        */
        bool add_fact(const char * data);

        bool add_reserve_content();

        void garbage_collect();

        sparse_table(sparse_table_plugin & p, const table_signature & sig, unsigned init_capacity=0);
        sparse_table(const sparse_table & t);
        ~sparse_table() override;
    public:

        void deallocate() override {
            get_plugin().recycle(this);
        }

        unsigned row_count() const { return m_data.entry_count(); }

        sparse_table_plugin & get_plugin() const 
        { return static_cast<sparse_table_plugin &>(table_base::get_plugin()); }

        bool empty() const override { return row_count()==0; }
        void add_fact(const table_fact & f) override;
        bool contains_fact(const table_fact & f) const override;
        bool fetch_fact(table_fact & f) const override;
        void ensure_fact(const table_fact & f) override;
        void remove_fact(const table_element* fact) override;
        void reset() override;

        table_base * clone() const override;

        table_base::iterator begin() const override;
        table_base::iterator end() const override;

        unsigned get_size_estimate_rows() const override { return row_count(); }
        unsigned get_size_estimate_bytes() const override;
        bool knows_exact_size() const override { return true; }
    };

 };

#endif /* DL_SPARSE_TABLE_H_ */
