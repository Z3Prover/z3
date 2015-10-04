/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_sparse_table.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-24.

Revision History:

--*/

#include<utility>
#include"dl_context.h"
#include"dl_util.h"
#include"dl_sparse_table.h"

namespace datalog {


    // -----------------------------------
    //
    // entry_storage
    //
    // -----------------------------------
    
    entry_storage::store_offset entry_storage::insert_or_get_reserve_content() {
        SASSERT(has_reserve());
        store_offset entry_ofs = m_data_indexer.insert_if_not_there(m_reserve);
        if (m_reserve == entry_ofs) {
            //entry inserted, so reserve is no longer a reserve
            m_reserve = NO_RESERVE;
        }
        return entry_ofs;
    }
    bool entry_storage::insert_reserve_content() {
        SASSERT(has_reserve());
        store_offset entry_ofs = m_data_indexer.insert_if_not_there(m_reserve);
        if (m_reserve == entry_ofs) {
            //entry inserted, so reserve is no longer a reserve
            m_reserve = NO_RESERVE;
            return true;
        }
        return false;
    }

    bool entry_storage::remove_reserve_content() {
        SASSERT(has_reserve());
        store_offset entry_ofs;
        if (!find_reserve_content(entry_ofs)) {
            //the fact was not in the table
            return false;
        }
        remove_offset(entry_ofs);
        return true;
    }

    void entry_storage::remove_offset(store_offset ofs) {
        m_data_indexer.remove(ofs);
        store_offset last_ofs = after_last_offset() - m_entry_size;
        if (ofs!=last_ofs) {
            SASSERT(ofs + m_entry_size <= last_ofs);
            //we don't want any holes, so we put the last element at the place
            //of the removed one
            m_data_indexer.remove(last_ofs);
            char * base = &m_data.get(0);
            memcpy(base+ofs, base+last_ofs, m_entry_size);
            m_data_indexer.insert(ofs);
        }
        if (has_reserve()) {
            //we already have a reserve, so we need to shrink a little to keep having just one
            resize_data(m_data_size-m_entry_size);
        }
        m_reserve=last_ofs;
    }

    unsigned entry_storage::get_size_estimate_bytes() const {
        size_t sz = m_data.capacity();
        sz += m_data_indexer.capacity()*sizeof(storage_indexer::entry);
        return static_cast<unsigned>(sz);
    }

    // -----------------------------------
    //
    // sparse_table::column_layout
    //
    // -----------------------------------

    unsigned get_domain_length(uint64 dom_size) {
        SASSERT(dom_size>0);

        unsigned length = 0;

        unsigned dom_size_sm;
        if (dom_size>UINT_MAX) {
            dom_size_sm = static_cast<unsigned>(dom_size>>32);
            length += 32;
            if ( (dom_size&UINT_MAX)!=0 && dom_size_sm!=UINT_MAX ) {
                dom_size_sm++;
            }
        }
        else {
            dom_size_sm=static_cast<unsigned>(dom_size);
        }
        if (dom_size_sm == 1) {
            length += 1; //unary domains
        }
        else if (dom_size_sm > 0x80000000u) {
            length += 32;
        }
        else {
            length += get_num_1bits(next_power_of_two(dom_size_sm)-1); //ceil(log2(dom_size))
        }
        return length;
    }

    sparse_table::column_layout::column_layout(const table_signature & sig)
            : m_functional_col_cnt(sig.functional_columns()) {
        SASSERT(sig.size() > 0);
        unsigned ofs = 0;
        unsigned sig_sz = sig.size();
        unsigned first_functional = sig_sz-m_functional_col_cnt;
        for (unsigned i=0; i<sig_sz; i++) {
            uint64 dom_size = sig[i];
            unsigned length = get_domain_length(dom_size);
            SASSERT(length>0);
            SASSERT(length<=64);
            
            if (size() > 0 && (length > 54 || i == first_functional)) {
                //large domains must start byte-aligned, as well as functional columns
                make_byte_aligned_end(size()-1);
                ofs = back().next_ofs();
            }

            push_back(column_info(ofs, length));
            ofs += length;
        }
        make_byte_aligned_end(size()-1);
        SASSERT(back().next_ofs()%8 == 0);//the entries must be aligned to whole bytes
        m_entry_size = back().next_ofs()/8;
        if (m_functional_col_cnt) { 
            SASSERT((*this)[first_functional].m_offset%8 == 0);
            m_functional_part_size = m_entry_size - (*this)[first_functional].m_offset/8;
        }
        else {
            m_functional_part_size = 0;
        }
    }

    void sparse_table::column_layout::make_byte_aligned_end(unsigned col_index0) {
        unsigned ofs = (*this)[col_index0].next_ofs();
        unsigned ofs_bit_part = ofs%8;
        unsigned rounded_ofs = (ofs_bit_part == 0) ? ofs : (ofs+8-ofs_bit_part);

        if (rounded_ofs!=ofs) {
            SASSERT(rounded_ofs>ofs);
            int diff = rounded_ofs-ofs;
            unsigned col_idx = col_index0+1;
            while(diff!=0) {
                //we should always be able to fix the alignment by the time we reach zero
                SASSERT(col_idx>0);
                col_idx--;
                column_info & ci = (*this)[col_idx];
                unsigned new_length = ci.m_length;
                if (ci.m_length < 64) {
                    unsigned swallowed = std::min(64-static_cast<int>(ci.m_length), diff);
                    diff -= swallowed;
                    new_length += swallowed;
                }
                unsigned new_ofs = ci.m_offset+diff;
                ci = column_info(new_ofs, new_length);
            }
        }

        SASSERT(rounded_ofs%8 == 0);
        SASSERT((*this)[col_index0].next_ofs()%8 == 0);
    }

    // -----------------------------------
    //
    // sparse_table
    //
    // -----------------------------------

    class sparse_table::our_iterator_core : public iterator_core {

        class our_row : public row_interface {
            const our_iterator_core & m_parent;
        public:
            our_row(const sparse_table & t, const our_iterator_core & parent) : 
              row_interface(t), 
              m_parent(parent) {}

            virtual table_element operator[](unsigned col) const {
                return m_parent.m_layout.get(m_parent.m_ptr, col);
            }

        };

        const char * m_end;
        const char * m_ptr;
        unsigned m_fact_size;
        our_row m_row_obj;
        const column_layout & m_layout;

    public:
        our_iterator_core(const sparse_table & t, bool finished) : 
          m_end(t.m_data.after_last()),
          m_ptr(finished ? m_end : t.m_data.begin()),
          m_fact_size(t.m_fact_size),
          m_row_obj(t, *this),
          m_layout(t.m_column_layout) {}

        virtual bool is_finished() const {
            return m_ptr == m_end;
        }

        virtual row_interface & operator*() {
            SASSERT(!is_finished());
            return m_row_obj;
        }
        virtual void operator++() {
            SASSERT(!is_finished());
            m_ptr+=m_fact_size;
        }
    };

    class sparse_table::key_indexer {
    protected:
        unsigned_vector m_key_cols;
    public:
        typedef const store_offset * offset_iterator;

        /**
           Iterators returned by \c begin() and \c end() are valid only as long as the \c query_result
           object that returned them exists.
        */
        struct query_result {
        private:
            bool m_singleton;
            union {
                store_offset m_single_result;
                struct {
                    offset_iterator begin;
                    offset_iterator end;
                } m_many;
            };
        public:
            /**
               \brief Empty result.
            */
            query_result() : m_singleton(false) {
                m_many.begin = 0;
                m_many.end = 0;
            }
            query_result(offset_iterator begin, offset_iterator end) : m_singleton(false) {
                m_many.begin = begin;
                m_many.end = end;
            }
            query_result(store_offset single_result) : m_singleton(true), m_single_result(single_result) {}

            offset_iterator begin() const { return m_singleton ? &m_single_result : m_many.begin; }
            offset_iterator end() const { return m_singleton ? (&m_single_result+1) : m_many.end; }
            bool empty() const { return begin() == end(); }
        };

        key_indexer(unsigned key_len, const unsigned * key_cols) 
            : m_key_cols(key_len, key_cols) {}

        virtual ~key_indexer() {}

        virtual void update(const sparse_table & t) {}

        virtual query_result get_matching_offsets(const key_value & key) const = 0;
    };


    class sparse_table::general_key_indexer : public key_indexer {
        typedef svector<store_offset> offset_vector;
        typedef size_t_map<offset_vector> index_map;

        index_map m_map;
        mutable entry_storage m_keys;
        store_offset m_first_nonindexed;


        void key_to_reserve(const key_value & key) const {
            m_keys.ensure_reserve();
            m_keys.write_into_reserve((char *)(key.c_ptr()));
        }

        offset_vector & get_matching_offset_vector(const key_value & key) {
            key_to_reserve(key);
            store_offset ofs = m_keys.insert_or_get_reserve_content();
            index_map::entry * e = m_map.find_core(ofs);
            if (!e) {
                TRACE("dl_table_relation", tout << "inserting\n";);
                e = m_map.insert_if_not_there2(ofs, offset_vector());
            }
            return e->get_data().m_value;
        }
    public:
        general_key_indexer(unsigned key_len, const unsigned * key_cols) 
            : key_indexer(key_len, key_cols),
            m_keys(key_len*sizeof(table_element)), 
            m_first_nonindexed(0) {}

        virtual void update(const sparse_table & t) {
            if (m_first_nonindexed == t.m_data.after_last_offset()) {
                return;
            }
            SASSERT(m_first_nonindexed<t.m_data.after_last_offset());
            //we need to add new facts into the index

            unsigned key_len = m_key_cols.size();

            store_offset ofs = m_first_nonindexed;
            store_offset after_last = t.m_data.after_last_offset();

            key_value key;
            key.resize(key_len);

            offset_vector * index_entry;
            DEBUG_CODE( index_entry = 0; );
            bool key_modified = true;

            for (; ofs!=after_last; ofs+=t.m_fact_size) {
                for (unsigned i=0; i<key_len; i++) {
                    table_element col_val = t.get_cell(ofs, m_key_cols[i]);
                    if (key[i]!=col_val) {
                        key[i] = col_val;
                        key_modified = true;
                    }
                }
                
                if (key_modified) {
                    index_entry = &get_matching_offset_vector(key);
                    key_modified = false;
                }
                SASSERT(index_entry);
                //here we insert the offset of the fact in m_data vector into the indexer
                index_entry->insert(ofs);
            }

            m_first_nonindexed = t.m_data.after_last_offset();
        }

        virtual query_result get_matching_offsets(const key_value & key) const {
            key_to_reserve(key);
            store_offset ofs;
            if (!m_keys.find_reserve_content(ofs)) {
                return query_result();
            }
            index_map::entry * e = m_map.find_core(ofs);
            if (!e) {
                return query_result();
            }
            const offset_vector & res = e->get_data().m_value;
            return query_result(res.begin(), res.end());
        }
    };

    /**
       When doing lookup using this index, the content of the reserve in sparse_table::m_data changes.
    */
    class sparse_table::full_signature_key_indexer : public key_indexer {
        const sparse_table & m_table;

        /**
           Permutation of key columns to make it into table facts. If empty, no permutation is necessary.
        */
        unsigned_vector m_permutation;
        mutable table_fact m_key_fact;
    public:

        static bool can_handle(unsigned key_len, const unsigned * key_cols, const sparse_table & t) {
            unsigned non_func_cols = t.get_signature().first_functional();
            if (key_len!=non_func_cols) {
                return false;
            }
            counter ctr;
            ctr.count(key_len, key_cols);
            if (ctr.get_max_counter_value()!=1 || ctr.get_max_positive()!=non_func_cols-1) {
                return false;
            }
            SASSERT(ctr.get_positive_count() == non_func_cols);
            return true;
        }

        full_signature_key_indexer(unsigned key_len, const unsigned * key_cols, const sparse_table & t) 
                : key_indexer(key_len, key_cols),
                m_table(t) {
            SASSERT(can_handle(key_len, key_cols, t));
            
            m_permutation.resize(key_len);
            for (unsigned i=0; i<key_len; i++) {
                //m_permutation[m_key_cols[i]] = i;
                m_permutation[i] = m_key_cols[i];
            }
            m_key_fact.resize(t.get_signature().size());
        }

        virtual ~full_signature_key_indexer() {}

        virtual query_result get_matching_offsets(const key_value & key) const {
            unsigned key_len = m_key_cols.size();
            for (unsigned i=0; i<key_len; i++) {
                m_key_fact[m_permutation[i]] = key[i];
            }
            //We will change the content of the reserve; which does not change the 'high-level' 
            //content of the table.
            sparse_table & t = const_cast<sparse_table&>(m_table);
            t.write_into_reserve(m_key_fact.c_ptr());

            store_offset res;
            if (!t.m_data.find_reserve_content(res)) {
                return query_result();
            }
            return query_result(res);
        }
    };

    sparse_table::sparse_table(sparse_table_plugin & p, const table_signature & sig, unsigned init_capacity)
            : table_base(p, sig), 
            m_column_layout(sig),
            m_fact_size(m_column_layout.m_entry_size),
            m_data(m_fact_size, m_column_layout.m_functional_part_size, init_capacity) {}
    
    sparse_table::sparse_table(const sparse_table & t)
            : table_base(t.get_plugin(), t.get_signature()), 
            m_column_layout(t.m_column_layout),
            m_fact_size(t.m_fact_size),
            m_data(t.m_data) {}

    table_base * sparse_table::clone() const {
        return get_plugin().mk_clone(*this);
    }

    sparse_table::~sparse_table() {
        reset_indexes();
    }

    void sparse_table::reset() {
        reset_indexes();
        m_data.reset();
    }

    table_base::iterator sparse_table::begin() const {
        return mk_iterator(alloc(our_iterator_core, *this, false));
    }

    table_base::iterator sparse_table::end() const {
        return mk_iterator(alloc(our_iterator_core, *this, true));
    }

    sparse_table::key_indexer& sparse_table::get_key_indexer(unsigned key_len, 
            const unsigned * key_cols) const {
            verbose_action  _va("get_key_indexer");

#if Z3DEBUG
        //We allow indexes only on non-functional columns because we want to be able to modify them 
        //without having to worry about updating indexes.
        //Maybe we might keep a list of indexes that contain functional columns and on an update reset 
        //only those.
        SASSERT(key_len == 0 || 
            counter().count(key_len, key_cols).get_max_positive()<get_signature().first_functional());
#endif
        key_spec kspec;
        kspec.append(key_len, key_cols);
        key_index_map::entry * key_map_entry = m_key_indexes.insert_if_not_there2(kspec, 0);
        if (!key_map_entry->get_data().m_value) {
            if (full_signature_key_indexer::can_handle(key_len, key_cols, *this)) {
                key_map_entry->get_data().m_value = alloc(full_signature_key_indexer, key_len, key_cols, *this);
            }
            else {
                key_map_entry->get_data().m_value = alloc(general_key_indexer, key_len, key_cols);
            }
        }
        key_indexer & indexer = *key_map_entry->get_data().m_value;
        indexer.update(*this);
        return indexer;
    }

    void sparse_table::reset_indexes() {
        key_index_map::iterator kmit = m_key_indexes.begin();
        key_index_map::iterator kmend = m_key_indexes.end();
        for (; kmit!=kmend; ++kmit) {
            dealloc((*kmit).m_value);
        }
        m_key_indexes.reset();
    }

    void sparse_table::write_into_reserve(const table_element* f) {
        TRACE("dl_table_relation", tout << "\n";);
        m_data.ensure_reserve();
        char * reserve = m_data.get_reserve_ptr();
        unsigned col_cnt = m_column_layout.size();
        for (unsigned i = 0; i < col_cnt; ++i) {
            SASSERT(f[i] < get_signature()[i]); //the value fits into the table signature
            m_column_layout.set(reserve, i, f[i]);
        }
    }

    bool sparse_table::add_fact(const char * data) {
        verbose_action  _va("add_fact", 10);
        m_data.write_into_reserve(data);
        return add_reserve_content();
    }

    void sparse_table::add_fact(const table_fact & f) {
        write_into_reserve(f.c_ptr());
        add_reserve_content();
    }

    bool sparse_table::add_reserve_content() {
        return m_data.insert_reserve_content();
    }

    bool sparse_table::contains_fact(const table_fact & f) const {
        verbose_action  _va("contains_fact", 2);
        sparse_table & t = const_cast<sparse_table &>(*this);
        t.write_into_reserve(f.c_ptr());
        unsigned func_col_cnt = get_signature().functional_columns();
        if (func_col_cnt == 0) {
            return t.m_data.reserve_content_already_present();
        }
        else {
            store_offset ofs;
            if (!t.m_data.find_reserve_content(ofs)) {
                return false;
            }
            unsigned sz = get_signature().size();
            for (unsigned i=func_col_cnt; i<sz; i++) {
                if (t.get_cell(ofs, i)!=f[i]) {
                    return false;
                }
            }
            return true;
        }
    }

    bool sparse_table::fetch_fact(table_fact & f) const {
        verbose_action  _va("fetch_fact", 2);
        const table_signature & sig = get_signature();
        SASSERT(f.size() == sig.size());
        if (sig.functional_columns() == 0) {
            return contains_fact(f);
        }
        else {
            sparse_table & t = const_cast<sparse_table &>(*this);
            t.write_into_reserve(f.c_ptr());
            store_offset ofs;
            if (!t.m_data.find_reserve_content(ofs)) {
                return false;
            }
            unsigned sz = sig.size();
            for (unsigned i=sig.first_functional(); i<sz; i++) {
                f[i] = t.get_cell(ofs, i);
            }
            return true;
        }
    }

    /**
       In this function we modify the content of table functional columns without reseting indexes.
       This is ok as long as we do not allow indexing on functional columns.
    */
    void sparse_table::ensure_fact(const table_fact & f) {
        verbose_action  _va("ensure_fact", 2);
        const table_signature & sig = get_signature();
        if (sig.functional_columns() == 0) {
            add_fact(f);
        }
        else {
            write_into_reserve(f.c_ptr());
            store_offset ofs;
            if (!m_data.find_reserve_content(ofs)) {
                add_fact(f);
                return;
            }
            unsigned sz = sig.size();
            for (unsigned i=sig.first_functional(); i<sz; i++) {
                set_cell(ofs, i, f[i]);
            }
        }
    }

    void sparse_table::remove_fact(const table_element*  f) {
        verbose_action  _va("remove_fact", 2);
        //first insert the fact so that we find it's original location and remove it
        write_into_reserve(f);
        if (!m_data.remove_reserve_content()) {
            //the fact was not in the table
            return;
        }
        reset_indexes();
    }

    void sparse_table::copy_columns(const column_layout & src_layout, const column_layout & dest_layout,
            unsigned start_index, unsigned after_last, const char * src, char * dest, 
            unsigned & dest_idx, unsigned & pre_projection_idx, const unsigned * & next_removed) {
        for (unsigned i=start_index; i<after_last; i++, pre_projection_idx++) {
            if (*next_removed == pre_projection_idx) {
                next_removed++;
                continue;
            }
            SASSERT(*next_removed>pre_projection_idx);
            dest_layout.set(dest, dest_idx++, src_layout.get(src, i));
        }
    }

    void sparse_table::concatenate_rows(const column_layout & layout1, const column_layout & layout2,
            const column_layout & layout_res, const char * ptr1, const char * ptr2, char * res,
            const unsigned * removed_cols) {
        unsigned t1non_func = layout1.size()-layout1.m_functional_col_cnt;
        unsigned t2non_func = layout2.size()-layout2.m_functional_col_cnt;
        unsigned t1cols = layout1.size();
        unsigned t2cols = layout2.size();
        unsigned orig_i = 0;
        unsigned res_i = 0;
        const unsigned * next_removed = removed_cols;
        copy_columns(layout1, layout_res, 0, t1non_func, ptr1, res, res_i, orig_i, next_removed);
        copy_columns(layout2, layout_res, 0, t2non_func, ptr2, res, res_i, orig_i, next_removed);
        copy_columns(layout1, layout_res, t1non_func, t1cols, ptr1, res, res_i, orig_i, next_removed);
        copy_columns(layout2, layout_res, t2non_func, t2cols, ptr2, res, res_i, orig_i, next_removed);
    }

    void sparse_table::garbage_collect() {
        if (memory::above_high_watermark()) {
            get_plugin().garbage_collect();
        }       
        if (memory::above_high_watermark()) {
            IF_VERBOSE(1, verbose_stream() << "Ran out of memory while filling table of size: " << get_size_estimate_rows() << " rows " << get_size_estimate_bytes() << " bytes\n";);
            throw out_of_memory_error();
        }       
    }

    void sparse_table::self_agnostic_join_project(const sparse_table & t1, const sparse_table & t2,
            unsigned joined_col_cnt, const unsigned * t1_joined_cols, const unsigned * t2_joined_cols,
            const unsigned * removed_cols, bool tables_swapped, sparse_table & result) {

        verbose_action _va("join_project", 1);
        unsigned t1_entry_size = t1.m_fact_size;
        unsigned t2_entry_size = t2.m_fact_size;

        size_t t1idx = 0;
        size_t t1end = t1.m_data.after_last_offset();

        TRACE("dl_table_relation", 
              tout << "joined_col_cnt: " << joined_col_cnt << "\n";
              tout << "t1_entry_size:  " << t1_entry_size << "\n";
              tout << "t2_entry_size:  " << t2_entry_size << "\n";
              t1.display(tout);
              t2.display(tout);
              tout << (&t1) << " " << (&t2) << " " << (&result) << "\n";
              );

        if (joined_col_cnt == 0) {
            size_t t2idx = 0;
            size_t t2end = t2.m_data.after_last_offset();

            for (; t1idx!=t1end; t1idx+=t1_entry_size) {
                for (t2idx = 0; t2idx != t2end; t2idx += t2_entry_size) {
                    result.m_data.ensure_reserve();
                    result.garbage_collect();
                    char * res_reserve = result.m_data.get_reserve_ptr();
                    char const* t1ptr = t1.get_at_offset(t1idx);
                    char const* t2ptr = t2.get_at_offset(t2idx);
                    if (tables_swapped) {
                        concatenate_rows(t2.m_column_layout, t1.m_column_layout, result.m_column_layout,
                            t2ptr, t1ptr, res_reserve, removed_cols);
                    } else {
                        concatenate_rows(t1.m_column_layout, t2.m_column_layout, result.m_column_layout,
                            t1ptr, t2ptr, res_reserve, removed_cols);
                    }
                    result.add_reserve_content();
                }
            }
            return;
        }

        key_value t1_key;
        t1_key.resize(joined_col_cnt);
        key_indexer& t2_indexer = t2.get_key_indexer(joined_col_cnt, t2_joined_cols);

        bool key_modified = true;
        key_indexer::query_result t2_offsets;

        for (; t1idx != t1end; t1idx += t1_entry_size) {
            for (unsigned i = 0; i < joined_col_cnt; i++) {
                table_element val = t1.m_column_layout.get(t1.get_at_offset(t1idx), t1_joined_cols[i]);
                TRACE("dl_table_relation", tout << "val: " << val << " " << t1idx << " " << t1_joined_cols[i] << "\n";);
                if (t1_key[i] != val) {
                    t1_key[i] = val;
                    key_modified = true;
                }
            }
            if (key_modified) {
                t2_offsets = t2_indexer.get_matching_offsets(t1_key);
                key_modified = false;
            }

            if (t2_offsets.empty()) {
                continue;
            }
            
            key_indexer::offset_iterator t2ofs_it  = t2_offsets.begin();
            key_indexer::offset_iterator t2ofs_end = t2_offsets.end();
            for (; t2ofs_it != t2ofs_end; ++t2ofs_it) {
                store_offset t2ofs = *t2ofs_it;
                result.m_data.ensure_reserve();
                result.garbage_collect();
                char * res_reserve = result.m_data.get_reserve_ptr();
                char const * t1ptr = t1.get_at_offset(t1idx);
                char const * t2ptr = t2.get_at_offset(t2ofs);
                if (tables_swapped) {
                    concatenate_rows(t2.m_column_layout, t1.m_column_layout, result.m_column_layout,
                        t2ptr, t1ptr, res_reserve, removed_cols);
                } else {
                    concatenate_rows(t1.m_column_layout, t2.m_column_layout, result.m_column_layout,
                        t1ptr, t2ptr, res_reserve, removed_cols);
                }
                result.add_reserve_content();
            }
        }
    }


    // -----------------------------------
    //
    // sparse_table_plugin
    //
    // -----------------------------------

    sparse_table_plugin::sparse_table_plugin(relation_manager & manager) 
        : table_plugin(symbol("sparse"), manager) {}

    sparse_table_plugin::~sparse_table_plugin() {
        reset();
    }

    sparse_table const& sparse_table_plugin::get(table_base const& t) { return dynamic_cast<sparse_table const&>(t); }
    sparse_table& sparse_table_plugin::get(table_base& t) { return dynamic_cast<sparse_table&>(t); }
    sparse_table const* sparse_table_plugin::get(table_base const* t) { return dynamic_cast<sparse_table const*>(t); }
    sparse_table* sparse_table_plugin::get(table_base* t) { return dynamic_cast<sparse_table*>(t); }


    void sparse_table_plugin::reset() {
        table_pool::iterator it = m_pool.begin();
        table_pool::iterator end = m_pool.end();
        for (; it!=end; ++it) {
            sp_table_vector * vect = it->m_value;
            sp_table_vector::iterator vit = vect->begin();
            sp_table_vector::iterator vend = vect->end();
            for (; vit!=vend; ++vit) {
                (*vit)->destroy(); //calling deallocate() would only put the table back into the pool
            }
            dealloc(vect);
        }
        m_pool.reset();
    }

    void sparse_table_plugin::garbage_collect() {
        IF_VERBOSE(2, verbose_stream() << "garbage collecting "<< memory::get_allocation_size() << " bytes down to ";);
        reset();
        IF_VERBOSE(2, verbose_stream() << memory::get_allocation_size() << " bytes\n";);
    }

    void sparse_table_plugin::recycle(sparse_table * t) {
        verbose_action  _va("recycle", 2);
        const table_signature & sig = t->get_signature();
        t->reset();

        table_pool::entry * e = m_pool.insert_if_not_there2(sig, 0);
        sp_table_vector * & vect = e->get_data().m_value;
        if (vect == 0) {
            vect = alloc(sp_table_vector);
        }
        IF_VERBOSE(12, verbose_stream() << "Recycle: " << t->get_size_estimate_bytes() << "\n";);

        vect->push_back(t);
    }

    table_base * sparse_table_plugin::mk_empty(const table_signature & s) {
        SASSERT(can_handle_signature(s));

        sp_table_vector * vect;
        if (!m_pool.find(s, vect) || vect->empty()) {
            return alloc(sparse_table, *this, s);
        }
        sparse_table * res = vect->back();
        vect->pop_back();
        return res;
    }

    sparse_table * sparse_table_plugin::mk_clone(const sparse_table & t) {
        sparse_table * res = get(mk_empty(t.get_signature()));
        res->m_data = t.m_data;
        return res;
    }


    bool sparse_table_plugin::join_involves_functional(const table_signature & s1, const table_signature & s2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (col_cnt == 0) {
            return false;
        }
        return counter().count(col_cnt, cols1).get_max_positive()>=s1.first_functional()
            || counter().count(col_cnt, cols2).get_max_positive()>=s2.first_functional();
    }


    class sparse_table_plugin::join_project_fn : public convenient_table_join_project_fn {
    public:
        join_project_fn(const table_signature & t1_sig, const table_signature & t2_sig, unsigned col_cnt, 
                const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
                const unsigned * removed_cols) 
                : convenient_table_join_project_fn(t1_sig, t2_sig, col_cnt, cols1, cols2, 
                removed_col_cnt, removed_cols) {
            m_removed_cols.push_back(UINT_MAX);
        }

        virtual table_base * operator()(const table_base & tb1, const table_base & tb2) {

            const sparse_table & t1 = get(tb1);
            const sparse_table & t2 = get(tb2);

            sparse_table_plugin & plugin = t1.get_plugin();

            sparse_table * res = get(plugin.mk_empty(get_result_signature()));

            //If we join with some intersection, want to iterate over the smaller table and
            //do indexing into the bigger one. If we simply do a product, we want the bigger
            //one to be at the outer iteration (then the small one will hopefully fit into 
            //the cache)
            if ( (t1.row_count() > t2.row_count()) == (!m_cols1.empty()) ) {
                sparse_table::self_agnostic_join_project(t2, t1, m_cols1.size(), m_cols2.c_ptr(), 
                    m_cols1.c_ptr(), m_removed_cols.c_ptr(), true, *res);
            }
            else {
                sparse_table::self_agnostic_join_project(t1, t2, m_cols1.size(), m_cols1.c_ptr(), 
                    m_cols2.c_ptr(), m_removed_cols.c_ptr(), false, *res);
            }
            TRACE("dl_table_relation", tb1.display(tout); tb2.display(tout); res->display(tout); );
            return res;
        }
    };

    table_join_fn * sparse_table_plugin::mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        const table_signature & sig1 = t1.get_signature();
        const table_signature & sig2 = t2.get_signature();
        if (t1.get_kind()!=get_kind() || t2.get_kind()!=get_kind() 
            || join_involves_functional(sig1, sig2, col_cnt, cols1, cols2)) {
            //We also don't allow indexes on functional columns (and they are needed for joins)
            return 0;
        }
        return mk_join_project_fn(t1, t2, col_cnt, cols1, cols2, 0, static_cast<unsigned*>(0));
    }

    table_join_fn * sparse_table_plugin::mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols) {
        const table_signature & sig1 = t1.get_signature();
        const table_signature & sig2 = t2.get_signature();
        if (t1.get_kind()!=get_kind() || t2.get_kind()!=get_kind()
            || removed_col_cnt == t1.get_signature().size()+t2.get_signature().size()
            || join_involves_functional(sig1, sig2, col_cnt, cols1, cols2)) {
            //We don't allow sparse tables with zero signatures (and project on all columns leads to such)
            //We also don't allow indexes on functional columns.
            return 0;
        }
        return alloc(join_project_fn, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2,
            removed_col_cnt, removed_cols);
    }

    class sparse_table_plugin::union_fn : public table_union_fn {
    public:
        virtual void operator()(table_base & tgt0, const table_base & src0, table_base * delta0) {
            verbose_action  _va("union");
            sparse_table & tgt = get(tgt0);
            const sparse_table & src = get(src0);
            sparse_table * delta = get(delta0);

            unsigned fact_size = tgt.m_fact_size;
            const char* ptr = src.m_data.begin();
            const char* after_last=src.m_data.after_last();
            for (; ptr<after_last; ptr+=fact_size) {
                if (tgt.add_fact(ptr) && delta) {
                    delta->add_fact(ptr);
                }
            }
        }
    };

    table_union_fn * sparse_table_plugin::mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta) {
        if (tgt.get_kind()!=get_kind() || src.get_kind()!=get_kind() 
            || (delta && delta->get_kind()!=get_kind()) 
            || tgt.get_signature()!=src.get_signature() 
            || (delta && delta->get_signature()!=tgt.get_signature())) {
            return 0;
        }
        return alloc(union_fn);
    }

    class sparse_table_plugin::project_fn : public convenient_table_project_fn {
        const unsigned m_inp_col_cnt;
        const unsigned m_removed_col_cnt;
        const unsigned m_result_col_cnt;
    public:
        project_fn(const table_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_table_project_fn(orig_sig, removed_col_cnt, removed_cols), 
            m_inp_col_cnt(orig_sig.size()),
            m_removed_col_cnt(removed_col_cnt),
            m_result_col_cnt(orig_sig.size()-removed_col_cnt) {
                SASSERT(removed_col_cnt>0);
        }

        virtual void transform_row(const char * src, char * tgt, 
            const sparse_table::column_layout & src_layout, 
            const sparse_table::column_layout & tgt_layout) {
                unsigned r_idx=0;
                unsigned tgt_i=0;
                for (unsigned i=0; i<m_inp_col_cnt; i++) {
                    if (r_idx!=m_removed_col_cnt && i == m_removed_cols[r_idx]) {
                        SASSERT(r_idx<m_removed_col_cnt);
                        r_idx++;
                        continue;
                    }
                    tgt_layout.set(tgt, tgt_i, src_layout.get(src, i));
                    tgt_i++;
                }
                SASSERT(tgt_i == m_result_col_cnt);
                SASSERT(r_idx == m_removed_col_cnt);
        }

        virtual table_base * operator()(const table_base & tb) {
            verbose_action  _va("project");
            const sparse_table & t = get(tb);

            unsigned t_fact_size = t.m_fact_size;

            sparse_table_plugin & plugin = t.get_plugin();
            sparse_table * res = get(plugin.mk_empty(get_result_signature()));

            const sparse_table::column_layout & src_layout = t.m_column_layout;
            const sparse_table::column_layout & tgt_layout = res->m_column_layout;

            const char* t_ptr = t.m_data.begin();
            const char* t_end = t.m_data.after_last();
            for (; t_ptr!=t_end; t_ptr+=t_fact_size) {
                SASSERT(t_ptr<t_end);
                res->m_data.ensure_reserve();
                char * res_ptr = res->m_data.get_reserve_ptr();
                transform_row(t_ptr, res_ptr, src_layout, tgt_layout);
                res->m_data.insert_reserve_content();
            }
            return res;
        }
    };

    table_transformer_fn * sparse_table_plugin::mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols) {
        if (col_cnt == t.get_signature().size()) {
            return 0;
        }
        return alloc(project_fn, t.get_signature(), col_cnt, removed_cols);
    }


    class sparse_table_plugin::select_equal_and_project_fn : public convenient_table_transformer_fn {
        const unsigned m_col;
        sparse_table::key_value m_key;
    public:
        select_equal_and_project_fn(const table_signature & orig_sig, table_element val, unsigned col) 
                : m_col(col) {
            table_signature::from_project(orig_sig, 1, &col, get_result_signature());
            m_key.push_back(val);
        }

        virtual table_base * operator()(const table_base & tb) {
            verbose_action  _va("select_equal_and_project");
            const sparse_table & t = get(tb);

            sparse_table_plugin & plugin = t.get_plugin();
            sparse_table * res = get(plugin.mk_empty(get_result_signature()));

            const sparse_table::column_layout & t_layout = t.m_column_layout;
            const sparse_table::column_layout & res_layout = res->m_column_layout;
            unsigned t_cols = t_layout.size();

            sparse_table::key_indexer & indexer = t.get_key_indexer(1, &m_col);
            sparse_table::key_indexer::query_result t_offsets = indexer.get_matching_offsets(m_key);
            if (t_offsets.empty()) {
                //no matches
                return res;
            }
            sparse_table::key_indexer::offset_iterator ofs_it=t_offsets.begin();
            sparse_table::key_indexer::offset_iterator ofs_end=t_offsets.end();

            for (; ofs_it!=ofs_end; ++ofs_it) {
                sparse_table::store_offset t_ofs = *ofs_it;
                const char * t_ptr = t.get_at_offset(t_ofs);

                res->m_data.ensure_reserve();
                char * res_reserve = res->m_data.get_reserve_ptr();

                unsigned res_i = 0;
                for (unsigned i=0; i<t_cols; i++) {
                    if (i == m_col) {
                        continue;
                    }
                    res_layout.set(res_reserve, res_i++, t_layout.get(t_ptr, i));
                }
                res->add_reserve_content();
            }
            return res;
        }
    };

    table_transformer_fn * sparse_table_plugin::mk_select_equal_and_project_fn(const table_base & t, 
            const table_element & value, unsigned col) {
        if (t.get_kind()!=get_kind() || t.get_signature().size() == 1 || col>=t.get_signature().first_functional()) {
            //We don't allow sparse tables with zero signatures (and project on a single 
            //column table produces one).
            //We also don't allow indexes on functional columns. And our implementation of
            //select_equal_and_project uses index on \c col.
            return 0;
        }
        return alloc(select_equal_and_project_fn, t.get_signature(), value, col);
    }


    class sparse_table_plugin::rename_fn : public convenient_table_rename_fn {
        unsigned_vector m_out_of_cycle;
    public:
        rename_fn(const table_signature & orig_sig, unsigned permutation_cycle_len, const unsigned * permutation_cycle) 
            : convenient_table_rename_fn(orig_sig, permutation_cycle_len, permutation_cycle) {
                SASSERT(permutation_cycle_len>=2);
                idx_set cycle_cols;
                for (unsigned i=0; i < permutation_cycle_len; ++i) {
                    cycle_cols.insert(permutation_cycle[i]);
                }
                for (unsigned i=0; i < orig_sig.size(); ++i) {
                    if (!cycle_cols.contains(i)) {
                        m_out_of_cycle.push_back(i);
                    }
                }
        }

        void transform_row(const char * src, char * tgt,
            const sparse_table::column_layout & src_layout, 
            const sparse_table::column_layout & tgt_layout) {

                for (unsigned i=1; i < m_cycle.size(); ++i) {
                    tgt_layout.set(tgt, m_cycle[i-1], src_layout.get(src, m_cycle[i]));
                }
                tgt_layout.set(tgt, m_cycle[m_cycle.size()-1], src_layout.get(src, m_cycle[0]));

                unsigned_vector::const_iterator it = m_out_of_cycle.begin();
                unsigned_vector::const_iterator end = m_out_of_cycle.end();
                for (; it!=end; ++it) {
                    unsigned col = *it;
                    tgt_layout.set(tgt, col, src_layout.get(src, col));
                }
        }

        virtual table_base * operator()(const table_base & tb) {
            verbose_action  _va("rename");

            const sparse_table & t = get(tb);

            unsigned t_fact_size = t.m_fact_size;

            sparse_table_plugin & plugin = t.get_plugin();
            sparse_table * res = get(plugin.mk_empty(get_result_signature()));

            size_t res_fact_size = res->m_fact_size;
            size_t res_data_size = res_fact_size*t.row_count();
            if (res_fact_size != 0 && (res_data_size / res_fact_size) != t.row_count()) {
                throw default_exception("multiplication overflow");
            }

            res->m_data.resize_data(res_data_size);

            //here we can separate data creating and insertion into hashmap, since we know
            //that no row will become duplicate

            //create the data
            const char* t_ptr = t.m_data.begin();
            char* res_ptr = res->m_data.begin();
            char* res_end = res_ptr+res_data_size;
            for (; res_ptr!=res_end; t_ptr+=t_fact_size, res_ptr+=res_fact_size) {
                transform_row(t_ptr, res_ptr, t.m_column_layout, res->m_column_layout);
            }

            //and insert them into the hash-map
            for (size_t i = 0; i != res_data_size; i += res_fact_size) {
                TRUSTME(res->m_data.insert_offset(i));
            }

            return res;
        }
    };

    table_transformer_fn * sparse_table_plugin::mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) {
        if (t.get_kind()!=get_kind()) {
            return 0;
        }
        return alloc(rename_fn, t.get_signature(), permutation_cycle_len, permutation_cycle);
    }

    class sparse_table_plugin::negation_filter_fn : public convenient_table_negation_filter_fn {
        typedef sparse_table::store_offset store_offset;
        typedef sparse_table::key_value key_value;
        typedef sparse_table::key_indexer key_indexer;

        bool m_joining_neg_non_functional;

        /**
           Used by \c collect_intersection_offsets function.
           If tgt_is_first is false, contains the same items as \c res.
        */
        idx_set m_intersection_content;
        

    public:
        negation_filter_fn(const table_base & tgt, const table_base & neg, 
                    unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) 
                : convenient_table_negation_filter_fn(tgt, neg, joined_col_cnt, t_cols, negated_cols) {
            unsigned neg_first_func = neg.get_signature().first_functional();
            counter ctr;
            ctr.count(m_cols2);
            m_joining_neg_non_functional = ctr.get_max_counter_value() == 1
                && ctr.get_positive_count() == neg_first_func 
                && (neg_first_func == 0 || ctr.get_max_positive() == neg_first_func-1);
        }

        /**
           Collect offsets of rows in \c t1 or \c t2 (depends on whether \c tgt_is_first is true or false) 
           that have a match in the other table into \c res. Offsets in \c res are in ascending order.
        */
        void collect_intersection_offsets(const sparse_table & t1, const sparse_table & t2,
                bool tgt_is_first, svector<store_offset> & res) {
            SASSERT(res.empty());

            m_intersection_content.reset();

            unsigned joined_col_cnt = m_cols1.size();
            unsigned t1_entry_size = t1.m_data.entry_size();

            const unsigned * cols1 = tgt_is_first ? m_cols1.c_ptr() : m_cols2.c_ptr();
            const unsigned * cols2 = tgt_is_first ? m_cols2.c_ptr() : m_cols1.c_ptr();

            key_value t1_key;
            t1_key.resize(joined_col_cnt);
            key_indexer & t2_indexer = t2.get_key_indexer(joined_col_cnt, cols2);

            bool key_modified=true;
            key_indexer::query_result t2_offsets;
            store_offset t1_after_last = t1.m_data.after_last_offset();
            for (store_offset t1_ofs=0; t1_ofs<t1_after_last; t1_ofs+=t1_entry_size) {
            
                for (unsigned i=0; i<joined_col_cnt; i++) {
                    table_element val = t1.get_cell(t1_ofs, cols1[i]);
                    if (t1_key[i]!=val) {
                        t1_key[i]=val;
                        key_modified=true;
                    }
                }
                if (key_modified) {
                    t2_offsets = t2_indexer.get_matching_offsets(t1_key);
                    key_modified = false;
                }

                if (t2_offsets.empty()) {
                    continue;
                }
                if (tgt_is_first) {
                    res.push_back(t1_ofs);
                }
                else {
                    key_indexer::offset_iterator it  = t2_offsets.begin();
                    key_indexer::offset_iterator end = t2_offsets.end();
                    for (; it!=end; ++it) {
                        store_offset ofs = *it;
                        unsigned offs2 = static_cast<unsigned>(ofs);
                        if (ofs != offs2) {
                            throw default_exception("Z3 cannot perform negation with excessively large tables");
                        }
                        if (!m_intersection_content.contains(offs2)) {
                            m_intersection_content.insert(offs2);
                            res.push_back(ofs);
                        }
                    }
                }
            }

            if (!tgt_is_first) {
                //in this case \c res now may be in arbitrary order
                std::sort(res.begin(), res.end());
            }
        }

        virtual void operator()(table_base & tgt0, const table_base & neg0) {
            sparse_table & tgt = get(tgt0);
            const sparse_table & neg = get(neg0);
           
            verbose_action  _va("filter_by_negation");

            if (m_cols1.size() == 0) {
                if (!neg.empty()) {
                    tgt.reset();
                }
                return;
            }

            svector<store_offset> to_remove; //offsets here are in increasing order

            //We don't do just the simple tgt.row_count()>neg.row_count() because the swapped case is 
            //more expensive. The constant 4 is, however, just my guess what the ratio might be.
            if (tgt.row_count()/4>neg.row_count()) {
                collect_intersection_offsets(neg, tgt, false, to_remove);
            }
            else {
                collect_intersection_offsets(tgt, neg, true, to_remove);
            }


            //the largest offsets are at the end, so we can remove them one by one
            while (!to_remove.empty()) {
                store_offset removed_ofs = to_remove.back();
                to_remove.pop_back();
                tgt.m_data.remove_offset(removed_ofs);
            }
            tgt.reset_indexes();
        }

    };

    table_intersection_filter_fn * sparse_table_plugin::mk_filter_by_negation_fn(const table_base & t, 
            const table_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) { 
        if (!check_kind(t) || !check_kind(negated_obj)
            || join_involves_functional(t.get_signature(), negated_obj.get_signature(), joined_col_cnt, 
                t_cols, negated_cols) ) {
            return 0;
        }
        return alloc(negation_filter_fn, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
    }

    /**
           T \ (S1 Join S2)

           t_cols    - columns from T
           s_cols    - columns from (S1 Join S2) that are equated
           src1_cols - columns from S1 equated with columns from S2
           src2_cols - columns from S2 equated with columns from S1

           t1_cols    - columns from T that map into S1
           s1_cols    - matching columns from s_cols for t1_cols
           t2s1_cols  - columns from T that map into S2, and columns from src1 that join src2
           s2_cols    - matching columns from t2s1_cols

           columns from s2 that are equal to a column from s1 that is in s_cols:

           - ...
           
    */

    class sparse_table_plugin::negated_join_fn : public table_intersection_join_filter_fn {
        typedef sparse_table::store_offset store_offset;
        typedef sparse_table::key_value key_value;
        typedef sparse_table::key_indexer key_indexer;
        unsigned_vector m_t1_cols;
        unsigned_vector m_s1_cols;
        unsigned_vector m_t2_cols;
        unsigned_vector m_s2_cols;
        unsigned_vector m_src1_cols;
    public:
        negated_join_fn(        
            table_base const& src1,
            unsigned_vector const& t_cols,
            unsigned_vector const& src_cols,
            unsigned_vector const& src1_cols,
            unsigned_vector const& src2_cols):
            m_src1_cols(src1_cols) {

            // split t_cols and src_cols according to src1, and src2

            unsigned src1_size = src1.get_signature().size();
            for (unsigned i = 0; i < t_cols.size(); ++i) {
                if (src_cols[i] < src1_size) {
                    m_t1_cols.push_back(t_cols[i]);
                    m_s1_cols.push_back(src_cols[i]);
                }
                else {
                    m_t2_cols.push_back(t_cols[i]);
                    m_s2_cols.push_back(src_cols[i]);                    
                }
            }
            m_s2_cols.append(src2_cols);
        }

        virtual void operator()(table_base & _t, const table_base & _s1, const table_base& _s2) {

            verbose_action  _va("negated_join");
            sparse_table& t = get(_t);
            svector<store_offset> to_remove;
            collect_to_remove(t, get(_s1), get(_s2), to_remove);
            for (unsigned i = 0; i < to_remove.size(); ++i) {
                t.m_data.remove_offset(to_remove[i]);
            }
            t.reset_indexes();
        }

    private:
        void collect_to_remove(sparse_table& t, sparse_table const& s1, sparse_table const& s2, svector<store_offset>& to_remove) {
            key_value s1_key, s2_key;
            SASSERT(&s1 != &s2);
            SASSERT(m_s1_cols.size() == m_t1_cols.size());
            SASSERT(m_s2_cols.size() == m_t2_cols.size() + m_src1_cols.size());
            s1_key.resize(m_s1_cols.size());
            s2_key.resize(m_s2_cols.size());
            key_indexer & s1_indexer = s1.get_key_indexer(m_s1_cols.size(), m_s1_cols.c_ptr());
            key_indexer & s2_indexer = s2.get_key_indexer(m_s2_cols.size(), m_s2_cols.c_ptr());

            store_offset t_after_last = t.m_data.after_last_offset();
            key_indexer::query_result s1_offsets, s2_offsets;
            unsigned t_entry_size = t.m_data.entry_size();
            for (store_offset t_ofs = 0; t_ofs < t_after_last; t_ofs += t_entry_size) {

                if (update_key(s1_key, 0, t, t_ofs, m_t1_cols)) {
                    s1_offsets = s1_indexer.get_matching_offsets(s1_key);
                }
                key_indexer::offset_iterator it  = s1_offsets.begin();
                key_indexer::offset_iterator end = s1_offsets.end();
                for (; it != end; ++it) {
                    store_offset s1_ofs = *it;
                    bool upd1 = update_key(s2_key, 0, t, t_ofs, m_t2_cols);
                    bool upd2 = update_key(s2_key, m_t2_cols.size(), s1, s1_ofs, m_src1_cols);
                    if (upd1 || upd2) {
                        s2_offsets = s2_indexer.get_matching_offsets(s2_key);
                    }
                    if (!s2_offsets.empty()) {
                        to_remove.push_back(t_ofs);
                        break;
                    }
                }                
            }                       
        }

        inline bool update_key(key_value& key, unsigned key_offset, sparse_table const& t, store_offset ofs, unsigned_vector const& cols) {
            bool modified = false;
            unsigned sz = cols.size();
            for (unsigned i = 0; i < sz; ++i) {
                table_element val = t.get_cell(ofs, cols[i]);
                modified = update_key(key[i+key_offset], val) || modified;
            }
            return modified;
        }

        inline bool update_key(table_element& tgt, table_element src) {
            if (tgt == src) {
                return false;
            }
            else {
                tgt = src;
                return true;
            }
        }
        
    };

    table_intersection_join_filter_fn* sparse_table_plugin::mk_filter_by_negated_join_fn(
        const table_base & t, 


        const table_base & src1, 
        const table_base & src2, 
        unsigned_vector const& t_cols,
        unsigned_vector const& src_cols,
        unsigned_vector const& src1_cols,
        unsigned_vector const& src2_cols) {
        if (check_kind(t) && check_kind(src1) && check_kind(src2)) {            
            return alloc(negated_join_fn, src1, t_cols, src_cols, src1_cols, src2_cols);
        }
        else {
            return 0;
        }
    }


    unsigned sparse_table::get_size_estimate_bytes() const {
        unsigned sz = 0;
        sz += m_data.get_size_estimate_bytes();
        sz += m_key_indexes.capacity()*8; // TBD
        return sz;
    }


};

