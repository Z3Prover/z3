/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-01.

Revision History:

--*/

#include "muz/base/dl_context.h"
#include "muz/base/dl_util.h"
#include "muz/rel/dl_table.h"
#include "muz/rel/dl_relation_manager.h"

namespace datalog {

    // -----------------------------------
    //
    // hashtable_table
    //
    // -----------------------------------

    table_base * hashtable_table_plugin::mk_empty(const table_signature & s) {
        SASSERT(can_handle_signature(s));
        return alloc(hashtable_table, *this, s);
    }


    class hashtable_table_plugin::join_fn : public convenient_table_join_fn {
        unsigned m_joined_col_cnt;
    public:
        join_fn(const table_signature & t1_sig, const table_signature & t2_sig, unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) 
            : convenient_table_join_fn(t1_sig, t2_sig, col_cnt, cols1, cols2),
            m_joined_col_cnt(col_cnt) {}

        table_base * operator()(const table_base & t1, const table_base & t2) override {

            const hashtable_table & ht1 = static_cast<const hashtable_table &>(t1);
            const hashtable_table & ht2 = static_cast<const hashtable_table &>(t2);

            hashtable_table_plugin & plugin = ht1.get_plugin();

            hashtable_table * res = static_cast<hashtable_table *>(plugin.mk_empty(get_result_signature()));

            hashtable_table::storage::iterator els1it = ht1.m_data.begin();
            hashtable_table::storage::iterator els1end = ht1.m_data.end();
            hashtable_table::storage::iterator els2end = ht2.m_data.end();

            table_fact acc;

            for(; els1it!=els1end; ++els1it) {
                const table_fact & row1 = *els1it;

                hashtable_table::storage::iterator els2it = ht2.m_data.begin();
                for(; els2it!=els2end; ++els2it) {
                    const table_fact & row2 = *els2it;

                    bool match=true;
                    for(unsigned i=0; i<m_joined_col_cnt; i++) {
                        if(row1[m_cols1[i]]!=row2[m_cols2[i]]) {
                            match=false;
                            break;
                        }
                    }
                    if(!match) {
                        continue;
                    }

                    acc.reset();
                    acc.append(row1);
                    acc.append(row2);
                    res->m_data.insert(acc);
                }
            }
            return res;
        }
    };

    table_join_fn * hashtable_table_plugin::mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if(t1.get_kind()!=get_kind() || t2.get_kind()!=get_kind()) {
            return nullptr;
        }
        return alloc(join_fn, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2);
    }


    class hashtable_table::our_iterator_core : public iterator_core {
        const hashtable_table & m_parent;
        storage::iterator m_inner;
        storage::iterator m_end;

        class our_row : public row_interface {
            const our_iterator_core & m_parent;
        public:
            our_row(const our_iterator_core & parent) : row_interface(parent.m_parent), m_parent(parent) {}

            void get_fact(table_fact & result) const override {
                result = *m_parent.m_inner;
            }
            table_element operator[](unsigned col) const override {
                return (*m_parent.m_inner)[col];
            }

        };

        our_row m_row_obj;

    public:
        our_iterator_core(const hashtable_table & t, bool finished) : 
            m_parent(t), m_inner(finished ? t.m_data.end() : t.m_data.begin()), 
            m_end(t.m_data.end()), m_row_obj(*this) {}

        bool is_finished() const override {
            return m_inner==m_end;
        }

        row_interface & operator*() override {
            SASSERT(!is_finished());
            return m_row_obj;
        }
        void operator++() override {
            SASSERT(!is_finished());
            ++m_inner;
        }
    };



    table_base::iterator hashtable_table::begin() const {
        return mk_iterator(alloc(our_iterator_core, *this, false));
    }

    table_base::iterator hashtable_table::end() const {
        return mk_iterator(alloc(our_iterator_core, *this, true));
    }

    // -----------------------------------
    //
    // bitvector_table
    //
    // -----------------------------------

    bool bitvector_table_plugin::can_handle_signature(const table_signature & sig) {
        if(sig.functional_columns()!=0) {
            return false;
        }
        unsigned cols = sig.size();
        unsigned shift = 0;
        for (unsigned i = 0; i < cols; ++i) {            
            unsigned s = static_cast<unsigned>(sig[i]);
            if (s != sig[i] || !is_power_of_two(s)) {
                return false;
            }
            unsigned num_bits = 0;
            unsigned bit_pos = 1;
            for (num_bits = 1; num_bits < 32; ++num_bits) {
                if (bit_pos & s) {
                    break;
                }
                bit_pos <<= 1;                
            }
            shift += num_bits;
            if (shift >= 32) {
                return false;
            }
        }
        return true;
    }

    table_base * bitvector_table_plugin::mk_empty(const table_signature & s) {
        SASSERT(can_handle_signature(s));
        return alloc(bitvector_table, *this, s);
    }

    class bitvector_table::bv_iterator : public iterator_core {
        
        bitvector_table const& m_bv;
        unsigned         m_offset;

        class our_row : public caching_row_interface {
            const bv_iterator& m_parent;
        public:
            our_row(const bv_iterator & p) : caching_row_interface(p.m_bv), m_parent(p) {}
            void get_fact(table_fact& result) const override {
                if (result.size() < size()) {
                    result.resize(size(), 0);
                }
                m_parent.m_bv.offset2fact(m_parent.m_offset, result);
            }
        };
        our_row m_row_obj;

    public:
        bv_iterator(const bitvector_table& bv, bool end):
            m_bv(bv), m_offset(end?m_bv.m_bv.size():0), m_row_obj(*this)
        {
            if (!is_finished() && !m_bv.m_bv.get(m_offset)) {
                ++(*this);
            }
        }

        bool is_finished() const override {
            return m_offset == m_bv.m_bv.size();
        }

        row_interface & operator*() override {
            SASSERT(!is_finished());
            return m_row_obj;
        }
        void operator++() override {
            SASSERT(!is_finished());
            ++m_offset;
            while (!is_finished() && !m_bv.m_bv.get(m_offset)) {
                ++m_offset;
            }
            m_row_obj.reset();
        }        
    };

    bitvector_table::bitvector_table(bitvector_table_plugin & plugin, const table_signature & sig)
        : table_base(plugin, sig) {
        SASSERT(plugin.can_handle_signature(sig));

        m_num_cols = sig.size();
        unsigned shift = 0;
        for (unsigned i = 0; i < m_num_cols; ++i) {            
            unsigned s = static_cast<unsigned>(sig[i]);
            if (s != sig[i] || !is_power_of_two(s)) {
                  throw default_exception("bit-vector table is specialized to small domains that are powers of two");
            }
            m_shift.push_back(shift);
            m_mask.push_back(s - 1);
            unsigned num_bits = 0;
            unsigned bit_pos = 1;
            for (num_bits = 1; num_bits < 32; ++num_bits) {
                if (bit_pos & s) {
                    break;
                }
                bit_pos <<= 1;                
            }
            shift += num_bits;
            if (shift >= 32) {
                  throw default_exception("bit-vector table is specialized to small domains that are powers of two");
            }
            m_bv.reserve(1 << shift);
        }
    }
    
    unsigned bitvector_table::fact2offset(const table_element* f) const {
        unsigned result = 0;
        for (unsigned i = 0; i < m_num_cols; ++i) {
            SASSERT(f[i]<get_signature()[i]);
            result +=  ((unsigned)f[i]) << m_shift[i];
        }
        return result;
    }

    void bitvector_table::offset2fact(unsigned offset, table_fact& f) const {
        SASSERT(m_num_cols == f.size());
        for (unsigned i = 0; i < m_num_cols; ++i) {
            f[i] = m_mask[i] & (offset >> m_shift[i]);
        }
    }
    
    void bitvector_table::add_fact(const table_fact & f) {
        m_bv.set(fact2offset(f.c_ptr()));
    }

    void bitvector_table::remove_fact(const table_element* fact) {
        m_bv.unset(fact2offset(fact));
    }

    bool bitvector_table::contains_fact(const table_fact & f) const {
        return m_bv.get(fact2offset(f.c_ptr()));
    }

    table_base::iterator bitvector_table::begin() const {
        return mk_iterator(alloc(bv_iterator, *this, false));
    }

    table_base::iterator bitvector_table::end() const {
        return mk_iterator(alloc(bv_iterator, *this, true));
    }
};

