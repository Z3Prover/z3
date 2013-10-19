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

#include"dl_context.h"
#include"dl_util.h"
#include"dl_table.h"
#include"dl_relation_manager.h"

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

        virtual table_base * operator()(const table_base & t1, const table_base & t2) {

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
            return 0;
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

            virtual void get_fact(table_fact & result) const {
                result = *m_parent.m_inner;
            }
            virtual table_element operator[](unsigned col) const {
                return (*m_parent.m_inner)[col];
            }

        };

        our_row m_row_obj;

    public:
        our_iterator_core(const hashtable_table & t, bool finished) : 
            m_parent(t), m_inner(finished ? t.m_data.end() : t.m_data.begin()), 
            m_end(t.m_data.end()), m_row_obj(*this) {}

        virtual bool is_finished() const {
            return m_inner==m_end;
        }

        virtual row_interface & operator*() {
            SASSERT(!is_finished());
            return m_row_obj;
        }
        virtual void operator++() {
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
            virtual void get_fact(table_fact& result) const {
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

        virtual bool is_finished() const {
            return m_offset == m_bv.m_bv.size();
        }

        virtual row_interface & operator*() {
            SASSERT(!is_finished());
            return m_row_obj;
        }
        virtual void operator++() {
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




    // -----------------------------------
    //
    // equivalence_table
    //
    // -----------------------------------

    bool equivalence_table_plugin::can_handle_signature(const table_signature & sig) {
        return sig.functional_columns() == 0 && sig.size() == 2 && sig[0] < UINT_MAX && sig[0] == sig[1];
    }

    bool equivalence_table_plugin::is_equivalence_table(table_base const& tbl) const {
        if (tbl.get_kind() != get_kind()) return false;
        equivalence_table const& t = static_cast<equivalence_table const&>(tbl);
        return !t.is_sparse();
    }

    table_base * equivalence_table_plugin::mk_empty(const table_signature & s) {
        TRACE("dl", for (unsigned i = 0; i < s.size(); ++i) tout << s[i] << " "; tout << "\n";);
        SASSERT(can_handle_signature(s));
        return alloc(equivalence_table, *this, s);
    }

    class equivalence_table_plugin::select_equal_and_project_fn : public table_transformer_fn {
        unsigned      m_val;
        table_sort    m_sort;
    public:
        select_equal_and_project_fn(const table_signature & sig, table_element val, unsigned col) 
            : m_val(static_cast<unsigned>(val)),
              m_sort(sig[0]) {
            SASSERT(val <= UINT_MAX);
            SASSERT(col == 0 || col == 1);
            SASSERT(sig.functional_columns() == 0);
            SASSERT(sig.size() == 2);
            SASSERT(sig[0] < UINT_MAX && sig[0] == sig[1]);
        }

        virtual table_base* operator()(const table_base& tb) {
            TRACE("dl", tout << "\n";);
            table_plugin & plugin = tb.get_plugin();
            table_plugin* rp = plugin.get_manager().get_table_plugin(symbol("sparse"));
            SASSERT(rp);
            table_signature sig;
            sig.push_back(m_sort);
            table_base* result = rp->mk_empty(sig);
            equivalence_table const& eq_table = static_cast<equivalence_table const&>(tb);
            if (eq_table.is_valid(m_val)) {
                table_fact fact;
                fact.resize(1);
                unsigned r = m_val;
                do {
                    fact[0] = r;
                    result->add_fact(fact);
                    r = eq_table.m_uf.next(r);
                }
                while (r != m_val);
            }
            TRACE("dl", tb.display(tout << "src:\n"); result->display(tout << "result\n"););
            return result;
        }
    };

    table_transformer_fn * equivalence_table_plugin::mk_select_equal_and_project_fn(
        const table_base & t, const table_element & value, unsigned col) { 
        return alloc(select_equal_and_project_fn, t.get_signature(), value, col);
    }

    class equivalence_table_plugin::union_fn : public table_union_fn {    

        equivalence_table_plugin& m_plugin;

        
        void mk_union1(equivalence_table & tgt, const equivalence_table & src, table_base * delta) {
            unsigned num_vars = src.m_uf.get_num_vars();
            table_fact fact;
            fact.resize(2);
            for (unsigned i = 0; i < num_vars; ++i) {
                if (src.is_valid(i) && src.m_uf.find(i) == i) {
                    fact[0] = i;
                    equivalence_table::class_iterator it = src.class_begin(i);
                    equivalence_table::class_iterator end = src.class_end(i);
                    for (; it != end; ++it) {
                        fact[1] = *it;
                        if (!tgt.contains_fact(fact)) {
                            tgt.add_fact(fact);
                            if (delta) {
                                delta->add_fact(fact);
                            }
                        }
                    }
                }
            }
        }

        void mk_union2(equivalence_table & tgt, const table_base & src, table_base * delta) {
            table_fact fact;
            table_base::iterator it = src.begin(), end = src.end();
            for (; it != end; ++it) {
                it->get_fact(fact);
                if (!tgt.contains_fact(fact)) {
                    tgt.add_fact(fact);
                    if (delta) {
                        delta->add_fact(fact);
                        TRACE("dl", 
                              tout << "Add: "; 
                              for (unsigned i = 0; i < fact.size(); ++i) tout << fact[i] << " "; 
                              tout << "\n";);
                    }
                }
            }
        }

    public:
        union_fn(equivalence_table_plugin& p) : m_plugin(p) {}

        virtual void operator()(table_base & tgt0, const table_base & src, table_base * delta) {
            TRACE("dl", tout << "union\n";);
            equivalence_table & tgt = static_cast<equivalence_table &>(tgt0);   
            if (m_plugin.is_equivalence_table(src)) {
                mk_union1(tgt, static_cast<equivalence_table const&>(src), delta);
            }
            else {
                mk_union2(tgt, src, delta);
            }
            TRACE("dl", src.display(tout << "src\n"); tgt.display(tout << "tgt\n"); 
                        if (delta) delta->display(tout << "delta\n"););
        }
    };
    
    table_union_fn * equivalence_table_plugin::mk_union_fn(
        const table_base & tgt, const table_base & src, const table_base * delta) {
        if (!is_equivalence_table(tgt) ||
            tgt.get_signature() != src.get_signature() ||
            (delta && delta->get_signature() != tgt.get_signature())) {
            return 0;
        }
        return alloc(union_fn,*this);
    }
    
    class equivalence_table_plugin::join_project_fn : public convenient_table_join_project_fn {
        equivalence_table_plugin& m_plugin;
    public:
        join_project_fn(
            equivalence_table_plugin& plugin, const table_signature & t1_sig, const table_signature & t2_sig, unsigned col_cnt, 
            const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols) 
            : convenient_table_join_project_fn(t1_sig, t2_sig, col_cnt, cols1, cols2, removed_col_cnt, removed_cols),
              m_plugin(plugin) {
            m_removed_cols.push_back(UINT_MAX);
        }

        virtual table_base * operator()(const table_base & tb1, const table_base & tb2) {            
            SASSERT(m_cols1.size() == 1);
            const table_signature & res_sign = get_result_signature();
            table_plugin * plugin = &tb1.get_plugin();
            if (!plugin->can_handle_signature(res_sign)) {
                plugin = &tb2.get_plugin();
                if (!plugin->can_handle_signature(res_sign)) {
                    plugin = &tb1.get_manager().get_appropriate_plugin(res_sign);
                }
            }
            SASSERT(plugin->can_handle_signature(res_sign));
            table_base * result = plugin->mk_empty(res_sign);
            
            if (m_plugin.is_equivalence_table(tb1)) {
                mk_join(0, m_cols1[0], static_cast<const equivalence_table&>(tb1), 
                        2, m_cols2[0], tb2, result);
            }
            else if (m_plugin.is_equivalence_table(tb2)) {
                mk_join(tb1.get_signature().size(), m_cols2[0], static_cast<const equivalence_table&>(tb2), 
                        0, m_cols1[0], tb1, result);
            }
            else {
                UNREACHABLE();
            }
            TRACE("dl", tb1.display(tout << "tb1\n"); tb2.display(tout << "tb2\n"); result->display(tout << "result\n"););
            return result;
        }

    private:
        table_base * mk_join(unsigned offs1, unsigned col1, equivalence_table const & t1, 
                             unsigned offs2, unsigned col2, table_base const& t2, table_base* res) {
            table_base::iterator els2it  = t2.begin();
            table_base::iterator els2end = t2.end();

            table_fact acc, proj;
            acc.resize(t1.get_signature().size() + t2.get_signature().size()); 

            for(; els2it != els2end; ++els2it) {
                const table_base::row_interface & row2 = *els2it;
                table_element const& e2 = row2[col2];
                equivalence_table::class_iterator it  = t1.class_begin(e2);
                equivalence_table::class_iterator end = t1.class_end(e2);
                if (it != end) {
                    for (unsigned i = 0; i < row2.size(); ++i) {
                        acc[i+offs2] = row2[i];
                    }
                }
                for (; it != end; ++it) {
                    acc[offs1+col1] = e2;
                    acc[offs1+1-col1] = *it;   
                    mk_project(acc, proj);
                    TRACE("dl", for (unsigned i = 0; i < proj.size(); ++i) tout << proj[i] << " "; tout << "\n";);
                    res->add_fact(proj);
                }
            }
            return res;
        }

        virtual void mk_project(table_fact const & f, table_fact & p) const {
            unsigned sz = f.size();
            p.reset();
            for (unsigned i = 0, r = 0; i < sz; ++i) {
                if (r < m_removed_cols.size() && m_removed_cols[r] == i) {
                    ++r;
                }
                else {
                    p.push_back(f[i]);
                }
            }            
        }


    };

    table_join_fn * equivalence_table_plugin::mk_join_project_fn(
        const table_base & t1, const table_base & t2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
        const unsigned * removed_cols) {
        if (col_cnt != 1) {
            TRACE("dl", tout << "WARNING: join_project on multiple columns is not implemented\n";);
            return 0;
        }
        if (is_equivalence_table(t1) || is_equivalence_table(t2)) {
            return alloc(join_project_fn, *this, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2,
                         removed_col_cnt, removed_cols);
        }
        return 0;
    }

    class equivalence_table::eq_iterator : public iterator_core {
        
        equivalence_table const& m_eq;
        unsigned                 m_last;
        unsigned                 m_current;
        unsigned                 m_next;

        class our_row : public caching_row_interface {
            const eq_iterator& m_parent;
        public:
            our_row(const eq_iterator & p) : caching_row_interface(p.m_eq), m_parent(p) {}

            virtual void get_fact(table_fact& result) const {
                if (result.size() < size()) {
                    result.resize(size(), 0);
                }
                result[0] = m_parent.m_current;
                result[1] = m_parent.m_next;
            }

            virtual table_element operator[](unsigned col) const {
                if (col == 0) return m_parent.m_current;
                if (col == 1) return m_parent.m_next;
                UNREACHABLE();
                return 0;
            }

        };
        our_row m_row_obj;

    public:
        eq_iterator(const equivalence_table& eq, bool end):
            m_eq(eq), 
            m_last(eq.m_uf.get_num_vars()),
            m_current(end?m_last:0),
            m_next(0),
            m_row_obj(*this)
        { 
            while (m_current < m_last && !m_eq.is_valid(m_current)) {
                m_current++;
                m_next = m_current;
            }
        }

        virtual bool is_finished() const {
            return m_current == m_last;
        }

        virtual row_interface & operator*() {
            SASSERT(!is_finished());
            return m_row_obj;
        }

        virtual void operator++() {
            SASSERT(!is_finished());            
            m_next = m_eq.m_uf.next(m_next);
            if (m_next == m_current) {
                do {
                    m_current++;
                    m_next = m_current;
                }
                while (m_current < m_last && !m_eq.is_valid(m_current));
            }
        }        
    };

    equivalence_table::equivalence_table(equivalence_table_plugin & plugin, const table_signature & sig)
        : table_base(plugin, sig), m_uf(m_ctx), m_sparse(0) {
        SASSERT(plugin.can_handle_signature(sig));        
        }

    equivalence_table::~equivalence_table() { 
        if (is_sparse()) {
            m_sparse->deallocate();
        }
    }

           
    void equivalence_table::add_fact(const table_fact & f) {
        if (is_sparse()) {
            add_fact_sparse(f);
        }
        else {
            TRACE("dl_verbose", for (unsigned i = 0; i < f.size(); ++i) tout << f[i] << " "; tout << "\n";);
            while (first(f) >= m_uf.get_num_vars()) m_uf.mk_var();
            while (second(f) >= m_uf.get_num_vars()) m_uf.mk_var();     
            m_uf.merge(first(f), second(f));
            m_valid.reserve(m_uf.get_num_vars());
            m_valid.set(first(f));
            m_valid.set(second(f));
        }
    }

    void equivalence_table::remove_fact(const table_element* fact) {
        mk_sparse();
        m_sparse->remove_fact(fact);
    }

    void equivalence_table::mk_sparse() {
        if (m_sparse) return;

        TRACE("dl",tout << "\n";);
        table_plugin & plugin = get_plugin();
        table_plugin* rp = plugin.get_manager().get_table_plugin(symbol("sparse"));
        SASSERT(rp);
        table_base* result = rp->mk_empty(get_signature());
        table_base::iterator it = begin(), e = end();
        table_fact fact;
        for (; it != e; ++it) {            
            it->get_fact(fact);
            result->add_fact(fact);
        }
        m_sparse = result;
    }

    void equivalence_table::add_fact_sparse(table_fact const& f) {
        table_base::iterator it = m_sparse->begin(), end = m_sparse->end();
        vector<table_fact> to_add;
        to_add.push_back(f);
        table_fact f1(f);

        f1[0] = f[1];
        f1[1] = f[0];
        to_add.push_back(f1);

        f1[0] = f[1];
        f1[1] = f[1];
        to_add.push_back(f1);

        f1[0] = f[0];
        f1[1] = f[0];
        to_add.push_back(f1);

        for (; it != end; ++it) {
            if ((*it)[0] == f[0]) {
                f1[0] = f[1];
                f1[1] = (*it)[1];
                to_add.push_back(f1);
                std::swap(f1[0],f1[1]);
                to_add.push_back(f1);
            }
        }
        for (unsigned i = 0; i < to_add.size(); ++i) {
            m_sparse->add_fact(to_add[i]);
        }
    }

    bool equivalence_table::contains_fact(const table_fact & f) const {
        TRACE("dl_verbose", for (unsigned i = 0; i < f.size(); ++i) tout << f[i] << " "; tout << "\n";);
        if (is_sparse()) {
            return m_sparse->contains_fact(f);
        }
        return  
            is_valid(first(f)) &&
            is_valid(second(f)) &&
            m_uf.find(first(f)) == m_uf.find(second(f));
    }

    table_base* equivalence_table::clone() const {
        if (is_sparse()) {
            return m_sparse->clone();
        }
        TRACE("dl",tout << "\n";);
        table_plugin & plugin = get_plugin();
        table_base* result = plugin.mk_empty(get_signature());
        table_fact fact;
        fact.resize(2);
        for (unsigned i = 0; i < m_uf.get_num_vars(); ++i) {
            if (m_valid.get(i) && m_uf.find(i) == i) {
                unsigned n = m_uf.next(i);
                fact[0] = i;
                while (n != i) {
                    fact[1] = n;
                    result->add_fact(fact);
                    n = m_uf.next(n);
                }
            }
        }
        return result;
    }

    table_base::iterator equivalence_table::begin() const {
        if (is_sparse()) return m_sparse->begin();
        return mk_iterator(alloc(eq_iterator, *this, false));
    }

    table_base::iterator equivalence_table::end() const {
        if (is_sparse()) return m_sparse->end();
        return mk_iterator(alloc(eq_iterator, *this, true));
    }

    equivalence_table::class_iterator equivalence_table::class_begin(table_element const& _e) const {
        SASSERT(!is_sparse());
        unsigned e = static_cast<unsigned>(_e);
        return class_iterator(*this, e, !is_valid(e));
    }

    equivalence_table::class_iterator equivalence_table::class_end(table_element const& _e) const {
        SASSERT(!is_sparse());
        unsigned e = static_cast<unsigned>(_e);
        return class_iterator(*this, e, true);
    }

    void equivalence_table::display(std::ostream& out) const {
        if (is_sparse()) {
            m_sparse->display(out);
            return;
        }
        for (unsigned i = 0; i < m_uf.get_num_vars(); ++i) {
            if (is_valid(i) && m_uf.find(i) == i) {
                unsigned j = i, last = i;                
                do {
                    out << "<" << i << " " << j << ">\n";
                    j = m_uf.next(j);
                }
                while (last != j);
            }
        }
    }

    unsigned equivalence_table::get_size_estimate_rows() const {
        if (is_sparse()) return m_sparse->get_size_estimate_rows();
        return static_cast<unsigned>(get_signature()[0]); 
    }

    unsigned equivalence_table::get_size_estimate_bytes() const {
        if (is_sparse()) return m_sparse->get_size_estimate_bytes();
        return static_cast<unsigned>(get_signature()[0]); 
    }

    bool equivalence_table::knows_exact_size() const { 
        return (!is_sparse() || m_sparse->knows_exact_size());
    }

};

