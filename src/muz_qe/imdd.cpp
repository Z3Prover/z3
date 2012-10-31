/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    imdd.cpp

Abstract:

    Interval based Multiple-valued Decision Diagrams.

Author:

    Leonardo de Moura (leonardo) 2010-10-13.

Revision History:

--*/

#include"imdd.h"
#include"map.h"

#define DEFAULT_SIMPLE_MAX_ENTRIES 32

inline bool is_cached(imdd2imdd_cache & cache, imdd * d, imdd * & r) {
    if (d->is_shared()) {
        if (cache.find(d, r) && (r == 0 || !r->is_dead()))
            return true;
    }
    return false;
}

inline void cache_result(imdd2imdd_cache & cache, imdd * d, imdd * r) {
    if (d->is_shared())
        cache.insert(d, r);
}

inline bool is_cached(imdd_pair2imdd_cache & cache, imdd * d1, imdd * d2, imdd * & r) {
    if (d1->is_shared() && d2->is_shared()) {
        if (cache.find(d1, d2, r) && (r == 0 || !r->is_dead()))
            return true;
    }
    return false;
}

inline void cache_result(imdd_pair2imdd_cache & cache, imdd * d1, imdd * d2, imdd * r) {
    if (d1->is_shared() && d2->is_shared())
        cache.insert(d1, d2, r);
}

inline bool destructive_update_at(bool destructive, imdd * d) {
    return destructive && !d->is_memoized() && !d->is_shared();
}

void sl_imdd_manager::inc_ref_eh(imdd * v) {
    m_manager->inc_ref(v);
}

void sl_imdd_manager::dec_ref_eh(imdd * v) {
    m_manager->dec_ref(v);
}

unsigned imdd::hc_hash() const {
    unsigned r = 0;
    r = get_arity();
    imdd_children::iterator it  = begin_children();
    imdd_children::iterator end = end_children();
    for (; it != end; ++it) {
        unsigned b = it->begin_key();
        unsigned e = it->end_key();
        imdd const * child = it->val();
        mix(b, e, r);
        if (child) {
            SASSERT(child->is_memoized());
            unsigned v = child->get_id();
            mix(v, v, r);
        }
    }
   return r;
}

bool imdd::hc_equal(imdd const * other) const {
    if (m_arity != other->m_arity)
        return false;
    return m_children.is_equal(other->m_children);
}

imdd_manager::delay_dealloc::~delay_dealloc() {
    SASSERT(m_manager.m_to_delete.size() >= m_to_delete_size);
    ptr_vector<imdd>::iterator it  = m_manager.m_to_delete.begin() + m_to_delete_size;
    ptr_vector<imdd>::iterator end = m_manager.m_to_delete.end();
    for (; it != end; ++it) {
        SASSERT((*it)->is_dead());
        m_manager.deallocate_imdd(*it);
    }
    m_manager.m_to_delete.shrink(m_to_delete_size);
    m_manager.m_delay_dealloc = m_delay_dealloc_value;
}

imdd_manager::imdd_manager():
    m_sl_manager(m_alloc),
    m_simple_max_entries(DEFAULT_SIMPLE_MAX_ENTRIES),
    m_delay_dealloc(false) {
    m_sl_manager.m_manager = this;
    m_swap_new_child = 0;
}

imdd * imdd_manager::_mk_empty(unsigned arity) {
    SASSERT(arity > 0);
    void * mem = m_alloc.allocate(sizeof(imdd));
    return new (mem) imdd(m_sl_manager, m_id_gen.mk(), arity);
}

imdd * imdd_manager::defrag_core(imdd * d) {
    if (d->is_memoized())
        return d;
    unsigned h = d->get_arity();
    if (h == 1 && !is_simple_node(d))
        return d;
    imdd * new_d = 0;
    if (is_cached(m_defrag_cache, d, new_d))
        return new_d;
    
    if (h == 1) {
        SASSERT(is_simple_node(d));
        imdd * new_can_d = memoize(d);
        cache_result(m_defrag_cache, d, new_can_d);
        return new_can_d;
    }
    
    SASSERT(h > 1);
    new_d = _mk_empty(h);
    imdd_children::push_back_proc push_back(m_sl_manager, new_d->m_children);
    bool has_new = false;
    bool children_memoized = true;
    
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    for (; it != end; ++it) {
        imdd * child     = it->val();
        imdd * new_child = defrag_core(child);
        if (child != new_child)
            has_new = true;
        if (!new_child->is_memoized())
            children_memoized = false;
        push_back(it->begin_key(), it->end_key(), new_child);
    }
    
    if (has_new) {
        if (children_memoized && is_simple_node(new_d)) {
            imdd * new_can_d = memoize(new_d);
            if (new_can_d != new_d) {
                SASSERT(new_d->get_ref_count() == 0);
                delete_imdd(new_d);
            }
            new_d = new_can_d;
        }
    }
    else {
        SASSERT(!has_new);
        delete_imdd(new_d);
        new_d = d;
        if (children_memoized && is_simple_node(new_d)) {
            new_d = memoize(new_d);
        }
    }
    
    cache_result(m_defrag_cache, d, new_d);
    return new_d;
}

/**
   \brief Compress the given IMDD by using hash-consing.
*/
void imdd_manager::defrag(imdd_ref & d) {
    delay_dealloc delay(*this);
    m_defrag_cache.reset();
    d = defrag_core(d);
}

/**
   \brief Memoize the given IMDD.
   Return an IMDD structurally equivalent to d.
   This method assumes the children of d are memoized.
   If that is not the case, the user should invoke defrag instead.
*/
imdd * imdd_manager::memoize(imdd * d) {
    if (d->is_memoized())
        return d;
    unsigned h = d->get_arity();
    m_tables.reserve(h);
    DEBUG_CODE({
        if (h > 1) {
            imdd_children::iterator it  = d->begin_children();
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                SASSERT(it->val()->is_memoized());
            }
        }
    });
    imdd * r = m_tables[h-1].insert_if_not_there(d);
    if (r == d) {
        r->mark_as_memoized();
    }
    SASSERT(r->is_memoized());
    return r;
}

/**
   \brief Remove the given IMDD from the hash-consing table
*/
void imdd_manager::unmemoize(imdd * d) {
    SASSERT(d->is_memoized());
    m_tables[d->get_arity()-1].erase(d);
    d->mark_as_memoized(false);
}
    

/**
   \brief Remove the given IMDD (and its children) from the hash-consing tables.
*/
void imdd_manager::unmemoize_rec(imdd * d) {
    SASSERT(m_worklist.empty());
    m_worklist.push_back(d);
    while (!m_worklist.empty()) {
        d = m_worklist.back();
        if (d->is_memoized()) {
            unmemoize(d);
            SASSERT(!d->is_memoized());
            if (d->get_arity() > 1) {
                imdd_children::iterator it  = d->begin_children();
                imdd_children::iterator end = d->end_children();
                for (; it != end; ++it) 
                    m_worklist.push_back(it->val());
            }
        }
    }
}

bool imdd_manager::is_simple_node(imdd * d) const {
    return !d->m_children.has_more_than_k_entries(m_simple_max_entries);
}

void imdd_manager::mark_as_dead(imdd * d) { 
    // The references to the children were decremented by delete_imdd.
    SASSERT(!d->is_dead());
    d->m_children.deallocate_no_decref(m_sl_manager);
    d->mark_as_dead();
    if (m_delay_dealloc)
        m_to_delete.push_back(d);
    else
        deallocate_imdd(d);
}

void imdd_manager::deallocate_imdd(imdd * d) { 
    SASSERT(d->is_dead());
    memset(d, 0, sizeof(*d));
    m_alloc.deallocate(sizeof(imdd), d); 
}

void imdd_manager::delete_imdd(imdd * d) {
    SASSERT(m_worklist.empty());
    m_worklist.push_back(d);
    
    while (!m_worklist.empty()) {
        d = m_worklist.back();
        m_worklist.pop_back();

        m_id_gen.recycle(d->get_id());
        
        SASSERT(d->get_ref_count() == 0);
        if (d->is_memoized()) {
            unsigned arity = d->get_arity();
            SASSERT(m_tables[arity-1].contains(d));
            m_tables[arity-1].erase(d);
        }

        if (d->get_arity() > 1) {
            imdd_children::iterator it  = d->begin_children();
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                imdd * child = it->val();
                SASSERT(child);
                child->dec_ref();
                if (child->get_ref_count() == 0)
                    m_worklist.push_back(child);
            }
        }
        
        mark_as_dead(d);
    }
}

/**
   \brief Return a (non-memoized) shallow copy of d.
*/
imdd * imdd_manager::copy_main(imdd * d) {
    imdd * d_copy = _mk_empty(d->get_arity());
    d_copy->m_children.copy(m_sl_manager, d->m_children);
    SASSERT(!d_copy->is_memoized());
    SASSERT(d_copy->get_ref_count() == 0);
    return d_copy;
}

/**
   \brief Insert the values [b, e] into a IMDD of arity 1.
   
   If destructive == true, d is not memoized and is not shared, then a
   destructive update is performed, and d is returned.
   
   Otherwise, a fresh IMDD is returned. 
*/
imdd * imdd_manager::insert_main(imdd * d, unsigned b, unsigned e, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == 1);
    if (destructive_update_at(destructive, d)) {
        add_child(d, b, e, 0);
        return d;
    }
    else {
        imdd * new_d = copy_main(d);
        add_child(new_d, b, e, 0);
        return memoize_new_imdd_if(memoize_res, new_d);
    }
}


/**
   \brief Remove the values [b, e] from an IMDD of arity 1.
   
   If destructive == true, d is not memoized and is not shared, then a
   destructive update is performed, and d is returned.
   
   Otherwise, a fresh IMDD is returned. 
*/
imdd * imdd_manager::remove_main(imdd * d, unsigned b, unsigned e, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == 1);
    if (destructive_update_at(destructive, d)) {
        remove_child(d, b, e);
        return d;
    }
    else {
        imdd * new_d = copy_main(d);
        remove_child(new_d, b, e);
        return memoize_new_imdd_if(memoize_res, new_d);
    }
}

/**
   \brief Auxiliary functor used to implement destructive version of mk_product.
*/
struct imdd_manager::null2imdd_proc {
    imdd * m_d2;
    null2imdd_proc(imdd * d2):m_d2(d2) {}
    imdd * operator()(imdd * d) { SASSERT(d == 0); return m_d2; }
};

/**
   \brief Auxiliary functor used to implement destructive version of mk_product.
*/
struct imdd_manager::mk_product_proc {
    imdd_manager & m_manager;
    imdd *         m_d2;
    bool           m_memoize;
    mk_product_proc(imdd_manager & m, imdd * d2, bool memoize):
        m_manager(m),
        m_d2(d2),
        m_memoize(memoize) {
    }
    imdd * operator()(imdd * d1) { return m_manager.mk_product_core(d1, m_d2, true, m_memoize); }
};

imdd * imdd_manager::mk_product_core(imdd * d1, imdd * d2, bool destructive, bool memoize_res) {
    SASSERT(!d1->empty());
    SASSERT(!d2->empty());
    if (destructive && !d1->is_shared()) {
        if (d1->is_memoized())
            unmemoize(d1);
        
        if (d1->get_arity() == 1) {
            null2imdd_proc f(d2);
            d1->m_children.update_values(m_sl_manager, f);
            d1->m_arity += d2->m_arity;
        }
        else {
            mk_product_proc f(*this, d2, memoize_res);
            d1->m_children.update_values(m_sl_manager, f);
            d1->m_arity += d2->m_arity;
        }
        return d1;
    }
    else {
        imdd * new_d1 = 0;
        if (is_cached(m_mk_product_cache, d1, new_d1))
            return new_d1;
        unsigned arity1 = d1->get_arity();
        unsigned arity2 = d2->get_arity();
        new_d1 = _mk_empty(arity1 + arity2);
        imdd_children::push_back_proc push_back(m_sl_manager, new_d1->m_children);
        imdd_children::iterator it  = d1->begin_children();
        imdd_children::iterator end = d1->end_children();
        bool children_memoized = true;
        for (; it != end; ++it) {
            imdd * new_child;
            if (arity1 == 1)
                new_child = d2;
            else
                new_child = mk_product_core(it->val(), d2, false, memoize_res);
            if (!new_child->is_memoized())
                children_memoized = false;
            push_back(it->begin_key(), it->end_key(), new_child);
        }
        new_d1 = memoize_new_imdd_if(memoize_res && children_memoized, new_d1);
        cache_result(m_mk_product_cache, d1, new_d1);
        return new_d1;
    }
}

imdd * imdd_manager::mk_product_main(imdd * d1, imdd * d2, bool destructive, bool memoize_res) {
    if (d1->empty() || d2->empty()) {
        unsigned a1 = d1->get_arity();
        unsigned a2 = d2->get_arity();
        return _mk_empty(a1 + a2);
    }
    delay_dealloc delay(*this);
    if (d1 == d2)
        destructive = false;
    m_mk_product_cache.reset();
    return mk_product_core(d1, d2, destructive, memoize_res);
}

void imdd_manager::init_add_facts_new_children(unsigned num, unsigned const * lowers, unsigned const * uppers, bool memoize_res) {
    if (m_add_facts_new_children[num] != 0) {
        DEBUG_CODE({
            for (unsigned i = 1; i <= num; i++) {
                SASSERT(m_add_facts_new_children[i] != 0);
            }});
        return;
    }
    for (unsigned i = 1; i <= num; i++) {
        if (m_add_facts_new_children[i] == 0) {
            imdd * new_child = _mk_empty(i);
            unsigned b = lowers[num - i];
            unsigned e = uppers[num - i];
            bool prev_memoized = true;
            if (i == 1) {
                add_child(new_child, b, e, 0);
            }
            else {
                SASSERT(m_add_facts_new_children[i-1] != 0);
                prev_memoized = m_add_facts_new_children[i-1]->is_memoized();
                add_child(new_child, b, e, m_add_facts_new_children[i-1]);
            }
            new_child = memoize_new_imdd_if(memoize_res && prev_memoized, new_child);
            m_add_facts_new_children[i] = new_child;
        }
    }
    DEBUG_CODE({
        for (unsigned i = 1; i <= num; i++) {
            SASSERT(m_add_facts_new_children[i] != 0);
        }});
}

imdd * imdd_manager::add_facts_core(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == num);
    imdd_ref new_child(*this);
    bool new_children_memoized = true;    
#define INIT_NEW_CHILD() {                                                                      \
            if (new_child == 0) {                                                               \
                init_add_facts_new_children(num - 1, lowers + 1, uppers + 1, memoize_res);      \
                new_child = m_add_facts_new_children[num-1];                                    \
                if (!new_child->is_memoized()) new_children_memoized = false;                   \
            }}
    
    if (destructive_update_at(destructive, d)) {
        if (num == 1)
            return insert_main(d, *lowers, *uppers, destructive, memoize_res);
        SASSERT(num > 1);
        sbuffer<entry> to_insert;
        new_child = m_add_facts_new_children[num-1];
        
        unsigned b  = *lowers;
        unsigned e  = *uppers;
        imdd_children::iterator it  = d->m_children.find_geq(b);
        imdd_children::iterator end = d->end_children();
        for (; it != end && b <= e; ++it) {
            imdd_children::entry const & curr_entry = *it;
            if (e < curr_entry.begin_key())
                break;
            if (b < curr_entry.begin_key()) {
                INIT_NEW_CHILD();
                SASSERT(b <= curr_entry.begin_key() - 1);
                to_insert.push_back(entry(b, curr_entry.begin_key() - 1, new_child));
                b = curr_entry.begin_key();
            }
            imdd * curr_child     = curr_entry.val();
            SASSERT(b >= curr_entry.begin_key());
            bool cover = b == curr_entry.begin_key() && e >= curr_entry.end_key();
            // If cover == true, then the curr_child is completely covered by the new facts, and it is not needed anymore. 
            // So, we can perform a destructive update. 
            imdd * new_curr_child = add_facts_core(curr_child, num - 1, lowers + 1, uppers + 1, cover, memoize_res);
            
            if (e >= curr_entry.end_key()) {
                SASSERT(b <= curr_entry.end_key());
                to_insert.push_back(entry(b, curr_entry.end_key(), new_curr_child));
            }
            else {
                SASSERT(e < curr_entry.end_key());
                SASSERT(b <= e);
                to_insert.push_back(entry(b, e, new_curr_child));
            }
            b = curr_entry.end_key() + 1;
        }
        // Re-insert entries in m_add_facts_to_insert into d->m_children,
        // and if b <= e also insert [b, e] -> new_child
        if (b <= e) {
            INIT_NEW_CHILD();
            add_child(d, b, e, new_child);
        }

        svector<entry>::iterator it2  = to_insert.begin();
        svector<entry>::iterator end2 = to_insert.end();
        for (; it2 != end2; ++it2) {
            imdd_children::entry const & curr_entry = *it2;
            add_child(d, curr_entry.begin_key(), curr_entry.end_key(), curr_entry.val());
        }

        return d;
    }
    else {
        imdd * new_d = 0;
        if (is_cached(m_add_facts_cache, d, new_d))
            return new_d;
        
        if (num == 1) {
            new_d = insert_main(d, *lowers, *uppers, destructive, memoize_res);
        }
        else {
            new_d = copy_main(d);
            new_child = m_add_facts_new_children[num-1];
            TRACE("add_facts_bug", tout << "after copying: " << new_d << "\n" << mk_ll_pp(new_d, *this) << "\n";);

            unsigned b  = *lowers;
            unsigned e  = *uppers;
            imdd_children::iterator it  = d->m_children.find_geq(b);
            imdd_children::iterator end = d->end_children();
            for (; it != end && b <= e; ++it) {
                imdd_children::entry const & curr_entry = *it;
                if (e < curr_entry.begin_key())
                    break;
                if (b < curr_entry.begin_key()) {
                    INIT_NEW_CHILD();
                    SASSERT(b <= curr_entry.begin_key() - 1);
                    add_child(new_d, b, curr_entry.begin_key() - 1, new_child);
                    TRACE("add_facts_bug", tout << "after inserting new child: " << new_d << "\n" << mk_ll_pp(new_d, *this) << "\n";);
                    b = curr_entry.begin_key();
                }
                imdd * curr_child     = curr_entry.val();
                imdd * new_curr_child = add_facts_core(curr_child, num - 1, lowers + 1, uppers + 1, false, memoize_res);
                if (!new_curr_child->is_memoized())
                    new_children_memoized = false;
                if (e >= curr_entry.end_key()) {
                    SASSERT(b <= curr_entry.end_key());
                    add_child(new_d, b, curr_entry.end_key(), new_curr_child);
                    TRACE("add_facts_bug", tout << "1) after inserting new curr child: " << new_d << "\n" << mk_ll_pp(new_d, *this) << "\n";
                          tout << "new_curr_child: " << mk_ll_pp(new_curr_child, *this) << "\n";);
                }
                else {
                    SASSERT(e < curr_entry.end_key());
                    SASSERT(b <= e);
                    add_child(new_d, b, e, new_curr_child);
                    TRACE("add_facts_bug", tout << "2) after inserting new curr child: " << new_d << "\n" << mk_ll_pp(new_d, *this) << "\n";
                          tout << "new_curr_child: " << mk_ll_pp(new_curr_child, *this) << "\n";);
                }
                b = curr_entry.end_key() + 1;
            }
            if (b <= e) {
                INIT_NEW_CHILD();
                add_child(new_d, b, e, new_child);
            }
            
            new_d = memoize_new_imdd_if(memoize_res && d->is_memoized() && new_children_memoized, new_d);
        }
        
        cache_result(m_add_facts_cache, d, new_d);
        return new_d;
    }
}

imdd * imdd_manager::add_facts_main(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == num);
    delay_dealloc delay(*this);
    m_add_facts_cache.reset();
    m_add_facts_new_children.reset();
    m_add_facts_new_children.resize(num, 0);
    return add_facts_core(d, num, lowers, uppers, destructive, memoize_res);
}

inline void update_memoized_flag(imdd * d, bool & memoized_flag) {
    if (d && !d->is_memoized())
        memoized_flag = false;
}

void imdd_manager::push_back_entries(unsigned head, imdd_children::iterator & it, imdd_children::iterator & end, 
                                     imdd_children::push_back_proc & push_back, bool & children_memoized) {
    if (it != end) {
        push_back(head, it->end_key(), it->val());
        update_memoized_flag(it->val(), children_memoized);
        ++it;
        for (; it != end; ++it) {
            update_memoized_flag(it->val(), children_memoized);
            push_back(it->begin_key(), it->end_key(), it->val());
        }
    }
}

/**
   \brief Push the entries starting at head upto the given limit (no included).
   That is, we are copying the entries in the interval [head, limit).
*/
void imdd_manager::push_back_upto(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end,
                                  unsigned limit, imdd_children::push_back_proc & push_back, bool & children_memoized) {
    SASSERT(it != end);
    SASSERT(head <= it->end_key());
    SASSERT(head >= it->begin_key());
    SASSERT(head < limit);
    while (head < limit && it != end) {
        if (it->end_key() < limit) {
            update_memoized_flag(it->val(), children_memoized);
            push_back(head, it->end_key(), it->val());
            ++it;
            if (it != end)
                head = it->begin_key();
        }
        else {
            SASSERT(it->end_key() >= limit);
            update_memoized_flag(it->val(), children_memoized);
            push_back(head, limit-1, it->val());
            head = limit;
        }
    }
    SASSERT(head == limit || it == end || head == it->begin_key());
}

void imdd_manager::move_head(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end, unsigned new_head) {
    SASSERT(new_head >= head);
    SASSERT(head >= it->begin_key());
    SASSERT(head <= it->end_key());
    SASSERT(new_head <= it->end_key());
    if (new_head < it->end_key()) {
        head = new_head+1;
        SASSERT(head <= it->end_key());
    }
    else {
        SASSERT(new_head == it->end_key());
        ++it;
        if (it != end)
            head = it->begin_key();
    }
}

/**
   \brief Copy the entries starting at head upto the given limit (no included).
   That is, we are copying the entries in the interval [head, limit).
*/
void imdd_manager::copy_upto(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end,
                             unsigned limit, sbuffer<entry> & result) {
    SASSERT(it != end);
    SASSERT(head <= it->end_key());
    SASSERT(head >= it->begin_key());
    SASSERT(head < limit);
    while (head < limit && it != end) {
        if (it->end_key() < limit) {
            result.push_back(entry(head, it->end_key(), it->val()));
            ++it;
            if (it != end)
                head = it->begin_key();
        }
        else {
            SASSERT(it->end_key() >= limit);
            result.push_back(entry(head, limit-1, it->val()));
            head = limit;
        }
    }
    SASSERT(head == limit || it == end || head == it->begin_key());
}

imdd * imdd_manager::mk_union_core(imdd * d1, imdd * d2, bool destructive, bool memoize_res) {
    if (d1 == d2)
        return d1;
    if (destructive_update_at(destructive, d1)) {
        if (d1->get_arity() == 1) {
            imdd_children::iterator it  = d2->begin_children();
            imdd_children::iterator end = d2->end_children();
            for (; it != end; ++it)
                add_child(d1, it->begin_key(), it->end_key(), 0);
            return d1;
        }
        else {
            imdd_children::iterator it2  = d2->begin_children();
            imdd_children::iterator end2 = d2->end_children();
            imdd_children::iterator it1  = d1->m_children.find_geq(it2->begin_key());
            imdd_children::iterator end1 = d1->end_children();
            sbuffer<entry> to_insert; 
            unsigned head1 = it1 != end1 ? it1->begin_key() : UINT_MAX;
            SASSERT(it2 != end2);
            unsigned head2 = it2->begin_key();
            while (true) {
                if (it1 == end1) {
                    // copy it2 to d1
                    // Remark: we don't need to copy to to_insert, since we will not be using it1 anymore.
                    // That is, we can directly insert into d1->m_children.
                    if (it2 != end2) {
                        add_child(d1, head2, it2->end_key(), it2->val());
                        ++it2;
                        for (; it2 != end2; ++it2)
                            add_child(d1, it2->begin_key(), it2->end_key(), it2->val());
                    }
                    break;
                }
                
                if (it2 == end2) {
                    break;
                }

                if (head1 < head2) {
                    it1.move_to(head2);
                    head1 = it1 != end1 ? (it1->begin_key() < head2?head2:it1->begin_key()): UINT_MAX;
                }
                else if (head1 > head2) {
                    copy_upto(head2, it2, end2, head1, to_insert);
                }
                else {
                    SASSERT(head1 == head2);
                    unsigned tail = std::min(it1->end_key(), it2->end_key());
                    imdd * new_child = 0;
                    SASSERT(d1->get_arity() > 1);
                    bool cover = head1 == it1->begin_key() && tail == it1->end_key();
                    // If cover == true, then the it1->val() (curr_child) is completely covered by 
                    // the new_child, and it is not needed anymore. 
                    // So, we can perform a destructive update. 
                    new_child = mk_union_core(it1->val(), it2->val(), cover, memoize_res);
                    if (new_child != it1->val())
                        to_insert.push_back(entry(head1, tail, new_child));
                    move_head(head1, it1, end1, tail);
                    move_head(head2, it2, end2, tail);
                }
            }
            sbuffer<entry>::const_iterator it3  = to_insert.begin();
            sbuffer<entry>::const_iterator end3 = to_insert.end();
            for (; it3 != end3; ++it3)
                add_child(d1, it3->begin_key(), it3->end_key(), it3->val());
            return d1;
        }
    }
    else {
        imdd * r = 0;
        if (is_cached(m_union_cache, d1, d2, r))
            return r;

        unsigned arity = d1->get_arity();
        r = _mk_empty(arity);
        imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);
        imdd_children::iterator it1  = d1->begin_children();
        imdd_children::iterator end1 = d1->end_children();
        imdd_children::iterator it2  = d2->begin_children();
        imdd_children::iterator end2 = d2->end_children();
        SASSERT(it1 != end1);
        SASSERT(it2 != end2);
        unsigned head1 = it1->begin_key();
        unsigned head2 = it2->begin_key();
        bool children_memoized = true;
        while (true) {
            if (it1 == end1) {
                // copy it2 to result
                push_back_entries(head2, it2, end2, push_back, children_memoized);
                break;
            }
            if (it2 == end2) {
                // copy it1 to result
                push_back_entries(head1, it1, end1, push_back, children_memoized);
                break;
            }

            if (head1 < head2) {
                push_back_upto(head1, it1, end1, head2, push_back, children_memoized); 
            }
            else if (head1 > head2) {
                push_back_upto(head2, it2, end2, head1, push_back, children_memoized);
            }
            else {
                SASSERT(head1 == head2);
                unsigned tail = std::min(it1->end_key(), it2->end_key());
                imdd * new_child = 0;
                if (arity > 1) {
                    new_child = mk_union_core(it1->val(), it2->val(), false, memoize_res);
                    update_memoized_flag(new_child, children_memoized);
                }
                push_back(head1, tail, new_child);
                move_head(head1, it1, end1, tail);
                move_head(head2, it2, end2, tail);
            }
        }
        r = memoize_new_imdd_if(memoize_res && children_memoized, r);
        cache_result(m_union_cache, d1, d2, r);
        return r;
    }
}

void imdd_manager::reset_union_cache() {
    m_union_cache.reset();
}

imdd * imdd_manager::mk_union_main(imdd * d1, imdd * d2, bool destructive, bool memoize_res) {
    SASSERT(d1->get_arity() == d2->get_arity());
    if (d1 == d2)
        return d1;
    if (d1->empty())
        return d2;
    if (d2->empty())
        return d1;
    delay_dealloc delay(*this);
    reset_union_cache();
    return mk_union_core(d1, d2, destructive, memoize_res);
}

void imdd_manager::mk_union_core_dupdt(imdd_ref & d1, imdd * d2, bool memoize_res) {
    SASSERT(d1->get_arity() == d2->get_arity());
    if (d1 == d2 || d2->empty())
        return;
    if (d1->empty()) {
        d1 = d2;
        return;
    }
    d1 = mk_union_core(d1, d2, true, memoize_res);
}

void imdd_manager::mk_union_core(imdd * d1, imdd * d2, imdd_ref & r, bool memoize_res) { 
    SASSERT(d1->get_arity() == d2->get_arity());
    if (d1 == d2 || d2->empty()) {
        r = d1;
        return;
    }
    if (d1->empty()) {
        r = d2;
        return;
    }
    TRACE("mk_union_core", 
          tout << "d1:\n"; 
          display_ll(tout, d1); 
          tout << "d2:\n";
          display_ll(tout, d2););
    r = mk_union_core(d1, d2, false, memoize_res); 
}

imdd * imdd_manager::mk_complement_core(imdd * d, unsigned num, unsigned const * mins, unsigned const * maxs, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == num);
    SASSERT(!d->empty());
    SASSERT(*mins <= *maxs);
    unsigned arity = d->get_arity();
    imdd_ref new_child(*this);
    bool new_children_memoized = true;    
#undef  INIT_NEW_CHILD
#define INIT_NEW_CHILD() {                                                              \
            if (arity > 1 && new_child == 0) {                                          \
                init_add_facts_new_children(num - 1, mins + 1, maxs + 1, memoize_res);  \
                new_child = m_add_facts_new_children[num-1];                            \
                SASSERT(new_child != 0);                                                \
                if (!new_child->is_memoized()) new_children_memoized = false;           \
            }}
    
    if (false && destructive_update_at(destructive, d)) {
        // TODO
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    else {
        destructive = false;
        imdd * r = 0;
        if (is_cached(m_complement_cache, d, r))
            return r;
        
        r = _mk_empty(arity);
        imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);

        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        unsigned prev_key           = *mins;
        for (; it != end; ++it) {
            SASSERT(it->begin_key() >= *mins);
            SASSERT(it->end_key()   <= *maxs);
            if (prev_key < it->begin_key()) {
                INIT_NEW_CHILD();
                push_back(prev_key, it->begin_key() - 1, new_child);
            }
            if (arity > 1) {
                imdd * new_curr = mk_complement_core(it->val(), num - 1, mins + 1, maxs + 1, false, memoize_res);
                if (new_curr != 0) {
                    push_back(it->begin_key(), it->end_key(), new_curr);
                    if (!new_curr->is_memoized())
                        new_children_memoized = false;
                }
            }
            prev_key = it->end_key() + 1;
        }

        if (prev_key <= *maxs) {
            INIT_NEW_CHILD();
            push_back(prev_key, *maxs, new_child);
        }

        if (r->empty()) {
            delete_imdd(r);
            r = 0;
        }
        
        r = memoize_new_imdd_if(r && memoize_res && new_children_memoized, r);
        cache_result(m_complement_cache, d, r);
        return r;
    }
}

imdd * imdd_manager::mk_complement_main(imdd * d, unsigned num, unsigned const * mins, unsigned const * maxs, bool destructive, bool memoize_res) {
    unsigned arity = d->get_arity();
    SASSERT(arity == num);
    // reuse m_add_facts_new_children for creating the universe-set IMDDs
    m_add_facts_new_children.reset();
    m_add_facts_new_children.resize(num+1, 0);

    if (d->empty()) {
        // return the universe-set
        init_add_facts_new_children(num, mins, maxs, memoize_res);
        return m_add_facts_new_children[num];
    }

    delay_dealloc delay(*this);
    m_complement_cache.reset();
    imdd * r = mk_complement_core(d, num, mins, maxs, destructive, memoize_res);
    if (r == 0)
        return _mk_empty(arity);
    else
        return r;
}

/**
   \brief Replace the IMDD children with new_children.
   The function will also decrement the ref-counter of every IMDD in new_children, since
   it assumes the counter was incremented when the IMDD was inserted into the buffer.
*/
void imdd::replace_children(sl_imdd_manager & m, sbuffer<imdd_children::entry> & new_children) {
    m_children.reset(m);
    imdd_children::push_back_proc push_back(m, m_children);
    svector<imdd_children::entry>::iterator it  = new_children.begin();
    svector<imdd_children::entry>::iterator end = new_children.end();
    for (; it != end; ++it) {
        SASSERT(it->val() == 0 || it->val()->get_ref_count() > 0);
        push_back(it->begin_key(), it->end_key(), it->val());
        SASSERT(it->val() == 0 || it->val()->get_ref_count() > 1);
        if (it->val() != 0)
            it->val()->dec_ref();
    }
}

imdd * imdd_manager::mk_filter_equal_core(imdd * d, unsigned vidx, unsigned value, bool destructive, bool memoize_res) {
    SASSERT(!d->empty());
    SASSERT(vidx >= 0 && vidx < d->get_arity());
    unsigned arity = d->get_arity();
    if (destructive_update_at(destructive, d)) {
        if (vidx == 0) {
            imdd * child = 0;
            if (d->m_children.find(value, child)) {
                imdd_ref ref(*this);
                ref = child; // protect child, we don't want the following reset to delete it.
                d->m_children.reset(m_sl_manager);
                add_child(d, value, child);
                return d;
            }
            else {
                return 0;
            }
        }
        SASSERT(arity > 1);
        sbuffer<entry> to_insert;
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        for (; it != end; ++it) {
            imdd * curr_child = it->val();
            imdd * new_child  = mk_filter_equal_core(curr_child, vidx-1, value, true, memoize_res);
            if (new_child != 0) {
                new_child->inc_ref(); // protect new child, we will be resetting d->m_children later.
                to_insert.push_back(entry(it->begin_key(), it->end_key(), new_child));
            }
        }
        if (to_insert.empty()) {
            return 0;
        }
        d->replace_children(m_sl_manager, to_insert);
        return d;
    }

    imdd * r = 0;
    if (is_cached(m_filter_equal_cache, d, r))
        return r;
    bool new_children_memoized = true;
    
    if (vidx == 0) {
        // found filter variable
        imdd * child = 0;
        if (d->m_children.find(value, child)) {
            r = _mk_empty(arity);
            add_child(r, value, child);
            if (child && !child->is_memoized())
                new_children_memoized = false;
        }
        else {
            r = 0;
        }
    }
    else {
        SASSERT(arity > 1);
        r = _mk_empty(arity);
        imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        for (; it != end; ++it) {
            imdd * curr_child = it->val();
            imdd * new_child  = mk_filter_equal_core(curr_child, vidx-1, value, false, memoize_res);
            if (new_child != 0) {
                push_back(it->begin_key(), it->end_key(), new_child);
                if (!new_child->is_memoized())
                    new_children_memoized = false;
            }
        }
        if (r->empty()) {
            delete_imdd(r);
            r = 0;
        }
    }

    r = memoize_new_imdd_if(r && memoize_res && new_children_memoized, r);
    cache_result(m_filter_equal_cache, d, r);
    return r;
}

imdd * imdd_manager::mk_filter_equal_main(imdd * d, unsigned vidx, unsigned value, bool destructive, bool memoize_res) {
    unsigned arity = d->get_arity();
    SASSERT(vidx >= 0 && vidx < arity);
    if (d->empty())
        return d;
    delay_dealloc delay(*this);
    m_filter_equal_cache.reset();
    imdd * r = mk_filter_equal_core(d, vidx, value, destructive, memoize_res);
    if (r == 0)
        return _mk_empty(arity);
    else
        return r;
}


/**
   \brief create map from imdd nodes to the interval of variables that are covered by variable.
   
*/

static void mk_interval_set_intersect(sl_manager_base<unsigned> &m, sl_interval_set const& src, unsigned b, unsigned e, sl_interval_set& dst) {
    sl_interval_set::iterator it = src.find_geq(b);
    sl_interval_set::iterator end = src.end();
    for (; it != end; ++it) {
        unsigned b1 = it->begin_key();
        unsigned e1 = it->end_key();
        if (e < b1) {
            break;
        }
        if (b1 < b) {
            b1 = b;
        }
        if (e < e1) {
            e1 = e;
        }
        SASSERT(b <= b1 && b1 <= e1 && e1 <= e);
        dst.insert(m, b1, e1);      
    }
}

static void mk_interval_set_union(sl_manager_base<unsigned> &m, sl_interval_set& dst, sl_interval_set const& src) {
    sl_interval_set::iterator it = src.begin(), end = src.end();
    for (; it != end; ++it) {
        dst.insert(m, it->begin_key(), it->end_key());
    }
}

void imdd_manager::reset_fi_intervals(sl_imanager& m) {
    for (unsigned i = 0; i < m_alloc_is.size(); ++i) {
        m_alloc_is[i]->deallocate(m);
        dealloc(m_alloc_is[i]);
    }
    m_alloc_is.reset();
    m_imdd2interval_set.reset();
}

sl_interval_set const* imdd_manager::init_fi_intervals(sl_imanager& m, imdd* d, unsigned var, unsigned num_found) {
    sl_interval_set* result = 0;
#define ALLOC_RESULT() if (!result) { result = alloc(sl_interval_set, m); m_alloc_is.push_back(result); }
    if (m_imdd2interval_set.find(d, result)) {
        return result;
    }
    bool _is_fi_var = is_fi_var(var);
    unsigned new_num_found = _is_fi_var?num_found+1:num_found;
    bool last_fi_var = (new_num_found == m_fi_num_vars);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    for (; it != end; ++it) {
        imdd_children::entry const & curr_entry = *it;
        unsigned b = curr_entry.begin_key();
        unsigned e = curr_entry.end_key();
        
        if (last_fi_var) {
            ALLOC_RESULT();
            result->insert(m, b, e, 1);                
        }
        else {
            SASSERT(d->get_arity() > 1);
            imdd* curr_child = curr_entry.val();
            sl_interval_set const* is2 = init_fi_intervals(m, curr_child, var+1, new_num_found);
            if (!is2) {
                continue;
            }
            if (_is_fi_var) {                
                sl_interval_set is3(m);
                mk_interval_set_intersect(m, *is2, b, e, is3);                
                if (!is3.empty()) {
                    ALLOC_RESULT();
                    mk_interval_set_union(m, *result, is3);
                }
                is3.deallocate(m);
            }
            else {
                if (is2 && result != is2) {
                    ALLOC_RESULT();
                    mk_interval_set_union(m, *result, *is2);                
                }
            }
        }
    }
    m_imdd2interval_set.insert(d, result);
    return result;
}

inline mk_fi_result mk(imdd * d) {
    mk_fi_result r;
    r.m_d = d;
    return r;
}

inline mk_fi_result mk(fi_cache_entry * e) {
    mk_fi_result r;
    r.m_entry = e;
    return r;
}

fi_cache_entry * imdd_manager::mk_fi_cache_entry(imdd * d, unsigned lower, unsigned upper, unsigned num_pairs, imdd_value_pair pairs[]) {
    void * mem = m_fi_entries.allocate(sizeof(fi_cache_entry) + sizeof(imdd_value_pair) * num_pairs);
    DEBUG_CODE({
        for (unsigned i = 0; i < num_pairs; i++) {
            SASSERT(pairs[i].first != 0);
        }
    });
   return new (mem) fi_cache_entry(d, lower, upper, num_pairs, pairs);
}

struct imdd_value_pair_lt_value {
    bool operator()(imdd_value_pair const & p1, imdd_value_pair const & p2) const {
        return p1.second < p2.second;
    }
};

// Review note: identical nodes should be unit intervals?
// 1 -> 1 -> x

mk_fi_result imdd_manager::mk_filter_identical_core(imdd * d, unsigned var, unsigned num_found, unsigned lower, unsigned upper, 
                                                    bool destructive, bool memoize_res) {
    TRACE("imdd", tout << "#" << d->get_id() << " var: " << var << " num_found: " << num_found << 
          " lower: " << lower << " upper: " << upper << "\n";);

    unsigned arity = d->get_arity();
#define MK_EMPTY_ENTRY (num_found == 0 && destructive_update_at(destructive, d))?mk(static_cast<imdd*>(0)):mk(static_cast<fi_cache_entry*>(0))
    sl_interval_set* node_ranges = m_imdd2interval_set.find(d);
    if (!node_ranges) {
        return MK_EMPTY_ENTRY;        
    }
    sl_interval_set::iterator sl_it = node_ranges->find_geq(lower);
    if (sl_it == node_ranges->end() || upper < sl_it->begin_key()) {
        return MK_EMPTY_ENTRY;    
    }        

    bool new_children_memoized = true;
    bool _is_fi_var = is_fi_var(var);
    if (num_found == 0) {
        SASSERT(arity > 1);
        if (destructive_update_at(destructive, d)) {
            sbuffer<entry> to_insert;
            imdd_children::iterator it  = d->begin_children();
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                imdd * curr_child = it->val();
                if (_is_fi_var) {
                    fi_cache_entry * child_entry = (mk_filter_identical_core(curr_child, 
                                                                             var+1, 
                                                                             1, 
                                                                             it->begin_key(), 
                                                                             it->end_key(), 
                                                                             false, 
                                                                             memoize_res)).m_entry;
                    for (unsigned i = 0; child_entry && i < child_entry->m_num_result; i++) {
                        imdd * new_child = child_entry->m_result[i].first;
                        unsigned value   = child_entry->m_result[i].second;
                        to_insert.push_back(entry(value, value, new_child));
                    }
                }
                else {
                    imdd * new_child  = (mk_filter_identical_core(curr_child, var+1, 0, 0, UINT_MAX, false, memoize_res)).m_d;
                    if (new_child != 0) {
                        new_child->inc_ref();
                        to_insert.push_back(entry(it->begin_key(), it->end_key(), new_child));
                    }
                }
            }
            if (to_insert.empty()) {
                return mk(static_cast<imdd*>(0));
            }
            d->replace_children(m_sl_manager, to_insert);
            return mk(d);
        }
        else {
            // num_found == 0 && variable is not part of the filter && no destructive update.
            imdd * r = 0;
            if (is_cached(m_fi_top_cache, d, r))
                return mk(r);
            r = _mk_empty(arity);
            imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);
            imdd_children::iterator it  = d->begin_children();
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                imdd * curr_child = it->val();
                if (_is_fi_var) {
                    fi_cache_entry * entry = (mk_filter_identical_core(curr_child, 
                                                                       var+1, 
                                                                       1, 
                                                                       it->begin_key(), 
                                                                       it->end_key(), 
                                                                       false, 
                                                                       memoize_res)).m_entry;
                    for (unsigned i = 0; entry && i < entry->m_num_result; i++) {
                        imdd * new_child = entry->m_result[i].first;
                        unsigned value   = entry->m_result[i].second;
                        push_back(value, value, new_child);
                        if (!new_child->is_memoized())
                            new_children_memoized = false;
                    }
                }
                else {
                    imdd * new_child  = (mk_filter_identical_core(curr_child, var+1, 0, 0, UINT_MAX, false, memoize_res)).m_d;
                    if (new_child != 0) {
                        push_back(it->begin_key(), it->end_key(), new_child);
                        if (!new_child->is_memoized())
                            new_children_memoized = false;
                    }
                }
            }
            if (r->empty()) {
                delete_imdd(r);
                r = 0;
            }
            r = memoize_new_imdd_if(r && memoize_res && new_children_memoized, r);
            cache_result(m_fi_top_cache, d, r);
            return mk(r);
        }
    }
    else {
        SASSERT(num_found > 0);
        fi_cache_entry d_entry(d, lower, upper);
        fi_cache_entry * r_entry;
        if (d->is_shared() && m_fi_bottom_cache.find(&d_entry, r_entry))
            return mk(r_entry);
        sbuffer<imdd_value_pair> result;
        if (_is_fi_var) {
            unsigned new_num_found = num_found + 1;
            bool     last_fi_var   = (new_num_found == m_fi_num_vars);
            imdd_children::iterator it  = d->m_children.find_geq(lower);
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                imdd * curr_child = it->val();
                unsigned curr_lower = it->begin_key();
                unsigned curr_upper = it->end_key();
                if (curr_lower < lower)
                    curr_lower = lower;
                if (curr_upper > upper)
                    curr_upper = upper;
                if (curr_lower <= curr_upper) {
                    if (last_fi_var) {
                        for (unsigned i = curr_lower; i <= curr_upper; i++) {
                            imdd * new_d = _mk_empty(arity);
                            add_child(new_d, i, curr_child);
                            new_d = memoize_new_imdd_if(memoize_res && (curr_child == 0 || curr_child->is_memoized()), new_d);
                            result.push_back(imdd_value_pair(new_d, i));
                        }
                    }
                    else {
                        fi_cache_entry * new_entry = (mk_filter_identical_core(curr_child, 
                                                                               var+1, 
                                                                               new_num_found,
                                                                               curr_lower,
                                                                               curr_upper,
                                                                               false,
                                                                               memoize_res)).m_entry;
                        for (unsigned i = 0; new_entry && i < new_entry->m_num_result; i++) {
                            SASSERT(new_entry->m_result[i].first != 0);
                            imdd * curr_child = new_entry->m_result[i].first;
                            unsigned value    = new_entry->m_result[i].second;
                            imdd * new_d      = _mk_empty(arity);
                            add_child(new_d, value, curr_child);
                            SASSERT(curr_child != 0);
                            new_d = memoize_new_imdd_if(memoize_res && curr_child->is_memoized(), new_d);
                            result.push_back(imdd_value_pair(new_d, value));
                        }
                    }
                }
                if (curr_upper == upper)
                    break;
            }
        }
        else {
            SASSERT(arity > 1);
            u_map<imdd*> value2imdd;
            imdd_children::iterator it  = d->begin_children();
            imdd_children::iterator end = d->end_children();
            for (; it != end; ++it) {
                imdd * curr_child = it->val();
                SASSERT(curr_child != 0);
                fi_cache_entry * new_entry = (mk_filter_identical_core(curr_child, 
                                                                       var+1, 
                                                                       num_found,
                                                                       lower,
                                                                       upper,
                                                                       false,
                                                                       memoize_res)).m_entry;
                for (unsigned i = 0; new_entry && i < new_entry->m_num_result; i++) {
                    unsigned value     = new_entry->m_result[i].second;
                    imdd *   new_child = new_entry->m_result[i].first;
                    imdd *   new_d     = 0;
                    if (!value2imdd.find(value, new_d)) {
                        new_d = _mk_empty(arity);
                        value2imdd.insert(value, new_d);
                        result.push_back(imdd_value_pair(new_d, value));
                    }
                    SASSERT(new_d != 0);
                    add_child(new_d, it->begin_key(), it->end_key(), new_child);
                }
            }
            std::sort(result.begin(), result.end(), imdd_value_pair_lt_value());
        }
        r_entry = mk_fi_cache_entry(d, lower, upper, result.size(), result.c_ptr());
        if (d->is_shared())
            m_fi_bottom_cache.insert(r_entry);
        return mk(r_entry);
    }
}

imdd * imdd_manager::mk_filter_identical_main(imdd * d, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res) {
    if (d->empty() || num_vars < 2)
        return d;
    TRACE("imdd",
          tout << "vars: ";
          for (unsigned i = 0; i < num_vars; ++i) {
              tout << vars[i] << " ";
          }
          tout << "\n";
          tout << "rows: " << get_num_rows(d) << "\n";
          display_ll(tout, d); );
    unsigned arity = d->get_arity();
    DEBUG_CODE(for (unsigned i = 0; i < num_vars; ++i) SASSERT(vars[i] < arity););
    m_fi_num_vars   = num_vars;
    m_fi_begin_vars = vars;
    m_fi_end_vars   = vars + num_vars;
    delay_dealloc delay(*this);
    m_fi_bottom_cache.reset();
    m_fi_top_cache.reset();
    m_fi_entries.reset();
    
    sl_imanager imgr;
    init_fi_intervals(imgr, d, 0, 0);

    TRACE("imdd_verbose",
        ptr_addr_hashtable<sl_interval_set> ht;
        imdd2intervals::iterator it = m_imdd2interval_set.begin();
        imdd2intervals::iterator end = m_imdd2interval_set.end();
        for (; it != end; ++it) {
            tout << it->m_key->get_id() << " ";
            if (it->m_value) {
                if (ht.contains(it->m_value)) {
                    tout << "dup\n";
                    continue;
                }
                ht.insert(it->m_value);
                sl_interval_set::iterator sit = it->m_value->begin();
                sl_interval_set::iterator send = it->m_value->end(); 
                for (; sit != send; ++sit) {
                    tout << "[" << sit->begin_key() << ":" << sit->end_key() << "] ";
                }
            }
            else {
                tout << "{}";
            }
            tout << "\n";
        });
    mk_fi_result r = mk_filter_identical_core(d, 0, 0, 0, UINT_MAX, destructive, memoize_res);
    reset_fi_intervals(imgr);

    TRACE("imdd", if (r.m_d) display_ll(tout << "result\n", r.m_d););
    if (r.m_d == 0) 
        return _mk_empty(arity);
    else
        return r.m_d;
}

void imdd_manager::swap_in(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars) {
    // variables are sorted.
    DEBUG_CODE(for (unsigned i = 0; i + 1 < num_vars; ++i) SASSERT(vars[i] < vars[i+1]););
    imdd_ref tmp1(*this), tmp2(*this);
    tmp1 = d;
    SASSERT(num_vars > 1);
    unsigned v1 = vars[0]+1; // next position to swap to.
    for (unsigned i = 1; i  < num_vars; ++i) {
        unsigned v2 = vars[i];
        SASSERT(v1 <= v2);
        for (unsigned j = v2-1; j >= v1; --j) {
            mk_swap(tmp1, tmp2, j);
            tmp1 = tmp2;
        }
        ++v1;
    }
    TRACE("imdd", 
        for (unsigned i = 0; i < num_vars; ++i) tout << vars[i] << " ";
        tout << "\n";
        display_ll(tout << "in\n", d); 
        display_ll(tout << "out\n", tmp1);
        tout << "\n";);
    r = tmp1;
}

void imdd_manager::swap_out(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars) {
    // variables are sorted.
    DEBUG_CODE(for (unsigned i = 0; i + 1 < num_vars; ++i) SASSERT(vars[i] < vars[i+1]););
    imdd_ref tmp1(*this), tmp2(*this);
    tmp1 = d;
    SASSERT(num_vars > 1);
    unsigned v1 = vars[0]+num_vars-1; // position of next variable to be swapped.
    for (unsigned i = num_vars; i > 1; ) {
        --i;
        unsigned v2 = vars[i];
        for (unsigned j = v1; j < v2; ++j) {
            mk_swap(tmp1, tmp2, j);
            tmp1 = tmp2;
        }
        --v1;
    }    
    TRACE("imdd", 
        for (unsigned i = 0; i < num_vars; ++i) tout << vars[i] << " ";
        tout << "\n";
        display_ll(tout << "out\n", d); 
        display_ll(tout << "in\n", tmp1);
        tout << "\n";);
    r = tmp1;
}

void imdd_manager::filter_identical_core2(imdd* d, unsigned num_vars, unsigned b, unsigned e, ptr_vector<imdd>& ch) {
    SASSERT(num_vars > 0);
    imdd* r = 0;

    imdd_children::iterator it  = d->m_children.find_geq(b);
    imdd_children::iterator end = d->m_children.end();

    for (; it != end; ++it) {
        unsigned b1 = it->begin_key();
        unsigned e1 = it->end_key();
        if (e < b1) {
            break;
        }
        if (b1 < b) {
            b1 = b;
        }        
        if (e <= e1) {
            e1 = e;
        }
        SASSERT(b <= b1 && b1 <= e1 && e1 <= e);
        imdd* curr_child = it->val();
        if (num_vars == 1) {
            for (unsigned i = b1; i <= e1; ++i) {
                r = _mk_empty(d->get_arity());
                add_child(r, i, i, it->val());
                r = memoize_new_imdd_if(!it->val() || it->val()->is_memoized(), r);
                ch.push_back(r);
            }
            continue;
        }
        ptr_vector<imdd> ch2;
        filter_identical_core2(curr_child, num_vars-1, b1, e1, ch2);
        for (unsigned i = 0; i < ch2.size(); ++i) {
            r = _mk_empty(d->get_arity());
            unsigned key = ch2[i]->begin_children()->begin_key();
            SASSERT(ch2[i]->begin_children()->end_key() == key);
            add_child(r, key, key, ch2[i]);
            r = memoize_new_imdd_if(ch2[i]->is_memoized(), r);
            ch.push_back(r);
        }
    }
}

imdd* imdd_manager::filter_identical_core2(imdd* d, unsigned var, unsigned num_vars, bool memoize_res) {
    imdd* r = 0;
    if (m_filter_identical_cache.find(d, r)) {
        return r;
    }

    bool children_memoized = true;

    r = _mk_empty(d->get_arity());
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);

    if (var > 0) {
        for (; it != end; ++it) {
            imdd* curr_child = it->val();
            imdd* new_child = filter_identical_core2(curr_child, var-1, num_vars, memoize_res);
            if (new_child) {
                push_back(it->begin_key(), it->end_key(), new_child);
                if (!new_child->is_memoized()) {
                    children_memoized = false;
                }
            }
        }
    }
    else {
        ptr_vector<imdd> ch;

        for (; it != end; ++it) {
            imdd* curr_child = it->val();
            filter_identical_core2(curr_child, num_vars-1, it->begin_key(), it->end_key(), ch);
        }
        for (unsigned i = 0; i < ch.size(); ++i) {
            unsigned key = ch[i]->begin_children()->begin_key();
            SASSERT(ch[i]->begin_children()->end_key() == key);
            push_back(key, key, ch[i]);
            if (!ch[i]->is_memoized()) {
                children_memoized = false;
            }
        }
    }        
    if (r->empty()) {
        delete_imdd(r);
        r = 0;
    }
    m_filter_identical_cache.insert(d, r);
    r = memoize_new_imdd_if(r && memoize_res && children_memoized, r);
    return r;
}

void imdd_manager::filter_identical_main2(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res) {
    m_filter_identical_cache.reset();
    imdd_ref tmp1(*this), tmp2(*this);
    swap_in(d, tmp1, num_vars, vars);
    tmp2 = filter_identical_core2(tmp1, vars[0], num_vars, memoize_res);
    if (!tmp2) {
        r = _mk_empty(d->get_arity());
    }
    else {
        swap_out(tmp2, r, num_vars, vars);
    }
    m_filter_identical_cache.reset();
}

void imdd_manager::filter_identical_main3(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res) {
    for (unsigned i = 0; i+1 < num_vars; ++i) {
        imdd_ref tmp(*this);
        tmp = r;
        filter_identical_main3(tmp, r, vars[i], false, vars[i+1], false, memoize_res);
    }
}

void imdd_manager::filter_identical_main3(imdd * d, imdd_ref& r, unsigned v1, bool del1, unsigned v2, bool del2, bool memoize_res) {
    r = filter_identical_loop3(d, v1, del1, v2, del2, memoize_res);
    if (r == 0) {
        r = _mk_empty(d->get_arity()-del1-del2);
    }
    m_filter_identical_cache.reset();
}

imdd* imdd_manager::filter_identical_loop3(imdd * d, unsigned v1, bool del1, unsigned v2, bool del2, bool memoize_res) {
    imdd* r;
    if (m_filter_identical_cache.find(d, r)) {
        return r;
    }
    if (v1 == 0) {
        return filter_identical_mk_nodes(d, v2, del1, del2, memoize_res);
    }
    
    r = _mk_empty(d->get_arity()-del1-del2);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);
    bool children_memoized = true;

    for (; it != end; ++it) {
        imdd* curr_child = it->val();
        imdd* new_child = filter_identical_loop3(curr_child, v1-1, del1, v2-1, del2, memoize_res);
        if (!new_child) {
            continue;
        }
        if (new_child->empty()) {
            delete_imdd(new_child);
            continue;
        }
        if (!new_child->is_memoized()) {
            children_memoized = false;
        }
        push_back(it->begin_key(), it->end_key(), new_child);
    }
    if (r->empty()) {
        delete_imdd(r);
        r = 0;
    }
    m_filter_identical_cache.insert(d, r);
    r = memoize_new_imdd_if(r && memoize_res && children_memoized, r);
    return r;
}

void imdd_manager::merge_intervals(svector<interval>& dst, svector<interval> const& src) {
    svector<interval>& tmp = m_i_nodes_tmp;
    tmp.reset();
    // invariant: intervals are sorted.
    for (unsigned i = 0, j = 0; i < src.size() || j < dst.size();) {
        SASSERT(!(i + 1 < src.size()) || src[i].m_hi < src[i+1].m_lo);
        SASSERT(!(i + 1 < dst.size()) || dst[i].m_hi < dst[i+1].m_lo);
        SASSERT(!(i < src.size()) || src[i].m_lo <= src[i].m_hi);
        SASSERT(!(i < dst.size()) || dst[i].m_lo <= dst[i].m_hi);
        if (i < src.size() && j < dst.size()) {
            if (src[i].m_lo == dst[j].m_lo) {
                tmp.push_back(src[i]);
                ++i; 
                ++j;
            }
            else if (src[i].m_lo < dst[j].m_lo) {
                tmp.push_back(src[i]);
                ++i;
            }
            else {
                tmp.push_back(dst[j]);
                ++j;
            }
        }
        else if (i < src.size()) {
            tmp.push_back(src[i]);
            ++i;
        }
        else {
            tmp.push_back(dst[j]);
            ++j;
        }
    }
    dst.reset();
    dst.append(tmp);
}

/**
 * Propagate intervals down: what intervals can reach which nodes.
 */
imdd* imdd_manager::filter_identical_mk_nodes(imdd* d, unsigned v, bool del1, bool del2, bool memoize_res) {
    SASSERT(v > 0);

    TRACE("imdd", display_ll(tout << "v: " << v << "\n", d););

    //
    // (0)
    // Create map d |-> [I] from nodes to ordered set of disjoint intervals that visit the node.
    // 
    // For each level up to 'v' create a list of nodes visited
    // insert to a map the set of intervals that visit the node.
    // 
    m_nodes.reset();
    filter_id_map& nodes = m_nodes;
    imdd* d1, *d2, *d3;
    vector<ptr_vector<imdd> > levels;
    levels.push_back(ptr_vector<imdd>());
    
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();  
    imdd* curr_child;
    for (; it != end; ++it) {
        curr_child = it->val();
        svector<interval>& iv = nodes.init(curr_child);
        if (iv.empty()) {
            levels.back().push_back(curr_child);
        }
        iv.push_back(interval(it->begin_key(), it->end_key()));        
    }

    for (unsigned j = 0; j+1 < v; ++j) {
        levels.push_back(ptr_vector<imdd>());        
        for (unsigned i = 0; i < levels[j].size(); ++i) {
            d1 = levels[j][i];
            svector<interval>& i_nodes = nodes.init(d1);
            it  = d1->begin_children();
            end = d1->end_children();
            for(; it != end; ++it) {
                imdd* curr_child = it->val();
                svector<interval>& i_nodes2 = nodes.init(curr_child);
                if (i_nodes2.empty()) {
                    levels[j+1].push_back(curr_child);
                    i_nodes2.append(i_nodes);
                }
                else {
                    merge_intervals(i_nodes2, i_nodes);
                }
            }
        }
    }

    TRACE("imdd",
          for (unsigned i = 0; i < levels.size(); ++i) {
              tout << "Level: " << i << "\n";
              for (unsigned j = 0; j < levels[i].size(); ++j) {
                  tout << levels[i][j]->get_id() << " ";
                  svector<interval> const& i_nodes = nodes.init(levels[i][j]);
                  for (unsigned k = 0; k < i_nodes.size(); ++k) {
                      tout << i_nodes[k].m_lo << ":" << i_nodes[k].m_hi << " ";
                  }
                  tout << "\n";
              }
          }
          );


    //
    // (1)
    // Intersect with children:
    // - d [l1:h1:ch1][l2:h2:ch2][...]
    //   => produce_units:   d |-> [uI1 |-> d'[uI1:ch1], uI2 |-> d''[uI2:ch1], ...] // unit intervals
    //   => del2:            d |-> [I |-> union of ch1, ch2, .. under intersection]
    //   => del1 & !del2:    d |-> [I |-> d'[I:ch]] // intersections of intervals.
    //
    
    m_nodes_dd.reset();
    filter_idd_map& nodes_dd = m_nodes_dd;
    SASSERT(levels.size() == v);
    for (unsigned i = 0; i < levels[v-1].size(); ++i) {
        d1 = levels[v-1][i];
        svector<interval> const & i_nodes = nodes.init(d1);
        it  = d1->begin_children();
        end = d1->end_children();
        unsigned j = 0;
        svector<interval_dd>& i_nodes_dd = nodes_dd.init(d1);
        while (it != end && j < i_nodes.size()) {
            unsigned lo1 = it->begin_key();
            unsigned hi1 = it->end_key();
            unsigned lo2 = i_nodes[j].m_lo;
            unsigned hi2 = i_nodes[j].m_hi;
            if (hi2 < lo1) {
                ++j;
            }
            else if (hi1 < lo2) {
                ++it;
            }
            // lo1 <= hi2 && lo2 <= hi1
            else {
                curr_child = it->val();
                unsigned lo = std::max(lo1, lo2);
                unsigned hi = std::min(hi1, hi2);
                SASSERT(lo <= hi);
               
                if (!del1 && !del2) {
                    for (unsigned k = lo; k <= hi; ++k) {
                        imdd* d2 = _mk_empty(d1->get_arity());
                        add_child(d2, k, k, curr_child);
                        i_nodes_dd.push_back(interval_dd(k, k, d2)); 
                    }
                }
                else if (del2) {
                    i_nodes_dd.push_back(interval_dd(lo, hi, curr_child)); // retrofill after loop.
                }
                else {
                    imdd* d2 = _mk_empty(d1->get_arity());
                    add_child(d2, lo, hi, curr_child);
                    i_nodes_dd.push_back(interval_dd(lo, hi, d2));                     
                }
                if (hi2 <= hi) {
                    ++j;
                }
                if (hi1 <= hi) {
                    ++it;
                }
            }
        }
        // take union of accumulated children.
        // retrofill union inside list.
        if (del2) {
            d2 = 0;
            for (unsigned k = 0; k < i_nodes_dd.size(); ++k) {
                d3 = i_nodes_dd[k].m_dd;
                if (!d2) {
                    d2 = d3;
                }
                else {
                    d2 = mk_union_core(d2, d3, true, memoize_res);
                }
            }
            for (unsigned k = 0; k < i_nodes_dd.size(); ++k) {
                i_nodes_dd[k].m_dd = d2;
            }
        }
    }    

    TRACE("imdd", print_filter_idd(tout, nodes_dd););  

    //
    // (2)
    // Move up: 
    //    d1    |-> [I1]               // intervals visiting d1
    //    d1    |-> [lo:hi:child]      // children of d1
    //    child |-> [I2 |-> child']    // current decomposition
    //  result:
    //    d3 = d1' |-> [lo:hi:child']
    //    d1 |-> [I3 |-> d3] for I3 in merge of [I1] and [I2]
    // 
    //  The merge is defined as the intersection of intervals that reside in I1 and
    //  the fractions in I2. They are decomposed so that all intervals are covered.
    //  By construction I2 are contained in I1, 
    //  but they may be overlapping among different I2. 
    //  

    for (unsigned i = v-1; i > 0; ) {
        --i;
        for (unsigned j = 0; j < levels[i].size(); ++j) {
            d1 = levels[i][j];
            m_i_nodes_dd.reset();
            svector<interval> i_nodes = nodes.init(d1);
            svector<interval_dd>& i_nodes_dd = nodes_dd.init(d1);
            it  = d1->begin_children();
            end = d1->end_children();
            unsigned num_children = 0;
            for( ; it != end; ++it, ++num_children);

            m_offsets.reset();
            unsigned_vector& offsets = m_offsets;
            offsets.resize(num_children);
            it  = d1->begin_children();
            for( ; it != end; ++it) {
                curr_child = it->val();
                refine_intervals(i_nodes, nodes_dd.init(curr_child));
            }            
            
            for (unsigned k = 0; k < i_nodes.size(); ++k) {
                interval const& intv = i_nodes[k];
                d3 = _mk_empty(d1->get_arity()-del2);
                it = d1->begin_children();
                for(unsigned child_id = 0; it != end; ++it, ++child_id) {
                    curr_child = it->val();
                    svector<interval_dd> const& ch_nodes_dd = nodes_dd.init(curr_child);
                    unsigned offset = offsets[child_id];
                    TRACE("imdd_verbose", tout << intv.m_lo << ":" << intv.m_hi << "\n";
                          for (unsigned l = offset; l < ch_nodes_dd.size(); ++l) {
                              tout << ch_nodes_dd[l].m_lo << ":" << ch_nodes_dd[l].m_hi << " " << ch_nodes_dd[l].m_dd->get_id() << " ";
                          }                    
                          tout << "\n";
                        );

                    unsigned hi, lo;
                    d2 = 0;
                    while (offset < ch_nodes_dd.size() && !d2) {
                        lo = ch_nodes_dd[offset].m_lo;
                        hi = ch_nodes_dd[offset].m_hi;
                        if (intv.m_hi < lo) {
                            break;
                        }
                        if (hi < intv.m_lo) {
                            ++offset;
                            continue;
                        }                        
                        SASSERT(lo <= intv.m_lo);
                        SASSERT(intv.m_hi <= hi);  
                        d2 = ch_nodes_dd[offset].m_dd;
                        if (intv.m_hi == hi) {
                            ++offset;
                        }
                    }
                    offsets[child_id] = offset;
                    if (d2) {                                                
                        add_child(d3, it->begin_key(), it->end_key(), d2);                        
                    }
                }
                if (d3->empty()) {
                    delete_imdd(d3);
                }
                else {
                    i_nodes_dd.push_back(interval_dd(intv.m_lo, intv.m_hi, d3));
                }
            }
            TRACE("imdd", tout << d1->get_id() << ": "; print_interval_dd(tout, i_nodes_dd););                           
            
        }
    }

    TRACE("imdd", print_filter_idd(tout, nodes_dd);); 

    //
    // (3)
    // Finalize:
    //    d     |-> [I1:child]        // children of d
    //    child |-> [I2 |-> child']   // current decomposition
    //  result:
    //    d' = union of child'        // if  del1
    //    d' |-> [I2:child']          // if !del1
    //

    
    it  = d->begin_children();
    end = d->end_children();
    d1  = _mk_empty(d->get_arity()-del1-del2);
    m_i_nodes_dd.reset();
    m_i_nodes_tmp.reset();
    svector<interval_dd>& i_nodes_dd = m_i_nodes_dd;
    svector<interval_dd>& i_nodes_tmp = m_i_nodes_dd_tmp;
    for (; it != end; ++it) {
        curr_child = it->val();
        i_nodes_tmp.reset();
        svector<interval_dd> const& i_nodes_dd1 = nodes_dd.init(curr_child);
        for (unsigned i = 0, j = 0; i < i_nodes_dd.size() || j < i_nodes_dd1.size(); ) {
            if (i < i_nodes_dd.size() && j < i_nodes_dd1.size()) {
                interval_dd const& iv1 = i_nodes_dd[i];
                interval_dd const& iv2 = i_nodes_dd1[j];
                if (iv1.m_lo == iv2.m_lo) {
                    SASSERT(iv1.m_hi == iv2.m_hi);
                    SASSERT(iv1.m_dd == iv2.m_dd);
                    i_nodes_tmp.push_back(iv1);
                    ++i; 
                    ++j;
                }
                else if (iv1.m_lo < iv2.m_lo) {
                    SASSERT(iv1.m_hi < iv2.m_lo);
                    i_nodes_tmp.push_back(iv1);
                    ++i;
                }
                else {
                    SASSERT(iv2.m_hi < iv1.m_lo);
                    i_nodes_tmp.push_back(iv2);
                    ++j;
                }
            }
            else if (i < i_nodes_dd.size()) {
                i_nodes_tmp.push_back(i_nodes_dd[i]);
                ++i;
            }
            else if (j < i_nodes_dd1.size()) {
                i_nodes_tmp.push_back(i_nodes_dd1[j]);
                ++j;
            }
        }
        i_nodes_dd.reset();
        i_nodes_dd.append(i_nodes_tmp);
    }  

    for (unsigned i = 0; i < i_nodes_dd.size(); ++i) {
        imdd* ch = i_nodes_dd[i].m_dd;
        unsigned lo = i_nodes_dd[i].m_lo;
        unsigned hi = i_nodes_dd[i].m_hi;
        if (del1) {
            d1 = mk_union_core(d1, ch, true, memoize_res);
        }
        else {
            add_child(d1, lo, hi, ch);
        }
    }

    TRACE("imdd", display_ll(tout, d1););

    return d1;
}


void imdd_manager::print_interval_dd(std::ostream& out, svector<interval_dd> const& m) {
    for (unsigned i = 0; i < m.size(); ++i) {
        out << m[i].m_lo << ":" << m[i].m_hi << " " << m[i].m_dd->get_id() << " ";
    }
    out << "\n";   
}

void imdd_manager::print_filter_idd(std::ostream& out, filter_idd_map const& m) {
    filter_idd_map::iterator it = m.begin(), end = m.end();
    for (unsigned i = 0; it != end; ++it, ++i) {
        out << i << ": ";
        print_interval_dd(out, *it);
    }
}

/**
   \brief partition intervals of i_nodes by sub-intervals that are used in i_nodes_dd.
   Assumption:
   - All values covered in i_nodes_dd are present in i_nodes.
*/

void imdd_manager::refine_intervals(svector<interval>& i_nodes, svector<interval_dd> const& i_nodes_dd) {
    m_i_nodes.reset();
    svector<interval>& result = m_i_nodes;
    unsigned sz1 = i_nodes.size();
    unsigned sz2 = i_nodes_dd.size();
    for (unsigned i = 0, j = 0; i < sz1; ++i) {
        interval& iv = i_nodes[i];
        result.push_back(iv);
        unsigned lo = iv.m_lo;
        unsigned hi = iv.m_hi;
        for (; j < sz2; ++j) {
            unsigned lo1 = i_nodes_dd[j].m_lo;
            unsigned hi1 = i_nodes_dd[j].m_hi;
            SASSERT(lo <= hi);
            SASSERT(lo1 <= hi1);
            if (hi < lo1) {
                break;
            }            
            if (lo < lo1) {
                result.back().m_hi = lo1-1;
                result.push_back(interval(lo1, hi));
                lo = lo1;
            }
            SASSERT(lo1 <= lo);
            if (lo > hi1) {
                continue;
            }
            if (hi1 < hi) {
                result.back().m_hi = hi1;
                result.push_back(interval(hi1+1, hi)); 
                lo = hi1+1;
            }
        }
    }
    i_nodes.reset();
    i_nodes.append(result);
}



void imdd_manager::mk_project_core(imdd * d, imdd_ref & r, unsigned var, unsigned num_found, bool memoize_res) {
    unsigned arity = d->get_arity();
    bool _is_proj_var = is_proj_var(var);
    
    if (_is_proj_var && arity == (m_proj_num_vars - num_found)) {
        r = 0; // 0 here means the unit element (aka the 0-tuple).
        return;
    }

    imdd * _r = 0;
    if (is_cached(m_proj_cache, d, _r)) {
        r = _r;
        return;
    }
    
    bool new_children_memoized = true;
    if (_is_proj_var) {
        SASSERT(d != 0);
        SASSERT(d->get_arity() > 1);
        unsigned new_var = var + 1;
        unsigned new_num_found = num_found + 1;
        bool     found_all     = new_num_found == m_proj_num_vars;
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        imdd_ref tmp_r(*this);
        CTRACE("imdd", it == end, display_ll(tout, d););
        SASSERT(it != end);        
        for (; it != end; ++it) {
            imdd_ref new_child(*this);
            if (found_all)
                new_child = it->val();
            else
                mk_project_core(it->val(), new_child, new_var, new_num_found, memoize_res);
     
            if (tmp_r == 0)
                tmp_r = new_child;
            else
                mk_union_core(tmp_r, new_child, tmp_r, memoize_res);
            SASSERT(tmp_r != 0);
        }
        SASSERT(tmp_r != 0);
        SASSERT(tmp_r->get_arity() == d->get_arity() - (m_proj_num_vars - num_found));
        r = tmp_r;
    }
    else {
        SASSERT(num_found < m_proj_num_vars);
        unsigned new_var = var+1;
        _r = _mk_empty(arity - (m_proj_num_vars - num_found));
        imdd_children::push_back_proc push_back(m_sl_manager, _r->m_children);
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        SASSERT(it != end);
        for (; it != end; ++it) {
            imdd * curr_child = it->val();
            imdd_ref new_child(*this);
            mk_project_core(curr_child, new_child, new_var, num_found, memoize_res);
            push_back(it->begin_key(), it->end_key(), new_child);
            if (new_child != 0 && !new_child->is_memoized())
                new_children_memoized = false;
        }
        SASSERT(!_r->empty());
        _r = memoize_new_imdd_if(memoize_res && new_children_memoized, _r);
        r  = _r;
    }
    cache_result(m_proj_cache, d, r);
}

void imdd_manager::mk_project_dupdt_core(imdd_ref & d, unsigned var, unsigned num_found, bool memoize_res) {
    unsigned arity = d->get_arity();
    bool _is_proj_var = is_proj_var(var);

    if (_is_proj_var && arity == (m_proj_num_vars - num_found)) {
        d = 0; // 0 here means the unit element (aka the 0-tuple).
        return;
    }

    if (!destructive_update_at(true, d)) {
        mk_project_core(d, d, var, num_found, memoize_res);
        return;
    }

    if (_is_proj_var) {
        SASSERT(d != 0);
        SASSERT(d->get_arity() > 1);
        unsigned new_var = var + 1;
        unsigned new_num_found = num_found + 1;
        bool     found_all     = new_num_found == m_proj_num_vars;
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        imdd_ref r(*this);
        for (; it != end; ++it) {
            imdd_ref new_child(*this);
            it.take_curr_ownership(m_sl_manager, new_child);
            if (!found_all) {
                mk_project_dupdt_core(new_child, new_var, new_num_found, memoize_res);
            }
            if (r == 0)
                r = new_child;
            else
                mk_union_core_dupdt(r, new_child, memoize_res);
        }
        // we traverse the children of d, and decrement the reference counter of each one of them.
        d->m_children.reset_no_decref(m_sl_manager);
        d = r;
        SASSERT(r != 0);
        SASSERT(r->get_arity() == d->get_arity() - (m_proj_num_vars - num_found)); 
    }
    else {
        SASSERT(!_is_proj_var);
        sbuffer<entry> to_insert;
        unsigned new_var = var+1;
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        for (; it != end; ++it) {
            imdd_ref new_child(*this);
            it.take_curr_ownership(m_sl_manager, new_child);
            mk_project_dupdt_core(new_child, new_var, num_found, memoize_res);
            if (new_child) 
                new_child->inc_ref(); // protect new child, since we will insert it into to_insert
            to_insert.push_back(entry(it->begin_key(), it->end_key(), new_child));            
        }
        SASSERT(!to_insert.empty());
        d->replace_children(m_sl_manager, to_insert);
    }
}

void imdd_manager::mk_project_init(unsigned num_vars, unsigned * vars) {
    m_proj_num_vars   = num_vars;
    m_proj_begin_vars = vars;
    m_proj_end_vars   = vars + num_vars;
    m_proj_cache.reset();
    reset_union_cache();
}

void imdd_manager::mk_project_dupdt(imdd_ref & d, unsigned num_vars, unsigned * vars, bool memoize_res) {
    if (num_vars == 0) {
        return;
    }
    unsigned arity = d->get_arity();
    SASSERT(num_vars < arity);
    if (d->empty()) {
        d = _mk_empty(arity - num_vars);
        return;
    }
    delay_dealloc delay(*this);
    mk_project_init(num_vars, vars);
    mk_project_dupdt_core(d, 0, 0, memoize_res);
}

void imdd_manager::mk_project(imdd * d, imdd_ref & r, unsigned num_vars, unsigned * vars, bool memoize_res) {
    if (num_vars == 0) {
        r = d;
        return;
    }
    unsigned arity = d->get_arity();
    SASSERT(num_vars < arity);
    if (d->empty()) {
        r = _mk_empty(arity - num_vars);
        return;
    }
    delay_dealloc delay(*this);
    mk_project_init(num_vars, vars);
    mk_project_core(d, r, 0, 0, memoize_res);

    STRACE("imdd_trace", tout << "mk_project(0x" << d << ", 0x" << r.get() << ", ";
           for (unsigned i = 0; i < num_vars; i++) tout << vars[i] << ", ";
           tout << memoize_res << ");\n";);
}

void imdd_manager::mk_join(
    imdd * d1, imdd * d2, imdd_ref & r, 
    unsigned_vector const& vars1, unsigned_vector const& vars2,
    bool memoize_res) {
    SASSERT(vars1.size() == vars2.size());
    imdd_ref tmp(*this);
    unsigned d1_arity = d1->get_arity();
    mk_product(d1, d2, tmp);
    for (unsigned i = 0; i < vars1.size(); ++i) {
        unsigned vars[2] = { vars1[i], vars2[i] + d1_arity };
        mk_filter_identical_dupdt(tmp, 2, vars);
    }    
    r = tmp; // memoize_new_imdd_if(memoize_res, tmp);
}

#if 0
void imdd_manager::mk_join_project(
    imdd * d1, imdd * d2, imdd_ref & r,
    unsigned_vector const& vars1, unsigned_vector const& vars2,
    unsigned_vector const& proj_vars, bool memoize_res) {
    SASSERT(vars1.size() == vars2.size());
    imdd_ref tmp(*this);
    unsigned d1_arity = d1->get_arity();
    mk_product(d1, d2, tmp);
    for (unsigned i = 0; i < vars1.size(); ++i) {
        unsigned vars[2] = { vars1[i], vars2[i] + d1_arity };
        mk_filter_identical(tmp, tmp, 2, vars);
    }    
    mk_project(tmp, tmp, proj_vars.size(), proj_vars.c_ptr());
    TRACE("dl",
          tout << "vars: ";
          for (unsigned i = 0; i < vars1.size(); ++i) tout << vars1[i] << ":" << vars2[i] << " ";
          tout << "\n";
          tout << "proj: ";
          for (unsigned i = 0; i < proj_vars.size(); ++i) tout << proj_vars[i] << " ";
          tout << "\n";
          tout << "arity: " << d1->get_arity() << " + " << d2->get_arity() << "\n";
          display_ll(tout << "d1\n", d1);
          display_ll(tout << "d2\n", d2);
          display_ll(tout << "result\n", tmp);
          tout << "\n";
          );

    r = tmp; // memoize_new_imdd_if(memoize_res, tmp);
}
#endif


void imdd_manager::mk_join_project(
    imdd * d1, imdd * d2, imdd_ref & r,
    unsigned_vector const& vars1, unsigned_vector const& vars2,
    unsigned_vector const& proj_vars, bool memoize_res) {
    SASSERT(vars1.size() == vars2.size());
    imdd_ref tmp(*this);
    mk_product(d1, d2, tmp);
    unsigned d1_arity = d1->get_arity();
    unsigned sz = tmp->get_arity();

    // set up schedule for join-project.
    unsigned_vector remap; 
    svector<bool> projected;
    unsigned_vector ref_count;
    for (unsigned i = 0; i < sz; ++i) {
        remap.push_back(i);        
    }
    projected.resize(sz, false);
    ref_count.resize(sz, 0);
    for (unsigned i = 0; i < proj_vars.size(); ++i) {
        projected[proj_vars[i]] = true;
    }
    for (unsigned i = 0; i < vars1.size(); ++i) {
        ref_count[vars1[i]]++;
        ref_count[vars2[i]+d1_arity]++;
    }

#define UPDATE_REMAP()                                        \
    for (unsigned i = 0, j = 0; i < sz; ++i) {  \
        remap[i] = j;                                         \
        if (!projected[i] || ref_count[i] > 0) {              \
            ++j;                                              \
        }                                                     \
    }                                                         \


    UPDATE_REMAP();
    // project unused variables:
    unsigned_vector proj2;
    for (unsigned i = 0; i < sz; ++i) {
        if (projected[i] && ref_count[i] == 0) {
            proj2.push_back(i);
        }
    }
    mk_project(tmp, tmp, proj2.size(), proj2.c_ptr());
   
    for (unsigned i = 0; i < vars1.size(); ++i) {
        unsigned idx1 = vars1[i];
        unsigned idx2 = vars2[i]+d1_arity;
        ref_count[idx1]--;
        ref_count[idx2]--;
        bool del1 = ref_count[idx1] == 0 && projected[idx1];
        bool del2 = ref_count[idx2] == 0 && projected[idx2];
        
        filter_identical_main3(tmp, tmp, remap[idx1], del1, remap[idx2], del2, memoize_res);
        if (del1 || del2) {
            UPDATE_REMAP();
        }
    }    
    TRACE("imdd",
          tout << "vars: ";
          for (unsigned i = 0; i < vars1.size(); ++i) tout << vars1[i] << ":" << vars2[i] << " ";
          tout << "\n";
          tout << "proj: ";
          for (unsigned i = 0; i < proj_vars.size(); ++i) tout << proj_vars[i] << " ";
          tout << "\n";
          tout << "arity: " << d1->get_arity() << " + " << d2->get_arity() << "\n";
          display_ll(tout << "d1\n", d1);
          display_ll(tout << "d2\n", d2);
          display_ll(tout << "result\n", tmp);
          tout << "\n";
          );

    r = tmp; // memoize_new_imdd_if(memoize_res, tmp);
}



imdd * imdd_manager::mk_swap_new_child(unsigned lower, unsigned upper, imdd * grandchild) {
    if (m_swap_new_child == 0) {
        m_swap_new_child = _mk_empty(grandchild == 0 ? 1 : grandchild->get_arity() + 1);
        add_child(m_swap_new_child, lower, upper, grandchild);
        if (grandchild && !grandchild->is_memoized())
            m_swap_granchildren_memoized = false;
        inc_ref(m_swap_new_child);
    }
    SASSERT(m_swap_new_child != 0);
    return m_swap_new_child;
}

void imdd_manager::mk_swap_acc1_dupdt(imdd_ref & d, unsigned lower, unsigned upper, imdd * grandchild, bool memoize_res) {
    SASSERT(d->get_ref_count() == 1);
    sbuffer<entry> to_insert;
    imdd_children::ext_iterator it;
    imdd_children::ext_iterator end; 
    d->m_children.move_geq(it, lower);
    while (it != end && lower <= upper) {
        imdd_children::entry const & curr_entry = *it;
        unsigned curr_entry_begin_key = curr_entry.begin_key();
        unsigned curr_entry_end_key   = curr_entry.end_key();
        imdd *   curr_entry_val       = curr_entry.val();
        bool     move_head            = true;
        if (upper < curr_entry_begin_key)
            break;
        if (lower < curr_entry_begin_key) {
            to_insert.push_back(entry(lower, curr_entry_begin_key - 1, grandchild));
            lower = curr_entry_begin_key;
        }
        SASSERT(lower >= curr_entry_begin_key);
        imdd * curr_grandchild = curr_entry_val;
        imdd_ref new_grandchild(*this);
        SASSERT((curr_grandchild == 0) == (grandchild == 0));
        if (curr_grandchild != 0) {
            bool cover = lower == curr_entry_begin_key && upper >= curr_entry_end_key;
            // If cover == true, then the curr_child is completely covered, and it is not needed anymore. 
            // So, we can perform a destructive update. 
            if (cover) {
                new_grandchild = curr_grandchild; // take over the ownership of curr_grandchild
                it.erase(m_sl_manager);
                move_head = false; // it.erase is effectively moving the head.
                mk_union_core_dupdt(new_grandchild, grandchild, memoize_res);
            }
            else {
                mk_union_core(curr_grandchild, grandchild, new_grandchild, memoize_res);
            }
            if (!new_grandchild->is_memoized())
                m_swap_granchildren_memoized = false;
            // protect new_grandchild, since it will be stored in to_insert.
            new_grandchild->inc_ref();
        }
        if (upper >= curr_entry_end_key) {
            to_insert.push_back(entry(lower, curr_entry_end_key, new_grandchild));
        }
        else {
            to_insert.push_back(entry(lower, upper, new_grandchild));
        }
        lower = curr_entry_end_key + 1;
        if (move_head)
            ++it;
    }
    svector<entry>::iterator it2  = to_insert.begin();
    svector<entry>::iterator end2 = to_insert.end();
    for (; it2 != end2; ++it2) {
        imdd_children::entry const & curr_entry = *it2;
        add_child(d, curr_entry.begin_key(), curr_entry.end_key(), curr_entry.val());
        if (curr_entry.val())
            curr_entry.val()->dec_ref(); // to_insert will be destroyed, so decrement ref.
    }
    if (lower <= upper) {
        add_child(d, lower, upper, grandchild);
    }
    TRACE("mk_swap_bug", tout << "after mk_swap_acc1_dupt\n" << mk_ll_pp(d, *this) << "\n";);
}

void imdd_manager::mk_swap_acc1(imdd * d, imdd_ref & r, unsigned lower, unsigned upper, imdd * grandchild, bool memoize_res) {
    copy(d, r);
    imdd_children::iterator it  = d->m_children.find_geq(lower);
    imdd_children::iterator end = d->end_children();
    for (; it != end && lower <= upper; ++it) {
        imdd_children::entry const & curr_entry = *it;
        if (upper < curr_entry.begin_key())
            break;
        if (lower < curr_entry.begin_key()) {
            SASSERT(lower <= curr_entry.begin_key() - 1);
            add_child(r, lower, curr_entry.begin_key() - 1, grandchild);
            lower = curr_entry.begin_key();
        }
        SASSERT(lower >= curr_entry.begin_key());
        imdd * curr_grandchild = curr_entry.val();
        SASSERT((curr_grandchild == 0) == (grandchild == 0));
        imdd_ref new_curr_grandchild(*this);
        mk_union_core(curr_grandchild, grandchild, new_curr_grandchild, memoize_res);
        if (new_curr_grandchild && !new_curr_grandchild->is_memoized())
            m_swap_granchildren_memoized = false;
        if (upper >= curr_entry.end_key()) {
            add_child(r, lower, curr_entry.end_key(), new_curr_grandchild);
        }
        else {
            SASSERT(upper < curr_entry.end_key());
            SASSERT(lower <= upper);
            add_child(r, lower, upper, new_curr_grandchild);
        }
        lower = curr_entry.end_key() + 1;
    }
    if (lower <= upper) {
        add_child(r, lower, upper, grandchild);
    }
    TRACE("mk_swap_bug", tout << "after mk_swap_acc1\n" << mk_ll_pp(r, *this) << "\n";);
}

/**
   \brief Auxiliary function for mk_swap_core
*/
void imdd_manager::mk_swap_acc2(imdd_ref & r, unsigned lower1, unsigned upper1, unsigned lower2, unsigned upper2, imdd * grandchild, bool memoize_res) {
    SASSERT((r->get_arity() == 2 && grandchild == 0) ||
            (r->get_arity() == grandchild->get_arity() + 2));
    SASSERT(r->get_ref_count() <= 1); // we perform destructive updates on r.
    SASSERT(!r->is_memoized());
    TRACE("mk_swap_bug", 
          tout << mk_ll_pp(r, *this) << "\n";
          tout << "adding\n[" << lower1 << ", " << upper1 << "] -> [" << lower2 << ", " << upper2 << "] ->\n";
          tout << mk_ll_pp(grandchild, *this) << "\n";);

    sbuffer<entry> to_insert;
    imdd_children::ext_iterator it;  
    imdd_children::ext_iterator end;
    r->m_children.move_geq(it, lower1);
    SASSERT(m_swap_new_child == 0);    
    
    while(it != end && lower1 <= upper1) {
        imdd_children::entry const & curr_entry = *it;
        unsigned curr_entry_begin_key = curr_entry.begin_key();
        unsigned curr_entry_end_key   = curr_entry.end_key();
        imdd *   curr_entry_val       = curr_entry.val();
        bool     move_head            = true;
        TRACE("mk_swap_bug", tout << lower1 << " " << upper1 << " " << curr_entry_begin_key << "\n";);
        if (upper1 < curr_entry_begin_key)
            break;
        if (lower1 < curr_entry_begin_key) {
            imdd * new_child = mk_swap_new_child(lower2, upper2, grandchild);            
            SASSERT(lower1 <= curr_entry_begin_key - 1);
            add_child(r, lower1, curr_entry_begin_key - 1, new_child);
            lower1 = curr_entry_begin_key;
        }
        SASSERT(lower1 >= curr_entry_begin_key);
        imdd * curr_child = curr_entry_val;
        SASSERT(curr_child != 0);
        SASSERT(!curr_child->is_memoized());
        imdd_ref new_curr_child(*this);
        bool destructive = curr_child->get_ref_count() == 1 && lower1 == curr_entry_begin_key && upper1 >= curr_entry_end_key;
        if (destructive) {
            new_curr_child = curr_child; // take over curr_child.
            it.erase(m_sl_manager);
            move_head = false; // it.erase is effectively moving the head.
            mk_swap_acc1_dupdt(new_curr_child, lower2, upper2, grandchild, memoize_res);
        }
        else {
            mk_swap_acc1(curr_child, new_curr_child, lower2, upper2, grandchild, memoize_res);
        }
        new_curr_child->inc_ref(); // it will be stored in to_insert
        if (upper1 >= curr_entry_end_key) {
            to_insert.push_back(entry(lower1, curr_entry_end_key, new_curr_child));
        }
        else {
            to_insert.push_back(entry(lower1, upper1, new_curr_child));
        }
        lower1 = curr_entry_end_key + 1;
        if (move_head)
            ++it;
    }
    svector<entry>::iterator it2  = to_insert.begin();
    svector<entry>::iterator end2 = to_insert.end();
    for (; it2 != end2; ++it2) {
        imdd_children::entry const & curr_entry = *it2;
        add_child(r, curr_entry.begin_key(), curr_entry.end_key(), curr_entry.val());
        SASSERT(curr_entry.val());
        curr_entry.val()->dec_ref(); // to_insert will be destroyed, so decrement ref.
    }
    if (lower1 <= upper1) {
        imdd * new_child = mk_swap_new_child(lower2, upper2, grandchild);            
        add_child(r, lower1, upper1, new_child);
    }
    if (m_swap_new_child != 0) {
        dec_ref(m_swap_new_child);
        m_swap_new_child = 0;
    }
    TRACE("mk_swap_bug", tout << "after mk_swap_acc2\n" << mk_ll_pp(r, *this) << "\n";);
}

/**
   \brief Memoize the given IMDD assuming all grandchildren of d are memoized.
*/
imdd * imdd_manager::mk_swap_memoize(imdd * d) {
    if (d->is_memoized())
        return d;
    bool children_memoized = true;
    imdd * new_d = _mk_empty(d->get_arity());
    imdd_children::push_back_proc push_back(m_sl_manager, new_d->m_children);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    for (; it != end; ++it) {
        imdd * child     = it->val();
        imdd * new_child = memoize(child);
        if (!new_child->is_memoized())
            children_memoized = false;
        push_back(it->begin_key(), it->end_key(), new_child);
    }
    
    if (children_memoized && is_simple_node(new_d)) {
        imdd * new_can_d = memoize(new_d);
        if (new_can_d != new_d) {
            SASSERT(new_d->get_ref_count() == 0);
            delete_imdd(new_d);
        }
        new_d = new_can_d;
    }
    return new_d;
}

/**
   \brief Swap the two top vars.
*/
void imdd_manager::mk_swap_top_vars(imdd * d, imdd_ref & r, bool memoize_res) {
    SASSERT(d->get_arity() >= 2);
    r = _mk_empty(d->get_arity());
    m_swap_granchildren_memoized = true;
    m_swap_new_child             = 0;
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    for (; it != end; ++it) {
        imdd * curr_child = it->val();
        SASSERT(curr_child != 0);
        SASSERT(m_swap_new_child == 0);
        imdd_children::iterator it2  = curr_child->begin_children();
        imdd_children::iterator end2 = curr_child->end_children();
        for (; it2 != end2; ++it2) {
            imdd * grandchild = it2->val();
            mk_swap_acc2(r, it2->begin_key(), it2->end_key(), it->begin_key(), it->end_key(), grandchild, memoize_res);
        }
        SASSERT(m_swap_new_child == 0);
    }

    if (memoize_res && m_swap_granchildren_memoized) {
        r = mk_swap_memoize(r);
    }
    TRACE("mk_swap_bug", tout << "result:\n" << mk_ll_pp(r, *this) << "\n";);
}

void imdd_manager::mk_swap_core(imdd * d, imdd_ref & r, unsigned vidx, bool memoize_res) {
    SASSERT(d);
    unsigned arity = d->get_arity();
    SASSERT(arity > 1);
    
    imdd * _r = 0;
    if (is_cached(m_swap_cache, d, _r)) {
        r = _r;
        return;
    }

    if (vidx == 0) {
        mk_swap_top_vars(d, r, memoize_res);
    }
    else {
        SASSERT(vidx > 0);
        bool new_children_memoized = true;
        unsigned new_vidx = vidx - 1;
        _r = _mk_empty(arity);
        imdd_children::push_back_proc push_back(m_sl_manager, _r->m_children);
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        SASSERT(it != end);
        for (; it != end; ++it) {
            imdd * curr_child = it->val();
            imdd_ref new_child(*this);
            mk_swap_core(curr_child, new_child, new_vidx, memoize_res);
            push_back(it->begin_key(), it->end_key(), new_child);
            if (new_child != 0 && !new_child->is_memoized())
                new_children_memoized = false;
        }
        SASSERT(!_r->empty());
        _r = memoize_new_imdd_if(memoize_res && new_children_memoized, _r);
        r  = _r;
    }
    cache_result(m_swap_cache, d, r);
}

void imdd_manager::mk_swap_dupdt_core(imdd_ref & d, unsigned vidx, bool memoize_res) {
    SASSERT(d);
    unsigned arity = d->get_arity();
    SASSERT(arity > 1);
    
    if (!destructive_update_at(true, d)) {
        mk_swap_core(d, d, vidx, memoize_res);
        return;
    }
    
    if (vidx == 0) {
        mk_swap_top_vars(d, d, memoize_res);
        return;
    }

    SASSERT(vidx > 0);
    sbuffer<entry> to_insert;
    unsigned new_vidx = vidx-1;
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    for (; it != end; ++it) {
        imdd_ref new_child(*this);
        it.take_curr_ownership(m_sl_manager, new_child);
        mk_swap_dupdt_core(new_child, new_vidx, memoize_res);
        new_child->inc_ref(); // protect new child, since we insert into to_insert
        to_insert.push_back(entry(it->begin_key(), it->end_key(), new_child));
    }
    SASSERT(!to_insert.empty());
    d->replace_children(m_sl_manager, to_insert);
}

void imdd_manager::mk_swap_dupdt(imdd_ref & d, unsigned vidx, bool memoize_res) {
    SASSERT(d);
    unsigned arity = d->get_arity();
    SASSERT(arity > 1);
    SASSERT(vidx < arity - 1);
    if (d->empty()) {
        return;
    }
    m_swap_cache.reset();
    reset_union_cache();
    delay_dealloc delay(*this);
    mk_swap_dupdt_core(d, vidx, memoize_res);
}

void imdd_manager::mk_swap(imdd * d, imdd_ref & r, unsigned vidx, bool memoize_res) {
    SASSERT(d);
    unsigned arity = d->get_arity();
    SASSERT(arity > 1);
    SASSERT(vidx < arity - 1);
    if (d->empty()) {
        r = d;
        return;
    }
    TRACE("mk_swap_bug", tout << "mk_swap: " << vidx << "\n"; display_ll(tout, d); );
    TRACE("mk_swap_bug2", tout << "mk_swap: " << vidx << "\n"; display_ll(tout, d); );
    m_swap_cache.reset();
    reset_union_cache();
    delay_dealloc delay(*this);
    mk_swap_core(d, r, vidx, memoize_res);
    TRACE("mk_swap_bug2", tout << "mk_swap result\n"; display_ll(tout, r); );
    STRACE("imdd_trace", tout << "mk_swap(0x" << d << ", 0x" << r.get() << ", " << vidx << ", " << memoize_res << ");\n";);
}

imdd_manager::iterator::iterator(imdd_manager const & m, imdd const * d) {
    if (d->empty()) {
        m_done = true;
        return;
    }
    m_done = false;
    unsigned arity = d->get_arity();
    m_iterators.resize(arity);
    m_element.resize(arity);
    begin_iterators(d, 0);
}

void imdd_manager::iterator::begin_iterators(imdd const * curr, unsigned start_idx) {
    for (unsigned i = start_idx; i < get_arity(); i++) {
        m_iterators[i] = curr->begin_children();
        imdd_children::iterator & it = m_iterators[i];
        SASSERT(!it.at_end());
        m_element[i] = it->begin_key();
        curr = it->val();
    }
}

imdd_manager::iterator & imdd_manager::iterator::operator++() {
    unsigned i = get_arity();
    while (i > 0) {
        --i;
        imdd_children::iterator & it = m_iterators[i];
        if (m_element[i] < it->end_key()) {
            m_element[i]++;
            begin_iterators(it->val(), i+1);
            return *this;
        }
        else {
            ++it;
            if (!it.at_end()) {
                m_element[i] = it->begin_key();
                begin_iterators(it->val(), i+1);
                return *this;
            }
        }
    }
    m_done = true; // at end...
    return *this;
}
        
bool imdd_manager::iterator::operator==(iterator const & it) const {
    if (m_done && it.m_done)
        return true;
    if (m_done || it.m_done)
        return false;
    if (m_element.size() != it.m_element.size())
        return false;
    unsigned sz = m_element.size();
    for (unsigned i = 0; i < sz; i++)
        if (m_element[i] != it.m_element[i])
            return false;
    return true;
}

bool imdd_manager::is_equal_core(imdd * d1, imdd * d2) {
    if (d1 == d2)
        return true;
    if (d1->is_memoized() && d2->is_memoized())
        return false;
    SASSERT(d1->get_arity() == d2->get_arity());
    SASSERT(!d1->empty());
    SASSERT(!d2->empty());
    bool shared = d1->is_shared() && d2->is_shared();
    bool r;
    if (shared && m_is_equal_cache.find(d1, d2, r))
        return r;

    if (d1->get_arity() == 1) {
        r = d1->m_children.is_equal(d2->m_children);
    }
    else {
        imdd_children::iterator it1  = d1->begin_children();
        imdd_children::iterator end1 = d1->end_children();
        imdd_children::iterator it2  = d2->begin_children();
        imdd_children::iterator end2 = d2->end_children();
        SASSERT(it1 != end1);
        SASSERT(it2 != end2);
        if (it1->begin_key() != it2->begin_key()) {
            r = false;
        }
        else {
            while (true) {
                if (it1 == end1) {
                    r = (it2 == end2);
                    break;
                }
                if (it2 == end2) {
                    r = (it1 == end1);
                    break;
                }
                SASSERT(it1->val() != 0 && it2->val() != 0);
                if (!is_equal_core(it1->val(), it2->val())) {
                    r = false;
                    break;
                }
                if (it1->end_key() < it2->end_key()) {
                    unsigned prev_end_key = it1->end_key();
                    ++it1;
                    if (it1 == end1 || it1->begin_key() != prev_end_key + 1) {
                        r = false;
                        break;
                    }
                }
                else if (it1->end_key() > it2->end_key()) {
                    unsigned prev_end_key = it2->end_key();
                    ++it2;
                    if (it2 == end2 || it2->begin_key() != prev_end_key + 1) {
                        r = false;
                        break;
                    }
                }
                else {
                    SASSERT(it1->end_key() == it2->end_key());
                    ++it1;
                    ++it2;
                }
            }
        }
    }
    if (shared)
        m_is_equal_cache.insert(d1, d2, r);
    return r;
}

bool imdd_manager::is_equal(imdd * d1, imdd * d2) {
    if (d1 == d2)
        return true;
    if (d1->is_memoized() && d2->is_memoized())
        return false;
    if (d1->get_arity() != d2->get_arity())
        return false;
    if (d1->empty() && d2->empty())
        return true;
    if (d1->empty() || d2->empty())
        return false;
    SASSERT(!d1->empty());
    SASSERT(!d2->empty());
    m_is_equal_cache.reset();
    return is_equal_core(d1, d2);
}

/**
   \brief Return true if the given imdd contains the tuple (values[0], ..., values[num-1])
*/
bool imdd_manager::contains(imdd * d, unsigned num, unsigned const * values) const {
    SASSERT(d->get_arity() == num);
    imdd * curr = d;
    for (unsigned i = 0; i < num; i++) {
        imdd * child; 
        if (!curr->m_children.find(values[i], child))
            return false;
        curr = child;
    }
    return true;
}

inline bool overlap(unsigned b1, unsigned e1, unsigned b2, unsigned e2) {
    // [b1, e1] [b2, e2]
    if (e1 < b2)
        return false;
    // [b2, e2] [b1, e1]
    if (e2 < b1)
        return false;
    return true;
}

bool imdd_manager::subsumes_core(imdd * d1, imdd * d2) {
   if (d1 == d2)
        return true;
    SASSERT(d1->get_arity() == d2->get_arity());
    SASSERT(!d1->empty());
    SASSERT(!d2->empty());
    bool shared = d1->is_shared() && d2->is_shared();
    bool r;
    if (shared && m_subsumes_cache.find(d1, d2, r))
        return r;

    imdd_children::iterator it1  = d1->begin_children();
    imdd_children::iterator end1 = d1->end_children();
    imdd_children::iterator it2  = d2->begin_children();
    imdd_children::iterator end2 = d2->end_children();
    SASSERT(it1 != end1);
    SASSERT(it2 != end2);
    if (it1->begin_key() > it2->begin_key()) {
        r = false;
        goto subsumes_end;
    }

    if (d1->get_arity() == 1) {
        // leaf case
        while(true) {
            SASSERT(it1 != end1);
            SASSERT(it2 != end2);
            it1.move_to(it2->begin_key());
            if (it1 == end1 ||
                it1->begin_key() > it2->begin_key() || // missed beginning of it2 curr entry
                it1->end_key() < it2->end_key() // missed end of it2 curr entry
                ) {
                r = false;
                goto subsumes_end;
            }
            SASSERT(it1->end_key() >= it2->end_key());
            ++it2; 
            if (it2 == end2) {
                r = true;
                goto subsumes_end;
            }
        }
    }
    else {
        // non-leaf case
        while (true) {
            SASSERT(it1 != end1);
            SASSERT(it2 != end2);
            SASSERT(it1->val() != 0);
            SASSERT(it2->val() != 0);
            it1.move_to(it2->begin_key());
            if (it1 == end1 ||
                it1->begin_key() > it2->begin_key() // missed beginning of it2 curr entry
                ) {
                r = false;
                goto subsumes_end;
            }
            // the beginning of it2 is inside it1
            SASSERT(it2->begin_key() >= it1->begin_key() && it2->begin_key() <= it1->end_key());
            //  it1:   [    ][  ][   ]
            //  it2       [        ]
            while (true) {
                SASSERT(it1 != end1);
                SASSERT(it2 != end2);
                // there is a overlap between the current entry in it1 and the current entry in it2
                SASSERT(overlap(it1->begin_key(), it1->end_key(),
                                it2->begin_key(), it2->end_key()));
                if (!subsumes_core(it1->val(), it2->val())) {
                    r = false;
                    goto subsumes_end;
                }
                if (it1->end_key() >= it2->end_key()) {
                    ++it2; // processed the whole entry in it2
                    break;
                }
                SASSERT(it1->end_key() < it2->end_key());
                unsigned prev_end_key = it1->end_key();
                ++it1;
                if (it1 == end1 || it1->begin_key() != prev_end_key + 1) {
                    r = false;
                    goto subsumes_end;
                }
            }
            if (it2 == end2) {
                r = true;
                goto subsumes_end;
            }
        }
    }
 subsumes_end:
    if (shared)
        m_subsumes_cache.insert(d1, d2, r);
    return r;
}
    
/**
   \brief Return true is d1 is a superset of d2, or equal to d2.
*/
bool imdd_manager::subsumes(imdd * d1, imdd * d2) {
    SASSERT(d1->get_arity() == d2->get_arity());
    if (d1 == d2)
        return true;
    if (d2->empty())
        return true;
    if (d1->empty()) {
        SASSERT(!d2->empty());
        return false;
    }
    SASSERT(!d1->empty());
    SASSERT(!d2->empty());
    m_subsumes_cache.reset();
    return subsumes_core(d1, d2);
}

void imdd_manager::remove_facts_dupdt(imdd_ref & d, unsigned num, unsigned const * lowers, unsigned const * uppers) {
    SASSERT(d->get_arity() == num);
    d = remove_facts_main(d, num, lowers, uppers, true, true);
}

void imdd_manager::remove_facts(imdd * d, imdd_ref & r, unsigned num, unsigned const * lowers, unsigned const * uppers) {
    SASSERT(d->get_arity() == num);
    r = remove_facts_main(d, num, lowers, uppers, false, true);
}

imdd * imdd_manager::remove_facts_main(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == num);
    delay_dealloc delay(*this);
    m_remove_facts_cache.reset();
    return remove_facts_core(d, num, lowers, uppers, destructive, memoize_res);
}

imdd * imdd_manager::remove_facts_core(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res) {
    SASSERT(d->get_arity() == num && num > 0);

    imdd * new_d = 0;
    unsigned b  = *lowers;
    unsigned e  = *uppers;
    sbuffer<entry> to_insert, to_remove;
    imdd_children::iterator it  = d->m_children.find_geq(b);
    imdd_children::iterator end = d->end_children();
    bool is_destructive = destructive_update_at(destructive, d);

    if (!is_destructive && is_cached(m_remove_facts_cache, d, new_d)) {
        return new_d;
    }

    if (num == 1) {
        new_d = remove_main(d, *lowers, *uppers, destructive, memoize_res);
        if (!is_destructive) {
            cache_result(m_remove_facts_cache, d, new_d);  
        }
        return new_d;
    }

    if (it == end || e < it->begin_key()) {
        if (!is_destructive) {
            cache_result(m_remove_facts_cache, d, d);
        }
        return d;
    }    

    if (!is_destructive) {
        new_d = copy_main(d); 
    }
    else {
        new_d = d;
    }
    for (; it != end && b <= e; ++it) {
        //
        // remove ([b:e]::rest), [b_key:e_key] * ch) = 
        //  { [b_key:e_key] * ch  }                      if e < b_key
        //  { [b_key:e_key] * ch' }                      if b <= b_key <= e_key <= e
        //  { [b_key:e]*ch' [e+1:e_key]*ch }             if b <= b_key <= e < e_key
        //  { [b_key:b-1]*ch [b:e]*ch', [e+1:e_key]*ch } if b_key < b <= e < e_key
        //  { [b_key:b-1]*ch [b:e_key]*ch' }             if b_key < b <= e_key <= e
        // where 
        //      ch' = remove(rest, ch)
        // assumption: remove_child retains the cases where ch is in the tree.
        //
        
        imdd_children::entry const & curr_entry = *it;
        unsigned b_key = curr_entry.begin_key();
        unsigned e_key = curr_entry.end_key();
        imdd* curr_child = curr_entry.val();
        imdd* new_curr_child = 0;
        
        if (e < b_key) {
            break;
        }

        new_curr_child = remove_facts_core(curr_child, num-1, lowers+1, uppers+1, destructive, memoize_res);
        
        if (new_curr_child == curr_child) {
            continue;
        }
        
        if (new_curr_child != 0) {
            if (b <= b_key && e_key <= e) {
                to_insert.push_back(entry(b_key, e_key, new_curr_child));
            }
            if (b <= b_key && e < e_key) {
                to_insert.push_back(entry(b_key, e, new_curr_child));
            }
            if (b_key < b && e < e_key) {
                to_insert.push_back(entry(b, e, new_curr_child));
            }
            if (b_key < b && e_key <= e) {
                to_insert.push_back(entry(b, e_key, new_curr_child));
            }                    
        }
        if (is_destructive) {
            to_remove.push_back(entry(b, e, 0));
        }
        else {
            remove_child(new_d, b, e);
        }
        b = e_key + 1;
    }
    for (unsigned i = 0; i < to_remove.size(); ++i) {
        remove_child(new_d, to_remove[i].begin_key(), to_remove[i].end_key());
    }                        
    for (unsigned i = 0; i < to_insert.size(); ++i) {
        add_child(new_d, to_insert[i].begin_key(), to_insert[i].end_key(), to_insert[i].val());
    }                        
    if (!is_destructive) {
        cache_result(m_remove_facts_cache, d, new_d);
    }
    return new_d;
}

void imdd_manager::display(std::ostream & out, imdd const * d, unsigned_vector & intervals, bool & first) const {
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    if (d->get_arity() == 1) {
        for (; it != end; ++it) {
            SASSERT(it->val() == 0);
            if (first) {
                first = false;
            }
            else {
                out << ",\n ";
            }
            out << "(";
            unsigned sz = intervals.size();
            for (unsigned i = 0; i < sz; i+=2) {
                out << "[" << intervals[i] << ", " << intervals[i+1] << "]";
                out << ", ";
            }
            out << "[" << it->begin_key() << ", " << it->end_key() << "])";
        }
    }
    else {
        for (; it != end; ++it) {
            intervals.push_back(it->begin_key());
            intervals.push_back(it->end_key());
            display(out, it->val(), intervals, first);
            intervals.pop_back();
            intervals.pop_back();
        }
    }
}

void imdd_manager::display(std::ostream & out, imdd const * d) const {
    unsigned_vector intervals;
    bool first = true;
    out << "{";
    display(out, d, intervals, first);
    out << "}";
}

struct display_ll_context {
    typedef map<imdd *, unsigned, ptr_hash<imdd>, default_eq<imdd*> > imdd2uint;
    std::ostream & m_out;
    unsigned       m_next_id;
    imdd2uint      m_map;
    display_ll_context(std::ostream & out):m_out(out), m_next_id(1) {}

    void display_tabs(unsigned num_tabs) {
        for (unsigned i = 0; i < num_tabs; i++)
            m_out << "    ";
    }

    void display_node(unsigned num_tabs, imdd const * d) {
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        if (it == end) {
            m_out << "{}";
            return;
        }
        if (d->get_arity() == 1) {
            // leaf
            m_out << "{";
            for (bool first = true; it != end; ++it) {
                if (first)
                    first = false;
                else
                    m_out << ", ";
                m_out << "[" << it->begin_key() << ", " << it->end_key() << "]";
            }
            m_out << "}";
        }
        else {
            m_out << "{\n";
            display_tabs(num_tabs);
            while (it != end) {
                m_out << " [" << it->begin_key() << ", " << it->end_key() << "] -> ";
                display(num_tabs+1, it->val());
                ++it;
                if (it != end) {
                    m_out << "\n";
                    display_tabs(num_tabs);
                }
                else {
                    m_out << "}";
                }
            }
        }
        m_out << (d->is_memoized() ? "*" : "") << "$" << d->memory();
    }

    void display(unsigned num_tabs, imdd const * d) {
        if (d == 0) {
            m_out << "<NULL>";
            return;
        }
        unsigned id;
        if (m_map.find(const_cast<imdd*>(d), id)) {
            m_out << "#" << id;
        }
        else if (d->is_shared()) {
            id = m_next_id;
            m_next_id++;
            m_map.insert(const_cast<imdd*>(d), id);
            m_out << "#" << id << ":";
            display_node(num_tabs, d);
        }
        else {
            display_node(num_tabs, d);
        }
    }
};

void imdd_manager::display_ll(std::ostream & out, imdd const * d) const {
    display_ll_context ctx(out);
    ctx.display(0, d);
    out << "\n";
}

struct addone_proc {
    unsigned m_r;
    addone_proc():m_r(0) {}
    void operator()(imdd * d) { m_r++; }
};

/**
   \brief Return the number of nodes in an IMDD.
   This is *not* a constant time operation. 
   It is linear on the size of the IMDD
*/
unsigned imdd_manager::get_num_nodes(imdd const * d) const {
    addone_proc p;
    for_each(const_cast<imdd*>(d), p);
    return p.m_r;
}

struct addmem_proc {
    unsigned m_r;
    addmem_proc():m_r(0) {}
    void operator()(imdd * d) { m_r += d->memory(); }
};

/**
   \brief Return the amount of memory consumed by the given IMDD.
*/
unsigned imdd_manager::memory(imdd const * d) const {
    addmem_proc p;
    for_each(const_cast<imdd*>(d), p);
    return p.m_r;
}

/**
   \brief Return number of rows the given IMDD represents.
*/
size_t imdd_manager::get_num_rows(imdd const* root) const {
    obj_map<imdd const, size_t> counts;
    ptr_vector<imdd const> todo;
    todo.push_back(root);
    while (!todo.empty()) {        
        imdd const* d = todo.back();
        if (counts.contains(d)) {
            todo.pop_back();
            continue;
        }
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        bool all_valid = true;
        size_t count = 0, c;
        for (; it != end; ++it) {
            imdd const* ch = it->val();
            if (!ch) {
                count += (it->end_key()-it->begin_key()+1);
            }
            else if (counts.find(ch, c)) {
                count += c*(it->end_key()-it->begin_key()+1);
            }
            else {
                all_valid = false;
                todo.push_back(ch);
            }
        }        
        if (all_valid) {
            todo.pop_back();
            counts.insert(d, count);
        }
    }
    return counts.find(root);
}

imdd * imdd_manager::add_bounded_var_core(imdd * d, unsigned before_vidx, unsigned lower, unsigned upper, bool destructive, bool memoize_res) {
    if (d == 0) {
        SASSERT(before_vidx == 0);
        imdd * r = _mk_empty(1);
        add_child(r, lower, upper, 0);
        r = memoize_new_imdd_if(memoize_res, r);
        return r;
    }
    imdd * r = 0;
    if (is_cached(m_add_bounded_var_cache, d, r))
        return r;
    if (before_vidx == 0) {
        imdd * r = _mk_empty(d->get_arity() + 1);
        add_child(r, lower, upper, d);
        r = memoize_new_imdd_if(d->is_memoized() && memoize_res, r);
        return r;
    }

    if (destructive_update_at(destructive, d)) {
        sbuffer<entry> to_insert;
        imdd_children::iterator it  = d->begin_children();
        imdd_children::iterator end = d->end_children();
        for (; it != end; ++it) {
            imdd * curr_child = it->val();
            imdd * new_child  = add_bounded_var_core(curr_child, before_vidx-1, lower, upper, true, memoize_res);
            new_child->inc_ref(); // we will be resetting d->m_children later.
            to_insert.push_back(entry(it->begin_key(), it->end_key(), new_child));
        }
        SASSERT(!to_insert.empty());
        d->replace_children(m_sl_manager, to_insert);
        return d;
    }

    bool new_children_memoized = true;
    r = _mk_empty(d->get_arity() + 1);
    imdd_children::push_back_proc push_back(m_sl_manager, r->m_children);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    SASSERT(it != end);
    for (; it != end; ++it) {
        imdd * curr_child = it->val();
        imdd * new_child  = add_bounded_var_core(curr_child, before_vidx-1, lower, upper, false, memoize_res);
        push_back(it->begin_key(), it->end_key(), new_child);
        if (!new_child->is_memoized())
            new_children_memoized = false;
    }
    r = memoize_new_imdd_if(r && memoize_res && new_children_memoized, r);
    cache_result(m_add_bounded_var_cache, d, r);
    return r;
}

/**
   \brief Add a variable (bounded by lower and upper) before the variable before_var.

   That is, for each tuple (v_1, ..., v_n) in the IMDD \c d, the resultant IMDD contains the
   tuples
   
   (v_1, ..., v_{after_vidx}, lower,   ..., v_n)
   (v_1, ..., v_{after_vidx}, lower+1, ..., v_n)
   ...
   (v_1, ..., v_{after_vidx}, upper,   ..., v_n)

   This function is mainly used to implement mk_filter.

   \pre after_vidx < d->get_arity()
*/
imdd * imdd_manager::add_bounded_var_main(imdd * d, unsigned before_vidx, unsigned lower, unsigned upper, bool destructive, bool memoize_res) {
    SASSERT(before_vidx <= d->get_arity());
    if (d->empty())
        return d;
    m_add_bounded_var_cache.reset();
    delay_dealloc delay(*this);
    imdd * r = add_bounded_var_core(d, before_vidx, lower, upper, destructive, memoize_res);
    return r;
}

filter_cache_entry * imdd_manager::mk_filter_cache_entry(imdd * d, unsigned ctx_sz, unsigned * ctx, imdd * r) {
    void * mem = m_filter_entries.allocate(filter_cache_entry::get_obj_size(ctx_sz));
    return new (mem) filter_cache_entry(d, r, ctx_sz, ctx);
}

imdd * imdd_manager::is_mk_filter_cached(imdd * d, unsigned ctx_sz, unsigned * ctx) {
    if (!d->is_shared())
        return 0;
    m_filter_entries.push_scope();
    filter_cache_entry * tmp_entry = mk_filter_cache_entry(d, ctx_sz, ctx, 0);
    filter_cache_entry * e = 0;
    bool r = m_filter_cache.find(tmp_entry, e);
    m_filter_entries.pop_scope();
    if (!r || e->m_r->is_dead())
        return 0;
    return e->m_r;
}

void imdd_manager::cache_mk_filter(imdd * d, unsigned ctx_sz, unsigned * ctx, imdd * r) {
    if (d->is_shared()) {
        filter_cache_entry * new_entry = mk_filter_cache_entry(d, ctx_sz, ctx, r);
        m_filter_cache.insert(new_entry);
    }
}

void imdd_manager::init_mk_filter(unsigned arity, unsigned num_vars, unsigned * vars) {
    m_filter_cache.reset();
    m_filter_entries.reset();
    m_filter_context.reset();
    m_filter_num_vars   = num_vars;
    m_filter_begin_vars = vars;
    m_filter_end_vars   = vars + num_vars;
    DEBUG_CODE({
        for (unsigned i = 0; i < num_vars; i++) {
            SASSERT(vars[i] < arity);
        }
    });
}

template<typename FilterProc>
void imdd_manager::mk_filter_dupdt_core(imdd_ref & d, unsigned vidx, unsigned num_found, FilterProc & proc, bool memoize_res) {
    SASSERT(!d->empty());

    if (!destructive_update_at(true, d)) {
        mk_filter_core(d, d, vidx, num_found, proc, memoize_res);
        return;
    }

    bool _is_filter_var = is_filter_var(vidx);
    if (_is_filter_var)
        num_found++;
    unsigned new_vidx   = vidx+1;
    imdd_ref new_r(*this);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    SASSERT(it != end);
    for (; it != end; ++it) {
        imdd_ref new_child(*this);
        it.take_curr_ownership(m_sl_manager, new_child); // take ownership of the current child.
        if (!_is_filter_var) {
            mk_filter_dupdt_core(new_child, new_vidx, num_found, proc, memoize_res);
            add_bounded_var_dupdt(new_child, num_found, it->begin_key(), it->end_key(), memoize_res);
            if (new_r == 0)
                new_r = new_child;
            else
                mk_union_core_dupdt(new_r, new_child, memoize_res);
        }
        else {
            m_filter_context.push_back(it->begin_key());
            m_filter_context.push_back(it->end_key());
            if (num_found < m_filter_num_vars) {
                mk_filter_dupdt_core(new_child, new_vidx, num_found, proc, memoize_res);
            }
            else {
                proc(m_filter_context.c_ptr(), new_child, new_child, memoize_res);
            }
            m_filter_context.pop_back();
            m_filter_context.pop_back();
            if (new_r == 0)
                new_r = new_child;
            else
                mk_union_core_dupdt(new_r, new_child, memoize_res); 
        }
    }
    d->m_children.reset(m_sl_manager);
    d = new_r;
}

template<typename FilterProc>
void imdd_manager::mk_filter_core(imdd * d, imdd_ref & r, unsigned vidx, unsigned num_found, FilterProc & proc, bool memoize_res) {
    SASSERT(!d->empty());
    
    imdd * _r = is_mk_filter_cached(d, m_filter_context.size(), m_filter_context.c_ptr());
    if (_r) {
        r = _r;
        return;
    }
    
    bool _is_filter_var = is_filter_var(vidx);
    if (_is_filter_var)
        num_found++;
    unsigned new_vidx   = vidx+1;
    imdd_ref new_r(*this);
    imdd_children::iterator it  = d->begin_children();
    imdd_children::iterator end = d->end_children();
    SASSERT(it != end);
    for (; it != end; ++it) {
        imdd * curr_child = it->val();
        imdd_ref new_child(*this);
        if (!_is_filter_var) {
            mk_filter_core(curr_child, new_child, new_vidx, num_found, proc, memoize_res);
            imdd_ref tmp(*this);
            add_bounded_var(new_child, tmp, num_found, it->begin_key(), it->end_key(), memoize_res);
            if (new_r == 0)
                new_r = tmp;
            else
                mk_union_core(new_r, tmp, new_r, memoize_res);
        }
        else {
            m_filter_context.push_back(it->begin_key());
            m_filter_context.push_back(it->end_key());
            if (num_found < m_filter_num_vars) {
                mk_filter_core(curr_child, new_child, new_vidx, num_found, proc, memoize_res);
            }
            else {
                proc(m_filter_context.c_ptr(), curr_child, new_child, memoize_res);
            }
            m_filter_context.pop_back();
            m_filter_context.pop_back();
            if (new_r == 0)
                new_r = new_child;
            else
                mk_union_core(new_r, new_child, new_r, memoize_res); 
        }
    }
    r = new_r;
    cache_mk_filter(d, m_filter_context.size(), m_filter_context.c_ptr(), r);
}

template<typename FilterProc>
void imdd_manager::mk_filter_dupdt(imdd_ref & d, unsigned num_vars, unsigned * vars, FilterProc & proc, bool memoize_res) {
    if (d->empty())
        return;
    unsigned arity = d->get_arity();
    init_mk_filter(arity, num_vars, vars);
    mk_filter_dupdt_core(d, 0, 0, proc, memoize_res);
    if (d == 0)
        d = _mk_empty(arity);
}

template<typename FilterProc>
void imdd_manager::mk_filter(imdd * d, imdd_ref & r, unsigned num_vars, unsigned * vars, FilterProc & proc, bool memoize_res) {
    if (d->empty()) {
        r = d;
        return;
    }
    unsigned arity = d->get_arity();
    init_mk_filter(arity, num_vars, vars);
    mk_filter_core(d, r, 0, 0, proc, memoize_res);
    if (r == 0)
        r = _mk_empty(arity);
}

imdd * imdd_manager::mk_distinct_imdd(unsigned l1, unsigned u1, unsigned l2, unsigned u2, imdd * d, bool memoize_res) {
    unsigned d_arity;
    if (d == 0) {
        d_arity = 0;
    }
    else {
        d_arity     = d->get_arity();
        memoize_res = memoize_res && d->is_memoized();
    }
    imdd * r = _mk_empty(d_arity + 2);
    imdd_children::push_back_proc  push_back(m_sl_manager, r->m_children);
    
    TRACE("mk_distinct_imdd", tout << "STARTING: " << l1 << " " << u1 << " " << l2 << " " << u2 << "\n";);

#define ADD_ENTRY(L1, U1, L2, U2) {                                                                     \
    TRACE("mk_distinct_imdd", tout << "[" << L1 << " " << U1 << " " << L2 << " " << U2 << "]\n";);      \
    imdd * new_child = _mk_empty(d_arity + 1);                                                           \
    add_child(new_child, L2, U2, d);                                                                    \
    new_child = memoize_new_imdd_if(memoize_res, new_child);                                            \
    push_back(L1, U1, new_child);}

    if (u1 < l2 || u2 < l1) {
        ADD_ENTRY(l1, u1, l2, u2); // the intervals are disjoint
    }
    else {
        if (l1 < l2) {
            SASSERT(u1 >= l2);
            // [l1 ...   
            //    [l2 ...
            // -->
            // [l1, l2-1] X [l2, u2]
            ADD_ENTRY(l1, l2-1, l2, u2);
        }
        
        unsigned l = std::max(l1, l2);
        unsigned u = std::min(u1, u2);
        // [l, l] X [l2, l-1]   // if l-1 >= l2 (i.e., l > l2)
        // [l, l] X [l+1, u2]
        // [l+1, l+1] X [l2, l]
        // [l+1, l+1] X [l+2, u2]
        // [l+2, l+2] X [l2, l+1]
        // [l+2, l+2] X [l+3, u2]
        // ...
        // [u, u] X [l2, u-1]
        // [u, u] X [u+1,  u2]  // if u+1 <= u2 (i.e., u < u2)
        for (unsigned i = l; i <= u; i++) {
            if (i > l2 && i < u2) {
                // ADD_ENTRY(i, i, l2, i-1);
                // ADD_ENTRY(i, i, i+1, u2);
                imdd * new_child = _mk_empty(d_arity + 1);
                add_child(new_child, l2, i-1, d);
                add_child(new_child, i+1, u2, d);
                new_child = memoize_new_imdd_if(memoize_res, new_child);
                push_back(i, i, new_child);
            }
            else if (i > l2) {
                SASSERT(!(i < u2));
                ADD_ENTRY(i, i, l2, i-1);
            }
            else if (i < u2) {
                SASSERT(!(i > l2));
                ADD_ENTRY(i, i, i+1, u2);
            }
        }
        
        if (u1 > u2) {
            //       ... u1]
            //     ... u2]
            // -->
            // [u2+1, u1] X [l2, u2]
            SASSERT(u2 >= l1);
            ADD_ENTRY(u2+1, u1, l2, u2);
        }
    }
#undef ADD_ENTRY

    r = memoize_new_imdd_if(memoize_res, r);
    return r;
}

/**
   \brief Auxiliary functor used to implement mk_filter_distinct
*/
struct distinct_proc {
    imdd_manager &                m_manager;

    distinct_proc(imdd_manager & m):
        m_manager(m) {
    }
    
    void operator()(unsigned * lowers_uppers, imdd * d, imdd_ref & r, bool memoize_res) {
        r = m_manager.mk_distinct_imdd(lowers_uppers[0], lowers_uppers[1], lowers_uppers[2], lowers_uppers[3], d, memoize_res);
    }
};

void imdd_manager::mk_filter_distinct_dupdt(imdd_ref & d, unsigned v1, unsigned v2, bool memoize_res) {
    unsigned vars[2] = { v1, v2 };
    distinct_proc proc(*this);
    mk_filter_dupdt(d, 2, vars, proc, memoize_res);
}

void imdd_manager::mk_filter_distinct(imdd * d, imdd_ref & r, unsigned v1, unsigned v2, bool memoize_res) {
    unsigned vars[2] = { v1, v2 };
    distinct_proc proc(*this);
    mk_filter(d, r, 2, vars, proc, memoize_res);

    STRACE("imdd_trace", tout << "mk_filter_distinct(0x" << d << ", 0x" << r.get() << ", " << v1 << ", " << v2 << ", " << memoize_res << ");\n";);
}

imdd * imdd_manager::mk_disequal_imdd(unsigned l1, unsigned u1, unsigned value, imdd * d, bool memoize_res) {
    unsigned d_arity;
    if (d == 0) {
        d_arity = 0;
    }
    else {
        d_arity     = d->get_arity();
        memoize_res = memoize_res && d->is_memoized();
    }
    imdd * r = _mk_empty(d_arity + 1);
    if (value < l1 || value > u1) {
        add_child(r, l1, u1, d);
    }
    else {
        SASSERT(l1 <= value && value <= u1);
        if (l1 < value) {
            add_child(r, l1, value-1, d);
        }
        if (value < u1) {
            add_child(r, value+1, u1, d);
        }
    }
    r = memoize_new_imdd_if(memoize_res, r);
    return r;
}

struct disequal_proc {
    imdd_manager &                m_manager;
    unsigned                      m_value;

    disequal_proc(imdd_manager & m, unsigned v):
        m_manager(m),
        m_value(v) {
    }
    
    void operator()(unsigned * lowers_uppers, imdd * d, imdd_ref & r, bool memoize_res) {
        r = m_manager.mk_disequal_imdd(lowers_uppers[0], lowers_uppers[1], m_value, d, memoize_res);
    }
};

void imdd_manager::mk_filter_disequal_dupdt(imdd_ref & d, unsigned var, unsigned value, bool memoize_res) {
    unsigned vars[1] = { var };
    disequal_proc proc(*this, value);
    mk_filter_dupdt(d, 1, vars, proc, memoize_res);
}

void imdd_manager::mk_filter_disequal(imdd * d, imdd_ref & r, unsigned var, unsigned value, bool memoize_res) {
    unsigned vars[1] = { var };
    disequal_proc proc(*this, value);
    mk_filter(d, r, 1, vars, proc, memoize_res);

    STRACE("imdd_trace", tout << "mk_filter_disequal(0x" << d << ", 0x" << r.get() << ", " << var << ", " << value << ", " << memoize_res << ");\n";);
}


