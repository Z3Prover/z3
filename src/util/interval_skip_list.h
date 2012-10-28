/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    interval_skip_list.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-10-01.

Revision History:

--*/
#ifndef _INTERVAL_SKIP_LIST_H_
#define _INTERVAL_SKIP_LIST_H_

#include"skip_list_base.h"

/*
  Interval skip lists implement a mapping from keys to values.
  The key must be a total order. 

  It compress consecutive entries k->v and (k+1)->v by
  using intervals. Internally, we have [k1, k2]->v to represent
  the set of entries k1->v, (k1+1)->v, ..., k2->v. 

  For improving cache behavior, the entries are packed in
  buckets. As regular skip-lists, a node/bucket may have
  several next/forward pointers.

  Interval skip lists can also encode sets. In this case,
  there is no value type. We achieve that by allowing the template
  to be instantiated with an arbitrary "entry" class for encoding
  [k1, k2]->v. This class must provide the methods:
     
    key const & begin_key() const
    key const & end_key() const
    value const & val() const
    void set_begin_key(key const & k)
    void set_end_key(key const & k)
    void set_val(value const & v)
    void display(ostream & out) const
    bool operator==(entry const & other) const;

  And a definition for the key and value types.
*/

/**
   \brief Default interval_skip_list entry.
   It is useful for implementing mappings.
*/
template<typename Key, typename Value>
class default_islist_entry {
public:
    typedef Key   key;
    typedef Value value;
private:
    key   m_begin_key;
    key   m_end_key;
    value m_value;
public:
    default_islist_entry() {}
    default_islist_entry(key const & b, key const & e, value const & v):
        m_begin_key(b),
        m_end_key(e),
        m_value(v) {
    }
    key const & begin_key() const { return m_begin_key; }
    key const & end_key() const { return m_end_key; }
    value const & val() const { return m_value; }
    void set_begin_key(key const & k) { m_begin_key = k; }
    void set_end_key(key const & k) { m_end_key = k; }
    void set_val(value const & v) { m_value = v; }
    void display(std::ostream & out) const {
        out << "[" << begin_key() << ", " << end_key() << "] -> " << val();
    }
};

/**
   \brief Default interval_skip_list entry for encoding sets.
*/
template<typename Key>
struct default_set_islist_entry {
public:
    typedef Key      key;
    typedef unsigned value; // don't care type
private:
    key   m_begin_key;
    key   m_end_key;
public:
    default_set_islist_entry() {}
    default_set_islist_entry(key const & b, key const & e):
        m_begin_key(b),
        m_end_key(e) {
    }
    key const & begin_key() const { return m_begin_key; }
    key const & end_key() const { return m_end_key; }
    unsigned const & val() const { static unsigned v = 0; return v; }
    void set_begin_key(key const & k) { m_begin_key = k; }
    void set_end_key(key const & k) { m_end_key = k; }
    void set_val(value const & v) { /* do nothing */ }
    void display(std::ostream & out) const {
        out << "[" << begin_key() << ", " << end_key() << "]";
    }
};


/**
   \brief An interval skip list.

   See comments at skip_list_base.h
*/
template<typename Traits>
class interval_skip_list : public skip_list_base<Traits> {
protected:
    typedef typename skip_list_base<Traits>::bucket bucket;
public:
    typedef typename Traits::manager manager;
    typedef typename Traits::entry   entry;
    typedef typename entry::key      key;
    typedef typename entry::value    value;

protected:
    bool lt(key const & k1, key const & k2) const { return skip_list_base<Traits>::lt(k1, k2); }

    static key const & first_key(bucket const * bt) { return bt->first_entry().begin_key(); }

    static key const & last_key(bucket const * bt) { return bt->last_entry().end_key(); }
    
    static void set_entry(bucket * bt, unsigned idx, key const & b, key const & e, value const & v) {
        entry & en = bt->get(idx);
        en.set_begin_key(b);
        en.set_end_key(e);
        en.set_val(v);
    }

    /**
       \brief Add first entry to the list.

       \remark This method will invoke inc_ref_eh for v.
    */
    void insert_first_entry(manager & m, key const & b, key const & e, value const & v) {
        entry en;
        en.set_begin_key(b);
        en.set_end_key(e);
        en.set_val(v);
        skip_list_base<Traits>::insert_first_entry(m, en);
    }

    /**
       \brief Return true if the given key \c k is in the entry \c e. That is,
       k \in [e.begin_key(), e.end_key()].
    */
    bool contains(entry const & e, key const & k) const { return this->leq(e.begin_key(), k) && this->leq(k, e.end_key()); }
    
    /**
       \brief Return true if the given key \c k is in the entry \c e. That is,
       k \in [e.begin_key(), e.end_key()]. If that is the case, then store e.value() in v. 
       Otherwise, return false.
    */
    bool contains(entry const & e, key const & k, value & v) const { 
        if (contains(e, k)) {
            v = e.val();
            return true;
        }
        else {
            return false;
        }
    }            
    
    /**
       \brief Search for a key in a bucket starting at position s_idx using binary search.
       
       Return true if k was found in the bucket and store the index of
       the entry containing \c k in \c idx.
       
       Otherwise, return false and \c idx will contain the index 
       s.t.
       (idx == s_idx || entry[idx-1].end_key() < k) && (idx == bt->size() || k < entry[idx].begin_key())
    */
    bool find_core(bucket const * bt, unsigned s_idx, key const & k, unsigned & idx) const {
        if (s_idx >= bt->size()) {
            idx = s_idx;
            return false;
        }
        int low  = s_idx;
        int high = bt->size() - 1;
        for (;;) {
            int mid = low + ((high - low) / 2);
            entry const & mid_entry = bt->get(mid);
            if (this->gt(k, mid_entry.end_key())) {
                low = mid + 1;
                if (low > high) {
                    idx = static_cast<unsigned>(mid) + 1;
                    SASSERT(idx >= s_idx);
                    SASSERT(idx == s_idx || lt(bt->get(idx - 1).end_key(), k));
                    SASSERT(idx == bt->size() || lt(k, bt->get(idx).begin_key()));
                    return false;
                }

            }
            else if (lt(k, mid_entry.begin_key())) {
                high = mid - 1;
                if (low > high) {
                    idx = static_cast<unsigned>(mid);
                    SASSERT(idx >= s_idx);
                    SASSERT(idx == s_idx || lt(bt->get(idx - 1).end_key(), k));
                    SASSERT(idx == bt->size() || lt(k, bt->get(idx).begin_key()));
                    return false;
                }
            }
            else {
                SASSERT(contains(mid_entry, k));
                SASSERT(mid >= 0);
                idx = static_cast<unsigned>(mid);
                SASSERT(idx >= s_idx);
                return true;
            }
        }
    }

    /**
       \brief Search for a key in a bucket using binary search.
       
       Return true if k was found in the bucket and store the index of
       the entry containing \c k in \c idx.
       
       Otherwise, return false and \c idx will contain the index 
       s.t.
       (idx == 0 || entry[idx-1].end_key() < k) && (idx == bt->size() || k < entry[idx].begin_key()
    */
    bool find_core(bucket const * bt, key const & k, unsigned & idx) const {
        bool r = find_core(bt, 0, k, idx);
        SASSERT(!r || contains(bt->get(idx), k));
        SASSERT( r || idx == 0 || lt(bt->get(idx - 1).end_key(), k));
        SASSERT( r || idx == bt->size() || lt(k, bt->get(idx).begin_key()));
        return r;
    }

    /**
       \brief Search for the given key in the interval skip list.
       Return true if the key is stored in the list, and store the location of the entry that contains the k in the
       pair (bt, idx). The location should be read as the key is in the entry idx of the bucket bt.
       Otherwise, returns false and (bt, idx) contains:
       Case 1: bt != 0 && 0 < idx < bt->size() && bt->get(idx-1).end_key() < k && k < bt->get(idx).begin_key()
       Case 2: bt != 0 && idx == 0 && (pred_bucket(bt) == m_header || last_key(pred_bucket(bt)) < k) && k < first_key(bt)
       Case 3: bt == 0 && idx == 0 && k is greater than all keys in the list.
       bt != m_header
       
       Even when find_core returns false, the pair (bt, idx) can be used to create an iterator object
       to traverse keys >= k.
    */
    template<bool UpdatePredVect>
    bool find_core(key const & k, bucket * & bt, unsigned & idx, bucket * pred_vect[]) const {
        bucket * curr = this->m_header;
        unsigned i    = this->m_header->level();
        bucket * next;
        while (i > 0) {
            i--;
            for (;;) {
                next = curr->get_next(i);
                if (next != 0 && lt(first_key(next), k))
                    curr = next;
                else
                    break;
            }
            if (UpdatePredVect)
                pred_vect[i] = curr;
        }
        
        SASSERT(next == curr->get_next(0));

        // the search_key must be in the current bucket, or in the first entry of the next bucket (if the next bucket is not 0).
        SASSERT(curr->empty() || lt(first_key(curr), k));
        SASSERT(next == 0 || this->geq(first_key(next), k));
        DEBUG_CODE({
            if (UpdatePredVect && next != 0)
                for (unsigned i = 0; i < next->level(); i++) 
                    SASSERT(pred_vect[i]->get_next(i) == next);
        });

        if (next != 0 && contains(next->first_entry(), k)) {
            bt  = next;
            idx = 0;
            return true;
        }
        
        bool r = find_core(curr, k, idx);
        if (idx == curr->size()) {
            SASSERT(!r);
            bt  = next;
            idx = 0;
        }
        else {
            SASSERT(idx < curr->size());
            bt = curr;
        }
        SASSERT(bt != this->m_header);
        SASSERT((bt == 0 && idx == 0) || (bt != 0 && idx < bt->size()));
        SASSERT(!r || contains(bt->get(idx), k));
        SASSERT(r || 
                // Case 1
                (bt != 0 && 0 < idx && idx < bt->size() && lt(bt->get(idx-1).end_key(), k) && lt(k, bt->get(idx).begin_key())) ||
                // Case 2
                (bt != 0 && idx == 0 && (this->pred_bucket(bt) == this->m_header || lt(last_key(this->pred_bucket(bt)), k)) && lt(k, first_key(bt))) ||
                // Case 3
                (bt == 0 && idx == 0) // k is greater than all keys in the list.
                );
        return r;
    }

    /**
       \brief Return true if the two entries (that satisfy lt(e1, e2)) can be merged.
    */
    bool can_be_merged(entry const & e1, entry const & e2) const {
        return this->val_eq(e1.val(), e2.val()) && this->eq(this->succ(e1.end_key()), e2.begin_key());
    }
    
    /**
       \brief Try to merge the last entry with bt with the first entry of its successor.
       
       \remark pred_vect contains the predecessors of the successor of bt.
    */
    void merge_first_of_succ_if_possible(manager & m, bucket * bt, bucket * pred_vect[]) {
        SASSERT(this->check_pred_vect(bt->get_next(0), pred_vect));
        bucket * next_bucket = bt->get_next(0);
        if (next_bucket != 0) {
            entry & curr_entry = bt->last_entry();
            entry & next_entry = next_bucket->get(0);
            if (can_be_merged(curr_entry, next_entry)) {
                curr_entry.set_end_key(next_entry.end_key());
                this->del_entry(m, next_bucket, 0); // del_entry invokes dec_ref_eh
                if (next_bucket->empty())
                    this->del_bucket(m, next_bucket, pred_vect);
            }
        }
    }

    /**
       \brief Try to merge the entry at position idx with the next entry if possible.
    */
    void merge_next_if_possible(manager & m, bucket * bt, unsigned idx, bucket * pred_vect[]) {
        SASSERT(!bt->empty());
        if (idx + 1 == bt->size()) {
            // it is the last element
            merge_first_of_succ_if_possible(m, bt, pred_vect);
        }
        else {
            entry & curr_entry = bt->get(idx);
            entry & next_entry = bt->get(idx+1);
            if (can_be_merged(curr_entry, next_entry)) {
                curr_entry.set_end_key(next_entry.end_key());
                this->del_entry(m, bt, idx+1); // del_entry invokes dec_ref_eh
            }
        }
    }

    /**
       \brief Try to merge the entry at position idx with the previous entry if possible.
       
       \remark This method assumes that idx > 0.
    */
    void merge_prev_if_possible(manager & m, bucket * bt, unsigned idx) {
        SASSERT(idx > 0);
        entry & curr_entry = bt->get(idx);
        entry & prev_entry = bt->get(idx-1);
        if (can_be_merged(prev_entry, curr_entry)) {
            prev_entry.set_end_key(curr_entry.end_key());
            this->del_entry(m, bt, idx); // del_entry invokes dec_ref_eh
        }
    }

    /**
       \brief Delete entries starting at indices [s_idx, e_idx), assuming e_idx < bt->size()
       
       \remark The pre-condition guarantees that the bucket will not be empty after the entries
       are deleted.

       \remark If RECYCLE_ENTRY is true, then method will try to recycle position s_idx if it is deleted, and will return true.
       Position s_idx will be an empty slot in this case.
    */
    template<bool RECYCLE_ENTRY>
    bool del_entries(manager & m, bucket * bt, unsigned s_idx, unsigned e_idx) {
        bool result = false;
        if (RECYCLE_ENTRY && s_idx + 1 < e_idx) {
            // The position s_idx will be recycled, but the reference to the value stored there 
            // will be lost.
            this->dec_ref(m, bt->get(s_idx).val()); 
            s_idx++;
            result = true;
        }
        TRACE("del_entries_upto_bug", this->display(tout, bt); tout << "[" << s_idx << ", " << e_idx << ")\n";);
        SASSERT(e_idx >= s_idx);
        SASSERT(e_idx < bt->size());
        // move entries
        unsigned num_removed = e_idx - s_idx;
        entry *  dest_it     = bt->get_entries() + s_idx;
        entry *  source_it   = bt->get_entries() + e_idx;
        entry *  source_end  = bt->get_entries() + bt->size();
        if (Traits::ref_count) {
            // invoke dec_ref_eh for entries between dest_it and source_it, since they are being removed
            entry * it = dest_it;
            for (; it < source_it; ++it) {
                this->dec_ref(m, it->val());
            }
        }
        for (; source_it < source_end; ++dest_it, ++source_it) {
            *dest_it = *source_it;
        }
        // update size
        bt->shrink(num_removed);
        SASSERT(!bt->empty());
        TRACE("del_entries_upto_bug", this->display(tout, bt););
        return result;
    }

    /**
       \brief Delete all keys (starting at position s_idx) in the given bucket that are <= k.
       The method assumes that k < bt->last_key().
       This condition guarantees that the bucket will not be empty after removing the keys.
    
       
       \remark If RECYCLE_ENTRY is true, then method will try to recycle position s_idx if it is deleted, and will return true.
       Position s_idx will be an empty slot in this case.
    */
    template<bool RECYCLE_ENTRY>
    bool del_last_entries_upto(manager & m, bucket * bt, unsigned s_idx, key const & k) {
        SASSERT(s_idx < bt->size());
        SASSERT(lt(k, last_key(bt)));
        int low  = s_idx;
        int high = bt->size() - 1;
        SASSERT(low <= high);
        for (;;) {
            int mid = low + ((high - low) / 2);
            SASSERT(mid < static_cast<int>(bt->size())); 
            entry & mid_entry = bt->get(mid);
            if (this->gt(k, mid_entry.end_key())) {
                low = mid + 1;
                if (low > high) {
                    // mid entry must be deleted since k > mid_entry.end_key().
                    TRACE("del_entries_upto_bug", tout << "exit 1) mid: " << mid << "\n"; this->display(tout, mid_entry); tout << "\n";);
                    SASSERT(mid + 1 < static_cast<int>(bt->size())); // Reason: method pre-condition: lt(k, last_key(bt))
                    return del_entries<RECYCLE_ENTRY>(m, bt, s_idx, mid + 1);
                }
            }
            else if (lt(k, mid_entry.begin_key())) {
                high = mid - 1;
                if (low > high) {
                    // mid entry must not be deleted since k < mid_entry.begin_key().
                    TRACE("del_entries_upto_bug", tout << "exit 2) mid: " << mid << "\n"; this->display(tout, mid_entry); tout << "\n";);
                    SASSERT(mid < static_cast<int>(bt->size())); // Reason: loop invariant
                    return del_entries<RECYCLE_ENTRY>(m, bt, s_idx, mid);
                }
            }
            else {
                SASSERT(contains(mid_entry, k));
                if (lt(k, mid_entry.end_key())) {
                    TRACE("del_entries_upto_bug", tout << "exit 3) mid: " << mid << "\n"; this->display(tout, mid_entry); tout << "\n";);
                    mid_entry.set_begin_key(this->succ(k));
                    SASSERT(mid < static_cast<int>(bt->size())); // Reason: loop invariant
                    return del_entries<RECYCLE_ENTRY>(m, bt, s_idx, mid);
                }
                else {
                    // mid_entry should also be removed
                    TRACE("del_entries_upto_bug", tout << "exit 4) mid: " << mid << "\n"; this->display(tout, mid_entry); tout << "\n";);
                    SASSERT(mid + 1 < static_cast<int>(bt->size())); // Reason: method pre-condition: lt(k, last_key(bt))
                    return del_entries<RECYCLE_ENTRY>(m, bt, s_idx, mid + 1);
                }
            }
        }
    }

    /**
       \brief Keep deleting keys <= k in bt and its successors.
    */
    void del_entries_upto_loop(manager & m, bucket * bt, key const & k, bucket * pred_vect []) {
      SASSERT(this->check_pred_vect(bt, pred_vect));
        while (bt != 0) {
            key const & bt_last_key = last_key(bt);
            if (lt(k, bt_last_key)) {
                del_last_entries_upto<false>(m, bt, 0, k);
                return;
            }
            else if (this->eq(k, bt_last_key)) {
                this->del_bucket(m, bt, pred_vect);
                return;
            }
            else {
                SASSERT(this->gt(k, bt_last_key));
                bucket * next = bt->get_next(0);
                this->del_bucket(m, bt, pred_vect);
                bt = next;
                // continue deleting...
            }
        }
    }

    /**
       \brief Delete entries starting at position 0 such that keys are <= k.
    
       If INSERT == true, then try to save/recycle an entry. Return true, if 
       managed to recycle the entry.

       The bucket bt may be deleted when INSERT==false and k >= last_key(bt).

       - pred_vect must contain the predecessors of bt.
       
       - next_pred_vect is an uninitialized predecessor vector. It may be initialized
       when INSERT == true. If needed it is initialized using
       update_predecessor_vector(pred_vect, bt, next_pred_vect);
    */
    template<bool INSERT>
    bool del_entries_upto(manager & m, bucket * bt, key const & k, bucket * pred_vect[], bucket * next_pred_vect[]) {
        SASSERT(this->check_pred_vect(bt, pred_vect)); // pred_vect contains the predecessors of bt.
        if (lt(k, first_key(bt))) {
            // nothing to be done...
            return false; // didn't manage to recycle entry.
        }
        
        key const & bt_last_key = last_key(bt);
        TRACE("del_entries_upto_bug", tout << "bt_last_key: " << bt_last_key << "\n";);
        if (this->lt(k, bt_last_key)) {
            return del_last_entries_upto<INSERT>(m, bt, 0, k);
        }
        else {
            if (INSERT) {
                // Invoke DEC-REF for all entries in bt
                this->dec_ref(m, bt);
                // REMARK: the slot 0 will be reused, but the element there is gone.
                bt->set_size(1);
                if (this->gt(k, bt_last_key)) {
                    bucket * next = bt->get_next(0);
                    if (next != 0) {
                        this->update_predecessor_vector(pred_vect, bt, next_pred_vect);
                        del_entries_upto_loop(m, next, k, next_pred_vect);
                    }
                }
                return true; // recycled entry.
            }
            else {
                bucket * next = bt->get_next(0);
                this->del_bucket(m, bt, pred_vect); // it will invoke dec_ref_eh for all values in bt.
                // pred_vect does not need to be updated since it contains the predecessors of
                // bt, since bt was deleted they are now the predecessors of its successor.
                if (next != 0) {
                    del_entries_upto_loop(m, next, k, pred_vect);
                }
                return false; // don't care in this case, since it is not an insertion.
            }
        }
    }

    /**
       \brief Delete entries starting at position s_idx (> 0) such that keys are <= k.
       The bucket bt cannot be deleted since s_idx > 0. 
    
       If INSERT == true, then try to save/recycle an entry. Return true, if 
       managed to recycle the entry.

       - pred_vect must contain the predecessors of bt->get_next(0).
    */
    template<bool INSERT>
    bool del_entries_upto(manager & m, bucket * bt, unsigned s_idx, key const & k, bucket * pred_vect[]) {
        SASSERT(this->check_pred_vect(bt->get_next(0), pred_vect)); // pred_vect contains the predecessors of the successor of bt.
        SASSERT(s_idx > 0);
        TRACE("del_entries_upto_bug",
              tout << "INSERT: " << INSERT << "\n";
              tout << "del_entries_upto, s_idx: " << s_idx << ", k: " << k << "\n";
              this->display(tout, bt);
              tout << "\n";
              this->display_predecessor_vector(tout, pred_vect););
        
        if (s_idx >= bt->size()) {
            // nothing to do in bt, moving to successors...
            del_entries_upto_loop(m, bt->get_next(0), k, pred_vect);
            return false; // didn't manage to recycle an entry
        }
        
        if (lt(k, bt->get(s_idx).begin_key())) {
            // nothing to be done...
            return false; // didn't manage to recycle an entry
        }

        key const & bt_last_key = last_key(bt);
        TRACE("del_entries_upto_bug", tout << "bt_last_key: " << bt_last_key << "\n";);
        if (lt(k, bt_last_key)) {
            return del_last_entries_upto<INSERT>(m, bt, s_idx, k);
        }
        else {
            if (this->gt(k, bt_last_key)) {
                del_entries_upto_loop(m, bt->get_next(0), k, pred_vect);
            }
            if (Traits::ref_count) {
                // Invoke dec_ref_eh for all values in [s_idx, bt->size())
                unsigned sz = bt->size();
                for (unsigned i = s_idx; i < sz; i++)
                    this->dec_ref(m, bt->get(i).val());
            }
            if (INSERT) {
                SASSERT(s_idx < bt->size());
                bt->set_size(s_idx + 1);
                return true; // recycled an entry

            }
            else {
                bt->set_size(s_idx);
                return false; // don't care. it is not an insertion.
            }
        }
    }

    /**
       \brief Insert entry [b,e]->v in the beginning of the bucket bt.
    */
    void insert_begin(manager & m, bucket * bt, key const & b, key const & e, value const & v, bucket * pred_vect[]) {
        TRACE("interval_skip_list_bug", tout << "insert_begin: [" << b << ", " << e << "] -> " << v << "\n"; this->display(tout, bt););
        SASSERT(this->check_pred_vect(bt, pred_vect));
        SASSERT(!bt->empty());
        SASSERT(bt->size() <= bt->capacity());
        SASSERT(this->leq(b, first_key(bt)));
        bucket * next_pred_vect[Traits::max_level];
        next_pred_vect[0] = 0; 

        this->inc_ref(m, v);

        // Delete entries that will be overlapped by new entry. 
        // Try to reuse a slot that was deleted... 
        bool recycled = del_entries_upto<true>(m, bt, e, pred_vect, next_pred_vect);
        if (recycled) {
            set_entry(bt, 0, b, e, v); // Reference to v was stored, and inc_ref_eh was invoked above.
            TRACE("interval_skip_list_bug", this->display_physical(tout););
            if (next_pred_vect[0] != 0) {
                // the vector next_pred_vect was initialized by del_entries_upto<true>.
                merge_next_if_possible(m, bt, 0, next_pred_vect);
            }
            else {
	        this->update_predecessor_vector(pred_vect, bt);
                merge_next_if_possible(m, bt, 0, pred_vect);
            }
            return;
        }
        // check if can merge with first entry in the bucket.
        entry & fe = bt->first_entry();
        if (this->val_eq(fe.val(), v) && this->eq(fe.begin_key(), this->succ(e))) {
            // can merge
            fe.set_begin_key(b);
            // A new reference to v was not created. So, we must invoke dec_ref_eh since we increased the counter above.
            this->dec_ref(m, v);
            return;
        }
        // Is there space for the new entry?
        if (bt->size() == bt->capacity()) {
            if (bt->capacity() < Traits::max_capacity) {
                SASSERT(this->first_bucket() == bt && this->first_bucket()->get_next(0) == 0);
                this->expand_first_bucket(m);
                bt = this->first_bucket();
            }
            else {
                // there is no space
                this->splice(m, bt, pred_vect);
            }
        }
        this->open_space(bt, 0);
        set_entry(bt, 0, b, e, v); // Reference to v was stored, and inc_ref_eh was invoked above.
        SASSERT(!can_be_merged(bt->get(0), bt->get(1)));
    }

    /**
       \brief Insert the entry [b, e]->v at position idx. 
    */
    void insert_at(manager & m, bucket * bt, unsigned idx, key const & b, key const & e, value const & v, bucket * pred_vect[]) {
        SASSERT(idx > 0);
        SASSERT(this->check_pred_vect(bt->get_next(0), pred_vect));

        this->inc_ref(m, v);
        TRACE("insert_at_bug", tout << "before del_entries_upto:\n"; this->display_physical(tout););

        bool recycled = del_entries_upto<true>(m, bt, idx, e, pred_vect);

        TRACE("insert_at_bug", tout << "after del_entries_upto:\n"; this->display_physical(tout););

        if (recycled) {
            set_entry(bt, idx, b, e, v); // Reference to v was stored, and inc_ref_eh was invoked above.
            merge_next_if_possible(m, bt, idx, pred_vect);
            merge_prev_if_possible(m, bt, idx);
            TRACE("insert_at_bug", tout << "using recycled:\n"; this->display_physical(tout););
            return;
        }

        // Is there space for the new entry?
        if (bt->size() == bt->capacity()) {
            // there is no space
            if (bt->capacity() < Traits::max_capacity) {
                SASSERT(this->first_bucket() == bt && this->first_bucket()->get_next(0) == 0);
                this->expand_first_bucket(m);
                bt = this->first_bucket();
                // there is no need to update pred_vect, since the list contains only one bucket.
            }
            else {
                this->splice(m, bt, pred_vect);
                bucket * new_next = bt->get_next(0);
                SASSERT(bt->size() == bt->capacity()/2);
                if (idx == bt->capacity()/2) {
                    entry & bt_last_entry = bt->last_entry();
                    if (this->val_eq(bt_last_entry.val(), v) && this->eq(bt_last_entry.end_key(), this->pred(b))) {
                        // merged with the last key of bt
                        bt_last_entry.set_end_key(e);
                        // A new reference to v was not created. So, we must invoke dec_ref_eh since we increased the counter above.
                        this->dec_ref(m, v);
                        return;
                    }
                    entry & new_next_first_entry = new_next->first_entry();
                    if (this->val_eq(new_next_first_entry.val(), v) && this->eq(new_next_first_entry.begin_key(), this->succ(e))) {
                        // merged with the first key of new_next
                        new_next_first_entry.set_begin_key(b);
                        // A new reference to v was not created. So, we must invoke dec_ref_eh since we increased the counter above.
                        this->dec_ref(m, v);
                        return;
                    }
                    // insert in the end of bt.
                    bt->set_size(bt->capacity()/2 + 1);
                    set_entry(bt, bt->capacity()/2, b, e, v); // Reference to v was stored, and inc_ref_eh was invoked above.
                    return;
                }
                else if (idx > bt->capacity()/2) {
                    idx -= bt->capacity()/2;
                    SASSERT(idx > 0);
                    bt   = new_next;
                    this->update_predecessor_vector(pred_vect, bt);
                }
            }
        }
        SASSERT(idx > 0);
        this->open_space(bt, idx);
        set_entry(bt, idx, b, e, v); // Reference to v was stored, and inc_ref_eh was invoked above.
        merge_next_if_possible(m, bt, idx, pred_vect);
        merge_prev_if_possible(m, bt, idx);
        TRACE("insert_at_bug", tout << "using open-space:\n"; this->display_physical(tout););
    }

    /**
       \brief Insert the entry [b,e]->v into the bucket bt.
       
       pred_vect contains the predecessors of the successor of bt (i.e., bt->get_next(0))
    */
    void insert_inside(manager & m, bucket * bt, key const & b, key const & e, value const & v, bucket * pred_vect[]) {
        TRACE("interval_skip_list_bug", tout << "insert_inside: [" << b << ", " << e << "] -> " << v << "\n";);
        SASSERT(this->check_pred_vect(bt->get_next(0), pred_vect));
        SASSERT(!bt->empty());
        SASSERT(bt->size() <= bt->capacity());
        // perform binary search to find position to insert [b, e]->v
        int low  = 0;
        int high = bt->size() - 1;
        for (;;) {
            int mid = low + ((high - low) / 2);
            entry & mid_entry = bt->get(mid);
            if (this->gt(b, mid_entry.end_key())) {
                low = mid + 1;
                if (low > high) {
                    // insert after mid_entry since b > mid_entry.end_key().
                    insert_at(m, bt, mid+1, b, e, v, pred_vect);
                    return;
                }
            }
            else if (lt(b, mid_entry.begin_key())) {
                high = mid - 1;
                if (low > high) {
                    // insert before mid_entry since b < mid_entry.begin_key().
                    SASSERT(mid > 0); // Reason: insert_begin would have been called instead.
                    insert_at(m, bt, mid, b, e, v, pred_vect);
                    return;
                }
            }
            else {
                SASSERT(contains(mid_entry, b));
                TRACE("insert_inside_bug", tout << "insert_inside:\n"; this->display(tout, bt););
                if (this->val_eq(mid_entry.val(), v)) {
                    if (this->gt(e, mid_entry.end_key())) {
                        // No need to create space.
                        // We did not create a new reference to v.
                        mid_entry.set_end_key(e);
                        del_entries_upto<false>(m, bt, mid+1, e, pred_vect);
                        merge_next_if_possible(m, bt, mid, pred_vect);
                        return;
                    }
                }
                else {
                    if (this->gt(b, mid_entry.begin_key())) {
                        if (this->lt(e, mid_entry.end_key())) {
                            // New interval is the middle of existing interval

                            // We must INVOKE add_ref_eh for mid_entry.val() and v.
                            this->inc_ref(m, v);
                            this->inc_ref(m, mid_entry.val()); // mid_entry was split in two.

                            // we need two new entries.
                            if (bt->size() >= bt->capacity() - 1) { 
                                if (bt->capacity() < Traits::max_capacity) {
                                    SASSERT(this->first_bucket() == bt && this->first_bucket()->get_next(0) == 0);
                                    this->expand_first_bucket(m);
                                    bt = this->first_bucket();
                                }
                                else {
                                    this->splice(m, bt, pred_vect);
                                    int new_sz = bt->size();
                                    bucket * new_next = bt->get_next(0);
                                    if (mid >= new_sz) {
                                        mid -= new_sz;
                                        SASSERT(mid >= 0);
                                        bt = new_next;
                                    }
                                }
                            }
                            this->open_2spaces(bt, mid);
                            entry & mid1_entry = bt->get(mid);
                            entry & new_entry  = bt->get(mid+1);
                            entry & mid2_entry = bt->get(mid+2);
                            mid2_entry             = mid1_entry;
                            mid1_entry.set_end_key(this->pred(b));
                            new_entry.set_begin_key(b);
                            new_entry.set_end_key(e);
                            new_entry.set_val(v);
                            mid2_entry.set_begin_key(this->succ(e));
                        }
                        else {
                            mid_entry.set_end_key(this->pred(b));
                            insert_at(m, bt, mid+1, b, e, v, pred_vect);
                        }
                    }
                    else {
                        SASSERT(this->eq(b, mid_entry.begin_key()));
                        SASSERT(mid > 0); // Reason: insert_begin would have been called instead.
                        insert_at(m, bt, mid, b, e, v, pred_vect);
                    }
                }
                return;
            }
        }
    }

    /**
       \brief Remove [b,e]->v from the beginning of the bucket bt.
    */
    void remove_begin(manager & m, bucket * bt, key const & b, key const & e, bucket * pred_vect[]) {
        TRACE("interval_skip_list_bug", tout << "remove_begin: [" << b << ", " << e << "]\n";);
        SASSERT(!bt->empty());
        SASSERT(pred_vect[0]->get_next(0) == bt); 
        del_entries_upto<false>(m, bt, e, pred_vect, 0);
    }

    /**
       \brief Remove [b,e]->v from the bucket bt.
    */
    void remove_inside(manager & m, bucket * bt, key const & b, key const & e, bucket * pred_vect[]) {
        TRACE("interval_skip_list_bug", tout << "remove_inside: [" << b << ", " << e << "]\n";);
        // perform binary search to find position to insert [b, e]->v
        int low  = 0;
        int high = bt->size() - 1;
        for (;;) {
            int mid = low + ((high - low) / 2);
            entry & mid_entry = bt->get(mid);
            if (this->gt(b, mid_entry.end_key())) {
                low = mid + 1;
                if (low > high) {
                    // insert after mid_entry since b > mid_entry.end_key().
                    del_entries_upto<false>(m, bt, mid+1, e, pred_vect);
                    return;
                }
            }
            else if (this->lt(b, mid_entry.begin_key())) {
                high = mid - 1;
                if (low > high) {
                    // insert before mid_entry since b < mid_entry.begin_key().
                    SASSERT(mid > 0); // Reason: remove_begin would have been called instead.
                    del_entries_upto<false>(m, bt, mid, e, pred_vect);
                    return;
                }
            }
            else {
                SASSERT(contains(mid_entry, b));
                if (this->gt(b, mid_entry.begin_key())) {
                    if (this->lt(e, mid_entry.end_key())) {
                        // The removed interval is inside of an existing interval.

                        // mid_entry will be split in two. So, we must invoke add_ref_eh for mid_entry.val()
                        this->inc_ref(m, mid_entry.val());

                        // We need to break mid_entry in two parts.
                        if (bt->size() == bt->capacity()) {
                            if (bt->capacity() < Traits::max_capacity) {
                                SASSERT(this->first_bucket() == bt && this->first_bucket()->get_next(0) == 0);
                                this->expand_first_bucket(m);
                                bt = this->first_bucket();
                                SASSERT(bt->size() < bt->capacity());
                            }
                            else {
                                this->splice(m, bt, pred_vect);
                                if (mid >= static_cast<int>(bt->size())) {
                                    // mid_entry moved to new (successor) bucket
                                    mid -= bt->size();
                                    bt   = bt->get_next(0);
                                }
                            }
                        }
                        this->open_space(bt, mid);
                        entry & mid1_entry = bt->get(mid);
                        entry & mid2_entry = bt->get(mid+1);
                        mid1_entry.set_end_key(this->pred(b));
                        mid2_entry.set_begin_key(this->succ(e));
                    }
                    else {
                        mid_entry.set_end_key(this->pred(b));
                        del_entries_upto<false>(m, bt, mid+1, e, pred_vect);
                    }
                }
                else {
                    SASSERT(this->eq(b, mid_entry.begin_key()));
                    SASSERT(mid > 0); // Reason: remove_begin would have been called instead.
                    del_entries_upto<false>(m, bt, mid, e, pred_vect);
                }
                return;
            }
        }
    }
    
public:
    interval_skip_list() {
    }

    interval_skip_list(manager & m):skip_list_base<Traits>(m) {
    }

    ~interval_skip_list() {
    }

    /**
       \brief Copy the elements of other. 
       This method assumes that the *this* skip-list is empty.
    */
    void copy(manager & m, interval_skip_list const & other) {
        SASSERT(this->empty());
        other.clone_core(m, this);
    }

    /**
       \brief Return the smallest key stored in the interval skip list.
    */
    key const & smallest() const {
        SASSERT(!this->empty());
        return this->first_bucket()->get(0).begin_key();
    }

    /**
       \brief Search for the given key in the interval skip list.
       Return true if the key is stored in the list, and store the associated value in \c v.
    */
    bool contains(key const & k, value & v) const {
        bucket * bt;
        unsigned idx;
        if (find_core<false>(k, bt, idx, 0)) {
            v = bt->get(idx).val();
            return true;
        }
        return false;
    }

    /**
       \brief Alias for #contains.
    */
    bool find(key const & k, value & v) const {
        return contains(k, v);
    }

private:
    /**
       \brief Search for a bucket based on the key \c k.
       
       curr, next and pred_vect are output arguments.
       
       pred_vect must be an array of size level().
       
       Post-conditions:

       pred_vect contains the predecessors of next. 
       That is, pred_vect[i] is the predecessor of level i.
       
       next is the successor of curr.
       
       pred_vect[0] == curr.
       
       curr == m_header || first_key(curr) < k

       next == 0 || k <= first_key(next)
    */
    void find_bucket(key const & k, bucket * & curr, bucket * & next, bucket * pred_vect[]) {
        SASSERT(this->level() > 0);
        curr       = this->m_header;
        unsigned i = curr->level();
        SASSERT(i > 0);
        while (i > 0) {
            i--;
            for (;;) {
                next = curr->get_next(i);
                if (next != 0 && lt(first_key(next), k))
                    curr = next;
                else
                    break;
            }
            pred_vect[i] = curr;
        }

        SASSERT(next == curr->get_next(0));
        SASSERT(pred_vect[0] == curr);
        DEBUG_CODE({
            if (next != 0)
                for (unsigned i = 0; i < next->level(); i++) 
                    SASSERT(pred_vect[i]->get_next(i) == next);
        });
        SASSERT(curr == this->m_header || lt(first_key(curr), k));
        SASSERT(next == 0 || this->leq(k, first_key(next)));
    }

public:

    /**
       \brief Insert the entries [i -> v] for every i \in [b, e].
    */
    void insert(manager & m, key const & b, key const & e, value const & v) {
        SASSERT(this->leq(b, e));
        if (this->empty()) {
            insert_first_entry(m, b, e, v);
            return;
        }

        // find the bucket where the new entries should be stored.
        
        // pred_vect[i] contains a pointer to the rightmost bucket of
        // level i or higher that is to the left of the location of
        // the insertion.
        bucket * pred_vect[Traits::max_level]; 
        bucket * curr, * next;
        find_bucket(b, curr, next, pred_vect);
        
        if (curr == this->m_header) {
            SASSERT(next != 0);
            // entry must be inserted in the first bucket.
            SASSERT(this->first_bucket() == next);
            insert_begin(m, next, b, e, v, pred_vect);
        }
        else if (next == 0 || this->gt(first_key(next), b)) {
            insert_inside(m, curr, b, e, v, pred_vect);
        }
        else {
            SASSERT(!curr->empty());
            SASSERT(!next->empty());
            SASSERT(next != 0);
            SASSERT(this->eq(first_key(next), b));
            // Bucket curr is the predecessor of next.
            SASSERT(curr->get_next(0) == next); 
            
            // check if we can merge with last entry of curr
            entry & curr_last_entry = curr->last_entry();
            if (this->val_eq(curr_last_entry.val(), v) && this->eq(curr_last_entry.end_key(), this->pred(b))) {
                // No new reference to v was create, we don't need to invok inc_ref_eh
                curr_last_entry.set_end_key(e);
                del_entries_upto<false>(m, next, e, pred_vect, 0);
                merge_first_of_succ_if_possible(m, curr, pred_vect);
                return;
            }
            insert_begin(m, next, b, e, v, pred_vect);
        }
    }

    /**
       \brief Insert key [k->v].
    */
    void insert(manager & m, key const & k, value const & v) {
        insert(m, k, k, v);
    }

    class push_back_proc;
    friend class push_back_proc;
    
    /**
       \brief Functor for efficiently inserting elements in the end of the skip list.
       
       \remark The context becomes invalid if the skip-list is updated by other methods.
    */
    class push_back_proc {
        friend class interval_skip_list;
        manager &            m_manager;
        interval_skip_list & m_list;
        bucket *             m_pred_vect[Traits::max_level]; 
        
        bucket * last_bucket() const { return m_pred_vect[0]; }
        
    public:
        push_back_proc(manager & m, interval_skip_list & l):
            m_manager(m), 
            m_list(l) {
            // initialize m_pred_vect
            unsigned lvl  = m_list.level();
            bucket * curr = m_list.m_header;
            bucket * next;
            unsigned i    = lvl;
            while (i > 0) {
                i--;
                for (;;) {
                    next = curr->get_next(i);
                    if (next != 0)
                        curr = next;
                    else
                        break;
                }
                m_pred_vect[i] = curr;
            }
            SASSERT(next == 0);
        }

        interval_skip_list & list() {
            return m_list;
        }

        bool empty() const { 
            return m_list.empty();
        }

        key const & last_key() const {
            return last_bucket()->last_entry().end_key();
        }
        
        void operator()(key const & b, key const & e, value const & v) {
            SASSERT(m_list.leq(b, e));
            if (m_list.empty()) {
                m_list.insert_first_entry(m_manager, b, e, v);
                bucket * new_bucket = m_list.first_bucket();
                skip_list_base<Traits>::update_predecessor_vector(m_pred_vect, new_bucket);
            }
            else {
                bucket * bt = last_bucket();
                entry & et  = bt->last_entry();
                SASSERT(m_list.lt(et.end_key(), b));
                // first check if new entry can be merged with the last entry in the list
                if (m_list.val_eq(et.val(), v) && m_list.eq(et.end_key(), m_list.pred(b))) {
                    // can merge
                    et.set_end_key(e);
                    return;
                }
                // insert in the last bucket
                unsigned sz = bt->size();
                if (sz >= bt->capacity()) {
                    if (bt->capacity() < Traits::max_capacity) {
                        SASSERT(m_list.first_bucket() == bt && m_list.first_bucket()->get_next(0) == 0);
                        m_list.expand_first_bucket(m_manager);
                        bt = m_list.first_bucket();
                        SASSERT(bt->size() < bt->capacity());
                        skip_list_base<Traits>::update_predecessor_vector(m_pred_vect, bt);
                        sz = bt->size();
                    }
                    else {
                        // last bucket is full... creating new bucket...
                        unsigned new_bucket_lvl = m_manager.random_level(Traits::max_level);
                        bucket * new_bucket     = interval_skip_list::mk_bucket(m_manager, new_bucket_lvl);
                        m_list.update_list_level(m_manager, new_bucket_lvl, m_pred_vect);
                        for (unsigned i = 0; i < new_bucket_lvl; i++) {
                            SASSERT(m_pred_vect[i]->get_next(i) == 0);
                            m_pred_vect[i]->set_next(i, new_bucket);
                            m_pred_vect[i] = new_bucket;
                            SASSERT(m_pred_vect[i]->get_next(i) == 0);
                        }
                        SASSERT(last_bucket() == new_bucket);
                        bt = new_bucket;
                        sz = 0;
                    }
                }
                SASSERT(sz < bt->capacity());
                m_list.inc_ref(m_manager, v);
                bt->expand(1); 
                interval_skip_list::set_entry(bt, sz, b, e, v); 
            }
        }
    };

    /**
       \brief For each i \in [b, e] remove any entry [i->v] if it is in the list.
    */
    void remove(manager & m, key const & b, key const & e) {
        SASSERT(this->leq(b, e));
        if (this->empty())
            return;
        bucket * pred_vect[Traits::max_level]; 
        bucket * curr, * next;

        find_bucket(b, curr, next, pred_vect);

        if (curr == this->m_header) {
            SASSERT(next != 0);
            remove_begin(m, next, b, e, pred_vect);
        }
        else if (next == 0 || this->gt(first_key(next), b)) {
            remove_inside(m, curr, b, e, pred_vect);
        }
        else {
            SASSERT(next != 0);
            SASSERT(this->eq(first_key(next), b));
            remove_begin(m, next, b, e, pred_vect);
        }
    }

    /**
       \brief Remove entry [k->v] for some v, if it is in the list.
    */
    void remove(manager & m, key const & k) {
        remove(m, k, k);
    }

    /**
       \brief Alias for #remove.
    */
    void erase(manager & m, key const & b, key const & e) {
        remove(m, b, e);
    }

    /**
       \brief Alias for #remove.
    */
    void erase(manager & m, key const & k) {
        remove(m, k, k);
    }
    
    /**
       \begin Traverse the list applying the functor f.
       The functor must have a method
       
       bool operator()(key const & b, key const & e, value const & v)

       The method will invoke f(b, e, v) whenever the entries [i -> v] for i \in [b, e] are
       in the list.
       
       If the functor returns false, then the traversal is interrupted.
    */
    template<typename Functor>
    void for_each(Functor & f) const {
        SASSERT(this->m_header->empty());
        bucket * curr = this->first_bucket();
        while (curr != 0) {
            unsigned sz = curr->size();
            for (unsigned i = 0; i < sz; i++) {
                entry const & e = curr->get(i);
                if (!f(e.begin_key(), e.end_key(), e.val()))
                    return;
            }
            curr = curr->get_next(0);
        }
    }

    /**
       \brief Return the next/successor buffer, but skipping buffers that do not contains keys greater than or equal to k.
    */
    bucket * next_bucket(bucket const * bt, key const & k) const {
        bucket * curr = bt->get_next(0); // move to successor
        if (curr == 0)
            return 0;
        unsigned i     = curr->level();
        unsigned max   = i;
        bucket * next  = 0;
        while (i > 0) {
            --i;
            for (;;) {
                next = curr->get_next(i);
                if (next != 0 && this->leq(first_key(next), k)) {
                    TRACE("interval_skip_list", tout << "next_bucket(" << k << "), i: " << i << " skipping #" << this->get_bucket_idx(curr); 
                          tout << ", moving to: #" << this->get_bucket_idx(next) << "\n"; this->display(tout, next););
                    curr = next;
                    if (curr->level() > max) {
                        max = curr->level();
                        i   = curr->level();
                        TRACE("interval_skip_list", tout << "max: " << max << ", curr->level(): " << curr->level() << ", i: " << i << "\n";);
                        break;
                    }
                }
                else {
                    break; 
                }
            }
        }
        SASSERT(i == 0);
        SASSERT(curr->get_next(0) == next);
        SASSERT(next == 0 || lt(k, first_key(next)));
        return curr;
    }

    class iterator;
    friend class iterator;

    class iterator {
        interval_skip_list const * m_list;
        bucket const *             m_curr;
        unsigned                   m_idx;
    public:
        iterator():m_list(0), m_curr(0), m_idx(0) {}
        iterator(interval_skip_list const * l, bucket const * b = 0, unsigned idx = 0):m_list(l), m_curr(b), m_idx(idx) {}
        entry const & operator*() const { return m_curr->get(m_idx); }
        entry const * operator->() const { return &(operator*()); }
        iterator & operator++() { 
            SASSERT(m_curr);
            m_idx++; 
            if (m_idx >= m_curr->size()) { 
                m_idx  = 0;
                m_curr = m_curr->get_next(0);
            }
            return *this; 
        }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        
        bool at_end() const {
            return m_curr == 0;
        }

        /**
           \brief Move the iterator to the next entry of the form ([b, e] -> v) s.t.
           
           1) k in [b, e], or
           2) b > k and for every entry ([b',e']->v') between the old current entry and ([b,e]->v), we 
           have k > e'
           
           If such entry does not exist, then the iterator is moved to the end.
           That is, at_end() returns true.
        */
        void move_to(key const & k) {
            SASSERT(m_curr);
            SASSERT(m_idx < m_curr->size());
            entry const & curr_entry = m_curr->get(m_idx);
            if (m_list->gt(k, curr_entry.end_key())) {
                m_list->find_core(m_curr, m_idx+1, k, m_idx);
                if (m_idx < m_curr->size())
                    return; // found new position
                SASSERT(m_idx == m_curr->size());
                m_curr = m_list->next_bucket(m_curr, k);
                if (m_curr != 0) {
                    // search for k in the current buffer.
                    m_list->find_core(m_curr, k, m_idx);
                    if (m_idx == m_curr->size()) {
                        // k is greater than all keys in the list.
                        m_curr = 0;
                        m_idx  = 0;
                    }
                }
                else {
                    SASSERT(m_curr == 0);
                    m_idx = 0;
                }
            }
        }

        bool operator==(iterator const & it) const { 
            SASSERT(m_list == it.m_list);
            return m_curr == it.m_curr && m_idx == it.m_idx; 
        }

        bool operator!=(iterator const & it) const { 
            SASSERT(m_list == it.m_list);
            return m_curr != it.m_curr; 
        }

        /**
           \brief Take the ownership of the current value and reset it to 0.

           \warning This method should be used with extreme care, since it puts the interval skip list
           in an inconsistent state that must be restored. This method should be only used by developers
           familiar with the interval skip-lists internal invariants.
           For users not familiar with internal invariants, they should only use the reset method in the skip list class
           after this method is invoked.
           
           Store in r the current value.
        */
        template<typename ObjRef>
        void take_curr_ownership(manager & m, ObjRef & r) {
            SASSERT(!at_end());
            entry & curr = const_cast<entry&>(operator*()); // <<< HACK
            r = curr.val();
            if (Traits::ref_count)
                m.dec_ref_eh(curr.val());
            curr.set_val(0);
        }
    };

    iterator begin() const { return iterator(this, this->first_bucket()); }

    iterator end() const { return iterator(this); }

    /**
       \brief Return an iterator starting at the first entry that contains k.
       If the skip-list does not contain k, then return the "end()" iterator.
    */
    iterator find(key const & k) const {
        bucket *  bt;
        unsigned  idx;
        if (find_core<false>(k, bt, idx, 0)) {
            return iterator(this, bt, idx);
        }
        else {
            return end();
        }
    }

    iterator find_geq(key const & k) const {
        bucket *  bt;
        unsigned  idx;
        find_core<false>(k, bt, idx, 0);
        return iterator(this, bt, idx);
    }

    /**
       \brief Return true if the skip lists are equal.
    */
    bool is_equal(interval_skip_list const & other) const {
        iterator it1  = begin();
        iterator end1 = end();
        iterator it2  = other.begin();
        iterator end2 = other.end();
        for (; it1 != end1 && it2 != end2; it1++, it2++) {
            entry const & e1 = *it1;
            entry const & e2 = *it2;
            if (!this->eq(e1.begin_key(), e2.begin_key()))
                return false;
            if (!this->eq(e1.end_key(), e2.end_key()))
                return false;
            if (!this->val_eq(e1.val(), e2.val()))
                return false;
        }
        return true;
    }

    /**
       \brief Update the values stored in the skip-list by appling the given
       functor to them. The functor must provide the operation:
       
       value operator()(value const & v);

       The functor must be injective. That is
       
       x != y implies f(x) != f(y)
    
       If a non-injective functor is used, then the resultant skip-list may
       not be in a consistent state.
    */
    template<typename InjectiveFunction>
    void update_values(manager & m, InjectiveFunction & f) {
        if (!this->empty()) {
            iterator it     = begin();
            iterator it_end = end();
            for (; it != it_end; ++it) {
                entry & curr = const_cast<entry&>(*it);
                value const & old_val = curr.val();
                value new_val   = f(old_val);
                this->inc_ref(m, new_val);
                this->dec_ref(m, old_val);
                curr.set_val(new_val);
            }
            SASSERT(check_invariant());
        }
    }

    class ext_iterator;
    friend class ext_iterator;

    class ext_iterator {
        friend class interval_skip_list; 

        interval_skip_list * m_list;
        bucket *             m_curr;
        unsigned             m_idx;
        bucket *             m_pred_vect[Traits::max_level]; 

        void move_next_bucket() {
            m_list->update_predecessor_vector(m_pred_vect, m_curr);
            m_idx  = 0;
            m_curr = m_curr->get_next(0);
        }

    public:
        ext_iterator():m_list(0), m_curr(0), m_idx(0) {}

        entry const & operator*() const { return m_curr->get(m_idx); }

        entry const * operator->() const { return &(operator*()); }

        ext_iterator & operator++() { 
            SASSERT(m_curr);
            m_idx++; 
            if (m_idx >= m_curr->size())
                move_next_bucket();
            return *this; 
        }

        ext_iterator operator++(int) { ext_iterator tmp = *this; ++*this; return tmp; }
        
        bool at_end() const {
            return m_curr == 0;
        }

        bool operator==(ext_iterator const & it) const { 
            return m_curr == it.m_curr && m_idx == it.m_idx; 
        }

        bool operator!=(ext_iterator const & it) const { 
            return m_curr != it.m_curr; 
        }

        void erase(manager & m) {
            SASSERT(!at_end());
            SASSERT(m_curr->size() > 0);
            if (m_curr->size() > 1) {
                m_list->del_entry(m, m_curr, m_idx);
                if (m_idx >= m_curr->size())
                    move_next_bucket();
            }
            else {
                SASSERT(m_curr->size() == 1);
                bucket * old_curr = m_curr;
                m_curr = m_curr->get_next(0);
                m_list->del_bucket(m, old_curr, m_pred_vect);
            }
        }
    };

    void move_begin(ext_iterator & it) {
        if (!this->empty()) {
            it.m_list = this;
            it.m_curr = this->first_bucket();
            it.m_idx  = 0;
            unsigned lvl = this->level();
            for (unsigned i = 0; i < lvl; i++)
                it.m_pred_vect[i] = this->m_header;
        }
        else {
            it.m_curr = 0;
            it.m_idx  = 0;
        }
    }

    void move_geq(ext_iterator & it, key const & k) {
        it.m_list = this;
        find_core<true>(k, it.m_curr, it.m_idx, it.m_pred_vect);
    }

private:
    /**
       \brief Auxiliary data-structure used to implement the join of two interval_skip_lists.
       To implement an efficient join, we want to be able to skip as many entries as possible.
    */
    struct join_state {
        bucket * m_bucket;
        unsigned m_entry_idx;
        key      m_head; // it it a key in [m_bucket->m_entries[m_entry_idx].begin_key(), m_bucket->m_entries[m_entry_idx].end_key()]
    public:
        join_state(bucket * bt):
            m_bucket(bt),
            m_entry_idx(0),
            m_head(bt->first_entry().begin_key()) {
        }

        bool done() const {
            return m_bucket == 0;
        }

        key const & head() const {
            SASSERT(!done());
            return m_head;
        }

        key const & tail() const {
            SASSERT(!done());
            SASSERT(m_entry_idx < m_bucket->size());
            return m_bucket->get(m_entry_idx).end_key();
        }

        value const & val() const {
            SASSERT(!done());
            return m_bucket->get(m_entry_idx).val();
        }
    };
    
    /**
       \brief Create a join_state auxiliary data-structure for performing a join starting at key k.
    */
    join_state mk_join_state(key const & k) const {
        return join_state(next_bucket(this->m_header, k));
    }
    
    /**
       \brief Move the join_state towards k.
    */
    void move_js(join_state & js, key const & k) const {
        SASSERT(!js.done());
        if (this->leq(k, js.tail())) {
            // We can't skip the current entry, because k in inside it.
            // So, we just update the head.
            js.m_head = k;
        }
        else {
            // Moving to the next entry.
            js.m_entry_idx++;
            if (js.m_entry_idx < js.m_bucket->size()) {
                // Update js.m_head with the beginning of the next entry.
                js.m_head = js.m_bucket->get(js.m_entry_idx).begin_key();
            }
            else {
                // We processed all entries in the current bucket. So, set state to js.m_move_next.
                js.m_bucket    = next_bucket(js.m_bucket, k);
                js.m_entry_idx = 0;
                if (js.m_bucket != 0) 
                    js.m_head      = first_key(js.m_bucket);
            }
        }
    }

public:

    /**
       \brief Join two interval_skip_lists and apply the given functor in the process.

       The functor must have a method
       
       bool operator()(key const & b, key const & e, value const & v1, value const & v2)
       
       The method will invoke f(b, e, v1, v2) whenever forall i \in [b, e] entries [i -> v1] are in the *this* list, and [i->v2] in the *other* list.
    */
    template<typename Functor>
    void join(interval_skip_list const & other, Functor & f) {
        if (this->empty() || other.empty())
            return;
        key const & f1    = smallest();
        key const & f2    = other.smallest();
        key const & smallest_key = leq(f1, f2) ? f1 : f2;
        join_state s1 = mk_join_state(smallest_key);
        join_state s2 = other.mk_join_state(smallest_key);
        while (!s1.done() && !s2.done()) {
            key const & h1 = s1.head();
            key const & h2 = s2.head();
            if (eq(h1, h2)) {
                key const & t1 = s1.tail();
                key const & t2 = s2.tail();
                key const & t  = leq(t1, t2) ? t1 : t2;
                f(h1, t, s1.val(), s2.val());
                key next_key   = succ(t);
                move_js(s1, next_key);
                move_js(s2, next_key);
            }
            else if (lt(h1, h2)) {
                move_js(s1, h2);
            }
            else {
                SASSERT(lt(h2, h1));
                move_js(s2, h1);
            }
        }
    }

#ifdef Z3DEBUG
private:
    bool check_invariant(entry const & e) const {
        SASSERT(this->leq(e.begin_key(), e.end_key()));
        return true;
    }

    /**
       \brief Return true if the last key of \c e1 is less than the first key of \c e2.
    */
    bool lt(entry const & e1, entry const & e2) const {
        return lt(e1.end_key(), e2.begin_key());
    }

    bool check_invariant(bucket const * bt) const {
        SASSERT(bt->size() <= bt->capacity());
        SASSERT(bt == this->m_header || !bt->empty());
        for (unsigned i = 0; i < bt->size(); i++) {
            entry const & curr = bt->get(i);
            check_invariant(curr);
            if (i > 0) {
                entry const & prev = bt->get(i-1);
                CTRACE("interval_skip_list", !lt(prev, curr), this->display_physical(tout););
                SASSERT(lt(prev, curr));
                CTRACE("interval_skip_list", can_be_merged(prev, curr), this->display_physical(tout););
                SASSERT(!can_be_merged(prev, curr));
            }
        }
        return true;
    }

public:
    bool check_invariant() const {
        SASSERT(this->m_header->empty());
        for (unsigned i = 0; i < this->m_header->level(); i++) {
            // traverse buckets using get_next(i) pointers
            bucket const * curr = this->m_header->get_next(i);
            while (curr != 0) {
                SASSERT(!curr->empty()); // only the header is empty.
                bucket const * next = curr->get_next(i);
                if (next != 0) {
                    SASSERT(next->level() >= i);
                    SASSERT(i == 0 || this->is_reachable_at_i(curr, next, i-1));
                    SASSERT(!next->empty());
                    entry const & last_of_curr  = curr->last_entry();
                    entry const & first_of_next = next->first_entry();
                    CTRACE("interval_skip_list", !lt(last_of_curr, first_of_next),
                           this->display_physical(tout);
                           tout << "\ncurr:\n";
                           this->display(tout, curr);
                           tout << "\nnext:\n";
                           this->display(tout, next););
                    SASSERT(lt(last_of_curr, first_of_next));
                    CTRACE("interval_skip_list", can_be_merged(last_of_curr, first_of_next),
                           this->display_physical(tout);
                           tout << "\ncurr:\n";
                           this->display(tout, curr);
                           tout << "\nnext:\n";
                           this->display(tout, next););
                    SASSERT(!can_be_merged(last_of_curr, first_of_next));
                }
                curr = next;
            }
        }
        bucket const * curr = this->m_header;
        while (curr != 0) {
            check_invariant(curr);
            curr = curr->get_next(0);
        }
        return true;
    }
#endif

    static void display_size_info(std::ostream & out) {
        skip_list_base<Traits>::display_size_info_core(out, sizeof(interval_skip_list));
    }
    
    /**
       \brief Return the amount of memory consumed by the list.
    */
    unsigned memory() const {
        return this->memory_core(sizeof(interval_skip_list));
    }

};

/**
   \brief Traits for instantiating a mapping from unsigned to Value using the interval_skip_list template.
*/
template<typename Value, 
         typename EqProc=default_eq<Value>, 
         unsigned MaxCapacity=32, 
         unsigned MaxLevel=32, 
         bool RefCount=false, 
         typename Manager=sl_manager_base<Value> >
struct unsigned_interval_skip_list_traits : private EqProc {
    typedef default_islist_entry<unsigned, Value> entry;
    typedef Manager manager;
    typedef typename entry::key   key;
    typedef typename entry::value value;
    static const unsigned max_capacity     = MaxCapacity;
    static const unsigned initial_capacity = 2;
    static const unsigned max_level        = MaxLevel;
    static const bool     ref_count        = RefCount;

    bool lt(key const & k1, key const & k2) const { return k1 < k2; }
    bool eq(key const & k1, key const & k2) const { return k1 == k2; }
    key succ(key const & k) const { return k + 1; }
    key pred(key const & k) const { SASSERT(k > 0); return k - 1; }
    bool val_eq(value const & v1, value const & v2) const { return EqProc::operator()(v1, v2); }
};

/**
   \brief Traits for instantiating a set of unsigned values using the interval_skip_list template.
*/
template<unsigned MaxCapacity=32, 
         unsigned MaxLevel=32, 
         typename Manager=sl_manager_base<unsigned> >
struct unsigned_set_interval_skip_list_traits {
    typedef default_set_islist_entry<unsigned> entry;
    typedef Manager manager;
    typedef typename entry::key   key;
    typedef typename entry::value value;
    static const unsigned max_capacity     = MaxCapacity;
    static const unsigned initial_capacity = 2;
    static const unsigned max_level        = MaxLevel;
    static const bool     ref_count        = false;

    bool lt(key const & k1, key const & k2) const { return k1 < k2; }
    bool eq(key const & k1, key const & k2) const { return k1 == k2; }
    key succ(key const & k) const { return k + 1; }
    key pred(key const & k) const { SASSERT(k > 0); return k - 1; }
    bool val_eq(value const & v1, value const & v2) const { return true; }
};

/**
   \brief Generic adapater for generating a set-like API on top of the map API
*/
template<typename Map>
class map2set_adapter : public Map {
    typedef typename Map::manager manager;
    typedef typename Map::key     key;
    typedef typename Map::value   value;
    
    template<typename Functor>
    struct for_each_functor_adapter : public Functor {
        for_each_functor_adapter(Functor const & f):Functor(f) {
        }
        bool operator()(key const & b, key const & e, value const & v) {
            return Functor::operator()(b, e);
        }
    };

public:
    map2set_adapter(manager & m):
        Map(m) {
        SASSERT(this->m_header != 0);
    }

    void insert(manager & m, key const & b, key const & e) {
        value _dummy;
        Map::insert(m, b, e, _dummy);
    }

    void insert(manager & m, key const & k) {
        value _dummy;
        Map::insert(m, k, k, _dummy);
    }

    bool contains(key const & k) const {
        value _dummy;
        return Map::contains(k);
    }

    bool find(key const & k) const {
        return contains(k);
    }

    /**
       \begin Traverse the set applying the functor f.
       The functor must have a method
       
       bool operator()(key const & b, key const & e)

       The method will invoke f(b, e) whenever the interval [b, e] are
       in the set.
       
       If the functor returns false, then the traversal is interrupted.
    */
    template<typename Functor>
    void for_each(Functor & f) const {
        for_each_functor_adapter<Functor> F(f);
        Map::for_each(F);
    }
};


/**
   \brief A set of unsigned values using interval_skip_list.
*/
template<unsigned MaxCapacity=32, unsigned MaxLevel=32, typename Manager=sl_manager_base<unsigned> >
class unsigned_isp_set : public map2set_adapter<interval_skip_list<unsigned_set_interval_skip_list_traits<MaxCapacity, MaxLevel, Manager> > > {
public:
    unsigned_isp_set(Manager & m):
        map2set_adapter<interval_skip_list<unsigned_set_interval_skip_list_traits<MaxCapacity, MaxLevel, Manager> > >(m) {
    }
};

#endif /* _INTERVAL_SKIP_LIST_H_ */

    
