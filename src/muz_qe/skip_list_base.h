/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    skip_list_base.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-10-01.

Revision History:

   WARNING: IT IS NOT SAFE TO STORE KEYS, VALUES in the SKIP_LIST that need non-default constructors/destructors.

--*/
#ifndef _SKIP_LIST_BASE_H_
#define _SKIP_LIST_BASE_H_

#include<memory.h>
#include"util.h"
#include"memory_manager.h"
#include"small_object_allocator.h"
#include"trace.h"

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#endif

/*
  This file defines a base class for implementing skip-list like data-structures.
  This base class is relies on a manager for providing some basic services.
  The manager is a template parameter.

  A Skip-list manager is responsible for:

  - Providing primitives for allocating/deallocating memory
         void * allocate(size_t size);
         void deallocate(size_t size, void* p);
  - Generating random skip-list levels efficiently
         unsigned random_level(unsigned max_level);
  - Call-backs that will be invoked when a reference for a "value" stored in the skip-list is incremented/decremented.
         void inc_ref_eh(value const & v);
         void dec_ref_eh(value const & h);
*/

/**
   \brief Base class for generating random_levels.
*/
class random_level_manager {
#define SL_BITS_IN_RANDOM 16
    unsigned m_random_data;
    unsigned m_random_bits:16;
    unsigned m_random_left:16;
    
    unsigned random_value() {
        return ((m_random_data = m_random_data * 214013L + 2531011L) >> 16) & 0xffff; 
    }

    void init_random() {
        m_random_data = 0;
        m_random_bits = random_value();
        m_random_left = SL_BITS_IN_RANDOM/2;
    }
public:
    random_level_manager() {
        init_random();
    }

    unsigned random_level(unsigned max_level) {
        unsigned level = 1;
        unsigned b;
        do {
            b = m_random_bits&3; 
            if (!b) 
                level++;
            m_random_bits >>= 2;
            m_random_left--;
            if (m_random_left == 0) {
                m_random_bits = random_value();
                m_random_left = SL_BITS_IN_RANDOM/2;
            }
        } while (!b);
        return (level > max_level ? max_level : level);
    }
    
};

/**
   \brief Basic skip-list manager. 
   The class is parametrized by the Value type that is stored in the skip-list.
*/
template<typename Value>
class sl_manager_base : public random_level_manager {
    typedef Value value;

    small_object_allocator m_alloc;

public:
    void * allocate(size_t size) {
        return m_alloc.allocate(size);
    }
    
    void deallocate(size_t size, void* p) {
        m_alloc.deallocate(size, p);
    }

    void inc_ref_eh(value const & v) {
        /* do nothing */
    }

    void dec_ref_eh(value const & h) {
        /* do nothing */
    }
};

#define SL_SIZE_NUM_BITS 12
#define SL_CAPACITY_NUM_BITS SL_SIZE_NUM_BITS
#define SL_MAX_CAPACITY ((1 << SL_SIZE_NUM_BITS) - 1)
#define SL_LEVEL_NUM_BITS    8
#define SL_MAX_LEVEL ((1 << SL_LEVEL_NUM_BITS) - 1)
COMPILE_TIME_ASSERT(SL_SIZE_NUM_BITS == SL_CAPACITY_NUM_BITS);
COMPILE_TIME_ASSERT(SL_SIZE_NUM_BITS + SL_CAPACITY_NUM_BITS + SL_LEVEL_NUM_BITS == 32);

/**
   \brief Base (template) class for implementing skip-list like data-structures where
   entries are stored in buckets to improve cache behavior.

   The Traits template parameter must provide:
   
   - a definition for the class Traits::manager
   - a definition for the class Traits::entry which provides:
      - a definition for the types key and value
      - the methods: 
          key const & begin_key() const
          key const & end_key() const
          value const & val() const
          void set_begin_key(key const & k)
          void set_end_key(key const & k)
          void set_val(value const & v)
          void display(ostream & out) const
   - the maximal number of levels Traits::max_level
   - the maximal capacity of each bucket  Traits::max_capacity
   - the initial capacity of the first bucket Traits::initial_capacity
   - flag for reference counting support Traits::ref_count. If this flag is true
     the methods inc_ref_eh and dec_ref_eh in the manager object will be invoked.
   - the methods
        bool lt(key const & k1, key const & k2)
        bool eq(key const & k1, key const & k2)
        bool val_eq(value const & v1, value const & v2)
        key succ(key const & k)   
        key pred(key const & k)
*/
template<typename Traits>
class skip_list_base : protected Traits {
protected:
    typedef typename Traits::entry   entry;
public:
    typedef typename Traits::manager manager;
    typedef typename entry::key      key;
    typedef typename entry::value    value;

    struct bucket {
        unsigned   m_size:SL_SIZE_NUM_BITS;          //!< number of entries stored in the bucket.
        unsigned   m_capacity:SL_CAPACITY_NUM_BITS;  //!< capacity (number of entries) that can be stored in the bucket.
        unsigned   m_level:SL_LEVEL_NUM_BITS; 
        char       m_extra[0];
    
        static unsigned get_obj_size(unsigned num_lvls, unsigned capacity) {
            return sizeof(bucket) + num_lvls*sizeof(bucket*) + capacity*sizeof(entry);
        }

        entry * get_entries() { return reinterpret_cast<entry*>(m_extra); }
        entry const * get_entries() const { return reinterpret_cast<entry const *>(m_extra); }
        
        bucket ** next_vect() { return reinterpret_cast<bucket**>(get_entries() + m_capacity); }
        bucket * const * next_vect() const { return reinterpret_cast<bucket* const *>(get_entries() + m_capacity); }
    
        bucket(unsigned lvl, unsigned capacity = Traits::max_capacity):
            m_size(0),
            m_capacity(capacity),
            m_level(lvl) {
            memset(next_vect(), 0, sizeof(bucket*)*lvl);
        }
    
        unsigned level() const { return m_level; }
        unsigned size() const { return m_size; }
        unsigned capacity() const { return m_capacity; }
        bool empty() const { return size() == 0; }
        void set_size(unsigned sz) { m_size = sz; }
        void shrink(unsigned delta) { m_size -= delta; }
        void expand(unsigned delta) { m_size += delta; }
        entry & first_entry() { SASSERT(!empty()); return get_entries()[0]; } 
        entry & last_entry() { SASSERT(!empty()); return get_entries()[size() - 1]; }
        entry const & first_entry() const { SASSERT(!empty()); return get_entries()[0]; } 
        entry const & last_entry() const { SASSERT(!empty()); return get_entries()[size() - 1]; }
        entry const & get(unsigned idx) const { SASSERT(idx < size()); return get_entries()[idx]; }
        entry & get(unsigned idx) { SASSERT(idx < size()); return get_entries()[idx]; }
        void set(unsigned idx, entry const & e) { SASSERT(idx < capacity()); get_entries()[idx] = e; }
        bucket * get_next(unsigned idx) const { return next_vect()[idx]; }
        void set_next(unsigned idx, bucket * bt) { SASSERT(idx < level()); next_vect()[idx] = bt; }
    };

    // Only the header bucket has zero entries.
    bucket * m_header;
    
    bucket * first_bucket() const {
        return m_header->get_next(0);
    }

#ifdef Z3DEBUG
    /**
       \brief (debugging only) Return the predecessor bucket of the given bucket.
       
       \pre bt != m_header, and bt is a bucket of the list.
    */
    bucket * pred_bucket(bucket * bt) const {
        SASSERT(bt != m_header);
        bucket * curr = m_header;
        while (curr->get_next(0) != bt) {
            curr = curr->get_next(0);
            SASSERT(curr != 0); // bt is not in the list
        }
        return curr;
    }
#endif

    bool lt(key const & k1, key const & k2) const { return Traits::lt(k1, k2); }

    bool gt(key const & k1, key const & k2) const { return lt(k2, k1); }

    bool geq(key const & k1, key const & k2) const { return !lt(k1, k2); }

    bool leq(key const & k1, key const & k2) const { return !gt(k1, k2); }
    
    /**
       \brief Create a new bucket of the given level.
    */
    static bucket * mk_bucket(manager & m, unsigned lvl, unsigned capacity = Traits::max_capacity) {
        void * mem = m.allocate(bucket::get_obj_size(lvl, capacity));
        return new (mem) bucket(lvl, capacity);
    }

    static bucket * mk_header(manager & m, unsigned lvl) {
        return mk_bucket(m, lvl, 0);
    }

    static void inc_ref(manager & m, value const & v) {
        if (Traits::ref_count)
            m.inc_ref_eh(v);
    }

    static void dec_ref(manager & m, value const & v) {
        if (Traits::ref_count)
            m.dec_ref_eh(v);
    }

    /**
       \brief Invoke dec_ref_eh for each value stored in the bucket.
    */
    static void dec_ref(manager & m, bucket * bt) {
        if (Traits::ref_count) {
            unsigned sz = bt->size();
            for (unsigned i = 0; i < sz; i++)
                m.dec_ref_eh(bt->get(i).val());
        }
    }

    /**
       \brief Deallocate the given bucket.
       
       \remark This method invokes dec_ref_eh for each value in the bucket.
    */
    template<bool DecRef>
    static void deallocate_bucket(manager & m, bucket * bt) {
        if (DecRef)
            dec_ref(m, bt);
        unsigned sz = bucket::get_obj_size(bt->level(), bt->capacity());
        bt->~bucket();
        m.deallocate(sz, bt);
    }

    /**
       \brief Deallocate all buckets in the skip list.
       
       \remark This method invokes dec_ref_eh for each value in the list.
    */
    template<bool DecRef>
    void deallocate_list(manager & m) {
        bucket * curr = m_header;
        while (curr != 0) {
            bucket * old = curr;
            curr = curr->get_next(0);
            deallocate_bucket<DecRef>(m, old);
        }
    }

#ifdef Z3DEBUG
    /**
       \brief Check the following property
       
       for all i \in [0, b->level()) . pred_vect[i]->get_next(i) == b
    */
    bool check_pred_vect(bucket * bt, bucket * pred_vect[]) {
        if (bt == 0) 
            return true;
        for (unsigned i = 0; i < bt->level(); i++) {
            SASSERT(pred_vect[i]->get_next(i) == bt);
        }
        return true;
    }
#endif

    /**
       \brief Delete the given buffer and update the forward/next pointer of the buckets in pred_vect.
       
       \remark This method invokes dec_ref_eh for each value in the bucket.
    */
    void del_bucket(manager & m, bucket * bt, bucket * pred_vect[]) {
        SASSERT(check_pred_vect(bt, pred_vect));
        for (unsigned i = 0; i < bt->level(); i++)
            pred_vect[i]->set_next(i, bt->get_next(i));
        deallocate_bucket<true>(m, bt);
    }

    /**
       \brief Update the \c pred_vect vector from levels [0, bt->level()).
       That is, bt will be now the "predecessor" for these levels.
    */
    static void update_predecessor_vector(bucket * pred_vect [], bucket * bt) {
        unsigned lvl = bt->level();
        for (unsigned i = 0; i < lvl; i++) {
            pred_vect[i] = bt;
        }
    }

    /**
       \brief Similar to the previous method, but the updated vector is stored in new_pred_vect.
    */
    void update_predecessor_vector(bucket * pred_vect[], bucket * bt, bucket * new_pred_vect[]) {
        unsigned bt_lvl = bt->level();
        for (unsigned i = 0; i < bt_lvl; i++) {
            new_pred_vect[i] = bt;
        }
        unsigned list_lvl = level();
        for (unsigned i = bt_lvl; i < list_lvl; i++) {
            new_pred_vect[i] = pred_vect[i];
        }
    }

    /**
       \brief Return the list level.
    */
    unsigned level() const {
        return m_header->level();
    }

    /**
       \brief Expand/Increase the number of levels in the header.
    */
    void expand_header(manager & m, unsigned new_lvl) {
        SASSERT(new_lvl > level());
        bucket * new_header = mk_header(m, new_lvl);
        // copy forward pointers of the old header.
        unsigned old_lvl    = level();
        for (unsigned i = 0; i < old_lvl; i++)
            new_header->set_next(i, m_header->get_next(i));
        // update header
        deallocate_bucket<false>(m, m_header);
        m_header = new_header;
    }

    /**
       \brief Increase list level to lvl if lvl > level()
    */
    void update_list_level(manager & m, unsigned lvl) {
        if (lvl > level()) {
            expand_header(m, lvl);
        }
    }

    /**
       \brief Increase list level (and store m_header in the new levels in pred_vect) if lvl > level().
    */
    void update_list_level(manager & m, unsigned lvl, bucket * pred_vect[]) {
        if (lvl > level()) {
            bucket * old_header = m_header;
            unsigned old_lvl    = m_header->level();
            expand_header(m, lvl);
            for (unsigned i = 0; i < old_lvl; i++) {
                if (pred_vect[i] == old_header)
                    pred_vect[i] = m_header;
            }
            for (unsigned i = old_lvl; i < lvl; i++) {
                pred_vect[i] = m_header;
            }
            SASSERT(level() == lvl);
        }
    }

    /**
       \brief Add first entry to the list.

       \remark This method will invoke inc_ref_eh for e.val()
    */
    void insert_first_entry(manager & m, entry const & e) {
        unsigned lvl        = m.random_level(Traits::max_level);
        bucket * new_bucket = mk_bucket(m, lvl, Traits::initial_capacity);
        update_list_level(m, lvl);
        for (unsigned i = 0; i < lvl; i++) {
            m_header->set_next(i, new_bucket);
        }
        inc_ref(m, e.val());
        new_bucket->set_size(1);
        new_bucket->set(0, e);
    }

    /**
       \brief Expand the capacity of the first-bucket in a skip-list with only one bucket.
       This method assumes the capacity of the first-bucket < Traits::max_capacity
     */
    void expand_first_bucket(manager & m) {
        bucket * f = first_bucket();
        SASSERT(f != 0);
        SASSERT(f->get_next(0) == 0);
        SASSERT(f->capacity() < Traits::max_capacity);
        unsigned old_capacity = f->capacity();
        SASSERT(old_capacity > 0);
        unsigned new_capacity = old_capacity * 2;
        if (new_capacity > Traits::max_capacity)
            new_capacity = Traits::max_capacity;
        unsigned lvl = f->level();
        bucket * new_f = mk_bucket(m, lvl, new_capacity);
        unsigned sz = f->size();
        new_f->set_size(sz);
        for (unsigned i = 0; i < sz; i++) 
            new_f->set(i, f->get(i));
        for (unsigned i = 0; i < lvl; i++)
            m_header->set_next(i, new_f);
        deallocate_bucket<false>(m, f);
        SASSERT(first_bucket() == new_f);
    }

    /**
       \brief Create a new bucket and divide the elements in bt between bt and the new bucket.
    */
    void splice(manager & m, bucket * bt, bucket * pred_vect[]) {
        SASSERT(bt->capacity() == Traits::max_capacity);
        unsigned bt_lvl         = bt->level();
        unsigned new_bucket_lvl = m.random_level(Traits::max_level);
        bucket * new_bucket     = mk_bucket(m, new_bucket_lvl);
        update_list_level(m, new_bucket_lvl, pred_vect);
        unsigned _lvl           = std::min(bt_lvl, new_bucket_lvl);
        for (unsigned i = 0; i < _lvl; i++) {
            new_bucket->set_next(i, bt->get_next(i));
            bt->set_next(i, new_bucket);
        }
        for (unsigned i = bt_lvl; i < new_bucket_lvl; i++) {
            new_bucket->set_next(i,   pred_vect[i]->get_next(i));
            pred_vect[i]->set_next(i, new_bucket);
        }
        unsigned old_size  = bt->size();
        SASSERT(old_size >= 2);
        unsigned mid              = old_size/2;
        new_bucket->set_size(old_size - mid);
        unsigned i = mid;
        unsigned j = 0;
        for (; i < old_size; i++, j++) {
            new_bucket->set(j, bt->get(i));
        }
        bt->set_size(mid);
        SASSERT(!bt->empty());
        SASSERT(!new_bucket->empty());
    }
    
    /**
       \brief Open space at position idx. The number of entries in bt is increased by one.

       \remark This method will *NOT* invoke inc_ref_eh
    */
    void open_space(bucket * bt, unsigned idx) {
        SASSERT(bt->size() < bt->capacity());
        SASSERT(idx <= bt->size());
        unsigned i = bt->size();
        while (i > idx) {
            bt->set(i, bt->get(i-1));
            i--;
        }
        bt->expand(1);
    }

    /**
       \brief Open two spaces at position idx. The number of entries in bt is increased by one.

       \remark This method will *NOT* invoke inc_ref_eh
    */
    void open_2spaces(bucket * bt, unsigned idx) {
        SASSERT(bt->size() < bt->capacity() - 1);
        SASSERT(idx <= bt->size());
        unsigned i = bt->size() + 1;
        unsigned end = idx + 1;
        while (i > end) {
            bt->set(i, bt->get(i-2));
            i--;
        }
        bt->expand(2);
    }

    /**
       \brief Delete entry at position idx.

       \remark This method will invoke dec_ref_eh for the value stored in entry at position idx.
    */
    void del_entry(manager & m, bucket * bt, unsigned idx) {
        SASSERT(!bt->empty());
        SASSERT(idx < bt->size());
        dec_ref(m, bt->get(idx).val());
        unsigned sz = bt->size();
        for (unsigned i = idx; i < sz - 1; i++) {
            bt->set(i, bt->get(i+1));
        }
        bt->shrink(1);
    }

    /**
       \brief Create a copy of the skip list.

       \remark This method will invoke inc_ref_eh for all values copied.
    */
    void clone_core(manager & m, skip_list_base * new_list) const {
        bucket * pred_vect[Traits::max_level]; 
        unsigned lvl = level();
        new_list->update_list_level(m, lvl);
        bucket * new_header = new_list->m_header;
        for (unsigned i = 0; i < lvl; i++)
            pred_vect[i] = new_header;
        bucket * curr = first_bucket();
        while (curr != 0) {
            unsigned curr_lvl   = curr->level();
            bucket * new_bucket = new_list->mk_bucket(m, curr_lvl, curr->capacity());
            for (unsigned i = 0; i < curr_lvl; i++) {
                pred_vect[i]->set_next(i, new_bucket);
                pred_vect[i]            = new_bucket;
            }
            unsigned curr_sz    = curr->size();
            for (unsigned i = 0; i < curr_sz; i++) {
                entry const & curr_entry = curr->get(i);
                inc_ref(m, curr_entry.val());
                new_bucket->set(i, curr_entry);
            }
            new_bucket->set_size(curr_sz);
            curr = curr->get_next(0);
        }
    }

public:
    skip_list_base():
        m_header(0) {
        SASSERT(Traits::max_capacity >= 2);
        SASSERT(Traits::initial_capacity >= 2);
        SASSERT(Traits::initial_capacity <= Traits::max_capacity);
        SASSERT(Traits::max_level >= 1);
        SASSERT(Traits::max_capacity <= SL_MAX_CAPACITY);
        SASSERT(Traits::max_level <= SL_MAX_LEVEL);
    }

    skip_list_base(manager & m):
        m_header(0) {
        SASSERT(Traits::max_capacity >= 2);
        SASSERT(Traits::initial_capacity >= 2);
        SASSERT(Traits::initial_capacity <= Traits::max_capacity);
        SASSERT(Traits::max_level >= 1);
        SASSERT(Traits::max_capacity <= SL_MAX_CAPACITY);
        SASSERT(Traits::max_level <= SL_MAX_LEVEL);
        init(m);
    }

    ~skip_list_base() {
        SASSERT(m_header == 0);
    }

    void deallocate(manager & m) {
        deallocate_list<true>(m);
        m_header = 0;
    }
    
    /**
       \brief Deallocate the list but do not invoke dec_ref_eh.
    */
    void deallocate_no_decref(manager & m) {
        deallocate_list<false>(m);
        m_header = 0;
    }

    /**
       \brief Initialize a list that was created using the default constructor.
       It can be used also to initialized a list deallocated using the method #deallocate.
    */
    void init(manager & m) {
        SASSERT(m_header == 0);
        m_header = mk_header(m, 1);
    }

    /**
       \brief Remove all elements from the skip-list.
    */
    void reset(manager & m) {        
        deallocate_list<true>(m);
        m_header = mk_header(m, 1);
    }

    /**
       \brief Remove all elements from the skip-list without invoking dec_ref_eh.
    */
    void reset_no_decref(manager & m) {        
        deallocate_list<false>(m);
        m_header = mk_header(m, 1);
    }
    
    /**
       \brief Return true if the list is empty.
    */
    bool empty() const {
        SASSERT(m_header != 0);
        return first_bucket() == 0;
    }
    
protected:
    /**
       \brief Return the position of the bucket in the skip list.
    */
    unsigned get_bucket_idx(bucket const * bt) const {
        bucket * curr = m_header;
        unsigned pos  = 0;
        while (curr != 0) {
            if (curr == bt)
                return pos;
            pos++;
            curr = curr->get_next(0);
        }
        UNREACHABLE();
        return pos;
    }

    /**
       \brief Display the given entry.
    */
    void display(std::ostream & out, entry const & e) const {
        e.display(out);
    }

    /**
       \brief Display a reference to the given bucket.
    */
    void display_bucket_ref(std::ostream & out, bucket const * bt) const {
        if (bt == 0)
            out << "NIL";
        else
            out << "#" << get_bucket_idx(bt);
    }

    /**
       \brief Display the predecessor vector.
    */
    void display_predecessor_vector(std::ostream & out, bucket const * const pred_vect[]) const {
        for (unsigned i = 0; i < level(); i++) {
            out << i << ": ";
            display_bucket_ref(out, pred_vect[i]);
            if (pred_vect[i]) {
                out << " -> ";
                display_bucket_ref(out, pred_vect[i]->get_next(i));
            }
            out << "\n";
        }
    }

    /**
       \brief Display the successors of the given bucket.
    */
    void display_successors(std::ostream & out, bucket const * bt) const {
        out << "[";
        for (unsigned i = 0; i < bt->level(); i++) {
            if (i > 0) out << ", ";
            display_bucket_ref(out, bt->get_next(i));
        }
        out << "]";
    }

    /**
       \brief Display the given bucket.
    */
    void display(std::ostream & out, bucket const * bt) const {
        if (bt == 0) {
            out << "NIL\n";
            return;
        }
        out << "bucket ";
        display_bucket_ref(out, bt);
        out << ", capacity: " << bt->capacity() << "\n";
        out << "successors: ";
        display_successors(out, bt);
        out << "\n";
        out << "entries:\n";
        for (unsigned i = 0; i < bt->size(); i++) {
            display(out, bt->get(i));
            out << "\n";
        }
        out << "----------\n";
    }

public:
    /**
       \brief Dump the skip list for debugging purposes. 
       It assumes that key and value types implement operator <<.
    */
    void display_physical(std::ostream & out) const {
        out << "{\nskip-list level: " << m_header->level() << "\n";
        bucket * curr = m_header;
        while (curr != 0) {
            display(out, curr);
            curr = curr->get_next(0);
        }
        out << "}\n";
    }

    void display(std::ostream & out) const {
        bucket * curr = m_header;
        while (curr != 0) {
            unsigned sz = curr->size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0)
                    out << " ";
                curr->get(i).display(out);
            }
            curr = curr->get_next(0);
        }
    }

protected:
    /**
       \brief Return true if bucket b2 can be reached from b1 following get_next(i) pointers
    */
    bool is_reachable_at_i(bucket const * bt1, bucket const * bt2, unsigned i) const {
        bucket * curr = bt1->get_next(i);
        while (curr != 0) {
            if (curr == bt2)
                return true;
            curr = curr->get_next(i);
        }
        return false;
    }

protected:
    static void display_size_info_core(std::ostream & out, unsigned cls_size) {
        out << "sizeof root:          " << cls_size << "\n";
        out << "bucket max capacity:  " << Traits::max_capacity << "\n";
        out << "bucket max level:     " << Traits::max_level << "\n";
        out << "sizeof(bucket):       " << sizeof(bucket) << " + " << sizeof(bucket*) << "*lvl + " << sizeof(entry) << "*capacity\n";
        out << "sizeof(usual bucket): " << (sizeof(bucket) + sizeof(entry)*Traits::max_capacity) << " + " << sizeof(bucket*) << "*lvl\n";
        out << "sizeof(max. bucket):  " << (sizeof(bucket) + sizeof(entry)*Traits::max_capacity + sizeof(bucket*)*Traits::max_level) << "\n";
        out << "sizeof(entry):        " << sizeof(entry) << "\n";
        out << "sizeof empty:         " << cls_size + bucket::get_obj_size(1, 0) << "\n";;
        out << "sizeof singleton:    [" 
            << (cls_size + bucket::get_obj_size(1, 0) + bucket::get_obj_size(1, Traits::initial_capacity)) << ", "
            << (cls_size + 
                bucket::get_obj_size(Traits::max_level, 0) + 
                bucket::get_obj_size(Traits::max_level, Traits::max_capacity)) << "]\n";
    }

public:
    /**
       \brief Return true if skip-list has more than k buckets (not considering the header).

       \remark This method is for debugging purposes.
    */
    bool has_more_than_k_buckets(unsigned k) const {
        bucket * curr = first_bucket();
        while (curr != 0 && k > 0) {
            curr = curr->get_next(0);
            k--;
        }
        return curr != 0;
    }
    
    /**
       \brief Return true if the skip-list has more than k entries.
    */
    bool has_more_than_k_entries(unsigned k) const {
        bucket * curr = first_bucket();
        while (curr != 0 && k >= curr->size()) {
            k -= curr->size();
            curr = curr->get_next(0);
        }
        SASSERT(curr == 0 || curr->size() > k);
        return curr != 0;
    }

protected:
    /**
       \brief Return the amount of memory consumed by the list.
    */
    unsigned memory_core(unsigned cls_size) const {
        unsigned r    = 0;
        r += cls_size;
        bucket * curr = m_header;
        while (curr != 0) {
            r += bucket::get_obj_size(curr->level(), curr->capacity());
            curr = curr->get_next(0);
        }
        return r;
    }

public:
    /**
       \brief Compress the buckets of the skip-list.
       Make sure that all, but the last bucket, have at least \c load entries.
       
       \remark If load > Traits::max_capacity, then it assumes load = Traits::max_capacity.
    */
    void compress(manager & m, unsigned load = Traits::max_capacity/2) {
        if (load > Traits::max_capacity)
            load = Traits::max_capacity;
        bucket * pred_vect[Traits::max_level]; 
        update_predecessor_vector(pred_vect, m_header);
        bucket * curr = first_bucket();
        while (curr != 0) {
            update_predecessor_vector(pred_vect, curr);
            bucket * next    = curr->get_next(0);
            while (curr->size() < load && next != 0) {
                // steal entries of the successor bucket.
                unsigned deficit   = load - curr->size();
                unsigned next_size = next->size(); 
                if (next_size <= deficit) {
                    for (unsigned i = 0, j = curr->size(); i < next_size; i++, j++) {
                        curr->set(j, next->get(i));
                    }
                    curr->expand(next_size);
                    bucket * new_next = next->get_next(0);
                    del_bucket(m, next, pred_vect);
                    next = new_next;
                    SASSERT(curr->size() <= load);
                }
                else {
                    for (unsigned i = 0, j = curr->size(); i < deficit; i++, j++) {
                        curr->set(j, next->get(i));
                    }
                    curr->expand(deficit);
                    for (unsigned i = deficit, j = 0; i < next_size; i++, j++) {
                        next->set(j, next->get(i));
                    }
                    next->set_size(next_size - deficit);
                    SASSERT(curr->size() == load);
                }
            }
            curr = curr->get_next(0);
        }
    }

    void swap(skip_list_base & other) {
        bucket * tmp   = m_header;
        m_header       = other.m_header;
        other.m_header = tmp;
    }
};


#endif
