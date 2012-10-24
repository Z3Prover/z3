/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    imdd.h

Abstract:

    Interval based Multiple-valued Decision Diagrams.

Author:

    Leonardo de Moura (leonardo) 2010-10-13.

Revision History:

--*/
#ifndef _IMDD_H_
#define _IMDD_H_

#include"id_gen.h"
#include"hashtable.h"
#include"map.h"
#include"obj_hashtable.h"
#include"obj_pair_hashtable.h"
#include"buffer.h"
#include"interval_skip_list.h"
#include"region.h"
#include"obj_ref.h"

class imdd;
class imdd_manager;

/**
   \brief Manager for skip-lists used to implement IMDD nodes.
*/
class sl_imdd_manager : public random_level_manager {
    imdd_manager *           m_manager; // real manager
    small_object_allocator & m_alloc;
    friend class imdd_manager;
public:
    sl_imdd_manager(small_object_allocator & alloc):m_alloc(alloc) {}
    void * allocate(size_t size) { return m_alloc.allocate(size); }
    void deallocate(size_t size, void* p) { m_alloc.deallocate(size, p); }
    void inc_ref_eh(imdd * v);
    void dec_ref_eh(imdd * v);
};

#define IMDD_BUCKET_CAPACITY 128
#define IMDD_MAX_LEVEL       32

typedef interval_skip_list<unsigned_interval_skip_list_traits<imdd*,
    default_eq<imdd*>,
    IMDD_BUCKET_CAPACITY,
    IMDD_MAX_LEVEL,
    true, /* support ref-counting */
    sl_imdd_manager> > imdd_children;

typedef interval_skip_list<unsigned_interval_skip_list_traits<unsigned,
    default_eq<unsigned>,
    IMDD_BUCKET_CAPACITY,
    IMDD_MAX_LEVEL,
    false,
    sl_manager_base<unsigned> > > sl_interval_set; 

/*
  Notes:
  
  - We use reference counting for garbage collecting IMDDs nodes.

  - Each IMDD node has a "memoized" flag. If the flag is true, the we use hash-consing for this node.

  - The children of a memoized node must be memoized.

  - The children of a non-memoized node may be memoized.

  - The "memoized" flag cannot be reset after it was set.

  - The result of some operations may be cached. We only use caching for
    operations processing memoized nodes.

  - For non-memoized nodes, if m_ref_count <= 1, destructive updates may be performed by some operations.

  - IMPORTANT: "memoized" flag == false doesn't imply m_ref_count <= 1. 
*/


/**
   \brief IMDDs
*/
class imdd {

protected:
    friend class imdd_manager;
    
    unsigned       m_id; //!< Unique ID
    unsigned       m_ref_count;
    unsigned       m_arity:30;
    unsigned       m_memoized:1;   
    unsigned       m_dead:1;     
    imdd_children  m_children;

    void inc_ref() {
        m_ref_count ++;
    }

    void dec_ref() {
        SASSERT(m_ref_count > 0);
        m_ref_count --;
    }

    void mark_as_memoized(bool flag = true) {
        SASSERT(is_memoized() != flag);
        m_memoized = flag;
    }
    
    void mark_as_dead() { SASSERT(!m_dead); m_dead = true; }

    void replace_children(sl_imdd_manager & m, sbuffer<imdd_children::entry> & new_children);
    
public:
    imdd(sl_imdd_manager & m, unsigned id, unsigned arity):m_id(id), m_ref_count(0), m_arity(arity), m_memoized(false), m_dead(false), m_children(m) {}
    unsigned get_id() const { return m_id; }
    unsigned get_ref_count() const { return m_ref_count; }
    bool is_memoized() const { return m_memoized; }
    bool is_shared() const { return m_ref_count > 1; }
    bool is_dead() const { return m_dead; }
    unsigned get_arity() const { return m_arity; }
    imdd_children::iterator begin_children() const { return m_children.begin(); }
    imdd_children::iterator end_children() const { return m_children.end(); }
    unsigned hc_hash() const; // hash code for hash-consing.
    bool hc_equal(imdd const * other) const; // eq function for hash-consing
    bool empty() const { return m_children.empty(); }
    unsigned hash() const { return m_id; }
    unsigned memory() const { return sizeof(imdd) + m_children.memory() - sizeof(imdd_children); }
};

// -----------------------------------
//
// IMDD hash-consing
//
// -----------------------------------

// this is the internal hashing functor for hash-consing IMDDs.
struct imdd_hash_proc {
    unsigned operator()(imdd const * d) const { return d->hc_hash(); }
};

// This is the internal comparison functor for hash-consing IMDDs.
struct imdd_eq_proc {
    bool operator()(imdd const * d1, imdd const * d2) const { return d1->hc_equal(d2); }
};

typedef ptr_hashtable<imdd, imdd_hash_proc, imdd_eq_proc> imdd_table;
typedef obj_hashtable<imdd> imdd_cache;
typedef obj_map<imdd, imdd*> imdd2imdd_cache;
typedef obj_pair_map<imdd, imdd, imdd*> imdd_pair2imdd_cache;
typedef obj_pair_map<imdd, imdd, bool> imdd_pair2bool_cache;
typedef obj_map<imdd, sl_interval_set*> imdd2intervals;

typedef std::pair<imdd*, unsigned> imdd_value_pair;

struct fi_cache_entry {
    imdd *          m_d;
    unsigned        m_lower;
    unsigned        m_upper;
    unsigned        m_hash;
    unsigned        m_num_result;
    imdd_value_pair m_result[0];

    void mk_hash() {
        m_hash = hash_u_u(m_d->get_id(), hash_u_u(m_lower, m_upper));
    }
    
    fi_cache_entry(imdd * d, unsigned l, unsigned u):
        m_d(d), 
        m_lower(l),
        m_upper(u) {
        mk_hash();
    }

    fi_cache_entry(imdd * d, unsigned l, unsigned u, unsigned num, imdd_value_pair result[]):
        m_d(d),
        m_lower(l),
        m_upper(u),
        m_num_result(num) {
        mk_hash();
        memcpy(m_result, result, sizeof(imdd_value_pair)*num);
    }

    unsigned hash() const { 
        return m_hash; 
    }
    
    bool operator==(fi_cache_entry const & other) const {
        return 
            m_d     == other.m_d &&
            m_lower == other.m_lower &&
            m_upper == other.m_upper;
    }
};

typedef obj_hashtable<fi_cache_entry> imdd_fi_cache;
typedef union {
    imdd *           m_d;
    fi_cache_entry * m_entry;
} mk_fi_result;

struct filter_cache_entry {
    imdd *          m_d;
    imdd *          m_r;
    unsigned        m_hash;
    unsigned        m_ctx_size;
    unsigned        m_ctx[0];    // lower and upper bounds that are part of the context.
    
    static unsigned get_obj_size(unsigned ctx_size) {
        return sizeof(filter_cache_entry) + ctx_size * sizeof(unsigned);
    }
    
    void mk_hash() {
        if (m_ctx_size > 0)
            m_hash = string_hash(reinterpret_cast<char *>(m_ctx), m_ctx_size * sizeof(unsigned), m_d->get_id());
        else
            m_hash = m_d->get_id();
    }
    
    filter_cache_entry(imdd * d, imdd * r, unsigned ctx_size, unsigned * ctx):
        m_d(d),
        m_r(r),
        m_ctx_size(ctx_size) {
        memcpy(m_ctx, ctx, sizeof(unsigned)*m_ctx_size);
        mk_hash();
    }

    unsigned hash() const { 
        return m_hash; 
    }
    
    bool operator==(filter_cache_entry const & other) const {
        if (m_d != other.m_d)
            return false;
        if (m_ctx_size != other.m_ctx_size)
            return false;
        for (unsigned i = 0; i < m_ctx_size; i++)
            if (m_ctx[i] != other.m_ctx[i])
                return false;
        return true;
    }
};

typedef obj_hashtable<filter_cache_entry> imdd_mk_filter_cache;

typedef obj_ref<imdd, imdd_manager> imdd_ref;

class imdd_manager {
    typedef imdd_children::entry entry;
    small_object_allocator m_alloc;
    id_gen                 m_id_gen;
    vector<imdd_table>     m_tables; // we keep a table for each height.
    sl_imdd_manager        m_sl_manager;
    unsigned               m_simple_max_entries; //!< maximum number of entries in a "simple" node.
    bool                   m_delay_dealloc; 
    ptr_vector<imdd>       m_to_delete; //!< list of IMDDs marked as dead. These IMDDs may still be in cache tables.

    // generic cache and todo-lists
    ptr_vector<imdd>       m_worklist;
    imdd_cache             m_visited;
    
    void mark_as_dead(imdd * d);
    void deallocate_imdd(imdd * d);
    void delete_imdd(imdd * d);

    class delay_dealloc;
    friend class delay_dealloc;

    class delay_dealloc {
        imdd_manager & m_manager;
        bool           m_delay_dealloc_value;
        unsigned       m_to_delete_size;
    public:
        delay_dealloc(imdd_manager & m):
            m_manager(m), 
            m_delay_dealloc_value(m_manager.m_delay_dealloc),
            m_to_delete_size(m_manager.m_to_delete.size()) {
            m_manager.m_delay_dealloc = true;
        }
        ~delay_dealloc();
    };

    bool is_simple_node(imdd * d) const;

    void add_child(imdd * d, unsigned lower, unsigned upper, imdd * child) {
        d->m_children.insert(m_sl_manager, lower, upper, child);
    }

    void add_child(imdd * d, unsigned value, imdd * child) {
        add_child(d, value, value, child);
    }

    void remove_child(imdd * d, unsigned lower, unsigned upper) {
        d->m_children.remove(m_sl_manager, lower, upper);
    }

    imdd * copy_main(imdd * d);

    imdd * insert_main(imdd * d, unsigned b, unsigned e, bool destructive, bool memoize_res);
    
    imdd * remove_main(imdd * d, unsigned b, unsigned e, bool destructive, bool memoize_res);

    imdd2imdd_cache        m_mk_product_cache;
    struct null2imdd_proc;
    struct mk_product_proc;
    friend struct mk_product_proc;
    imdd * mk_product_core(imdd * d1, imdd * d2, bool destructive, bool memoize);
    imdd * mk_product_main(imdd * d1, imdd * d2, bool destructive, bool memoize_res);

    imdd2imdd_cache        m_add_facts_cache;
    ptr_vector<imdd>       m_add_facts_new_children;
    void init_add_facts_new_children(unsigned num, unsigned const * lowers, unsigned const * uppers, bool memoize_res);
    imdd * add_facts_core(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res);
    imdd * add_facts_main(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res);
    
    imdd2imdd_cache        m_remove_facts_cache;
    imdd * remove_facts_core(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res);
    imdd * remove_facts_main(imdd * d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool destructive, bool memoize_res);


    imdd2imdd_cache        m_defrag_cache;
    imdd * defrag_core(imdd * d);
    
    imdd_pair2imdd_cache   m_union_cache;
    void push_back_entries(unsigned head, imdd_children::iterator & it, imdd_children::iterator & end, 
                           imdd_children::push_back_proc & push_back, bool & children_memoized);
    void push_back_upto(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end, unsigned limit, 
                        imdd_children::push_back_proc & push_back, bool & children_memoized);
    void move_head(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end, unsigned new_head);
    void copy_upto(unsigned & head, imdd_children::iterator & it, imdd_children::iterator & end, unsigned limit, sbuffer<entry> & result);
    void reset_union_cache();
    imdd * mk_union_core(imdd * d1, imdd * d2, bool destructive, bool memoize_res);
    imdd * mk_union_main(imdd * d1, imdd * d2, bool destructive, bool memoize_res);
    void mk_union_core_dupdt(imdd_ref & d1, imdd * d2, bool memoize_res);
    void mk_union_core(imdd * d1, imdd * d2, imdd_ref & r, bool memoize_res);

    imdd_pair2bool_cache   m_is_equal_cache;
    bool is_equal_core(imdd * d1, imdd * d2);

    imdd_pair2bool_cache   m_subsumes_cache;
    bool subsumes_core(imdd * d1, imdd * d2);

    imdd2imdd_cache        m_complement_cache;
    imdd * mk_complement_core(imdd * d, unsigned num, unsigned const * mins, unsigned const * maxs, bool destructive, bool memoize_res);
    imdd * mk_complement_main(imdd * d, unsigned num, unsigned const * mins, unsigned const * maxs, bool destructive, bool memoize_res);

    imdd2imdd_cache        m_filter_equal_cache;
    imdd * mk_filter_equal_core(imdd * d, unsigned vidx, unsigned value, bool destructive, bool memoize_res);
    imdd * mk_filter_equal_main(imdd * d, unsigned vidx, unsigned value, bool destructive, bool memoize_res);
    

    // original 
    imdd2intervals m_imdd2interval_set;
    ptr_vector<sl_interval_set> m_alloc_is;
    typedef sl_manager_base<unsigned> sl_imanager;
    void reset_fi_intervals(sl_imanager& m);
    sl_interval_set const* init_fi_intervals(sl_imanager& m, imdd* d, unsigned var, unsigned num_found);

    imdd2imdd_cache        m_fi_top_cache;
    imdd_fi_cache          m_fi_bottom_cache;
    unsigned               m_fi_num_vars;
    unsigned *             m_fi_begin_vars;
    unsigned *             m_fi_end_vars;
    region                 m_fi_entries;
    bool is_fi_var(unsigned v) const { return std::find(m_fi_begin_vars, m_fi_end_vars, v) != m_fi_end_vars; }
    fi_cache_entry * mk_fi_cache_entry(imdd * d, unsigned lower, unsigned upper, unsigned num_pairs, imdd_value_pair pairs[]);
    mk_fi_result mk_filter_identical_core(imdd * d, unsigned offset, unsigned num_found, unsigned lower, unsigned upper, 
                                          bool destructive, bool memoize_res);
    imdd * mk_filter_identical_main(imdd * d, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res);

    // v2
    obj_map<imdd, imdd*> m_filter_identical_cache;
    void  filter_identical_core2(imdd* d, unsigned num_vars, unsigned b, unsigned e, ptr_vector<imdd>& ch);
    imdd* filter_identical_core2(imdd* d, unsigned var, unsigned num_vars, bool memoize_res);
    void  filter_identical_main2(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res);
    void  swap_in(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars);
    void  swap_out(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars);

    // v3
    struct interval {
        unsigned m_lo;
        unsigned m_hi;
        interval(unsigned lo, unsigned hi): m_lo(lo), m_hi(hi) {}
    };
    struct interval_dd : public interval {
        imdd* m_dd;
        interval_dd(unsigned lo, unsigned hi, imdd* d): interval(lo, hi), m_dd(d) {}
    };
    template<typename I>
    class id_map {
        unsigned m_T;
        unsigned_vector m_Ts;
        svector<svector<I>*> m_vecs;
        unsigned_vector m_alloc;
        unsigned        m_first_free;
        void hard_reset() {
            std::for_each(m_vecs.begin(), m_vecs.end(), delete_proc<svector<I> >());
            m_alloc.reset();
            m_first_free = 0;
            m_vecs.reset();
            m_Ts.reset();
            m_T = 0;
        }

        void allocate_entry(unsigned id) {
            if (m_vecs[id]) {
               return;
            }
            while (m_first_free < m_alloc.size()) {
                if (m_vecs[m_first_free] && m_Ts[m_first_free] < m_T) {
                    svector<I>* v = m_vecs[m_first_free];
                    m_vecs[m_first_free] = 0;
                    m_vecs[id] = v;
                    ++m_first_free;
                    return;
                }
                ++m_first_free;
            }
            m_vecs[id] = alloc(svector<I>);
            m_alloc.push_back(id);
        }
    public:
        id_map():m_T(0) {}
        ~id_map() { hard_reset(); }
        void reset() { ++m_T; m_first_free = 0; if (m_T == UINT_MAX) hard_reset(); }
        svector<I>& init(imdd* d) {
            unsigned id = d->get_id();
            if (id >= m_vecs.size()) {
                m_vecs.resize(id+1);
                m_Ts.resize(id+1);
            }
            if (m_Ts[id] < m_T) {
                allocate_entry(id);
                m_vecs[id]->reset();
                m_Ts[id] = m_T;
            }
            return *m_vecs[id];
        }

        typedef svector<I> data;
        struct iterator { 
            unsigned m_offset; 
            id_map const& m; 
            iterator(unsigned o, id_map const& m):m_offset(o),m(m) {}
            data const & operator*() const { return *m.m_vecs[m_offset]; }
            data const * operator->() const { return &(operator*()); }
            data * operator->() { return &(operator*()); }
            iterator & operator++() { ++m_offset; return move_to_used(); }
            iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
            bool operator==(iterator const & it) const { return m_offset == it.m_offset; }
            bool operator!=(iterator const & it) const { return m_offset != it.m_offset; }
            iterator & move_to_used() {
                while (m_offset < m.m_vecs.size() &&
                       m.m_Ts[m_offset] < m.m_T) {
                    ++m_offset;
                }
                return *this;
            }
        };         
        iterator begin() const { return iterator(0, *this).move_to_used(); }
        iterator end() const { return iterator(m_vecs.size(), *this); }        
    };
    typedef id_map<interval >    filter_id_map;
    typedef id_map<interval_dd > filter_idd_map;
    filter_id_map        m_nodes;
    filter_idd_map       m_nodes_dd;
    svector<interval_dd> m_i_nodes_dd, m_i_nodes_dd_tmp;
    svector<interval>    m_i_nodes,    m_i_nodes_tmp;
    unsigned_vector      m_offsets;
    void filter_identical_main3(imdd * d, imdd_ref& r, unsigned num_vars, unsigned * vars, bool destructive, bool memoize_res);
    void filter_identical_main3(imdd * d, imdd_ref& r, unsigned v1, bool del1, unsigned v2, bool del2, bool memoize_res);
    imdd* filter_identical_loop3(imdd * d, unsigned v1, bool del1, unsigned v2, bool del2, bool memoize_res);
    void refine_intervals(svector<interval>& i_nodes, svector<interval_dd> const& i_nodes_dd);
    void merge_intervals(svector<interval>& dst, svector<interval> const& src);
    imdd* filter_identical_mk_nodes(imdd* d, unsigned v, bool del1, bool del2, bool memoize_res);
    void print_filter_idd(std::ostream& out, filter_idd_map const& m);
    void print_interval_dd(std::ostream& out, svector<interval_dd> const& m);

    

    unsigned               m_proj_num_vars;
    unsigned *             m_proj_begin_vars;
    unsigned *             m_proj_end_vars;
    imdd2imdd_cache        m_proj_cache;
    bool is_proj_var(unsigned v) const { return std::find(m_proj_begin_vars, m_proj_end_vars, v) != m_proj_end_vars; }
    void mk_project_init(unsigned num_vars, unsigned * vars);
    void mk_project_core(imdd * d, imdd_ref & r, unsigned var, unsigned num_found, bool memoize_res);
    void mk_project_dupdt_core(imdd_ref & d, unsigned var, unsigned num_found, bool memoize_res);

    imdd2imdd_cache        m_swap_cache;
    imdd *                 m_swap_new_child;
    bool                   m_swap_granchildren_memoized;
    imdd * mk_swap_new_child(unsigned lower, unsigned upper, imdd * child);
    void mk_swap_acc1_dupdt(imdd_ref & d, unsigned lower, unsigned upper, imdd * grandchild, bool memoize_res);
    void mk_swap_acc1(imdd * d, imdd_ref & r, unsigned lower, unsigned upper, imdd * grandchild, bool memoize_res);
    void mk_swap_acc2(imdd_ref & r, unsigned lower1, unsigned upper1, unsigned lower2, unsigned upper2, imdd * grandchild, bool memoize_res);
    void mk_swap_top_vars(imdd * d, imdd_ref & r, bool memoize_res);
    imdd * mk_swap_memoize(imdd * d);
    void mk_swap_core(imdd * d, imdd_ref & r, unsigned vidx, bool memoize_res);
    void mk_swap_dupdt_core(imdd_ref & d, unsigned vidx, bool memoize_res);

    imdd2imdd_cache        m_add_bounded_var_cache;
    imdd * add_bounded_var_core(imdd * d, unsigned before_vidx, unsigned lower, unsigned upper, bool destructive, bool memoize_res);
    imdd * add_bounded_var_main(imdd * d, unsigned before_vidx, unsigned lower, unsigned upper, bool destructive, bool memoize_res);

    friend struct distinct_proc;
    imdd * mk_distinct_imdd(unsigned l1, unsigned u1, unsigned l2, unsigned u2, imdd * d, bool memoize_res = true);

    imdd_mk_filter_cache   m_filter_cache;
    region                 m_filter_entries;
    unsigned               m_filter_num_vars;
    unsigned *             m_filter_begin_vars;
    unsigned *             m_filter_end_vars;
    unsigned_vector        m_filter_context;
    bool is_filter_var(unsigned v) const { return std::find(m_filter_begin_vars, m_filter_end_vars, v) != m_filter_end_vars; }
    filter_cache_entry * mk_filter_cache_entry(imdd * d, unsigned ctx_sz, unsigned * ctx, imdd * r);
    imdd * is_mk_filter_cached(imdd * d, unsigned ctx_sz, unsigned * ctx);
    void cache_mk_filter(imdd * d, unsigned ctx_sz, unsigned * ctx, imdd * r);
    void init_mk_filter(unsigned arity, unsigned num_vars, unsigned * vars);
    template<typename FilterProc>
    void mk_filter_dupdt_core(imdd_ref & d, unsigned vidx, unsigned num_found, FilterProc & proc, bool memoize_res);
    template<typename FilterProc>
    void mk_filter_core(imdd * d, imdd_ref & r, unsigned vidx, unsigned num_found, FilterProc & proc, bool memoize_res);
    /**
       \brief Filter the elements of the given IMDD using the given filter.

       The FilterProc template parameter is a filter for computing subsets of sets of the form:
       
       [L_1, U_1] X [L_2, U_2] X ... X [L_n, U_n] X d  (where d is an IMDD)
       
       where n == num_vars

       The subset of elements is returned as an IMDD.

       FilterProc must have a method of the form:
       
       void operator()(unsigned * lowers_uppers, imdd * d, imdd_ref & r, bool memoize_res);

       The size of the array lowers_uppers is 2*num_vars
       
       The arity of the resultant IMDD must be num_vars + d->get_arity().
    */
    template<typename FilterProc>
    void mk_filter_dupdt(imdd_ref & d, unsigned num_vars, unsigned * vars, FilterProc & proc, bool memoize_res = true);
    template<typename FilterProc>
    void mk_filter(imdd * d, imdd_ref & r, unsigned num_vars, unsigned * vars, FilterProc & proc, bool memoize_res = true);

    imdd * mk_disequal_imdd(unsigned l1, unsigned u1, unsigned value, imdd * d, bool memoize_res);
    friend struct disequal_proc;

public:
    imdd_manager();

    void inc_ref(imdd * d) { 
        if (d) 
            d->inc_ref();
    }

    void dec_ref(imdd * d) { 
        if (d) {
            d->dec_ref();
            if (d->get_ref_count() == 0)
                delete_imdd(d);
        }
    }

    unsigned get_num_nodes(imdd const * d) const;

    // count number of keys (rows) in table as if table is uncompressed.
    size_t get_num_rows(imdd const* d) const;

    unsigned memory(imdd const * d) const;

private:
    imdd * _mk_empty(unsigned arity);

public:
    imdd * mk_empty(unsigned arity) { 
        imdd * r = _mk_empty(arity); 
        STRACE("imdd_trace", tout << "mk_empty(" << arity << ", 0x" << r << ");\n";);
        return r;
    }

private:
    imdd * memoize(imdd * d);
    
public:
    void memoize(imdd_ref const & d, imdd_ref & r) { r = memoize(d.get()); }

    void memoize(imdd_ref & d) { d = memoize(d.get()); }

    imdd * memoize_new_imdd_if(bool cond, imdd * r) {
        if (cond && is_simple_node(r)) {
            SASSERT(!r->is_shared());
            imdd * can_r = memoize(r);
            if (can_r != r) {
                SASSERT(r->get_ref_count() == 0);
                delete_imdd(r);
            }
            return can_r;
        }
        return r;
    }

public:
    void defrag(imdd_ref & d);
    
    void unmemoize(imdd * d);
    
    void unmemoize_rec(imdd * d);
    
    void copy(imdd * d, imdd_ref & r) { r = copy_main(d); }
    
    void insert_dupdt(imdd_ref & d, unsigned b, unsigned e, bool memoize_res = true) { 
        d = insert_main(d, b, e, true, memoize_res); 
    }
    
    void insert(imdd * d, imdd_ref & r, unsigned b, unsigned e, bool memoize_res = true) { 
        r = insert_main(d, b, e, false, memoize_res); 
    }
    
    void mk_product_dupdt(imdd_ref & d1, imdd * d2, bool memoize_res = true) { 
        d1 = mk_product_main(d1.get(), d2, true, memoize_res); 
    }
    
    void mk_product(imdd * d1, imdd * d2, imdd_ref & r, bool memoize_res = true) { 
        r = mk_product_main(d1, d2, false, memoize_res); 
        STRACE("imdd_trace", tout << "mk_product(0x" << d1 << ", 0x" << d2 << ", 0x" << r.get() << ", " << memoize_res << ");\n";);
    }
    
    void mk_union_dupdt(imdd_ref & d1, imdd * d2, bool memoize_res = true) { 
        d1 = mk_union_main(d1.get(), d2, true, memoize_res); 
    }
    
    void mk_union(imdd * d1, imdd * d2, imdd_ref & r, bool memoize_res = true) { 
        r = mk_union_main(d1, d2, false, memoize_res); 
        STRACE("imdd_trace", tout << "mk_union(0x" << d1 << ", 0x" << d2 << ", 0x" << r.get() << ", " << memoize_res << ");\n";);
    }
    
    void mk_complement_dupdt(imdd_ref & d, unsigned num, unsigned const * mins, unsigned const * maxs, bool memoize_res = true) {
        d = mk_complement_main(d, num, mins, maxs, true, memoize_res);
    }

    void mk_complement(imdd * d, imdd_ref & r, unsigned num, unsigned const * mins, unsigned const * maxs, bool memoize_res = true) {
        r = mk_complement_main(d, num, mins, maxs, false, memoize_res);
        
        STRACE("imdd_trace", tout << "mk_complement(0x" << d << ", 0x" << r.get() << ", ";
               for (unsigned i = 0; i < num; i++) tout << mins[i] << ", " << maxs[i] << ", ";
               tout << memoize_res << ");\n";);
    }

    void mk_filter_equal_dupdt(imdd_ref & d, unsigned vidx, unsigned value, bool memoize_res = true) {
        d = mk_filter_equal_main(d, vidx, value, true, memoize_res);
    }

    void mk_filter_equal(imdd * d, imdd_ref & r, unsigned vidx, unsigned value, bool memoize_res = true) {
        r = mk_filter_equal_main(d, vidx, value, false, memoize_res);

        STRACE("imdd_trace", tout << "mk_filter_equal(0x" << d << ", 0x" << r.get() << ", " << vidx << ", " << value << ", " << memoize_res << ");\n";);
    }

    void mk_filter_identical_dupdt(imdd_ref & d, unsigned num_vars, unsigned * vars, bool memoize_res = true) {
        // d = mk_filter_identical_main(d, num_vars, vars, true, memoize_res);
        filter_identical_main3(d, d, num_vars, vars, true, memoize_res);
    }

    void mk_filter_identical(imdd * d, imdd_ref & r, unsigned num_vars, unsigned * vars, bool memoize_res = true) {
        filter_identical_main3(d, r, num_vars, vars, false, memoize_res);

        STRACE("imdd_trace", tout << "mk_filter_identical(0x" << d << ", 0x" << r.get() << ", ";
           for (unsigned i = 0; i < num_vars; i++) tout << vars[i] << ", ";
           tout << memoize_res << ");\n";);
    }

    void mk_project_dupdt(imdd_ref & d, unsigned num_vars, unsigned * vars, bool memoize_res = true);

    void mk_project(imdd * d, imdd_ref & r, unsigned num_vars, unsigned * vars, bool memoize_res = true);
    
    // swap vidx and vidx+1
    void mk_swap_dupdt(imdd_ref & d, unsigned vidx, bool memoize_res = true);

    // swap vidx and vidx+1
    void mk_swap(imdd * d, imdd_ref & r, unsigned vidx, bool memoize_res = true);

    void add_facts_dupdt(imdd_ref & d, unsigned num, unsigned const * lowers, unsigned const * uppers, bool memoize_res = true) {
        d = add_facts_main(d, num, lowers, uppers, true, memoize_res);
    }

    void add_facts(imdd * d, imdd_ref & r, unsigned num, unsigned const * lowers, unsigned const * uppers, bool memoize_res = true) {
        r = add_facts_main(d, num, lowers, uppers, false, memoize_res);
        
        STRACE("imdd_trace", tout << "add_facts(0x" << d << ", 0x" << r.get() << ", ";
               for (unsigned i = 0; i < num; i++) tout << lowers[i] << ", " << uppers[i] << ", ";
               tout << memoize_res << ");\n";);
    }

    void add_fact_dupdt(imdd_ref & d, unsigned num, unsigned const * values, bool memoize_res = true) { 
        add_facts_dupdt(d, num, values, values, memoize_res);
    }

    void add_fact(imdd * d, imdd_ref & r, unsigned num, unsigned const * values, bool memoize_res = true) { 
        add_facts(d, r, num, values, values, memoize_res);
    }

    void add_bounded_var_dupdt(imdd_ref & d, unsigned before_vidx, unsigned lower, unsigned upper, bool memoize_res = true) {
        d = add_bounded_var_main(d, before_vidx, lower, upper, true, memoize_res);
    }

    void add_bounded_var(imdd * d, imdd_ref & r, unsigned before_vidx, unsigned lower, unsigned upper, bool memoize_res = true) {
        r = add_bounded_var_main(d, before_vidx, lower, upper, false, memoize_res);
    }

    void mk_filter_distinct_dupdt(imdd_ref & d, unsigned v1, unsigned v2, bool memoize_res = true);

    void mk_filter_distinct(imdd * d, imdd_ref & r, unsigned v1, unsigned v2, bool memoize_res = true);

    void mk_filter_disequal_dupdt(imdd_ref & d, unsigned var, unsigned value, bool memoize_res = true);

    void mk_filter_disequal(imdd * d, imdd_ref & r, unsigned var, unsigned value, bool memoize_res = true);

    void mk_join(imdd * d1, imdd * d2, imdd_ref & r, unsigned_vector const& vars1, unsigned_vector const& vars2, bool memoize_res = true);

    void mk_join_project(imdd * d1, imdd * d2, imdd_ref & r,
                         unsigned_vector const& vars1, unsigned_vector const& vars2,
                         unsigned_vector const& proj_vars, bool memoize_res = true);

    void mk_join_dupdt(imdd_ref & d1, imdd * d2, unsigned num_vars, unsigned const * vars1, unsigned const * vars2, bool memoize_res = true);

    void remove_facts_dupdt(imdd_ref & d, unsigned num, unsigned const * lowers, unsigned const * uppers);

    void remove_facts(imdd * d, imdd_ref & r, unsigned num, unsigned const * lowers, unsigned const * uppers);

    bool is_equal(imdd * d1, imdd * d2);

    bool contains(imdd * d, unsigned num, unsigned const * values) const;

    bool contains(imdd * d, unsigned v) const { return contains(d, 1, &v); }

    bool contains(imdd * d, unsigned v1, unsigned v2) const { unsigned vs[2] = {v1, v2}; return contains(d, 2, vs); }

    bool contains(imdd * d, unsigned v1, unsigned v2, unsigned v3) const { unsigned vs[3] = {v1,v2,v3}; return contains(d, 3, vs); }
    
    bool subsumes(imdd * d1, imdd * d2);

    bool is_subset(imdd * d1, imdd * d2) { return subsumes(d2, d1); }

private:
    void display(std::ostream & out, imdd const * d, unsigned_vector & intervals, bool & first) const;

public:
    void display(std::ostream & out, imdd const * d) const;

    void display_ll(std::ostream & out, imdd const * d) const;

    /**
       \brief Execute proc (once) in each node in the IMDD rooted by d.
    */
    template<typename Proc>
    void for_each(imdd * d, Proc & proc) const {
        // for_each is a generic procedure, we don't know what proc will actually do.
        // So, it is not safe to reuse m_worklist and m_visited.
        ptr_buffer<imdd,128> worklist;
        imdd_cache       visited;
        worklist.push_back(d);
        while (!worklist.empty()) {
            d = worklist.back();
            worklist.pop_back();
            if (d->is_shared() && visited.contains(d))
                continue;
            if (d->is_shared())
                visited.insert(d);
            proc(d);
            if (d->get_arity() > 1) {
                imdd_children::iterator it  = d->begin_children();
                imdd_children::iterator end = d->end_children();
                for (; it != end; ++it)
                    worklist.push_back(it->val());
            }
        }
    } 

    class iterator {
        bool                             m_done;
        svector<imdd_children::iterator> m_iterators;
        svector<unsigned>                m_element;
        
        void begin_iterators(imdd const * curr, unsigned start_idx);

    public:
        iterator():m_done(true) {}
        iterator(imdd_manager const & m, imdd const * d);
        
        unsigned   get_arity() const { return m_element.size(); }
        unsigned * operator*() const { return m_element.c_ptr(); }
        iterator & operator++();
        
        bool operator==(iterator const & it) const;
        bool operator!=(iterator const & it) const { return !operator==(it); }
    };
    
    friend class iterator;

    iterator begin(imdd const * d) const { return iterator(*this, d); }
    iterator end(imdd const * d) const { return iterator(); }
};

inline std::ostream & operator<<(std::ostream & out, imdd_ref const & r) {
    r.get_manager().display(out, r.get());
    return out;
}

struct mk_imdd_pp {
    imdd *         m_d;
    imdd_manager & m_manager;
    mk_imdd_pp(imdd * d, imdd_manager & m):m_d(d), m_manager(m) {}
};

inline mk_imdd_pp mk_pp(imdd * d, imdd_manager & m) { 
    return mk_imdd_pp(d, m); 
}

inline std::ostream & operator<<(std::ostream & out, mk_imdd_pp const & pp) {
    pp.m_manager.display(out, pp.m_d);
    return out;
}

struct mk_imdd_ll_pp : public mk_imdd_pp  {
    mk_imdd_ll_pp(imdd * d, imdd_manager & m):mk_imdd_pp(d, m) {}
};

inline mk_imdd_ll_pp mk_ll_pp(imdd * d, imdd_manager & m) { 
    return mk_imdd_ll_pp(d, m); 
}

inline std::ostream & operator<<(std::ostream & out, mk_imdd_ll_pp const & pp) {
    pp.m_manager.display_ll(out, pp.m_d);
    return out;
}

#endif /* _IMDD_H_ */

