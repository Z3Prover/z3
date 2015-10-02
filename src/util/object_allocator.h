/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    object_allocator.h

Abstract:

    Yet another object allocator. This allocator is supposed to be efficient 
    when there is a collection of worker threads accessing it.
    
Author:

    Leonardo de Moura (leonardo) 2010-06-09.

Revision History:

--*/
#ifndef OBJECT_ALLOCATOR_H_
#define OBJECT_ALLOCATOR_H_

#include"util.h"
#include"vector.h"

#define DEFAULT_NUM_WORKERS 8
#define NUM_OBJECTS_PER_PAGE 1024

template<typename T>
struct do_nothing_reset_proc {
public:
    void operator()(T * obj) {}
};

template<typename T>
struct simple_reset_proc {
public:
    void operator()(T * obj) { obj->reset(); }
};

/**
   \brief Allocator for T objects. This allocator is supposed to be efficient even
   when a collection of working threads are accessing it. 
   
   Assumptions:
   - T must have an empty constructor.

   - The destructors for T objects are only invoked when the object_allocator is deleted.

   - The destructors are not invoked if CallDestructors == false.

   - The functor ResetProc is invoked for \c ptr when recycle(ptr) or recycle(worker_id, ptr) are invoked. 

   The default ResetProc does nothing.
*/
template<typename T, bool CallDestructors = true, typename ResetProc = do_nothing_reset_proc<T> >
class object_allocator : public ResetProc {

    /**
       \brief Auxiliary allocator for storing object into chunks of memory.
    */
    class region {
        ptr_vector<T> m_pages;
        unsigned      m_idx;   //!< next position in the current page.
        
        void allocate_new_page() {
            T * new_page = static_cast<T*>(memory::allocate(sizeof(T) * NUM_OBJECTS_PER_PAGE));
            m_pages.push_back(new_page);
            m_idx = 0;
        }

        void call_destructors_for_page(T * page, unsigned end) {
            T * page_end = page + end;
            for (; page < page_end; page++)
                page->~T();
        }

        void call_destructors() {
            if (CallDestructors) {
                SASSERT(!m_pages.empty());
                typename ptr_vector<T>::iterator it = m_pages.begin();
                typename ptr_vector<T>::iterator end = m_pages.end();
                end--;
                call_destructors_for_page(*end, m_idx);
                for (; it != end; ++it)
                    call_destructors_for_page(*it, NUM_OBJECTS_PER_PAGE);
            }
        }
        
        void free_memory() {
            call_destructors();
            typename ptr_vector<T>::iterator it = m_pages.begin();
            typename ptr_vector<T>::iterator end = m_pages.end();
            for (; it != end; ++it)
                memory::deallocate(*it);
        }
        
    public:
        region() {
            allocate_new_page();
        }

        ~region() {
            free_memory();
        }

        template<bool construct>
        T * allocate() {
            SASSERT(!m_pages.empty());
            T * r = m_pages.back() + m_idx;
            if (construct) new (r) T();
            m_idx++;
            if (m_idx == NUM_OBJECTS_PER_PAGE)
                allocate_new_page();
            return r;
        }

        void reset() {
            free_memory();
            m_pages.reset();
            allocate_new_page();
        }

        unsigned get_objects_count() {
            return (m_pages.size() - 1) * NUM_OBJECTS_PER_PAGE + m_idx;
        }
    };
    
#ifdef Z3DEBUG
    bool                   m_concurrent; //!< True when the allocator can be accessed concurrently.
#endif
    ptr_vector<region>     m_regions;
    vector<ptr_vector<T> > m_free_lists;
    
    template <bool construct>
    T * allocate_core(unsigned idx) {
        ptr_vector<T> & free_list = m_free_lists[idx];
        if (!free_list.empty()) {
            T * r = free_list.back();
            free_list.pop_back();
            return r;
        }
        return m_regions[idx]->template allocate<construct>();
    }

    void recycle_core(unsigned idx, T * ptr) {
        ResetProc::operator()(ptr);
        m_free_lists[idx].push_back(ptr);
    }

public:
    object_allocator(ResetProc const & r = ResetProc()):ResetProc(r) {
        DEBUG_CODE(m_concurrent = false;);
        reserve(DEFAULT_NUM_WORKERS);
    }

    ~object_allocator() {
        std::for_each(m_regions.begin(), m_regions.end(), delete_proc<region>());
    }

    /**
       \brief Enable/Disable concurrent access.
    */
    void enable_concurrent(bool flag) {
        DEBUG_CODE(m_concurrent = flag;);
    }
    
    /**
       \brief Make sure that \c num_workers can access this object allocator concurrently.
       This method must only be invoked if the allocator is not in concurrent mode.
    */
    void reserve(unsigned num_workers) {
        SASSERT(!m_concurrent);
        unsigned old_capacity = capacity();
        if (num_workers > old_capacity) {
            m_regions.resize(num_workers);
            m_free_lists.resize(num_workers);
            for (unsigned i = old_capacity; i < capacity(); i++) {
                m_regions[i] = alloc(region);
            }
        }
    }

    /**
       \brief Return the number of workers supported by this object allocator.
    */
    unsigned capacity() const {
        return m_regions.size();
    }

    /**
       \brief Free all memory allocated using this allocator.
       This method must only be invoked when the allocator is not in concurrent mode.
    */
    void reset() {
        SASSERT(!m_concurrent);
        unsigned c = capacity();
        for (unsigned i = 0; i < c; i++) {
            m_regions[i]->reset();
            m_free_lists[i].reset();
        }
    }

    /**
       \brief Allocate a new object. 
       This method must only be invoked when the object_allocator is not in concurrent mode.
    */
    template<bool construct>
    T * allocate() {
        SASSERT(!m_concurrent);
        return allocate_core<construct>(0);
    }


    /**
       \brief Recycle the given object. 
       This method must only be invoked when the object_allocator is not in concurrent mode.

       \remark It is OK to recycle an object allocated by a worker when the object_allocator was 
       in concurrent mode.
    */
    void recycle(T * ptr) {
        SASSERT(!m_concurrent);
        recycle_core(0, ptr);
    }

    /**
       \brief Allocate a new object for the given worker.
       This method must only be invoked when the object_allocator is in concurrent mode.
    */
    template <bool construct>
    T * allocate(unsigned worker_id) {
        SASSERT(m_concurrent);
        return allocate_core<construct>(worker_id);
    }

    /**
       \brief Recycle the given object. 
       This method must only be invoked when the object_allocator is in concurrent mode.
       
       \remark It is OK to recycle an object allocated by a different worker, or allocated when the 
       object_allocator was not in concurrent mode.
    */
    void recycle(unsigned worker_id, T * ptr) {
        SASSERT(m_concurrent);
        return recycle_core(worker_id, ptr);
    }

    /**
       \brief Wrapper for currying worker_id in allocate and recycle methods.
    */
    class worker_object_allocator {
        object_allocator & m_owner;
        unsigned           m_worker_id;
        
        friend class object_allocator;

        worker_object_allocator(object_allocator & owner, unsigned id):m_owner(owner), m_worker_id(id) {}
    public:
        template<bool construct>
        T * allocate() { return m_owner.allocate<construct>(m_worker_id); }

        void recycle(T * ptr) { return m_owner.recycle(m_worker_id, ptr); }
    };
    
    /**
       \brief Return a wrapper for allocating memory for the given worker.
       The wrapper remains valid even when the object_allocator is not in concurrent mode.
       However, the methods allocate/recycle of the wrapper must only be invoked when the object_allocator is in concurrent mode.
    */
    worker_object_allocator get_worker_allocator(unsigned worker_id) {
        SASSERT(worker_id < capacity());
        return worker_object_allocator(*this, worker_id);
    }

    unsigned get_objects_count() const {
        unsigned count = 0;
        unsigned n_regions = m_regions.size();
        for (unsigned i = 0; i < n_regions; i++) {
            count += m_regions[i]->get_objects_count();
            count -= m_free_lists[i].size();
        }
        return count;
    }

};

#endif /* OBJECT_ALLOCATOR_H_ */

