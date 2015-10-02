/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fingerprints.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-02-24.

Revision History:

--*/
#ifndef FINGERPRINTS_H_
#define FINGERPRINTS_H_

#include"smt_enode.h"

namespace smt {

    class fingerprint {
    protected:
        void *        m_data;
        unsigned      m_data_hash;
        unsigned      m_num_args;
        enode * *     m_args;

        friend class fingerprint_set;
        fingerprint() {}
    public:
        fingerprint(region & r, void * d, unsigned d_hash, unsigned n, enode * const * args);
        void * get_data() const { return m_data; }
        unsigned get_data_hash() const { return m_data_hash; }
        unsigned get_num_args() const { return m_num_args;  }
        enode * const * get_args() const { return m_args; }
        enode * get_arg(unsigned idx) const { SASSERT(idx < m_num_args); return m_args[idx]; }
    };
    
    class fingerprint_set {
        
        struct fingerprint_khasher {
            unsigned operator()(fingerprint const * f) const { return f->get_data_hash(); }
        };
        struct fingerprint_chasher {
            unsigned operator()(fingerprint const * f, unsigned idx) const { return f->get_arg(idx)->hash(); }
        };
        struct fingerprint_hash_proc {
            unsigned operator()(fingerprint const * f) const {
                return get_composite_hash<fingerprint *, fingerprint_khasher, fingerprint_chasher>(const_cast<fingerprint*>(f), f->get_num_args());
            }
        };
        struct fingerprint_eq_proc { bool operator()(fingerprint const * f1, fingerprint const * f2) const; };
        typedef ptr_hashtable<fingerprint, fingerprint_hash_proc, fingerprint_eq_proc> set;

        region &                 m_region;
        set                      m_set;
        ptr_vector<fingerprint>  m_fingerprints;
        unsigned_vector          m_scopes;
        ptr_vector<enode>        m_tmp;
        fingerprint              m_dummy;

        fingerprint * mk_dummy(void * data, unsigned data_hash, unsigned num_args, enode * const * args);

    public:
        fingerprint_set(region & r):m_region(r) {}
        fingerprint * insert(void * data, unsigned data_hash, unsigned num_args, enode * const * args);
        unsigned size() const { return m_fingerprints.size(); }
        bool contains(void * data, unsigned data_hash, unsigned num_args, enode * const * args);
        void reset();
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void display(std::ostream & out) const;
#ifdef Z3DEBUG
        bool slow_contains(void const * data, unsigned data_hash, unsigned num_args, enode * const * args) const;
#endif
    };
};

#endif /* FINGERPRINTS_H_ */

