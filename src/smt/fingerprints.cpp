/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fingerprints.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-02-24.

Revision History:

--*/
#include"fingerprints.h"

namespace smt {

    fingerprint::fingerprint(region & r, void * d, unsigned d_h, unsigned n, enode * const * args):
        m_data(d), 
        m_data_hash(d_h),
        m_num_args(n), 
        m_args(0) {
        m_args = new (r) enode*[n];
        memcpy(m_args, args, sizeof(enode*) * n);
    }

    bool fingerprint_set::fingerprint_eq_proc::operator()(fingerprint const * f1, fingerprint const * f2) const {
        if (f1->get_data() != f2->get_data()) 
            return false;
        if (f1->get_num_args() != f2->get_num_args())
            return false;
        unsigned n = f1->get_num_args();
        for(unsigned i = 0; i < n; i++)
            if (f1->get_arg(i) != f2->get_arg(i))
                return false;
        return true;
    }

    fingerprint * fingerprint_set::mk_dummy(void * data, unsigned data_hash, unsigned num_args, enode * const * args) {
        m_tmp.reset();
        m_tmp.append(num_args, args);
        m_dummy.m_data      = data;
        m_dummy.m_data_hash = data_hash;
        m_dummy.m_num_args  = num_args;
        m_dummy.m_args      = m_tmp.c_ptr();
        return &m_dummy;
    }
    
    fingerprint * fingerprint_set::insert(void * data, unsigned data_hash, unsigned num_args, enode * const * args) {
        fingerprint * d = mk_dummy(data, data_hash, num_args, args);
        if (m_set.contains(d)) 
            return 0;
        TRACE("fingerprint_bug", tout << "1) inserting: " << data_hash << " num_args: " << num_args;
              for (unsigned i = 0; i < num_args; i++) tout << " " << args[i]->get_owner_id(); 
              tout << "\n";);
        for (unsigned i = 0; i < num_args; i++)
            d->m_args[i] = d->m_args[i]->get_root();
        if (m_set.contains(d)) {
            TRACE("fingerprint_bug", tout << "failed: " << data_hash << " num_args: " << num_args;
                  for (unsigned i = 0; i < num_args; i++) tout << " " << d->m_args[i]->get_owner_id(); 
                  tout << "\n";);
            return 0;
        }
        TRACE("fingerprint_bug", tout << "2) inserting: " << data_hash << " num_args: " << num_args;
              for (unsigned i = 0; i < num_args; i++) tout << " " << args[i]->get_owner_id(); 
              tout << "\n";);
        fingerprint * f = new (m_region) fingerprint(m_region, data, data_hash, num_args, d->m_args);
        m_fingerprints.push_back(f);
        m_set.insert(f);
        return f;
    }

    bool fingerprint_set::contains(void * data, unsigned data_hash, unsigned num_args, enode * const * args) {
        fingerprint * d = mk_dummy(data, data_hash, num_args, args);
        if (m_set.contains(d)) 
            return true;
        for (unsigned i = 0; i < num_args; i++)
            d->m_args[i] = d->m_args[i]->get_root();
        if (m_set.contains(d))
            return true;
        return false;
    }
    
    void fingerprint_set::reset() {
        m_set.reset();
        m_fingerprints.reset();
    }
        
    void fingerprint_set::push_scope() {
        m_scopes.push_back(m_fingerprints.size());
    }
    
    void fingerprint_set::pop_scope(unsigned num_scopes) {
        unsigned lvl      = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl  = lvl - num_scopes;
        unsigned old_size = m_scopes[new_lvl];
        unsigned size     = m_fingerprints.size();
        for (unsigned i = old_size; i < size; i++) 
            m_set.erase(m_fingerprints[i]);
        m_fingerprints.shrink(old_size);
        m_scopes.shrink(new_lvl);
    }

    void fingerprint_set::display(std::ostream & out) const {
        out << "fingerprints:\n";
        SASSERT(m_set.size() == m_fingerprints.size());
        ptr_vector<fingerprint>::const_iterator it  = m_fingerprints.begin();
        ptr_vector<fingerprint>::const_iterator end = m_fingerprints.end();
        for (; it != end; ++it) {
            fingerprint const * f = *it;
            out << f->get_data() << " #" << f->get_data_hash();
            for (unsigned i = 0; i < f->get_num_args(); i++) 
                out << " #" << f->get_arg(i)->get_owner_id();
            out << "\n";
        }
    }

#ifdef Z3DEBUG
    /**
       \brief Slow function for checking if there is a fingerprint congruent to (data args[0] ... args[num_args-1])
    */
    bool fingerprint_set::slow_contains(void const * data, unsigned data_hash, unsigned num_args, enode * const * args) const {
        ptr_vector<fingerprint>::const_iterator it  = m_fingerprints.begin();
        ptr_vector<fingerprint>::const_iterator end = m_fingerprints.end();
        for (; it != end; ++it) {
            fingerprint const * f = *it;
            if (f->get_data() != data)
                continue;
            if (f->get_num_args() != num_args)
                continue;
            unsigned i = 0;
            for (i = 0; i < num_args; i++)
                if (f->get_arg(i)->get_root() != args[i]->get_root())
                    break;
            if (i == num_args) {
                TRACE("missing_instance_detail", tout << "found instance data: " << data << "=" << f->get_data() << " hash: " << f->get_data_hash();
                      for (unsigned i = 0; i < num_args; i++) {
                          tout << " " << f->get_arg(i)->get_owner_id() << ":" << f->get_arg(i)->get_root()->get_owner_id() << "=" 
                               << args[i]->get_owner_id() << ":" << args[i]->get_root()->get_owner_id();
                      }
                      tout << "\n";);
                return true;
            }
        }
        return false;
    }
#endif

    
};
