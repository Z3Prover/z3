/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    sorting_network.h

Abstract:

    Utility for creating a sorting network.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-07

Notes:

    Same routine is used in Formula.

--*/

#include "vector.h"

#ifndef _SORTING_NETWORK_H_
#define _SORTING_NETWORK_H_


    template <typename Ext>
    class sorting_network {
        typedef typename Ext::vector vect;
        Ext&               m_ext;
        svector<unsigned>  m_currentv;
        svector<unsigned>  m_nextv;
        svector<unsigned>* m_current;
        svector<unsigned>* m_next;

        unsigned& current(unsigned i) { return (*m_current)[i]; }
        unsigned& next(unsigned i) { return (*m_next)[i]; }
       
        void exchange(unsigned i, unsigned j, vect& out) {
            SASSERT(i <= j);
            if (i < j) {
                Ext::T ei = out.get(i);
                Ext::T ej = out.get(j);
                out.set(i, m_ext.mk_ite(m_ext.mk_le(ei, ej), ei, ej));
                out.set(j, m_ext.mk_ite(m_ext.mk_le(ej, ei), ei, ej));
            }
        }
        
        void sort(unsigned k, vect& out) {
            SASSERT(is_power_of2(k) && k > 0);
            if (k == 2) {
                for (unsigned i = 0; i < out.size()/2; ++i) {
                    exchange(current(2*i), current(2*i+1), out);
                    next(2*i) = current(2*i);
                    next(2*i+1) = current(2*i+1);
                }
                std::swap(m_current, m_next);
            }
            else {
                
                for (unsigned i = 0; i < out.size()/k; ++i) {
                    unsigned ki = k * i;
                    for (unsigned j = 0; j < k / 2; ++j) {
                        next(ki + j) = current(ki + (2 * j));
                        next(ki + (k / 2) + j) = current(ki + (2 * j) + 1);
                    }
                }
                
                std::swap(m_current, m_next);
                sort(k / 2, out);
                for (unsigned i = 0; i < out.size() / k; ++i) {
                    unsigned ki = k * i;
                    for (unsigned j = 0; j < k / 2; ++j) {
                        next(ki + (2 * j)) = current(ki + j);
                        next(ki + (2 * j) + 1) = current(ki + (k / 2) + j);
                    }
                    
                    for (unsigned j = 0; j < (k / 2) - 1; ++j) {
                        exchange(next(ki + (2 * j) + 1), next(ki + (2 * (j + 1))), out);
                    }
                }
                std::swap(m_current, m_next);
            }
        }        

        bool is_power_of2(unsigned n) const {
            return n != 0 && ((n-1) & n) == 0;
        }
        
    public:
        sorting_network(Ext& ext):
            m_ext(ext),
            m_current(&m_currentv),
            m_next(&m_nextv)
        {}
        
        void operator()(vect const& in, vect& out) {
            out.reset();
            out.append(in);
            if (in.size() <= 1) {
                return;
            }
            while (!is_power_of2(out.size())) {
                out.push_back(m_ext.mk_default());
            }
            for (unsigned i = 0; i < out.size(); ++i) {
                m_currentv.push_back(i);
                m_nextv.push_back(i);
            }
            unsigned k = 2;
            while (k <= out.size()) {
                sort(k, out);
                k *= 2;
            }
        }        
    };

#endif
