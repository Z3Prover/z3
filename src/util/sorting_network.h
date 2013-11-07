
#include "vector.h"

#ifndef _SORTING_NETWORK_H_
#define _SORTING_NETWORK_H_


    template <typename Ext>
    class sorting_network {
        typename Ext::vector&       m_es;
        Ext&               m_ext;
        svector<unsigned>  m_currentv;
        svector<unsigned>  m_nextv;
        svector<unsigned>* m_current;
        svector<unsigned>* m_next;

        unsigned& current(unsigned i) { return (*m_current)[i]; }
        unsigned& next(unsigned i) { return (*m_next)[i]; }
       
        void exchange(unsigned i, unsigned j) {
            SASSERT(i <= j);
            if (i < j) {
                Ext::T ei = m_es.get(i);
                Ext::T ej = m_es.get(j);
                m_es.set(i, m_ext.mk_ite(m_ext.mk_le(ei, ej), ei, ej));
                m_es.set(j, m_ext.mk_ite(m_ext.mk_le(ej, ei), ei, ej));
            }
        }
        
        void sort(unsigned k) {
            SASSERT(is_power_of2(k) && k > 0);
            if (k == 2) {
                for (unsigned i = 0; i < m_es.size()/2; ++i) {
                    exchange(current(2*i), current(2*i+1));
                    next(2*i) = current(2*i);
                    next(2*i+1) = current(2*i+1);
                }
                std::swap(m_current, m_next);
            }
            else {
                
                for (unsigned i = 0; i < m_es.size()/k; ++i) {
                    unsigned ki = k * i;
                    for (unsigned j = 0; j < k / 2; ++j) {
                        next(ki + j) = current(ki + (2 * j));
                        next(ki + (k / 2) + j) = current(ki + (2 * j) + 1);
                    }
                }
                
                std::swap(m_current, m_next);
                sort(k / 2);
                for (unsigned i = 0; i < m_es.size() / k; ++i) {
                    unsigned ki = k * i;
                    for (unsigned j = 0; j < k / 2; ++j) {
                        next(ki + (2 * j)) = current(ki + j);
                        next(ki + (2 * j) + 1) = current(ki + (k / 2) + j);
                    }
                    
                    for (unsigned j = 0; j < (k / 2) - 1; ++j) {
                        exchange(next(ki + (2 * j) + 1), next(ki + (2 * (j + 1))));
                    }
                }
                std::swap(m_current, m_next);
            }
        }        

        bool is_power_of2(unsigned n) const {
            return n != 0 && ((n-1) & n) == 0;
        }
        
    public:
        sorting_network(Ext& ext, typename Ext::vector& es):
            m_ext(ext),
            m_es(es),
            m_current(&m_currentv),
            m_next(&m_nextv)
        {}
        
        void operator()(typename Ext::vector const& inputs) {
            if (inputs.size() <= 1) {
                return;
            }
            m_es.reset();
            m_es.append(inputs);
            while (!is_power_of2(m_es.size())) {
                m_es.push_back(m_ext.mk_default());
            }
            for (unsigned i = 0; i < m_es.size(); ++i) {
                current(i) = i;
            }
            unsigned k = 2;
            while (k <= m_es.size()) {
                sort(k);
                k *= 2;
            }
        }        
    };

#endif
