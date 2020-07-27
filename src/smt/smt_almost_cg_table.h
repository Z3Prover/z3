/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_almost_cg_table.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-03-06.

Revision History:

--*/
#pragma once

#include "smt/smt_enode.h"
#include "util/map.h"

namespace smt {
    
    /**
       \brief An index for detecting 'almost' congruences. 
       We say (f t_1 ... t_n) is almost congruent to (f s_1 ... s_n) with respect to (r1,r2) iff
       for all j in [1,n] j  t_j = s_j or (t_j = r1 and s_j = r1) or (t_j = r1 and s_j = r2) or (t_j = r2 and s_j = r1) or (t_j = r2 and s_j = r2)
       
       This index is used to speedup is_ext_diseq.
    */
    class almost_cg_table {
        struct cg_hash {
            enode * & m_r1;
            enode * & m_r2;
            unsigned arg_hash(enode * n, unsigned idx) const;
        public:
            cg_hash(enode * & r1, enode * & r2):m_r1(r1), m_r2(r2) {}
            unsigned operator()(enode * n) const;
        };

        struct cg_eq {
            enode * & m_r1;
            enode * & m_r2;
        public:
            cg_eq(enode * & r1, enode * & r2):m_r1(r1), m_r2(r2) {}
            bool operator()(enode * n1, enode * n2) const;
        };
        
        typedef map<enode *, list<enode*> *, cg_hash, cg_eq> table; 
        
        region  m_region;
        enode * m_r1;
        enode * m_r2;
        table   m_table;

    public:
        almost_cg_table(enode * r1 = nullptr, enode * r2 = nullptr);
        void reset(enode * r1, enode * r2) { m_r1 = r1->get_root(); m_r2 = r2->get_root(); reset(); }
        void reset();
        void insert(enode *);
        void erase(enode * n) { m_table.erase(n); }
        list<enode*> * find(enode *);
        bool empty() const { return m_table.empty(); }
    };

};


