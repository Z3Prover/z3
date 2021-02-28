/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_almost_cg_table.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-03-06.

Revision History:

--*/

#include "smt/smt_almost_cg_table.h"

namespace smt {

    inline unsigned almost_cg_table::cg_hash::arg_hash(enode * n, unsigned idx) const {
        enode * arg = n->get_arg(idx)->get_root();
        if (arg == m_r1 || arg == m_r2)
            return 17;
        return arg->hash();
    }

    unsigned almost_cg_table::cg_hash::operator()(enode * n) const {
        unsigned num_args = n->get_num_args();
        unsigned kind_hash = n->get_decl_id();
        if (num_args == 1)
            return kind_hash;
        unsigned a = 0x9e3779b9;
        unsigned b = 0x9e3779b9;
        unsigned c = 11;    

        switch (num_args) {
        case 2:
            a += kind_hash;
            b += arg_hash(n, 0);
            c += arg_hash(n, 1);
            mix(a, b, c);
            return c;
        case 3:
            a += kind_hash;
            b += arg_hash(n, 0);
            c += arg_hash(n, 1);
            mix(a, b, c);
            c += arg_hash(n, 1);
            mix(a, b, c);
            return c;
        default:
            while (num_args >= 3) {
                num_args--;
                a += arg_hash(n, num_args);
                num_args--;
                b += arg_hash(n, num_args);
                num_args--;
                c += arg_hash(n, num_args);
                mix(a, b, c);
            }
            
            a += kind_hash;
            switch (num_args) {
            case 2:
                b += arg_hash(n, 1);
                Z3_fallthrough;
            case 1:
                c += arg_hash(n, 0);
            }
            mix(a, b, c);
            return c;
        }
    }

    bool almost_cg_table::cg_eq::operator()(enode * n1, enode * n2) const {
        if (n1->get_expr()->get_decl() != n2->get_expr()->get_decl())
            return false;
        unsigned num_args = n1->get_num_args();
        if (num_args != n2->get_num_args())
            return false;
        for (unsigned j = 0; j < num_args; j++) {
            enode * arg1 = n1->get_arg(j)->get_root();
            enode * arg2 = n2->get_arg(j)->get_root();
            if (arg1 == arg2)
                continue;
            if ((arg1 == m_r1 || arg1 == m_r2) &&
                (arg2 == m_r1 || arg2 == m_r2))
                continue;
            return false;
        }
        return true;
    }

    almost_cg_table::almost_cg_table(enode * r1, enode * r2):
        m_r1(r1),
        m_r2(r2),
        m_table(cg_hash(m_r1, m_r2), cg_eq(m_r1, m_r2)) {
    }

    void almost_cg_table::reset() {
        m_region.reset();
        m_table.reset();
    }

    void almost_cg_table::insert(enode * n) {
        table::entry * entry = m_table.find_core(n);
        if (entry == nullptr) {
            list<enode*> * new_lst = new (m_region) list<enode*>(n, nullptr);
            m_table.insert(n, new_lst);
        }
        else {
            list<enode*> * new_lst = new (m_region) list<enode*>(n, entry->get_data().m_value);
            entry->get_data().m_value = new_lst;
        }
    }

    list<enode*> * almost_cg_table::find(enode * n) {
        list<enode*> * result = nullptr;
        m_table.find(n, result);
        return result;
    }

};
