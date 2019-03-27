/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_cg_table.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef SMT_CG_TABLE_H_
#define SMT_CG_TABLE_H_

#include "smt/smt_enode.h"
#include "util/hashtable.h"
#include "util/chashtable.h"

namespace smt {

    typedef std::pair<enode *, bool> enode_bool_pair;
    
    // one table per function symbol

    /**
       \brief Congruence table.
    */
    class cg_table {
        struct cg_unary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 1);
                return n->get_arg(0)->get_root()->hash();
            }
        };

        struct cg_unary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 1);
                SASSERT(n2->get_num_args() == 1);
                SASSERT(n1->get_decl() == n2->get_decl());
                return n1->get_arg(0)->get_root() == n2->get_arg(0)->get_root();
            }
        };

        typedef chashtable<enode *, cg_unary_hash, cg_unary_eq> unary_table;
        
        struct cg_binary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 2);
                return combine_hash(n->get_arg(0)->get_root()->hash(), n->get_arg(1)->get_root()->hash());
            }
        };

        struct cg_binary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 2);
                SASSERT(n2->get_num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
                return 
                    n1->get_arg(0)->get_root() == n2->get_arg(0)->get_root() &&
                    n1->get_arg(1)->get_root() == n2->get_arg(1)->get_root();
            }
        };

        typedef chashtable<enode*, cg_binary_hash, cg_binary_eq> binary_table;
        
        struct cg_comm_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->get_num_args() == 2);
                unsigned h1 = n->get_arg(0)->get_root()->hash();
                unsigned h2 = n->get_arg(1)->get_root()->hash();
                if (h1 > h2)
                    std::swap(h1, h2);
                return hash_u((h1 << 16) | (h2 & 0xFFFF));
            }
        };
        
        struct cg_comm_eq {
            bool & m_commutativity;
            cg_comm_eq(bool & c):m_commutativity(c) {}
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 2);
                SASSERT(n2->get_num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
                enode * c1_1 = n1->get_arg(0)->get_root();
                enode * c1_2 = n1->get_arg(1)->get_root();
                enode * c2_1 = n2->get_arg(0)->get_root();
                enode * c2_2 = n2->get_arg(1)->get_root();
                if (c1_1 == c2_1 && c1_2 == c2_2) {
                    return true;
                }
                if (c1_1 == c2_2 && c1_2 == c2_1) {
                    m_commutativity = true;
                    return true;
                }
                return false;
            }
        };

        typedef chashtable<enode*, cg_comm_hash, cg_comm_eq> comm_table;

        struct cg_hash {
            unsigned operator()(enode * n) const;
        };

        struct cg_eq {
            bool operator()(enode * n1, enode * n2) const;
        };

        typedef chashtable<enode*, cg_hash, cg_eq> table;

        ast_manager &                 m_manager;
        bool                          m_commutativity; //!< true if the last found congruence used commutativity
        ptr_vector<void>              m_tables;
        obj_map<func_decl, unsigned>  m_func_decl2id;

        enum table_kind {
            UNARY,
            BINARY,
            BINARY_COMM,
            NARY
        };

        void * mk_table_for(func_decl * d);
        unsigned set_func_decl_id(enode * n);
        
        void * get_table(enode * n) {
            unsigned tid = n->get_func_decl_id();
            if (tid == UINT_MAX)
                tid = set_func_decl_id(n);
            SASSERT(tid < m_tables.size());
            return m_tables[tid];
        }

    public:
        cg_table(ast_manager & m);
        ~cg_table();

        /**
           \brief Try to insert n into the table. If the table already
           contains an element n' congruent to n, then do nothing and
           return n' and a boolean indicating whether n and n' are congruence
           modulo commutativity, otherwise insert n and return (n,false).
        */
        enode_bool_pair insert(enode * n);

        void erase(enode * n);

        bool contains(enode * n) const {
            SASSERT(n->get_num_args() > 0);
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->contains(n);
            case BINARY:
                return UNTAG(binary_table*, t)->contains(n);
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->contains(n);
            default:
                return UNTAG(table*, t)->contains(n);
            }
        }

        enode * find(enode * n) const {
            SASSERT(n->get_num_args() > 0);
            enode * r = nullptr;
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->find(n, r) ? r : nullptr;
            case BINARY:
                return UNTAG(binary_table*, t)->find(n, r) ? r : nullptr;
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->find(n, r) ? r : nullptr;
            default:
                return UNTAG(table*, t)->find(n, r) ? r : nullptr;
            }
        }

        bool contains_ptr(enode * n) const {
            enode * r;
            SASSERT(n->get_num_args() > 0);
            void * t = const_cast<cg_table*>(this)->get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                return UNTAG(unary_table*, t)->find(n, r) && n == r;
            case BINARY:
                return UNTAG(binary_table*, t)->find(n, r) && n == r;
            case BINARY_COMM:
                return UNTAG(comm_table*, t)->find(n, r) && n == r;
            default:
                return UNTAG(table*, t)->find(n, r) && n == r;
            }
        }

        void reset();

        void display(std::ostream & out) const;

        void display_binary(std::ostream& out, void* t) const;

        void display_binary_comm(std::ostream& out, void* t) const;

        void display_unary(std::ostream& out, void* t) const;

        void display_nary(std::ostream& out, void* t) const;

        void display_compact(std::ostream & out) const;

        bool check_invariant() const;
    };

};

#endif /* SMT_CG_TABLE_H_ */

