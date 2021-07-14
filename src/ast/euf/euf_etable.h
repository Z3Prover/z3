/*++ Copyright (c) 2006 Microsoft Corporation

Module Name:

    euf_etable.h

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

    copied from smt_cg_table

--*/

#pragma once

#include "ast/euf/euf_enode.h"
#include "util/hashtable.h"
#include "util/chashtable.h"

namespace euf {
    
    // one table per function symbol


    /**
       \brief Congruence table.
    */
    class etable {
        static enode* get_root(enode* n, unsigned idx) { return n->get_arg(idx)->get_root(); }

        struct cg_unary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->num_args() == 1);
                return get_root(n, 0)->hash();
            }
        };

        struct cg_unary_eq {

            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->num_args() == 1);
                SASSERT(n2->num_args() == 1);
                SASSERT(n1->get_decl() == n2->get_decl());
                return get_root(n1, 0) == get_root(n2, 0);
            }
        };

        typedef chashtable<enode *, cg_unary_hash, cg_unary_eq> unary_table;
        
        struct cg_binary_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->num_args() == 2);
                return combine_hash(get_root(n, 0)->hash(), get_root(n, 1)->hash());
            }
        };

        struct cg_binary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->num_args() == 2);
                SASSERT(n2->num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
                return
                    get_root(n1, 0) == get_root(n2, 0) &&
                    get_root(n1, 1) == get_root(n2, 1);
            }
        };

        typedef chashtable<enode*, cg_binary_hash, cg_binary_eq> binary_table;
        
        struct cg_comm_hash {
            unsigned operator()(enode * n) const {
                SASSERT(n->num_args() == 2);
                unsigned h1 = get_root(n, 0)->hash();
                unsigned h2 = get_root(n, 1)->hash(); 
                if (h1 > h2)
                    std::swap(h1, h2);
                return hash_u((h1 << 16) | (h2 & 0xFFFF));
            }
        };
        
        struct cg_comm_eq {
            bool & m_commutativity;
            cg_comm_eq(bool & c): m_commutativity(c) {}
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->num_args() == 2);
                SASSERT(n2->num_args() == 2);
                if (n1->get_decl() != n2->get_decl())
                    return false;
                enode* c1_1 = get_root(n1, 0);  
                enode* c1_2 = get_root(n1, 1); 
                enode* c2_1 = get_root(n2, 0); 
                enode* c2_2 = get_root(n2, 1); 
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
        typedef std::pair<func_decl*, unsigned> decl_info;
        struct decl_hash {
            unsigned operator()(decl_info const& d) const { return d.first->hash(); }
        };
        struct decl_eq {
            bool operator()(decl_info const& a, decl_info const& b) const { return a == b; }
        };


        ast_manager &                 m_manager;
        bool                          m_commutativity{ false }; //!< true if the last found congruence used commutativity
        ptr_vector<void>              m_tables;
        map<decl_info, unsigned, decl_hash, decl_eq>  m_func_decl2id;

        enum table_kind {
            UNARY,
            BINARY,
            BINARY_COMM,
            NARY
        };

        void * mk_table_for(unsigned n, func_decl * d);
        unsigned set_table_id(enode * n);
        
        void * get_table(enode * n) {
            unsigned tid = n->get_table_id();
            if (tid == UINT_MAX)
                tid = set_table_id(n);
            SASSERT(tid < m_tables.size());
            return m_tables[tid];
        }

        void display_binary(std::ostream& out, void* t) const;
        void display_binary_comm(std::ostream& out, void* t) const;
        void display_unary(std::ostream& out, void* t) const;
        void display_nary(std::ostream& out, void* t) const;

    public:
        etable(ast_manager & m);

        ~etable();

        /**
           \brief Try to insert n into the table. If the table already
           contains an element n' congruent to n, then do nothing and
           return n' and a boolean indicating whether n and n' are congruence
           modulo commutativity, otherwise insert n and return (n,false).
        */
        enode_bool_pair insert(enode * n);

        void erase(enode * n);

        bool contains(enode* n) const;

        enode* find(enode* n) const;

        bool contains_ptr(enode* n) const;

        void reset();

        void display(std::ostream & out) const;

    };

};




