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
    
#if 0
    /**
       \brief Congruence table.
    */
    class cg_table {
        struct cg_khasher {
            unsigned operator()(enode const * n) const { return n->get_decl_id(); }
        };

        struct cg_chasher {
            unsigned operator()(enode const * n, unsigned idx) const { 
                return n->get_arg(idx)->get_root()->hash();
            }
        };

        struct cg_hash {
            cg_khasher m_khasher;
            cg_chasher m_chasher;
        public:
            unsigned operator()(enode * n) const;
        };

        struct cg_eq {
            bool & m_commutativity; 
            cg_eq(bool & comm):m_commutativity(comm) {}
            bool operator()(enode * n1, enode * n2) const;
        };

        typedef ptr_hashtable<enode, cg_hash, cg_eq> table;

        ast_manager &             m_manager;
        bool                      m_commutativity; //!< true if the last found congruence used commutativity
        table                     m_table;
    public:
        cg_table(ast_manager & m);

        /**
           \brief Try to insert n into the table. If the table already
           contains an element n' congruent to n, then do nothing and
           return n' and a boolean indicating whether n and n' are congruence
           modulo commutativity, otherwise insert n and return (n,false).
        */
        enode_bool_pair insert(enode * n) {
            // it doesn't make sense to insert a constant.
            SASSERT(n->get_num_args() > 0);
            m_commutativity = false;
            enode * n_prime = m_table.insert_if_not_there(n); 
            SASSERT(contains(n));
            return enode_bool_pair(n_prime, m_commutativity);
        }

        void erase(enode * n) {
            SASSERT(n->get_num_args() > 0);
            m_table.erase(n);
            SASSERT(!contains(n));
        }

        bool contains(enode * n) const {
            return m_table.contains(n);
        }

        enode * find(enode * n) const {
            enode * r = 0;
            return m_table.find(n, r) ? r : 0;
        }

        bool contains_ptr(enode * n) const {
            enode * n_prime;
            return m_table.find(n, n_prime) && n == n_prime;
        }

        void reset() {
            m_table.reset();
        }

        void display(std::ostream & out) const;

        void display_compact(std::ostream & out) const;
#ifdef Z3DEBUG
        bool check_invariant() const;
#endif
    };
#else 
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
                // too many collisions
                // unsigned r = 17 + n->get_arg(0)->get_root()->hash();
                // return r * 31 + n->get_arg(1)->get_root()->hash();
                return combine_hash(n->get_arg(0)->get_root()->hash(), n->get_arg(1)->get_root()->hash());
            }
        };

        struct cg_binary_eq {
            bool operator()(enode * n1, enode * n2) const {
                SASSERT(n1->get_num_args() == 2);
                SASSERT(n2->get_num_args() == 2);
                SASSERT(n1->get_decl() == n2->get_decl());
#if 1
                return 
                    n1->get_arg(0)->get_root() == n2->get_arg(0)->get_root() &&
                    n1->get_arg(1)->get_root() == n2->get_arg(1)->get_root();
#else
                bool r = 
                    n1->get_arg(0)->get_root() == n2->get_arg(0)->get_root() &&
                    n1->get_arg(1)->get_root() == n2->get_arg(1)->get_root();
                static unsigned counter = 0;
                static unsigned failed  = 0;
                if (!r) 
                    failed++;
                counter++;
                if (counter % 100000 == 0) 
                    std::cerr << "[cg_eq] " << counter << " " << failed << "\n";
                return r;
#endif
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
        enode_bool_pair insert(enode * n) {
            // it doesn't make sense to insert a constant.
            SASSERT(n->get_num_args() > 0);
            enode * n_prime;
            void * t = get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                n_prime = UNTAG(unary_table*, t)->insert_if_not_there(n);
                return enode_bool_pair(n_prime, false);
            case BINARY:
                n_prime = UNTAG(binary_table*, t)->insert_if_not_there(n);
                return enode_bool_pair(n_prime, false);
            case BINARY_COMM:
                m_commutativity = false;
                n_prime = UNTAG(comm_table*, t)->insert_if_not_there(n);
                return enode_bool_pair(n_prime, m_commutativity);
            default:
                n_prime = UNTAG(table*, t)->insert_if_not_there(n);
                return enode_bool_pair(n_prime, false);
            }
        }

        void erase(enode * n) {
            SASSERT(n->get_num_args() > 0);
            void * t = get_table(n); 
            switch (static_cast<table_kind>(GET_TAG(t))) {
            case UNARY:
                UNTAG(unary_table*, t)->erase(n);
                break;
            case BINARY:
                UNTAG(binary_table*, t)->erase(n);
                break;
            case BINARY_COMM:
                UNTAG(comm_table*, t)->erase(n);
                break;
            default:
                UNTAG(table*, t)->erase(n);
                break;
            }
        }

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

        void display_compact(std::ostream & out) const;
#ifdef Z3DEBUG
        bool check_invariant() const;
#endif
    };

#endif 
};

#endif /* SMT_CG_TABLE_H_ */

