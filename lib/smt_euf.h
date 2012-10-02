/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_euf.h

Abstract:

    Equality and uninterpreted functions

Author:

    Leonardo de Moura (leonardo) 2012-02-14.

Revision History:

--*/
#ifndef _SMT_EUF_H_
#define _SMT_EUF_H_

#include"ast.h"
#include"smt_enode.h"
#include"smt_eq_justification.h"

namespace smt {
    class context;

    class euf_manager {
        struct imp;
        imp * m_imp;
    public:
        euf_manager(context & ctx);
        ~euf_manager();

        enode * mk_enode(app * n, bool suppress_args, bool merge_tf, bool cgc_enabled);
        
        void add_eq(enode * n1, enode * n2, eq_justification js);
        bool assume_eq(enode * lhs, enode * rhs);
        void reset();
        
        static bool is_eq(enode const * n1, enode const * n2) { return n1->get_root() == n2->get_root(); }
        bool is_diseq(enode * n1, enode * n2) const;
        bool is_ext_diseq(enode * n1, enode * n2, unsigned depth);
        enode * get_enode_eq_to(func_decl * f, unsigned num_args, enode * const * args);
        bool is_shared(enode * n) const;

        unsigned get_num_enodes_of(func_decl const * decl) const;
        enode_vector::const_iterator begin_enodes_of(func_decl const * decl) const;
        enode_vector::const_iterator end_enodes_of(func_decl const * decl) const;
    };
};


#endif
