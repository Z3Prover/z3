/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_case_split_queue.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-20.

Revision History:

--*/
#ifndef _SMT_CASE_SPLIT_QUEUE_H_
#define _SMT_CASE_SPLIT_QUEUE_H_

#include"smt_types.h"
#include"heap.h"
#include"smt_params.h"

namespace smt {
    class context;

    /**
       \brief Abstract case split queue.
    */
    class case_split_queue {
    public:
        virtual void activity_increased_eh(bool_var v) = 0;
        virtual void mk_var_eh(bool_var v) = 0;
        virtual void del_var_eh(bool_var v) = 0;
        virtual void assign_lit_eh(literal l) {}
        virtual void unassign_var_eh(bool_var v) = 0;
        virtual void relevant_eh(expr * n) = 0;
        virtual void init_search_eh() = 0;
        virtual void end_search_eh() = 0;
        virtual void internalize_instance_eh(expr * e, unsigned gen) {}
        virtual void reset() = 0;
        virtual void push_scope() = 0;
        virtual void pop_scope(unsigned num_scopes) = 0;
        virtual void next_case_split(bool_var & next, lbool & phase) = 0;
        virtual void display(std::ostream & out) = 0;
        virtual ~case_split_queue() {}
    };

    case_split_queue * mk_case_split_queue(context & ctx, smt_params & p);
};

#endif /* _SMT_CASE_SPLIT_QUEUE_H_ */

