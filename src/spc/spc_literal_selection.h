/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_literal_selection.h

Abstract:

    Superposition Calculus Literal Selection

Author:

    Leonardo de Moura (leonardo) 2008-02-05.

Revision History:

--*/
#ifndef _SPC_LITERAL_SELECTION_H_
#define _SPC_LITERAL_SELECTION_H_

#include"spc_clause.h"
#include"order.h"

namespace spc {
    
    /**
       \brief Abstract functor for literal selection.
    */
    class literal_selection {
    public:
        virtual ~literal_selection() {}
        /**
           \brief Updates the selected status flag of the literals of the given clause.
        */
        virtual void operator()(clause * cls) = 0;
    };

    /**
       \brief Never selects a literal. This strategy is supposed to be good for planning problems 
       of TPTP.
    */
    class no_literal_selection : public literal_selection {
    public:
        virtual void operator()(clause * cls) {}
    };

    
    /**
       \brief Selects a negative literal l with the largest V(l)
       where V is defined as:

       - difference in symbol count for the left-right hand sides of equalities, .

       - symbol count for other predicates
       
    */
    class diff_literal_selection : public literal_selection {
    protected:
        ast_manager & m_manager;
    public:
        diff_literal_selection(ast_manager & m):m_manager(m) {}
        virtual void operator()(clause * cls);
    };

    /**
      \brief Selects a negative literal using the following algo:

      - if there is x != y, select it.

      - else if there is negative ground literal, select the smallest one.

      - else if use the approach in diff_literal_selection.
    */
    class complex_literal_selection : public diff_literal_selection {
    public:
        complex_literal_selection(ast_manager & m):diff_literal_selection(m) {}
        virtual void operator()(clause * cls);
    };

    /**
       \brief Similar to diff_literal_selection, but a literal
       is not selected if the clause contains a positive literal
       greater than all other literals.
    */
    class max_no_selection : public diff_literal_selection {
        order & m_order;
    public:
        max_no_selection(order & o):diff_literal_selection(o.get_manager()), m_order(o) {}
        virtual void operator()(clause * cls);
    };

};

#endif /* _SPC_LITERAL_SELECTION_H_ */
