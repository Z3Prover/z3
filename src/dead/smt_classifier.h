/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_classifier.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-24.

Revision History:

--*/
#ifndef _SMT_CLASSIFIER_H_
#define _SMT_CLASSIFIER_H_

#include"static_features.h"

namespace smt {

    class classifier {
        context     &     m_context;
        ast_manager &     m_manager;
        static_features   m_static_features;
        symbol            m_logic;
    public:
        classifier(context & c);
        /**
           \brief Give a hint by specifying the logic used to describe a problem.
        */
        void set_logic(symbol & s);
        /**
           \brief Setup the logical context for solving the following formulas.
        */
        void setup(unsigned num_formulas, expr * const * fs);
    };
    
};

#endif /* _SMT_CLASSIFIER_H_ */

