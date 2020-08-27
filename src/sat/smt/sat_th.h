/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.h

Abstract:

    Theory plugins

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "sat/smt/sat_smt.h"
#include "ast/euf/euf_egraph.h"

namespace sat {
    

    class th_dependencies {
    public:
        th_dependencies() {}
        euf::enode * const* begin() const { return nullptr; }
        euf::enode * const* end() const { return nullptr; }

        /*
         * \brief add dependency: dst depends on src.
         */
        void add(euf::enode* src, euf::enode* dst);

        /*
         * \brief sort dependencies.
         */
        void sort();
    };

    class th_internalizer {
    public:
        virtual literal internalize(sat_internalizer& si, expr* e, bool sign, bool root) = 0;
        virtual ~th_internalizer() {}
    };

    class th_model_builder {
    public:

        virtual ~th_model_builder() {}

        /**
           \brief compute the value for enode \c n and store the value in \c values 
           for the root of the class of \c n.
         */
        virtual void add_value(euf::enode* n, expr_ref_vector& values) = 0;

        /**
           \brief compute dependencies for node n
         */
        virtual void add_dep(euf::enode* n, th_dependencies& dep) = 0;
    };


}
