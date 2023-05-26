/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_internalizer.h

Abstract:

    Header for SMT theories over SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "util/sat_literal.h"

namespace sat {
    class sat_internalizer {
    public:
        virtual ~sat_internalizer() = default;
        virtual bool is_bool_op(expr* e) const = 0;
        virtual literal internalize(expr* e) = 0;
        virtual bool_var to_bool_var(expr* e) = 0;
        virtual bool_var add_bool_var(expr* e)  = 0;
        virtual literal get_cached(app* t) const = 0;
        virtual bool is_cached(app* t, literal l) const = 0;
        virtual void cache(app* t, literal l) = 0;
        virtual void uncache(literal l) = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual void set_expr2var_replay(obj_map<expr, sat::bool_var>* r) = 0;
    };
}
