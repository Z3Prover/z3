/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_costs.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-20.

Revision History:

--*/

#pragma once

#include<iosfwd>

#include "ast/ast.h"

class stopwatch;

namespace datalog {

    class context;
    class rule;

    class cost_recorder;

    struct costs {
        typedef unsigned time_type;

        time_type milliseconds;
        unsigned instructions;

        costs();

        bool empty() const;
        void reset();

        costs operator-(const costs & o) const;
        void operator+=(const costs & o);

        bool passes_thresholds(context & ctx) const;

        void output(std::ostream & out) const;
    };


    class accounted_object {
        friend class cost_recorder;

        context * m_context;
        rule * m_parent_object;

        costs m_current_cost;
        costs m_processed_cost;
        bool m_being_recorded;
    protected:
        accounted_object() : m_context(nullptr), m_parent_object(nullptr), m_being_recorded(false) {}
        ~accounted_object();
    public:

        void set_accounting_parent_object(context & ctx, rule * parent);
        rule * get_parent_object() const { return m_parent_object; }

        costs & get_current_costs() { return m_current_cost; }
        const costs & get_current_costs() const { return m_current_cost; }
        const costs & get_processed_costs() const { return m_processed_cost; }
        void get_total_cost(costs & result) const;
        bool being_recorded() const { return m_being_recorded; }

        void process_costs();

        bool passes_output_thresholds(context & ctx) const;
        void output_profile(std::ostream & out) const;

    private:
        //private and undefined copy constructor and operator= to avoid the default ones
        accounted_object(const accounted_object &);
        accounted_object& operator=(const accounted_object &);
    };


    class cost_recorder {
        accounted_object * m_obj;
        //it's a pointer to avoid everything depending on the stopwatch.h 
        //(and transitively then on windows.h) header file
        stopwatch * m_stopwatch;

        bool m_running;
        uint64_t m_last_time;
    public:
        cost_recorder();
        ~cost_recorder();
        /**
           \brief Start recording costs for the next object.

           If the recording of the previous object did not finish, it will be finished here.
           Also, it will be done more efficiently than if the \c finish() function was called
           before separately.
         */
        void start(accounted_object *);
        void finish() { start(nullptr); }
    };
};


