/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_costs.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-20.

Revision History:

--*/

#include "util/debug.h"
#include "util/stopwatch.h"
#include "muz/base/dl_context.h"
#include "muz/base/dl_rule.h"
#include "muz/base/dl_costs.h"

namespace datalog {

    // -----------------------------------
    //
    // costs
    //
    // -----------------------------------

    costs::costs() : milliseconds(0), instructions(0) {}

    bool costs::empty() const { 
        return !milliseconds && !instructions;
    }

    void costs::reset() {
        milliseconds = 0;
        instructions = 0;
    }

    costs costs::operator-(const costs & o) const {
        costs res(*this);
        SASSERT(milliseconds>o.milliseconds);
        res.milliseconds-=o.milliseconds;
        SASSERT(instructions>o.instructions);
        res.instructions-=o.instructions;
        return res;
    }

    void costs::operator+=(const costs & o) {
        milliseconds+=o.milliseconds;
        instructions+=o.instructions;
    }

    bool costs::passes_thresholds(context & ctx) const {
        return milliseconds >= ctx.dl_profile_milliseconds_threshold();
    }

    void costs::output(std::ostream & out) const {
        out << "instr: " << instructions << "  time: " << milliseconds << "ms";
    }


    // -----------------------------------
    //
    // accounted_object
    //
    // -----------------------------------

    accounted_object::~accounted_object() {
        if(m_parent_object) {
            SASSERT(m_context);
            m_context->get_rule_manager().dec_ref(m_parent_object);
        }
    }

    void accounted_object::set_accounting_parent_object(context & ctx, rule * parent) {
        if(m_parent_object) {
            SASSERT(m_context);
            SASSERT(m_context==&ctx);
            m_context->get_rule_manager().dec_ref(m_parent_object);
        }
        m_context = &ctx;
        m_parent_object = parent;
        m_context->get_rule_manager().inc_ref(m_parent_object);
    }

    void accounted_object::process_costs() {
        costs delta = get_current_costs();
        if(delta.empty()) {
            return;
        }
        get_current_costs().reset();
        accounted_object * obj = this;
        do {
            obj->m_processed_cost+=delta;
            obj=obj->m_parent_object;
        } while(obj);
    }

    void accounted_object::get_total_cost(costs & result) const {
        result.reset();
        result+=m_current_cost;
        result+=m_processed_cost;
    }

    bool accounted_object::passes_output_thresholds(context & ctx) const {
        costs c;
        get_total_cost(c);
        return c.passes_thresholds(ctx);
    }


    void accounted_object::output_profile(std::ostream & out) const {
        costs c;
        get_total_cost(c);
        c.output(out);
    }


    // -----------------------------------
    //
    // cost_recorder
    //
    // -----------------------------------

    cost_recorder::cost_recorder() : m_obj(nullptr) {
        m_stopwatch = alloc(stopwatch);
        m_stopwatch->start();
    }
    
    cost_recorder::~cost_recorder() { 
        if(m_obj) {
            finish();
        }
        dealloc(m_stopwatch);
    }

    void cost_recorder::start(accounted_object * obj) {
        uint64_t curr_time = static_cast<uint64_t>(m_stopwatch->get_current_seconds()*1000);
        if(m_obj) {
            costs::time_type time_delta = static_cast<costs::time_type>(curr_time-m_last_time);
            costs & c = m_obj->get_current_costs();
            c.instructions++;
            c.milliseconds+=time_delta;
            m_obj->m_being_recorded = false;
        }
        m_running = obj!=nullptr;
        m_obj = obj;
        m_last_time = curr_time;
        if(obj) {
            m_obj->m_being_recorded = true;
        }
    }

};
