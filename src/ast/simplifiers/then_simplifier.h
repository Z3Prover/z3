/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    then_simplifier.h

Abstract:

    create a simplifier from a sequence of simplifiers

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "util/stopwatch.h"
#include "ast/simplifiers/dependent_expr_state.h"


class then_simplifier : public dependent_expr_simplifier {
    scoped_ptr_vector<dependent_expr_simplifier> m_simplifiers;

    struct collect_stats {
        stopwatch       m_watch;
        double          m_start_memory = 0;
        dependent_expr_simplifier& s;
        collect_stats(dependent_expr_simplifier& s) : 
            m_start_memory(static_cast<double>(memory::get_allocation_size()) / static_cast<double>(1024 * 1024)), 
            s(s) {
            m_watch.start();
        }
        ~collect_stats() {
            m_watch.stop();
            double end_memory = static_cast<double>(memory::get_allocation_size()) / static_cast<double>(1024 * 1024);
            IF_VERBOSE(10,
                statistics st;
                verbose_stream() << "(" << s.name()
                << " :num-exprs " << s.get_fmls().num_exprs()
                << " :num-asts " << s.get_manager().get_num_asts()
                << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds()
                << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory
                << " :after-memory " << std::fixed << std::setprecision(2) << end_memory
                << ")" << "\n";
            s.collect_statistics(st);
            if (st.size() > 0)
                st.display_smt2(verbose_stream()));
        }
    };

protected:
    
    bool m_bail_on_no_change = false;
    
public:
    
    then_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls) {
    }

    char const* name() const override { return "and-then"; }
    
    void add_simplifier(dependent_expr_simplifier* s) {
        m_simplifiers.push_back(s);
    }
        
    void reduce() override {
        TRACE("simplifier", tout << m_fmls);
        for (auto* s : m_simplifiers) {
            if (m_fmls.inconsistent())
                break;
            if (!m.inc())
                break;
            s->reset_statistics();
            collect_stats _cs(*s);
            m_fmls.reset_updated();
            try {
                s->reduce();
                m_fmls.flatten_suffix();
            }
            catch (rewriter_exception &) {
                break;
            }
            TRACE("simplifier", tout << s->name() << "\n" << m_fmls);
            if (m_bail_on_no_change && !m_fmls.updated())
                break;
        }      
    }
    
    void collect_statistics(statistics& st) const override {
        for (auto* s : m_simplifiers)
            s->collect_statistics(st);
    }
    
    void reset_statistics() override {
        for (auto* s : m_simplifiers)
            s->reset_statistics();
    }
    
    void updt_params(params_ref const& p) override {
        for (auto* s : m_simplifiers)
            s->updt_params(p);        
    }
    
    void collect_param_descrs(param_descrs& r) override {
        for (auto* s : m_simplifiers)
            s->collect_param_descrs(r);
    }
    
    void push() override {
        for (auto* s : m_simplifiers)
            s->push();       
    }
    
    void pop(unsigned n) override {
        for (auto* s : m_simplifiers)
            s->pop(n);     
    }
};

class if_change_simplifier : public then_simplifier {
public:
    if_change_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        then_simplifier(m, p, fmls) {
        m_bail_on_no_change = true;
    }

    char const* name() const override { return "if-change-then"; }

};
