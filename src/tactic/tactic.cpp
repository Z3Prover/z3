/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic.h

Abstract:

    Abstract tactic object.

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#include<iomanip>
#include "tactic/tactic.h"
#include "tactic/probe.h"
#include "util/stopwatch.h"
#include "model/model_v2_pp.h"


struct tactic_report::imp {
    char const *    m_id;
    goal const &    m_goal;
    stopwatch       m_watch;
    double          m_start_memory;

    imp(char const * id, goal const & g):
        m_id(id),
        m_goal(g),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
        TRACE("tactic", g.display_with_proofs(tout << id << "\n"););
        SASSERT(g.is_well_formed());
    }
        
    ~imp() {
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        TRACE("tactic", m_goal.display(tout << m_id << "\n");
              if (m_goal.mc()) m_goal.mc()->display(tout);
              );
        IF_VERBOSE(0, 
                   verbose_stream() << "(" << m_id
                   << " :num-exprs " << m_goal.num_exprs()
                   << " :num-asts " << m_goal.m().get_num_asts()
                   << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds()
                   << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory
                   << " :after-memory " << std::fixed << std::setprecision(2) << end_memory
                   << ")" << std::endl);
        SASSERT(m_goal.is_well_formed());
    }
};

tactic_report::tactic_report(char const * id, goal const & g) {
    if (get_verbosity_level() >= TACTIC_VERBOSITY_LVL)
        m_imp = alloc(imp, id, g);
    else
        m_imp = nullptr;
}

tactic_report::~tactic_report() {
    if (m_imp)
        dealloc(m_imp);
}

void report_tactic_progress(char const * id, unsigned val) {
    if (val > 0) {
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(" << id << " " << val << ")" << std::endl;);
    }
}

void skip_tactic::operator()(goal_ref const & in, goal_ref_buffer& result) {
    result.push_back(in.get());
}

tactic * mk_skip_tactic() {
    return alloc(skip_tactic);
}

class fail_tactic : public tactic {
public:
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        throw tactic_exception("fail tactic");
    }

    void cleanup() override {}

    tactic * translate(ast_manager & m) override { return this; }
};

tactic * mk_fail_tactic() {
    return alloc(fail_tactic);
}

class report_verbose_tactic : public skip_tactic {
    char const * m_msg;
    unsigned     m_lvl;
public:
    report_verbose_tactic(char const * msg, unsigned lvl) : m_msg(msg), m_lvl(lvl) {}

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        IF_VERBOSE(m_lvl, verbose_stream() << m_msg << "\n";);
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_report_verbose_tactic(char const * msg, unsigned lvl) {
    return alloc(report_verbose_tactic, msg, lvl);
}

class trace_tactic : public skip_tactic {
    char const * m_tag;
public:
    trace_tactic(char const * tag): m_tag(tag) {}
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        TRACE(m_tag, in->display(tout););
        (void)m_tag;
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_trace_tactic(char const * tag) {
    return alloc(trace_tactic, tag);
}

class fail_if_undecided_tactic : public skip_tactic {
public:
    fail_if_undecided_tactic() {}

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (!in->is_decided()) 
            throw tactic_exception("undecided");
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_fail_if_undecided_tactic() {
    return alloc(fail_if_undecided_tactic);
}

void exec(tactic & t, goal_ref const & in, goal_ref_buffer & result) {
    t.reset_statistics();
    try {
        t(in, result);
        t.cleanup();
    }
    catch (tactic_exception & ex) {
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(tactic-exception \"" << escaped(ex.msg()) << "\")" << std::endl;);
        t.cleanup();
        throw ex;
    }
}


lbool check_sat(tactic & t, goal_ref & g, model_ref & md, labels_vec & labels, proof_ref & pr, expr_dependency_ref & core, std::string & reason_unknown) {
    bool models_enabled = g->models_enabled();
    bool cores_enabled  = g->unsat_core_enabled();
    md   = nullptr;
    pr   = nullptr;
    core = nullptr;
    ast_manager & m = g->m();
    goal_ref_buffer r;
    try {
        exec(t, g, r);
    }
    catch (z3_exception & ex) {
        reason_unknown = ex.msg();
        if (r.size() > 0) pr = r[0]->pr(0);
        return l_undef;
    }
    TRACE("tactic",
          tout << "r.size(): " << r.size() << "\n";
          for (unsigned i = 0; i < r.size(); i++) r[i]->display_with_dependencies(tout););

    if (r.size() > 0) {
        pr = r[0]->pr(0);
        CTRACE("tactic", pr, tout << pr << "\n";);
    }
    

    if (is_decided_sat(r)) {
        model_converter_ref mc = r[0]->mc();            
        if (mc.get()) {
            (*mc)(labels);
            model_converter2model(m, mc.get(), md);
        }
        if (!m.inc()) {
            reason_unknown = "canceled";
            return l_undef;
        }
        if (!md) {
            // create empty model.
            md = alloc(model, m);
        }
        return l_true;
    }
    else if (is_decided_unsat(r)) {
        goal * final = r[0];
        SASSERT(m.is_false(final->form(0)));
        pr = final->pr(0);
        if (cores_enabled)  core = final->dep(0);
        return l_false;
    }
    else {
        if (models_enabled && !r.empty()) {
            model_converter_ref mc = r[0]->mc();            
            model_converter2model(m, mc.get(), md);
            if (mc)
                (*mc)(labels);
        }
        reason_unknown = "incomplete";
        return l_undef;
    }
}

void fail_if_proof_generation(char const * tactic_name, goal_ref const & in) {
    if (in->proofs_enabled()) {
        std::string msg = tactic_name;
        msg += " does not support proof production";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_unsat_core_generation(char const * tactic_name, goal_ref const & in) {
    if (in->unsat_core_enabled()) {
        std::string msg = tactic_name;
        msg += " does not support unsat core production";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_model_generation(char const * tactic_name, goal_ref const & in) {
    if (in->models_enabled()) {
        std::string msg = tactic_name;
        msg += " does not generate models";
        throw tactic_exception(std::move(msg));
    }
}

void fail_if_has_quantifiers(char const* tactic_name, goal_ref const& g) {
    for (unsigned i = 0; i < g->size(); ++i)
        if (has_quantifiers(g->form(i))) {
            std::string msg = tactic_name;
            msg += " does not apply to quantified goals";
            throw tactic_exception(std::move(msg));
        }
}

void tactic::checkpoint(ast_manager& m) {
    if (!m.inc())
        throw tactic_exception(m.limit().get_cancel_msg());
}
