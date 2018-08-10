/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_jobscheduler.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2018-09-08.

Revision History:

--*/

#include "smt/theory_jobscheduler.h"
#include "smt/smt_context.h"

namespace smt {

    theory_var theory_jobscheduler::mk_var(enode * n) {
        theory_var v = theory::mk_var(n);
        return v;
    }

    bool theory_jobscheduler::internalize_term(app * term) {
        context & ctx = get_context();        
        if (ctx.e_internalized(term))
            return true;
        enode* e = ctx.mk_enode(term, false, false, true);
        switch (static_cast<js_op_kind>(term->get_decl()->get_decl_kind())) {            
        case OP_JS_JOB: {
            unsigned j = u.job2id(term);
            app_ref start(u.mk_start(j), m);
            app_ref end(u.mk_end(j), m);
            app_ref res(u.mk_resource(j), m);
            if (!ctx.e_internalized(start)) ctx.internalize(start, false);
            if (!ctx.e_internalized(end))   ctx.internalize(end, false);
            if (!ctx.e_internalized(res))   ctx.internalize(res, false);
            theory_var v = mk_var(e);
            SASSERT(m_var2index.size() == v);
            m_var2index.push_back(j);
            m_jobs.reserve(j + 1);
            m_jobs[j].m_start    = ctx.get_enode(start);
            m_jobs[j].m_end      = ctx.get_enode(end);
            m_jobs[j].m_resource = ctx.get_enode(res);
            ctx.attach_th_var(e, this, v);
            break;
        }
        case OP_JS_RESOURCE: {
            theory_var v = mk_var(e);
            SASSERT(m_var2index.size() == v);
            unsigned r = u.resource2id(term);
            m_var2index.push_back(r);        
            ctx.attach_th_var(e, this, v);    
            break;
        }
        case OP_JS_START:
        case OP_JS_END:
        case OP_JS_JOB2RESOURCE: {
            unsigned j = u.job2id(term);
            app_ref job(u.mk_job(j), m);
            if (!ctx.e_internalized(job)) ctx.internalize(job, false);
            break;
        }
        }
        return true;
    }


    void theory_jobscheduler::push_scope_eh() {
    }

    void theory_jobscheduler::pop_scope_eh(unsigned num_scopes) {
    }

    final_check_status theory_jobscheduler::final_check_eh() {
        return FC_DONE;
    }

    bool theory_jobscheduler::can_propagate() {
        return false;
    }

    void theory_jobscheduler::propagate() {
        
    }
        
    theory_jobscheduler::theory_jobscheduler(ast_manager& m): theory(m.get_family_id("jobshop")), m(m), u(m) {

    }
        
    void theory_jobscheduler::display(std::ostream & out) const {

    }
        
    void theory_jobscheduler::collect_statistics(::statistics & st) const {

    }

    void theory_jobscheduler::init_model(model_generator & m) {

    }
    
    model_value_proc * theory_jobscheduler::mk_value(enode * n, model_generator & mg) {
        return nullptr;
    }

    bool theory_jobscheduler::get_value(enode * n, expr_ref & r) {
        return false;
    }

    theory * theory_jobscheduler::mk_fresh(context * new_ctx) { 
        return alloc(theory_jobscheduler, new_ctx->get_manager()); 
    }

    uint64_t theory_jobscheduler::est(unsigned j) {
        return 0;
    }

    uint64_t theory_jobscheduler::lst(unsigned j) {
        return 0;
    }

    uint64_t theory_jobscheduler::ect(unsigned j) {
        return 0;
    }

    uint64_t theory_jobscheduler::lct(unsigned j) {
        return 0;
    }

    uint64_t theory_jobscheduler::start(unsigned j) {
        return 0;
    }

    uint64_t theory_jobscheduler::end(unsigned j) {
        return 0;
    }

    unsigned theory_jobscheduler::resource(unsigned j) {
        return 0;
    }


    void theory_jobscheduler::add_job_resource(unsigned j, unsigned r, unsigned cap, unsigned loadpct, uint64_t end) {
        // assert: done at base level
        m_jobs.reserve(j + 1);
        m_resources.reserve(r + 1);
        job_info& ji = m_jobs[j];
        if (ji.m_resource2index.contains(r)) {
            throw default_exception("resource already bound to job");
        }
        ji.m_resource2index.insert(r, ji.m_resources.size());
        ji.m_resources.push_back(job_resource(r, cap, loadpct, end));
        SASSERT(!m_resources[r].m_jobs.contains(j));
        m_resources[r].m_jobs.push_back(j);
    }

    void theory_jobscheduler::add_resource_available(unsigned r, unsigned max_loadpct, uint64_t start, uint64_t end) {
        // assert: done at base level
        SASSERT(start < end);
        m_resources.reserve(r + 1);
        m_resources[r].m_available.push_back(res_available(max_loadpct, start, end));
    }
    
};

