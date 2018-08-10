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

    bool theory_jobscheduler::internalize_atom(app * atom, bool gate_ctx) {
        return false;
    }

    bool theory_jobscheduler::internalize_term(app * term) {
        return false;
    }

    void theory_jobscheduler::assign_eh(bool_var v, bool is_true) {

    }

    void theory_jobscheduler::new_eq_eh(theory_var v1, theory_var v2) {

    }

    void theory_jobscheduler::new_diseq_eh(theory_var v1, theory_var v2) {

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
        SASSERT(start < end);
        m_resources.reserve(r + 1);
        m_resources[r].m_available.push_back(res_available(max_loadpct, start, end));
    }
    
};

