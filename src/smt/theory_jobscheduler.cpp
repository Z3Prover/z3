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
        
    theory_jobscheduler::theory_jobscheduler(ast_manager& m): 
        theory(m.get_family_id("jobshop")), m(m), u(m), a(m) {

    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, job_resource const& jr) const {
        return out << "   r:" << jr.m_resource_id << " cap:" << jr.m_capacity << " load:" << jr.m_loadpct << " end:" << jr.m_end << "\n";
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, job_info const& j) const {
        for (job_resource const& jr : j.m_resources) {
            display(out, jr);
        }
        return out;
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, res_available const& r) const {
        out << "[" << r.m_start << ":" << r.m_end << "] @ " << r.m_loadpct << "%%\n";
        return out;
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, res_info const& r) const {
        for (res_available const& ra : r.m_available) {
            display(out, ra);
        }
        return out;
    }

    void theory_jobscheduler::display(std::ostream & out) const {
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            display(out << "job " << j << ":\n", m_jobs[j]);
        }
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            display(out << "resource " << r << ":\n", m_resources[r]);
        }
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

    time_t theory_jobscheduler::est(unsigned j) {
        return 0;
    }

    time_t theory_jobscheduler::lst(unsigned j) {
        return 0;
    }

    time_t theory_jobscheduler::ect(unsigned j) {
        return 0;
    }

    time_t theory_jobscheduler::lct(unsigned j) {
        return 0;
    }

    time_t theory_jobscheduler::start(unsigned j) {
        return 0;
    }

    time_t theory_jobscheduler::end(unsigned j) {
        return 0;
    }

    unsigned theory_jobscheduler::resource(unsigned j) {
        return 0;
    }


    void theory_jobscheduler::add_job_resource(unsigned j, unsigned r, unsigned cap, unsigned loadpct, time_t end) {
        SASSERT(get_context().at_base_level());
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

    void theory_jobscheduler::add_resource_available(unsigned r, unsigned max_loadpct, time_t start, time_t end) {
        SASSERT(get_context().at_base_level());
        SASSERT(start < end);
        m_resources.reserve(r + 1);
        m_resources[r].m_available.push_back(res_available(max_loadpct, start, end));
    }

    /*
     * Initialze the state based on the set of jobs and resources added.
     * For each job j, with possible resources r1, ..., r_n assert
     *   resource(j) = r_1 || resource(j) = r_2 || ... || resource(j) = r_n
     * For each job and resource r with deadline end(j,r) assert
     *   resource(j) = r => end(j) <= end(j,r)
     *
     * Ensure that the availability slots for each resource is sorted by time.
     */
    void theory_jobscheduler::add_done() {
        context & ctx = get_context();        
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            job_info const& ji = m_jobs[j];
            expr_ref_vector disj(m);
            app_ref job(u.mk_job(j), m);
            if (ji.m_resources.empty()) {
                throw default_exception("every job should be associated with at least one resource");
            }
            // resource(j) = r => end(j) <= end(j, r)
            for (job_resource const& jr : ji.m_resources) {
                app_ref res(u.mk_resource(jr.m_resource_id), m);
                expr_ref eq(m.mk_eq(job, res), m);
                expr_ref imp(m.mk_implies(eq, a.mk_le(ji.m_start->get_owner(), a.mk_int(rational(jr.m_end, rational::ui64())))), m);
                ctx.assert_expr(imp);                
                disj.push_back(eq);
            }
            // resource(j) = r1 || ... || resource(j) = r_n
            expr_ref fml = mk_or(disj);
            ctx.assert_expr(fml);
        }        
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            vector<res_available>& available = m_resources[r].m_available;
            res_available::compare cmp;
            std::sort(available.begin(), available.end(), cmp);
            for (unsigned i = 0; i < available.size(); ++i) {
                if (i + 1 < available.size() &&
                    available[i].m_end > available[i + 1].m_start) {
                    throw default_exception("availability intervals should be disjoint");
                }
            }
        }
    }

    /**
     * check that each job is run on some resource according to 
     * requested capacity.
     * 
     * Check that the sum of jobs run in each time instance
     * does not exceed capacity.
     */
    void theory_jobscheduler::validate_assignment() {
        vector<vector<job_time>> start_times, end_times;
        start_times.reserve(m_resources.size());
        end_times.reserve(m_resources.size());
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            unsigned r = resource(j);
            start_times[r].push_back(job_time(j, start(j))); 
            end_times[r].push_back(job_time(j, end(j))); 
            time_t cap = capacity_used(j, r, start(j), end(j));
            job_resource const& jr = get_job_resource(j, r);
            if (jr.m_capacity > cap) {
                throw default_exception("job not assigned full capacity");
            }
        }
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            unsigned load_pct = 0;
            unsigned idx;
            time_t next = 0, start = 0;

            // order jobs running on r by start, end-time intervals
            // then consume ordered list to find jobs in scope.
            vector<job_time>& starts = start_times[r];
            vector<job_time>& ends = end_times[r];
            job_time::compare cmp;
            std::sort(starts.begin(), starts.end(), cmp);
            std::sort(ends.begin(),   ends.end(),   cmp);
            unsigned s_idx = 0, e_idx = 0;

            uint_set jobs; // set of jobs currently in scope.
            while (resource_available(r, start, load_pct, next, idx)) {
                if (load_pct == 0) {
                    start = next + 1;
                    continue;
                }
                // add jobs that begin at or before start.
                while (s_idx < starts.size() && starts[s_idx].m_time <= start) {
                    jobs.insert(starts[s_idx].m_job);
                    ++s_idx;
                }
                // remove jobs that end before start.
                while (e_idx < ends.size() && ends[s_idx].m_time < start) {
                    jobs.remove(ends[e_idx].m_job);
                    ++e_idx;
                }

                // check that sum of job loads does not exceed 100%
                unsigned cap = 0;
                for (auto j : jobs) {
                    cap += get_job_resource(j, r).m_loadpct;
                }
                if (cap > 100) {
                    throw default_exception("capacity on resource exceeded");
                }
                if (s_idx < starts.size()) {
                    // start time of the next unprocessed job.
                    start = starts[s_idx].m_time;
                }
                else {
                    // done checking.
                    break;
                }
            }
        }
    }

    theory_jobscheduler::job_resource const& theory_jobscheduler::get_job_resource(unsigned j, unsigned r) const {
        job_info const& ji = m_jobs[j];
        return ji.m_resources[ji.m_resource2index[r]];
    }

    bool theory_jobscheduler::resource_available(unsigned r, time_t t, unsigned& load_pct, time_t& end, unsigned& idx) {
        vector<res_available>& available = m_resources[r].m_available;
        unsigned lo = 0, hi = available.size(), mid = hi / 2;
        while (lo < hi) {
            res_available const& ra = available[mid];
            if (ra.m_start <= t && t <= ra.m_end) {
                end = ra.m_end;
                load_pct = ra.m_loadpct;
                idx = mid;
                return true;
            }
            else if (ra.m_start > t && mid > 0) {
                hi = mid - 1;
                mid = lo + (mid - lo) / 2;
            }
            else if (ra.m_end < t) {
                lo = mid + 1;
                mid += (hi - mid) / 2;
            }
            else {
                break;
            }
        }
        return false;
    }

    /**
     * compute the capacity used by job j on resource r between start and end.
     * The resource r partitions time intervals into segments where a fraction of
     * the full capacity of the resource is available. The resource can use up to the
     * available fraction.
     */
    time_t theory_jobscheduler::capacity_used(unsigned j, unsigned r, time_t start, time_t end) {
        time_t cap = 0;
        unsigned j_load_pct = get_job_resource(j, r).m_loadpct;
        vector<res_available>& available = m_resources[r].m_available;
        unsigned load_pct = 0;
        time_t next = 0;
        unsigned idx = 0;
        if (!resource_available(r, start, load_pct, next, idx)) {
            return cap;
        }
        while (start < end) {
            next = std::min(end, next);
            SASSERT(start < next);
            cap += (std::min(j_load_pct, load_pct) / j_load_pct) * (next - start - 1);
            ++idx;
            if (idx == available.size()) {
                break;
            }
            start = available[idx].m_start;
            next  = available[idx].m_end;
            load_pct = available[idx].m_loadpct;
        }        
        return cap;
    }
    
};

