/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_jobscheduler.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2018-09-08.

Revision History:

TODO:

- arithmetic interface

- propagation queue:
  - register theory variables for catching when jobs are bound to resources
  - register bounds on start times to propagate energy constraints
  - more general registration mechanism for arithmetic theory.
- csp_cmds
  - use predicates for add_ feature set? Closed world.
    set up environment in one swoop.
  - interact with opt
- jobs without resources
  - complain or add dummy resource? At which level.

Features:
- properties
- priority
  - try mss based from outside
- job-goal
   - try optimization based on arithmetic solver.
   - earliest start, latest start
- constraint level
- resource groups
  - resource groups like a resource
  - resources bound to resource groups within time intervals
  - job can require to use K resources from a resource group simultaneously.

--*/

#include "smt/theory_jobscheduler.h"
#include "smt/smt_context.h"
#include "smt/smt_arith_value.h"

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
            app_ref res(u.mk_job2resource(j), m);
            if (!ctx.e_internalized(start)) ctx.internalize(start, false);
            if (!ctx.e_internalized(end))   ctx.internalize(end, false);
            if (!ctx.e_internalized(res))   ctx.internalize(res, false);
            theory_var v = mk_var(e);
            SASSERT(m_var2index.size() == v);
            m_var2index.push_back(j);
            m_jobs.reserve(j + 1);
            m_jobs[j].m_start    = ctx.get_enode(start);
            m_jobs[j].m_end      = ctx.get_enode(end);
            m_jobs[j].m_job2resource = ctx.get_enode(res);
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

    bool theory_jobscheduler::internalize_atom(app * atom, bool gate_ctx) {
        SASSERT(u.is_model(atom));
        for (expr* arg : *atom) {
            internalize_cmd(arg);
        }
        add_done();
        return true;
    }

    // TBD: stronger parameter validation
    void theory_jobscheduler::internalize_cmd(expr* cmd) {
        symbol key, val;
        rational r;
        if (u.is_kv(cmd, key, r)) {
            if (key == ":set-preemptable" && r.is_unsigned()) {
                set_preemptable(r.get_unsigned(), true);
                return;
            }
            warning_msg("command not recognized");
        }
        else if (u.is_alist(cmd, key) && key == ":add-job-resource") {
            properties ps;
            unsigned j = 0, res = 0, cap = 0, loadpct = 100;
            time_t end = std::numeric_limits<time_t>::max();
            for (expr* arg : *to_app(cmd)) {
                if (u.is_kv(arg, key, r)) {
                    if (key == ":job") {
                        j = r.get_unsigned();
                    }
                    else if (key == ":resource") {
                        res = r.get_unsigned();
                    }
                    else if (key == ":capacity") {
                        cap = r.get_unsigned();
                    }
                    else if (key == ":loadpct") {
                        loadpct = r.get_unsigned();
                    }
                    else if (key == ":end") {
                        end = r.get_uint64();
                    }
                }
                else if (u.is_alist(arg, key) && key == ":properties") {
                    // TBD
                }
            }
            if (cap > 0) {
                add_job_resource(j, res, cap, loadpct, end, ps);
            }
            else {
                warning_msg("no job capacity provided");
            }
        }
        else if (u.is_alist(cmd, key) && key == ":add-resource-available") {
            properties ps;
            unsigned res = 0, loadpct = 100;
            time_t start = 0, end = 0;
            for (expr* arg : *to_app(cmd)) {
                if (u.is_kv(arg, key, r)) {
                    if (key == ":resource") {
                        res = r.get_unsigned();
                    }
                    else if (key == ":start") {
                        start = r.get_unsigned();
                    }
                    else if (key == ":end") {
                        end = r.get_unsigned();
                    }
                    else if (key == ":loadpct") {
                        loadpct = r.get_unsigned();
                    }
                }
                else if (u.is_alist(arg, key) && key == ":properties") {
                    // TBD
                }
                add_resource_available(res, loadpct, start, end, ps);
            }
            
        }
        else {
            warning_msg("command not recognized");
        }
    }

    void theory_jobscheduler::push_scope_eh() {
    }

    void theory_jobscheduler::pop_scope_eh(unsigned num_scopes) {
    }

    final_check_status theory_jobscheduler::final_check_eh() {

        bool blocked = false;
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            if (constrain_resource_energy(r)) {
                blocked = true;
            }
        }
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            if (constrain_end_time_interval(j, resource(j))) {
                blocked = true;
            }
        }
        
        if (blocked) return FC_CONTINUE;
        return FC_DONE;
    }

    bool theory_jobscheduler::can_propagate() {
        return false;
    }

    literal theory_jobscheduler::mk_literal(expr * e) {
        expr_ref _e(e, m);
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        ctx.mark_as_relevant(ctx.get_enode(e));
        return ctx.get_literal(e);
    }

    literal theory_jobscheduler::mk_ge_lit(expr* e, time_t t) {
        return mk_literal(mk_ge(e, t));
    }

    expr* theory_jobscheduler::mk_ge(expr* e, time_t t) {
        return a.mk_ge(e, a.mk_int(rational(t, rational::ui64())));
    }

    expr* theory_jobscheduler::mk_ge(enode* e, time_t t) {
        return mk_ge(e->get_owner(), t);
    }

    literal theory_jobscheduler::mk_le_lit(expr* e, time_t t) {
        return mk_literal(mk_le(e, t));
    }

    expr* theory_jobscheduler::mk_le(expr* e, time_t t) {
        return a.mk_le(e, a.mk_int(rational(t, rational::ui64())));
    }

    literal theory_jobscheduler::mk_le(enode* l, enode* r) {
        context& ctx = get_context();
        expr_ref le(a.mk_le(l->get_owner(), r->get_owner()), m);
        ctx.get_rewriter()(le);
        return mk_literal(le);
    }

    expr* theory_jobscheduler::mk_le(enode* e, time_t t) {
        return mk_le(e->get_owner(), t);
    }

    /**
     * iterator of job overlaps.
     */
    theory_jobscheduler::job_overlap::job_overlap(vector<job_time>& starts, vector<job_time>& ends):
        m_starts(starts), m_ends(ends), s_idx(0), e_idx(0) {
        job_time::compare cmp;
        std::sort(starts.begin(), starts.end(), cmp);
        std::sort(ends.begin(),   ends.end(),   cmp);        
    }

    bool theory_jobscheduler::job_overlap::next(time_t& start) {
        if (s_idx == m_starts.size()) {
            return false;
        }
        while (s_idx < m_starts.size() && m_starts[s_idx].m_time <= start) {
            m_jobs.insert(m_starts[s_idx].m_job);
            ++s_idx;
        }
        // remove jobs that end before start.
        while (e_idx < m_ends.size() && m_ends[s_idx].m_time < start) {
            m_jobs.remove(m_ends[e_idx].m_job);
            ++e_idx;
        }        
        // TBD: check logic
        if (s_idx < m_starts.size()) {
            start = m_starts[s_idx].m_time;
        }
        return true;
    }


    /**
     *  r = resource(j) & start(j) >= slb => end(j) >= ect(j, r, slb)
     */
    void theory_jobscheduler::propagate_end_time(unsigned j, unsigned r) {
        time_t slb = est(j);
        time_t clb = ect(j, r, slb);
        context& ctx = get_context();

        if (clb > end(j)) {
            job_info const& ji = m_jobs[j];
            literal start_ge_lo = mk_literal(mk_ge(ji.m_start, slb));
            if (ctx.get_assignment(start_ge_lo) != l_true) {
                return;
            }
            enode_pair eq(ji.m_job2resource, resource2enode(r));
            if (eq.first->get_root() != eq.second->get_root()) {
                return;
            }

            literal end_ge_lo = mk_literal(mk_ge(ji.m_end, clb));
            // Initialization ensures that satisfiable states have completion time below end.
            VERIFY(clb <= get_job_resource(j, r).m_end);
            region& r = ctx.get_region();
            ctx.assign(end_ge_lo, 
                       ctx.mk_justification(
                           ext_theory_propagation_justification(get_id(), r, 1, &start_ge_lo, 1, &eq, end_ge_lo, 0, nullptr)));
        }
    }

    /**
     *  For time interval [t0, t1] the end-time can be computed as a function 
     *  of start time based on reource load availability.
     * 
     *  r = resource(j) & t1 >= start(j) >= t0 => end(j) = start(j) + ect(j, r, t0) - t0
     */
    bool theory_jobscheduler::constrain_end_time_interval(unsigned j, unsigned r) {
        unsigned idx1 = 0, idx2 = 0;
        time_t s = start(j);
        if (!resource_available(r, s, idx1)) return false;
        vector<res_available>& available = m_resources[r].m_available;
        time_t e = ect(j, r, s);
        if (!resource_available(r, e, idx2)) return false;
        time_t start1 = available[idx1].m_start;
        time_t end1   = available[idx1].m_end;
        unsigned cap1 = available[idx1].m_loadpct;
        time_t start2 = available[idx2].m_start;
        time_t end2   = available[idx2].m_end;
        unsigned cap2 = available[idx2].m_loadpct;
        // calculate minimal start1 <= t0 <= s,    such that ect(j, r, t0) >= start2 
        // calculate maximal s      <= t1 <= end1, such that ect(j, r, t1) <= end2
        time_t delta1 = (s - start1)*cap1;
        time_t delta2 = (e - start2)*cap2;
        time_t t0, t1;
        if (delta1 <= delta2) {
            t0 = start1;
        }
        else {
            // solve for t0:
            // (s - t0)*cap1 = (e - start2)*cap2;
            t0 = s - (delta2 / cap1); 
        }
        delta1 = (end1 - s)*cap1;
        delta2 = (end2 - e)*cap2;
        if (delta1 <= delta2) {
            t1 = end1;
        }
        else {
            // solve for t1:
            // (t1 - s)*cap1 = (end2 - e)*cap2
            t1 = s + (delta2 / cap1);
        }

        time_t delta = ect(j, r, t0) - t0;
        if (end(j) == start(j) + delta) {
            return false;
        }
        literal_vector lits;
        lits.push_back(~mk_eq(u.mk_job2resource(j), u.mk_resource(r), false));
        lits.push_back(~mk_ge_lit(u.mk_start(j), t0));
        lits.push_back(~mk_le_lit(u.mk_start(j), t1));        
        expr_ref rhs(a.mk_add(u.mk_start(j), a.mk_int(rational(delta, rational::ui64()))), m);
        lits.push_back(mk_eq(u.mk_end(j), rhs, false));
        context& ctx = get_context();
        ctx.mk_clause(lits.size(), lits.c_ptr(), nullptr, CLS_AUX_LEMMA, nullptr);
        return true;
    }

    void theory_jobscheduler::propagate_resource_energy(unsigned r) {
        
    }

    /**
     *  Ensure that job overlaps don't exceed available energy
     */ 
    bool theory_jobscheduler::constrain_resource_energy(unsigned r) {
        bool blocked = false;
        vector<job_time> starts, ends;
        res_info const& ri = m_resources[r];
        for (unsigned j : ri.m_jobs) {
            if (resource(j) == r) {
                starts.push_back(job_time(j, start(j)));
                ends.push_back(job_time(j, end(j)));
            }
        }
        job_overlap overlap(starts, ends);
        time_t start = 0;
        while (overlap.next(start)) {
            unsigned cap = 0;
            auto const& jobs = overlap.jobs();
            for (auto j : jobs) {
                cap += get_job_resource(j, r).m_loadpct;
                if (cap > 100) {
                    block_job_overlap(r, jobs, j);
                    blocked = true;
                    goto try_next_overlap;
                }
            }    
        try_next_overlap:
            ;
        }
        return blocked;
    }

    void theory_jobscheduler::block_job_overlap(unsigned r, uint_set const& jobs, unsigned last_job) {
        //
        // block the following case:
        // each job is assigned to r.
        // max { start(j) | j0..last_job } <= min { end(j) | j0..last_job }
        // joint capacity of jobs exceeds availability of resource.
        // 
        time_t max_start = 0;
        unsigned max_j = last_job;
        for (auto j : jobs) {
            if (max_start < start(j)) {
                max_start = start(j);
                max_j = j;
            }
            if (j == last_job) break;
        }
        literal_vector lits;
        for (auto j : jobs) {
            // create literals for:  
            // resource(j) == r
            // m_jobs[j].m_start <= m_jobs[max_j].m_start;
            // m_jobs[max_j].m_start <= m_jobs[j].m_end;
            lits.push_back(~mk_eq(u.mk_job2resource(j), u.mk_resource(r), false));
            if (j != max_j) {
                lits.push_back(~mk_le(m_jobs[j].m_start, m_jobs[max_j].m_start));
                lits.push_back(~mk_le(m_jobs[max_j].m_start, m_jobs[j].m_end));
            }
            if (j == last_job) break;
        }
        context& ctx = get_context();
        ctx.mk_clause(lits.size(), lits.c_ptr(), nullptr, CLS_AUX_LEMMA, nullptr);
    }

    void theory_jobscheduler::propagate() {
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            job_info const& ji = m_jobs[j];
            unsigned r = resource(j);
            propagate_end_time(j, r);
        }
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            // TBD: check energy constraints on resources.
        }
    }
        
    theory_jobscheduler::theory_jobscheduler(ast_manager& m): 
        theory(m.get_family_id("csp")), m(m), u(m), a(m) {
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

    time_t theory_jobscheduler::get_lo(expr* e) {
        arith_value av(get_context());
        rational val;
        bool is_strict;
        if (av.get_lo(e, val, is_strict) && !is_strict && val.is_uint64()) {
            return val.get_uint64();
        }
        return 0;
    }

    time_t theory_jobscheduler::get_up(expr* e) {
        arith_value av(get_context());
        rational val;
        bool is_strict;
        if (av.get_up(e, val, is_strict) && !is_strict && val.is_uint64()) {
            return val.get_uint64();
        }
        return std::numeric_limits<time_t>::max();
    }

    time_t theory_jobscheduler::get_value(expr* e) {
        arith_value av(get_context());
        rational val;
        if (av.get_value(e, val) && val.is_uint64()) {
            return val.get_uint64();
        }
        return 0;
    }    

    time_t theory_jobscheduler::est(unsigned j) {
        return get_lo(m_jobs[j].m_start->get_owner());
    }

    time_t theory_jobscheduler::lst(unsigned j) {
        return get_up(m_jobs[j].m_start->get_owner());
    }

    time_t theory_jobscheduler::ect(unsigned j) {
        return get_lo(m_jobs[j].m_end->get_owner());
    }

    time_t theory_jobscheduler::lct(unsigned j) {
        return get_up(m_jobs[j].m_end->get_owner());
    }

    time_t theory_jobscheduler::start(unsigned j) {
        return get_value(m_jobs[j].m_start->get_owner());
    }

    time_t theory_jobscheduler::end(unsigned j) {
        return get_value(m_jobs[j].m_end->get_owner());
    }

    unsigned theory_jobscheduler::resource(unsigned j) {
        unsigned r;
        enode* next = m_jobs[j].m_job2resource, *n = next;
        do {
            if (u.is_resource(next->get_owner(), r)) {
                return r;
            }
            next = next->get_next();
        }
        while (next != n);
        return 0;
    }

    enode* theory_jobscheduler::resource2enode(unsigned r) {
        return get_context().get_enode(u.mk_resource(r));
    }

    void theory_jobscheduler::set_preemptable(unsigned j, bool is_preemptable) {
        m_jobs.reserve(j + 1);
        m_jobs[j].m_is_preemptable = is_preemptable;        
    }

    void theory_jobscheduler::add_job_resource(unsigned j, unsigned r, unsigned cap, unsigned loadpct, time_t end, properties const& ps) {
        SASSERT(get_context().at_base_level());
        SASSERT(1 <= loadpct && loadpct <= 100);
        SASSERT(0 < cap);
        m_jobs.reserve(j + 1);
        m_resources.reserve(r + 1);
        job_info& ji = m_jobs[j];
        if (ji.m_resource2index.contains(r)) {
            throw default_exception("resource already bound to job");
        }
        ji.m_resource2index.insert(r, ji.m_resources.size());
        ji.m_resources.push_back(job_resource(r, cap, loadpct, end, ps));
        SASSERT(!m_resources[r].m_jobs.contains(j));
        m_resources[r].m_jobs.push_back(j);
    }

    void theory_jobscheduler::add_resource_available(unsigned r, unsigned max_loadpct, time_t start, time_t end, properties const& ps) {
        SASSERT(get_context().at_base_level());
        SASSERT(1 <= max_loadpct && max_loadpct <= 100);
        SASSERT(start <= end);
        m_resources.reserve(r + 1);
        res_info& ri = m_resources[r];
        ri.m_available.push_back(res_available(max_loadpct, start, end, ps));
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
        
        // sort availability intervals
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            res_info& ri = m_resources[r];
            vector<res_available>& available = ri.m_available;
            res_available::compare cmp;
            std::sort(available.begin(), available.end(), cmp);
        }

        expr_ref fml(m);

        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            job_info const& ji = m_jobs[j];
            expr_ref_vector disj(m);
            app_ref job(u.mk_job(j), m);
            if (ji.m_resources.empty()) {
                throw default_exception("every job should be associated with at least one resource");
            }

            // start(j) <= end(j)
            fml = a.mk_le(ji.m_start->get_owner(), ji.m_end->get_owner());
            ctx.assert_expr(fml);

            time_t start_lb = std::numeric_limits<time_t>::max();
            time_t end_ub = 0;
            for (job_resource const& jr : ji.m_resources) {
                // resource(j) = r => end(j) <= end(j, r)
                // resource(j) = r => start(j) <= lst(j, r, end(j, r))
                unsigned r = jr.m_resource_id;
                app_ref res(u.mk_resource(r), m);
                expr_ref eq(m.mk_eq(job, res), m);
                expr_ref imp(m.mk_implies(eq, mk_le(ji.m_end, jr.m_end)), m);
                ctx.assert_expr(imp);
                time_t t;
                if (!lst(j, r, t)) {
                    imp = m.mk_implies(eq, mk_le(ji.m_start, t));
                }
                else {
                    imp = m.mk_not(eq);
                }
                ctx.assert_expr(imp);
                disj.push_back(eq);
                res_info const& ri = m_resources[r];
                start_lb = std::min(start_lb, ri.m_available[0].m_start);
                end_ub = std::max(end_ub, ri.m_available.back().m_end);

            }
            // resource(j) = r1 || ... || resource(j) = r_n
            expr_ref fml = mk_or(disj);
            ctx.assert_expr(fml);

            // start(j) >= start_lb
            fml = mk_ge(ji.m_start, start_lb);
            ctx.assert_expr(fml);

            // end(j) <= end_ub
            fml = mk_le(ji.m_end, end_ub);
            ctx.assert_expr(fml);
        }        
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            res_info& ri = m_resources[r];
            vector<res_available>& available = ri.m_available;
            if (available.empty()) continue;
            app_ref res(u.mk_resource(r), m);
            for (unsigned j : ri.m_jobs) {
                // resource(j) == r => start(j) >= available[0].m_start;
                app_ref job(u.mk_job(j), m);
                expr_ref eq(m.mk_eq(job, res), m);
                expr_ref ge(mk_ge(u.mk_start(j), available[0].m_start), m);
                expr_ref fml(m.mk_implies(eq, ge), m);
                ctx.assert_expr(fml);                
            }
            for (unsigned i = 0; i + 1 < available.size(); ++i) {
                if (available[i].m_end > available[i + 1].m_start) {
                    throw default_exception("availability intervals should be disjoint");
                }
                for (unsigned j : ri.m_jobs) {
                    // jobs start within an interval.
                    // resource(j) == r => start(j) <= available[i].m_end || start(j) >= available[i + 1].m_start;
                    app_ref job(u.mk_job(j), m);
                    expr_ref eq(m.mk_eq(job, res), m);
                    expr_ref ge(mk_ge(u.mk_start(j), available[i + 1].m_start), m);
                    expr_ref le(mk_le(u.mk_start(j), available[i].m_end), m);
                    fml = m.mk_implies(eq, m.mk_or(le, ge));
                    ctx.assert_expr(fml);                

                    // if job is not pre-emptable, start and end have to align within contiguous interval.
                    // resource(j) == r => end(j) <= available[i].m_end || start(j) >= available[i + 1].m_start
                    if (!m_jobs[j].m_is_preemptable && available[i].m_end + 1 < available[i+1].m_start) {
                        le = mk_le(u.mk_end(j), available[i].m_end);
                        ge = mk_ge(u.mk_start(j), available[i+1].m_start);
                        fml = m.mk_implies(eq, m.mk_or(le, ge));
                        ctx.assert_expr(fml);
                    }
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
            if (ect(j, r, start(j)) > end(j)) {
                throw default_exception("job not assigned full capacity");
            }
            unsigned idx;
            if (!resource_available(r, start(j), idx)) {
                throw default_exception("resource is not available at job start time");
            }
        }
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            // order jobs running on r by start, end-time intervals
            // then consume ordered list to find jobs in scope.
            time_t start = 0;
            job_overlap overlap(start_times[r], end_times[r]);
            while (overlap.next(start)) {
                // check that sum of job loads does not exceed 100%
                unsigned cap = 0;
                for (auto j : overlap.jobs()) {
                    cap += get_job_resource(j, r).m_loadpct;
                }
                if (cap > 100) {
                    throw default_exception("capacity on resource exceeded");
                }
            }
        }
    }

    theory_jobscheduler::job_resource const& theory_jobscheduler::get_job_resource(unsigned j, unsigned r) const {
        job_info const& ji = m_jobs[j];
        return ji.m_resources[ji.m_resource2index[r]];
    }

    bool theory_jobscheduler::resource_available(unsigned r, time_t t, unsigned& idx) {
        vector<res_available>& available = m_resources[r].m_available;
        unsigned lo = 0, hi = available.size(), mid = hi / 2;
        while (lo < hi) {
            res_available const& ra = available[mid];
            if (ra.m_start <= t && t <= ra.m_end) {
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
     * compute earliest completion time for job j on resource r starting at time start.
     */    
    time_t theory_jobscheduler::ect(unsigned j, unsigned r, time_t start) {
        job_resource const& jr = get_job_resource(j, r);
        vector<res_available>& available = m_resources[r].m_available;

        unsigned j_load_pct = jr.m_loadpct;
        time_t cap = jr.m_capacity;
        unsigned idx = 0;
        if (!resource_available(r, start, idx)) {
            return std::numeric_limits<time_t>::max();
        }
        SASSERT(cap > 0);
        
        for (; idx < available.size(); ++idx) {
            start             = std::max(start, available[idx].m_start);
            time_t end        = available[idx].m_end;
            unsigned load_pct = available[idx].m_loadpct;
            time_t delta = solve_for_capacity(load_pct, j_load_pct, start, end);
            if (delta > cap) {
                //
                // solve for end: 
                //     cap = load * (end - start + 1)
                // <=>
                //     cap / load = (end - start + 1)
                // <=>
                //     end = cap / load + start - 1
                //
                end = solve_for_end(load_pct, j_load_pct, start, cap);
                cap = 0;
            }
            else {
                cap -= delta;
            }
            if (cap == 0) {
                return end;
            }
        }        
        return std::numeric_limits<time_t>::max();        
    }

    time_t theory_jobscheduler::solve_for_end(unsigned load_pct, unsigned job_load_pct, time_t start, time_t cap) {
        SASSERT(load_pct > 0);
        SASSERT(job_load_pct > 0);
        //      cap = (load / job_load_pct) * (start - end + 1)
        // <=> 
        //      start - end + 1 = (cap * job_load_pct) / load 
        // <=>
        //      end = start + 1 - (cap * job_load_pct) / load
        // <=>
        //      end = (load * (start + 1) - cap * job_load_pct) / load
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (start + 1) - cap * job_load_pct) / load;
    }

    time_t theory_jobscheduler::solve_for_start(unsigned load_pct, unsigned job_load_pct, time_t end, time_t cap) {
        SASSERT(load_pct > 0);
        SASSERT(job_load_pct > 0);
        //      cap = (load / job_load_pct) * (start - end + 1)
        // <=> 
        //      start - end + 1 = (cap * job_load_pct) / load 
        // <=>
        //      start = (cap * job_load_pct) / load + end - 1
        // <=>
        //      start = (load * (end - 1) + cap * job_load_pct) / load
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (end - 1) + cap * job_load_pct) / load;
    }

    time_t theory_jobscheduler::solve_for_capacity(unsigned load_pct, unsigned job_load_pct, time_t start, time_t end) {
        SASSERT(job_load_pct > 0);
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (end - start + 1)) / job_load_pct;
    }

    /**
     * Compute last start time for job on resource r.
     */
    bool theory_jobscheduler::lst(unsigned j, unsigned r, time_t& start) {
        job_resource const& jr = get_job_resource(j, r);
        vector<res_available>& available = m_resources[r].m_available;
        unsigned j_load_pct = jr.m_loadpct;
        time_t cap = jr.m_capacity;
        for (unsigned idx = available.size(); idx-- > 0; ) {
            time_t start    = available[idx].m_start;
            time_t end      = available[idx].m_end;
            unsigned load_pct = available[idx].m_loadpct;
            time_t delta = solve_for_capacity(load_pct, j_load_pct, start, end);
            if (delta > cap) {
                start = solve_for_start(load_pct, j_load_pct, start, cap);
                cap = 0;
            }
            else {
                cap -= delta;
            }
            if (cap == 0) {
                return true;
            }
        }
        return false;
    }
    
};

