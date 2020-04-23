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
  - register bounds on start times to propagate energy constraints
  - more general registration mechanism for arithmetic theory.
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
   - add constraints gradually
- resource groups
  - resource groups like a resource
  - resources bound to resource groups within time intervals
  - job can require to use K resources from a resource group simultaneously.

--*/

#include "ast/ast_pp.h"
#include "smt/theory_jobscheduler.h"
#include "smt/smt_context.h"
#include "smt/smt_arith_value.h"
#include "smt/smt_model_generator.h"

namespace smt {

    theory_var theory_jobscheduler::mk_var(enode * n) {
        theory_var v = theory::mk_var(n);
        return v;
    }

    bool theory_jobscheduler::internalize_term(app * term) {
        context & ctx = get_context();        
        if (ctx.e_internalized(term))
            return true;
        for (expr* arg : *term) {
            if (!ctx.e_internalized(arg)) 
                ctx.internalize(arg, false);
        }        
        enode* e = ctx.mk_enode(term, false, false, true);
        theory_var v = mk_var(e);
        ctx.attach_th_var(e, this, v);
        ctx.mark_as_relevant(e);
        return true;
    }

    bool theory_jobscheduler::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("csp", tout << mk_pp(atom, m) << "\n";);
        context & ctx = get_context();        
        SASSERT(u.is_model(atom));
        for (expr* arg : *atom) {
            if (!ctx.e_internalized(arg)) ctx.internalize(arg, false);
            internalize_cmd(arg);
        }
        add_done();
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        return true;
    }

    struct symbol_cmp {
        bool operator()(symbol const& s1, symbol const& s2) const {
            return lt(s1, s2);
        }
    };

    // TBD: stronger parameter validation
    void theory_jobscheduler::internalize_cmd(expr* cmd) {
        symbol key, val;
        rational r;
        expr* job, *resource;
        unsigned j = 0, res = 0, cap = 0, loadpct = 100, level = 0;
        time_t start = 0, end = std::numeric_limits<time_t>::max(), capacity = 0;
        js_job_goal goal;
        js_optimization_objective obj;
        properties ps;
        if (u.is_set_preemptable(cmd, job) && u.is_job(job, j)) {
            set_preemptable(j, true);            
        }
        else if (u.is_add_resource_available(cmd, resource, loadpct, cap, start, end, ps) && u.is_resource(resource, res)) {
            std::sort(ps.begin(), ps.end(), symbol_cmp());
            (void) cap; // TBD
            add_resource_available(res, loadpct, start, end, ps);
        }
        else if (u.is_add_job_resource(cmd, job, resource, loadpct, capacity, end, ps) && u.is_job(job, j) && u.is_resource(resource, res)) {
            std::sort(ps.begin(), ps.end(), symbol_cmp());
            add_job_resource(j, res, loadpct, capacity, end, ps);
        }
        else if (u.is_job_goal(cmd, goal, level, job) && u.is_job(job, j)) {
            // skip
        }
        else if (u.is_objective(cmd, obj)) {
            // skip
        }
        else {
            invalid_argument("command not recognized ", cmd);
        }
    }

    void theory_jobscheduler::invalid_argument(char const* msg, expr* arg) {
        std::ostringstream strm;
        strm << msg << mk_pp(arg, m);
        throw default_exception(strm.str());
    }

    void theory_jobscheduler::new_eq_eh(theory_var v1, theory_var v2) {
        enode* e1 = get_enode(v1);
        enode* root = e1->get_root();
        unsigned r;
        if (u.is_resource(root->get_owner(), r)) {
            enode* next = e1;
            do {
                unsigned j;
                if (u.is_job2resource(next->get_owner(), j) && !m_jobs[j].m_is_bound) {
                    m_bound_jobs.push_back(j);
                    m_jobs[j].m_is_bound = true;
                }
                next = next->get_next();
            }
            while (e1 != next);
        }
    }


    void theory_jobscheduler::new_diseq_eh(theory_var v1, theory_var v2) {

    }

    void theory_jobscheduler::push_scope_eh() {
        scope s;
        s.m_bound_jobs_lim = m_bound_jobs.size();
        s.m_bound_qhead = m_bound_qhead;
        m_scopes.push_back(s);
    }

    void theory_jobscheduler::pop_scope_eh(unsigned num_scopes) {
        unsigned new_lvl = m_scopes.size() - num_scopes;
        scope const& s = m_scopes[new_lvl];
        for (unsigned i = s.m_bound_jobs_lim; i < m_bound_jobs.size(); ++i) {
            unsigned j = m_bound_jobs[i];
            m_jobs[j].m_is_bound = false;
        }
        m_bound_jobs.shrink(s.m_bound_jobs_lim);
        m_bound_qhead = s.m_bound_qhead;
        m_scopes.shrink(new_lvl);
    }

    final_check_status theory_jobscheduler::final_check_eh() {
        TRACE("csp", tout << "\n";);
        bool blocked = false;
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            if (split_job2resource(j)) {
                return FC_CONTINUE;
            }
        }
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
        return m_bound_qhead < m_bound_jobs.size();
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

    literal theory_jobscheduler::mk_ge(expr* e, time_t t) {
        return mk_literal(mk_ge_expr(e, t));
    }

    expr* theory_jobscheduler::mk_ge_expr(expr* e, time_t t) {
        return a.mk_ge(e, a.mk_int(rational(t, rational::ui64())));
    }

    literal theory_jobscheduler::mk_ge(enode* e, time_t t) {
        return mk_ge(e->get_owner(), t);
    }

    literal theory_jobscheduler::mk_le(expr* e, time_t t) {
        return mk_literal(mk_le_expr(e, t));
    }

    expr* theory_jobscheduler::mk_le_expr(expr* e, time_t t) {
        return a.mk_le(e, a.mk_int(rational(t, rational::ui64())));
    }

    literal theory_jobscheduler::mk_le(enode* l, enode* r) {
        context& ctx = get_context();
        expr_ref le(a.mk_le(l->get_owner(), r->get_owner()), m);
        ctx.get_rewriter()(le);
        return mk_literal(le);
    }

    literal theory_jobscheduler::mk_le(enode* e, time_t t) {
        return mk_le(e->get_owner(), t);
    }

    literal theory_jobscheduler::mk_eq_lit(expr * l, expr * r) {
        literal lit = mk_eq(l, r, false);
        get_context().mark_as_relevant(lit);
        return lit;
    }


    /**
     * iterator of job overlaps.
     */
    theory_jobscheduler::job_overlap::job_overlap(vector<job_time>& starts, vector<job_time>& ends):
        m_start(0), m_starts(starts), m_ends(ends), s_idx(0), e_idx(0) {
        job_time::compare cmp;
        std::sort(starts.begin(), starts.end(), cmp);
        std::sort(ends.begin(),   ends.end(),   cmp);        
    }

    bool theory_jobscheduler::job_overlap::next() {
        if (s_idx == m_starts.size()) {
            return false;
        }
        do {
            m_start = std::max(m_start, m_starts[s_idx].m_time);
                
            // add jobs that start before or at m_start
            while (s_idx < m_starts.size() && m_starts[s_idx].m_time <= m_start) {
                m_jobs.insert(m_starts[s_idx].m_job);
                ++s_idx;
            }
            // remove jobs that end before m_start.
            while (e_idx < m_ends.size() && m_ends[e_idx].m_time < m_start) {
                m_jobs.remove(m_ends[e_idx].m_job);
                ++e_idx;
            }   
        }
        // as long as set of jobs increments, add to m_start
        while (s_idx < m_starts.size() && e_idx < m_ends.size() && 
               m_starts[s_idx].m_time <= m_ends[e_idx].m_time);
            
        return true;
    }


    /**
     *  r = resource(j) & start(j) >= slb => end(j) >= ect(j, r, slb)
     *
     * note: not used so far
     * note: subsumed by constrain_end_time_interval used in final-check
     */
    void theory_jobscheduler::propagate_end_time(unsigned j, unsigned r) {
        time_t slb = est(j);
        time_t clb = ect(j, r, slb);
        context& ctx = get_context();

        if (clb > end(j)) {
            job_info const& ji = m_jobs[j];
            literal start_ge_lo = mk_ge(ji.m_start, slb);
            if (ctx.get_assignment(start_ge_lo) != l_true) {
                return;
            }
            enode_pair eq(ji.m_job2resource, m_resources[r].m_resource);
            if (eq.first->get_root() != eq.second->get_root()) {
                return;
            }

            literal end_ge_lo = mk_ge(ji.m_end, clb);
            // Initialization ensures that satisfiable states have completion time below end.
            ast_manager& m = get_manager();
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_and(m.mk_eq(eq.first->get_owner(), eq.second->get_owner()), ctx.bool_var2expr(start_ge_lo.var())), ctx.bool_var2expr(end_ge_lo.var()));
                log_axiom_instantiation(body);
                m.trace_stream() << "[end-of-instance]\n";
            }
            region& r = ctx.get_region();
            ctx.assign(end_ge_lo, 
                       ctx.mk_justification(
                           ext_theory_propagation_justification(get_id(), r, 1, &start_ge_lo, 1, &eq, end_ge_lo, 0, nullptr)));
        }
    }

    /**
     *  For time interval [t0, t1] the end-time can be computed as a function 
     *  of start time based on resource load availability.
     * 
     *  r = resource(j) & t1 >= start(j) >= t0 => end(j) = start(j) + ect(j, r, t0) - t0
     */
    bool theory_jobscheduler::constrain_end_time_interval(unsigned j, unsigned r) {
        unsigned idx1 = 0, idx2 = 0;
        if (!job_has_resource(j, r)) {
            IF_VERBOSE(0, verbose_stream() << "job " << j << " assigned non-registered resource " << r << "\n");
            return false;
        }
        time_t s = start(j);
        job_resource const& jr = get_job_resource(j, r);
        TRACE("csp", tout << "job: " << j << " resource: " << r << " start: " << s <<  "\n";);
        vector<res_available>& available = m_resources[r].m_available;
        if (!resource_available(r, s, idx1)) return false;
        if (!resource_available(jr, available[idx1])) return false;
        time_t e = ect(j, r, s);
        TRACE("csp", tout << "job: " << j << " resource: " << r << " ect: " << e <<  "\n";);
        if (!resource_available(r, e, idx2)) return false; // infeasible..
        if (!resource_available(jr, available[idx2])) return false;
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
        TRACE("csp", tout << "job: " << j << " resource " << r << " t0: " << t0 << " t1: " << t1 << " delta: " << delta << "\n";);
        literal_vector lits;
        enode* start_e = m_jobs[j].m_start;
        enode* end_e = m_jobs[j].m_end;
        lits.push_back(~mk_eq_lit(m_jobs[j].m_job2resource, m_resources[r].m_resource));
        lits.push_back(~mk_ge(start_e, t0));
        lits.push_back(~mk_le(start_e, t1));        
        expr_ref rhs(a.mk_add(start_e->get_owner(), a.mk_int(rational(delta, rational::ui64()))), m);
        lits.push_back(mk_eq_lit(end_e->get_owner(), rhs));
        context& ctx = get_context();
        ctx.mk_clause(lits.size(), lits.c_ptr(), nullptr, CLS_TH_LEMMA, nullptr);
        ast_manager& m = get_manager();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(m.mk_and(ctx.bool_var2expr(lits[0].var()), ctx.bool_var2expr(lits[1].var()), ctx.bool_var2expr(lits[2].var())), ctx.bool_var2expr(lits[3].var()));
            log_axiom_instantiation(body);
            m.trace_stream() << "[end-of-instance]\n";
        }
        return true;
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
        while (overlap.next()) {
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
            lits.push_back(~mk_eq_lit(m_jobs[j].m_job2resource, m_resources[r].m_resource));
            if (j != max_j) {
                lits.push_back(~mk_le(m_jobs[j].m_start, m_jobs[max_j].m_start));
                lits.push_back(~mk_le(m_jobs[max_j].m_start, m_jobs[j].m_end));
            }
            if (j == last_job) break;
        }
        context& ctx = get_context();
        ctx.mk_clause(lits.size(), lits.c_ptr(), nullptr, CLS_TH_LEMMA, nullptr);
    }

    void theory_jobscheduler::propagate() {
        while (m_bound_qhead < m_bound_jobs.size()) {
            unsigned j = m_bound_jobs[m_bound_qhead++];
            unsigned r = 0;
            job_info const& ji = m_jobs[j];
            VERIFY(u.is_resource(ji.m_job2resource->get_root()->get_owner(), r));
            TRACE("csp", tout << "job: " << j << " resource: " << r << "\n";);
            std::cout << j << " -o " << r << "\n";
            propagate_job2resource(j, r);
        }
    }

    void theory_jobscheduler::propagate_job2resource(unsigned j, unsigned r) {
        job_info const& ji = m_jobs[j];
        res_info const& ri = m_resources[r];
        literal eq = mk_eq_lit(ji.m_job2resource, ri.m_resource);
        if (!job_has_resource(j, r)) {
            IF_VERBOSE(0, verbose_stream() << "job " << j << " assigned non-registered resource " << r << "\n");
            return;
        }
        return;
        job_resource const& jr = get_job_resource(j, r);
        assert_last_end_time(j, r, jr, eq);
        assert_last_start_time(j, r, eq);
        assert_first_start_time(j, r, eq);
        vector<res_available> const& available = ri.m_available;
        // TBD: needs to take properties into account
        
        unsigned i = 0;
        if (!first_available(jr, ri, i)) return;
        while (true) {
            unsigned next = i + 1;
            if (!first_available(jr, ri, next)) return;
            SASSERT(available[i].m_end < available[next].m_start);
            assert_job_not_in_gap(j, r, i, next, eq);            
            if (!ji.m_is_preemptable && available[i].m_end + 1 < available[i+1].m_start) {
                assert_job_non_preemptable(j, r, i, next, eq);
            }
            i = next;
        }
    }
        
    theory_jobscheduler::theory_jobscheduler(ast_manager& m): 
        theory(m.get_family_id("csp")), 
        m(m), 
        u(m), 
        a(m), 
        m_bound_qhead(0) {
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, job_resource const& jr) const {
        return out << "r:" << jr.m_resource_id << " cap:" << jr.m_capacity << " load:" << jr.m_loadpct << " end:" << jr.m_finite_capacity_end;
        for (auto const& s : jr.m_properties) {
            out << " " << s;
        }
        out << "\n";
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, job_info const& j) const {
        for (job_resource const& jr : j.m_resources) {
            display(out << "  ", jr) << "\n";
        }
        return out;
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, res_available const& r) const {
        return out << "[" << r.m_start << ":" << r.m_end << "] @ " << r.m_loadpct << "%";
        for (auto const& s : r.m_properties) {
            out << " " << s;
        }
        out << "\n";
    }

    std::ostream& theory_jobscheduler::display(std::ostream & out, res_info const& r) const {
        for (res_available const& ra : r.m_available) {
            display(out << "   ", ra);
        }
        return out;
    }

    void theory_jobscheduler::display(std::ostream & out) const {
        out << "jobscheduler:\n";
        for (unsigned j = 0; j < m_jobs.size(); ++j) {
            display(out << "job " << j << ":\n", m_jobs[j]) << "\n";
        }
        for (unsigned r = 0; r < m_resources.size(); ++r) {
            display(out << "resource " << r << ":\n", m_resources[r]) << "\n";
        }
    }
        
    void theory_jobscheduler::collect_statistics(::statistics & st) const {

    }

    bool theory_jobscheduler::include_func_interp(func_decl* f) {
        return 
            f->get_decl_kind() == OP_JS_START ||
            f->get_decl_kind() == OP_JS_END ||
            f->get_decl_kind() == OP_JS_JOB2RESOURCE;
    }

    void theory_jobscheduler::init_model(model_generator & m) {

    }
    
    model_value_proc * theory_jobscheduler::mk_value(enode * n, model_generator & mg) {
        return alloc(expr_wrapper_proc, n->get_root()->get_owner());
    }

    bool theory_jobscheduler::get_value(enode * n, expr_ref & r) {
        std::cout << mk_pp(n->get_owner(), m) << "\n";
        return false;
    }

    theory * theory_jobscheduler::mk_fresh(context * new_ctx) { 
        return alloc(theory_jobscheduler, new_ctx->get_manager()); 
    }

    time_t theory_jobscheduler::get_lo(expr* e) {
        arith_value av(m);
        av.init(&get_context());
        rational val;
        bool is_strict;
        if (av.get_lo(e, val, is_strict) && !is_strict && val.is_uint64()) {
            return val.get_uint64();
        }
        return 0;
    }

    time_t theory_jobscheduler::get_up(expr* e) {
        arith_value av(m);
        av.init(&get_context());
        rational val;
        bool is_strict;
        if (av.get_up(e, val, is_strict) && !is_strict && val.is_uint64()) {
            return val.get_uint64();
        }
        return std::numeric_limits<time_t>::max();
    }

    time_t theory_jobscheduler::get_value(expr* e) {
        arith_value av(get_manager());
        av.init(&get_context());
        rational val;
        if (av.get_value_equiv(e, val) && val.is_uint64()) {
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

    void theory_jobscheduler::set_preemptable(unsigned j, bool is_preemptable) {
        ensure_job(j).m_is_preemptable = is_preemptable;        
    }

    theory_jobscheduler::res_info& theory_jobscheduler::ensure_resource(unsigned last) {
        while (m_resources.size() <= last) {
            unsigned r = m_resources.size();
            m_resources.push_back(res_info());
            res_info& ri = m_resources.back();
            context& ctx = get_context();
            app_ref res(u.mk_resource(r), m);
            if (!ctx.e_internalized(res)) ctx.internalize(res, false);            
            ri.m_resource = ctx.get_enode(res);
            app_ref ms(u.mk_makespan(r), m);
            if (!ctx.e_internalized(ms)) ctx.internalize(ms, false);            
            ri.m_makespan = ctx.get_enode(ms);
        }
        return m_resources[last];
    }

    theory_jobscheduler::job_info& theory_jobscheduler::ensure_job(unsigned last) {
        while (m_jobs.size() <= last) {
            unsigned j = m_jobs.size();
            m_jobs.push_back(job_info());
            job_info& ji = m_jobs.back();
            context& ctx = get_context();
            app_ref job(u.mk_job(j), m);
            app_ref start(u.mk_start(j), m);
            app_ref end(u.mk_end(j), m);
            app_ref res(u.mk_job2resource(j), m);
            if (!ctx.e_internalized(job))   ctx.internalize(job, false);
            if (!ctx.e_internalized(start)) ctx.internalize(start, false);
            if (!ctx.e_internalized(end))   ctx.internalize(end, false);
            if (!ctx.e_internalized(res))   ctx.internalize(res, false);
            ji.m_job      = ctx.get_enode(job);
            ji.m_start    = ctx.get_enode(start);
            ji.m_end      = ctx.get_enode(end);
            ji.m_job2resource = ctx.get_enode(res);
        }
        return m_jobs[last];
    }

    void theory_jobscheduler::add_job_resource(unsigned j, unsigned r, unsigned loadpct, uint64_t cap, time_t finite_capacity_end, properties const& ps) {
        SASSERT(get_context().at_base_level());
        SASSERT(0 <= loadpct && loadpct <= 100);
        SASSERT(0 <= cap);
        job_info& ji = ensure_job(j);
        res_info& ri = ensure_resource(r);
        if (ji.m_resource2index.contains(r)) {
            throw default_exception("resource already bound to job");
        }
        ji.m_resource2index.insert(r, ji.m_resources.size());
        ji.m_resources.push_back(job_resource(r, cap, loadpct, finite_capacity_end, ps));
        SASSERT(!ri.m_jobs.contains(j));
        ri.m_jobs.push_back(j);
    }


    void theory_jobscheduler::add_resource_available(unsigned r, unsigned max_loadpct, time_t start, time_t end, properties const& ps) {
        SASSERT(get_context().at_base_level());
        SASSERT(1 <= max_loadpct && max_loadpct <= 100);
        SASSERT(start <= end);
        res_info& ri = ensure_resource(r);
        ri.m_available.push_back(res_available(max_loadpct, start, end, ps));
    }

    /*
     * Initialize the state based on the set of jobs and resources added.
     * Ensure that the availability slots for each resource is sorted by time.
     *
     * For each resource j:
     *   est(j) <= start(j) <= end(j) <= lct(j)
     * 
     * possible strengthenings:
     * - start(j) <= lst(j)
     * - start(j) + min_completion_time(j) <= end(j)
     * - start(j) + max_completion_time(j) >= end(j)
     * 
     * makespan constraints?
     *
     */
    void theory_jobscheduler::add_done() {
        TRACE("csp", tout << "add-done begin\n";);
        context & ctx = get_context();
        
        // sort availability intervals
        for (res_info& ri : m_resources) {
            vector<res_available>& available = ri.m_available;
            res_available::compare cmp;
            std::sort(available.begin(), available.end(), cmp);
        }

        literal lit;
        unsigned job_id = 0;
        
        for (job_info const& ji : m_jobs) {
            if (ji.m_resources.empty()) {
                throw default_exception("every job should be associated with at least one resource");
            }

            // start(j) <= end(j)            
            lit = mk_le(ji.m_start, ji.m_end);
            if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(lit.var()));
            ctx.mk_th_axiom(get_id(), 1, &lit);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

            time_t start_lb = std::numeric_limits<time_t>::max();
            time_t runtime_lb = std::numeric_limits<time_t>::max();
            time_t end_ub = 0; // , runtime_ub = 0;
            for (job_resource const& jr : ji.m_resources) {
                unsigned r = jr.m_resource_id;
                res_info const& ri = m_resources[r];
                if (ri.m_available.empty()) {
                    if (jr.m_capacity == 0) {
                        start_lb = 0;
                        end_ub = std::numeric_limits<time_t>::max();
                        runtime_lb = 0;
                    }
                    continue;
                }
                unsigned idx = 0;
                if (first_available(jr, ri, idx)) {
                    start_lb = std::min(start_lb, ri.m_available[idx].m_start);
                }
                else {
                    IF_VERBOSE(0, verbose_stream() << "not first-available\n";);
                }
                idx = ri.m_available.size();
                if (last_available(jr, ri, idx)) {
                    end_ub = std::max(end_ub, ri.m_available[idx].m_end);                    
                }
                else {
                    IF_VERBOSE(0, verbose_stream() << "not last-available\n";);
                }
                runtime_lb = std::min(runtime_lb, jr.m_capacity);
                // TBD: more accurate estimates for runtime_lb based on gaps
                // TBD: correct estimate of runtime_ub taking gaps into account.
            }
            CTRACE("csp", (start_lb > end_ub), tout << "there is no associated resource working time\n";);
            if (start_lb > end_ub) {
                IF_VERBOSE(0, verbose_stream() << start_lb << " " << end_ub << "\n");
                warning_msg("Job %d has no associated resource working time", job_id);
                continue;
            }

            // start(j) >= start_lb
            lit = mk_ge(ji.m_start, start_lb);
            if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(lit.var()));
            ctx.mk_th_axiom(get_id(), 1, &lit);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

            // end(j) <= end_ub
            lit = mk_le(ji.m_end, end_ub);
            if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(lit.var()));
            ctx.mk_th_axiom(get_id(), 1, &lit);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

            // start(j) + runtime_lb <= end(j)
            // end(j) <= start(j) + runtime_ub 

            ++job_id;
        }        
        
        TRACE("csp", tout << "add-done end\n";);
    }

    // resource(j) = r => end(j) <= end(j, r)
    void theory_jobscheduler::assert_last_end_time(unsigned j, unsigned r, job_resource const& jr, literal eq) {
#if 0
        job_info const& ji = m_jobs[j];
        literal l2 = mk_le(ji.m_end, jr.m_finite_capacity_end);
        context& ctx = get_context();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(ctx.bool_var2expr(eq.var()), ctx.bool_var2expr(l2.var()));
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), ~eq, l2);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
#endif
    }

    // resource(j) = r => start(j) <= lst(j, r, end(j, r))
    void theory_jobscheduler::assert_last_start_time(unsigned j, unsigned r, literal eq) {
        context& ctx = get_context();
        time_t t;
        if (lst(j, r, t)) {
            literal le = mk_le(m_jobs[j].m_start, t);
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(ctx.bool_var2expr(eq.var()), ctx.bool_var2expr(le.var()));
                log_axiom_instantiation(body);
            }
            ctx.mk_th_axiom(get_id(), ~eq, le);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
        else {
            eq.neg();
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_not(ctx.bool_var2expr(eq.var()));
                log_axiom_instantiation(body);
            }
            ctx.mk_th_axiom(get_id(), 1, &eq);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
    }

    // resource(j) = r => start(j) >= available[0].m_start
    void theory_jobscheduler::assert_first_start_time(unsigned j, unsigned r, literal eq) {
        job_resource const& jr = get_job_resource(j, r);
        unsigned idx = 0;
        if (!first_available(jr, m_resources[r], idx)) return;
        vector<res_available>& available = m_resources[r].m_available;
        literal l2 = mk_ge(m_jobs[j].m_start, available[idx].m_start);
        context& ctx = get_context();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(ctx.bool_var2expr(eq.var()), ctx.bool_var2expr(l2.var()));
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), ~eq, l2);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    // resource(j) = r => start(j) <= end[idx]  || start[idx+1] <= start(j);
    void theory_jobscheduler::assert_job_not_in_gap(unsigned j, unsigned r, unsigned idx, unsigned idx1, literal eq) {
        job_resource const& jr = get_job_resource(j, r);
        (void) jr;
        vector<res_available>& available = m_resources[r].m_available;        
        SASSERT(resource_available(jr, available[idx]));
        literal l2 = mk_ge(m_jobs[j].m_start, available[idx1].m_start);
        literal l3 = mk_le(m_jobs[j].m_start, available[idx].m_end);
        context& ctx = get_context();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(ctx.bool_var2expr(eq.var()), m.mk_or(ctx.bool_var2expr(l2.var()), ctx.bool_var2expr(l3.var())));
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), ~eq, l2, l3);        
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    // resource(j) = r => end(j) <= end[idx] || start[idx+1] <= start(j);
    void theory_jobscheduler::assert_job_non_preemptable(unsigned j, unsigned r, unsigned idx, unsigned idx1, literal eq) {
        vector<res_available>& available = m_resources[r].m_available;        
        job_resource const& jr = get_job_resource(j, r);
        (void) jr;
        SASSERT(resource_available(jr, available[idx]));
        literal l2 = mk_le(m_jobs[j].m_end, available[idx].m_end);
        literal l3 = mk_ge(m_jobs[j].m_start, available[idx1].m_start);
        context& ctx = get_context();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(ctx.bool_var2expr(eq.var()), m.mk_or(ctx.bool_var2expr(l2.var()), ctx.bool_var2expr(l3.var())));
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), ~eq, l2, l3);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }    

    /**
     * bind a job to one of the resources it can run on.
     */
    bool theory_jobscheduler::split_job2resource(unsigned j) {
        job_info const& ji = m_jobs[j];
        context& ctx = get_context();
        if (ji.m_is_bound) return false;
        auto const& jrs = ji.m_resources;
        for (job_resource const& jr : jrs) {
            unsigned r = jr.m_resource_id;
            res_info const& ri = m_resources[r];
            enode* e1 = ji.m_job2resource;
            enode* e2 = ri.m_resource;
            if (ctx.is_diseq(e1, e2))
                continue;
            literal eq = mk_eq_lit(e1, e2);
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_or(ctx.bool_var2expr(eq.var()), m.mk_not(ctx.bool_var2expr(eq.var())));
                log_axiom_instantiation(body);
                m.trace_stream() << "[end-of-instance]\n";
            }
            if (ctx.get_assignment(eq) != l_false) {
                ctx.mark_as_relevant(eq);
                if (assume_eq(e1, e2)) {
                    return true;
                }
            }
        }
        literal_vector lits;
        expr_ref_vector exprs(m);
        for (job_resource const& jr : jrs) {
            unsigned r = jr.m_resource_id;
            res_info const& ri = m_resources[r];
            enode* e1 = ji.m_job2resource;
            enode* e2 = ri.m_resource;
            literal eq = mk_eq_lit(e1, e2);
            lits.push_back(eq);
            exprs.push_back(ctx.bool_var2expr(eq.var()));
        }
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_or(exprs.size(), exprs.c_ptr());
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        return true;
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
            job_overlap overlap(start_times[r], end_times[r]);
            while (overlap.next()) {
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

    bool theory_jobscheduler::job_has_resource(unsigned j, unsigned r) const {
        return m_jobs[j].m_resource2index.contains(r);
    }

    theory_jobscheduler::job_resource const& theory_jobscheduler::get_job_resource(unsigned j, unsigned r) const {
        job_info const& ji = m_jobs[j];
        return ji.m_resources[ji.m_resource2index[r]];
    }

    /**
     * find idx, if any, such that t is within the time interval of available[idx]
     */    
    bool theory_jobscheduler::resource_available(unsigned r, time_t t, unsigned& idx) {
        vector<res_available>& available = m_resources[r].m_available;
        unsigned lo = 0, hi = available.size(), mid = hi / 2;
        while (lo < hi) {
            SASSERT(lo <= mid && mid < hi);
            res_available const& ra = available[mid];
            if (ra.m_start <= t && t <= ra.m_end) {
                idx = mid;
                return true;
            }
            else if (ra.m_start > t && mid > 0) {
                hi = mid;
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
            TRACE("csp", tout << "resource is not available for " << j << " " << r << "\n";);
            return std::numeric_limits<time_t>::max();
        }
        SASSERT(cap > 0);
        
        for (; idx < available.size(); ++idx) {
            if (!resource_available(jr, available[idx])) continue;
            start             = std::max(start, available[idx].m_start);
            time_t end        = available[idx].m_end;
            unsigned load_pct = available[idx].m_loadpct;
            time_t delta = solve_for_capacity(load_pct, j_load_pct, start, end);
            TRACE("csp", tout << "delta: " << delta << " capacity: " << cap << " load " 
                  << load_pct << " jload: " << j_load_pct << " start: " << start << " end " << end << "\n";);
            if (delta > cap) {
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

    /**
     * find end, such that cap = (load / job_load_pct) * (end - start + 1)
     */
    time_t theory_jobscheduler::solve_for_end(unsigned load_pct, unsigned job_load_pct, time_t start, time_t cap) {
        SASSERT(load_pct > 0);
        SASSERT(job_load_pct > 0);
        //      cap = (load / job_load_pct) * (end - start + 1)
        // <=> 
        //      end - start + 1 = (cap * job_load_pct) / load 
        // <=>
        //      end = start - 1 + (cap * job_load_pct) / load
        // <=>
        //      end = (load * (start - 1) + cap * job_load_pct) / load
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (start - 1) + cap * job_load_pct) / load;
    }

    /**
     * find start, such that cap = (load / job_load_pct) * (end - start + 1)
     */
    time_t theory_jobscheduler::solve_for_start(unsigned load_pct, unsigned job_load_pct, time_t end, time_t cap) {
        SASSERT(load_pct > 0);
        SASSERT(job_load_pct > 0);
        //      cap = (load / job_load_pct) * (end - start + 1)
        // <=> 
        //      end - start + 1 = (cap * job_load_pct) / load 
        // <=>
        //      start = end + 1 - (cap * job_load_pct) / load
        // <=>
        //      start = (load * (end + 1) - cap * job_load_pct) / load
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (end + 1) - cap * job_load_pct) / load;
    }

    /**
     * find cap, such that cap = (load / job_load_pct) * (end - start + 1)
     */
    time_t theory_jobscheduler::solve_for_capacity(unsigned load_pct, unsigned job_load_pct, time_t start, time_t end) {
        SASSERT(job_load_pct > 0);
        unsigned load = std::min(load_pct, job_load_pct);
        return (load * (end - start + 1)) / job_load_pct;
    }

    /**
     * Compute last start time for job on resource r.
     */
    bool theory_jobscheduler::lst(unsigned j, unsigned r, time_t& start) {
        start = 0;
        job_resource const& jr = get_job_resource(j, r);
        vector<res_available>& available = m_resources[r].m_available;
        unsigned j_load_pct = jr.m_loadpct;
        time_t cap = jr.m_capacity;
        for (unsigned idx = available.size(); idx-- > 0; ) {
            if (!resource_available(jr, available[idx])) continue;
            start    = available[idx].m_start;
            time_t end      = available[idx].m_end;
            unsigned load_pct = available[idx].m_loadpct;
            time_t delta = solve_for_capacity(load_pct, j_load_pct, start, end);
            if (delta > cap) {
                start = solve_for_start(load_pct, j_load_pct, end, cap);
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

    /**
     * \brief check that job properties is a subset of resource properties.
     * It assumes that both vectors are sorted.
     */

    bool theory_jobscheduler::resource_available(job_resource const& jr, res_available const& ra) const {
        auto const& jps = jr.m_properties;
        auto const& rps = ra.m_properties;
        if (jps.size() > rps.size()) {
            return false;
        }
        unsigned j = 0, i = 0;
        for (; i < jps.size() && j < rps.size(); ) {
            if (jps[i] == rps[j]) {
                ++i; ++j;
            }
            else if (lt(rps[j], jps[i])) {
                ++j;
            }
            else {
                break;
            }            
        }
        return i == jps.size();
    }

    /**
     * \brief minimal current resource available for job resource, includes idx.
     */
    bool theory_jobscheduler::first_available(job_resource const& jr, res_info const& ri, unsigned& idx) const {
        for (; idx < ri.m_available.size(); ++idx) {
            if (resource_available(jr, ri.m_available[idx])) 
                return true;
        }
        return false;
    }

    /**
     * \brief maximal previous resource available for job resource, excludes idx.
     */
    bool theory_jobscheduler::last_available(job_resource const& jr, res_info const& ri, unsigned& idx) const {
        while (idx-- > 0) {
            if (resource_available(jr, ri.m_available[idx])) 
                return true;
        }
        return false;
    }

    
};

