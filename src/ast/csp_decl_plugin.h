/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    csp_decl_plugin.h

Abstract:

    Declarations used for a job-shop scheduling domain.

    The job-shop domain comprises of constants job(j), resource(r)

    It finds values to variables:
    - start(j), end(j), job2resource(j)

    It assumes a background of:
    - resources : Job -> Resource -> Int * LoadPct - time to run job j on resource r assuming LoadPct
    - runtime   : Job -> Int                       - time to run job j if not associated with any resource
    - capacity  : Resource -> Int -> LoadPct       - capacity of resource r at time t, given as sequence of time intervals
    // assume each job has at least one resource associated with it.    
    // introduce a dummy resource if needed.

    // Theory:
    end(j) - start(j) = time-to-execute(j)
    time-to-execute(j) := time-to-execute(j, resource(j))  otherwise

    time-to-execute(j, r) := (T - start(j)) 
            where capacity(j,r) = sum_{t = start(j)}^{T} load(loadpct(j,r), r, t)

    capacity(j, r) := cap where (cap, loadpct) = resources j r
    loadpct(j, r)  := loadpct where (cap, loadpct) = resources j r

    load(loadpct, r, t) := min(capacity r t, loadpct) / loadpct

    capacity(r, t) >= sum_{j | job-on-resource(j, r, t) } min(capacity r t, loadpct(j, r))

    // Macros:
    job-on-resource(j, r)              := r = resource(j);
    job-on-resource(j, r, t)           := (job-on-resource(j, r) & start(j) <= t <= end(j));
    start_min(j, t)                    := start(j) >= t;
    end_max(j, t)                      := end(j) <= t;
    job_link(j1, j2, startstart, hard) := start(j1) = start(j2);
    job_link(j1, j2, startstart, soft) := start(j1) <= start(j2);
    job_link(j1, j2, endend, hard)     := end(j1) =  end(j2);
    job_link(j1, j2, endend, soft)     := end(j2) <= end(j1);
    job_link(j1, j2, endstart, hard)   := end(j1) =  start(j2);
    job_link(j1, j2, endstart, soft)   := end(j2) <= start(j1);
    job_link(j1, j2, startend, hard)   := end(j2) =  start(j1);
    job_link(j1, j2, startend, soft)   := end(j1) <= start(j2);
    job_delay(j1, j2, t)               := end(j1) + t <= end(j2);
    job_on_same_resource(j1, j2)       := resource(j1) = resource(j2);
    job_not_on_same_resource(j1, j2)   := resource(j1) != resource(j2);
    job_time_intersect(j1, j2)         := start(j1) <= end(j2) <= end(j1) || start(j2) <= end(j1) <= end(j2);
    
    job-on-resource(j, r, t) => job-property(j) = null or job_property(j) in working_time_property(r, t);
        
Author:

    Nikolaj Bjorner (nbjorner) 2018-8-9 

Revision History:


--*/
#pragma once
#include "ast/ast.h"

enum js_sort_kind {
    JOB_SORT,
    RESOURCE_SORT,
    ALIST_SORT
};

enum js_op_kind {
    OP_JS_JOB,               // value of type job
    OP_JS_RESOURCE,          // value of type resource
    OP_JS_RESOURCE_MAKESPAN, // makespan of resource: the minimal resource time required for assigned jobs.
    OP_JS_START,             // start time of a job
    OP_JS_END,               // end time of a job
    OP_JS_JOB2RESOURCE,      // resource associated with job
    OP_JS_MODEL,             // jobscheduler model
    OP_JS_JOB_RESOURCE,      // model declaration for job assignment to resource
    OP_JS_JOB_PREEMPTABLE,   // model declaration for whether job is pre-emptable
    OP_JS_RESOURCE_AVAILABLE, // model declaration for availability intervals of resource
    OP_JS_PROPERTIES,         // model declaration of a set of properties. Each property is a keyword.
    OP_JS_JOB_GOAL,           // job goal objective :earliest-end-time or :latest-start-time
    OP_JS_OBJECTIVE           // duration or completion-time
};

enum js_job_goal {
    JS_JOB_GOAL_EARLIEST_END_TIME,
    JS_JOB_GOAL_LATEST_START_TIME
};

enum js_optimization_objective {
    JS_OBJECTIVE_DURATION,
    JS_OBJECTIVE_PRIORITY
};

class csp_decl_plugin : public decl_plugin {
public:
    csp_decl_plugin() {}
    ~csp_decl_plugin() override {}
    void finalize() override;
    void set_manager(ast_manager* m, family_id fid) override;
    decl_plugin * mk_fresh() override { return alloc(csp_decl_plugin); }
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;	
    bool is_value(app * e) const override;
    bool is_unique_value(app * e) const override { return is_value(e); }
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;
    expr * get_some_value(sort * s) override;
    sort * mk_job_sort() const { return m_job_sort; }
    sort * mk_resource_sort() const { return m_resource_sort; }
    sort * mk_alist_sort() const { return m_alist_sort; }
private:
    sort* m_job_sort;
    sort* m_resource_sort;
    sort* m_alist_sort;
    sort* m_int_sort;

    void check_arity(unsigned arity);
    void check_index1(unsigned n, parameter const* ps);
    void check_index2(unsigned n, parameter const* ps);
};

class csp_util {
    ast_manager&         m;
    family_id            m_fid;
    csp_decl_plugin*     m_plugin;
public:
    csp_util(ast_manager& m);
    sort* mk_job_sort();
    sort* mk_resource_sort();

    app* mk_job(unsigned j);
    app* mk_resource(unsigned r);
    app* mk_start(unsigned j);
    app* mk_end(unsigned j);
    app* mk_job2resource(unsigned j);
    app* mk_makespan(unsigned r);

    bool is_job(expr* e, unsigned& j);
    bool is_job2resource(expr* e, unsigned& j);
    bool is_resource(expr* e, unsigned& r);
    bool is_makespan(expr* e, unsigned& r);
    bool is_add_resource_available(expr * e, expr *& res, unsigned& loadpct, unsigned& cap_time, uint64_t& start, uint64_t& end, svector<symbol>& properites);
    bool is_add_job_resource(expr * e, expr *& job, expr*& res, unsigned& loadpct, uint64_t& capacity, uint64_t& finite_capacity_end, svector<symbol>& properites); 
    bool is_set_preemptable(expr* e, expr *& job);
    bool is_model(expr* e) const { return is_app_of(e, m_fid, OP_JS_MODEL); }
    bool is_js_properties(expr* e, svector<symbol>& properties);
    bool is_job_goal(expr* e, js_job_goal& goal, unsigned& level, expr*& job);
    bool is_objective(expr* e, js_optimization_objective& objective);

private:
    unsigned job2id(expr* j);
    unsigned resource2id(expr* r);

};
