/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxsres.cpp

Abstract:
   
    MaxRes (weighted) max-sat algorithms:

    - mus:     max-sat algorithm by Nina and Bacchus, AAAI 2014.
    - mus-mss: based on dual refinement of bounds.

    MaxRes is a core-guided approach to maxsat.
    MusMssMaxRes extends the core-guided approach by
    leveraging both cores and satisfying assignments
    to make progress towards a maximal satisfying assignment.

    Given a (minimal) unsatisfiable core for the soft
    constraints the approach works like max-res.
    Given a (maximal) satisfying subset of the soft constraints
    the approach updates the upper bound if the current assignment
    improves the current best assignmet.
    Furthermore, take the soft constraints that are complements
    to the current satisfying subset. 
    E.g, if F are the hard constraints and 
    s1,...,sn, t1,..., tm are the soft clauses and 
    F & s1 & ... & sn is satisfiable, then the complement 
    of of the current satisfying subset is t1, .., tm.
    Update the hard constraint:
         F := F & (t1 or ... or tm)
    Replace t1, .., tm by m-1 new soft clauses:
         t1 & t2, t3 & (t1 or t2), t4 & (t1 or t2 or t3), ..., tn & (t1 or ... t_{n-1})
    Claim: 
       If k of these soft clauses are satisfied, then k+1 of 
       the previous soft clauses are satisfied.
       If k of these soft clauses are false in the satisfying assignment 
       for the updated F, then k of the original soft clauses are also false 
       under the assignment.
       In summary: any assignment to the new clauses that satsfies F has the
       same cost.
    Claim:
       If there are no satisfying assignments to F, then the current best assignment
       is the optimum.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/

#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "ast/ast_util.h"
#include "model/model_smt2_pp.h"
#include "solver/solver.h"
#include "solver/mus.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "smt/smt_solver.h"
#include "opt/opt_context.h"
#include "opt/opt_params.hpp"
#include "opt/maxsmt.h"
#include "opt/maxres.h"

using namespace opt;

class maxres : public maxsmt_solver_base {
public:
    enum strategy_t {
        s_primal,
        s_primal_dual
    };
private:
    struct stats {
        unsigned m_num_cores;
        unsigned m_num_cs;
        stats() { reset(); }
        void reset() {
            memset(this, 0, sizeof(*this));
        }
    };
    unsigned         m_index;
    stats            m_stats;
    expr_ref_vector  m_B;
    expr_ref_vector  m_asms;    
    expr_ref_vector  m_defs;
    obj_map<expr, rational> m_asm2weight;
    ptr_vector<expr> m_new_core;
    mus              m_mus;
    expr_ref_vector  m_trail;
    strategy_t       m_st;
    rational         m_max_upper;    
    model_ref        m_csmodel;
    unsigned         m_correction_set_size;
    bool             m_found_feasible_optimum;
    bool             m_hill_climb;             // prefer large weight soft clauses for cores
    unsigned         m_last_index;             // last index used during hill-climbing
    bool             m_add_upper_bound_block;  // restrict upper bound with constraint
    unsigned         m_max_num_cores;          // max number of cores per round.
    unsigned         m_max_core_size;          // max core size per round.
    bool             m_maximize_assignment;    // maximize assignment to find MCS
    unsigned         m_max_correction_set_size;// maximal set of correction set that is tolerated.
    bool             m_wmax;                   // Block upper bound using wmax
                                               // this option is disabled if SAT core is used.
    bool             m_pivot_on_cs;            // prefer smaller correction set to core.
    bool             m_dump_benchmarks;        // display benchmarks (into wcnf format)


    std::string      m_trace_id;
    typedef ptr_vector<expr> exprs;

public:
    maxres(maxsat_context& c, unsigned index, 
           weights_t& ws, expr_ref_vector const& soft, 
           strategy_t st):
        maxsmt_solver_base(c, ws, soft),
        m_index(index), 
        m_B(m), m_asms(m), m_defs(m),
        m_mus(c.get_solver()),
        m_trail(m),
        m_st(st),
        m_correction_set_size(0),
        m_found_feasible_optimum(false),
        m_hill_climb(true),
        m_last_index(0),
        m_add_upper_bound_block(false),
        m_max_num_cores(UINT_MAX),
        m_max_core_size(3),
        m_maximize_assignment(false),
        m_max_correction_set_size(3),
        m_pivot_on_cs(true)
    {
        switch(st) {
        case s_primal:
            m_trace_id = "maxres";
            break;
        case s_primal_dual:
            m_trace_id = "pd-maxres";
            break;
        }        
    }

    virtual ~maxres() {}

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }    

    void add_soft(expr* e, rational const& w) {
        TRACE("opt", tout << mk_pp(e, m) << " |-> " << w << "\n";);
        expr_ref asum(m), fml(m);
        app_ref cls(m);
        rational weight(0);
        if (m_asm2weight.find(e, weight)) {
            weight += w;
            m_asm2weight.insert(e, weight);
            return;
        }
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = mk_fresh_bool("soft");
            fml = m.mk_iff(asum, e);
            s().assert_expr(fml);
        }
        new_assumption(asum, w);
    }

    void new_assumption(expr* e, rational const& w) {
        IF_VERBOSE(13, verbose_stream() << "new assumption " << mk_pp(e, m) << " " << w << "\n";);
        TRACE("opt", tout << "insert: " << mk_pp(e, m) << " : " << w << "\n";);
        m_asm2weight.insert(e, w);
        m_asms.push_back(e);
        m_trail.push_back(e);        
    }

    void trace() {
        trace_bounds(m_trace_id.c_str());
    }

    lbool mus_solver() {
        lbool is_sat = l_true;
        if (!init()) return l_undef;
        is_sat = init_local();
        trace();
        if (is_sat != l_true) return is_sat;
        while (m_lower < m_upper) {
            TRACE("opt", 
                  display_vec(tout, m_asms);
                  s().display(tout);
                  tout << "\n";
                  display(tout);
                  );
            is_sat = check_sat_hill_climb(m_asms);
            if (m.canceled()) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true: 
                SASSERT(is_true(m_asms));
                found_optimum();
                return l_true;
            case l_false:
                is_sat = process_unsat();
                if (is_sat == l_false) {
                    m_lower = m_upper;
                }
                if (is_sat == l_undef) {
                    return is_sat;                        
                }
                break;
            case l_undef:
                return l_undef;
            default:
                break;
            }
        }
        found_optimum();
        trace();
        return l_true;
    }

    lbool primal_dual_solver() {
        if (!init()) return l_undef;
        lbool is_sat = init_local();
        trace();
        exprs cs;
        if (is_sat != l_true) return is_sat;
        while (m_lower < m_upper) {
            is_sat = check_sat_hill_climb(m_asms);
            if (m.canceled()) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true: 
                get_current_correction_set(cs);
                if (cs.empty()) {
                    m_found_feasible_optimum = m_model.get() != nullptr;
                    m_lower = m_upper;
                }
                else {
                    process_sat(cs);
                }
                break;
            case l_false:
                is_sat = process_unsat();
                if (is_sat == l_false) {
                    m_lower = m_upper;
                }
                if (is_sat == l_undef) {
                    return is_sat;                        
                }
                break;
            case l_undef:
                return l_undef;
            default:
                break;
            }
        }
        m_lower = m_upper;
        trace();
        return l_true;
    }

    lbool check_sat_hill_climb(expr_ref_vector& asms1) {
        expr_ref_vector asms(asms1);
        lbool is_sat = l_true;
        if (m_hill_climb) {
            /**
               Give preference to cores that have large minmal values.
            */
            sort_assumptions(asms);  
            
            m_last_index = std::min(m_last_index, asms.size()-1);
            m_last_index = 0;
            unsigned index = m_last_index>0?m_last_index-1:0;
            m_last_index = 0;
            bool first = index > 0;
            SASSERT(index < asms.size() || asms.empty());
            IF_VERBOSE(10, verbose_stream() << "start hill climb " << index << " asms: " << asms.size() << "\n";);
            while (index < asms.size() && is_sat == l_true) {
                while (!first && asms.size() > 20*(index - m_last_index) && index < asms.size()) {
                    index = next_index(asms, index);
                }
                first = false;
                IF_VERBOSE(3, verbose_stream() << "hill climb " << index << "\n";);
                // IF_VERBOSE(3, verbose_stream() << "weight: " << get_weight(asms[0].get()) << " " << get_weight(asms[index-1].get()) << " num soft: " << index << "\n";);
                m_last_index = index;
                is_sat = check_sat(index, asms.c_ptr());
            }            
        }
        else {
            is_sat = check_sat(asms.size(), asms.c_ptr());            
        }              
        return is_sat;
    }

    lbool check_sat(unsigned sz, expr* const* asms) {
        lbool r = s().check_sat(sz, asms);        
        if (r == l_true) {
            model_ref mdl;
            s().get_model(mdl);
            if (mdl.get()) {
                update_assignment(mdl.get());            
            }
        }
        return r;
    }

    void found_optimum() {
        IF_VERBOSE(1, verbose_stream() << "found optimum\n";);
        m_lower.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            m_assignment[i] = is_true(m_soft[i]);
            if (!m_assignment[i]) {
                m_lower += m_weights[i];
            }
        }
        m_upper = m_lower;
        m_found_feasible_optimum = true;
    }


    virtual lbool operator()() {
        m_defs.reset();
        switch(m_st) {
        case s_primal:
            return mus_solver();
        case s_primal_dual:
            return primal_dual_solver();
        }
        return l_undef;
    }

    virtual void collect_statistics(statistics& st) const { 
        st.update("maxres-cores", m_stats.m_num_cores);
        st.update("maxres-correction-sets", m_stats.m_num_cs);
    }

    lbool get_cores(vector<exprs>& cores) {
        // assume m_s is unsat.
        lbool is_sat = l_false;
        expr_ref_vector asms(m_asms);
        cores.reset();
        exprs core;
        while (is_sat == l_false) {
            core.reset();
            s().get_unsat_core(core);
            // verify_core(core);
            model_ref mdl;
            get_mus_model(mdl);
            is_sat = minimize_core(core);
            ++m_stats.m_num_cores;
            if (is_sat != l_true) {
                IF_VERBOSE(100, verbose_stream() << "(opt.maxres minimization failed)\n";);
                break;
            }
            if (core.empty()) {
                IF_VERBOSE(100, verbose_stream() << "(opt.maxres core is empty)\n";);
                cores.reset();
                m_lower = m_upper;
                return l_true;
            }
            split_core(core);
            cores.push_back(core);
            if (core.size() >= m_max_core_size) {
                break;
            }
            if (cores.size() >= m_max_num_cores) {
                break;
            }
            remove_soft(core, asms);
            is_sat = check_sat_hill_climb(asms);
        }
        TRACE("opt", 
              tout << "num cores: " << cores.size() << "\n";
              for (unsigned i = 0; i < cores.size(); ++i) {
                  display_vec(tout, cores[i]);
              }
              tout << "num satisfying: " << asms.size() << "\n";);
        
        return is_sat;
    }

    void get_current_correction_set(exprs& cs) {
        model_ref mdl;
        s().get_model(mdl);
        update_assignment(mdl.get());
        get_current_correction_set(mdl.get(), cs);
    }

    void get_current_correction_set(model* mdl, exprs& cs) {
        cs.reset();
        if (!mdl) return;
        for (expr* a : m_asms) {
            if (is_false(mdl, a)) {
                cs.push_back(a);
            }
            TRACE("opt", expr_ref tmp(m); mdl->eval(a, tmp, true); tout << mk_pp(a, m) << ": " << tmp << "\n";);
        }
        TRACE("opt", display_vec(tout << "new correction set: ", cs););
    }

    struct compare_asm {
        maxres& mr;
        compare_asm(maxres& mr):mr(mr) {}
        bool operator()(expr* a, expr* b) const {
            return mr.get_weight(a) > mr.get_weight(b);
        }
    };

    void sort_assumptions(expr_ref_vector& _asms) {
        compare_asm comp(*this);
        exprs asms(_asms.size(), _asms.c_ptr());
        expr_ref_vector trail(_asms);
        std::sort(asms.begin(), asms.end(), comp);
        _asms.reset();
        _asms.append(asms.size(), asms.c_ptr());
        DEBUG_CODE(
            for (unsigned i = 0; i + 1 < asms.size(); ++i) {
                SASSERT(get_weight(asms[i]) >= get_weight(asms[i+1]));
            });
    }

    unsigned next_index(expr_ref_vector const& asms, unsigned index) {
        if (index < asms.size()) {
            rational w = get_weight(asms[index]);
            ++index;
            for (; index < asms.size() && w == get_weight(asms[index]); ++index);
        }
        return index;
    }

    void process_sat(exprs const& corr_set) {
        ++m_stats.m_num_cs;
        expr_ref fml(m), tmp(m);
        TRACE("opt", display_vec(tout << "corr_set: ", corr_set););
        remove_core(corr_set);
        rational w = split_core(corr_set);
        cs_max_resolve(corr_set, w);       
        IF_VERBOSE(2, verbose_stream() << "(opt.maxres.correction-set " << corr_set.size() << ")\n";);
        m_csmodel = nullptr;
        m_correction_set_size = 0;
    }

    lbool process_unsat() {
        vector<exprs> cores;
        lbool is_sat = get_cores(cores);
        if (is_sat != l_true) {
            return is_sat;
        }
        if (cores.empty()) {
            return l_false;
        }
        else {
            process_unsat(cores);
            return l_true;
        }
    }

    unsigned max_core_size(vector<exprs> const& cores) {
        unsigned result = 0;
        for (unsigned i = 0; i < cores.size(); ++i) {
            result = std::max(cores[i].size(), result);
        }
        return result;
    }

    void process_unsat(vector<exprs> const& cores) {
        for (unsigned i = 0; i < cores.size(); ++i) {
            process_unsat(cores[i]);
        }
    }

    void update_model(expr* def, expr* value) {
        SASSERT(is_uninterp_const(def));        
        if (m_csmodel) {
            expr_ref val(m);
            SASSERT(m_csmodel.get());
            if (m_csmodel->eval(value, val, true)) {
                m_csmodel->register_decl(to_app(def)->get_decl(), val);
            }
        }
    }
    
    void process_unsat(exprs const& core) {
        IF_VERBOSE(3, verbose_stream() << "(maxres cs model valid: " << (m_csmodel.get() != nullptr) << " cs size:" << m_correction_set_size << " core: " << core.size() << ")\n";);
        expr_ref fml(m);
        remove_core(core);
        SASSERT(!core.empty());
        rational w = core_weight(core);
        TRACE("opt", display_vec(tout << "minimized core: ", core););
        IF_VERBOSE(10, display_vec(verbose_stream() << "core: ", core););
        max_resolve(core, w);
        fml = mk_not(m, mk_and(m, core.size(), core.c_ptr()));
        s().assert_expr(fml);
        m_lower += w;
        if (m_st == s_primal_dual) {
            m_lower = std::min(m_lower, m_upper);
        }
        if (m_csmodel.get() && m_correction_set_size > 0) {
            // this estimate can overshoot for weighted soft constraints. 
            --m_correction_set_size;
        }
        trace();
        if (m_c.num_objectives() == 1 && m_pivot_on_cs && m_csmodel.get() && m_correction_set_size < core.size()) {
            exprs cs;
            TRACE("opt", tout << "cs " << m_correction_set_size << " " << core.size() << "\n";);
            get_current_correction_set(m_csmodel.get(), cs);
            m_correction_set_size = cs.size();
            if (m_correction_set_size < core.size()) {
                process_sat(cs);
                return;
            }
        }
    }

    bool get_mus_model(model_ref& mdl) {
        rational w(0);
        if (m_c.sat_enabled()) {
            // SAT solver core extracts some model 
            // during unsat core computation.
            mdl = nullptr;
            s().get_model(mdl);
        }
        else {
            w = m_mus.get_best_model(mdl);
        }
        if (mdl.get() && w < m_upper) {
            update_assignment(mdl.get());
        }
        return nullptr != mdl.get();
    }

    lbool minimize_core(exprs& core) {
        if (core.empty()) {
            return l_true;
        }
        if (m_c.sat_enabled()) {
            return l_true;
        }
        m_mus.reset();
        m_mus.add_soft(core.size(), core.c_ptr());
        lbool is_sat = m_mus.get_mus(m_new_core);
        if (is_sat != l_true) {
            return is_sat;
        }
        core.reset();
        core.append(m_new_core);
        return l_true;
    }

    rational get_weight(expr* e) const {
        return m_asm2weight.find(e);
    }

    rational core_weight(exprs const& core) {
        if (core.empty()) return rational(0);
        // find the minimal weight:
        rational w = get_weight(core[0]);
        for (unsigned i = 1; i < core.size(); ++i) {
            w = std::min(w, get_weight(core[i]));
        }
        return w;
    }

    rational split_core(exprs const& core) {
        rational w = core_weight(core);
        // add fresh soft clauses for weights that are above w.
        for (expr* e : core) {
            rational w2 = get_weight(e);
            if (w2 > w) {
                rational w3 = w2 - w;
                new_assumption(e, w3);
            }
        }        
        return w;
    }

    void display_vec(std::ostream& out, exprs const& exprs) {
        display_vec(out, exprs.size(), exprs.c_ptr());
    }

    void display_vec(std::ostream& out, expr_ref_vector const& exprs) {
        display_vec(out, exprs.size(), exprs.c_ptr());
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) const {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " : " << get_weight(args[i]) << " ";
        }
        out << "\n";
    }

    void display(std::ostream& out) {
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            expr* a = m_asms[i].get();
            out << mk_pp(a, m) << " : " << get_weight(a) << "\n";
        }
    }

    void max_resolve(exprs const& core, rational const& w) {
        SASSERT(!core.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(core.size(), core.c_ptr());
        //
        // d_0 := true
        // d_i := b_{i-1} and d_{i-1}    for i = 1...sz-1
        // soft (b_i or !d_i) 
        //   == (b_i or !(!b_{i-1} or d_{i-1}))
        //   == (b_i or b_0 & b_1 & ... & b_{i-1})
        // 
        // Soft constraint is satisfied if previous soft constraint
        // holds or if it is the first soft constraint to fail.
        // 
        // Soundness of this rule can be established using MaxRes
        // 
        for (unsigned i = 1; i < core.size(); ++i) {
            expr* b_i = core[i-1];
            expr* b_i1 = core[i];
            if (i == 1) {
                d = to_app(b_i);
            }
            else if (i == 2) {
                d = m.mk_and(b_i, d);
                m_trail.push_back(d);
            }
            else {
                dd = mk_fresh_bool("d");
                fml = m.mk_implies(dd, d);
                s().assert_expr(fml);
                m_defs.push_back(fml);
                fml = m.mk_implies(dd, b_i);
                s().assert_expr(fml);
                m_defs.push_back(fml);
                fml = m.mk_and(d, b_i);
                update_model(dd, fml);
                d = dd;
            }
            asum = mk_fresh_bool("a");
            cls = m.mk_or(b_i1, d);
            fml = m.mk_implies(asum, cls);
            update_model(asum, cls);
            new_assumption(asum, w);
            s().assert_expr(fml);
            m_defs.push_back(fml);
        }
    }

    // cs is a correction set (a complement of a (maximal) satisfying assignment).
    void cs_max_resolve(exprs const& cs, rational const& w) {
        if (cs.empty()) return;
        TRACE("opt", display_vec(tout << "correction set: ", cs););
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(cs.size(), cs.c_ptr());
        d = m.mk_false();
        //
        // d_0 := false
        // d_i := b_{i-1} or d_{i-1}    for i = 1...sz-1
        // soft (b_i and d_i) 
        //   == (b_i and (b_0 or b_1 or ... or b_{i-1}))
        //
        // asm => b_i
        // asm => d_{i-1} or b_{i-1}
        // d_i => d_{i-1} or b_{i-1}
        //
        for (unsigned i = 1; i < cs.size(); ++i) {
            expr* b_i = cs[i - 1];
            expr* b_i1 = cs[i];
            cls = m.mk_or(b_i, d);
            if (i > 2) {
                d = mk_fresh_bool("d");
                fml = m.mk_implies(d, cls);
                update_model(d, cls);
                s().assert_expr(fml);
                m_defs.push_back(fml);
                
            }
            else {
                d = cls;
            }
            asum = mk_fresh_bool("a");
            fml = m.mk_implies(asum, b_i1);
            s().assert_expr(fml);
            m_defs.push_back(fml);
            fml = m.mk_implies(asum, cls);
            s().assert_expr(fml);
            m_defs.push_back(fml);
            new_assumption(asum, w);

            fml = m.mk_and(b_i1, cls);
            update_model(asum, fml);
        }
        fml = m.mk_or(cs.size(), cs.c_ptr());
        s().assert_expr(fml);
    }

    void update_assignment(model* mdl) {
        unsigned correction_set_size = 0;
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            if (is_false(mdl, m_asms[i].get())) {
                ++correction_set_size;
            }
        }
        if (!m_csmodel.get() || correction_set_size < m_correction_set_size) {
            m_csmodel = mdl;
            m_correction_set_size = correction_set_size;
        }

        rational upper(0);
        expr_ref tmp(m);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            if (!is_true(mdl, m_soft[i])) {
                upper += m_weights[i];
            }
        }

        if (upper > m_upper) {
            return;
        }

        if (!m_c.verify_model(m_index, mdl, upper)) {
            return;
        }

        m_model = mdl;
        m_c.model_updated(mdl);

        TRACE("opt", model_smt2_pp(tout << "updated model\n", m, *m_model, 0););

        for (unsigned i = 0; i < m_soft.size(); ++i) {
            m_assignment[i] = is_true(m_soft[i]);
        }
       
        // DEBUG_CODE(verify_assignment(););

        m_upper = upper;
        trace();

        add_upper_bound_block();

    }

    void add_upper_bound_block() {
        if (!m_add_upper_bound_block) return;
        pb_util u(m);
        expr_ref_vector nsoft(m);
        expr_ref fml(m);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            nsoft.push_back(mk_not(m, m_soft[i]));
        }            
        fml = u.mk_lt(nsoft.size(), m_weights.c_ptr(), nsoft.c_ptr(), m_upper);
        TRACE("opt", tout << "block upper bound " << fml << "\n";);;
        s().assert_expr(fml); 
    }

    bool is_true(model* mdl, expr* e) {
        expr_ref tmp(m);
        return mdl->eval(e, tmp, true) && m.is_true(tmp);
    }

    bool is_false(model* mdl, expr* e) {
        expr_ref tmp(m);
        return mdl->eval(e, tmp, true) && m.is_false(tmp);
    }

    bool is_true(expr* e) {
        return is_true(m_model.get(), e);
    }

    bool is_true(expr_ref_vector const& es) {
        unsigned i = 0;
        for (; i < es.size() && is_true(es[i]); ++i) { }
        CTRACE("opt", i < es.size(), tout << mk_pp(es[i], m) << "\n";
               model_smt2_pp(tout, m, *m_model, 0);
               );
        return i == es.size();
    }

    void remove_soft(exprs const& core, expr_ref_vector& asms) {
        for (unsigned i = 0; i < asms.size(); ++i) {
            if (core.contains(asms[i].get())) {
                asms[i] = asms.back();
                asms.pop_back();
                --i;
            }
        }
    }

    void remove_core(exprs const& core) {
        remove_soft(core, m_asms);
    }

    virtual void updt_params(params_ref& p) {
        maxsmt_solver_base::updt_params(p);
        opt_params _p(p);
        m_hill_climb = _p.maxres_hill_climb();
        m_add_upper_bound_block = _p.maxres_add_upper_bound_block();
        m_max_num_cores = _p.maxres_max_num_cores();
        m_max_core_size = _p.maxres_max_core_size();
        m_maximize_assignment = _p.maxres_maximize_assignment();
        m_max_correction_set_size = _p.maxres_max_correction_set_size();
        m_pivot_on_cs = _p.maxres_pivot_on_correction_set();
        m_wmax = _p.maxres_wmax();
        m_dump_benchmarks = _p.dump_benchmarks();
    }

    lbool init_local() {
        m_lower.reset();
        m_trail.reset();
        lbool is_sat = l_true;
        obj_map<expr, rational> new_soft;
        is_sat = find_mutexes(new_soft);
        if (is_sat != l_true) {
            return is_sat;
        }
        obj_map<expr, rational>::iterator it = new_soft.begin(), end = new_soft.end();
        for (; it != end; ++it) {
            add_soft(it->m_key, it->m_value);
        }
        m_max_upper = m_upper;
        m_found_feasible_optimum = false;
        m_last_index = 0;
        add_upper_bound_block();
        m_csmodel = nullptr;
        m_correction_set_size = 0;
        return l_true;
    }

    virtual void commit_assignment() {
        if (m_found_feasible_optimum) {
            TRACE("opt", tout << "Committing feasible solution\n";
                  tout << m_defs;
                  tout << m_asms;
                  );
            s().assert_expr(m_defs);
            s().assert_expr(m_asms);
        }
        // else: there is only a single assignment to these soft constraints.
    }

    void verify_core(exprs const& core) {
        IF_VERBOSE(3, verbose_stream() << "verify core\n";);                
        ref<solver> smt_solver = mk_smt_solver(m, m_params, symbol());
        for (unsigned i = 0; i < s().get_num_assertions(); ++i) {
            smt_solver->assert_expr(s().get_assertion(i));
        }
        smt_solver->assert_expr(core);
        lbool is_sat = smt_solver->check_sat(0, nullptr);
        if (is_sat == l_true) {
            IF_VERBOSE(0, verbose_stream() << "not a core\n";);
        }        
    }

    void verify_assignment() {
        IF_VERBOSE(1, verbose_stream() << "verify assignment\n";);        
        ref<solver> smt_solver = mk_smt_solver(m, m_params, symbol());
        for (unsigned i = 0; i < s().get_num_assertions(); ++i) {
            smt_solver->assert_expr(s().get_assertion(i));
        }
        expr_ref n(m);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            n = m_soft[i];
            if (!m_assignment[i]) {
                n = mk_not(m, n);
            }
            smt_solver->assert_expr(n);
        }
        lbool is_sat = smt_solver->check_sat(0, nullptr);
        if (is_sat == l_false) {
            IF_VERBOSE(0, verbose_stream() << "assignment is infeasible\n";);
        }
        IF_VERBOSE(1, verbose_stream() << "verified\n";);        
    }
};

opt::maxsmt_solver_base* opt::mk_maxres(
    maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft) {
    return alloc(maxres, c, id, ws, soft, maxres::s_primal);
}

opt::maxsmt_solver_base* opt::mk_primal_dual_maxres(
    maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft) {
    return alloc(maxres, c, id, ws, soft, maxres::s_primal_dual);
}

