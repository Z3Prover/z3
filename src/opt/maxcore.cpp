/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxcore.cpp

Abstract:

    Core based (weighted) max-sat algorithms:

    - mu:         max-sat algorithm by Nina and Bacchus, AAAI 2014.
    - mus-mss:    based on dual refinement of bounds.
    - binary:     binary version of maxres
    - rc2:        implementation of rc2 heuristic using cardinality constraints
    - rc2t:       implementation of rc2 heuristic using totalizerx
    - rc2-binary: hybrid of rc2 and binary maxres. Perform one step of binary maxres. 
                  If there are more than 16 soft constraints create a cardinality constraint.


    MaxRes is a core-guided approach to maxsat.
    MusMssMaxRes extends the core-guided approach by
    leveraging both cores and satisfying assignments
    to make progress towards a maximal satisfying assignment.

    Given a (minimal) unsatisfiable core for the soft
    constraints the approach works like max-res.
    Given a (maximal) satisfying subset of the soft constraints
    the approach updates the upper bound if the current assignment
    improves the current best assignment.
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
       In summary: any assignment to the new clauses that satisfies F has the
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
#include "ast/ast_smt_pp.h"
#include "model/model_smt2_pp.h"
#include "solver/solver.h"
#include "solver/mus.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "smt/smt_solver.h"
#include "opt/opt_context.h"
#include "opt/opt_params.hpp"
#include "opt/opt_lns.h"
#include "opt/opt_cores.h"
#include "opt/maxsmt.h"
#include "opt/maxcore.h"
#include "opt/totalizer.h"
#include <iostream>

using namespace opt;

class maxcore : public maxsmt_solver_base {
public:
    enum strategy_t {
        s_primal,
        s_primal_dual,
        s_primal_binary,
        s_rc2,
        s_primal_binary_rc2
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

    struct lns_maxcore : public lns_context {
        maxcore& i;
        lns_maxcore(maxcore& i) :i(i) {}
        void update_model(model_ref& mdl) override { i.update_assignment(mdl); }
        void relax_cores(vector<expr_ref_vector> const& cores) override { i.relax_cores(cores); }
        rational cost(model& mdl) override { return i.cost(mdl); }
        rational weight(expr* e) override { return i.m_asm2weight[e]; }
        expr_ref_vector const& soft() override { return i.m_asms; }
    };

    stats            m_stats;
    expr_ref_vector  m_B;
    expr_ref_vector  m_asms;
    expr_ref_vector  m_defs;
    obj_map<expr, rational> m_asm2weight;
    expr_ref_vector  m_new_core;
    mus              m_mus;
    expr_ref_vector  m_trail;
    strategy_t       m_st;
    rational         m_max_upper;
    model_ref        m_csmodel;
    lns_maxcore      m_lnsctx;
    lns              m_lns;
    unsigned         m_correction_set_size = 0;
    bool             m_found_feasible_optimum = false;
    bool             m_hill_climb = true;              // prefer large weight soft clauses for cores
    bool             m_add_upper_bound_block = false;  // restrict upper bound with constraint
    unsigned         m_max_core_size = 3;              // max core size per round.
    bool             m_maximize_assignment = false;    // maximize assignment to find MCS
    unsigned         m_max_correction_set_size = 3;    // maximal set of correction set that is tolerated.
    bool             m_wmax = false;                   // Block upper bound using wmax
                                                       // this option is disabled if SAT core is used.
    bool             m_pivot_on_cs = true;             // prefer smaller correction set to core.
    bool             m_dump_benchmarks;                // display benchmarks (into wcnf format)
    bool             m_enable_lns = false;             // enable LNS improvements
    unsigned         m_lns_conflicts = 1000;           // number of conflicts used for LNS improvement
    bool             m_enable_core_rotate = false;     // enable core rotation
    bool             m_use_totalizer = true;           // use totalizer instead of cardinality encoding
    std::string      m_trace_id;
    typedef ptr_vector<expr> exprs;

public:
    maxcore(maxsat_context& c, unsigned index,
           vector<soft>& soft,
           strategy_t st):
        maxsmt_solver_base(c, soft, index),
        m_B(m), m_asms(m), m_defs(m),
        m_new_core(m),
        m_mus(c.get_solver()),
        m_trail(m),
        m_st(st),
        m_lnsctx(*this),
        m_lns(s(), m_lnsctx)
    {
        switch(st) {
        case s_primal:
            m_trace_id = "maxres";
            break;
        case s_primal_dual:
            m_trace_id = "pd-maxres";
            break;
        case s_primal_binary:
            m_trace_id = "maxres-bin";
            break;
        case s_rc2:
            m_trace_id = "rc2";
            break;
        case s_primal_binary_rc2:
            m_trace_id = "rc2bin";
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    ~maxcore() override {
        for (auto& [k,t] : m_totalizers)
            dealloc(t);        
    }

    bool is_literal(expr* l) {
        return
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }

    void add(expr_ref_vector const& es) {
        for (expr* e : es) add(e);
    }

    void add(expr* e) {
        s().assert_expr(e);
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
            m_defs.push_back(fml);
            add(fml);
        }
        new_assumption(asum, w);
    }

    void new_assumption(expr* e, rational const& w) {
        IF_VERBOSE(13, verbose_stream() << "new assumption " << mk_pp(e, m) << " " << w << "\n";);
        m_asm2weight.insert(e, w);
        m_asms.push_back(e);
        m_trail.push_back(e);
        TRACE("opt", tout << "insert: " << mk_pp(e, m) << " : " << w << "\n";
              tout << m_asms << " " << "\n"; );
    }

    void trace() {
        trace_bounds(m_trace_id.c_str());
    }

    lbool mus_solver() {
        lbool is_sat = l_true;
        if (!init()) return l_undef;
        is_sat = init_local();
        trace();
        improve_model();
        if (is_sat != l_true) return is_sat;
        while (m_lower < m_upper) {
            TRACE("opt_verbose",
                  s().display(tout << m_asms << "\n") << "\n";
                  display(tout););
            is_sat = check_sat_hill_climb(m_asms);
            if (!m.inc()) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true:
                CTRACE("opt", m_model->is_false(m_asms),
                       tout << *m_model << "assumptions: ";
                       for (expr* a : m_asms) tout << mk_pp(a, m) << " -> " << (*m_model)(a) << " ";
                       tout << "\n";);
                SASSERT(!m_model->is_false(m_asms) || m.limit().is_canceled());
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
            if (!m.inc()) {
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
               Give preference to cores that have large minimal values.
            */
            sort_assumptions(asms);
            unsigned last_index = 0;
            unsigned index = 0;
            SASSERT(index < asms.size() || asms.empty());
            IF_VERBOSE(10, verbose_stream() << "start hill climb " << index << " asms: " << asms.size() << "\n";);
            while (index < asms.size() && is_sat == l_true) {
                while (asms.size() > 20*(index - last_index) && index < asms.size()) {
                    index = next_index(asms, index);
                }
                last_index = index;
                is_sat = check_sat(index, asms.data());
            }
        }
        else {
            is_sat = check_sat(asms.size(), asms.data());
        }
        return is_sat;
    }

    lbool check_sat(unsigned sz, expr* const* asms) {
        lbool r = s().check_sat(sz, asms);
        if (r == l_true) {
            model_ref mdl;
            s().get_model(mdl);
            TRACE("opt", tout << *mdl;);
            if (mdl.get()) {
                update_assignment(mdl);
            }
        }
        return r;
    }

    void found_optimum() {
        IF_VERBOSE(1, verbose_stream() << "found optimum\n";);
        verify_assumptions();
        m_lower.reset();
        for (soft& s : m_soft) {
            s.set_value(m_model->is_true(s.s));
            if (!s.is_true()) {
                m_lower += s.weight;
            }
        }
        m_upper = m_lower;
        m_found_feasible_optimum = true;
    }


    lbool operator()() override {
        m_defs.reset();
        switch(m_st) {
        case s_primal:
        case s_primal_binary:
        case s_rc2:
        case s_primal_binary_rc2:
            return mus_solver();
        case s_primal_dual:
            return primal_dual_solver();
        }
        return l_undef;
    }

    void collect_statistics(statistics& st) const override {
        st.update("maxsat-cores", m_stats.m_num_cores);
        st.update("maxsat-correction-sets", m_stats.m_num_cs);
    }

    lbool get_cores(vector<weighted_core>& cores) {
        // assume m_s is unsat.
        lbool is_sat = l_false;
        cores.reset();
        exprs core;
        while (is_sat == l_false) {
            core.reset();
            expr_ref_vector _core(m);
            s().get_unsat_core(_core);
            model_ref mdl;
            get_mus_model(mdl);
            is_sat = minimize_core(_core);
            core.append(_core.size(), _core.data());
            DEBUG_CODE(verify_core(core););
            ++m_stats.m_num_cores;
            if (is_sat != l_true) {
                IF_VERBOSE(100, verbose_stream() << "(opt.maxres minimization failed)\n";);
                break;
            }
            if (core.empty()) {
                IF_VERBOSE(100, verbose_stream() << "(opt.maxres core is empty)\n";);
                TRACE("opt", tout << "empty core\n";);
                cores.reset();
                m_lower = m_upper;
                return l_true;
            }


            // 1. remove all core literals from m_asms
            // 2. re-add literals of higher weight than min-weight.
            // 3. 'core' stores the core literals that are
            //    re-encoded as assumptions, afterwards
            cores.push_back(weighted_core(core, core_weight(core)));

            remove_soft(core, m_asms);
            split_core(core);

            if (core.size() >= m_max_core_size)
                break;

            is_sat = check_sat_hill_climb(m_asms);
        }

        TRACE("opt",
              tout << "sat: " << is_sat << " num cores: " << cores.size() << "\n";
              for (auto const& c : cores) display_vec(tout, c.m_core);
              tout << "num assumptions: " << m_asms.size() << "\n";);

        return is_sat;
    }

    void get_current_correction_set(exprs& cs) {
        model_ref mdl;
        s().get_model(mdl);
        update_assignment(mdl);
        get_current_correction_set(mdl.get(), cs);
    }

    void get_current_correction_set(model* mdl, exprs& cs) {
        cs.reset();
        if (!mdl) return;
        for (expr* a : m_asms) {
            if (mdl->is_false(a)) {
                cs.push_back(a);
            }
        }
        TRACE("opt", display_vec(tout << "new correction set: ", cs););
    }

    struct compare_asm {
        maxcore& mr;
        compare_asm(maxcore& mr):mr(mr) {}
        bool operator()(expr* a, expr* b) const {
            rational w1 = mr.get_weight(a);
            rational w2 = mr.get_weight(b);
            return w1 > w2 || (w1 == w2 && a->get_id() > b->get_id());
        }
    };

    void sort_assumptions(expr_ref_vector& _asms) {
        compare_asm comp(*this);
        exprs asms(_asms.size(), _asms.data());
        expr_ref_vector trail(_asms);
        std::sort(asms.begin(), asms.end(), comp);
        _asms.reset();
        _asms.append(asms.size(), asms.data());
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
        remove_soft(corr_set, m_asms);
        rational w = split_core(corr_set);
        cs_max_resolve(corr_set, w);
        IF_VERBOSE(2, verbose_stream() << "(opt.maxres.correction-set " << corr_set.size() << ")\n";);
        m_csmodel = nullptr;
        m_correction_set_size = 0;
    }

    lbool process_unsat() {
        if (m_enable_core_rotate)
            return core_rotate();

        vector<weighted_core> cores;
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

    lbool core_rotate() {
        cores find_cores(s(), m_lnsctx);
        find_cores.updt_params(m_params);
        vector<weighted_core> const& cores = find_cores();
        for (auto const & [core, w] : cores) {
            if (core.empty())
                return l_false;
            ++m_stats.m_num_cores;
            remove_soft(core, m_asms);
            split_core(core);
            process_unsat(core, w);
        }
        return l_true;
    }


    unsigned max_core_size(vector<exprs> const& cores) {
        unsigned result = 0;
        for (auto const& c : cores)
            result = std::max(c.size(), result);
        return result;
    }

    void process_unsat(vector<weighted_core> const& cores) {
        for (auto const & c : cores)
            process_unsat(c.m_core, c.m_weight);
        improve_model(m_model);
    }

    void update_model(expr* def, expr* value) {
        SASSERT(is_uninterp_const(def));
        if (m_csmodel)
            m_csmodel->register_decl(to_app(def)->get_decl(), (*m_csmodel)(value));
        if (m_model)
            m_model->register_decl(to_app(def)->get_decl(), (*m_model)(value));
    }

    void process_unsat(exprs const& core, rational w) {
        IF_VERBOSE(3, verbose_stream() << "(maxres cs model valid: " << (m_csmodel.get() != nullptr) << " cs size:" << m_correction_set_size << " core: " << core.size() << ")\n";);
        expr_ref fml(m);
        SASSERT(!core.empty());
        TRACE("opt", display_vec(tout << "minimized core: ", core););
        IF_VERBOSE(10, display_vec(verbose_stream() << "core: ", core););
        switch (m_st) {
        case strategy_t::s_primal_binary:
            bin_max_resolve(core, w);
            break;
        case strategy_t::s_rc2:
            max_resolve_rc2(core, w);
            break;
        case strategy_t::s_primal_binary_rc2:
            max_resolve_rc2bin(core, w);
            break;
        default:
            max_resolve(core, w);
            break;
        }
        fml = mk_not(m, mk_and(m, core.size(), core.data()));
        add(fml);
        // save small cores such that lex-combinations of maxres can reuse these cores.
        if (core.size() <= 2) {
            m_defs.push_back(fml);
        }
        m_lower += w;
        if (m_st == s_primal_dual) {
            m_lower = std::min(m_lower, m_upper);
        }
        if (m_csmodel.get() && m_correction_set_size > 0) {
            // this estimate can overshoot for weighted soft constraints.
            --m_correction_set_size;
        }
        trace();
        bool no_hidden_soft = (m_st == s_primal_dual || m_st == s_primal || m_st == s_primal_binary);
        if (no_hidden_soft && m_c.num_objectives() == 1 && m_pivot_on_cs && m_csmodel.get() && m_correction_set_size < core.size()) {
            exprs cs;
            get_current_correction_set(m_csmodel.get(), cs);
            m_correction_set_size = cs.size();
            TRACE("opt", tout << "cs " << m_correction_set_size << " " << core.size() << "\n";);
            if (m_correction_set_size >= core.size())
                return;
            rational w(0);
            for (expr* a : m_asms) {
                rational w1 = m_asm2weight[a];
                if (w != 0 && w1 != w) return;
                w = w1;
            }
            process_sat(cs);
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
        if (mdl.get() && w < m_upper)
            update_assignment(mdl);
        return nullptr != mdl.get();
    }

    lbool minimize_core(expr_ref_vector& core) {
        if (core.empty())
            return l_true;
        if (m_c.sat_enabled())
            return l_true;
        m_mus.reset();
        m_mus.add_soft(core.size(), core.data());
        lbool is_sat = m_mus.get_mus(m_new_core);
        if (is_sat != l_true)
            return is_sat;
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
        for (unsigned i = 1; i < core.size(); ++i)
            w = std::min(w, get_weight(core[i]));
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
        display_vec(out, exprs.size(), exprs.data());
    }

    void display_vec(std::ostream& out, expr_ref_vector const& exprs) {
        display_vec(out, exprs.size(), exprs.data());
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) const {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " : " << get_weight(args[i]) << " ";
        }
        out << "\n";
    }

    void display(std::ostream& out) {
        for (expr * a : m_asms)
            out << mk_pp(a, m) << " : " << get_weight(a) << "\n";
    }


    void max_resolve(exprs const& core, rational const& w) {
        SASSERT(!core.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(core.size(), core.data());
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
                add(fml);
                m_defs.push_back(fml);
                fml = m.mk_implies(dd, b_i);
                add(fml);
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
            add(fml);
            m_defs.push_back(fml);
        }
    }
    
    void bin_resolve(exprs const& _core, rational weight, expr_ref_vector& us) {
        expr_ref_vector core(m, _core.size(), _core.data()), fmls(m);
        expr_ref fml(m), cls(m);
        for (unsigned i = 0; i + 1 < core.size(); i += 2) {
            expr* a = core.get(i);
            expr* b = core.get(i + 1);
            expr* u = mk_fresh_bool("u");
            expr* v = mk_fresh_bool("v");
            // u = a or b
            // v = a and b
            cls = m.mk_or(a, b);
            fml = m.mk_implies(u, cls);
            add(fml);
            update_model(u, cls);
            m_defs.push_back(fml);
            cls = m.mk_and(a, b);
            fml = m.mk_implies(v, cls);
            add(fml);
            update_model(v, cls);
            m_defs.push_back(fml);
            us.push_back(u);
            core.push_back(v);
        }
        s().assert_expr(m.mk_not(core.back()));        
    }

    void bin_max_resolve(exprs const& _core, rational w) {
        expr_ref_vector core(m, _core.size(), _core.data()), us(m);
        expr_ref fml(m), cls(m);
        bin_resolve(_core, w, us);
        for (expr* u : us)
            new_assumption(u, w);
    }


    // rc2, using cardinality constraints

    // create and cache at-most k constraints
    struct bound_info {
        ptr_vector<expr> es;
        unsigned         k = 0;
        rational         weight;
        bound_info() = default;
        bound_info(ptr_vector<expr> const& es, unsigned k, rational const& weight):
            es(es), k(k), weight(weight) {}
        bound_info(expr_ref_vector const& es, unsigned k, rational const& weight):
            es(es.size(), es.data()), k(k), weight(weight) {}
    };

    obj_map<expr, expr*>      m_at_mostk;
    obj_map<expr, bound_info> m_bounds;
    rational                  m_unfold_upper;
    obj_map<expr, totalizer*> m_totalizers;

    expr* mk_atmost_tot(expr_ref_vector const& es, unsigned bound, rational const& weight) {
        pb_util pb(m);
        expr_ref am(pb.mk_at_most_k(es, 0), m);
        totalizer* t = nullptr;        
        if (!m_totalizers.find(am, t)) {
            m_trail.push_back(am);
            t = alloc(totalizer, es);
            m_totalizers.insert(am, t);
        }
        expr* at_least = t->at_least(bound + 1);
        am = m.mk_not(at_least);
        m_trail.push_back(am);
        expr_ref_vector& clauses = t->clauses();
        for (auto & clause : clauses) {
            add(clause);
            m_defs.push_back(clause);
        }
        clauses.reset();
        auto& defs = t->defs();
        for (auto & [v, d] : defs) 
            update_model(v, d);
        defs.reset();
        bound_info b(es, bound, weight);
        m_bounds.insert(am, b);
        return am;
    }

    expr* mk_atmost(expr_ref_vector const& es, unsigned bound, rational const& weight) {
        if (m_use_totalizer)
            return mk_atmost_tot(es, bound, weight);
        pb_util pb(m);
        expr_ref am(pb.mk_at_most_k(es, bound), m);
        expr* r = nullptr;
        if (m_at_mostk.find(am, r))
            return r;
        r = mk_fresh_bool("r");
        m_trail.push_back(am);
        bound_info b(es, bound, weight);
        m_at_mostk.insert(am, r);
        m_bounds.insert(r, b);
        expr_ref fml(m);
        fml = m.mk_implies(r, am);
        add(fml);
        m_defs.push_back(fml);
        update_model(r, am);
        return r;
    }

    void weaken_bounds(exprs const& core) {
        for (expr* f : core) {
            bound_info b;
            if (!m_bounds.find(f, b))
                continue;
            m_bounds.remove(f);
            if (b.k + 1 >= b.es.size())
                continue;
            expr_ref_vector es(m, b.es.size(), b.es.data());
            expr* amk = mk_atmost(es, b.k + 1, b.weight);
            new_assumption(amk, b.weight);
            m_unfold_upper -= b.weight;
        }
    }

    void max_resolve_rc2(exprs const& core, rational weight) {
        expr_ref_vector ncore(m);
        for (expr* f : core) 
            ncore.push_back(mk_not(m, f));

        weaken_bounds(core);

        if (core.size() > 1) {
            m_unfold_upper += rational(core.size() - 2) * weight;
            expr* am = mk_atmost(ncore, 1, weight);
            new_assumption(am, weight);
        }
    }

    /** 
     * \brief hybrid of rc2 and binary resolution.
     * Create us := u1, .., u_n, where core has size n + 1
     * If the core is of size at most 16 just use us as soft constraints
     * Otherwise introduce a single soft constraint, the conjunction of us.
     */

    void max_resolve_rc2bin(exprs const& core, rational weight) {
        weaken_bounds(core);
        expr_ref_vector us(m);
        bin_resolve(core, weight, us);        
        if (us.size() <= 15) {
            for (auto* u : us)
                new_assumption(u, weight);
        }
        else if (us.size() > 15) {
            expr_ref_vector ncore(m);
            for (expr* f : us) 
                ncore.push_back(mk_not(m, f));
            m_unfold_upper += rational(us.size() - 1) * weight;
            expr* am = mk_atmost(ncore, 0, weight);
            new_assumption(am, weight);
        }            
    }


    // cs is a correction set (a complement of a (maximal) satisfying assignment).
    void cs_max_resolve(exprs const& cs, rational const& w) {
        if (cs.empty()) return;
        TRACE("opt", display_vec(tout << "correction set: ", cs););
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m), dd(m);
        m_B.reset();
        m_B.append(cs.size(), cs.data());
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
                add(fml);
                m_defs.push_back(fml);
            }
            else {
                d = cls;
            }
            asum = mk_fresh_bool("a");
            fml = m.mk_implies(asum, b_i1);
            add(fml);
            m_defs.push_back(fml);
            fml = m.mk_implies(asum, cls);
            add(fml);
            m_defs.push_back(fml);
            new_assumption(asum, w);

            fml = m.mk_and(b_i1, cls);
            update_model(asum, fml);
        }
        fml = m.mk_or(cs);
        add(fml);
    }

    void improve_model() {
        if (!m_enable_lns)
            return;
        model_ref mdl;
        s().get_model(mdl);
        if (mdl)
            update_assignment(mdl);
    }



    void improve_model(model_ref& mdl) {
        if (!m_enable_lns)
            return;
        flet<bool> _disable_lns(m_enable_lns, false);
        m_lns.climb(mdl);
    }

    void relax_cores(vector<expr_ref_vector> const& cores) {
        vector<weighted_core> wcores;
        for (auto & core : cores) {
            exprs _core(core.size(), core.data());
            wcores.push_back(weighted_core(_core, core_weight(_core)));
            remove_soft(_core, m_asms);
            split_core(_core);
        }
        process_unsat(wcores);
    }

    rational cost(model& mdl) {
        rational upper = m_unfold_upper;
        for (soft& s : m_soft)
            if (!mdl.is_true(s.s))
                upper += s.weight;
        return upper;
    }

    void update_assignment(model_ref & mdl) {
        improve_model(mdl);
        mdl->set_model_completion(true);
        unsigned correction_set_size = 0;
        for (expr* a : m_asms)
            if (mdl->is_false(a))
                ++correction_set_size;

        if (!m_csmodel.get() || correction_set_size < m_correction_set_size) {
            m_csmodel = mdl;
            m_correction_set_size = correction_set_size;
        }

        TRACE("opt_verbose", tout << *mdl;);

        rational upper = cost(*mdl);

        if (upper > m_upper) {
            TRACE("opt", tout << "new upper: " << upper << " vs existing upper: " << m_upper << "\n";);
            return;
        }

        if (!m_c.verify_model(m_index, mdl.get(), upper))
            return;

        unsigned num_assertions = s().get_num_assertions();
        m_model = mdl;
        m_c.model_updated(mdl.get());

        TRACE("opt", tout << "updated upper: " << upper << "\n";);

        for (soft& s : m_soft)
            s.set_value(m_model->is_true(s.s));

        verify_assignment();

        if (num_assertions == s().get_num_assertions())
            m_upper = upper;

        trace();

        add_upper_bound_block();
    }

    void add_upper_bound_block() {
        if (!m_add_upper_bound_block) return;
        pb_util u(m);
        expr_ref_vector nsoft(m);
        vector<rational> weights;
        expr_ref fml(m);
        for (soft& s : m_soft) {
            nsoft.push_back(mk_not(m, s.s));
            weights.push_back(s.weight);
        }
        fml = u.mk_lt(nsoft.size(), weights.data(), nsoft.data(), m_upper);
        TRACE("opt", tout << "block upper bound " << fml << "\n";);;
        add(fml);
    }

    void remove_soft(exprs const& core, expr_ref_vector& asms) {
        TRACE("opt", tout << "before remove: " << asms << "\n";);
        unsigned j = 0;
        for (expr* a : asms)
            if (!core.contains(a))
                asms[j++] = a;
        asms.shrink(j);
        TRACE("opt", tout << "after remove: " << asms << "\n";);
    }

    void updt_params(params_ref& _p) override {
        maxsmt_solver_base::updt_params(_p);
        opt_params p(_p);
        m_hill_climb =              p.maxres_hill_climb();
        m_add_upper_bound_block =   p.maxres_add_upper_bound_block();
        m_max_core_size =           p.maxres_max_core_size();
        m_maximize_assignment =     p.maxres_maximize_assignment();
        m_max_correction_set_size = p.maxres_max_correction_set_size();
        m_pivot_on_cs =             p.maxres_pivot_on_correction_set();
        m_wmax =                    p.maxres_wmax();
        m_dump_benchmarks =         p.dump_benchmarks();
        m_enable_lns =              p.enable_lns();
        m_enable_core_rotate =      p.enable_core_rotate();
        m_lns_conflicts =           p.lns_conflicts();
        m_use_totalizer =           p.rc2_totalizer();
	if (m_c.num_objectives() > 1)
	  m_add_upper_bound_block = false;
    }

    lbool init_local() {
        m_trail.reset();
        for (auto const& [e, w, t] : m_soft)
            add_soft(e, w);
        m_max_upper = m_upper;
        m_found_feasible_optimum = false;
        add_upper_bound_block();
        m_csmodel = nullptr;
        m_correction_set_size = 0;
        m_unfold_upper = 0;
        m_at_mostk.reset();
        m_bounds.reset();
        for (auto& [k,t] : m_totalizers)
            dealloc(t);
        m_totalizers.reset();
        return l_true;
    }

    void commit_assignment() override {
        if (m_found_feasible_optimum) {
            add(m_defs);
            add(m_asms);
            TRACE("opt", tout << "Committing feasible solution\ndefs:" << m_defs << "\nasms:" << m_asms << "\n");
        }
        // else: there is only a single assignment to these soft constraints.
    }

    void verify_core(exprs const& core) {
        return;
        IF_VERBOSE(1, verbose_stream() << "verify core " << s().check_sat(core.size(), core.data()) << "\n";);
        ref<solver> _solver = mk_smt_solver(m, m_params, symbol());
        _solver->assert_expr(s().get_assertions());
        _solver->assert_expr(core);
        lbool is_sat = _solver->check_sat(0, nullptr);
        IF_VERBOSE(0, verbose_stream() << "core status (l_false:) " << is_sat << " core size " << core.size() << "\n");
        CTRACE("opt", is_sat != l_false,
               for (expr* c : core) tout << "core: " << mk_pp(c, m) << "\n";
               _solver->display(tout);
               tout << "other solver\n";
               s().display(tout);
               );
        VERIFY(is_sat == l_false || !m.inc());
    }

    void verify_assumptions() {
        return;
        IF_VERBOSE(1, verbose_stream() << "verify assumptions\n";);
        ref<solver> _solver = mk_smt_solver(m, m_params, symbol());
        _solver->assert_expr(s().get_assertions());
        _solver->assert_expr(m_asms);
        lbool is_sat = _solver->check_sat(0, nullptr);
        IF_VERBOSE(1, verbose_stream() << "assignment status (l_true) " << is_sat << "\n";);
        VERIFY(is_sat == l_true);
    }

    void verify_assignment() {
        return;
        IF_VERBOSE(1, verbose_stream() << "verify assignment\n";);
        ref<solver> _solver = mk_smt_solver(m, m_params, symbol());
        _solver->assert_expr(s().get_assertions());
        expr_ref n(m);
        for (soft& s : m_soft) {
            n = s.s;
            if (!s.is_true()) {
                n = mk_not(m, n);
            }
            _solver->assert_expr(n);
        }
        lbool is_sat = _solver->check_sat(0, nullptr);
        IF_VERBOSE(1, verbose_stream() << "assignment status (l_true) " << is_sat << "\n");
        VERIFY(is_sat == l_true);
    }
};

opt::maxsmt_solver_base* opt::mk_maxres(
    maxsat_context& c, unsigned id, vector<soft>& soft) {
    return alloc(maxcore, c, id, soft, maxcore::s_primal);
}

opt::maxsmt_solver_base* opt::mk_rc2(
    maxsat_context& c, unsigned id, vector<soft>& soft) {
    return alloc(maxcore, c, id, soft, maxcore::s_rc2);
}


opt::maxsmt_solver_base* opt::mk_rc2bin(
    maxsat_context& c, unsigned id, vector<soft>& soft) {
    return alloc(maxcore, c, id, soft, maxcore::s_primal_binary_rc2);
}

opt::maxsmt_solver_base* opt::mk_maxres_binary(
    maxsat_context& c, unsigned id, vector<soft>& soft) {
    return alloc(maxcore, c, id, soft, maxcore::s_primal_binary);
}


opt::maxsmt_solver_base* opt::mk_primal_dual_maxres(
    maxsat_context& c, unsigned id, vector<soft>& soft) {
    return alloc(maxcore, c, id, soft, maxcore::s_primal_dual);
}


