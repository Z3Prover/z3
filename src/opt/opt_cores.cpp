/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    opt_cores.cpp

Abstract:
   
    "walk" subsets of soft constraints to extract multiple cores and satisfying assignments.

    core rotation starts with an initial unsat core, which is a subset of soft constraints.
    Then it removes one element from the core from the soft constraints and finds remaining cores.
    At every stage it operates over a set of detected cores, and a subset of soft constraints have
    a hitting set from the cores removed.
    When enough constraints are removed, the remaining soft constraints become satisfiable.
    It then attempts extend the satisfying assignment by adding soft constraints removed in 
    the hitting set. In this process it detects new cores and may find assignments that improve
    the current feasible bound. As a final effort, it takes a maximal satisfying assignment and
    rotates out elements that belong to cores to explore a neighborhood for satisfying assignments
    that may potentially satisfy other soft constraints and potentially more of them.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-27

--*/

#include "solver/solver.h"
#include "opt/maxsmt.h"
#include "opt/opt_cores.h"
#include "opt/opt_params.hpp"

namespace opt {

    cores::cores(solver& s, lns_context& ctx):
        m(s.get_manager()), s(s), ctx(ctx) {}

    void cores::hitting_set(obj_hashtable<expr>& set) {
        for (auto const& [core, w] : m_cores) {
            bool seen = false;
            for (auto * c : core)
                seen |= set.contains(c);
            if (seen)
                continue;
            set.insert(core[m_rand(core.size())]);
        }
    }

    bool cores::improve() {
        model_ref mdl;
        s.get_model(mdl);
        rational cost = ctx.cost(*mdl);
        IF_VERBOSE(3, verbose_stream() << "(opt.maxcore new model cost " << cost << ")\n");
        if (m_best_cost < 0 || cost < m_best_cost) {            
            m_best_cost = cost;
            ctx.update_model(mdl);
            return true;
        }
        return false;
    }

    /**
     * retrieve cores that are disjoint modulo weights.
     * weighted soft constraints are treated as multi-sets.
     */
    vector<weighted_core> const& cores::disjoint_cores() {
        std::sort(m_cores.begin(), m_cores.end(), [&](weighted_core const& c1, weighted_core const& c2) { return c1.m_core.size() < c2.m_core.size(); });
        vector<weighted_core> result;
        for (auto const& [core, w] : m_cores) {
            rational weight = core_weight(core);
            if (weight == 0 && !core.empty())
                continue;
            for (auto *c : core) 
                m_weight[c] -= weight;
            result.push_back(weighted_core(core, weight));
        }
        IF_VERBOSE(3, verbose_stream() << "(opt.cores :cores-found " << m_cores.size() << " :disjoint-cores " << result.size() << ")\n");
        m_cores.reset();
        m_cores.append(result);
        return m_cores;
    }

    void cores::rotate_rec(obj_hashtable<expr> const& _mss, obj_map<expr, ptr_vector<expr>>& backbone2core, unsigned depth) {
        obj_map<expr, unsigned> counts;
        obj_hashtable<expr> mss(_mss);
        for (auto* f : mss)
            counts.insert(f, 0);
        for (auto const& [k, core] : backbone2core) 
            for (auto* c : core) 
                counts[c] += 1;
                    
        unsigned plateaus = 0;
        for (auto const& [c, count] : counts)
            if (count <= 1)
                ++plateaus;
        IF_VERBOSE(3, verbose_stream() << "(opt.maxcore :num-plateaus " << plateaus << "\n");

        for (auto const& [c, count] : counts) {
            if (count <= 1)
                continue;
            mss.remove(c);
            bool rotated = rotate(mss, c, depth + 1);
            mss.insert(c);
            if (rotated)
                break;
        }
    }

    /**
     * collect soft constraints that are not in the satisfying assignment mss into the set ps.
     * Try to add elements from ps in some order.
     * If an element can be added, (mss + p is sat), then mss is extended.
     * If mss + p is unsat, then extract core that includes p and a subset of mss
     * Then Not(p) is a backbone, and we maintain a map from Not(p) to the subset of mss used
     * in the core. Backbone literals are used in the satisfiability check.
     * For backbone literals that are used in other cores, resolve away Not(p) by the subset
     * of mss that comprised the core for p + mss.
     * The set qs accumulates don't knows. If a satisfiable assignment is found that satisfies
     * elements from qs, they are added to mss.
     */
    bool cores::rotate(obj_hashtable<expr> const& _mss, expr* excl, unsigned depth) {
        obj_hashtable<expr> ps, qs, mss(_mss);
        expr_ref_vector backbones(m);
        obj_map<expr, ptr_vector<expr>> backbone2core;
        bool improved = false;
        for (expr* f : ctx.soft())
            if (!mss.contains(f) && f != excl)
                ps.insert(f);
        while (!ps.empty() && m.inc() && m_cores.size() < m_max_num_cores) {
            expr* p = *ps.begin();
            ps.remove(p);
            expr_ref_vector asms(backbones);
            asms.push_back(p);
            for (expr* f : mss)
                asms.push_back(f);
            lbool is_sat = s.check_sat(asms);
            switch (is_sat) {
            case l_true: {
                model_ref mdl;
                s.get_model(mdl);
                ptr_vector<expr> moved;
                moved.push_back(p);
                for (auto* q : qs) 
                    if (mdl->is_true(q))
                        moved.push_back(q);

                for (auto* q : ps) 
                    if (mdl->is_true(q)) 
                        moved.push_back(q);

                for (auto* q : moved) {
                    mss.insert(q);
                    qs.remove(q);
                    ps.remove(q);
                }
                
                if (improve())
                    improved = true;
                break;
            }
            case l_false: {
                obj_hashtable<expr> core;
                for (auto* f : unsat_core()) {
                    ptr_vector<expr> core1;
                    if (backbone2core.find(f, core1))
                        for (expr* c : core1)
                            core.insert(c);
                    else
                        core.insert(f);
                }
                expr_ref_vector core1(m);
                for (expr* c : core)
                    core1.push_back(c);
                saturate_core(core1);
                add_core(core1);
                expr_ref not_p(m.mk_not(p), m);
                backbones.push_back(not_p);
                ptr_vector<expr> core2(core1.size(), core1.data());
                core2.erase(p);
                backbone2core.insert(not_p, core2);
                break;
            }                
            default:
                qs.insert(p);
                break;
            }
        }
        if (improved)
            rotate_rec(mss, backbone2core, depth);
        return improved;
    }

    struct cores::scoped_update {
        cores& c;
        char const* par;
        bool     is_uint = true;
        unsigned old_uval;
        bool     old_bval;
    public:
        scoped_update(cores& c, char const* par, unsigned old_val, unsigned new_val):
            c(c), par(par), old_uval(old_val) {
            params_ref p;        
            p.set_uint(par, new_val);
            c.s.updt_params(p);
        }

        scoped_update(cores& c, char const* par, bool old_val, bool new_val):
            c(c), par(par), old_bval(old_val) {
            is_uint = false;
            params_ref p;        
            p.set_bool(par, new_val);
            c.s.updt_params(p);
        }

        ~scoped_update() {            
            params_ref p;
            if (is_uint)
                p.set_uint(par, old_uval);
            else
                p.set_bool(par, old_bval);
            c.s.updt_params(p);
        }
    };

    void cores::saturate_core(expr_ref_vector& core) {
        scoped_update _upd(*this, "max_conflicts", m_max_conflicts, m_max_saturate_conflicts);
        shuffle(core.size(), core.data(), m_rand);
        while (l_false == s.check_sat(core) && unsat_core().size() < core.size()) {
            core.reset();
            core.append(unsat_core());
            shuffle(core.size(), core.data(), m_rand);
        }
    }

    void cores::local_mss() {
        obj_hashtable<expr> mss;
        model_ref mdl;
        s.get_model(mdl);
        for (expr* f : ctx.soft()) 
            if (mdl->is_true(f))
                mss.insert(f);
        rotate(mss, nullptr, 0);
    }

    expr_ref_vector cores::unsat_core() {
        expr_ref_vector core(m);
        s.get_unsat_core(core);
        return core;
    }

    /**
     * The solver state is unsatisfiable when this function is called.
     * Erase one element from each code that is found
     */
    void cores::rotate_cores() {
        expr_ref_vector soft(m);
        soft.append(ctx.soft());
        unsigned num_sat = 0, num_undef = 0;        
        lbool is_sat = l_false;
        while (m.inc() && m_cores.size() < m_max_num_cores) {
            switch (is_sat) {
            case l_false: {
                auto core = unsat_core();
                add_core(core);
                if (core.empty())
                    return;
                soft.erase(core.get(m_rand(core.size())));
                num_sat = 0;
                break;                
            }
            case l_true: {
                ++num_sat;
                improve();
                local_mss();
                if (num_sat > 1) 
                    return;
                soft.reset();
                obj_hashtable<expr> hs;
                hitting_set(hs);
                for (auto s : ctx.soft())
                    if (!hs.contains(s))
                        soft.push_back(s);
                break;
            }
            case l_undef:
                ++num_undef;
                if (num_undef > 2)
                    return;
            }
            is_sat = s.check_sat(soft);
        }        
    }

    rational cores::core_weight(unsigned sz, expr* const* core) {
        if (sz == 0)
            return rational(0);
        rational min_weight = m_weight[core[0]];
        for (unsigned i = 1; i < sz; ++i) {
            auto* c = core[i];
            if (m_weight[c] < min_weight)
                min_weight = m_weight[c];
        }
        return min_weight;
    }


    vector<weighted_core> const& cores::weighted_disjoint_cores() {
        lbool is_sat = l_false;
        expr_ref_vector soft = ctx.soft();
        
        while (is_sat == l_false && m.inc()) {
            auto core = unsat_core();
            saturate_core(core);
            rational weight = core_weight(core);
            add_core(core);
            if (core.empty()) {
                IF_VERBOSE(100, verbose_stream() << "(opt.maxres :empty-core)\n";);
                TRACE("opt", tout << "empty core\n";);
                break;
            }

            for (auto *c : core) {
                m_weight[c] -= weight;
                if (m_weight[c] == 0)
                    soft.erase(c);
            }

            if (core.size()  >= m_max_core_size)
                break;
            
            if (m_cores.size() >= m_max_num_cores)
                break;

            if (m_hill_climb)
                is_sat = check_sat_hill_climb(soft);
            else
                is_sat = s.check_sat(soft);
        }
        return m_cores;
    }

    /**
     * Give preference to cores that have large minimal values.
     * Explore largest values, and grow the set of explored values by at least 5% 
     * of all soft constraints in iterations (capping maximal iterations at 20).
     */
    lbool cores::check_sat_hill_climb(expr_ref_vector const& _soft) {
        expr_ref_vector soft(_soft);
        lbool is_sat = l_true;
        std::sort(soft.data(), soft.data() + soft.size(), [&](expr* a, expr* b) { return m_weight[a] > m_weight[b]; });
        unsigned index = 0, last_index = 0;
        SASSERT(index < soft.size() || soft.empty());
        IF_VERBOSE(10, verbose_stream() << "start hill climb " << index << " soft: " << soft.size() << "\n";);
        while (index < soft.size() && is_sat == l_true) {
            while (soft.size() > 20*(index - last_index) && index < soft.size()) {
                rational w = m_weight[_soft[index]];
                for (++index; index < soft.size() && w == m_weight[_soft[index]]; ++index); 
            }
            last_index = index;
            is_sat = s.check_sat(index, soft.data());
        }            
        return is_sat;
    }

    void cores::add_core(expr_ref_vector const& core) {
        IF_VERBOSE(3, verbose_stream() << "(opt.maxcore :core-size " << core.size() << ")\n");
        m_cores.push_back(weighted_core(ptr_vector<expr>(core.size(), core.data()), core_weight(core)));
    }

    void cores::updt_params(params_ref& _p) {
        opt_params p(_p);
        m_hill_climb =         p.maxres_hill_climb();
        m_max_num_cores =      p.maxres_max_num_cores();
        m_max_core_size =      p.maxres_max_core_size();
        m_enable_core_rotate = p.enable_core_rotate();        
    }
    
    vector<weighted_core> const& cores::operator()() {
        scoped_update _upd1(*this, "max_conflicts", UINT_MAX, m_max_conflicts);
        m_cores.reset();
        m_weight.reset();
        m_best_cost = -1;
        for (expr* s : ctx.soft())
            m_weight.insert(s, ctx.weight(s));

        if (m_enable_core_rotate) {
            scoped_update _upd2(*this, "minimize_core", false, false);
            rotate_cores();
            return disjoint_cores();
        }
        else {
            return weighted_disjoint_cores();
        }
    }

};
