/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    opt_preprocess.cpp

Abstract:
   
    Pre-processing for MaxSMT

    Find mutexes - at most 1 constraints and modify soft constraints and bounds.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-11


Notes:

   maxsat x, y, z, u . x + y + z <= 1 and F 
=>
   maxsst x or y or z, u . x + y + z <= 1 and F
   lower bound increased by 2

   maxsat x, y, z, u . x + y + z >= 2 and F 
=>
   maxsst x and y and z, u . x + y + z >= 2 and F
   lower bound decreased by 2

--*/


#include "opt/opt_preprocess.h"
#include "util/max_cliques.h"

namespace opt {

    expr_ref_vector preprocess::propagate(expr* f, lbool& is_sat) {
        expr_ref_vector asms(m);
        asms.push_back(f);
        is_sat = s.check_sat(asms);
        return s.get_trail(1);
    }

    bool preprocess::prop_mutexes(vector<soft>& softs, rational& lower) {
        expr_ref_vector fmls(m);
        obj_map<expr, rational> new_soft = soft2map(softs, fmls);

        params_ref p;
        p.set_uint("max_conflicts", 1);
        s.updt_params(p);

        obj_hashtable<expr> pfmls, nfmls;
        for (expr* f : fmls)
            if (m.is_not(f, f))
                nfmls.insert(f);
            else
                pfmls.insert(f);
        
        u_map<expr*> ids;
        unsigned_vector ps;
        for (expr* f : fmls) {
            ids.insert(f->get_id(), f);
            ps.push_back(f->get_id());
        }

        u_map<uint_set> conns;

        for (expr* f : fmls) {
            lbool is_sat;
            expr_ref_vector trail = propagate(f, is_sat);
            if (is_sat == l_false) {
                rational w = new_soft[f];
                lower += w;
                s.assert_expr(m.mk_not(f));
                new_soft.remove(f);
                continue;
            }
            if (!m.inc())
                return false;
                
            expr_ref_vector mux(m);
            for (expr* g : trail) {
                if (m.is_not(g, g)) {
                    if (pfmls.contains(g))
                        mux.push_back(g);
                }
                else if (nfmls.contains(g))
                    mux.push_back(m.mk_not(g));
            }
            uint_set reach;
            for (expr* g : mux)
                reach.insert(g->get_id());
            conns.insert(f->get_id(), reach);
        }
        
        p.set_uint("max_conflicts", UINT_MAX);
        s.updt_params(p);

        struct neg_literal {
            unsigned negate(unsigned id) {
                throw default_exception("unexpected call");
            }
        };
        max_cliques<neg_literal> mc;
        vector<unsigned_vector> mutexes;
        mc.cliques(ps, conns, mutexes);

        for (auto& mux : mutexes) {
            expr_ref_vector _mux(m);
            for (auto p : mux)
                _mux.push_back(ids[p]);
            process_mutex(_mux, new_soft, lower);
        }

        softs.reset();
        for (auto const& [k, v] : new_soft)
            softs.push_back(soft(expr_ref(k, m), v, false));
        m_trail.reset();
        return true;        
    }

    obj_map<expr, rational> preprocess::soft2map(vector<soft> const& softs, expr_ref_vector& fmls) {
        obj_map<expr, rational> new_soft;
        for (soft const& sf : softs) {
            m_trail.push_back(sf.s);
            if (new_soft.contains(sf.s))
                new_soft[sf.s] += sf.weight;
            else {
                new_soft.insert(sf.s, sf.weight);
                fmls.push_back(sf.s);
            }
        }
        return new_soft;
    }

    obj_map<expr, rational> preprocess::dualize(obj_map<expr, rational> const& soft, expr_ref_vector& fmls) {
        obj_map<expr, rational> new_soft;
        for (auto const& [k, v] : soft) {
            expr* nk = mk_not(m, k);
            m_trail.push_back(nk);
            new_soft.insert(nk, v);
        }
        unsigned i = 0;
        for (expr* f : fmls)
            fmls[i++] = mk_not(m, f);

        return new_soft;
    }

    bool preprocess::find_mutexes(vector<soft>& softs, rational& lower) {
        expr_ref_vector fmls(m);
        obj_map<expr, rational> new_soft = soft2map(softs, fmls);
        vector<expr_ref_vector> mutexes;
        lbool is_sat = s.find_mutexes(fmls, mutexes);
        if (is_sat == l_false)
            return true;
        if (is_sat == l_undef)
            return false;
        for (auto& mux : mutexes) 
            process_mutex(mux, new_soft, lower);

        if (mutexes.empty()) {
            obj_map<expr, rational> dual_soft = dualize(new_soft, fmls);
            mutexes.reset();
            lbool is_sat = s.find_mutexes(fmls, mutexes);
            if (is_sat == l_false)
                return true;
            if (is_sat == l_undef)
                return false;
            rational llower(0);
            for (auto& mux : mutexes) 
                process_mutex(mux, dual_soft, llower);
            if (dual_soft.size() != new_soft.size())
                new_soft = dualize(dual_soft, fmls);
        }
        
        softs.reset();
        for (auto const& [k, v] : new_soft)
            softs.push_back(soft(expr_ref(k, m), v, false));
        m_trail.reset();
        return true;
    }

    struct maxsmt_compare_soft {
        obj_map<expr, rational> const& m_soft;
        maxsmt_compare_soft(obj_map<expr, rational> const& soft): m_soft(soft) {}
        bool operator()(expr* a, expr* b) const {
            return m_soft.find(a) > m_soft.find(b);
        }
    };

    void preprocess::process_mutex(expr_ref_vector& mutex, obj_map<expr, rational>& new_soft, rational& lower) {
        TRACE("opt", 
              for (expr* e : mutex) {
                  tout << mk_pp(e, m) << " |-> " << new_soft.find(e) << "\n";
              });
        if (mutex.size() <= 1) 
            return;

        maxsmt_compare_soft cmp(new_soft);
        ptr_vector<expr> _mutex(mutex.size(), mutex.data());
        std::sort(_mutex.begin(), _mutex.end(), cmp);
        mutex.reset();
        mutex.append(_mutex.size(), _mutex.data());

        rational weight(0), sum1(0), sum2(0);
        vector<rational> weights;
        for (expr* e : mutex) {
            rational w = new_soft.find(e);
            weights.push_back(w);
            sum1 += w;
            new_soft.remove(e);
        }
        for (unsigned i = mutex.size(); i-- > 0; ) {
            expr_ref soft(m.mk_or(i+1, mutex.data()), m);
            m_trail.push_back(soft);
            rational w = weights[i];
            weight = w - weight;
            lower += weight*rational(i);
            IF_VERBOSE(1, verbose_stream() << "(opt.maxsat mutex size: " << i + 1 << " weight: " << weight << ")\n";);
            sum2 += weight * rational(i + 1);
            new_soft.insert(soft, weight);
            for (; i > 0 && weights[i-1] == w; --i) {} 
            weight = w;
        }        
        SASSERT(sum1 == sum2);        
    }


    preprocess::preprocess(solver& s):  m(s.get_manager()), s(s), m_trail(m) {}
    
    bool preprocess::operator()(vector<soft>& soft, rational& lower) {
        if (!find_mutexes(soft, lower))
            return false;
        if (false && !prop_mutexes(soft, lower))
            return false;
        return true;
    }
};
