/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    opt_preprocess.cpp

Abstract:
   
    Pre-processing for MaxSMT

    Find mutexes - at most 1 constraints and modify soft constraints and bounds.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-11

--*/

#pragma once

#include "opt/opt_preprocess.h"

namespace opt {

    bool preprocess::find_mutexes(vector<soft>& softs, rational& lower) {
        expr_ref_vector fmls(m);
        obj_map<expr, rational> new_soft;
        for (soft& sf : softs) {
            m_trail.push_back(sf.s);
            if (new_soft.contains(sf.s))
                new_soft[sf.s] += sf.weight;
            else
                new_soft.insert(sf.s, sf.weight);
            fmls.push_back(sf.s);
        }
        vector<expr_ref_vector> mutexes;
        lbool is_sat = s.find_mutexes(fmls, mutexes);
        if (is_sat == l_false)
            return true;
        if (is_sat == l_undef)
            return false;
        for (auto& mux : mutexes) 
            process_mutex(mux, new_soft, lower);
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
            sum2 += weight*rational(i+1);
            new_soft.insert(soft, weight);
            for (; i > 0 && weights[i-1] == w; --i) {} 
            weight = w;
        }        
        SASSERT(sum1 == sum2);        
    }

    preprocess::preprocess(solver& s):  m(s.get_manager()), s(s), m_trail(m) {}
    
    bool preprocess::operator()(vector<soft>& soft, rational& lower) {
        return find_mutexes(soft, lower);
    }
};
