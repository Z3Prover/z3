/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mss.cpp

Abstract:
   
    MSS/MCS extraction.

Author:

    Nikolaj Bjorner (nbjorner) 2014-2-8

Notes:


--*/

#include "solver.h"
#include "smt_literal.h"
#include "mss.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"

namespace opt {


    mss::mss(solver& s, ast_manager& m): s(s), m(m), m_cancel(false) {
    }
    
    mss::~mss() {
    }
    

    void mss::check_parameters(vector<exprs > const& cores, exprs& literals) {
        expr* n;
        for (unsigned i = 0; i < literals.size(); ++i) {
            n = literals[i];
            m.is_not(n, n);
            if (!is_uninterp_const(n)) {
                throw default_exception("arguments have to be uninterpreted literals");
            }
        }
        // cores are disjoint
        // cores are a subset of literals
        // literals not in cores evaluate to true in current model
    }

    /**
       \brief Move literals satisfied in todo into mss.
       Precondition: the solver state is satisfiable.
    */
    void mss::update_model() {
        expr_ref tmp(m);
        s.get_model(m_model);
        update_set(m_todo);
    }
    
    void mss::update_set(exprs& lits) {
        expr_ref tmp(m);
        unsigned sz = lits.size();
        unsigned j = 0;
        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* n = lits[i];
            if (m_mcs.contains(n)) {
                // remove from todo.
                continue;
            }
            VERIFY(m_model->eval(n, tmp));
            if (m.is_false(tmp)) {
                if (j != i) {
                    lits[j] = lits[i];
                }
                ++j;
            }
            else {
                m_mss.push_back(n);            
            }
        }
        lits.resize(j);
    }
    
    
    lbool mss::operator()(vector<exprs> const& cores, exprs& literals) {
        m_mss.reset();
        m_mcs.reset();
        m_todo.reset();
        m_todo.append(literals);
        check_parameters(cores, literals);
        update_model();
        lbool is_sat = l_true;
        for (unsigned i = 0; is_sat == l_true && i < cores.size(); ++i) {
            is_sat = process_core(cores[i]);
        }    
        if (is_sat == l_true) {
            literals.reset();
            literals.append(m_mss);
        }
        return is_sat;
    }
    
    lbool mss::process_core(exprs const& _core) {
        // at least one literal in core is false in current model.
        // pick literals in core that are not yet in mss.
        exprs core(_core);
        update_set(core);
        return process_core(1, core);    
    }
    
    lbool mss::process_core(unsigned sz, exprs& core) {
        TRACE("opt", tout << "process: " << sz << " out of " << core.size() << " literals\n";);
        SASSERT(sz > 0);
        if (core.empty()) {
            return l_true;
        }
        if (m_cancel) {
            return l_undef;
        }
        sz = std::min(sz, core.size());
        unsigned sz_save = m_mss.size();
        m_mss.append(sz, core.c_ptr());
        lbool is_sat = s.check_sat(m_mss.size(), m_mss.c_ptr());
        m_mss.resize(sz_save);
        switch (is_sat) {
        case l_true:
            update_model();
            update_set(core);
            return process_core(2*sz, core);
        case l_false:
            if (sz == 1) {
                m_mcs.insert(core[0]);
                core[0] = core.back();
                core.pop_back();
            }
            else {
                exprs core2;            
                core2.append(core.size()-sz, core.c_ptr()+sz);
                core.resize(sz);
                is_sat = process_core(sz, core2);
                if (is_sat != l_true) {
                    return is_sat;
                }
            }
            return process_core(1, core);
        case l_undef:
            return l_undef;
        }
        
        return l_true;
    }

    void mss::display(std::ostream& out) const {
        
    }
}




