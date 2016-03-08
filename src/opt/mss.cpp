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
#include "mss.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"

namespace opt {


    mss::mss(solver& s, ast_manager& m): m_s(s), m(m) {
    }
    
    mss::~mss() {
    }    

    bool mss::check_result() {
        lbool is_sat = m_s.check_sat(m_mss.size(), m_mss.c_ptr());
        if (is_sat == l_undef) return true;
        SASSERT(m_mss.empty() || is_sat == l_true);
        if (is_sat == l_false) return false;
        expr_set::iterator it = m_mcs.begin(), end = m_mcs.end();
        for (; it != end; ++it) {
            m_mss.push_back(*it);
            is_sat = m_s.check_sat(m_mss.size(), m_mss.c_ptr());
            m_mss.pop_back();
            if (is_sat == l_undef) return true;
            SASSERT(is_sat == l_false);
            if (is_sat == l_true) return false;
        }
        return true;
    }

    void mss::initialize(exprs& literals) {
        expr* n;
        expr_set lits, core_lits;
        for (unsigned i = 0; i < literals.size(); ++i) {
            n = literals[i];
            lits.insert(n);
            m.is_not(n, n);
            if (!is_uninterp_const(n)) {
                throw default_exception("arguments have to be uninterpreted literals");
            }
        }
        exprs rest_core;
        expr_ref tmp(m);
        //
        // the last core is a dummy core. It contains literals that
        // did not occur in previous cores and did not evaluate to true
        // in the current model.
        //
        for (unsigned i = 0; i < m_cores.size(); ++i) {
            exprs const& core = m_cores[i];
            for (unsigned j = 0; j < core.size(); ++j) {
                expr* n = core[j];
                if (!core_lits.contains(n)) {
                    core_lits.insert(n);
                    if (m_model->eval(n, tmp) && m.is_true(tmp)) {
                        add_mss(n);
                    }
                    else {
                        m_todo.push_back(n);
                    }
                }
            }
        }
        for (unsigned i = 0; i < literals.size(); ++i) {
            expr* n = literals[i];
            if (!core_lits.contains(n)) {
                if (m_model->eval(n, tmp) && m.is_true(tmp)) {
                    m_mss.push_back(n);
                }
                else {
                    rest_core.push_back(n);
                    core_lits.insert(n);
                    m_todo.push_back(n);
                }
            }
        }
        m_cores.push_back(rest_core);
    }

    void mss::add_mss(expr* n) {
        if (!m_mss_set.contains(n)) {
            m_mss_set.insert(n);
            m_mss.push_back(n);
        }
    }

    void mss::update_core(exprs& core) {
        unsigned j = 0;
        for (unsigned i = 0; i < core.size(); ++i) {            
            expr* n = core[i];
            if (!m_mss_set.contains(n)) {
                if (i != j) {
                    core[j] = core[i];
                }
                ++j;
            }
        }
        core.resize(j);
    }

    void mss::update_mss() {
        expr_ref tmp(m);
        unsigned j = 0;
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            expr* n = m_todo[i];
            SASSERT(!m_mss_set.contains(n));
            if (m_mcs.contains(n)) {
                continue; // remove from cores.
            }
            if (m_model->eval(n, tmp) && m.is_true(tmp)) {
                add_mss(n);
            }
            else {
                if (j != i) {
                    m_todo[j] = m_todo[i];
                }
                ++j;
            }
        }
        m_todo.resize(j);
    }       
    
    lbool mss::operator()(model* initial_model, vector<exprs> const& _cores, exprs& literals, exprs& mcs) {
        m_mss.reset();
        m_todo.reset();
        m_model = initial_model;
        m_cores.reset();
        SASSERT(m_model);
        m_cores.append(_cores);
        initialize(literals);
        TRACE("opt", 
              display_vec(tout << "lits: ", literals.size(), literals.c_ptr());
              display(tout););
        lbool is_sat = l_true;
        for (unsigned i = 0; is_sat == l_true && i < m_cores.size(); ++i) {
            bool has_mcs = false;
            bool is_last = i + 1 < m_cores.size();
            SASSERT(check_invariant());
            update_core(m_cores[i]); // remove members of mss
            is_sat = process_core(1, m_cores[i], has_mcs, is_last); 
        }    
        if (is_sat == l_true) {
            SASSERT(check_invariant());
            TRACE("opt", display(tout););
            literals.reset();
            literals.append(m_mss);
            mcs.reset();
            expr_set::iterator it = m_mcs.begin(), end = m_mcs.end();
            for (; it != end; ++it) {
                mcs.push_back(*it);
            }
            SASSERT(check_result());
        }
        m_mcs.reset();
        m_mss_set.reset();
        IF_VERBOSE(2, display_vec(verbose_stream() << "mcs: ", mcs.size(), mcs.c_ptr()););
        return is_sat;
    }

    
    //
    // at least one literal in core is false in current model.
    // pick literals in core that are not yet in mss.
    //    
    lbool mss::process_core(unsigned sz, exprs& core, bool& has_mcs, bool is_last) {
        SASSERT(sz > 0);
        if (core.empty()) {
            return l_true;
        }
        if (m.canceled()) {
            return l_undef;
        }
        if (sz == 1 && core.size() == 1 && is_last && !has_mcs) {
            // there has to be at least one false 
            // literal in the core.
            TRACE("opt", tout << "mcs: " << mk_pp(core[0], m) << "\n";);
            m_mcs.insert(core[0]);
            return l_true;
        }
        sz = std::min(sz, core.size());
        TRACE("opt", display_vec(tout << "process (total " << core.size() << ") :", sz, core.c_ptr()););
        unsigned sz_save = m_mss.size();
        m_mss.append(sz, core.c_ptr());
        lbool is_sat = m_s.check_sat(m_mss.size(), m_mss.c_ptr());
        IF_VERBOSE(3, display_vec(verbose_stream() << "mss: ", m_mss.size(), m_mss.c_ptr()););
        m_mss.resize(sz_save);
        switch (is_sat) {
        case l_true:
            m_s.get_model(m_model);
            update_mss();           
            DEBUG_CODE(
                for (unsigned i = 0; i < sz; ++i) {
                    SASSERT(m_mss_set.contains(core[i]));
                });
            update_core(core);
            return process_core(2*sz, core, has_mcs, is_last);
        case l_false:
            if (sz == 1) {
                has_mcs = true;
                m_mcs.insert(core[0]);
                core[0] = core.back();
                core.pop_back();
            }
            else {
                exprs core2;            
                core2.append(core.size()-sz, core.c_ptr()+sz);
                core.resize(sz);
                is_sat = process_core(sz, core2, has_mcs, false);
                if (is_sat != l_true) {
                    return is_sat;
                }
                update_core(core);
            }
            return process_core(1, core, has_mcs, is_last);
        case l_undef:
            return l_undef;
        }
        
        return l_true;
    }

    void mss::display_vec(std::ostream& out, unsigned sz, expr* const* args) const {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " ";
        }
        out << "\n";
    }

    void mss::display(std::ostream& out) const {
        for (unsigned i = 0; i < m_cores.size(); ++i) {
            display_vec(out << "core: ", m_cores[i].size(), m_cores[i].c_ptr());
        }
        expr_set::iterator it = m_mcs.begin(), end = m_mcs.end();
        out << "mcs:\n";
        for (; it != end; ++it) {
            out << mk_pp(*it, m) << "\n";
        }
        out << "\n";
        out << "mss:\n";
        for (unsigned i = 0; i < m_mss.size(); ++i) {
           out << mk_pp(m_mss[i], m) << "\n";
        }
        out << "\n";
        if (m_model) {
            model_smt2_pp(out, m, *(m_model.get()), 0);
        }
    }

    bool mss::check_invariant() const {
        if (!m_model) return true;
        expr_ref tmp(m);
        for (unsigned i = 0; i < m_mss.size(); ++i) {
            expr* n = m_mss[i];
            if (!m_model->eval(n, tmp)) return true;
            CTRACE("opt", !m.is_true(tmp), tout << mk_pp(n, m) << " |-> " << mk_pp(tmp, m) << "\n";);
            SASSERT(!m.is_false(tmp));
        }
        return true;
    }
}




