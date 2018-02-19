#include "solver/solver.h"
#include "opt/maxsmt.h"
#include "opt/mss_solver.h"
#include "opt/mss.h"
#include "opt/opt_context.h"
#include "opt/opt_params.hpp"

using namespace opt;

class mss_solver: public maxsmt_solver_base {

private:
    typedef ptr_vector<expr> exprs;
    typedef obj_hashtable<expr> expr_set;
    mss                 m_mss;
    unsigned            m_index;
    exprs               m_asms;
    unsigned            m_mss_found;
    vector<exprs>       m_cores;
    unsigned            m_core_idx;
    model_ref           m_last_model;
    exprs               m_mss_trail;
    exprs               m_mcs_trail;
    unsigned_vector     m_mss_trail_lim;
    unsigned_vector     m_mcs_trail_lim;
    unsigned            m_max_mss;
    bool                m_disjoint_cores;

public:
    mss_solver(maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft):
        maxsmt_solver_base(c, ws, soft),
        m_mss(c.get_solver(), m),
        m_index(id),
        m_mss_found(0),
        m_core_idx(0),
        m_max_mss(UINT_MAX),
        m_disjoint_cores(false) {
    }

    virtual ~mss_solver() {}

    virtual lbool operator()() {
        if (!init()) return l_undef;
        init_local();
        lbool is_sat = disjoint_cores();
        if (is_sat != l_true) return is_sat;
        if (m_cores.size() == 0) return l_true;
        update_model();
        exprs asms;
        while (true) {
            exprs mss, mcs;
            mss.append(m_cores[m_core_idx]);
            is_sat = cld(m_last_model, mss, mcs);
            if (is_sat == l_undef || m.canceled()) return l_undef;
            SASSERT(is_sat == l_true);
            update_trails(mss, mcs);
            if (m_core_idx < m_cores.size()-1) {
                m_core_idx++;
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :mss " << m_mss_trail.size() + m_asms.size() << " :mcs " << m_mcs_trail.size() << ")\n";);
                if (++m_mss_found >= m_max_mss) return l_true;
                asms.push_back(relax_and_assert(m.mk_or(m_mcs_trail.size(), m_mcs_trail.c_ptr())));
                is_sat = backtrack(asms);
                if (is_sat == l_false) {
                    SASSERT(m_core_idx == 0);
                    is_sat = disjoint_cores(asms);
                }
                if (is_sat == l_undef) return l_undef;
                if (is_sat == l_false) return l_true;
            }
        }
        return l_true;
    }

    virtual void updt_params(params_ref& p) {
        maxsmt_solver_base::updt_params(p);
        opt_params _p(p);
        m_max_mss = _p.mss_max();
        m_disjoint_cores = _p.mss_disjoint_cores();
    }

private:
    void init_local() {
        m_cores.reset();
        m_core_idx = 0;
        m_mss_found = 0;
        m_last_model.reset();
        m_mss_trail.reset();
        m_mcs_trail.reset();
        m_mss_trail_lim.reset();
        m_mcs_trail_lim.reset();
        m_asms.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            expr* e = m_soft[i];
            m_asms.push_back(relax_and_assert(e));
        }
    }

    expr_ref relax_and_assert(expr* e) {
        expr_ref asum(m);
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = mk_fresh_bool("r");
            e = m.mk_iff(asum, e);
            s().assert_expr(e);
        }
        return asum;
    }

    bool is_literal(expr* l) {
        return is_uninterp_const(l) || (m.is_not(l, l) && is_uninterp_const(l));
    }

    lbool disjoint_cores(exprs const& asms) {
        expr_set asm_lits, core_lits;
        for (unsigned i = 0; i < asms.size(); ++i) {
            asm_lits.insert(asms[i]);
        }
        lbool is_sat = l_false;
        exprs core;
        while (is_sat == l_false) {
            exprs tmp_asms;
            tmp_asms.append(asms);
            tmp_asms.append(m_asms);
            is_sat = check_sat(tmp_asms);
            if (is_sat == l_true) {
                update_model();
            }
            else if (is_sat == l_false) {
                core.reset();
                s().get_unsat_core(core);
                for (unsigned i = 0; i < core.size();) {
                    if (asm_lits.contains(core[i])) {
                        core[i] = core.back();
                        core.pop_back();
                    }
                    else {
                        core_lits.insert(core[i]);
                        ++i;
                    }
                }
                if (core.empty()) {
                    IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver empty core)\n";);
                    return l_false;
                }
                if (m_disjoint_cores) {
                    m_cores.push_back(core);
                    IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :core-size " << core.size() << " :num-cores " << m_cores.size() << ")\n";);
                    for (unsigned i = 0; i < m_asms.size();) {
                        if (core_lits.contains(m_asms[i]) || !m_disjoint_cores) {
                            m_asms[i] = m_asms.back();
                            m_asms.pop_back();
                        }
                        else {
                            ++i;
                        }
                    }
                }
                else {
                    m_cores.push_back(m_asms);
                    m_asms.reset();
                }
            }
        }
        IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :num-cores " << m_cores.size() << ")\n";);
        // TODO: update m_lower?
        return is_sat;
    }

    lbool disjoint_cores() {
        return disjoint_cores(exprs());
    }

    lbool backtrack(exprs& asms) {
        SASSERT(m_mss_trail_lim.size() == m_mcs_trail_lim.size());
        lbool is_sat = l_false;
        while (is_sat == l_false && m_core_idx > 0) {
            m_core_idx--;
            m_mss_trail.resize(m_mss_trail_lim.back());
            m_mss_trail_lim.pop_back();
            m_mcs_trail.resize(m_mcs_trail_lim.back());
            m_mcs_trail_lim.pop_back();
            exprs tmp_asms;
            tmp_asms.append(asms);
            get_trail_asms(tmp_asms);
            is_sat = check_sat(tmp_asms);
            if (is_sat == l_true) {
                update_model();
            }
        }
        IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :backtrack-lvl " << m_core_idx << ")\n";);
        return is_sat;
    }

    lbool cld(model_ref initial_model, exprs& mss, exprs& mcs) {
        exprs sat, undef;
        undef.append(mss);
        update_sat(initial_model, sat, undef);
        lbool is_sat = l_true;
        while (is_sat == l_true && !undef.empty()) {
            expr_ref asum = relax_and_assert(m.mk_or(undef.size(), undef.c_ptr()));
            exprs asms;
            asms.append(sat);
            get_trail_asms(asms);
            asms.push_back(asum);
            is_sat = check_sat(asms);
            if (is_sat == l_true) {
                update_model();
                update_sat(m_last_model, sat, undef);
            }
        }
        if (is_sat == l_false || undef.empty()) {
            mss.reset();
            mcs.reset();
            mss.append(sat);
            mcs.append(undef);
            is_sat = l_true;
        }
        return is_sat;
    }

    void get_trail_asms(exprs& asms) {
        asms.append(m_mss_trail);
        for (unsigned i = 0; i < m_mcs_trail.size(); ++i) {
            asms.push_back(m.mk_not(m_mcs_trail[i]));
        }
    }

    void update_trails(exprs const& mss, exprs const& mcs) {
        m_mss_trail_lim.push_back(m_mss_trail.size());
        m_mcs_trail_lim.push_back(m_mcs_trail.size());
        m_mss_trail.append(mss);
        m_mcs_trail.append(mcs);
    }

    void update_model() {
        m_last_model.reset();
        s().get_model(m_last_model);
        update_assignment(m_last_model.get());
    }

    void update_sat(model_ref mdl, exprs& sat, exprs& undef) {
        for (unsigned i = 0; i < undef.size();) {
            if (is_true(mdl.get(), undef[i])) {
                sat.push_back(undef[i]);
                undef[i] = undef.back();
                undef.pop_back();
            }
            else {
                ++i;
            }
        }
    }

    void push_exprs(exprs& dst, expr_ref_vector const& src) {
        for (unsigned i = 0; i < src.size(); ++i) {
            dst.push_back(src[i]);
        }
    }

    lbool check_sat() {
        return check_sat(exprs());
    }

    lbool check_sat(exprs const& asms) {
        return s().check_sat(asms.size(), asms.c_ptr());
    }

    void update_assignment(model* mdl) {
        rational upper(0);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            if (!is_true(mdl, m_soft[i])) {
                upper += m_weights[i];
            }
        }
        if (upper > m_upper) return;
        if (!m_c.verify_model(m_index, mdl, upper)) return;
        m_model = mdl;
        m_c.model_updated(mdl);
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            m_assignment[i] = is_true(m_soft[i]);
        }
        // TODO: DEBUG verify assignment?
        m_upper = upper;
        trace_bounds("mss-solver");
    }

    bool is_true(model* mdl, expr* e) {
        expr_ref tmp(m);
        return mdl->eval(e, tmp, true) && m.is_true(tmp);
    }

    bool is_true(expr* e) {
        return is_true(m_model.get(), e);
    }
};

maxsmt_solver_base* opt::mk_mss_solver(maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft) {
    return alloc(mss_solver, c, id, ws, soft);
}
