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
    mss                 m_mss;
    unsigned            m_index;
    expr_ref_vector     m_asms;
    unsigned            m_max_mss;

public:
    mss_solver(maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft):
        maxsmt_solver_base(c, ws, soft),
        m_mss(c.get_solver(), m),
        m_index(id),
        m_asms(m),
        m_max_mss(UINT_MAX) {
    }

    virtual ~mss_solver() {}

    virtual lbool operator()() {
        if (!init()) return l_undef;
        init_asms();
        lbool is_sat = check_sat(m_asms);
        if (is_sat == l_undef) return l_undef;
        if (is_sat == l_true) {
            IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :mss " << m_asms.size() << " :mcs " << 0 << ")\n";);
            model_ref mdl;
            s().get_model(mdl);
            update_assignment(mdl.get());
            return l_true;
        }
        return enumerate_mss();
    }

    virtual void updt_params(params_ref& p) {
        maxsmt_solver_base::updt_params(p);
        opt_params _p(p);
        m_max_mss = _p.mss_max();
    }

private:
    void init_asms() {
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

    lbool enumerate_mss() {
        expr_ref_vector asms(m);
        for (unsigned i = 0; i < m_max_mss; ++i) {
            exprs mss, mcs;
            lbool is_sat = next_mss(asms, mss, mcs);
            if (is_sat == l_false && i == 0) return l_false;
            if (is_sat == l_undef && i == 0) return l_undef;
            if (is_sat == l_false || is_sat == l_undef) return l_true;
            asms.push_back(relax_and_assert(m.mk_or(mcs.size(), mcs.c_ptr())));
        }
        return l_true;
    }

    lbool next_mss(expr_ref_vector const& asms, exprs& mss, exprs& mcs) {
        mss.reset();
        mcs.reset();
        lbool is_sat = check_sat(asms);
        if (is_sat != l_true) return is_sat;
        model_ref mdl;
        s().get_model(mdl);
        update_assignment(mdl.get());
        vector<exprs> dummy;
        push_exprs(mss, m_asms);
        push_exprs(mss, asms);
        is_sat = cld(mdl.get(), mss, mcs);
        if (is_sat == l_true) {
            IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :mss " << mss.size() - asms.size() << " :mcs " << mcs.size() << ")\n";);
        }
        /*is_sat = m_mss(mdl.get(), dummy, mss, mcs);
        SASSERT(is_sat != l_false);
        if (is_sat == l_true) {
            mdl.reset();
            m_mss.get_model(mdl);
            update_assignment(mdl.get());
            IF_VERBOSE(2, verbose_stream() << "(opt.mss-solver :mss " << mss.size() - asms.size() << " :mcs " << mcs.size() << ")\n";);
        }*/
        return is_sat;
    }

    lbool cld(model_ref initial_model, exprs& mss, exprs& mcs) {
        exprs sat, undef;
        undef.append(mss);
        update_sat(initial_model, sat, undef);
        lbool is_sat = l_true;
        while (is_sat == l_true) {
            expr_ref asum = relax_and_assert(m.mk_or(undef.size(), undef.c_ptr()));
            sat.push_back(asum);
            is_sat = check_sat(sat);
            sat.pop_back();
            if (is_sat == l_true) {
                model_ref mdl;
                s().get_model(mdl);
                update_sat(mdl, sat, undef);
                update_assignment(mdl.get());
            }
        }
        if (is_sat == l_false) {
            mss.reset();
            mcs.reset();
            mss.append(sat);
            mcs.append(undef);
            is_sat = l_true;
        }
        return is_sat;
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
        expr_ref_vector dummy(m);
        return check_sat(dummy);
    }

    lbool check_sat(expr_ref_vector const& asms) {
        return s().check_sat(asms);
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
        // TODO: DEBUG verify assignment
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
