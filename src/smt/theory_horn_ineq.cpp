/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_horn_ineq.h
    
Author:

    Nikolaj Bjorner (nbjorner) 2013-04-18

Revision History:

    The implementaton is derived from theory_diff_logic.

--*/
#include "theory_horn_ineq.h"
#include "theory_horn_ineq_def.h"

namespace smt {

    template class theory_horn_ineq<ihi_ext>;
    template class theory_horn_ineq<rhi_ext>;

    // similar to test_diff_logic:

    horn_ineq_tester::horn_ineq_tester(ast_manager& m): m(m), a(m) {}

    bool horn_ineq_tester::operator()(expr* e) {
        m_todo.reset();
        m_pols.reset();
        pos_mark.reset();
        neg_mark.reset();
        m_todo.push_back(e);
        m_pols.push_back(l_true);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            lbool  p = m_pols.back();
            m_todo.pop_back();
            m_pols.pop_back();
            switch (p) {
            case l_true:
                if (pos_mark.is_marked(e)) {
                    continue;
                }
                pos_mark.mark(e, true);
                break;
            case l_false:
                if (neg_mark.is_marked(e)) {
                    continue;
                }
                neg_mark.mark(e, true);
                break;
            case l_undef:
                if (pos_mark.is_marked(e) && neg_mark.is_marked(e)) {
                    continue;
                }
                pos_mark.mark(e, true);
                neg_mark.mark(e, true);
                break;
            }
            if (!test_expr(p, e)) {
                return false;
            }
        }
        return true;
    }

    vector<std::pair<expr*,rational> > const& horn_ineq_tester::get_linearization() const {
        return m_terms;
    }

    bool horn_ineq_tester::test_expr(lbool p, expr* e) {
        expr* e1, *e2, *e3;
        if (is_var(e)) {
            return true;
        }
        if (!is_app(e)) {
            return false;
        }
        app* ap = to_app(e);
        if (m.is_and(ap) || m.is_or(ap)) {
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                m_todo.push_back(ap->get_arg(i));
                m_pols.push_back(p);
            }
        }
        else if (m.is_not(e, e1)) {
            m_todo.push_back(e);
            m_pols.push_back(~p);
        }
        else if (m.is_ite(e, e1, e2, e3)) {
            m_todo.push_back(e1);
            m_pols.push_back(l_undef);
            m_todo.push_back(e2);
            m_pols.push_back(p);
            m_todo.push_back(e3);
            m_pols.push_back(p);
        }
        else if (m.is_iff(e, e1, e2)) {
            m_todo.push_back(e1);
            m_pols.push_back(l_undef);
            m_todo.push_back(e2);
            m_pols.push_back(l_undef);
            m_todo.push_back(e2);
        }
        else if (m.is_implies(e, e1, e2)) {
            m_todo.push_back(e1);
            m_pols.push_back(~p);
            m_todo.push_back(e2);
            m_pols.push_back(p);
        }
        else if (m.is_eq(e, e1, e2)) {
            return linearize(e1, e2) == diff;
        }
        else if (m.is_true(e) || m.is_false(e)) {
            // no-op
        }
        else if (a.is_le(e, e1, e2) || a.is_ge(e, e2, e1) || 
                 a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) {
            if (p == l_false) {
                std::swap(e2, e1);
            }
            classify_t cl = linearize(e1, e2);
            switch(p) {
            case l_undef:
                return cl == diff;
            case l_true:
            case l_false:
                return cl == horn || cl == diff;
            }
        }
        else if (!is_uninterp_const(e)) {
            return false;
        }
        return true;
    }
    
    bool horn_ineq_tester::operator()(unsigned num_fmls, expr* const* fmls) {
        for (unsigned i = 0; i < num_fmls; ++i) {
            if (!(*this)(fmls[i])) {
                return false;
            }
        }
        return true;
    }

    horn_ineq_tester::classify_t horn_ineq_tester::linearize(expr* e) {
        m_terms.reset();
        m_terms.push_back(std::make_pair(e, rational(1)));
        return linearize();
    }

    horn_ineq_tester::classify_t horn_ineq_tester::linearize(expr* e1, expr* e2) {
        m_terms.reset();
        m_terms.push_back(std::make_pair(e1, rational(1)));
        m_terms.push_back(std::make_pair(e2, rational(-1)));
        return linearize();
    }

    horn_ineq_tester::classify_t horn_ineq_tester::linearize() {

        m_weight.reset();
        m_coeff_map.reset();

        while (!m_terms.empty()) {
            expr* e1, *e2;
            rational num;
            rational mul = m_terms.back().second;
            expr* e = m_terms.back().first;
            m_terms.pop_back();
            if (a.is_add(e)) {
                for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
                    m_terms.push_back(std::make_pair(to_app(e)->get_arg(i), mul));
                }
            }
            else if (a.is_mul(e, e1, e2) && a.is_numeral(e1, num)) {
                m_terms.push_back(std::make_pair(e2, mul*num));
            }
            else if (a.is_mul(e, e2, e1) && a.is_numeral(e1, num)) {
                m_terms.push_back(std::make_pair(e2, mul*num));
            }
            else if (a.is_sub(e, e1, e2)) {
                m_terms.push_back(std::make_pair(e1, mul));
                m_terms.push_back(std::make_pair(e2, -mul));                
            }
            else if (a.is_uminus(e, e1)) {
                m_terms.push_back(std::make_pair(e1, -mul));
            }
            else if (a.is_numeral(e, num)) {
                m_weight += num*mul;
            }
            else if (a.is_to_real(e, e1)) {
                m_terms.push_back(std::make_pair(e1, mul));
            }
            else if (!is_uninterp_const(e)) {
                return non_horn;
            }
            else {
                m_coeff_map.insert_if_not_there2(e, rational(0))->get_data().m_value += mul;
            }
        }
        unsigned num_negative = 0;
        unsigned num_positive = 0;
        bool is_unit_pos = true, is_unit_neg = true;
        obj_map<expr, rational>::iterator it  = m_coeff_map.begin();
        obj_map<expr, rational>::iterator end = m_coeff_map.end();
        for (; it != end; ++it) {
            rational r = it->m_value;
            if (r.is_zero()) {
                continue;
            }
            m_terms.push_back(std::make_pair(it->m_key, r));
            if (r.is_pos()) {
                is_unit_pos = is_unit_pos && r.is_one();
                num_positive++;
            }
            else {
                is_unit_neg = is_unit_neg && r.is_minus_one();
                num_negative++;
            }
        }
        if (num_negative <= 1 && is_unit_pos && is_unit_neg && num_positive <= 1) {
            return diff;
        }
        if (num_positive <= 1 && is_unit_pos) {
            return horn;
        }
        if (num_negative <= 1 && is_unit_neg) {
            return co_horn;
        }
        return non_horn;
    }


}
