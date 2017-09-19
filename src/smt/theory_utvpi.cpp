/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_utvpi.h
    
Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26

Revision History:

    The implementaton is derived from theory_diff_logic.

--*/
#include "smt/theory_utvpi.h"
#include "smt/theory_utvpi_def.h"

namespace smt {

    template class theory_utvpi<idl_ext>;
    template class theory_utvpi<rdl_ext>;

    // similar to test_diff_logic:

    utvpi_tester::utvpi_tester(ast_manager& m): m(m), a(m) {}

    bool utvpi_tester::operator()(expr* e) {
        m_todo.reset();
        m_mark.reset();
        m_todo.push_back(e);
        expr* e1, *e2;

        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            m_todo.pop_back();
            if (!m_mark.is_marked(e)) {
                m_mark.mark(e, true);
                if (is_var(e)) {
                    continue;
                }
                if (!is_app(e)) {
                    return false;
                }
                app* ap = to_app(e);
                if (m.is_eq(ap, e1, e2)) {
                    if (!linearize(e1, e2)) {
                        return false;
                    }
                }
                else if (ap->get_family_id() == m.get_basic_family_id()) {
                    continue;
                }
                else if (a.is_le(e, e1, e2) || a.is_ge(e, e2, e1) || 
                    a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1)) {
                    if (!linearize(e1, e2)) {
                        return false;
                    }
                }
                else if (is_uninterp_const(e)) {
                    continue;
                }
                else {
                    return false;
                }
            }
        }
        return true;
    }

    vector<std::pair<expr*, rational> > const& utvpi_tester::get_linearization() const {
        SASSERT(m_terms.size() <= 2);
        return m_terms;
    }
    
    bool utvpi_tester::operator()(unsigned num_fmls, expr* const* fmls) {
        for (unsigned i = 0; i < num_fmls; ++i) {
            if (!(*this)(fmls[i])) {
                return false;
            }
        }
        return true;
    }

    bool utvpi_tester::linearize(expr* e) {
        m_terms.reset();
        m_terms.push_back(std::make_pair(e, rational(1)));
        return linearize();
    }

    bool utvpi_tester::linearize(expr* e1, expr* e2) {
        m_terms.reset();
        m_terms.push_back(std::make_pair(e1, rational(1)));
        m_terms.push_back(std::make_pair(e2, rational(-1)));
        return linearize();
    }

    bool utvpi_tester::linearize() {

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
                return false;
            }
            else {
                m_coeff_map.insert_if_not_there2(e, rational(0))->get_data().m_value += mul;
            }
        }
        obj_map<expr, rational>::iterator it  = m_coeff_map.begin();
        obj_map<expr, rational>::iterator end = m_coeff_map.end();
        for (; it != end; ++it) {
            rational r = it->m_value;
            if (r.is_zero()) {
                continue;
            }
            m_terms.push_back(std::make_pair(it->m_key, r));
            if (m_terms.size() > 2) {
                return false;
            }
            if (!r.is_one() && !r.is_minus_one()) {
                return false;
            }
        }
        return true;
    }

    
}
