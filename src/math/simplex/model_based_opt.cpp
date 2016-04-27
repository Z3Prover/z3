/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    model_based_opt.cpp

Abstract:

    Model-based optimization for linear real arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-27-4

Revision History:


--*/

#include "model_based_opt.h"

namespace opt {
    
        
    bool model_based_opt::invariant() {
        // variables in each row are sorted.
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            if (!invariant(m_rows[i])) {
                return false;
            }
        }
        return invariant(m_objective);
    }

    bool model_based_opt::invariant(row const& r) {
        rational val = r.m_coeff;
        vector<var> const& vars = r.m_vars;
        for (unsigned i = 0; i < vars.size(); ++i) {
            var const& v = vars[i];
            SASSERT(i + 1 == vars.size() || v.m_id < vars[i+1].m_id);
            SASSERT(!v.m_coeff.is_zero());
            val += v.m_coeff * m_var2value[v.m_id];
        }
        SASSERT(val == r.m_value);
        SASSERT(r.m_type != t_eq ||  val.is_zero());
        SASSERT(r.m_type != t_lt ||  val.is_neg());
        SASSERT(r.m_type != t_le || !val.is_pos());        
        return true;
    }
        
    // a1*x + obj 
    // a2*x + t2 <= 0
    // a3*x + t3 <= 0
    // a4*x + t4 <= 0
    // a1 > 0, a2 > 0, a3 > 0, a4 < 0
    // x <= -t2/a2
    // x <= -t2/a3
    // determine lub among these.
    // then resolve lub with others
    // e.g., -t2/a2 <= -t3/a3, then 
    // replace inequality a3*x + t3 <= 0 by -t2/a2 + t3/a3 <= 0
    // mark a4 as invalid.
    // 

    // a1 < 0, a2 < 0, a3 < 0, a4 > 0
    // x >= t2/a2
    // x >= t3/a3
    // determine glb among these
    // the resolve glb with others.
    // e.g. t2/a2 >= t3/a3
    // then replace a3*x + t3 by t3/a3 - t2/a2 <= 0
    // 
    bound_type model_based_opt::maximize(rational& value) {
        // tbd
        SASSERT(invariant());
        vector<var> & vars = m_objective.m_vars;
        unsigned_vector other;
        while (!vars.empty()) {
            var const& v = vars.back();
            unsigned x = v.m_id;
            rational const& coeff = v.m_coeff;
            rational const& x_val = m_var2value[x];
            unsigned_vector const& row_ids = m_var2row_ids[x];
            unsigned bound_index;
            other.reset();
            if (find_bound(x, bound_index, other, coeff.is_pos())) {                        
                rational bound_coeff = m_rows[bound_index].m_coeff;
                for (unsigned i = 0; i < other.size(); ++i) {
                    resolve(other[i], bound_coeff, bound_index, x);
                }
                // coeff*x + objective -> coeff*(bound) + objective
                // tbd:
                multiply(coeff/bound_coeff, bound_index);
                //add(m_objective_id, bound_index);
                m_rows[bound_index].m_alive = false;
            }
            else {
                return unbounded;
            }
        }
        value = m_objective.m_coeff;
        switch (m_objective.m_type) {
        case t_lt: return strict;
        case t_le: return non_strict;
        case t_eq: return non_strict;
        }
        return non_strict;
    }

    bool model_based_opt::find_bound(unsigned x, unsigned& bound_index, unsigned_vector& other, bool is_pos) {
        bound_index = UINT_MAX;
        rational lub_val;
        rational const& x_val = m_var2value[x];
        unsigned_vector const& row_ids = m_var2row_ids[x];
        for (unsigned i = 0; i < row_ids.size(); ++i) {
            unsigned row_id = row_ids[i];
            row& r = m_rows[row_id];
            if (r.m_alive) {
                rational a = get_coefficient(row_id, x);
                if (a.is_pos() == is_pos) {
                    rational value = r.m_value - x_val*a;  // r.m_value = val_x*a + val(t), val(t) := r.m_value - val_x*a;
                    if (bound_index == UINT_MAX) {
                        lub_val = value;
                        bound_index = row_id;
                    }
                    else if ((is_pos && value < lub_val) || (!is_pos && value > lub_val)) {
                        other.push_back(bound_index);
                        lub_val = value;
                        bound_index = row_id;                            
                    }
                    else {
                        other.push_back(bound_index);
                    }
                }
                else if (!a.is_zero()) {
                    r.m_alive = false;
                }
            }
        }
        return bound_index != UINT_MAX;
    }
        
    rational model_based_opt::get_coefficient(unsigned row_id, unsigned var_id) {
        row const& r = m_rows[row_id];
        unsigned lo = 0, hi = r.m_vars.size();
        while (lo < hi) {
            unsigned mid = lo + (hi - lo)/2;
            SASSERT(mid < hi);
            unsigned id = r.m_vars[mid].m_id;
            if (id == var_id) {
                lo = mid;
                break;
            }
            if (id < var_id) {
                lo = mid + 1;
            }
            else {
                hi = mid - 1;
            }
        }
        unsigned id = r.m_vars[lo].m_id;
        if (id == var_id) {
            return r.m_vars[lo].m_coeff;
        }
        else {
            return rational::zero();
        }
    }

    bool model_based_opt::resolve(unsigned row_id1, rational const& a1, unsigned row_id2, unsigned x) {
        // row1 is of the form a1*x + t1 <~ 0
        // row2 is of the form a2*x + t2 <~ 0
        // assume that a1, a2 have the same sign.
        // if a1 is positive, then val(t1*a2/a1) <= val(t2*a1/a2)
        //   replace row2 with the new inequality of the form:
        //   t1 - a1*t2/a2 <~~ 0
        //   where <~~ is strict if either <~1 or <~2 is strict.
        // if a1 is negative, then ....
        //   
        if (!m_rows[row_id2].m_alive) {
            return false;
        }
        rational a2 = get_coefficient(row_id2, x);
        if (a2.is_zero()) {
            return false;
        }
        else if (a1.is_pos() && a2.is_pos()) {
            multiply(-a1/a2, row_id2);
            add(row_id2, row_id1);
            return true;
        }
        else if (a1.is_neg() && a2.is_neg()) {
            NOT_IMPLEMENTED_YET();
            // tbd
            return true;
        } 
        else {
            m_rows[row_id2].m_alive = false;
            return false;
        }
    }

    void model_based_opt::multiply(rational const& c, unsigned row_id) {
        if (c.is_one()) {
            return;
        }
        row& r = m_rows[row_id];
        SASSERT(r.m_alive);
        for (unsigned i = 0; i < r.m_vars.size(); ++i) {
            r.m_vars[i].m_coeff *= c;
        }
        r.m_coeff *= c;
        r.m_value *= c;
    }
    
    // add row2 to row1, store result in row1.
    
    void model_based_opt::add(unsigned row_id1, unsigned row_id2) {
        m_new_vars.reset();
        row& r1 = m_rows[row_id1];
        row const& r2 = m_rows[row_id2];
        unsigned i = 0, j = 0;
        for(; i < r1.m_vars.size() || j < r2.m_vars.size(); ) {
            if (j == r2.m_vars.size()) {
                m_new_vars.append(r1.m_vars.size() - i, r1.m_vars.c_ptr() + i);
            }
            else if (i == r1.m_vars.size()) {
                for (; j < r2.m_vars.size(); ++j) {
                    m_new_vars.push_back(r2.m_vars[j]);
                    m_var2row_ids[r2.m_vars[j].m_id].push_back(row_id1);
                }
            }
            else {
                unsigned v1 = r1.m_vars[i].m_id;
                unsigned v2 = r2.m_vars[j].m_id;
                if (v1 == v2) {
                    m_new_vars.push_back(r1.m_vars[i]);
                    m_new_vars.back().m_coeff += r2.m_vars[j].m_coeff;
                    ++i;
                    ++j;
                    if (m_new_vars.back().m_coeff.is_zero()) {
                        m_new_vars.pop_back();
                    }
                }
                else if (v1 < v2) {
                    m_new_vars.push_back(r1.m_vars[i]);
                    ++i;                        
                }
                else {
                    m_new_vars.push_back(r2.m_vars[j]);
                    m_var2row_ids[r2.m_vars[j].m_id].push_back(row_id1);
                    ++j;                        
                }
            }                
        }
        r1.m_coeff += r2.m_coeff;
        r1.m_vars.swap(m_new_vars);
        r1.m_value += r2.m_value;
        if (r2.m_type == t_lt) {
            r1.m_type = t_lt;
        }
    }
    
    void model_based_opt::display(std::ostream& out) const {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            display(out, m_rows[i]);
        }
    }        

    void model_based_opt::display(std::ostream& out, row const& r) const {
        vector<var> const& vars = r.m_vars;
        for (unsigned i = 0; i < vars.size(); ++i) {
            if (i > 0 && vars[i].m_coeff.is_pos()) {
                out << "+ ";
            }
            out << vars[i].m_coeff << "* v" << vars[i].m_id << " ";                
        }
        out << r.m_coeff;
        switch (r.m_type) {
        case t_eq:
            out << " = 0\n";
            break;
        case t_lt:
            out << " < 0\n";
            break;
        case t_le:
            out << " <= 0\n";
            break;
        }
    }

    unsigned model_based_opt::add_var(rational const& value) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    void model_based_opt::add_constraint(vector<var> const& coeffs, rational const& c, ineq_type r) {
        NOT_IMPLEMENTED_YET();
    }

    void model_based_opt::set_objective(vector<var> const& coeffs, rational const& c) {
        NOT_IMPLEMENTED_YET();
    }

}

