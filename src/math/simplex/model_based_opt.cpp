/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    model_based_opt.cpp

Abstract:

    Model-based optimization and projection for linear real, integer arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-27-4

Revision History:


--*/

#include "model_based_opt.h"
#include "uint_set.h"

std::ostream& operator<<(std::ostream& out, opt::ineq_type ie) {
    switch (ie) {
    case opt::t_eq: return out << " = ";
    case opt::t_lt: return out << " < ";
    case opt::t_le: return out << " <= ";        
    case opt::t_mod: return out << " mod ";
    }
    return out;
}


namespace opt {
    

    model_based_opt::model_based_opt() {
        m_rows.push_back(row());
    }

        
    bool model_based_opt::invariant() {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            if (!invariant(i, m_rows[i])) {
                return false;
            }
        }
        return true;
    }

#define PASSERT(_e_) if (!(_e_)) { TRACE("opt", display(tout, r);); SASSERT(_e_); }

    bool model_based_opt::invariant(unsigned index, row const& r) {
        vector<var> const& vars = r.m_vars;
        for (unsigned i = 0; i < vars.size(); ++i) {
            // variables in each row are sorted and have non-zero coefficients
            PASSERT(i + 1 == vars.size() || vars[i].m_id < vars[i+1].m_id);
            PASSERT(!vars[i].m_coeff.is_zero());
            PASSERT(index == 0 || m_var2row_ids[vars[i].m_id].contains(index));
        }
        
        PASSERT(r.m_value == get_row_value(r));
        PASSERT(r.m_type != t_eq ||  r.m_value.is_zero());
        // values satisfy constraints
        PASSERT(index == 0 || r.m_type != t_lt ||  r.m_value.is_neg());
        PASSERT(index == 0 || r.m_type != t_le || !r.m_value.is_pos());        
        PASSERT(index == 0 || r.m_type != t_mod || (mod(r.m_value, r.m_mod).is_zero()));
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
    inf_eps model_based_opt::maximize() {
        SASSERT(invariant());
        unsigned_vector bound_trail, bound_vars;
        TRACE("opt", display(tout << "tableau\n"););
        while (!objective().m_vars.empty()) {
            var v = objective().m_vars.back();
            unsigned x = v.m_id;
            rational const& coeff = v.m_coeff;
            unsigned bound_row_index;
            rational bound_coeff;
            if (find_bound(x, bound_row_index, bound_coeff, coeff.is_pos())) {
                SASSERT(!bound_coeff.is_zero());
                TRACE("opt", display(tout << "update: " << v << " ", objective());
                      for (unsigned i = 0; i < m_above.size(); ++i) {
                          display(tout << "resolve: ", m_rows[m_above[i]]);
                      });
                for (unsigned i = 0; i < m_above.size(); ++i) {
                    resolve(bound_row_index, bound_coeff, m_above[i], x);
                }
                for (unsigned i = 0; i < m_below.size(); ++i) {
                    resolve(bound_row_index, bound_coeff, m_below[i], x);
                }
                // coeff*x + objective <= ub
                // a2*x + t2 <= 0
                // => coeff*x <= -t2*coeff/a2
                // objective + t2*coeff/a2 <= ub

                mul_add(false, m_objective_id, - coeff/bound_coeff, bound_row_index);
                retire_row(bound_row_index);
                bound_trail.push_back(bound_row_index);
                bound_vars.push_back(x);
            }
            else {
                TRACE("opt", display(tout << "unbound: " << v << " ", objective()););
                update_values(bound_vars, bound_trail);
                return inf_eps::infinity();
            }
        }

        //
        // update the evaluation of variables to satisfy the bound.
        //

        update_values(bound_vars, bound_trail);

        rational value = objective().m_value;
        if (objective().m_type == t_lt) {            
            return inf_eps(inf_rational(value, rational(-1)));
        }
        else {
            return inf_eps(inf_rational(value));
        }
    }


    void model_based_opt::update_value(unsigned x, rational const& val) {
        rational old_val = m_var2value[x];
        m_var2value[x] = val;
        unsigned_vector const& row_ids = m_var2row_ids[x];
        for (unsigned i = 0; i < row_ids.size(); ++i) {            
            unsigned row_id = row_ids[i];
            rational coeff = get_coefficient(row_id, x);
            if (coeff.is_zero()) {
                continue;
            }
            row & r = m_rows[row_id];
            rational delta = coeff * (val - old_val);            
            r.m_value += delta;
            SASSERT(invariant(row_id, r));
        }
    }


    void model_based_opt::update_values(unsigned_vector const& bound_vars, unsigned_vector const& bound_trail) {
        for (unsigned i = bound_trail.size(); i > 0; ) {
            --i;
            unsigned x = bound_vars[i];
            row& r = m_rows[bound_trail[i]];
            rational val = r.m_coeff;
            rational old_x_val = m_var2value[x];
            rational new_x_val;
            rational x_coeff, eps(0);
            vector<var> const& vars = r.m_vars;
            for (unsigned j = 0; j < vars.size(); ++j) {
                var const& v = vars[j];
                if (x == v.m_id) {
                    x_coeff = v.m_coeff;
                }
                else {
                    val += m_var2value[v.m_id]*v.m_coeff;
                }
            }
            SASSERT(!x_coeff.is_zero());
            new_x_val = -val/x_coeff;

            if (r.m_type == t_lt) {
                eps = abs(old_x_val - new_x_val)/rational(2);
                eps = std::min(rational::one(), eps);
                SASSERT(!eps.is_zero());

                //
                //     ax + t < 0
                // <=> x < -t/a
                // <=> x := -t/a - epsilon
                // 
                if (x_coeff.is_pos()) {
                    new_x_val -= eps;
                }
                //
                //     -ax + t < 0 
                // <=> -ax < -t
                // <=> -x < -t/a
                // <=> x > t/a
                // <=> x := t/a + epsilon
                //
                else {
                    new_x_val += eps;
                }
            }
            TRACE("opt", display(tout << "v" << x 
                                 << " coeff_x: " << x_coeff 
                                 << " old_x_val: " << old_x_val
                                 << " new_x_val: " << new_x_val
                                 << " eps: " << eps << " ", r); );
            m_var2value[x] = new_x_val;
            
            r.m_value = get_row_value(r);
            SASSERT(invariant(bound_trail[i], r));
        }        
        
        // update and check bounds for all other affected rows.
        for (unsigned i = bound_trail.size(); i > 0; ) {
            --i;
            unsigned x = bound_vars[i];
            unsigned_vector const& row_ids = m_var2row_ids[x];
            for (unsigned j = 0; j < row_ids.size(); ++j) {            
                unsigned row_id = row_ids[j];
                row & r = m_rows[row_id];
                r.m_value = get_row_value(r);
                SASSERT(invariant(row_id, r));
            }            
        }
        SASSERT(invariant());
    }

    bool model_based_opt::find_bound(unsigned x, unsigned& bound_row_index, rational& bound_coeff, bool is_pos) {
        bound_row_index = UINT_MAX;
        rational lub_val;
        rational const& x_val = m_var2value[x];
        unsigned_vector const& row_ids = m_var2row_ids[x];
        uint_set visited;
        m_above.reset();
        m_below.reset();
        for (unsigned i = 0; i < row_ids.size(); ++i) {
            unsigned row_id = row_ids[i];
            SASSERT(row_id != m_objective_id);
            if (visited.contains(row_id)) {
                continue;
            }
            visited.insert(row_id);
            row& r = m_rows[row_id];
            if (r.m_alive) {
                rational a = get_coefficient(row_id, x);
                if (a.is_zero()) {
                    // skip
                }
                else if (a.is_pos() == is_pos || r.m_type == t_eq) {
                    rational value = x_val - (r.m_value/a);
                    if (bound_row_index == UINT_MAX) {
                        lub_val = value;
                        bound_row_index = row_id;
                        bound_coeff = a;
                    }
                    else if ((value == lub_val && r.m_type == opt::t_lt) ||
                             (is_pos && value < lub_val) || 
                             (!is_pos && value > lub_val)) {
                        m_above.push_back(bound_row_index);
                        lub_val = value;
                        bound_row_index = row_id;                          
                        bound_coeff = a;
                    }
                    else {
                        m_above.push_back(row_id);
                    }
                }
                else {
                    m_below.push_back(row_id);
                }
            }
        }
        return bound_row_index != UINT_MAX;
    }

    void model_based_opt::retire_row(unsigned row_id) {
        m_rows[row_id].m_alive = false;
        m_retired_rows.push_back(row_id);
    }
       
    rational model_based_opt::get_row_value(row const& r) const {
        vector<var> const& vars = r.m_vars;
        rational val = r.m_coeff;
        for (unsigned i = 0; i < vars.size(); ++i) {
            var const& v = vars[i];
            val += v.m_coeff * m_var2value[v.m_id];
        }
        return val;
    }    
 
    rational model_based_opt::get_coefficient(unsigned row_id, unsigned var_id) const {
        row const& r = m_rows[row_id];
        if (r.m_vars.empty()) {
            return rational::zero();
        }
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
                hi = mid;
            }
        }
        if (lo == r.m_vars.size()) {
            return rational::zero();
        }
        unsigned id = r.m_vars[lo].m_id;
        if (id == var_id) {
            return r.m_vars[lo].m_coeff;
        }
        else {
            return rational::zero();
        }
    }

    // 
    // Let
    //   row1: t1 + a1*x <= 0
    //   row2: t2 + a2*x <= 0
    //
    // assume a1, a2 have the same signs:
    //       (t2 + a2*x) <= (t1 + a1*x)*a2/a1 
    //   <=> t2*a1/a2 - t1 <= 0
    //   <=> t2 - t1*a2/a1 <= 0
    //
    // assume a1 > 0, -a2 < 0:
    //       t1 + a1*x <= 0,  t2 - a2*x <= 0
    //       t2/a2 <= -t1/a1
    //       t2 + t1*a2/a1 <= 0
    // assume -a1 < 0, a2 > 0:
    //       t1 - a1*x <= 0,  t2 + a2*x <= 0
    //       t1/a1 <= -t2/a2
    //       t2 + t1*a2/a1 <= 0
    // 
    // the resolvent is the same in all cases (simpler proof should exist)
    // 

    void model_based_opt::resolve(unsigned row_src, rational const& a1, unsigned row_dst, unsigned x) {

        SASSERT(a1 == get_coefficient(row_src, x));
        SASSERT(!a1.is_zero());
        SASSERT(row_src != row_dst);
                
        if (m_rows[row_dst].m_alive) {
            rational a2 = get_coefficient(row_dst, x);
            if (is_int(x)) {
                TRACE("opt", 
                      tout << a1 << " " << a2 << ": ";
                      display(tout, m_rows[row_dst]);
                      display(tout, m_rows[row_src]););
                if (a1.is_pos() != a2.is_pos()) {  
                    mul_add(x, a1, row_src, a2, row_dst);
                }
                else {
                    mul(row_dst, abs(a1));
                    mul_add(false, row_dst, -abs(a2), row_src);
                }
                TRACE("opt", display(tout, m_rows[row_dst]););
                normalize(row_dst);
            }
            else {
                mul_add(row_dst != m_objective_id && a1.is_pos() == a2.is_pos(), row_dst, -a2/a1, row_src);            
            }
        }
    }

    // resolution for integer rows.
    void model_based_opt::mul_add(
        unsigned x, rational const& src_c, unsigned row_src, rational const& dst_c, unsigned row_dst) {
        row& dst = m_rows[row_dst];
        row const& src = m_rows[row_src];
        SASSERT(is_int(x));
        SASSERT(t_le == dst.m_type && t_le == src.m_type);
        SASSERT(src_c.is_int());
        SASSERT(dst_c.is_int());

        rational abs_src_c = abs(src_c);
        rational abs_dst_c = abs(dst_c);            
        rational x_val = m_var2value[x];
        rational slack = (abs_src_c - rational::one()) * (abs_dst_c - rational::one());
        rational dst_val = dst.m_value - x_val*dst_c;
        rational src_val = src.m_value - x_val*src_c;
        bool use_case1 = 
            (src_c * dst_val + dst_c * src_val + slack).is_nonpos() 
            || abs_src_c.is_one() 
            || abs_dst_c.is_one();

        if (use_case1) {
            // dst <- abs_src_c*dst + abs_dst_c*src - slack
            mul(row_dst, abs_src_c);
            sub(row_dst, slack);
            mul_add(false, row_dst, abs_dst_c, row_src);
            return;
        }

        //
        // create finite disjunction for |b|.                                
        //    exists x, z in [0 .. |b|-2] . b*x + s + z = 0 && ax + t <= 0 && bx + s <= 0
        // <=> 
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && ax + t <= 0 && bx + s <= 0
        // <=>
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && bx + s <= 0
        // <=>
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z - s + s <= 0
        // <=>
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z <= 0
        // <=>
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0
        // <=>
        //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a*n_sign(b)(s + z) + |b|t <= 0
        // <=>
        //    exists z in [0 .. |b|-2] . |b| | (z + s) && a*n_sign(b)(s + z) + |b|t <= 0
        //

        vector<var> coeffs;
        if (abs_dst_c <= abs_src_c) {
            rational z = mod(dst_val, abs_dst_c);
            if (!z.is_zero()) z = abs_dst_c - z;
            mk_coeffs_without(coeffs, dst.m_vars, x); 
            add_divides(coeffs, dst.m_coeff + z, abs_dst_c);
            add(row_dst, z);
            mul(row_dst, src_c * n_sign(dst_c));
            mul_add(false, row_dst, abs_dst_c, row_src);            
        }
        else {
            // z := b - (s + bx) mod b 
            //   := b - s mod b
            // b | s + z <=> b | s + b - s mod b <=> b | s - s mod b
            rational z = mod(src_val, abs_src_c);
            if (!z.is_zero()) z = abs_src_c - z;      
            mk_coeffs_without(coeffs, src.m_vars, x);
            add_divides(coeffs, src.m_coeff + z, abs_src_c);
            mul(row_dst, abs_src_c);
            add(row_dst, z * dst_c * n_sign(src_c));            
            mul_add(false, row_dst, dst_c * n_sign(src_c), row_src);
        }
    }

    void model_based_opt::mk_coeffs_without(vector<var>& dst, vector<var> const src, unsigned x) {
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src[i].m_id != x) dst.push_back(src[i]);
        }
    }

    rational model_based_opt::n_sign(rational const& b) const {
        return rational(b.is_pos()?-1:1);
    }
   
    void model_based_opt::mul(unsigned dst, rational const& c) {
        if (c.is_one()) return;
        row& r = m_rows[dst];
        for (unsigned i = 0; i < r.m_vars.size(); ++i) {
            r.m_vars[i].m_coeff *= c;
        }
        r.m_coeff *= c;
        r.m_value *= c;
    }

    void model_based_opt::add(unsigned dst, rational const& c) {
        row& r = m_rows[dst];
        r.m_coeff += c;
        r.m_value += c;
    }

    void model_based_opt::sub(unsigned dst, rational const& c) {
        row& r = m_rows[dst];
        r.m_coeff -= c;
        r.m_value -= c;
    }

    void model_based_opt::normalize(unsigned row_id) {
        row& r = m_rows[row_id];
        if (r.m_vars.empty()) return;
        if (r.m_type == t_mod) return;
        rational g(abs(r.m_vars[0].m_coeff));
        bool all_int = g.is_int();
        for (unsigned i = 1; all_int && !g.is_one() && i < r.m_vars.size(); ++i) {
            rational const& coeff = r.m_vars[i].m_coeff;
            if (coeff.is_int()) {
                g = gcd(g, abs(coeff));
            }
            else {
                all_int = false;
            }
        }
        if (all_int && !r.m_coeff.is_zero()) {
            if (r.m_coeff.is_int()) {
                g = gcd(g, abs(r.m_coeff));
            }
            else {
                all_int = false;
            }
        }
        if (all_int && !g.is_one()) {
            SASSERT(!g.is_zero());
            mul(row_id, rational::one()/g);
        }
    }
 
    //
    // set row1 <- row1 + c*row2
    //
    void model_based_opt::mul_add(bool same_sign, unsigned row_id1, rational const& c, unsigned row_id2) {
        if (c.is_zero()) {
            return;
        }

        m_new_vars.reset();
        row& r1 = m_rows[row_id1];
        row const& r2 = m_rows[row_id2];
        unsigned i = 0, j = 0;
        for(; i < r1.m_vars.size() || j < r2.m_vars.size(); ) {
            if (j == r2.m_vars.size()) {
                m_new_vars.append(r1.m_vars.size() - i, r1.m_vars.c_ptr() + i);
                break;
            }
            if (i == r1.m_vars.size()) {
                for (; j < r2.m_vars.size(); ++j) {
                    m_new_vars.push_back(r2.m_vars[j]);
                    m_new_vars.back().m_coeff *= c;
                    if (row_id1 != m_objective_id) {
                        m_var2row_ids[r2.m_vars[j].m_id].push_back(row_id1);
                    }
                }
                break;
            }

            unsigned v1 = r1.m_vars[i].m_id;
            unsigned v2 = r2.m_vars[j].m_id;
            if (v1 == v2) {
                m_new_vars.push_back(r1.m_vars[i]);
                m_new_vars.back().m_coeff += c*r2.m_vars[j].m_coeff;
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
                m_new_vars.back().m_coeff *= c;
                if (row_id1 != m_objective_id) {
                    m_var2row_ids[r2.m_vars[j].m_id].push_back(row_id1);
                }
                ++j;                        
            }
        }
        r1.m_coeff += c*r2.m_coeff;
        r1.m_vars.swap(m_new_vars);
        r1.m_value += c*r2.m_value;

        if (!same_sign && r2.m_type == t_lt) {
            r1.m_type = t_lt;
        }
        else if (same_sign && r1.m_type == t_lt && r2.m_type == t_lt) {
            r1.m_type = t_le;        
        }
        SASSERT(invariant(row_id1, r1));
    }
    
    void model_based_opt::display(std::ostream& out) const {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            display(out, m_rows[i]);
        }
        for (unsigned i = 0; i < m_var2row_ids.size(); ++i) {
            unsigned_vector const& rows = m_var2row_ids[i];
            out << i << ": ";
            for (unsigned j = 0; j < rows.size(); ++j) {
                out << rows[j] << " ";
            }
            out << "\n";
        }
    }        

    void model_based_opt::display(std::ostream& out, row const& r) const {
        vector<var> const& vars = r.m_vars;
        out << (r.m_alive?"+":"-") << " ";
        for (unsigned i = 0; i < vars.size(); ++i) {
            if (i > 0 && vars[i].m_coeff.is_pos()) {
                out << "+ ";
            }
            out << vars[i].m_coeff << "* v" << vars[i].m_id << " ";                
        }
        if (r.m_coeff.is_pos()) {
            out << " + " << r.m_coeff << " ";
        }
        else if (r.m_coeff.is_neg()) {
            out << r.m_coeff << " ";
        }        
        if (r.m_type == opt::t_mod) {
            out << r.m_type << " " << r.m_mod << " = 0; value: " << r.m_value  << "\n";
        }
        else {
            out << r.m_type << " 0; value: " << r.m_value  << "\n";
        }
    }

    unsigned model_based_opt::add_var(rational const& value, bool is_int) {
        unsigned v = m_var2value.size();
        m_var2value.push_back(value);
        m_var2is_int.push_back(is_int);
        m_var2row_ids.push_back(unsigned_vector());
        return v;
    }

    rational model_based_opt::get_value(unsigned var) {
        return m_var2value[var];
    }

    void model_based_opt::set_row(unsigned row_id, vector<var> const& coeffs, rational const& c, rational const& m, ineq_type rel) {
        row& r = m_rows[row_id];
        rational val(c);
        SASSERT(r.m_vars.empty());
        r.m_vars.append(coeffs.size(), coeffs.c_ptr());
        bool is_int_row = true;
        std::sort(r.m_vars.begin(), r.m_vars.end(), var::compare());
        for (unsigned i = 0; i < coeffs.size(); ++i) {
            val += m_var2value[coeffs[i].m_id] * coeffs[i].m_coeff;
            SASSERT(!is_int(coeffs[i].m_id) || coeffs[i].m_coeff.is_int());
            is_int_row &= is_int(coeffs[i].m_id);
        }
        r.m_alive = true;
        r.m_coeff = c;
        r.m_value = val;
        r.m_type = rel;
        r.m_mod = m;
        if (is_int_row && rel == t_lt) {
            r.m_type = t_le;
            r.m_coeff  += rational::one();
            r.m_value  += rational::one();
        }
    }

    unsigned model_based_opt::new_row() {
        unsigned row_id = 0;
        if (m_retired_rows.empty()) {
            row_id = m_rows.size();
            m_rows.push_back(row());
        }
        else {
            row_id = m_retired_rows.back();
            m_retired_rows.pop_back();
            m_rows[row_id].reset();
            m_rows[row_id].m_alive = true;
        }
        return row_id;
    }

    unsigned model_based_opt::copy_row(unsigned src) {
        unsigned dst = new_row();
        row const& r = m_rows[src];
        set_row(dst, r.m_vars, r.m_coeff, r.m_mod, r.m_type);
        for (unsigned i = 0; i < r.m_vars.size(); ++i) {
            m_var2row_ids[r.m_vars[i].m_id].push_back(dst);
        }
        SASSERT(invariant(dst, m_rows[dst]));
        return dst;
    }

    void model_based_opt::add_constraint(vector<var> const& coeffs, rational const& c, ineq_type rel) {
        add_constraint(coeffs, c, rational::zero(), rel);
    }

    void model_based_opt::add_divides(vector<var> const& coeffs, rational const& c, rational const& m) {
        add_constraint(coeffs, c, m, t_mod);
    }

    void model_based_opt::add_constraint(vector<var> const& coeffs, rational const& c, rational const& m, ineq_type rel) {
        unsigned row_id = new_row();
        set_row(row_id, coeffs, c, m, rel);
        for (unsigned i = 0; i < coeffs.size(); ++i) {
            m_var2row_ids[coeffs[i].m_id].push_back(row_id); 
        }
        SASSERT(invariant(row_id, m_rows[row_id]));
    }

    void model_based_opt::set_objective(vector<var> const& coeffs, rational const& c) {
        set_row(m_objective_id, coeffs, c, rational::zero(), t_le);
    }

    void model_based_opt::get_live_rows(vector<row>& rows) {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            if (m_rows[i].m_alive) {
                rows.push_back(m_rows[i]);
            }
        }
    }

    //
    // pick glb and lub representative.
    // The representative is picked such that it 
    // represents the fewest inequalities. 
    // The constraints that enforce a glb or lub are not forced.
    // The constraints that separate the glb from ub or the lub from lb
    // are not forced.
    // In other words, suppose there are 
    // . N inequalities of the form t <= x
    // . M inequalities of the form s >= x
    // . t0 is glb among N under valuation.
    // . s0 is lub among M under valuation.
    // If N < M
    //    create the inequalities:
    //       t <= t0 for each t other than t0 (N-1 inequalities).
    //       t0 <= s for each s (M inequalities).
    // If N >= M the construction is symmetric.
    // 
    void model_based_opt::project(unsigned x) {
        unsigned_vector& lub_rows = m_lub;
        unsigned_vector& glb_rows = m_glb;
        unsigned_vector& mod_rows = m_mod;
        unsigned lub_index = UINT_MAX, glb_index = UINT_MAX;
        bool     lub_strict = false, glb_strict = false;
        rational lub_val, glb_val;
        rational const& x_val = m_var2value[x];
        unsigned_vector const& row_ids = m_var2row_ids[x];
        uint_set visited;
        lub_rows.reset();
        glb_rows.reset();
        mod_rows.reset();
        bool lub_is_unit = false, glb_is_unit = false;
        // select the lub and glb.
        for (unsigned i = 0; i < row_ids.size(); ++i) {
            unsigned row_id = row_ids[i];
            if (visited.contains(row_id)) {
                continue;
            }
            visited.insert(row_id);
            row& r = m_rows[row_id];
            if (!r.m_alive) {
                continue;
            }
            rational a = get_coefficient(row_id, x);
            if (a.is_zero()) {
                continue;
            }
            if (r.m_type == t_eq) {
                solve_for(row_id, x);
                return;
            }
            if (r.m_type == t_mod) {
                mod_rows.push_back(row_id);
            }
            else if (a.is_pos()) {
                rational lub_value = x_val - (r.m_value/a);
                if (lub_rows.empty() || 
                    lub_value < lub_val ||
                    (lub_value == lub_val && r.m_type == t_lt && !lub_strict)) {
                    lub_val = lub_value;
                    lub_index = row_id;
                    lub_strict = r.m_type == t_lt;                    
                }
                lub_rows.push_back(row_id);
                lub_is_unit &= a.is_one();
            }
            else {
                SASSERT(a.is_neg());
                rational glb_value = x_val - (r.m_value/a);
                if (glb_rows.empty() || 
                    glb_value > glb_val ||
                    (glb_value == glb_val && r.m_type == t_lt && !glb_strict)) {
                    glb_val = glb_value;
                    glb_index = row_id;
                    glb_strict = r.m_type == t_lt;                    
                }
                glb_rows.push_back(row_id);
                glb_is_unit &= a.is_minus_one();
            }
        }

        if (!mod_rows.empty()) {
            solve_mod(x, mod_rows);
            return;
        }
        
        unsigned lub_size = lub_rows.size();
        unsigned glb_size = glb_rows.size();
        unsigned row_index = (lub_size <= glb_size) ? lub_index : glb_index;
        glb_rows.append(lub_rows);  
        
        // There are only upper or only lower bounds.
        if (row_index == UINT_MAX) {
            for (unsigned i = 0; i < glb_rows.size(); ++i) {
                unsigned row_id = glb_rows[i];
                SASSERT(m_rows[row_id].m_alive);
                SASSERT(!get_coefficient(row_id, x).is_zero());
                retire_row(row_id);
            }
            return;
        }

        // The number of matching lower and upper bounds is small.
        if ((lub_size <= 2 || glb_size <= 2) &&
            (lub_size <= 3 && glb_size <= 3) && 
            (!is_int(x) || lub_is_unit || glb_is_unit)) {
            for (unsigned i = 0; i < lub_size; ++i) {
                unsigned row_id1 = lub_rows[i];
                bool last = i + 1 == lub_rows.size();
                rational coeff = get_coefficient(row_id1, x);
                for (unsigned j = 0; j < glb_size; ++j) {
                    unsigned row_id2 = glb_rows[j];
                    if (last) {
                        resolve(row_id1, coeff, row_id2, x);
                    }
                    else {
                        unsigned row_id3 = copy_row(row_id2);
                        resolve(row_id1, coeff, row_id3, x);
                    }
                }
            }
            for (unsigned i = 0; i < lub_size; ++i) {
                retire_row(lub_rows[i]);
            }
            return;
        }

        // General case.
        rational coeff = get_coefficient(row_index, x);
        for (unsigned i = 0; i < glb_rows.size(); ++i) {
            unsigned row_id = glb_rows[i];
            if (row_id != row_index) {
                resolve(row_index, coeff, row_id, x);
            }
        }
        retire_row(row_index);
    }

    // 
    // compute D and u.
    //
    // D = lcm(d1, d2)
    // u = eval(x) mod D
    // 
    //   d1 | (a1x + t1) & d2 | (a2x + t2)
    // = 
    //   d1 | (a1(D*x' + u) + t1) & d2 | (a2(D*x' + u) + t2)
    // =
    //   d1 | (a1*u + t1) & d2 | (a2*u + t2)
    // 
    // x := D*x' + u
    // 

    void model_based_opt::solve_mod(unsigned x, unsigned_vector const& mod_rows) {
        SASSERT(!mod_rows.empty());
        rational D(1);
        for (unsigned i = 0; i < mod_rows.size(); ++i) {
            D = lcm(D, m_rows[mod_rows[i]].m_mod);            
        }
        TRACE("opt", display(tout << "lcm: " << D << " tableau\n"););
        rational val_x = m_var2value[x];
        rational u = mod(val_x, D);
        SASSERT(u.is_nonneg() && u < D);
        for (unsigned i = 0; i < mod_rows.size(); ++i) {
            replace_var(mod_rows[i], x, u);            
            SASSERT(invariant(mod_rows[i], m_rows[mod_rows[i]]));
        }
        //
        // update inequalities such that u is added to t and
        // D is multiplied to coefficient of x.
        // the interpretation of the new version of x is (x-u)/D
        //
        // a*x + t <= 0
        // a*(D*x' + u) + t <= 0
        // a*D*x' + a*u + t <= 0
        //
        rational new_val = (val_x - u) / D;
        SASSERT(new_val.is_int());
        unsigned y = add_var(new_val, true);
        unsigned_vector const& row_ids = m_var2row_ids[x];
        uint_set visited;
        for (unsigned i = 0; i < row_ids.size(); ++i) {
            unsigned row_id = row_ids[i];
            if (!visited.contains(row_id)) {
                // x |-> D*y + u
                replace_var(row_id, x, D, y, u);
                visited.insert(row_id);
            }
        }
        project(y);
    }

    // update row with: x |-> C
    void model_based_opt::replace_var(unsigned row_id, unsigned x, rational const& C) {
        row& r = m_rows[row_id];
        SASSERT(!get_coefficient(row_id, x).is_zero());
        unsigned sz = r.m_vars.size();
        unsigned i = 0, j = 0;
        rational coeff(0);
        for (; i < sz; ++i) {
            if (r.m_vars[i].m_id == x) {
                coeff = r.m_vars[i].m_coeff;
            }
            else {
                if (i != j) {
                    r.m_vars[j] = r.m_vars[i];
                }
                ++j;
            }
        }
        if (j != sz) {
            r.m_vars.shrink(j);
        }
        r.m_coeff += coeff*C;
        r.m_value += coeff*(C - m_var2value[x]);
    }

    // update row with: x |-> A*y + B
    void model_based_opt::replace_var(unsigned row_id, unsigned x, rational const& A, unsigned y, rational const& B) {
        row& r = m_rows[row_id];
        rational coeff = get_coefficient(row_id, x);
        if (coeff.is_zero()) return;
        if (!r.m_alive) return;
        replace_var(row_id, x, B);        
        r.m_vars.push_back(var(y, coeff*A));
        r.m_value += coeff*A*m_var2value[y];
        if (!r.m_vars.empty() && r.m_vars.back().m_id > y) {
            std::sort(r.m_vars.begin(), r.m_vars.end(), var::compare());
        }
        m_var2row_ids[y].push_back(row_id);
        SASSERT(invariant(row_id, r));
    }

    // 3x + t = 0 & 7 | (c*x + s) & ax <= u 
    // 3 | -t  & 21 | (-ct + 3s) & a-t <= 3u

    void model_based_opt::solve_for(unsigned row_id1, unsigned x) {
        rational a = get_coefficient(row_id1, x), b;
        SASSERT(!a.is_zero());
        SASSERT(m_rows[row_id1].m_type == t_eq);
        SASSERT(m_rows[row_id1].m_alive);
        if (m_var2is_int[x] && !abs(a).is_one()) {
            row& r1 = m_rows[row_id1];
            vector<var> coeffs;
            mk_coeffs_without(coeffs, r1.m_vars, x);
            add_divides(coeffs, r1.m_coeff, abs(a));
        }
        unsigned_vector const& row_ids = m_var2row_ids[x];
        uint_set visited;
        visited.insert(row_id1);
        for (unsigned i = 0; i < row_ids.size(); ++i) {
            unsigned row_id2 = row_ids[i];
            if (!visited.contains(row_id2)) {                
                visited.insert(row_id2);
                b = get_coefficient(row_id2, x);
                if (!b.is_zero()) {
                    resolve(row_id1, a, row_id2, x);            
                }
            }
        }
        retire_row(row_id1);
    }

    void model_based_opt::project(unsigned num_vars, unsigned const* vars) {
        for (unsigned i = 0; i < num_vars; ++i) {
            project(vars[i]);
            TRACE("opt", display(tout << "After projecting: v" << vars[i] << "\n"););
        }
    }

}

