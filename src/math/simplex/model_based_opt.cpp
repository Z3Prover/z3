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

#include "math/simplex/model_based_opt.h"
#include "util/uint_set.h"
#include "util/z3_exception.h"

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
    
    /**
     * Convert a row ax + coeffs + coeff = value into a definition for x
     *    x  = (value - coeffs - coeff)/a 
     * as backdrop we have existing assignments to x and other variables that 
     * satisfy the equality with value, and such that value satisfies
     * the row constraint ( = , <= , < , mod)
     */
    model_based_opt::def::def(row const& r, unsigned x) {
        for (var const & v : r.m_vars) {
            if (v.m_id != x) { 
                m_vars.push_back(v); 
            }
            else {
                m_div = -v.m_coeff;
            }
        }        
        m_coeff = r.m_coeff;
        switch (r.m_type) {
        case opt::t_lt: 
            m_coeff += m_div;
            break;
        case opt::t_le:
            // for: ax >= t, then x := (t + a - 1) div a
            if (m_div.is_pos()) {
                m_coeff += m_div;
                m_coeff -= rational::one();
            }
            break;
        default:
            break;
        }
        normalize();
        SASSERT(m_div.is_pos());
    }

    model_based_opt::def model_based_opt::def::operator+(def const& other) const {
        def result;
        vector<var> const& vs1 = m_vars;
        vector<var> const& vs2 = other.m_vars;
        vector<var> & vs = result.m_vars;
        rational c1(1), c2(1);
        if (m_div != other.m_div) {
            c1 = other.m_div;
            c2 = m_div;
        }        
        unsigned i = 0, j = 0;
        while (i < vs1.size() || j < vs2.size()) {
            unsigned v1 = UINT_MAX, v2 = UINT_MAX;
            if (i < vs1.size()) v1 = vs1[i].m_id;
            if (j < vs2.size()) v2 = vs2[j].m_id;
            if (v1 == v2) {
                vs.push_back(vs1[i]);
                vs.back().m_coeff *= c1; 
                vs.back().m_coeff += c2 * vs2[j].m_coeff; 
                ++i; ++j;
                if (vs.back().m_coeff.is_zero()) {
                    vs.pop_back();
                }
            }
            else if (v1 < v2) {
                vs.push_back(vs1[i]);
                vs.back().m_coeff *= c1;                 
            }
            else {
                vs.push_back(vs2[j]);
                vs.back().m_coeff *= c2;                 
            }
        }
        result.m_div = c1*m_div;
        result.m_coeff = (m_coeff*c1) + (other.m_coeff*c2);
        result.normalize();
        return result;
    }

    model_based_opt::def model_based_opt::def::operator/(rational const& r) const {
        def result(*this);
        result.m_div *= r;
        result.normalize();
        return result;
    }

    model_based_opt::def model_based_opt::def::operator*(rational const& n) const {
        def result(*this);
        for (var& v : result.m_vars) {
            v.m_coeff *= n;
        }
        result.m_coeff *= n;
        result.normalize();
        return result;
    }

    model_based_opt::def model_based_opt::def::operator+(rational const& n) const {
        def result(*this);
        result.m_coeff += n * result.m_div;
        result.normalize();
        return result;
    }

    void model_based_opt::def::normalize() {
        if (m_div.is_one()) return;
        rational g(m_div);
        g = gcd(g, m_coeff);
        for (var const& v : m_vars) {
            g = gcd(g, abs(v.m_coeff));
            if (g.is_one()) break;
        }
        if (m_div.is_neg()) {
            g.neg();
        }
        if (!g.is_one()) {
            for (var& v : m_vars) {
                v.m_coeff /= g;
            }
            m_coeff /= g;
            m_div /= g;
        }
    }

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

#define PASSERT(_e_) if (!(_e_)) { TRACE("opt1", display(tout, r); display(tout);); SASSERT(_e_); }

    bool model_based_opt::invariant(unsigned index, row const& r) {
        vector<var> const& vars = r.m_vars;
        for (unsigned i = 0; i < vars.size(); ++i) {
            // variables in each row are sorted and have non-zero coefficients
            PASSERT(i + 1 == vars.size() || vars[i].m_id < vars[i+1].m_id);
            PASSERT(!vars[i].m_coeff.is_zero());
            PASSERT(index == 0 || m_var2row_ids[vars[i].m_id].contains(index));
        }
        
        PASSERT(r.m_value == eval(r));
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
                      for (unsigned above : m_above) {
                          display(tout << "resolve: ", m_rows[above]);
                      });
                for (unsigned above : m_above) {
                    resolve(bound_row_index, bound_coeff, above, x);
                }
                for (unsigned below : m_below) {
                    resolve(bound_row_index, bound_coeff, below, x);
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
        SASSERT(val.is_int() || !is_int(x));
        unsigned_vector const& row_ids = m_var2row_ids[x];
        for (unsigned row_id : row_ids) {
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
        for (unsigned i = bound_trail.size(); i-- > 0; ) {
            unsigned x = bound_vars[i];
            row& r = m_rows[bound_trail[i]];
            rational val = r.m_coeff;
            rational old_x_val = m_var2value[x];
            rational new_x_val;
            rational x_coeff, eps(0);
            vector<var> const& vars = r.m_vars;
            for (var const& v : vars) {                 
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
            
            r.m_value = eval(r);
            SASSERT(invariant(bound_trail[i], r));
        }        
        
        // update and check bounds for all other affected rows.
        for (unsigned i = bound_trail.size(); i-- > 0; ) {
            unsigned x = bound_vars[i];
            unsigned_vector const& row_ids = m_var2row_ids[x];
            for (unsigned row_id : row_ids) {                
                row & r = m_rows[row_id];
                r.m_value = eval(r);
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
        for (unsigned row_id : row_ids) {
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

    rational model_based_opt::eval(unsigned x) const {
        return m_var2value[x];
    }

    rational model_based_opt::eval(def const& d) const {
        vector<var> const& vars = d.m_vars;
        rational val = d.m_coeff;
        for (var const& v : vars) {
            val += v.m_coeff * eval(v.m_id);
        }
        val /= d.m_div;
        return val;        
    }
       
    rational model_based_opt::eval(row const& r) const {
        vector<var> const& vars = r.m_vars;
        rational val = r.m_coeff;
        for (var const& v : vars) {
            val += v.m_coeff * eval(v.m_id);
        }
        return val;
    }    
 
    rational model_based_opt::get_coefficient(unsigned row_id, unsigned var_id) const {
        return m_rows[row_id].get_coefficient(var_id);
    }

    rational model_based_opt::row::get_coefficient(unsigned var_id) const {
        if (m_vars.empty()) {
            return rational::zero();
        }
        unsigned lo = 0, hi = m_vars.size();
        while (lo < hi) {
            unsigned mid = lo + (hi - lo)/2;
            SASSERT(mid < hi);
            unsigned id = m_vars[mid].m_id;
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
        if (lo == m_vars.size()) {
            return rational::zero();
        }
        unsigned id = m_vars[lo].m_id;
        if (id == var_id) {
            return m_vars[lo].m_coeff;
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
                if (a1.is_pos() != a2.is_pos() || m_rows[row_src].m_type == opt::t_eq) {  
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

    void model_based_opt::solve(unsigned row_src, rational const& a1, unsigned row_dst, unsigned x) {
        SASSERT(a1 == get_coefficient(row_src, x));
        SASSERT(a1.is_pos());
        SASSERT(row_src != row_dst);                
        if (!m_rows[row_dst].m_alive) return;
        rational a2 = get_coefficient(row_dst, x);
        mul(row_dst, a1);
        mul_add(false, row_dst, -a2, row_src);
        SASSERT(get_coefficient(row_dst, x).is_zero());
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
        SASSERT(m_var2value[x].is_int());

        rational abs_src_c = abs(src_c);
        rational abs_dst_c = abs(dst_c);            
        rational x_val = m_var2value[x];
        rational slack = (abs_src_c - rational::one()) * (abs_dst_c - rational::one());
        rational dst_val = dst.m_value - x_val*dst_c;
        rational src_val = src.m_value - x_val*src_c;
        rational distance = abs_src_c * dst_val + abs_dst_c * src_val + slack; 
        bool use_case1 = distance.is_nonpos() || abs_src_c.is_one() || abs_dst_c.is_one();

#if 0
        if (distance.is_nonpos() && !abs_src_c.is_one() && !abs_dst_c.is_one()) {
            unsigned r = copy_row(row_src);
            mul_add(false, r, rational::one(), row_dst);
            del_var(r, x);
            add(r, slack);
            TRACE("qe", tout << m_rows[r];);
            SASSERT(!m_rows[r].m_value.is_pos());
        }
#endif

        if (use_case1) {
            TRACE("opt", tout << "slack: " << slack << " " << src_c << " " << dst_val << " " << dst_c << " " << src_val << "\n";);
            // dst <- abs_src_c*dst + abs_dst_c*src + slack
            mul(row_dst, abs_src_c);
            add(row_dst, slack);
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

        TRACE("qe", tout << "finite disjunction " << distance << " " << src_c << " " << dst_c << "\n";); 
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

    void model_based_opt::mk_coeffs_without(vector<var>& dst, vector<var> const& src, unsigned x) {
        for (var const & v : src) {
            if (v.m_id != x) dst.push_back(v);
        }
    }

    rational model_based_opt::n_sign(rational const& b) const {
        return rational(b.is_pos()?-1:1);
    }
   
    void model_based_opt::mul(unsigned dst, rational const& c) {
        if (c.is_one()) return;
        row& r = m_rows[dst];
        for (auto & v : r.m_vars) {
            v.m_coeff *= c;
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

    void model_based_opt::del_var(unsigned dst, unsigned x) {
        row& r = m_rows[dst];
        unsigned j = 0; 
        for (var & v : r.m_vars) {
            if (v.m_id == x) {
                r.m_value -= eval(x)*r.m_coeff;
            }
            else {
                r.m_vars[j++] = v;
            }
        }
        r.m_vars.shrink(j);
    }


    void model_based_opt::normalize(unsigned row_id) {
        row& r = m_rows[row_id];
        if (r.m_vars.empty()) {
            retire_row(row_id);
            return;
        }
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
        while (i < r1.m_vars.size() || j < r2.m_vars.size()) {
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
        for (auto const& r : m_rows) {
            display(out, r);
        }
        for (unsigned i = 0; i < m_var2row_ids.size(); ++i) {
            unsigned_vector const& rows = m_var2row_ids[i];
            out << i << ": ";
            for (auto const& r : rows) {
                out << r << " ";
            }
            out << "\n";
        }
    }        

    void model_based_opt::display(std::ostream& out, vector<var> const& vars, rational const& coeff) {
        unsigned i = 0;
        for (var const& v : vars) {
            if (i > 0 && v.m_coeff.is_pos()) {
                out << "+ ";
            }
            ++i;
            if (v.m_coeff.is_one()) {
                out << "v" << v.m_id << " ";
            }
            else {
                out << v.m_coeff << "*v" << v.m_id << " ";                
            }
        }
        if (coeff.is_pos()) {
            out << " + " << coeff << " ";
        }
        else if (coeff.is_neg()) {
            out << coeff << " ";
        }                
    }

    std::ostream& model_based_opt::display(std::ostream& out, row const& r) {
        out << (r.m_alive?"+":"-") << " ";
        display(out, r.m_vars, r.m_coeff);
        if (r.m_type == opt::t_mod) {
            out << r.m_type << " " << r.m_mod << " = 0; value: " << r.m_value  << "\n";
        }
        else {
            out << r.m_type << " 0; value: " << r.m_value  << "\n";
        }
        return out;
    }

    std::ostream& model_based_opt::display(std::ostream& out, def const& r) {
        display(out, r.m_vars, r.m_coeff);
        if (!r.m_div.is_one()) {
            out << " / " << r.m_div;
        }
        return out;
    }

    unsigned model_based_opt::add_var(rational const& value, bool is_int) {
        unsigned v = m_var2value.size();
        m_var2value.push_back(value);
        m_var2is_int.push_back(is_int);
        SASSERT(value.is_int() || !is_int);
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
        for (auto const& c : coeffs) {
            val += m_var2value[c.m_id] * c.m_coeff;
            SASSERT(!is_int(c.m_id) || c.m_coeff.is_int());
            is_int_row &= is_int(c.m_id);
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
        for (auto const& v : r.m_vars) {
            m_var2row_ids[v.m_id].push_back(dst);
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
        for (var const& coeff : coeffs) {
            m_var2row_ids[coeff.m_id].push_back(row_id); 
        }
        SASSERT(invariant(row_id, m_rows[row_id]));
    }

    void model_based_opt::set_objective(vector<var> const& coeffs, rational const& c) {
        set_row(m_objective_id, coeffs, c, rational::zero(), t_le);
    }

    void model_based_opt::get_live_rows(vector<row>& rows) {
        for (row const& r : m_rows) {
            if (r.m_alive) {
                rows.push_back(r);
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
    model_based_opt::def model_based_opt::project(unsigned x, bool compute_def) {
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
        unsigned eq_row = UINT_MAX;
        // select the lub and glb.
        for (unsigned row_id : row_ids) {
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
                eq_row = row_id;
                continue;
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
            return solve_mod(x, mod_rows, compute_def);
        }

        if (eq_row != UINT_MAX) {
            return solve_for(eq_row, x, compute_def);
        }

        def result;
        unsigned lub_size = lub_rows.size();
        unsigned glb_size = glb_rows.size();
        unsigned row_index = (lub_size <= glb_size) ? lub_index : glb_index;
        
        // There are only upper or only lower bounds.
        if (row_index == UINT_MAX) {
            if (compute_def) {
                if (lub_index != UINT_MAX) {                    
                    result = solve_for(lub_index, x, true);
                }
                else if (glb_index != UINT_MAX) {
                    result = solve_for(glb_index, x, true);                
                }
                else {
                    result = def();
                    m_var2value[x] = rational::zero();
                }
                SASSERT(eval(result) == eval(x));
            }
            else {
                for (unsigned row_id : lub_rows) retire_row(row_id);
                for (unsigned row_id : glb_rows) retire_row(row_id);
            }
            return result;
        }

        SASSERT(lub_index != UINT_MAX);
        SASSERT(glb_index != UINT_MAX);
        if (compute_def) {
            if (lub_size <= glb_size) {
                result = def(m_rows[lub_index], x);
            }
            else {
                result = def(m_rows[glb_index], x);
            }
        }

        // The number of matching lower and upper bounds is small.
        if ((lub_size <= 2 || glb_size <= 2) &&
            (lub_size <= 3 && glb_size <= 3) && 
            (!is_int(x) || lub_is_unit || glb_is_unit)) {
            for (unsigned i = 0; i < lub_size; ++i) {
                unsigned row_id1 = lub_rows[i];
                bool last = i + 1 == lub_size;
                rational coeff = get_coefficient(row_id1, x);
                for (unsigned row_id2 : glb_rows) {
                    if (last) {
                        resolve(row_id1, coeff, row_id2, x);
                    }
                    else {
                        unsigned row_id3 = copy_row(row_id2);
                        resolve(row_id1, coeff, row_id3, x);
                    }
                }
            }
            for (unsigned row_id : lub_rows) retire_row(row_id);

            return result;
        }

        // General case.
        rational coeff = get_coefficient(row_index, x);
        for (unsigned row_id : lub_rows) {
            if (row_id != row_index) {
                resolve(row_index, coeff, row_id, x);
            }
        }
        for (unsigned row_id : glb_rows) {
            if (row_id != row_index) {
                resolve(row_index, coeff, row_id, x);
            }
        }
        retire_row(row_index);
        return result;
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

    model_based_opt::def model_based_opt::solve_mod(unsigned x, unsigned_vector const& mod_rows, bool compute_def) {
        SASSERT(!mod_rows.empty());
        rational D(1);
        for (unsigned idx : mod_rows) {
            D = lcm(D, m_rows[idx].m_mod);            
        }
        if (D.is_zero()) {
            throw default_exception("modulo 0 is not defined");
        }
        TRACE("opt1", display(tout << "lcm: " << D << " x: v" << x << " tableau\n"););
        rational val_x = m_var2value[x];
        rational u = mod(val_x, D);
        SASSERT(u.is_nonneg() && u < D);
        for (unsigned idx : mod_rows) {
            replace_var(idx, x, u);            
            SASSERT(invariant(idx, m_rows[idx]));
            normalize(idx);
        }
        TRACE("opt1", display(tout << "tableau after replace x under mod\n"););
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
        for (unsigned row_id : row_ids) {           
            if (!visited.contains(row_id)) {
                // x |-> D*y + u
                replace_var(row_id, x, D, y, u);
                visited.insert(row_id);
                normalize(row_id);
            }
        }
        TRACE("opt1", display(tout << "tableau after replace x by y := v" << y << "\n"););
        def result = project(y, compute_def);
        if (compute_def) {
            result = (result * D) + u;     
        }
        SASSERT(!compute_def || eval(result) == eval(x));
        return result;
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

    model_based_opt::def model_based_opt::solve_for(unsigned row_id1, unsigned x, bool compute_def) {
        TRACE("opt", tout << "v" << x << "\n" << m_rows[row_id1] << "\n";);
        rational a = get_coefficient(row_id1, x), b;
        ineq_type ty = m_rows[row_id1].m_type;
        SASSERT(!a.is_zero());
        SASSERT(m_rows[row_id1].m_alive);
        if (a.is_neg()) {
            a.neg();
            m_rows[row_id1].neg();
        }
        SASSERT(a.is_pos());
        if (ty == t_lt) {
            SASSERT(compute_def);
            m_rows[row_id1].m_coeff += a;            
        }
        if (m_var2is_int[x] && !a.is_one()) {
            row& r1 = m_rows[row_id1];
            vector<var> coeffs;
            mk_coeffs_without(coeffs, r1.m_vars, x);
            rational c = r1.m_coeff;
            add_divides(coeffs, c, a);
        }
        unsigned_vector const& row_ids = m_var2row_ids[x];
        uint_set visited;
        visited.insert(row_id1);
        for (unsigned row_id2 : row_ids) {
            if (!visited.contains(row_id2)) {                
                visited.insert(row_id2);                
                b = get_coefficient(row_id2, x);
                if (!b.is_zero()) {
                    row& dst = m_rows[row_id2];
                    switch (dst.m_type) {
                    case t_eq:                        
                    case t_lt:
                    case t_le:
                        solve(row_id1, a, row_id2, x);
                        break;
                    case t_mod:
                        // mod reduction already done.
                        UNREACHABLE();
                        break;
                    }
                }
            }
        }
        def result;
        if (compute_def) {
            result = def(m_rows[row_id1], x);
            m_var2value[x] = eval(result);
        }
        retire_row(row_id1);
        return result;
    }
    
    vector<model_based_opt::def> model_based_opt::project(unsigned num_vars, unsigned const* vars, bool compute_def) {
        vector<def> result;
        for (unsigned i = 0; i < num_vars; ++i) {
            result.push_back(project(vars[i], compute_def));
            TRACE("opt", display(tout << "After projecting: v" << vars[i] << "\n"););
        }
        return result;
    }

}

