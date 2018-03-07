/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_eq.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-22.

Revision History:

--*/
#ifndef THEORY_ARITH_EQ_H_
#define THEORY_ARITH_EQ_H_

// #define PROFILE_OFFSET_ROW

#ifdef PROFILE_OFFSET_ROW
#include "util/stopwatch.h"
#undef max
#undef min
#endif 

namespace smt {

    /**
       \brief This method is invoked when a variable was non fixed and become fixed.
    */
    template<typename Ext>
    void theory_arith<Ext>::fixed_var_eh(theory_var v) {
        if (!propagate_eqs())
            return;

        SASSERT(is_fixed(v));
        // WARNINING: it is not safe to use get_value(v) here, since
        // get_value(v) may not satisfy v bounds at this point.
        CTRACE("arith_bug", !lower_bound(v).is_rational(), display_var(tout, v););
        SASSERT(lower_bound(v).is_rational());
        numeral const & val = lower_bound(v).get_rational();
        value_sort_pair key(val, is_int_src(v));
        TRACE("arith_eq", tout << mk_pp(get_enode(v)->get_owner(), get_manager()) << " = " << val << "\n";);
        theory_var v2;
        if (m_fixed_var_table.find(key, v2)) {
            if (v2 < static_cast<int>(get_num_vars()) && is_fixed(v2) && lower_bound(v2).get_rational() == val) {
                // It only makes sense to propagate equality to the core when v and v2 have the same sort.
                // The table m_fixed_var_table is not restored during backtrack. So, it may
                // contain invalid (key -> value) pairs. So, we must check whether v2 is really equal to val (previous test) AND it has
                // the same sort of v. The following test was missing in a previous version of Z3. 
                if (!is_equal(v, v2) && is_int_src(v) == is_int_src(v2)) {
                    antecedents ante(*this);

                    //
                    // v <= k <= v2  => v <= v2
                    // v >= k >= v2 => v >= v2
                    // 

                    lower(v)->push_justification(ante, numeral::zero(), proofs_enabled());
                    upper(v2)->push_justification(ante, numeral::zero(), proofs_enabled());
                    lower(v2)->push_justification(ante, numeral::zero(), proofs_enabled());
                    upper(v)->push_justification(ante, numeral::zero(), proofs_enabled());

                    TRACE("arith_eq", tout << "propagate eq: v" << v << " = v" << v2 << "\n";
                          display_var(tout, v);
                          display_var(tout, v2););
                    m_stats.m_fixed_eqs++;
                    propagate_eq_to_core(v, v2, ante);
                }
            }
            else {
                // the original fixed variable v2 was deleted or its bounds were removed
                // during backtracking.
                m_fixed_var_table.erase(key);
                m_fixed_var_table.insert(key, v);
            }
        }
        else {
            m_fixed_var_table.insert(key, v);
        }
    }

    /**
       \brief Returns true if r is a offset row.
       A offset row is a row that can be written as:
       
       x = y + M
       
       where x and y are non fixed variables, and 
       M is linear polynomials where all variables are fixed,
       and M evaluates to k.
       When true is returned, x, y and k are stored in the given arguments.
       
       \remark The following rule is used to select x and y.
       - if the base variable is not fixed, then x is the base var.
       - otherwise x is the smallest var.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_offset_row(row const & r, theory_var & x, theory_var & y, numeral & k) const {
#ifdef PROFILE_OFFSET_ROW
        static stopwatch timer;
        static unsigned total = 0;
        static unsigned ok    = 0;
        timer.start();
        total ++;
#endif

        // Quick check without using big numbers...
        // Check if there are more than 2 unbounded vars.
        unsigned bad = 0;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                theory_var v = it->m_var;
                if (lower(v) != nullptr && upper(v) != nullptr)
                    continue;
                bad++;
                if (bad > 2) {
#ifdef PROFILE_OFFSET_ROW
                    timer.stop();
#endif
                    return false;
                }
            }
        }

        // Full check using == for big numbers...
        x = null_theory_var;
        y = null_theory_var;
        it  = r.begin_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                theory_var v = it->m_var;
                if (is_fixed(v))
                    continue;
                if (it->m_coeff.is_one() && x == null_theory_var) {
                    x = v;
                    continue;
                }
                if (it->m_coeff.is_minus_one() && y == null_theory_var) {
                    y = v;
                    continue;
                }
#ifdef PROFILE_OFFSET_ROW
                timer.stop();
#endif
                return false;
            }
        }

        if (x == null_theory_var && y == null_theory_var) {
#ifdef PROFILE_OFFSET_ROW
            timer.stop();
#endif
            return false;
        }

        k.reset();
        it  = r.begin_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                theory_var v = it->m_var;
                if (v == x || v == y)
                    continue;
                SASSERT(is_fixed(v));
                k -= it->m_coeff * lower_bound(v).get_rational();
            }
        }

#ifdef PROFILE_OFFSET_ROW
        timer.stop();
        ok++;
        if (ok % 100000 == 0) {
            TRACE("arith_eq", 
                  tout << total << " " << ok << " " 
                  << static_cast<double>(ok)/static_cast<double>(total) 
                  << " " << timer.get_seconds() << "\n";
                  tout.flush(););
        }
#endif
        
        if (y == null_theory_var)
            return true;

        if (x == null_theory_var) {
            std::swap(x, y);
            k.neg();
            SASSERT(x != null_theory_var);
            return true;
        }

        if (r.get_base_var() != x && x > y) {
            std::swap(x, y);
            k.neg();
        }
        return true;
    }

    
    /**
       \brief Cheap propagation of equalities x_i = x_j, when
       x_i = y + k 
       x_j = y + k

       This equalities are detected by maintaining a map:
       (y, k) ->  row_id   when a row is of the form  x = y + k
 
       This methods checks whether the given row is an offset row (See is_offset_row), 
       and uses the map to find new equalities if that is the case.
    */
    template<typename Ext>
    void theory_arith<Ext>::propagate_cheap_eq(unsigned rid) {
        if (!propagate_eqs())
            return;
        TRACE("arith_eq_verbose", tout << "checking if row " << rid << " can propagate equality.\n";
              display_row_info(tout, rid););
        row const & r = m_rows[rid];
        theory_var x;
        theory_var y;
        numeral k;
        if (is_offset_row(r, x, y, k)) {
            
            if (y == null_theory_var) {
                // x is an implied fixed var at k.
                value_sort_pair key(k, is_int_src(x));
                theory_var x2;
                if (m_fixed_var_table.find(key, x2) && 
                    x2 < static_cast<int>(get_num_vars()) && 
                    is_fixed(x2) && 
                    lower_bound(x2).get_rational() == k &&
                    // We must check whether x2 is an integer. 
                    // The table m_fixed_var_table is not restored during backtrack. So, it may
                    // contain invalid (key -> value) pairs. 
                    // So, we must check whether x2 is really equal to k (previous test) 
                    // AND has the same sort of x.
                    // The following test was missing in a previous version of Z3. 
                    is_int_src(x) == is_int_src(x2) &&
                    !is_equal(x, x2)) {

                    antecedents ante(*this);
                    collect_fixed_var_justifications(r, ante);

                    //
                    // x1 <= k1 x1 >= k1, x2 <= x1 + k2 x2 >= x1 + k2
                    // 
                    TRACE("arith_eq_propagation", tout << "fixed\n";);
                    lower(x2)->push_justification(ante, numeral::zero(), proofs_enabled());
                    upper(x2)->push_justification(ante, numeral::zero(), proofs_enabled());
                    m_stats.m_fixed_eqs++;
                    propagate_eq_to_core(x, x2, ante);
                }
            }

            if (k.is_zero() && y != null_theory_var && !is_equal(x, y) && is_int_src(x) == is_int_src(y)) {
                // found equality x = y
                antecedents ante(*this);
                collect_fixed_var_justifications(r, ante);
                TRACE("arith_eq", tout << "propagate eq using x-y=0 row:\n"; display_row_info(tout, r););
                m_stats.m_offset_eqs++;
                propagate_eq_to_core(x, y, ante);
            }

            int row_id;
            var_offset key(y, k);
            if (m_var_offset2row_id.find(key, row_id)) {
                row & r2 = m_rows[row_id];
                if (r.get_base_var() == r2.get_base_var()) {
                    // it is the same row.
                    return;
                }
                theory_var x2;
                theory_var y2;
                numeral    k2;
                if (r2.get_base_var() != null_theory_var && is_offset_row(r2, x2, y2, k2)) {
                    bool new_eq  = false;
#ifdef _TRACE
                    bool swapped = false;
#endif
                    if (y == y2 && k == k2) {
                        new_eq = true;
                    }
                    else if (y2 != null_theory_var) {
#ifdef _TRACE
                        swapped = true;
#endif
                        std::swap(x2, y2);
                        k2.neg();
                        if (y == y2 && k == k2) {
                            new_eq = true;
                        }
                    }

                    if (new_eq) {
                        if (!is_equal(x, x2) && is_int_src(x) == is_int_src(x2)) {
                            SASSERT(y == y2 && k == k2);
                            antecedents ante(*this);
                            collect_fixed_var_justifications(r, ante);
                            collect_fixed_var_justifications(r2, ante);
                            TRACE("arith_eq", tout << "propagate eq two rows:\n"; 
                                  tout << "swapped: " << swapped << "\n";
                                  tout << "x  : v" << x << "\n";
                                  tout << "x2 : v" << x2 << "\n";
                                  display_row_info(tout, r); 
                                  display_row_info(tout, r2););
                            m_stats.m_offset_eqs++;
                            propagate_eq_to_core(x, x2, ante);
                        }
                        return;
                    }
                }
                // the original row was delete or it is not offset row anymore ===> remove it from table 
                m_var_offset2row_id.erase(key);
            }
            // add new entry
            m_var_offset2row_id.insert(key, rid);
        }
        
    }


    template<typename Ext>
    void theory_arith<Ext>::propagate_eq_to_core(theory_var x, theory_var y, antecedents& antecedents) {
        // Ignore equality if variables are already known to be equal.
        ast_manager& m = get_manager();
        if (is_equal(x, y))
            return;
        // I doesn't make sense to propagate an equality (to the core) of variables of different sort.
        if (m.get_sort(var2expr(x)) != m.get_sort(var2expr(y))) {
            TRACE("arith", tout << mk_pp(var2expr(x), m) << " = " << mk_pp(var2expr(y), m) << "\n";);
            return;
        }
        context & ctx      = get_context();
        region & r         = ctx.get_region();
        enode * _x         = get_enode(x);
        enode * _y         = get_enode(y);
        eq_vector const& eqs = antecedents.eqs();
        literal_vector const& lits = antecedents.lits();
        justification * js = 
            ctx.mk_justification(
                ext_theory_eq_propagation_justification(
                    get_id(), r, 
                    lits.size(), lits.c_ptr(),
                    eqs.size(), eqs.c_ptr(),
                    _x, _y, 
                    antecedents.num_params(), antecedents.params("eq-propagate")));
        TRACE("arith_eq", tout << "detected equality: #" << _x->get_owner_id() << " = #" << _y->get_owner_id() << "\n";
              display_var(tout, x);
              display_var(tout, y););
        TRACE("arith_eq_propagation",
              for (unsigned i = 0; i <  lits.size(); ++i) {
                  ctx.display_detailed_literal(tout, lits[i]);
                  tout << "\n";
              } 
              for (unsigned i = 0; i < eqs.size(); ++i) {
                  tout << mk_pp(eqs[i].first->get_owner(), m) << " = " << mk_pp(eqs[i].second->get_owner(), m) << "\n";
              } 
              tout << " ==> ";
              tout << mk_pp(_x->get_owner(), m) << " = " << mk_pp(_y->get_owner(), m) << "\n";
              );
        ctx.assign_eq(_x, _y, eq_justification(js));
    }
};

#endif /* THEORY_ARITH_EQ_H_ */

