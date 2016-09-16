 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.h

 Abstract:

 A class used to determine bounds on bit-vector variables.
 The satisfiability procedure is polynomial.


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_BOUNDS_H_23754
#define BV_BOUNDS_H_23754
#include"ast.h"
#include"bv_decl_plugin.h"
#include"rewriter_types.h"

/* \brief A class to analyze constraints on bit vectors.

  The objective is to identify inconsistencies in polynomial time.
  All bounds/intervals are closed. Methods that add new constraints
  return false if inconsistency has already been reached.
  Typical usage is to call repeatedly add_constraint(e) and call is_sat() in the end.  
 */
class bv_bounds {
public:
    typedef rational numeral;
    typedef std::pair<numeral, numeral> interval;
    typedef obj_map<app, numeral>       bound_map;
    bv_bounds(ast_manager& m) : m_m(m), m_bv_util(m), m_okay(true) {};
    ~bv_bounds();
public: // bounds addition methods
	br_status rewrite(unsigned limit, func_decl * f, unsigned num, expr * const * args, expr_ref& result);

    /** \brief Add a constraint to the system.

       The added constraints are to be considered by is_sat.
       Currently, only special types of inequalities are supported, e.g. v <= v+1.
       Other constraints are ignored.
       Returns false if the system became trivially unsatisfiable
    **/
    bool add_constraint(expr* e);

    bool bound_up(app * v, numeral u); // v <= u
    bool bound_lo(app * v, numeral l); // l <= v
    inline bool add_neg_bound(app * v, numeral a, numeral b); // not (a<=v<=b)
    bool add_bound_signed(app * v, numeral a, numeral b, bool negate);
    bool add_bound_unsigned(app * v, numeral a, numeral b, bool negate);
public:
    bool is_sat();  ///< Determine if the set of considered constraints is satisfiable.
    bool is_okay();
    const bound_map& singletons() { return m_singletons; }
    bv_util& bvu() { return m_bv_util;  }
    void reset();
protected:
    struct ninterval {
        //ninterval(app * v, numeral lo, numeral hi, bool negated) : v(v), lo(lo), hi(hi), negated(negated) {}
        app * v;
        numeral lo, hi;
        bool negated;
    };
    enum conv_res { CONVERTED, UNSAT, UNDEF };
    conv_res convert(expr * e, vector<ninterval>& nis, bool negated);
    conv_res record(app * v, numeral lo, numeral hi, bool negated, vector<ninterval>& nis);
    conv_res convert_signed(app * v, numeral a, numeral b, bool negate, vector<ninterval>& nis);

    typedef vector<interval>            intervals;
    typedef obj_map<app, intervals*>    intervals_map;
    ast_manager&              m_m;
    bound_map                 m_unsigned_lowers;
    bound_map                 m_unsigned_uppers;
    intervals_map             m_negative_intervals;
    bound_map                 m_singletons;
    bv_util                   m_bv_util;
    bool                      m_okay;
    bool                      is_sat(app * v);
	bool                      is_sat_core(app * v);
    inline bool               in_range(app *v, numeral l);
    inline bool               is_constant_add(unsigned bv_sz, expr * e, app*& v, numeral& val);
    void                      record_singleton(app * v,  numeral& singleton_value);
    inline bool               to_bound(const expr * e) const;
    bool is_uleq(expr * e, expr * &  v, numeral & c);
};


inline bool bv_bounds::is_okay() { return m_okay; }

inline bool bv_bounds::to_bound(const expr * e) const {
	return is_app(e) && m_bv_util.is_bv(e)
       && !m_bv_util.is_bv_add(e)
       && !m_bv_util.is_numeral(e);
}

inline bool bv_bounds::in_range(app *v, bv_bounds::numeral n) {
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    const bv_bounds::numeral zero(0);
    const bv_bounds::numeral mod(rational::power_of_two(bv_sz));
    return (zero <= n) && (n < mod);
}

inline bool bv_bounds::is_constant_add(unsigned bv_sz, expr * e, app*& v, numeral& val) {
    SASSERT(e && !v);
    SASSERT(m_bv_util.get_bv_size(e) == bv_sz);
    expr *lhs(NULL), *rhs(NULL);
    if (!m_bv_util.is_bv_add(e, lhs, rhs)) {
        v = to_app(e);
        val = rational(0);
        return true;
    }
    if (to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) {
        v = to_app(lhs);
        return true;
    }
    if (to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) {
        v = to_app(rhs);
        return true;
    }
    return false;
}


#endif /* BV_BOUNDS_H_23754 */
