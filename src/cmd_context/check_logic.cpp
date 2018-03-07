/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    check_logic.cpp

Abstract:

    Check whether a given assertion is in the correct logic or not

Author:

    Leonardo de Moura (leonardo) 2011-08-11.

Revision History:

--*/
#include "cmd_context/check_logic.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include<sstream>

struct check_logic::imp {
    ast_manager & m;
    symbol        m_logic;
    arith_util    m_a_util;
    bv_util       m_bv_util;
    array_util    m_ar_util;
    seq_util      m_seq_util;
    datatype_util m_dt_util;
    pb_util       m_pb_util;
    bool          m_uf;        // true if the logic supports uninterpreted functions
    bool          m_dt;        // true if the lgoic supports dattypes
    bool          m_arrays;    // true if the logic supports arbitrary arrays
    bool          m_bv_arrays; // true if the logic supports only bv arrays
    bool          m_reals;     // true if the logic supports reals
    bool          m_ints;      // true if the logic supports integers
    bool          m_diff;      // true if the logic supports difference logic only
    bool          m_nonlinear; // true if the logic supports nonlinear arithmetic
    bool          m_bvs;       // true if the logic supports bit-vectors
    bool          m_quantifiers; // true if the logic supports quantifiers
    bool          m_unknown_logic;

    imp(ast_manager & _m):m(_m), m_a_util(m), m_bv_util(m), m_ar_util(m), m_seq_util(m), m_dt_util(m), m_pb_util(m) {
        reset();
    }

    void reset() {
        m_uf          = false;
        m_dt          = false;
        m_arrays      = false;
        m_bv_arrays   = false;
        m_reals       = false;
        m_ints        = false;
        m_diff        = false;
        m_nonlinear   = false;
        m_bvs         = false;
        m_quantifiers = false;
        m_unknown_logic = true;
    }

    void set_logic(symbol const & logic) {
        reset();
        m_unknown_logic = false;
        if (logic == "AUFLIA") {
            m_uf     = true;
            m_arrays = true;
            m_ints   = true;
            m_quantifiers = true;
        }
        else if (logic == "AUFLIRA") {
            m_uf     = true;
            m_arrays = true;
            m_reals  = true;
            m_ints   = true;
            m_quantifiers = true;
        }
        else if (logic == "AUFNIRA") {
            m_uf     = true;
            m_arrays = true;
            m_reals  = true;
            m_ints   = true;
            m_nonlinear   = true;
            m_quantifiers = true;
        }
        else if (logic == "LRA") {
            m_reals       = true;
            m_quantifiers = true;
        }
        else if (logic == "QF_ABV") {
            m_bv_arrays = true;
            m_bvs       = true;
        }
        else if (logic == "QF_AUFBV") {
            m_uf        = true;
            m_bv_arrays = true;
            m_bvs       = true;
        }
        else if (logic == "QF_UFBV") {
            m_uf        = true;
            m_bvs       = true;
        }
        else if (logic == "QF_DT") {
            m_uf        = true;            
            m_dt        = true;
        }
        else if (logic == "QF_AUFLIA") {
            m_uf     = true;
            m_arrays = true;
            m_ints   = true;
        }
        else if (logic == "QF_AX") {
            m_arrays = true;
        }
        else if (logic == "QF_BV") {
            m_bvs    = true;
        }
        else if (logic == "QF_IDL") {
            m_ints   = true;
            m_diff   = true;
        }
        else if (logic == "QF_RDL") {
            m_reals  = true;
            m_diff   = true;
        }
        else if (logic == "QF_LIA") {
            m_ints   = true;
        }
        else if (logic == "QF_LRA") {
            m_reals   = true;
        }
        else if (logic == "QF_NIA") {
            m_ints   = true;
            m_nonlinear = true;
        }
        else if (logic == "QF_NRA") {
            m_reals     = true;
            m_nonlinear = true;
        }
        else if (logic == "QF_UF") {
            m_uf = true;
        }
        else if (logic == "QF_UFIDL") {
            m_uf     = true;
            m_ints   = true;
            m_diff   = true;
        }
        else if (logic == "QF_UFLIA") {
            m_uf     = true;
            m_ints   = true;
        }
        else if (logic == "QF_UFLRA") {
            m_uf     = true;
            m_reals  = true;
        }
        else if (logic == "QF_UFNRA") {
            m_uf        = true;
            m_reals     = true;
            m_nonlinear = true;
        }
        else if (logic == "UFLRA") {
            m_uf          = true;
            m_reals       = true;
            m_quantifiers = true;
        }
        else if (logic == "UFNIA") {
            m_uf          = true;
            m_ints        = true;
            m_quantifiers = true;
            m_nonlinear   = true;
        }
        else if (logic == "UFBV") {
            m_uf          = true;
            m_bvs         = true;
            m_quantifiers = true;
        }
        else if (logic == "QF_S") {
            m_uf          = true;
            m_bvs         = true;
            m_ints        = true;
            m_arrays      = true;
            m_reals       = true;
            m_quantifiers = false;
        }
        else if (logic == "QF_FD") {
            m_bvs         = true;
            m_uf          = true;
            m_ints        = true;
            m_dt          = true;
            m_nonlinear   = true; // non-linear 0-1 variables may get eliminated
        }
        else {
            m_unknown_logic = true;
        }

        m_logic = logic;
    }

    struct failed {};
    std::string m_last_error;

    void fail(char const * msg) {
        m_last_error = msg;
        throw failed();
    }

    void check_sort(sort * s) {
        if (s->get_family_id() == null_family_id) {
            if (!m_uf)
                fail("logic does not support uninterpreted sorts");
        }
        else if (m.is_bool(s)) {
            return;
        }
        else if (m_a_util.is_int(s)) {
            if (!m_ints)
                fail("logic does not support integers");
        }
        else if (m_a_util.is_real(s)) {
            if (!m_reals)
                fail("logic does not support reals");
        }
        else if (m_bv_util.is_bv_sort(s)) {
            if (!m_bvs)
                fail("logic does not support bitvectors");
        }
        else if (m_ar_util.is_array(s)) {
            if (m_arrays) {
                return;
            }
            else if (m_bv_arrays) {
                if (get_array_arity(s) != 1)
                    fail("logic supports only unidimensional arrays");
                if (!m_bv_util.is_bv_sort(get_array_range(s)) || !m_bv_util.is_bv_sort(get_array_domain(s, 0)))
                    fail("logic supports only arrays from bitvectors to bitvectors");
            }
            else {
                fail("logic does not support arrays");
            }
        }
    }

    void operator()(var * n) {
        if (!m_quantifiers)
            fail("logic does not support quantifiers");
        check_sort(m.get_sort(n));
    }

    bool is_int(expr * t) {
        if (m_a_util.is_uminus(t))
            t = to_app(t)->get_arg(0);
        // Take care of coercions automatically added by Z3
        if (m_a_util.is_to_real(t))
            t = to_app(t)->get_arg(0);
        return m_a_util.is_numeral(t);
    }

    bool is_numeral(expr * t) {
        if (m_a_util.is_uminus(t))
            t = to_app(t)->get_arg(0);
        // c
        if (is_int(t))
            return true;
        // c1/c2
        if (m_a_util.is_div(t) && is_int(to_app(t)->get_arg(0)) && is_int(to_app(t)->get_arg(1)))
            return true;
        return false;
    }

    // check if n has at most one argument that is not numeral.
    void check_mul(app * n) {
        if (m_nonlinear)
            return; // nothing to check
        unsigned num_args = n->get_num_args();
        bool found_non_numeral = false;
        for (unsigned i = 0; i < num_args; i++) {
            if (!is_numeral(n->get_arg(i))) {
                if (found_non_numeral)
                    fail("logic does not support nonlinear arithmetic");
                else
                    found_non_numeral = true;
            }
        }
    }

    // check if the divisor is a numeral
    void check_div(app * n) {
        SASSERT(n->get_num_args() == 2);
        if (!m_nonlinear && !is_numeral(n->get_arg(1)))
            fail("logic does not support nonlinear arithmetic");
    }

    bool is_diff_var(expr * t) const {
        if (is_app(t) && to_app(t)->get_decl()->get_family_id() == null_family_id)
            return true;
        if (m.is_ite(t))
            return true;
        return false;
    }

    void fail_non_diff(expr * t) {
        TRACE("check_logic", tout << mk_pp(t, m) << "\n";);
        fail("logic only supports difference arithmetic");
    }

    bool same_args(app * t) {
        unsigned num_args = t->get_num_args();
        if (num_args == 0)
            return false;
        expr * arg = t->get_arg(0);
        for (unsigned i = 1; i < num_args; i++) {
            if (t->get_arg(i) != arg)
                return false;
        }
        return true;
    }

    bool is_arith(expr * t) const {
        return m.get_sort(t)->get_family_id() == m_a_util.get_family_id();
    }

    bool is_offset(app * t) {
        while (true) {
            expr * non_numeral = nullptr;
            unsigned num_args = t->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = t->get_arg(i);
                if (is_numeral(arg))
                    continue;
                if (non_numeral != nullptr)
                    return false;
                non_numeral = arg;
            }
            if (non_numeral == nullptr)
                return true;
            if (is_diff_var(non_numeral))
                return true;
            if (!m_a_util.is_add(non_numeral) && !m_a_util.is_sub(non_numeral))
                return false;
            t = to_app(non_numeral);
        }
        return true;
    }

    bool is_diff_arg(expr * t) {
        if (is_diff_var(t))
            return true;
        if (is_numeral(t))
            return true;
        if (m_a_util.is_add(t) || m_a_util.is_sub(t))
            return is_offset(to_app(t));
        return false;
    }

    // Check if n is a diff logic predicate
    void check_diff_predicate(app * n) {
        expr * lhs = n->get_arg(0);
        expr * rhs = n->get_arg(1);
        if (!is_arith(lhs))
            return; // formula is not in arithmetic
        if (is_diff_arg(lhs) && is_diff_arg(rhs))
            return;
        if (is_numeral(lhs))
            std::swap(lhs, rhs);
        if (!is_numeral(rhs))
            fail_non_diff(n);
        if (!m_a_util.is_sub(lhs) || to_app(lhs)->get_num_args() != 2)
            fail_non_diff(n);
        expr * t1 = to_app(lhs)->get_arg(0);
        expr * t2 = to_app(lhs)->get_arg(1);
        if (is_diff_var(t1) && is_diff_var(t2))
            return;
        if (m_a_util.is_add(t1) && m_a_util.is_add(t2)) {
            // QF_RDL supports (<= (- (+ x ... x) (+ y ... y)) c)
            if (to_app(t1)->get_num_args() != to_app(t2)->get_num_args())
                fail_non_diff(n);
            if (!same_args(to_app(t1)) || !same_args(to_app(t2)))
                fail_non_diff(n);
            return;
        }
        fail_non_diff(n);
    }

    void check_diff_arg(expr * t) {
        if (!is_diff_arg(t))
            fail_non_diff(t);
    }

    // Check if the arith args of n are of the form (t + k) where k is a numeral.
    void check_diff_args(app * n) {
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (is_arith(n))
                check_diff_arg(n);
        }
    }

    void operator()(app * n) {
        sort * s = m.get_sort(n);
        check_sort(s);
        func_decl * f = n->get_decl();
        family_id fid = f->get_family_id();
        if (fid == null_family_id) {
            if (!m_uf && f->get_arity() > 0)
                fail("logic does not support uninterpreted functions");
            if (m_diff)
                check_diff_args(n);
        }
        else if (fid == m_a_util.get_family_id()) {
            if (m_a_util.is_mul(n))
                check_mul(n);
            else if (m_a_util.is_div(n) || m_a_util.is_idiv(n) || m_a_util.is_rem(n) || m_a_util.is_mod(n))
                check_div(n);
            if (m_diff) {
                if (m_a_util.is_le(n) || m_a_util.is_lt(n) || m_a_util.is_ge(n) || m_a_util.is_gt(n))
                    check_diff_predicate(n);
            }
            if (!m_ints || !m_reals) {
                if (m_a_util.is_to_real(n) || m_a_util.is_to_int(n))
                    fail("logic does not support casting operators");
            }
        }
        else if (fid == m_bv_util.get_family_id()) {
            // nothing to check...
        }
        else if (fid == m_ar_util.get_family_id()) {
            // nothing to check...
            if (m_diff)
                check_diff_args(n);
        }
        else if (fid == m.get_basic_family_id()) {
            // nothing to check...
            if (m_diff) {
                if (m.is_eq(n))
                    check_diff_predicate(n);
                else if (m.is_distinct(n) || m.is_ite(n))
                    check_diff_args(n);
            }
        }
        else if (m.is_builtin_family_id(fid)) {
            // nothing to check
        }
        else if (fid == m_seq_util.get_family_id()) {
            // nothing to check
        }
        else if (fid == m_dt_util.get_family_id() && m_dt) {
            // nothing to check
        }
        else if (fid == m_pb_util.get_family_id() && m_logic == "QF_FD") {
            // nothing to check
        }
        else {
            std::stringstream strm;
            strm << "logic does not support theory " << m.get_family_name(fid);
            fail(strm.str().c_str());
        }
    }

    void operator()(quantifier * n) {
        if (!m_quantifiers)
            fail("logic does not support quantifiers");
    }

    bool operator()(expr * n) {
        if (m_unknown_logic)
            return true;
        try {
            quick_for_each_expr(*this, n);
            return true;
        }
        catch (failed) {
            return false;
        }
    }

    bool operator()(func_decl * f) {
        if (m_unknown_logic)
            return true;
        try {
            unsigned arity = f->get_arity();
            if (arity > 0) {
                if (!m_uf)
                    fail("logic does not support uninterpreted functions");
                for (unsigned i = 0; i < arity; i++)
                    check_sort(f->get_domain(i));
            }
            check_sort(f->get_range());
            return true;
        }
        catch (failed) {
            return false;
        }
    }
};

check_logic::check_logic() {
    m_imp = nullptr;
}

check_logic::~check_logic() {
    if (m_imp)
        dealloc(m_imp);
}

void check_logic::reset() {
    if (m_imp)
        dealloc(m_imp);
    m_imp = nullptr;
}

void check_logic::set_logic(ast_manager & m, symbol const & logic) {
    reset();
    m_imp = alloc(imp, m);
    m_imp->set_logic(logic);
}

bool check_logic::operator()(expr * n) {
    if (m_imp)
        return m_imp->operator()(n);
    return true;
}

bool check_logic::operator()(func_decl * f) {
    if (m_imp)
        return m_imp->operator()(f);
    return true;
}

char const * check_logic::get_last_error() const {
    if (m_imp)
        return m_imp->m_last_error.c_str();
    return "";
}
