/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ast_smt2_pp.cpp

Abstract:

    Pretty printer of AST formulas using SMT2 format.
    This printer is more expensive than the one in ast_smt_pp.h,
    but is supposed to generated a "prettier" and SMT2 compliant output.

Author:

    Leonardo de Moura (leonardo)

Revision History:

--*/
#include "ast/ast_smt2_pp.h"
#include "ast/shared_occs.h"
#include "ast/pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "math/polynomial/algebraic_numbers.h"
#include "ast/pp_params.hpp"
using namespace format_ns;

#define ALIAS_PREFIX "a"
#define MAX_INDENT   16
#define SMALL_INDENT 2

format * smt2_pp_environment::pp_fdecl_name(symbol const & s, unsigned & len, bool is_skolem) const {
    ast_manager & m = get_manager();
    if (is_smt2_quoted_symbol(s)) {
        std::string str = mk_smt2_quoted_symbol(s);
        len = static_cast<unsigned>(str.length());
        return mk_string(m, str.c_str());
    }
    else if (s.is_numerical()) {
        std::string str = s.str();
        len = static_cast<unsigned>(str.length());
        return mk_string(m, str.c_str());
    }
    else if (!s.bare_str()) {
        len = 4;
        return mk_string(m, "null");
    }
    else {
        len = static_cast<unsigned>(strlen(s.bare_str()));
        return mk_string(m, s.bare_str());
    }
}

format * smt2_pp_environment::pp_fdecl_name(func_decl * f, unsigned & len) const {
    ast_manager & m = get_manager();
    if (m.is_implies(f)) {
        len = 2;
        return mk_string(m, "=>");
    }
    else if (m.is_ite(f)) {
        len = 3;
        return mk_string(m, "ite");
    }
    else if (m.is_iff(f)) {
        len = 1;
        return mk_string(m, "=");
    }
    else {
        symbol s = f->get_name();
        return pp_fdecl_name(s, len, f->is_skolem());
    }
}

bool smt2_pp_environment::is_indexed_fdecl(func_decl * f) const {
    if (f->get_family_id() == null_family_id)
        return false;
    unsigned num = f->get_num_parameters();
    unsigned i;
    for (i = 0; i < num; i++) {
        if (f->get_parameter(i).is_int())
            continue;
        if (f->get_parameter(i).is_rational())
            continue;
        if (f->get_parameter(i).is_ast() && is_func_decl(f->get_parameter(i).get_ast()))
            continue;
        break;
    }
    return i == num && num > 0;
}

bool smt2_pp_environment::is_sort_param(func_decl * f) const {
    return
        f->get_family_id() != null_family_id &&
        f->get_num_parameters() == 1 &&
        f->get_parameter(0).is_ast() &&
        is_sort(f->get_parameter(0).get_ast()) &&
        f->get_range() == to_sort(f->get_parameter(0).get_ast());
}

format * smt2_pp_environment::pp_as(format * fname, sort * s) {
    format * buf[2] = { fname, pp_sort(s) };
    SASSERT(buf[0] != 0 && buf[1] != 0);
    return mk_seq1<format**, f2f>(get_manager(), buf, buf + 2, f2f(), "as");
}

format * smt2_pp_environment::pp_fdecl_params(format * fname, func_decl * f) {
    SASSERT(is_indexed_fdecl(f));
    unsigned num = f->get_num_parameters();
    ptr_buffer<format> fs;
    fs.push_back(fname);
    for (unsigned i = 0; i < num; i++) {
        SASSERT(f->get_parameter(i).is_int() ||
                f->get_parameter(i).is_rational() ||
                (f->get_parameter(i).is_ast() && is_func_decl(f->get_parameter(i).get_ast())));
        if (f->get_parameter(i).is_int())
            fs.push_back(mk_int(get_manager(), f->get_parameter(i).get_int()));
        else if (f->get_parameter(i).is_rational()) {
            std::string str = f->get_parameter(i).get_rational().to_string();
            fs.push_back(mk_string(get_manager(), str.c_str()));
        }
        else
            fs.push_back(pp_fdecl_ref(to_func_decl(f->get_parameter(i).get_ast())));
    }
    return mk_seq1(get_manager(), fs.begin(), fs.end(), f2f(), "_");
}

format * smt2_pp_environment::pp_fdecl(func_decl * f, unsigned & len) {
    format * fname = pp_fdecl_name(f, len);
    if (f->get_family_id() == null_family_id)
        return fname;
    if (is_sort_param(f)) {
        len = UINT_MAX;
        return pp_as(fname, f->get_range());
    }
    if (is_indexed_fdecl(f)) {
        len = UINT_MAX;
        return pp_fdecl_params(fname, f);
    }
    return fname;
}

format * smt2_pp_environment::pp_signature(format * f_name, func_decl * f) {
    if (is_indexed_fdecl(f)) {
        f_name = pp_fdecl_params(f_name, f);
    }
    ptr_buffer<format> f_domain;
    for (unsigned i = 0; i < f->get_arity(); i++)
        f_domain.push_back(pp_sort(f->get_domain(i)));
    ptr_buffer<format> args;
    args.push_back(f_name);
    args.push_back(mk_seq5(get_manager(), f_domain.begin(), f_domain.end(), f2f()));
    args.push_back(pp_sort(f->get_range()));
    return mk_seq5(get_manager(), args.begin(), args.end(), f2f());
}

format * smt2_pp_environment::pp_fdecl_ref(func_decl * f) {
    unsigned len;
    format * f_name = pp_fdecl_name(f, len);
    if (f->get_family_id() == null_family_id) {
        return f_name;
    }
    return pp_signature(f_name, f);
}

format * smt2_pp_environment::pp_bv_literal(app * t, bool use_bv_lits, bool bv_neg) {
    bv_util & u = get_bvutil();
    SASSERT(u.is_numeral(t));
    rational val;
    unsigned bv_size = 1;
    u.is_numeral(t, val, bv_size);
    SASSERT(val.is_int());
    val = u.norm(val, bv_size, bv_neg);
    bool is_neg = false;
    if (val.is_neg()) {
        val.neg();
        is_neg = true;
    }
    SASSERT(val.is_nonneg());
    format * vf;
    if (!use_bv_lits) {
        string_buffer<> buf;
        buf << "(_ bv" << val.to_string().c_str() << " " << bv_size << ")";
        vf = mk_string(get_manager(), buf.c_str());
    }
    else {
        sbuffer<char> buf;
        unsigned sz = 0;
        buf.push_back('#');
        if (bv_size % 4 == 0) {
            buf.push_back('x');
            while (val.is_pos()) {
                rational c = val % rational(16);
                val = div(val, rational(16));
                SASSERT(rational(0) <= c && c < rational(16));
                if (c <= rational(9))
                    buf.push_back('0' + c.get_unsigned());
                else
                    buf.push_back('a' + (c.get_unsigned() - 10));
                sz+=4;
            }
            while (sz < bv_size) {
                buf.push_back('0');
                sz+=4;
            }
        }
        else {
            buf.push_back('b');
            while (val.is_pos()) {
                rational c = val % rational(2);
                val = div(val, rational(2));
                SASSERT(rational(0) <= c && c < rational(2));
                if (c.is_zero())
                    buf.push_back('0');
                else
                    buf.push_back('1');
                sz += 1;
            }
            while (sz < bv_size) {
                buf.push_back('0');
                sz += 1;
            }
        }
        SASSERT(sz == bv_size);
        std::reverse(buf.begin()+2, buf.end());
        buf.push_back(0);
        vf = mk_string(get_manager(), buf.begin());
    }
    if (is_neg) {
        format * buffer[1] = {vf};
        return mk_seq1<format**, f2f>(get_manager(), buffer, buffer+1, f2f(), "bvneg");
    }
    return vf;
}

format * smt2_pp_environment::pp_float_literal(app * t, bool use_bv_lits, bool use_float_real_lits) {
    mpf_manager & fm = get_futil().fm();
    scoped_mpf v(fm);
    ast_manager & m = get_manager();
    format * body = nullptr;
    string_buffer<> buf;
    VERIFY(get_futil().is_numeral(t, v));
    if (fm.is_nan(v)) {
        buf << "(_ NaN " << v.get().get_ebits() << " " << v.get().get_sbits() << ")";
        return mk_string(m, buf.c_str());
    }
    else if (fm.is_pinf(v)) {
        buf << "(_ +oo " << v.get().get_ebits() << " " << v.get().get_sbits() << ")";
        return mk_string(m, buf.c_str());
    }
    else if (fm.is_ninf(v)) {
        buf << "(_ -oo " << v.get().get_ebits() << " " << v.get().get_sbits() << ")";
        return mk_string(m, buf.c_str());
    }
    else if (fm.is_pzero(v)) {
        buf << "(_ +zero " << v.get().get_ebits() << " " << v.get().get_sbits() << ")";
        return mk_string(m, buf.c_str());
    }
    else if (fm.is_nzero(v)) {
        buf << "(_ -zero " << v.get().get_ebits() << " " << v.get().get_sbits() << ")";
        return mk_string(m, buf.c_str());
    }
    else if (use_float_real_lits)
    {
        buf << "((_ to_fp " << v.get().get_ebits() << " " <<
                               v.get().get_sbits() << ") RTZ " <<
                               fm.to_string(v).c_str() << ")";
        return mk_string(m, buf.c_str());
    }
    else {
        if (use_bv_lits)
            buf << "(fp #b" << (fm.sgn(v) ? 1 : 0);
        else
            buf << "(fp (_ bv" << (fm.sgn(v) ? 1 : 0) << " 1)";
        body = mk_string(m, buf.c_str());
        body = mk_compose(m, body, mk_string(m, " "));

        mpf_exp_t exp = fm.exp(v);
        const mpz & bias = fm.m_powers2.m1(v.get().get_ebits() - 1);
        mpf_exp_t biased_exp = exp + fm.mpz_manager().get_int64(bias);
        app_ref e_biased_exp(m);
        e_biased_exp = get_bvutil().mk_numeral(biased_exp, v.get().get_ebits());
        body = mk_compose(m, body, pp_bv_literal(e_biased_exp, use_bv_lits, false));
        body = mk_compose(m, body, mk_string(m, " "));

        scoped_mpz sig(fm.mpz_manager());
        sig = fm.sig(v);
        app_ref e_sig(m);
        e_sig = get_bvutil().mk_numeral(rational(sig), v.get().get_sbits() - 1);
        body = mk_compose(m, body, pp_bv_literal(e_sig, use_bv_lits, false));

        body = mk_compose(m, body, mk_string(m, ")"));
        return body;
    }
}

// generate (- f)
format * smt2_pp_environment::mk_neg(format * f) const {
    format * buffer[1] = {f};
    return mk_seq1<format**, f2f>(get_manager(), buffer, buffer+1, f2f(), "-");
}

// Return the format string  <num>.0  where num is the value of val.
format * smt2_pp_environment::mk_float(rational const & val) const {
    SASSERT(val.is_nonneg());
    SASSERT(val.is_int());
    std::string s = val.to_string();
    s += ".0";
    return mk_string(get_manager(), s.c_str());
}

format * smt2_pp_environment::pp_arith_literal(app * t, bool decimal, unsigned decimal_prec) {
    arith_util & u = get_autil();
    SASSERT(u.is_numeral(t) || u.is_irrational_algebraic_numeral(t));
    rational val;
    bool is_int = true;
    if (u.is_numeral(t, val, is_int)) {
        if (is_int) {
            if (val.is_nonneg()) {
                return mk_string(get_manager(), val.to_string().c_str());
            }
            else {
                val.neg();
                return mk_neg(mk_string(get_manager(), val.to_string().c_str()));
            }
        }
        else {
            bool is_neg = val.is_neg();
            if (is_neg)
                val.neg();
            format * vf;
            if (val.is_int()) {
                vf = mk_float(val);
            }
            else if (decimal) {
                std::ostringstream buffer;
                val.display_decimal(buffer, decimal_prec);
                vf = mk_string(get_manager(), buffer.str().c_str());
            }
            else {
                format * buffer[2] = { mk_float(numerator(val)), mk_float(denominator(val)) };
                vf = mk_seq1<format**, f2f>(get_manager(), buffer, buffer+2, f2f(), "/");
            }
            return is_neg ? mk_neg(vf) : vf;
        }
    }
    else {
        SASSERT(u.is_irrational_algebraic_numeral(t));
        anum const & val2 = u.to_irrational_algebraic_numeral(t);
        algebraic_numbers::manager & am = u.am();
        format * vf;
        std::ostringstream buffer;
        bool is_neg = false;
        if (decimal) {
            scoped_anum abs_val(am);
            am.set(abs_val, val2);
            if (am.is_neg(val2)) {
                is_neg = true;
                am.neg(abs_val);
            }
            am.display_decimal(buffer, abs_val, decimal_prec);
        }
        else {
            am.display_root_smt2(buffer, val2);
        }
        vf = mk_string(get_manager(), buffer.str().c_str());
        return is_neg ? mk_neg(vf) : vf;
    }
}

format * smt2_pp_environment::pp_string_literal(app * t) {
    zstring s;
    std::string encs;
    VERIFY (get_sutil().str.is_string(t, s));
    encs = s.encode();
    std::ostringstream buffer;
    buffer << "\"";
    for (unsigned i = 0; i < encs.length(); ++i) {
        if (encs[i] == '\"') {
            buffer << "\"\"";
        }
        else {
            buffer << encs[i];
        }
    }
    buffer << "\"";
    return mk_string(get_manager(), buffer.str().c_str());
}

format * smt2_pp_environment::pp_datalog_literal(app * t) {
    uint64_t v;
    VERIFY (get_dlutil().is_numeral(t, v));
    std::ostringstream buffer;
    buffer << v;
    return mk_string(get_manager(), buffer.str().c_str());
}

format_ns::format * smt2_pp_environment::pp_sort(sort * s) {
    // Basic sort pretty printing.
    // This method is redefined in cmd_context::pp_env: support for parametric sorts.
    // Here, we just pretty print builtin sorts: Bool, Int, Real, BitVec and Array.
    ast_manager & m = get_manager();
    if (m.is_bool(s))
        return mk_string(m, "Bool");
    if (get_autil().is_int(s))
        return mk_string(m, "Int");
    if (get_autil().is_real(s))
        return mk_string(m, "Real");
    if (get_bvutil().is_bv_sort(s)) {
        unsigned sz = get_bvutil().get_bv_size(s);
        ptr_buffer<format> fs;
        fs.push_back(mk_string(m, "BitVec"));
        fs.push_back(mk_unsigned(m, sz));
        return mk_seq1(m, fs.begin(), fs.end(), f2f(), "_");
    }
    if (get_arutil().is_array(s)) {
        ptr_buffer<format> fs;
        unsigned sz = get_array_arity(s);
        for (unsigned i = 0; i < sz; i++) {
            fs.push_back(pp_sort(get_array_domain(s, i)));
        }
        fs.push_back(pp_sort(get_array_range(s)));
        return mk_seq1(m, fs.begin(), fs.end(), f2f(), "Array");
    }
    if (get_futil().is_float(s)) {
        unsigned ebits = get_futil().get_ebits(s);
        unsigned sbits = get_futil().get_sbits(s);
        ptr_buffer<format> fs;
        fs.push_back(mk_string(m, "FloatingPoint"));
        fs.push_back(mk_unsigned(m, ebits));
        fs.push_back(mk_unsigned(m, sbits));
        return mk_seq1(m, fs.begin(), fs.end(), f2f(), "_");
    }
    if ((get_sutil().is_seq(s) || get_sutil().is_re(s)) && !get_sutil().is_string(s)) {
        ptr_buffer<format> fs;
        fs.push_back(pp_sort(to_sort(s->get_parameter(0).get_ast())));
        return mk_seq1(m, fs.begin(), fs.end(), f2f(), get_sutil().is_seq(s)?"Seq":"RegEx");
    }
    if (get_dtutil().is_datatype(s)) {
        unsigned sz = get_dtutil().get_datatype_num_parameter_sorts(s);
        if (sz > 0) {
            ptr_buffer<format> fs;            
            for (unsigned i = 0; i < sz; i++) {
                fs.push_back(pp_sort(get_dtutil().get_datatype_parameter_sort(s, i)));
            }
            return mk_seq1(m, fs.begin(), fs.end(), f2f(), s->get_name().str().c_str());        
        }
    }
    return format_ns::mk_string(get_manager(), s->get_name().str().c_str());
}

typedef app_ref_vector format_ref_vector;

class smt2_printer {
    ast_manager &                         m_manager;
    smt2_pp_environment &                 m_env;

    shared_occs                           m_soccs;
    expr *                                m_root;

    typedef obj_map<expr, unsigned>       expr2alias; // expr -> position @ m_aliased_exprs, m_aliased_pps, m_aliased_lvls_names.
    ptr_vector<expr2alias>                m_expr2alias_stack;

    expr2alias *                          m_expr2alias; // expr -> position @ m_aliased_exprs, m_aliased_pps, m_aliased_lvls_names.
    ptr_vector<expr>                      m_aliased_exprs;
    format_ref_vector                     m_aliased_pps;
    svector<std::pair<unsigned, symbol> > m_aliased_lvls_names;
    unsigned                              m_next_alias_idx;
    struct scope {
        unsigned m_aliased_exprs_lim;
        unsigned m_old_next_alias_idx;
        expr *   m_old_root;
        scope(unsigned lim, unsigned idx, expr * r):m_aliased_exprs_lim(lim), m_old_next_alias_idx(idx), m_old_root(r) {}
    };
    svector<scope>                        m_scopes;     // size of m_aliased_exprs, m_aliased_pps, m_aliased_lvls_names.
    svector<symbol>                       m_var_names;
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
    symbol_set                            m_var_names_set;

    struct frame {
        expr *   m_curr;
        unsigned m_idx;
        unsigned m_spos;
        bool     m_use_alias; // if new aliases can be created
        frame(expr * c, unsigned i, unsigned s, bool use_alias):m_curr(c), m_idx(i), m_spos(s), m_use_alias(use_alias) {}
    };

    svector<frame>                        m_frame_stack;
    format_ref_vector                     m_format_stack;
    struct info {
        unsigned m_lvl;
        unsigned m_weight;
        unsigned m_depth;
        info(unsigned l, unsigned w, unsigned d):m_lvl(l), m_weight(w), m_depth(d) {}
    };
    svector<info>                         m_info_stack;

    string_buffer<> m_next_name_buffer;

    // Config
    bool     m_pp_decimal;
    unsigned m_pp_decimal_precision;
    bool     m_pp_bv_lits;
    bool     m_pp_float_real_lits;
    bool     m_pp_bv_neg;
    unsigned m_pp_max_depth;
    unsigned m_pp_min_alias_size;
    bool     m_pp_flat_assoc;


    symbol next_name(char const * prefix, unsigned & idx) {
        while (true) {
            m_next_name_buffer.reset();
            m_next_name_buffer.append(prefix);
            m_next_name_buffer.append("!");
            m_next_name_buffer.append(idx);
            symbol r(m_next_name_buffer.c_str());
            idx++;
            if (m_env.uses(r))
                continue;
            if (m_var_names_set.contains(r))
                continue;
            return r;
        }
    }

    symbol next_alias() {
        return next_name(ALIAS_PREFIX, m_next_alias_idx);
    }

    void register_alias(expr * n, format * nf, unsigned lvl, symbol const & name) {
        SASSERT(m_aliased_exprs.size() == m_aliased_pps.size());
        SASSERT(m_aliased_exprs.size() == m_aliased_lvls_names.size());
        unsigned idx = m_aliased_exprs.size();
        m_expr2alias->insert(n, idx);
        m_aliased_exprs.push_back(n);
        m_aliased_pps.push_back(nf);
        m_aliased_lvls_names.push_back(std::make_pair(lvl, name));
    }

    void push_frame(expr * n, bool use_alias) {
        m_frame_stack.push_back(frame(n, 0, m_format_stack.size(), use_alias));
    }

    void pop_frame() {
        m_frame_stack.pop_back();
    }

    ast_manager & m() const { return m_manager; }
    ast_manager & fm() const { return format_ns::fm(m()); }

    std::string ensure_quote(symbol const& s) {
        std::string str;
        if (is_smt2_quoted_symbol(s))
            str = mk_smt2_quoted_symbol(s);
        else
            str = s.str();
        return str;
    }

    symbol ensure_quote_sym(symbol const& s) {
        if (is_smt2_quoted_symbol(s)) {
            std::string str;
            str = mk_smt2_quoted_symbol(s);
            return symbol(str.c_str());
        }
        else
            return s;
    }

    void pp_var(var * v) {
        format * f;
        if (v->get_idx() < m_var_names.size()) {
            symbol s = m_var_names[m_var_names.size() - v->get_idx() - 1];
            std::string vname;
            if (is_smt2_quoted_symbol (s)) {
                vname = mk_smt2_quoted_symbol (s);
            }
            else {
                vname = s.str();
            }
            f = mk_string(m(), vname.c_str ());
        }
        else {
            // fallback... it is not supposed to happen when the printer is correctly used.
            string_buffer<> buf;
            buf.append("(:var ");
            buf.append(v->get_idx());
            //buf.append(" ");
            //buf.append(v->get_sort()->get_name().str().c_str());
            buf.append(")");
            f = mk_string(m(), buf.c_str());
        }
        m_format_stack.push_back(f);
        m_info_stack.push_back(info(0, 1, 1));
    }

    format * pp_attribute(char const * attr, format * f) {
        return mk_compose(m(),
                          mk_string(m(), attr),
                          mk_indent(m(), static_cast<unsigned>(strlen(attr)), f));
    }

    format * pp_simple_attribute(char const * attr, int v) {
        return mk_compose(m(), mk_string(m(), attr), mk_int(m(), v));
    }

    format * pp_simple_attribute(char const * attr, symbol const & s) {
        std::string str = ensure_quote(s);
        return mk_compose(m(), mk_string(m(), attr), mk_string(m(), str.c_str()));
    }

    format * pp_labels(bool is_pos, buffer<symbol> const & names, format * f) {
        if (names.empty())
            return f;
        ptr_buffer<format> buf;
        buf.push_back(f);
        for (symbol const& n : names) 
            buf.push_back(pp_simple_attribute(is_pos ? ":lblpos " : ":lblneg ", n));

        return mk_seq1(m(), buf.begin(), buf.end(), f2f(), "!");
    }

    void pp_const(app * c) {
        format * f;
        if (m_env.get_autil().is_numeral(c) || m_env.get_autil().is_irrational_algebraic_numeral(c)) {
            f = m_env.pp_arith_literal(c, m_pp_decimal, m_pp_decimal_precision);
        }
        else if (m_env.get_sutil().str.is_string(c)) {
            f = m_env.pp_string_literal(c);
        }
        else if (m_env.get_bvutil().is_numeral(c)) {
            f = m_env.pp_bv_literal(c, m_pp_bv_lits, m_pp_bv_neg);
        }
        else if (m_env.get_futil().is_numeral(c)) {
            f = m_env.pp_float_literal(c, m_pp_bv_lits, m_pp_float_real_lits);
        }
        else if (m_env.get_dlutil().is_numeral(c)) {
            f = m_env.pp_datalog_literal(c);
        }
        else {
            buffer<symbol> names;
            if (m().is_label_lit(c, names)) {
                f = pp_labels(true, names, mk_string(m(), "true"));
            }
            else {
                unsigned len;
                f = m_env.pp_fdecl(c->get_decl(), len);
            }
        }
        m_format_stack.push_back(f);
        m_info_stack.push_back(info(0, 1, 1));
    }

    bool pp_aliased(expr * t) {
        unsigned idx;
        if (m_expr2alias->find(t, idx)) {
            unsigned lvl     = m_aliased_lvls_names[idx].first;
            symbol const & s = m_aliased_lvls_names[idx].second;
            m_format_stack.push_back(mk_string(m(), s.str().c_str()));
            m_info_stack.push_back(info(lvl+1, 1, 1));
            return true;
        }
        return false;
    }

    void process_var(var * v) {
        pp_var(v);
        pop_frame();
    }

    bool process_args(app * t, frame & fr) {
        unsigned num = t->get_num_args();
        while (fr.m_idx < num) {
            expr * arg = t->get_arg(fr.m_idx);
            fr.m_idx++;
            if (pp_aliased(arg))
                continue;
            switch (arg->get_kind()) {
            case AST_VAR:
                pp_var(to_var(arg));
                break;
            case AST_APP:
                if (to_app(arg)->get_num_args() == 0) {
                    pp_const(to_app(arg));
                }
                else {
                    push_frame(arg, fr.m_use_alias);
                    return false;
                }
                break;
            case AST_QUANTIFIER:
                push_frame(arg, fr.m_use_alias);
                return false;
            default:
                UNREACHABLE();
            }
        }
        return true;
    }

    void store_result(expr * t, frame & fr, format * f, info & f_info) {
        m_format_stack.shrink(fr.m_spos);
        m_info_stack.shrink(fr.m_spos);
        if (fr.m_use_alias && m_root != t &&
            ((f_info.m_depth >= m_pp_max_depth) ||
             ((f_info.m_weight >= m_pp_min_alias_size || is_quantifier(t)) && m_soccs.is_shared(t)))) {
            symbol a = next_alias();
            TRACE("smt2_pp", tout << "a: " << a << " depth: " << f_info.m_depth << ", weight: " << f_info.m_weight
                  << ", lvl: " << f_info.m_lvl << " t: #" << t->get_id() << "\n" << mk_ll_pp(t, m())
                  << ", is-shared: " << m_soccs.is_shared(t) << "\n";);
            register_alias(t, f, f_info.m_lvl, a);
            m_format_stack.push_back(mk_string(m(), a.str().c_str()));
            m_info_stack.push_back(info(f_info.m_lvl + 1, 1, 1));
        }
        else {
            m_format_stack.push_back(f);
            m_info_stack.push_back(f_info);
        }
        pop_frame();
    }

    bool flat_assoc(app * t, frame const & fr) {
        if (!m_pp_flat_assoc)
            return false;
        func_decl * f = t->get_decl();
        if (f->is_associative() && m_frame_stack.size() >= 2 && !m_soccs.is_shared(t)) {
            frame const & prev_fr = m_frame_stack[m_frame_stack.size() - 2];
            return is_app(prev_fr.m_curr) && to_app(prev_fr.m_curr)->get_decl() == f;
        }
        return false;
    }

    void process_app(app * t, frame & fr) {
        if (fr.m_idx == 0) {
            if (pp_aliased(t)) {
                pop_frame();
                return;
            }
        }
        if (!process_args(t, fr))
            return;
        if (t->get_num_args() == 0) {
            pp_const(t);
            pop_frame();
            return;
        }
        if (flat_assoc(t, fr)) {
            pop_frame();
            return;
        }
        buffer<symbol> labels;
        bool is_pos;
        format * f = nullptr;
        format ** it  = m_format_stack.c_ptr() + fr.m_spos;
        format ** end = m_format_stack.c_ptr() + m_format_stack.size();
        if (m().is_label(t, is_pos, labels)) {
            SASSERT(it + 1 == end);
            f = pp_labels(is_pos, labels, *it);
        }
        else if (m().is_pattern(t)) {
            f = mk_seq5<format**, f2f>(m(), it, end, f2f());
        }
        else {
            unsigned len;
            SASSERT(it < end);
            format * fname = m_env.pp_fdecl(t->get_decl(), len);
            if (len > MAX_INDENT) {
                f = mk_group(m(), mk_compose(m(),
                                             mk_indent(m(), 1, mk_compose(m(), mk_string(m(), "("), fname)),
                                             mk_indent(m(), SMALL_INDENT, mk_compose(m(),
                                                                                     mk_seq<format**, f2f>(m(), it, end, f2f()),
                                                                                     mk_string(m(), ")")))));
            }
            else {
                format * first = *it;
                ++it;
                f = mk_group(m(), mk_compose(m(),
                                             mk_indent(m(), 1, mk_compose(m(), mk_string(m(), "("), fname)),
                                             mk_indent(m(), len + 2, mk_compose(m(),
                                                                                mk_string(m(), " "),
                                                                                first,
                                                                                mk_seq<format**, f2f>(m(), it, end, f2f()),
                                                                                mk_string(m(), ")")))));
            }
        }
        info f_info(0, 1, 1);
        info * it2  = m_info_stack.begin() + fr.m_spos;
        info * end2 = m_info_stack.end();
        for (; it2 != end2; ++it2) {
            if (it2->m_lvl > f_info.m_lvl)
                f_info.m_lvl = it2->m_lvl;
            f_info.m_weight += it2->m_weight;
            if (it2->m_depth > f_info.m_depth)
                f_info.m_depth = it2->m_depth;
        }
        f_info.m_depth++;
        store_result(t, fr, f, f_info);
    }

    // Add let decls used to build f.
    format * pp_let(format * f, unsigned & num_lets) {
        unsigned old_sz = m_scopes.empty() ? 0 : m_scopes.back().m_aliased_exprs_lim;
        unsigned sz     = m_aliased_exprs.size();
        SASSERT(old_sz <= sz);
        num_lets = sz - old_sz;
        TRACE("pp_let", tout << "old_sz: " << old_sz << ", sz: " << sz << "\n";);
        if (old_sz == sz)
            return f;
        vector<ptr_vector<format> > decls;
        for (unsigned i = old_sz; i < sz; i++) {
            unsigned lvl    = m_aliased_lvls_names[i].first;
            symbol   f_name = m_aliased_lvls_names[i].second;
            format * f_def[1] = { m_aliased_pps.get(i) };
            decls.reserve(lvl+1);
            ptr_vector<format> & lvl_decls = decls[lvl];
            lvl_decls.push_back(mk_seq1<format**, f2f>(m(), f_def, f_def+1, f2f(), f_name.str().c_str()));
        }
        TRACE("pp_let", tout << "decls.size(): " << decls.size() << "\n";);
        ptr_buffer<format> buf;
        unsigned num_op = 0;
        vector<ptr_vector<format> >::iterator it  = decls.begin();
        vector<ptr_vector<format> >::iterator end = decls.end();
        for (; it != end; ++it) {
            ptr_vector<format> & lvl_decls = *it;
            if (lvl_decls.empty())
                continue;
            if (num_op > 0)
                buf.push_back(mk_line_break(m()));
            num_op++;
            buf.push_back(mk_string(m(), "(let "));
            buf.push_back(mk_indent(m(), 5, mk_seq5(m(), lvl_decls.begin(), lvl_decls.end(), f2f())));
        }
        TRACE("pp_let", tout << "num_op: " << num_op << "\n";);
        if (num_op == 0)
            return f;
        buf.push_back(mk_indent(m(), SMALL_INDENT, mk_compose(m(), mk_line_break(m()), f)));
        for (unsigned i = 0; i < num_op; i++)
            buf.push_back(mk_string(m(), ")"));
        return mk_compose(m(), buf.size(), buf.c_ptr());
    }

    format * pp_let(format * f) {
        unsigned num_lets;
        return pp_let(f, num_lets);
    }

    void begin_scope() {
        SASSERT(m_aliased_exprs.size() == m_aliased_pps.size());
        SASSERT(m_aliased_exprs.size() == m_aliased_lvls_names.size());
        TRACE("pp_scope", tout << "[begin-scope] sz: " << m_aliased_exprs.size() << ", m_root: " << m_root << "\n";);
        m_scopes.push_back(scope(m_aliased_exprs.size(), m_next_alias_idx, m_root));
        unsigned lvl = m_scopes.size();
        while (lvl >= m_expr2alias_stack.size())
            m_expr2alias_stack.push_back(alloc(expr2alias));
        m_expr2alias = m_expr2alias_stack[lvl];
        m_next_alias_idx = 1;
    }

    void end_scope() {
        TRACE("pp_scope", tout << "[end-scope] before sz: " << m_aliased_exprs.size() << ", m_root: " << m_root << "\n";);
        m_expr2alias->reset();
        scope & s = m_scopes.back();
        unsigned old_sz = s.m_aliased_exprs_lim;
        m_root = s.m_old_root;
        m_next_alias_idx = s.m_old_next_alias_idx;
        m_scopes.pop_back();
        unsigned new_lvl = m_scopes.size();
        m_expr2alias = m_expr2alias_stack[new_lvl];
        SASSERT(old_sz <= m_aliased_exprs.size());
        m_aliased_exprs.shrink(old_sz);
        m_aliased_pps.shrink(old_sz);
        m_aliased_lvls_names.shrink(old_sz);
        TRACE("pp_scope", tout << "[end-scope] after sz: " << m_aliased_exprs.size() << ", m_root: " << m_root << "\n";);
    }

    void register_var_names(quantifier * q) {
        unsigned num_decls = q->get_num_decls();
        for (unsigned i = 0; i < num_decls; i++) {
            symbol name = ensure_quote_sym(q->get_decl_name(i));
            if (name.is_numerical()) {
                unsigned idx = 1;
                name = next_name("x", idx);
            }
            else if (m_env.uses(name) || m_var_names_set.contains(name)) {
                unsigned idx = 1;
                name = next_name(name.bare_str(), idx);
            }
            SASSERT(!m_var_names_set.contains(name));
            m_var_names.push_back(name);
            m_var_names_set.insert(name);
        }
    }

    void register_var_names(unsigned n) {
        unsigned idx = 1;
        for (unsigned i = 0; i < n; i++) {
            symbol name = next_name("x", idx);            
            SASSERT(!m_var_names_set.contains(name));
            m_var_names.push_back(name);
            m_var_names_set.insert(name);
        }
    }

    void unregister_var_names(quantifier * q) {
        unregister_var_names(q->get_num_decls());
    }

    void unregister_var_names(unsigned num_decls) {
        for (unsigned i = 0; i < num_decls; i++) {
            symbol s = m_var_names.back();
            m_var_names.pop_back();
            m_var_names_set.erase(s);
        }
    }

    format * pp_var_args(unsigned num_decls, sort* const* srts) {
        ptr_buffer<format> buf;
        SASSERT(num_decls <= m_var_names.size());
        symbol * it = m_var_names.end() - num_decls;
        for (unsigned i = 0; i < num_decls; i++, it++) {
            format * fs[1] = { m_env.pp_sort(srts[i]) };
            std::string var_name;
            if (is_smt2_quoted_symbol (*it)) {
                var_name = mk_smt2_quoted_symbol (*it);
            }
            else {
                var_name = it->str ();          
            }
            buf.push_back(mk_seq1<format**,f2f>(m(), fs, fs+1, f2f(), var_name.c_str ()));
        }
        return mk_seq5(m(), buf.begin(), buf.end(), f2f());
    }

    format * pp_var_decls(quantifier * q) {
        return pp_var_args(q->get_num_decls(), q->get_decl_sorts());
    }

    void process_quantifier(quantifier * q, frame & fr) {
        if (fr.m_idx == 0) {
            begin_scope();
            m_root = q->get_expr();
            register_var_names(q);
        }
        unsigned num_children = q->get_num_patterns() + q->get_num_no_patterns() + 1;
        if (fr.m_idx < num_children) {
            unsigned idx = fr.m_idx;
            fr.m_idx++;
            if (idx < q->get_num_patterns()) {
                push_frame(q->get_pattern(idx), false);
            }
            else if (idx < q->get_num_patterns() + q->get_num_no_patterns()) {
                push_frame(q->get_no_pattern(idx - q->get_num_patterns()), false);
            }
            else {
                push_frame(q->get_expr(), fr.m_use_alias);
            }
            return;
        }
        unsigned num_lets = 0;
        format * f_body = pp_let(m_format_stack.back(), num_lets);
        // The current SMT2 frontend uses weight 1 as default.
#define MIN_WEIGHT 1
        if (q->has_patterns() || q->get_weight() > MIN_WEIGHT ||
            q->get_skid() != symbol::null || (q->get_qid() != symbol::null && !q->get_qid().is_numerical())) {
            ptr_buffer<format> buf;
            buf.push_back(f_body);
            if (q->get_num_patterns() > 0) {
                format ** it  = m_format_stack.c_ptr() + fr.m_spos;
                format ** end = it + q->get_num_patterns();
                for (; it != end; ++it) {
                    buf.push_back(pp_attribute(":pattern ", *it));
                }
            }
            if (q->get_num_no_patterns() > 0) {
                format ** it  = m_format_stack.c_ptr() + fr.m_spos + q->get_num_patterns();
                format ** end = it + q->get_num_no_patterns();
                for (; it != end; ++it) {
                    buf.push_back(pp_attribute(":no-pattern ", *it));
                }
            }
            if (q->get_weight() > MIN_WEIGHT) {
                buf.push_back(pp_simple_attribute(":weight ", q->get_weight()));
            }
            if (q->get_skid() != symbol::null) {
                buf.push_back(pp_simple_attribute(":skolemid ", q->get_skid()));
            }
            if (q->get_qid() != symbol::null) {
#if 0
                buf.push_back(pp_simple_attribute(":qid ", q->get_qid()));
#else
                if (!q->get_qid().is_numerical())
                    buf.push_back(pp_simple_attribute(":qid ", q->get_qid()));
#endif
            }
            f_body = mk_seq1(m(), buf.begin(), buf.end(), f2f(), "!");
        }
        format * f_decls = pp_var_decls(q);
        format * fs[2] = { f_decls, f_body };
        char const * header = q->is_forall() ? "forall" : "exists";
        format * f = mk_seq3<format**, f2f>(m(), fs, fs+2, f2f(), header, 1, SMALL_INDENT);

        info f_info = m_info_stack.back();
        f_info.m_lvl     = 0; // quantifiers don't depend on any let-decls, pp_let added all dependencies for the body.
        f_info.m_depth++;
        f_info.m_weight += q->get_num_decls()*2 + num_lets*8;

        unregister_var_names(q);
        end_scope();

        store_result(q, fr, f, f_info);
    }

    void init_expr2alias_stack() {
        SASSERT(m_expr2alias_stack.empty());
        expr2alias * new_map = alloc(expr2alias);
        m_expr2alias_stack.push_back(new_map);
        m_expr2alias = new_map;
    }

    void del_expr2alias_stack() {
        std::for_each(m_expr2alias_stack.begin(), m_expr2alias_stack.end(), delete_proc<expr2alias>());
        m_expr2alias_stack.reset();
        m_expr2alias = nullptr;
    }

    void reset_expr2alias_stack() {
        SASSERT(!m_expr2alias_stack.empty());
        for (expr2alias * e : m_expr2alias_stack) 
            e->reset();
        m_expr2alias = m_expr2alias_stack[0];
    }

    void reset_stacks() {
        m_next_alias_idx = 1;
        reset_expr2alias_stack();
        m_aliased_exprs.reset();
        m_aliased_pps.reset();
        m_aliased_lvls_names.reset();
        m_scopes.reset();
        m_frame_stack.reset();
        m_format_stack.reset();
        m_info_stack.reset();
    }

    void process(expr * n, format_ref & r) {
        reset_stacks();
        SASSERT(&(r.get_manager()) == &(fm()));
        m_soccs(n);
        m_root = n;
        push_frame(n, true);
        while (!m_frame_stack.empty()) {
            frame & fr = m_frame_stack.back();
            switch (fr.m_curr->get_kind()) {
            case AST_QUANTIFIER:
                process_quantifier(to_quantifier(fr.m_curr), fr);
                break;
            case AST_APP:
                process_app(to_app(fr.m_curr), fr);
                break;
            case AST_VAR:
                process_var(to_var(fr.m_curr));
                break;
            default:
                UNREACHABLE();
            }
        }
        r = pp_let(m_format_stack.back());
        m_format_stack.pop_back();
    }

    void reset_var_names() {
        m_var_names.reset();
        m_var_names_set.reset();
    }

public:
    smt2_printer(smt2_pp_environment & env, params_ref const & params):
        m_manager(env.get_manager()),
        m_env(env),
        m_soccs(m_manager),
        m_root(nullptr),
        m_aliased_pps(fm()),
        m_next_alias_idx(1),
        m_format_stack(fm()) {
        init_expr2alias_stack();

        pp_params p(params);
        m_pp_decimal = p.decimal();
        m_pp_decimal_precision = p.decimal_precision();
        m_pp_bv_lits = p.bv_literals();
        m_pp_float_real_lits = p.fp_real_literals();
        m_pp_bv_neg  = p.bv_neg();
        m_pp_max_depth = p.max_depth();
        m_pp_min_alias_size = p.min_alias_size();
        m_pp_flat_assoc = p.flat_assoc();
    }

    ~smt2_printer() {
        del_expr2alias_stack();
    }

    void operator()(expr * n, format_ref & r) {
        reset_var_names();
        process(n, r);
    }

    void operator()(expr * n, unsigned num, char const * var_prefix, format_ref & r, sbuffer<symbol> & var_names) {
        reset_var_names();
        if (var_prefix == nullptr)
            var_prefix = "x";
        if (strcmp(var_prefix, ALIAS_PREFIX) == 0) {
            var_prefix = "_a";
        }
        unsigned idx = 0;
        for (unsigned i = 0; i < num; i++) {
            symbol name = next_name(var_prefix, idx);
            name = ensure_quote_sym(name);
            var_names.push_back(name);
            m_var_names_set.insert(name);
            m_var_names.push_back(name);
        }
        std::reverse(m_var_names.begin(), m_var_names.end());
        process(n, r);
    }

    void operator()(sort * s, format_ref & r) {
        r = m_env.pp_sort(s);
    }

    void operator()(func_decl * f, format_ref & r, char const* cmd) {
        unsigned arity = f->get_arity();
        unsigned len;
        format * fname = m_env.pp_fdecl_name(f, len);
        format * args[3];
        args[0] = fname;
        ptr_buffer<format> buf;
        for (unsigned i = 0; i < arity; i++) {
            buf.push_back(m_env.pp_sort(f->get_domain(i)));
        }
        args[1] = mk_seq5<format**, f2f>(m(), buf.begin(), buf.end(), f2f());
        args[2] = m_env.pp_sort(f->get_range());
        r = mk_seq1<format**, f2f>(m(), args, args+3, f2f(), cmd); 
    }


    void operator()(func_decl * f, expr * e, format_ref & r, char const* cmd) {
        unsigned len;
        format * fname = m_env.pp_fdecl_name(f, len);
        register_var_names(f->get_arity());        
        format * args[4];
        args[0] = fname;
        args[1] = pp_var_args(f->get_arity(), f->get_domain());
        args[2] = m_env.pp_sort(f->get_range());
        process(e, r);
        args[3] = r;
        r = mk_seq1<format**, f2f>(m(), args, args+4, f2f(), cmd); 
        unregister_var_names(f->get_arity());
    }



};

void mk_smt2_format(expr * n, smt2_pp_environment & env, params_ref const & p,
                    unsigned num_vars, char const * var_prefix,
                    format_ref & r, sbuffer<symbol> & var_names) {
    smt2_printer pr(env, p);
    pr(n, num_vars, var_prefix, r, var_names);
}

void mk_smt2_format(sort * s, smt2_pp_environment & env, params_ref const & p, format_ref & r) {
    smt2_printer pr(env, p);
    pr(s, r);
}

void mk_smt2_format(func_decl * f, smt2_pp_environment & env, params_ref const & p, format_ref & r, char const* cmd) {
    smt2_printer pr(env, p);
    pr(f, r, cmd);
}

void mk_smt2_format(func_decl * f, expr * e, smt2_pp_environment & env, params_ref const & p, format_ref & r, char const* cmd) {
    smt2_printer pr(env, p);
    pr(f, e, r, cmd);
}

void mk_smt2_format(unsigned sz, expr * const* es, smt2_pp_environment & env, params_ref const & p,
                    unsigned num_vars, char const * var_prefix,
                    format_ref & r, sbuffer<symbol> & var_names) {
    smt2_printer pr(env, p);
    ast_manager & m = env.get_manager();
    
    format_ref_vector fmts(fm(m));
    for (unsigned i = 0; i < sz; ++i) {
        format_ref fr(fm(m));
        pr(es[i], num_vars, var_prefix, fr, var_names);
        fmts.push_back(fr);
    }
    r = mk_seq<format**, f2f>(m, fmts.c_ptr(), fmts.c_ptr() + fmts.size(), f2f());
}

std::ostream & ast_smt2_pp(std::ostream & out, expr * n, smt2_pp_environment & env, params_ref const & p, unsigned indent,
                            unsigned num_vars, char const * var_prefix) {
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(n, env, p, num_vars, var_prefix, r, var_names);
    if (indent > 0)
        r = mk_indent(m, indent, r.get());
    pp(out, r.get(), m, p);
    return out;
}

std::ostream & ast_smt2_pp(std::ostream & out, sort * s, smt2_pp_environment & env, params_ref const & p, unsigned indent) {
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(s, env, p, r);
    if (indent > 0)
        r = mk_indent(m, indent, r.get());
    pp(out, r.get(), m, p);
    return out;
}

std::ostream & ast_smt2_pp(std::ostream & out, func_decl * f, smt2_pp_environment & env, params_ref const & p, unsigned indent, char const* cmd) {
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(f, env, p, r, cmd);
    if (indent > 0)
        r = mk_indent(m, indent, r.get());
    pp(out, r.get(), m, p);
    return out;
}

std::ostream & ast_smt2_pp(std::ostream & out, func_decl * f, expr* e, smt2_pp_environment & env, params_ref const & p, unsigned indent, char const* cmd) {
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(f, e, env, p, r, cmd);
    if (indent > 0)
        r = mk_indent(m, indent, r.get());
    pp(out, r.get(), m, p);
    return out;
}


std::ostream & ast_smt2_pp(std::ostream & out, unsigned sz, expr * const* es, smt2_pp_environment & env, params_ref const & p, unsigned indent,
                            unsigned num_vars, char const * var_prefix) {
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(sz, es, env, p, num_vars, var_prefix, r, var_names);
    if (indent > 0)
        r = mk_indent(m, indent, r.get());
    pp(out, r.get(), m, p);
    return out;
}

std::ostream & ast_smt2_pp(std::ostream & out, symbol const& s, bool is_skolem, smt2_pp_environment & env, params_ref const& p) {
    unsigned len;
    ast_manager & m = env.get_manager();
    format_ref r(fm(m));
    r = env.pp_fdecl_name(s, len, is_skolem);
    pp(out, r.get(), m, p);
    return out;
}

mk_ismt2_pp::mk_ismt2_pp(ast * t, ast_manager & m, params_ref const & p, unsigned indent, unsigned num_vars, char const * var_prefix):
    m_ast(t),
    m_manager(m),
    m_params(p),
    m_indent(indent),
    m_num_vars(num_vars),
    m_var_prefix(var_prefix) {
}

mk_ismt2_pp::mk_ismt2_pp(ast * t, ast_manager & m, unsigned indent, unsigned num_vars, char const * var_prefix):
    m_ast(t),
    m_manager(m),
    m_params(m_empty),
    m_indent(indent),
    m_num_vars(num_vars),
    m_var_prefix(var_prefix) {
}



std::ostream& operator<<(std::ostream& out, mk_ismt2_pp const & p) {
    smt2_pp_environment_dbg env(p.m_manager);    
    if (p.m_ast == nullptr) {
        out << "null";
    }
    else if (is_expr(p.m_ast)) {
        ast_smt2_pp(out, to_expr(p.m_ast), env, p.m_params, p.m_indent, p.m_num_vars, p.m_var_prefix);
    }
    else if (is_sort(p.m_ast)) {
        ast_smt2_pp(out, to_sort(p.m_ast), env, p.m_params, p.m_indent);
    }
    else {
        SASSERT(is_func_decl(p.m_ast));
        ast_smt2_pp(out, to_func_decl(p.m_ast), env, p.m_params, p.m_indent);
    }
    return out;
}

std::ostream& operator<<(std::ostream& out, expr_ref const&  e) {
    return out << mk_ismt2_pp(e.get(), e.get_manager());
}

std::ostream& operator<<(std::ostream& out, app_ref const&  e) {
    return out << mk_ismt2_pp(e.get(), e.get_manager());
}

std::ostream& operator<<(std::ostream& out, func_decl_ref const&  e) {
    return out << mk_ismt2_pp(e.get(), e.get_manager());
}

std::ostream& operator<<(std::ostream& out, sort_ref const&  e) {
    return out << mk_ismt2_pp(e.get(), e.get_manager());
}

std::ostream& operator<<(std::ostream& out, expr_ref_vector const&  e) {
    smt2_pp_environment_dbg env(e.get_manager());
    params_ref p;
    return ast_smt2_pp(out, e.size(), e.c_ptr(), env, p, 0, 0, nullptr);
}

std::ostream& operator<<(std::ostream& out, app_ref_vector const&  e) {
    smt2_pp_environment_dbg env(e.get_manager());
    params_ref p;
    return ast_smt2_pp(out, e.size(), (expr*const*)e.c_ptr(), env, p, 0, 0, nullptr);
}

std::ostream& operator<<(std::ostream& out, func_decl_ref_vector const&  e) {
    for (func_decl* f : e) 
        out << mk_ismt2_pp(f, e.get_manager()) << "\n";
    return out;
}

std::ostream& operator<<(std::ostream& out, sort_ref_vector const&  e) {
    for (sort* s : e) 
        out << mk_ismt2_pp(s, e.get_manager()) << "\n";
    return out;
}

#ifdef Z3DEBUG
void pp(expr const * n, ast_manager & m) {
    std::cout << mk_ismt2_pp(const_cast<expr*>(n), m) << std::endl;
}
void pp(expr_ref const & n) {
    std::cout << mk_ismt2_pp(n.get(), n.m()) << std::endl;
}
#endif
