/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.cpp

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#include"ast_smt2_pp.h"
#include"smt_context.h"
#include"theory_fpa.h"
#include"theory_bv.h"
#include"smt_model_generator.h"

namespace smt {

    class fpa_factory : public value_factory {
        float_util          m_util;

        virtual app * mk_value_core(mpf const & val, sort * s) {
            SASSERT(m_util.get_ebits(s) == val.get_ebits());
            SASSERT(m_util.get_sbits(s) == val.get_sbits());
            return m_util.mk_value(val);
        }

    public:
        fpa_factory(ast_manager & m, family_id fid) :
            value_factory(m, fid),
            m_util(m) {
        }

        virtual ~fpa_factory() {}

        virtual expr * get_some_value(sort * s) { NOT_IMPLEMENTED_YET(); }
        virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) { NOT_IMPLEMENTED_YET(); }
        virtual expr * get_fresh_value(sort * s) { NOT_IMPLEMENTED_YET(); }
        virtual void register_value(expr * n) { /* Ignore */ }

        app * mk_value(mpf const & x) {
            return m_util.mk_value(x);
        }
    };

    class fpa_conv_trail : public trail<theory_fpa> {
        ast_manager & m;
        obj_map<expr, expr*> & m_conversions;
        expr * m_e;
    public:
        fpa_conv_trail(ast_manager & m, obj_map<expr, expr*> & c, expr * e) : m(m), m_conversions(c), m_e(e) {}
        virtual ~fpa_conv_trail() {}
        virtual void undo(theory_fpa & th) {
            expr * v = m_conversions.find(m_e);
            m_conversions.remove(m_e);
            m.dec_ref(v);
        }
    };

    void theory_fpa::fpa2bv_converter_wrapped::mk_const(func_decl * f, expr_ref & result) {
        SASSERT(f->get_family_id() == null_family_id);
        SASSERT(f->get_arity() == 0);
        expr * r;
        if (m_const2bv.find(f, r)) {
            result = r;
        }
        else {
            sort * s = f->get_range();
            func_decl_ref w(m), u(m);
            m_th.get_wrap(s, w, u);
            expr_ref bv(m);
            bv = m.mk_app(w, m.mk_const(f));
            unsigned bv_sz = m_th.m_bv_util.get_bv_size(bv);
            unsigned ebits = m_th.m_float_util.get_ebits(f->get_range());
            unsigned sbits = m_th.m_float_util.get_sbits(f->get_range());
            SASSERT(bv_sz == ebits + sbits);
            m_th.m_converter.mk_triple(m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv),
                                       m_bv_util.mk_extract(sbits - 2, 0, bv),
                                       m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv),
                                       result);

            m_const2bv.insert(f, result);
            m.inc_ref(f);
            m.inc_ref(result);
        }
    }        

    void theory_fpa::fpa2bv_converter_wrapped::mk_rm_const(func_decl * f, expr_ref & result) {
        SASSERT(f->get_family_id() == null_family_id);
        SASSERT(f->get_arity() == 0);
        expr * r;
        if (m_rm_const2bv.find(f, r)) {
            result = r;
        }
        else {
            SASSERT(is_rm(f->get_range()));

            sort * s = f->get_range();
            func_decl_ref w(m), u(m);
            m_th.get_wrap(s, w, u);
            result = m.mk_app(w, m.mk_const(f));
            
            m_rm_const2bv.insert(f, result);
            m.inc_ref(f);
            m.inc_ref(result);
        }
    }

    theory_fpa::theory_fpa(ast_manager & m) :
        theory(m.mk_family_id("float")),
        m_converter(m, this),
        m_rw(m, m_converter, params_ref()),
        m_th_rw(m),
        m_trail_stack(*this),
        m_float_util(m_converter.fu()),
        m_bv_util(m_converter.bu()),
        m_arith_util(m_converter.au())
    {
    }

    theory_fpa::~theory_fpa()
    {        
        ast_manager & m = get_manager();
        dec_ref_map_values(m, m_conversions);
        dec_ref_map_values(m, m_wraps);
        dec_ref_map_values(m, m_unwraps);
    }

    app * theory_fpa::fpa_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {
        SASSERT(values.size() == 3);
        ast_manager & m = m_th.get_manager();

        TRACE("t_fpa", tout << "fpa_value_proc::mk_value for: [" << 
              mk_ismt2_pp(values[0], m) << " " <<
              mk_ismt2_pp(values[1], m) << " " <<
              mk_ismt2_pp(values[2], m) << "]" << std::endl;);

        mpf_manager & mpfm = m_fu.fm();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();
        unsynch_mpz_manager & mpzm = mpfm.mpz_manager(); 

        unsigned ebits = m_bu.get_bv_size(values[2]);
        unsigned sbits = m_bu.get_bv_size(values[1]) + 1;
        app * result;
        
        scoped_mpz sgn_z(mpzm), sig_z(mpzm), exp_z(mpzm);
        scoped_mpz bias(mpzm);
        mpzm.power(mpz(2), ebits - 1, bias);
        mpzm.dec(bias);

        rational sgn_q(0), sig_q(0), exp_q(bias);
        unsigned bv_sz;

        bool r;
        r = m_bu.is_numeral(values[0], sgn_q, bv_sz); SASSERT(r); SASSERT(bv_sz == 1);
        r = m_bu.is_numeral(values[1], sig_q, bv_sz); SASSERT(r); SASSERT(bv_sz == sbits - 1);
        r = m_bu.is_numeral(values[2], exp_q, bv_sz); SASSERT(r); SASSERT(bv_sz == ebits);

        TRACE("t_fpa", tout << "sgn=" << sgn_q.to_string() << " ; " <<
                               "sig=" << sig_q.to_string() << " ; " <<
                               "exp=" << exp_q.to_string() << std::endl;);

        rational exp_u = exp_q - rational(bias);
        SASSERT(exp_u.is_int64());

        scoped_mpf f(mpfm);
        scoped_mpq sig_mpq(mpqm);
        sig_mpq = sig_q.to_mpq();
        mpfm.set(f, ebits, sbits, sgn_q.is_one(), sig_mpq.get().numerator(), exp_u.get_int64());
        result = m_fu.mk_value(f);

        TRACE("t_fpa", tout << "fpa_value_proc::mk_value result: " << 
                               mk_ismt2_pp(result, m_th.get_manager()) << "\n";);
        return result;
    }

    app * theory_fpa::fpa_rm_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {
        SASSERT(values.size() == 1);
        ast_manager & m = m_th.get_manager();
        
        TRACE("t_fpa", tout << "fpa_rm_value_proc::mk_value for: [" <<
                                    mk_ismt2_pp(values[0], m) << "]" << std::endl;);        

        app * result = 0;
        sort * s = m.get_sort(values[0]);
        unsigned bv_sz;

        rational val(0);
        bool r = m_bu.is_numeral(values[0], val, bv_sz);
        SASSERT(r);
        SASSERT(bv_sz == 3);
            
        switch (val.get_uint64())
        {
        case BV_RM_TIES_TO_AWAY: result = m_fu.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: result = m_fu.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: result = m_fu.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: result = m_fu.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: result = m_fu.mk_round_toward_zero();
        }

        TRACE("t_fpa", tout << "fpa_rm_value_proc::mk_value result: " << 
                               mk_ismt2_pp(result, m_th.get_manager()) << "\n";);

        return result;
    }

    void theory_fpa::get_wrap(sort * s, func_decl_ref & wrap, func_decl_ref & unwrap)
    {
        func_decl *w, *u;

        if (!m_wraps.find(s, w) || !m_unwraps.find(s, u)) {
            SASSERT(!m_wraps.contains(s));
            SASSERT(!m_unwraps.contains(s));
            ast_manager & m = get_manager();
            context & ctx = get_context();
            sort * bv_srt = 0;

            if (m_converter.is_rm(s))
                bv_srt = m_bv_util.mk_sort(3);
            else {
                SASSERT(m_converter.is_float(s));
                unsigned ebits = m_float_util.get_ebits(s);
                unsigned sbits = m_float_util.get_sbits(s);
                bv_srt = m_bv_util.mk_sort(ebits + sbits);
            }
                       
            w = m.mk_func_decl(get_family_id(), OP_FLOAT_INTERNAL_BVWRAP, 0, 0, 1, &s, bv_srt);
            u = m.mk_func_decl(get_family_id(), OP_FLOAT_INTERNAL_BVUNWRAP, 0, 0, 1, &bv_srt, s);
            m_wraps.insert(s, w);
            m_unwraps.insert(s, u);
            m.inc_ref(w);
            m.inc_ref(u);
        }

        wrap = w;
        unwrap = u;
    }
    
    expr_ref theory_fpa::convert_atom(expr * e) {
        ast_manager & m = get_manager();
        expr_ref res(m);
        proof_ref pr(m);
        m_rw(e, res);
        m_th_rw(res, res);

        TRACE("t_fpa_detail", tout << "converted atom:" << std::endl;
                              tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                      mk_ismt2_pp(res, m) << std::endl;);

        SASSERT(is_app(res));
        SASSERT(m.is_bool(res));
        return res;
    }

    expr_ref theory_fpa::convert_term(expr * e) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr_ref res(m);
        proof_ref pr(m);
        m_rw(e, res);
        
        SASSERT(is_app(res));
        
        if (m_float_util.is_rm(e)) {
            SASSERT(is_sort_of(m.get_sort(res), m_bv_util.get_family_id(), BV_SORT));
            SASSERT(m_bv_util.get_bv_size(res) == 3);
            ctx.internalize(res, false);
        }
        else {
            SASSERT(to_app(res)->get_family_id() == get_family_id());
            decl_kind k = to_app(res)->get_decl_kind();
            if (k == OP_FLOAT_TO_FP) {
                SASSERT(to_app(res)->get_num_args() == 3);
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(0)), m_bv_util.get_family_id(), BV_SORT));
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(1)), m_bv_util.get_family_id(), BV_SORT));
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(2)), m_bv_util.get_family_id(), BV_SORT));

                expr *sgn, *sig, *exp;
                expr_ref s_sgn(m), s_sig(m), s_exp(m);
                m_converter.split_triple(res, sgn, sig, exp);
                m_th_rw(sgn, s_sgn);
                m_th_rw(sig, s_sig);
                m_th_rw(exp, s_exp);                
                
                m_converter.mk_triple(s_sgn, s_sig, s_exp, res);
            }
            else {
                SASSERT(is_sort_of(m.get_sort(e), get_family_id(), ROUNDING_MODE_SORT));
                SASSERT(is_sort_of(m.get_sort(res), m_bv_util.get_family_id(), BV_SORT));
            }
        }

        TRACE("t_fpa_detail", tout << "converted term:" << std::endl;
                              tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                   mk_ismt2_pp(res, m) << std::endl;);
        return res;
    }

    expr_ref theory_fpa::convert(expr * e)
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr_ref res(m);
        
        if (m_conversions.contains(e)) {
            res = m_conversions.find(e);
            TRACE("t_fpa_detail", tout << "cached:" << std::endl;
                                  tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                      mk_ismt2_pp(res, m) << std::endl;);
            return res;
        }
        else {
            if (m.is_bool(e))
                res = convert_atom(e);
            else if (m_float_util.is_float(e) || m_float_util.is_rm(e))
                res = convert_term(e);
            else
                UNREACHABLE();

            TRACE("t_fpa_detail", tout << "caching:" << std::endl;
            tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                mk_ismt2_pp(res, m) << std::endl;);

            m_conversions.insert(e, res);
            m.inc_ref(res);
            m_trail_stack.push(fpa_conv_trail(m, m_conversions, e));
        }

        return res;
    }

    expr_ref theory_fpa::mk_side_conditions()
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        simplifier & simp = ctx.get_simplifier();
        
        expr_ref res(m), t(m);
        proof_ref t_pr(m);
        res = m.mk_true();

        expr_ref_vector::iterator it = m_converter.m_extra_assertions.begin();
        expr_ref_vector::iterator end = m_converter.m_extra_assertions.end();
        for (; it != end; it++) {
            simp(*it, t, t_pr);
            res = m.mk_and(res, t);
        }
        m_converter.m_extra_assertions.reset();
        
        CTRACE("t_fpa", !m.is_true(res), tout << "side condition: " << mk_ismt2_pp(res, m) << "\n";);
        return res;
    }

    void theory_fpa::assert_cnstr(expr * e) {        
        TRACE("t_fpa_detail", tout << "asserting " << mk_ismt2_pp(e, get_manager()) << "\n";);
        if (get_manager().is_true(e)) return;
        context& ctx = get_context();
        ctx.internalize(e, false);
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }    

    void theory_fpa::attach_new_th_var(enode * n) {
        context & ctx = get_context();
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        TRACE("t_fpa", tout << "new theory var: " << mk_ismt2_pp(n->get_owner(), get_manager()) << " := " << v << "\n";);       
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa_detail", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());

        ast_manager & m = get_manager();
        context & ctx = get_context();

        if (ctx.b_internalized(atom))
            return true;

        unsigned num_args = atom->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(atom->get_arg(i), false);

        literal l(ctx.mk_bool_var(atom));
        ctx.set_var_theory(l.var(), get_id());

        expr_ref bv_atom(m);
        bv_atom = convert(atom);
        TRACE("t_fpa_detail", tout << "converted: " << mk_ismt2_pp(bv_atom, get_manager()) << "\n";);
        SASSERT(bv_atom.get()->get_kind() == AST_APP);
        bv_atom = m.mk_and(bv_atom, mk_side_conditions());
        
        expr_ref atom_iff(m);
        assert_cnstr(m.mk_iff(atom, bv_atom));
        return true;
    }

    bool theory_fpa::internalize_term(app * term) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        TRACE("t_fpa_detail", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!ctx.e_internalized(term));

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        
        enode * e = (ctx.e_internalized(term)) ? ctx.get_enode(term) : 
                                                 ctx.mk_enode(term, false, false, true);

        if (is_attached_to_var(e))
            return false;

        attach_new_th_var(e);        
        return true;
    }    

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {        
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);        
        SASSERT(n->get_owner()->get_family_id() == get_family_id() ||
                n->get_owner()->get_family_id() == null_theory_id);
        SASSERT(s->get_family_id() == get_family_id());
        ast_manager & m = get_manager();

        if (!is_attached_to_var(n))
            attach_new_th_var(n);
            
        app_ref owner(m);
        sort_ref owner_sort(m);
        owner = n->get_owner();
        owner_sort = m.get_sort(owner);

        if (m_float_util.is_rm(owner_sort)) {
            func_decl_ref wrap(m), unwrap(m);
            get_wrap(owner_sort, wrap, unwrap);
            if (owner->get_decl() != unwrap)
            {
                expr_ref converted(m), t(m), limit(m);
                converted = convert(owner);
                limit = m_bv_util.mk_numeral(4, 3);
                t = m_bv_util.mk_ule(converted, limit);
                assert_cnstr(t);
            }
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {        
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << std::endl;
                       tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " = " << 
                               mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl; );
        
        context & ctx = get_context();
        float_util & fu = m_float_util;
        bv_util & bu = m_bv_util;
        mpf_manager & mpfm = fu.fm();

        app * xe = get_enode(x)->get_owner();
        app * ye = get_enode(y)->get_owner();

        if (m_bv_util.is_bv(xe) && m_bv_util.is_bv(ye))
        {
            SASSERT(xe->get_decl()->get_family_id() == get_family_id());
            return;
        }

        expr_ref xc(m), yc(m);
        xc = convert(xe);
        yc = convert(ye);
        
        expr_ref c(m);

        if (fu.is_float(xe) && fu.is_float(ye))
        {
            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_triple(xc, x_sgn, x_sig, x_exp);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_triple(yc, y_sgn, y_sig, y_exp);

            c = m.mk_and(m.mk_eq(x_sgn, y_sgn),
                         m.mk_eq(x_sig, y_sig),
                         m.mk_eq(x_exp, y_exp));            
        }
        else if (fu.is_rm(xe) && fu.is_rm(ye))
            c = m.mk_eq(xc, yc);
        else
            UNREACHABLE();

        // assert_cnstr(m.mk_iff(m.mk_eq(xe, ye), c));
        assert_cnstr(c);
        assert_cnstr(mk_side_conditions());

        return;
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new diseq: " << x << " != " << y << std::endl;
                       tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " != " <<
                               mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl;);

        context & ctx = get_context();
        mpf_manager & mpfm = m_float_util.fm();

        app * xe = get_enode(x)->get_owner();
        app * ye = get_enode(y)->get_owner();

        if (m_bv_util.is_bv(xe) && m_bv_util.is_bv(ye))
        {
            SASSERT(xe->get_decl()->get_family_id() == get_family_id());
            return;
        }

        expr_ref xc(m), yc(m);
        xc = convert(xe);
        yc = convert(ye);

        expr_ref c(m);

        if (m_float_util.is_float(xe) && m_float_util.is_float(ye))
        {
            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_triple(xc, x_sgn, x_sig, x_exp);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_triple(yc, y_sgn, y_sig, y_exp);
            
            c = m.mk_or(m.mk_not(m.mk_eq(x_sgn, y_sgn)),
                        m.mk_not(m.mk_eq(x_sig, y_sig)),
                        m.mk_not(m.mk_eq(x_exp, y_exp)));
        }
        else if (m_float_util.is_rm(xe) && m_float_util.is_rm(ye))
            c = m.mk_not(m.mk_eq(xc, yc));
        else
            UNREACHABLE();

        // assert_cnstr(m.mk_iff(m.mk_not(m.mk_eq(xe, ye)), c));
        assert_cnstr(c);
        assert_cnstr(mk_side_conditions());

        return;
    }

    void theory_fpa::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();        
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {                
        m_trail_stack.pop_scope(num_scopes);
        TRACE("t_fpa", tout << "pop " << num_scopes << "; now " << m_trail_stack.get_num_scopes() << "\n";);
        // unsigned num_old_vars = get_old_num_vars(num_scopes);        
        theory::pop_scope_eh(num_scopes);
    }    

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr * e = ctx.bool_var2expr(v);
        
        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << "):\n" << mk_ismt2_pp(e, m) << "\n";);
        
        expr_ref converted(m);
        converted = convert(e);
        converted = m.mk_and(converted, mk_side_conditions());
        if (!is_true) converted = m.mk_not(converted);
        assert_cnstr(converted);
    }

    void theory_fpa::relevant_eh(app * n) {
        ast_manager & m = get_manager();
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, m) << "\n";);

        mpf_manager & mpfm = m_float_util.fm();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();

        if (m_float_util.is_float(n) || m_float_util.is_rm(n)) {
            sort * s = m.get_sort(n);
            func_decl_ref wrap(m), unwrap(m);
            get_wrap(s, wrap, unwrap);

            if (n->get_decl() != unwrap) {
                expr_ref wrapped(m), c(m);
                wrapped = m.mk_app(wrap, n);
                mpf_rounding_mode rm;
                scoped_mpf val(mpfm);
                if (m_float_util.is_rm_value(n, rm)) {
                    c = m.mk_eq(wrapped, m_bv_util.mk_numeral(rm, 3));
                    c = m.mk_and(c, mk_side_conditions());
                    assert_cnstr(c);
                }
                else if (m_float_util.is_value(n, val)) {
                    unsigned sz = val.get().get_ebits() + val.get().get_sbits();
                    expr_ref bv_val_e(m);
                    bv_val_e = convert(n);
                    SASSERT(is_app(bv_val_e));
                    SASSERT(to_app(bv_val_e)->get_num_args() == 3);
                    app_ref bv_val_a(to_app(bv_val_e.get()), m);
                    c = m.mk_eq(wrapped, m_bv_util.mk_concat(
                        m_bv_util.mk_concat(bv_val_a->get_arg(0), bv_val_a->get_arg(1)),
                        bv_val_a->get_arg(2)));
                    c = m.mk_and(c, mk_side_conditions());
                    assert_cnstr(c);
                }
                else {
                    c = m.mk_eq(m.mk_app(unwrap, wrapped), n);
                    c = m.mk_and(c, mk_side_conditions());
                    assert_cnstr(c);
                }
            }
        }
    }

    void theory_fpa::reset_eh() {
        TRACE("t_fpa", tout << "reset_eh\n";);
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_converter.reset();
        m_rw.reset();
        m_th_rw.reset();
        m_trail_stack.pop_scope(m_trail_stack.get_num_scopes());
        if (m_factory) dealloc(m_factory); m_factory = 0;
        ast_manager & m = get_manager();
        dec_ref_map_values(m, m_conversions);
        dec_ref_map_values(m, m_wraps);
        dec_ref_map_values(m, m_unwraps);
        theory::reset_eh();
    }

    void theory_fpa::init_model(model_generator & mg) {
        TRACE("t_fpa", tout << "initializing model" << std::endl;);
        m_factory = alloc(fpa_factory, get_manager(), get_family_id());
        mg.register_factory(m_factory);
        TRACE("t_fpa", display(tout););
    }

    void theory_fpa::add_value_dep(fpa_value_proc * vp, expr * e) {
        SASSERT(m_bv_util.is_bv(e));
        ast_manager & m = get_manager();
        context & ctx = get_context();        
        if (ctx.e_internalized(e))
            vp->add_dependency(ctx.get_enode(e));
        else {
            expr_ref n(m);
            n = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(e));
            if (!ctx.e_internalized(n))
                ctx.internalize(n, false);
            vp->add_dependency(ctx.get_enode(n));
        }
    }

    model_value_proc * theory_fpa::mk_value(enode * n, model_generator & mg) {
        TRACE("t_fpa", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);        

        ast_manager & m = get_manager();
        context & ctx = get_context();
        app * owner = n->get_owner();

        app_ref c_a(m);
        c_a = to_app(convert(owner));
        SASSERT(ctx.e_internalized(owner));

        TRACE("t_fpa", tout << "converted = " << mk_ismt2_pp(c_a, get_manager()) << "\n";);

        model_value_proc * res = 0;

        if (m_float_util.is_rm(owner)) {
             fpa_rm_value_proc * vp = alloc(fpa_rm_value_proc, this);
             add_value_dep(vp, c_a);
             res = vp;
        } 
        else if (m_float_util.is_float(owner)) {
            fpa_value_proc * vp = alloc(fpa_value_proc, this);
            expr_ref bv_sgn(m), bv_sig(m), bv_exp(m);
            m_converter.split_triple(c_a, bv_sgn, bv_sig, bv_exp);
            add_value_dep(vp, bv_sgn);
            add_value_dep(vp, bv_sig);
            add_value_dep(vp, bv_exp);
            res = vp;
        }
        else
            UNREACHABLE();

        return res;
    }

    void theory_fpa::finalize_model(model_generator & mg) {}

    void theory_fpa::display(std::ostream & out) const
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        
        out << "theory variables:" << std::endl;        
        ptr_vector<enode>::const_iterator it = ctx.begin_enodes();
        ptr_vector<enode>::const_iterator end = ctx.end_enodes();
        for (; it != end; it++) {
            theory_var v = (*it)->get_th_var(get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp((*it)->get_owner(), m) << std::endl;
        }
    }
};
