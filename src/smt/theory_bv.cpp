/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_bv.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-06.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/theory_bv.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/bv_decl_plugin.h"
#include "smt/smt_model_generator.h"
#include "util/stats.h"


namespace smt {

    theory_var theory_bv::mk_var(enode * n) {
        theory_var r  = theory::mk_var(n);
        m_find.mk_var();
        m_bits.push_back(literal_vector());
        m_wpos.push_back(0);
        m_zero_one_bits.push_back(zero_one_bits());
        ctx.attach_th_var(n, this, r);
        return r;
    }

    app * theory_bv::mk_bit2bool(app * bv, unsigned idx) {
        parameter p(idx);
        expr * args[1] = {bv};
        return get_manager().mk_app(get_id(), OP_BIT2BOOL, 1, &p, 1, args);
    }
    
    void theory_bv::mk_bits(theory_var v) {
        enode * n             = get_enode(v);
        app * owner           = n->get_expr();
        unsigned bv_size      = get_bv_size(n);
        bool is_relevant      = ctx.is_relevant(n);
        literal_vector & bits = m_bits[v];
        bits.reset();
        m_bits_expr.reset();

        for (unsigned i = 0; i < bv_size; i++) {
            m_bits_expr.push_back(mk_bit2bool(owner, i));
        }
        ctx.internalize(m_bits_expr.data(), bv_size, true);

        for (unsigned i = 0; i < bv_size; i++) {
            bool_var b = ctx.get_bool_var(m_bits_expr[i]);
            bits.push_back(literal(b));
            if (is_relevant && !ctx.is_relevant(b)) {
                ctx.mark_as_relevant(b);
            }
        }

        TRACE("bv", tout << "v" << v << " #" << owner->get_id() << "\n";
              for (unsigned i = 0; i < bv_size; i++) 
                  tout << mk_bounded_pp(m_bits_expr[i], m) << "\n";
              );

    }

    class mk_atom_trail : public trail {
        theory_bv& th;
        bool_var m_var;
    public:
        mk_atom_trail(theory_bv& th, bool_var v):th(th), m_var(v) {}
        void undo() override {
            theory_bv::atom * a = th.get_bv2a(m_var);
            a->~atom();
            th.erase_bv2a(m_var);
        }
    };

    void theory_bv::mk_bit2bool(app * n) {
        SASSERT(!ctx.b_internalized(n));
        
        TRACE("bv", tout << "bit2bool: " << mk_pp(n, ctx.get_manager()) << "\n";);
        expr* first_arg = n->get_arg(0);

        if (!ctx.e_internalized(first_arg)) {
            // This may happen if bit2bool(x) is in a conflict
            // clause that is being reinitialized, and x was not reinitialized
            // yet.
            // So, we internalize x (i.e., arg)
            ctx.internalize(first_arg, false);
            SASSERT(ctx.e_internalized(first_arg));
            // In most cases, when x is internalized, its bits are created.
            // They are created because x is a bit-vector operation or apply_sort_cnstr is invoked.
            // However, there is an exception. The method apply_sort_cnstr is not invoked for ite-terms.
            // So, I execute get_var on the enode attached to first_arg. 
            // This will force a theory variable to be created if it does not already exist.
            // This will also force the creation of all bits for x.
            enode * first_arg_enode = ctx.get_enode(first_arg);
            get_var(first_arg_enode);
        }
         
        enode * arg      = ctx.get_enode(first_arg);
        // The argument was already internalized, but it may not have a theory variable associated with it.
        // For example, for ite-terms the method apply_sort_cnstr is not invoked.
        // See comment in the then-branch.
        theory_var v_arg = arg->get_th_var(get_id());
        if (v_arg == null_theory_var) {
            // The method get_var will create a theory variable for arg. 
            // As a side-effect the bits for arg will also be created.
            get_var(arg);
            SASSERT(ctx.b_internalized(n));
        }
        else if (!ctx.b_internalized(n)) {
            SASSERT(v_arg != null_theory_var);
            bool_var bv      = ctx.mk_bool_var(n);
            ctx.set_var_theory(bv, get_id());
            bit_atom * a     = new (get_region()) bit_atom();
            insert_bv2a(bv, a);
            m_trail_stack.push(mk_atom_trail(*this, bv));
            unsigned idx     = n->get_decl()->get_parameter(0).get_int();
            SASSERT(a->m_occs == 0);
            a->m_occs = new (get_region()) var_pos_occ(v_arg, idx);
            // Fix for #2182, and SPACER bit-vector
            if (idx < m_bits[v_arg].size()) {
                ctx.mk_th_axiom(get_id(), m_bits[v_arg][idx], literal(bv, true));
                ctx.mk_th_axiom(get_id(), ~m_bits[v_arg][idx], literal(bv, false));
            }      
        }
        // axiomatize bit2bool on constants.
        rational val;
        unsigned sz;
        if (m_util.is_numeral(first_arg, val, sz)) {
            rational bit;
            unsigned idx = n->get_decl()->get_parameter(0).get_int();
            div(val, rational::power_of_two(idx), bit);
            mod(bit, rational(2), bit);
            literal lit = ctx.get_literal(n);
            if (bit.is_zero()) lit.neg();
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        }
    }

    void theory_bv::process_args(app * n) {
        ctx.internalize(n->get_args(), n->get_num_args(), false);
    }

    enode * theory_bv::mk_enode(app * n) {
        enode * e;
        if (ctx.e_internalized(n)) {
            e = ctx.get_enode(n);
        }
        else {
            e = ctx.mk_enode(n, !params().m_bv_reflect, false, params().m_bv_cc);
            mk_var(e);
        }
//        SASSERT(e->get_th_var(get_id()) != null_theory_var);
        return e;
    }

    theory_var theory_bv::get_var(enode * n) {
        theory_var v = n->get_th_var(get_id());
        if (v == null_theory_var) {
            v = mk_var(n);
            mk_bits(v);
        }
        return v;
    }

    enode * theory_bv::get_arg(enode * n, unsigned idx) {
        if (params().m_bv_reflect) {
            return n->get_arg(idx);
        }
        else {
            app * arg     = to_app(n->get_expr()->get_arg(idx));
            SASSERT(ctx.e_internalized(arg));
            return ctx.get_enode(arg);
        }
    }
    
    inline theory_var theory_bv::get_arg_var(enode * n, unsigned idx) {
        return get_var(get_arg(n, idx));
    }

    void theory_bv::get_bits(theory_var v, expr_ref_vector & r) {
        literal_vector & bits = m_bits[v];
        for (literal lit : bits) {
            expr_ref l(get_manager());
            ctx.literal2expr(lit, l);
            r.push_back(std::move(l));
        }
    }

    inline void theory_bv::get_bits(enode * n, expr_ref_vector & r) {
        get_bits(get_var(n), r);
    }

    inline void theory_bv::get_arg_bits(enode * n, unsigned idx, expr_ref_vector & r) {
        get_bits(get_arg_var(n, idx), r);
    }

    inline void theory_bv::get_arg_bits(app * n, unsigned idx, expr_ref_vector & r) {
        app * arg     = to_app(n->get_arg(idx));
        SASSERT(ctx.e_internalized(arg));
        get_bits(ctx.get_enode(arg), r);
    }
    
    class add_var_pos_trail : public trail {
        theory_bv::bit_atom * m_atom;
    public:
        add_var_pos_trail(theory_bv::bit_atom * a):m_atom(a) {}
        void undo() override {
            SASSERT(m_atom->m_occs);
            m_atom->m_occs = m_atom->m_occs->m_next;
        }
    };

    void theory_bv::add_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx) {
        if (!params().m_bv_eq_axioms)
            return;
        m_prop_diseqs.push_back(bv_diseq(v1, v2, idx));
        ctx.push_trail(push_back_vector<svector<bv_diseq>>(m_prop_diseqs));
    }

    /**
       \brief v1[idx] = ~v2[idx], then v1 /= v2 is a theory axiom.
    */
    void theory_bv::assert_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx) {
        SASSERT(m_bits[v1][idx] == ~m_bits[v2][idx]);
        TRACE("bv_diseq_axiom", tout << "found new diseq axiom\n"; display_var(tout, v1); display_var(tout, v2););
        // found new disequality
        m_stats.m_num_diseq_static++;
        app * e1       = get_expr(v1);
        app * e2       = get_expr(v2);
        expr_ref eq(m.mk_eq(e1, e2), m);
        literal l       = ~mk_literal(eq);
        std::function<expr*(void)> logfn = [&]() {
            return m.mk_implies(m.mk_eq(mk_bit2bool(e1, idx), m.mk_not(mk_bit2bool(e2, idx))), m.mk_not(eq));
        };
        scoped_trace_stream ts(*this, logfn);
        ctx.mk_th_axiom(get_id(), 1, &l);
        if (ctx.relevancy()) {
            relevancy_eh * eh = ctx.mk_relevancy_eh(pair_relevancy_eh(e1, e2, eq));
            ctx.add_relevancy_eh(e1, eh);
            ctx.add_relevancy_eh(e2, eh);
        }
    }

    void theory_bv::register_true_false_bit(theory_var v, unsigned idx) {
        SASSERT(m_bits[v][idx] == true_literal || m_bits[v][idx] == false_literal);
        bool is_true = (m_bits[v][idx] == true_literal);
        zero_one_bits & bits = m_zero_one_bits[v];
        bits.push_back(zero_one_bit(v, idx, is_true));
    }

    /**
       \brief v[idx] = ~v'[idx], then v /= v' is a theory axiom.
    */
    void theory_bv::find_new_diseq_axioms(var_pos_occ * occs, theory_var v, unsigned idx) {
        literal l = m_bits[v][idx];
        l.neg();
        while (occs) {
            theory_var v2   = occs->m_var;
            unsigned   idx2 = occs->m_idx;
            if (idx == idx2 && m_bits[v2][idx2] == l && get_bv_size(v2) == get_bv_size(v)) 
                add_new_diseq_axiom(v, v2, idx);
            occs = occs->m_next;
        }
    }

    /**
       \brief Add bit l to the given variable.
    */
    void theory_bv::add_bit(theory_var v, literal l) {
        literal_vector & bits = m_bits[v];
        unsigned idx          = bits.size();
        bits.push_back(l);
        if (l.var() == true_bool_var) {
            register_true_false_bit(v, idx);
        }
        else {
            theory_id th_id       = ctx.get_var_theory(l.var());
            TRACE("init_bits", tout << l << " " << th_id << "\n";);
            if (th_id == get_id()) {
                atom * a     = get_bv2a(l.var());
                SASSERT(a && a->is_bit());
                bit_atom * b = static_cast<bit_atom*>(a);
                find_new_diseq_axioms(b->m_occs, v, idx);
                m_trail_stack.push(add_var_pos_trail(b));
                b->m_occs = new (get_region()) var_pos_occ(v, idx, b->m_occs);
            }
            else {
                SASSERT(th_id == null_theory_id);
                ctx.set_var_theory(l.var(), get_id());
                SASSERT(ctx.get_var_theory(l.var()) == get_id());
                bit_atom * b = new (get_region()) bit_atom();
                insert_bv2a(l.var(), b);
                m_trail_stack.push(mk_atom_trail(*this, l.var()));
                SASSERT(b->m_occs == 0);
                b->m_occs = new (get_region()) var_pos_occ(v, idx);
            }
        }
    }

    void theory_bv::simplify_bit(expr * s, expr_ref & r) {
        // proof_ref p(get_manager());
        // if (ctx.at_base_level())
        //    ctx.get_rewriter()(s, r, p);
        // else
        r = s;
    }

    void theory_bv::init_bits(enode * n, expr_ref_vector const & bits) {
        theory_var v            = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        unsigned sz             = bits.size();
        SASSERT(get_bv_size(n) == sz);
        m_bits[v].reset();

        ctx.internalize(bits.data(), sz, true);

        for (unsigned i = 0; i < sz; i++) {
            expr * bit          = bits.get(i);
            literal l           = ctx.get_literal(bit);
            TRACE("init_bits", tout << "bit " << i << " of #" << n->get_owner_id() << "\n" << mk_bounded_pp(bit, m) << "\n";);
            add_bit(v, l);
        }
        find_wpos(v);
    }

    /**
       \brief Find an unassigned bit for m_wpos[v], if such bit cannot be found invoke fixed_var_eh
    */
    void theory_bv::find_wpos(theory_var v) {
        literal_vector const & bits = m_bits[v];
        unsigned sz                 = bits.size();
        unsigned & wpos             = m_wpos[v];
        unsigned init               = wpos;
        for (; wpos < sz; wpos++) {
            TRACE("find_wpos", tout << "curr bit: " << bits[wpos] << "\n";);
            if (ctx.get_assignment(bits[wpos]) == l_undef) {
                TRACE("find_wpos", tout << "moved wpos of v" << v << " to " << wpos << "\n";);
                return;
            }
        }
        wpos = 0;
        for (; wpos < init; wpos++) {
            if (ctx.get_assignment(bits[wpos]) == l_undef) {
                TRACE("find_wpos", tout << "moved wpos of v" << v << " to " << wpos << "\n";);
                return;
            }
        }
        TRACE("find_wpos", tout << "v" << v << " is a fixed variable.\n";);
        fixed_var_eh(v);
    }
    
    class fixed_eq_justification : public justification {
        theory_bv & m_th;
        theory_var  m_var1;
        theory_var  m_var2;

        void mark_bits(conflict_resolution & cr, literal_vector const & bits) {
            context & ctx = cr.get_context();
            for (literal lit : bits) {
                if (lit.var() != true_bool_var) {
                    if (ctx.get_assignment(lit) == l_true)
                        cr.mark_literal(lit);
                    else
                        cr.mark_literal(~lit);
                }
            }
        }
        
        void get_proof(conflict_resolution & cr, literal l, ptr_buffer<proof> & prs, bool & visited) {
            if (l.var() == true_bool_var)
                return;
            proof * pr = nullptr;
            if (cr.get_context().get_assignment(l) == l_true)
                pr = cr.get_proof(l);
            else
                pr = cr.get_proof(~l);
            if (pr) 
                prs.push_back(pr);
            else
                visited = false;
        }

    public:
        fixed_eq_justification(theory_bv & th, theory_var v1, theory_var v2):
            m_th(th), m_var1(v1), m_var2(v2) {
        }
        
        void get_antecedents(conflict_resolution & cr) override {
            mark_bits(cr, m_th.m_bits[m_var1]);
            mark_bits(cr, m_th.m_bits[m_var2]);
        }
        
        proof * mk_proof(conflict_resolution & cr) override {
            ptr_buffer<proof> prs;
            context & ctx                       = cr.get_context();
            bool visited                        = true;
            literal_vector const & bits1        = m_th.m_bits[m_var1];
            literal_vector const & bits2        = m_th.m_bits[m_var2];
            literal_vector::const_iterator it1  = bits1.begin();
            literal_vector::const_iterator it2  = bits2.begin();
            literal_vector::const_iterator end1 = bits1.end();
            for (; it1 != end1; ++it1, ++it2) {
                get_proof(cr, *it1, prs, visited);
                get_proof(cr, *it2, prs, visited);
            }
            if (!visited)
                return nullptr;
            expr * fact     = ctx.mk_eq_atom(m_th.get_enode(m_var1)->get_expr(), m_th.get_enode(m_var2)->get_expr());
            ast_manager & m = ctx.get_manager();
            return m.mk_th_lemma(get_from_theory(), fact, prs.size(), prs.data());
        }

        theory_id get_from_theory() const override {
            return m_th.get_id();
        }
        
        char const * get_name() const override { return "bv-fixed-eq"; }

    };

    void theory_bv::add_fixed_eq(theory_var v1, theory_var v2) {
        if (!params().m_bv_eq_axioms)
            return;

        if (v1 > v2) {
            std::swap(v1, v2);
        }

        unsigned act = m_eq_activity[hash_u_u(v1, v2) & 0xFF]++;
        if ((act & 0xFF) != 0xFF) {
            return;
        }
        ++m_stats.m_num_eq_dynamic;
        app* o1 = get_enode(v1)->get_expr();
        app* o2 = get_enode(v2)->get_expr();
        literal oeq = mk_eq(o1, o2, true);
        unsigned sz = get_bv_size(v1);
        TRACE("bv", 
              tout << mk_pp(o1, m) << " = " << mk_pp(o2, m) << " " 
              << ctx.get_scope_level() << "\n";);
        literal_vector eqs;
        for (unsigned i = 0; i < sz; ++i) {
            literal l1 = m_bits[v1][i];
            literal l2 = m_bits[v2][i];
            expr_ref e1(m), e2(m);
            e1 = mk_bit2bool(o1, i);
            e2 = mk_bit2bool(o2, i);
            literal eq = mk_eq(e1, e2, true);
            std::function<expr*()> logfn = [&]() {
                return m.mk_implies(m.mk_not(ctx.bool_var2expr(eq.var())), m.mk_not(ctx.bool_var2expr(oeq.var())));
            };
            scoped_trace_stream st(*this, logfn);
            ctx.mk_th_axiom(get_id(),  l1, ~l2, ~eq);
            ctx.mk_th_axiom(get_id(), ~l1,  l2, ~eq);
            ctx.mk_th_axiom(get_id(),  l1,  l2,  eq);
            ctx.mk_th_axiom(get_id(), ~l1, ~l2,  eq);
            ctx.mk_th_axiom(get_id(), eq, ~oeq);
            eqs.push_back(~eq);
        }
        eqs.push_back(oeq);
        ctx.mk_th_axiom(get_id(), eqs.size(), eqs.data());
    }

    void theory_bv::fixed_var_eh(theory_var v) {
        numeral val;
        VERIFY(get_fixed_value(v, val));
        enode* n = get_enode(v);
        if (ctx.watches_fixed(n)) {
            expr_ref num(m_util.mk_numeral(val, n->get_expr()->get_sort()), m);
            literal_vector& lits = m_tmp_literals;
            lits.reset();
            for (literal b : m_bits[v]) {
                if (ctx.get_assignment(b) == l_false)
                    b.neg();
                lits.push_back(b);
            }
            ctx.assign_fixed(n, num, lits);
        }
        unsigned sz = get_bv_size(v);
        value_sort_pair key(val, sz);
        theory_var v2;
        if (m_fixed_var_table.find(key, v2)) {
            numeral val2;
            if (v2 < static_cast<int>(get_num_vars()) && is_bv(v2) && 
                get_bv_size(v2) == sz && get_fixed_value(v2, val2) && val == val2) {
                if (get_enode(v)->get_root() != get_enode(v2)->get_root()) {
                    SASSERT(get_bv_size(v) == get_bv_size(v2));
                    TRACE("fixed_var_eh", tout << "detected equality: v" << v << " = v" << v2 << "\n";
                          display_var(tout, v);
                          display_var(tout, v2););
                    m_stats.m_num_th2core_eq++;
                    add_fixed_eq(v, v2);
                    justification * js = ctx.mk_justification(fixed_eq_justification(*this, v, v2));
                    ctx.assign_eq(get_enode(v), get_enode(v2), eq_justification(js));                    
                    m_fixed_var_table.insert(key, v2);
                }
            }
            else {
                // the original fixed variable v2 was deleted or it is not fixed anymore.
                m_fixed_var_table.erase(key);
                m_fixed_var_table.insert(key, v);
            }
        }
        else {
            m_fixed_var_table.insert(key, v);
        }
    }

    bool theory_bv::get_fixed_value(theory_var v, numeral & result)  const {
        result.reset();
        unsigned i = 0;
        for (literal b : m_bits[v]) {
            switch (ctx.get_assignment(b)) {
            case l_false: 
                break;
            case l_undef: 
                return false; 
            case l_true:  {
                for (unsigned j = m_power2.size(); j <= i; ++j) 
                    m_power2.push_back(m_bb.power(j));
                result += m_power2[i];
                break;
            }
            }
            ++i;
        }
        return true;
    }

    bool theory_bv::get_fixed_value(app* x, numeral & result) const {
        CTRACE("bv", !ctx.e_internalized(x), tout << "not internalized " << mk_pp(x, m) << "\n";);
        if (!ctx.e_internalized(x)) return false;
        enode * e    = ctx.get_enode(x);
        theory_var v = e->get_th_var(get_id());
        return get_fixed_value(v, result);
    }


    void theory_bv::internalize_num(app * n) {
        SASSERT(!ctx.e_internalized(n));
        numeral val;
        unsigned sz = 0;
        VERIFY(m_util.is_numeral(n, val, sz));
        enode * e    = mk_enode(n);
        // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
        // e->mark_as_interpreted();
        theory_var v = e->get_th_var(get_id());
        expr_ref_vector bits(m);
        m_bb.num2bits(val, sz, bits);
        SASSERT(bits.size() == sz);
        literal_vector & c_bits = m_bits[v];
        for (unsigned i = 0; i < sz; i++) {
            expr * l = bits.get(i);
            if (m.is_true(l)) {
                c_bits.push_back(true_literal);
            }
            else {
                SASSERT(m.is_false(l));
                c_bits.push_back(false_literal);
            }
            register_true_false_bit(v, i);
        }
        fixed_var_eh(v);
    }

    void theory_bv::internalize_mkbv(app* n) {
        expr_ref_vector bits(m);
        process_args(n);
        enode * e = mk_enode(n);
        bits.append(n->get_num_args(), n->get_args());
        init_bits(e, bits);
    }

    void theory_bv::internalize_bv2int(app* n) {
        SASSERT(!ctx.e_internalized(n));
        TRACE("bv", tout << mk_bounded_pp(n, m) << "\n";);
        process_args(n);
        mk_enode(n);
        if (!ctx.relevancy()) {
            assert_bv2int_axiom(n);
        }
    }


    void theory_bv::assert_bv2int_axiom(app * n) {
        // 
        // create the axiom:
        // n = bv2int(k) = ite(bit2bool(k[sz-1],2^{sz-1},0) + ... + ite(bit2bool(k[0],1,0))
        // 
        SASSERT(ctx.e_internalized(n));
        SASSERT(m_util.is_bv2int(n));
        TRACE("bv2int_bug", tout << "bv2int:\n" << mk_pp(n, m) << "\n";);
        sort * int_sort = n->get_sort();
        app * k = to_app(n->get_arg(0));
        SASSERT(m_util.is_bv_sort(k->get_sort()));
        expr_ref_vector k_bits(m);
        enode * k_enode = mk_enode(k);
        get_bits(k_enode, k_bits);
        unsigned sz = m_util.get_bv_size(k);
        expr_ref_vector args(m);
        expr_ref zero(m_autil.mk_numeral(numeral(0), int_sort), m);
        numeral num(1);
        for (unsigned i = 0; i < sz; ++i) {
            // Remark: A previous version of this method was using
            //
            //        expr* b = mk_bit2bool(k,i); 
            //
            // This is not correct. The predicate bit2bool is an
            // internal construct, and it was not meant for building
            // axioms directly.  It is used to represent the bits of a
            // constant, and in some cases the bits of a complicated
            // bit-vector expression.  In most cases, the bits of a
            // composite bit-vector expression T are just boolean
            // combinations of bit2bool atoms of the bit-vector
            // constants contained in T. So, instead of using
            // mk_bit2bool to access a particular bit of T, we should
            // use the method get_bits.
            // 
            expr * b = k_bits.get(i);
            expr_ref n(m_autil.mk_numeral(num, int_sort), m);
            args.push_back(m.mk_ite(b, n, zero));
            num *= numeral(2);
        }
        expr_ref sum(m_autil.mk_add(sz, args.data()), m);
        th_rewriter rw(m);
        rw(sum);
        literal l(mk_eq(n, sum, false));
        TRACE("bv", 
              tout << mk_pp(n, m) << "\n";
              tout << mk_pp(sum, m) << "\n";
              ctx.display_literal_verbose(tout, l); 
              tout << "\n";
              );
       
        ctx.mark_as_relevant(l);
        scoped_trace_stream _ts(*this, l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    void theory_bv::internalize_int2bv(app* n) {    
        SASSERT(!ctx.e_internalized(n));
        SASSERT(n->get_num_args() == 1);
        process_args(n);
        mk_enode(n);
        theory_var v = ctx.get_enode(n)->get_th_var(get_id()); 
        mk_bits(v);

        if (!ctx.relevancy()) {
            assert_int2bv_axiom(n);
        }
    }
    
    void theory_bv::assert_int2bv_axiom(app* n) {
        //
        // create the axiom:
        //   bv2int(n) = e mod 2^bit_width 
        // where n = int2bv(e)
        //
        // Create the axioms:
        //   bit2bool(i,n) == ((e div 2^i) mod 2 != 0)
        // for i = 0,.., sz-1
        //
        SASSERT(ctx.e_internalized(n));
        SASSERT(m_util.is_int2bv(n));

        parameter param(m_autil.mk_int());
        expr* n_expr = n;
        expr* e = n->get_arg(0);
        expr_ref lhs(m), rhs(m);
        lhs = m.mk_app(get_id(), OP_BV2INT, 1, &param, 1, &n_expr);
        unsigned sz = m_util.get_bv_size(n);
        numeral mod = power(numeral(2), sz);
        rhs = m_autil.mk_mod(e, m_autil.mk_numeral(mod, true));

        literal l(mk_eq(lhs, rhs, false));
        ctx.mark_as_relevant(l);
        {
            scoped_trace_stream _ts(*this, l);
            ctx.mk_th_axiom(get_id(), 1, &l);
        }
        
        TRACE("bv", 
              tout << mk_pp(lhs, m) << " == \n";
              tout << mk_pp(rhs, m) << "\n";
              );

        expr_ref_vector n_bits(m);
        enode * n_enode = mk_enode(n);
        get_bits(n_enode, n_bits);

        for (unsigned i = 0; i < sz; ++i) {
            numeral div = power(numeral(2), i);
            mod = numeral(2);
            expr_ref div_rhs((i == 0) ? e : m_autil.mk_idiv(e, m_autil.mk_numeral(div, true)), m);
            rhs = m_autil.mk_mod(div_rhs, m_autil.mk_numeral(mod, true));
            rhs = ctx.mk_eq_atom(rhs, m_autil.mk_int(1));
            lhs = n_bits.get(i);
            TRACE("bv", tout << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << "\n";);
            l = literal(mk_eq(lhs, rhs, false));
            ctx.mark_as_relevant(l);
            {
                scoped_trace_stream _st(*this, l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }
            {
                // 0 < e < 2^i => e div 2^i = 0                
                expr_ref zero(m_autil.mk_int(0), m);
                literal a = mk_literal(m_autil.mk_ge(e, m_autil.mk_int(div)));
                literal b = mk_literal(m_autil.mk_ge(e, zero));
                literal c = mk_eq(div_rhs, zero, false);
                ctx.mark_as_relevant(a);
                ctx.mark_as_relevant(b);
                ctx.mark_as_relevant(c);
                // scoped_trace_stream _st(*this, a, ~b);
                ctx.mk_th_axiom(get_id(), a, ~b, c);
            }
        }
    }


#define MK_UNARY(NAME, BLAST_OP)                                        \
    void theory_bv::NAME(app * n) {                                     \
        SASSERT(!ctx.e_internalized(n));                      \
        SASSERT(n->get_num_args() == 1);                                \
        process_args(n);                                                \
        enode * e       = mk_enode(n);                                  \
        expr_ref_vector arg1_bits(m), bits(m);                          \
        get_arg_bits(e, 0, arg1_bits);                                  \
        m_bb.BLAST_OP(arg1_bits.size(), arg1_bits.data(), bits);       \
        init_bits(e, bits);                                             \
    }

#define MK_BINARY(NAME, BLAST_OP)                                                       \
    void theory_bv::NAME(app * n) {                                                     \
        SASSERT(!ctx.e_internalized(n));                                      \
        SASSERT(n->get_num_args() == 2);                                                \
        process_args(n);                                                                \
        enode * e       = mk_enode(n);                                                  \
        expr_ref_vector arg1_bits(m), arg2_bits(m), bits(m);                            \
        get_arg_bits(e, 0, arg1_bits);                                                  \
        get_arg_bits(e, 1, arg2_bits);                                                  \
        SASSERT(arg1_bits.size() == arg2_bits.size());                                  \
        m_bb.BLAST_OP(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), bits);    \
        init_bits(e, bits);                                                             \
    }


#define MK_AC_BINARY(NAME, BLAST_OP)                                                            \
    void theory_bv::NAME(app * n) {                                                             \
        SASSERT(!ctx.e_internalized(n));                                              \
        SASSERT(n->get_num_args() >= 2);                                                        \
        process_args(n);                                                                        \
        enode * e       = mk_enode(n);                                                          \
        expr_ref_vector arg_bits(m);                                                            \
        expr_ref_vector bits(m);                                                                \
        expr_ref_vector new_bits(m);                                                            \
        unsigned i = n->get_num_args();                                                         \
        --i;                                                                                    \
        get_arg_bits(e, i, bits);                                                               \
        while (i > 0) {                                                                         \
            --i;                                                                                \
            arg_bits.reset();                                                                   \
            get_arg_bits(e, i, arg_bits);                                                       \
            SASSERT(arg_bits.size() == bits.size());                                            \
            new_bits.reset();                                                                   \
            m_bb.BLAST_OP(arg_bits.size(), arg_bits.data(), bits.data(), new_bits);           \
            bits.swap(new_bits);                                                                \
        }                                                                                       \
        init_bits(e, bits);                                                                     \
        TRACE("bv_verbose", tout << arg_bits << " " << bits << " " << new_bits << "\n";); \
    }

    void theory_bv::internalize_sub(app *n) {
        SASSERT(!ctx.e_internalized(n));                      
        SASSERT(n->get_num_args() == 2);                                                
        process_args(n);                                                               
        enode * e       = mk_enode(n);                                                  
        expr_ref_vector arg1_bits(m), arg2_bits(m), bits(m);                            
        get_arg_bits(e, 0, arg1_bits);                                                  
        get_arg_bits(e, 1, arg2_bits);                                                  
        SASSERT(arg1_bits.size() == arg2_bits.size());                                  
        expr_ref carry(m);
        m_bb.mk_subtracter(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), bits, carry);    
        init_bits(e, bits);                                                                
    }

    MK_UNARY(internalize_not,       mk_not);
    MK_UNARY(internalize_redand,    mk_redand);
    MK_UNARY(internalize_redor,     mk_redor);

    MK_AC_BINARY(internalize_add,      mk_adder);
    MK_AC_BINARY(internalize_mul,      mk_multiplier);
    MK_BINARY(internalize_udiv,     mk_udiv);
    MK_BINARY(internalize_sdiv,     mk_sdiv);
    MK_BINARY(internalize_urem,     mk_urem);
    MK_BINARY(internalize_srem,     mk_srem);
    MK_BINARY(internalize_smod,     mk_smod);
    MK_BINARY(internalize_shl,      mk_shl);
    MK_BINARY(internalize_lshr,     mk_lshr);
    MK_BINARY(internalize_ashr,     mk_ashr);
    MK_BINARY(internalize_ext_rotate_left,  mk_ext_rotate_left);
    MK_BINARY(internalize_ext_rotate_right, mk_ext_rotate_right);
    MK_AC_BINARY(internalize_and,      mk_and);
    MK_AC_BINARY(internalize_or,       mk_or);
    MK_AC_BINARY(internalize_xor,      mk_xor);
    MK_AC_BINARY(internalize_nand,     mk_nand);
    MK_AC_BINARY(internalize_nor,      mk_nor);
    MK_AC_BINARY(internalize_xnor,     mk_xnor);
    MK_BINARY(internalize_comp,     mk_comp);

#define MK_PARAMETRIC_UNARY(NAME, BLAST_OP)                                     \
    void theory_bv::NAME(app * n) {                                             \
        SASSERT(!ctx.e_internalized(n));                              \
        SASSERT(n->get_num_args() == 1);                                        \
        process_args(n);                                                        \
        enode * e       = mk_enode(n);                                          \
        expr_ref_vector arg1_bits(m), bits(m);                                  \
        get_arg_bits(e, 0, arg1_bits);                                          \
        unsigned param  = n->get_decl()->get_parameter(0).get_int();            \
        m_bb.BLAST_OP(arg1_bits.size(), arg1_bits.data(), param, bits);        \
        init_bits(e, bits);                                                     \
    }
    
    MK_PARAMETRIC_UNARY(internalize_sign_extend, mk_sign_extend);
    MK_PARAMETRIC_UNARY(internalize_zero_extend, mk_zero_extend);
    MK_PARAMETRIC_UNARY(internalize_rotate_left, mk_rotate_left);
    MK_PARAMETRIC_UNARY(internalize_rotate_right, mk_rotate_right);

    void theory_bv::internalize_concat(app * n) {
        process_args(n);        
        enode * e          = mk_enode(n);  
        theory_var v       = e->get_th_var(get_id());
        unsigned num_args  = n->get_num_args();
        unsigned i         = num_args;
        m_bits[v].reset();
        while (i > 0) {
            i--;
            theory_var arg = get_arg_var(e, i);
            for (literal lit : m_bits[arg]) {
                add_bit(v, lit);
            }
        }
        find_wpos(v);
    }

    void theory_bv::internalize_extract(app * n) {
        SASSERT(n->get_num_args() == 1);
        process_args(n);            
        enode * e          = mk_enode(n);  
        theory_var v       = e->get_th_var(get_id());
        theory_var arg     = get_arg_var(e, 0);
        unsigned start     = n->get_decl()->get_parameter(1).get_int();
        unsigned end       = n->get_decl()->get_parameter(0).get_int();
        SASSERT(start <= end);
        literal_vector & arg_bits = m_bits[arg];
        m_bits[v].reset();
        for (unsigned i = start; i <= end; ++i)
            add_bit(v, arg_bits[i]);
        find_wpos(v);
    }

    bool theory_bv::internalize_term_core(app * term) {
        SASSERT(term->get_family_id() == get_family_id());
        TRACE("bv", tout << "internalizing term: " << mk_bounded_pp(term, m) << "\n";);
        if (approximate_term(term)) {
            return false;
        }
        switch (term->get_decl_kind()) {
        case OP_BV_NUM:         internalize_num(term); return true;
        case OP_BADD:           internalize_add(term); return true;
        case OP_BSUB:           internalize_sub(term); return true;
        case OP_BMUL:           internalize_mul(term); return true;
        case OP_BSDIV_I:        internalize_sdiv(term); return true;
        case OP_BUDIV_I:        internalize_udiv(term); return true;
        case OP_BSREM_I:        internalize_srem(term); return true;
        case OP_BUREM_I:        internalize_urem(term); return true;
        case OP_BSMOD_I:        internalize_smod(term); return true;
        case OP_BAND:           internalize_and(term); return true;
        case OP_BOR:            internalize_or(term); return true;
        case OP_BNOT:           internalize_not(term); return true;
        case OP_BXOR:           internalize_xor(term); return true;
        case OP_BNAND:          internalize_nand(term); return true;
        case OP_BNOR:           internalize_nor(term); return true;
        case OP_BXNOR:          internalize_xnor(term); return true;
        case OP_CONCAT:         internalize_concat(term); return true;
        case OP_SIGN_EXT:       internalize_sign_extend(term); return true;
        case OP_ZERO_EXT:       internalize_zero_extend(term); return true;
        case OP_EXTRACT:        internalize_extract(term); return true;
        case OP_BREDOR:         internalize_redor(term); return true;
        case OP_BREDAND:        internalize_redand(term); return true;
        case OP_BCOMP:          internalize_comp(term); return true;
        case OP_BSHL:           internalize_shl(term); return true;
        case OP_BLSHR:          internalize_lshr(term); return true;
        case OP_BASHR:          internalize_ashr(term); return true;
        case OP_ROTATE_LEFT:    internalize_rotate_left(term); return true;
        case OP_ROTATE_RIGHT:   internalize_rotate_right(term); return true;
        case OP_EXT_ROTATE_LEFT:  internalize_ext_rotate_left(term); return true;
        case OP_EXT_ROTATE_RIGHT: internalize_ext_rotate_right(term); return true;
        case OP_BSDIV0:         return false;
        case OP_BUDIV0:         return false;
        case OP_BSREM0:         return false;
        case OP_BUREM0:         return false;
        case OP_BSMOD0:         return false;
        case OP_MKBV:           internalize_mkbv(term); return true;
        case OP_INT2BV:         
            if (params().m_bv_enable_int2bv2int) {
                internalize_int2bv(term); 
            }
            return params().m_bv_enable_int2bv2int;
        case OP_BV2INT:         
            if (params().m_bv_enable_int2bv2int) {
                internalize_bv2int(term); 
            }
            return params().m_bv_enable_int2bv2int;
        default:
            TRACE("bv_op", tout << "unsupported operator: " << mk_ll_pp(term, m) << "\n";);
            UNREACHABLE();
            return false;
        }
    }

    bool theory_bv::internalize_term(app * term) {
        scoped_suspend_rlimit _suspend_cancel(m.limit());
        try {
            return internalize_term_core(term);
        }
        catch (z3_exception& ex) {
            IF_VERBOSE(1, verbose_stream() << "internalize_term: " << ex.msg() << "\n";);
            throw;
        }
    }

#define MK_NO_OVFL(NAME, OP)                                                                                    \
    void theory_bv::NAME(app *n) {                                                                              \
        SASSERT(n->get_num_args() == 2);                                                                        \
        process_args(n);                                                                                        \
        expr_ref_vector arg1_bits(m), arg2_bits(m);                                                             \
        get_arg_bits(n, 0, arg1_bits);                                                                          \
        get_arg_bits(n, 1, arg2_bits);                                                                          \
        expr_ref out(m);                                                                                        \
        m_bb.OP(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), out);                                   \
        expr_ref s_out(m);                                                                                      \
        simplify_bit(out, s_out);                                                                               \
        ctx.internalize(s_out, true);                                                                           \
        literal def = ctx.get_literal(s_out);                                                                   \
        literal l(ctx.mk_bool_var(n));                                                                          \
        ctx.set_var_theory(l.var(), get_id());                                                                  \
        le_atom * a     = new (get_region()) le_atom(l, def); /* abuse le_atom */                               \
        insert_bv2a(l.var(), a);                                                                                \
        m_trail_stack.push(mk_atom_trail(*this, l.var()));                                                             \
        /* smul_no_overflow and umul_no_overflow are using the le_atom (THIS IS A BIG HACK)... */               \
        /* the connection between the l and def was never realized when                        */               \
        /* relevancy() is true and m_bv_lazy_le is false (the default configuration).          */               \
        /* So, we need to check also the m_bv_lazy_le flag here.                               */               \
        /* Maybe, we should rename the le_atom to bridge_atom, and m_bv_lazy_le option to m_bv_lazy_bridge. */  \
        if (!ctx.relevancy() || !params().m_bv_lazy_le) {                                                       \
            ctx.mk_th_axiom(get_id(),  l, ~def);                                                                \
            ctx.mk_th_axiom(get_id(), ~l,  def);                                                                \
        }                                                                                                       \
    }

    MK_NO_OVFL(internalize_umul_no_overflow, mk_umul_no_overflow);
    MK_NO_OVFL(internalize_smul_no_overflow, mk_smul_no_overflow);
    MK_NO_OVFL(internalize_smul_no_underflow, mk_smul_no_underflow);

    template<bool Signed>
    void theory_bv::internalize_le(app * n) {
        SASSERT(n->get_num_args() == 2);                                                
        process_args(n);                          
        expr_ref_vector arg1_bits(m), arg2_bits(m);
        get_arg_bits(n, 0, arg1_bits);                                                  
        get_arg_bits(n, 1, arg2_bits);                                                  
        expr_ref le(m);
        if (Signed)
            m_bb.mk_sle(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), le);
        else
            m_bb.mk_ule(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), le);
        expr_ref s_le(m);
        simplify_bit(le, s_le);
        ctx.internalize(s_le, true);
        literal def = ctx.get_literal(s_le);
        literal l(ctx.mk_bool_var(n));
        ctx.set_var_theory(l.var(), get_id());
        le_atom * a     = new (get_region()) le_atom(l, def);
        insert_bv2a(l.var(), a);
        m_trail_stack.push(mk_atom_trail(*this, l.var()));
        if (!ctx.relevancy() || !params().m_bv_lazy_le) {
            ctx.mk_th_axiom(get_id(),  l, ~def);
            ctx.mk_th_axiom(get_id(), ~l,  def);
        }
    }

    bool theory_bv::internalize_carry(app * n, bool gate_ctx) {
        ctx.internalize(n->get_args(), 3, true);
        bool is_new_var = false;
        bool_var v;
        if (!ctx.b_internalized(n)) {
            is_new_var  = true;
            v           = ctx.mk_bool_var(n);
            literal r(v);
            literal l1 = ctx.get_literal(n->get_arg(0));
            literal l2 = ctx.get_literal(n->get_arg(1));
            literal l3 = ctx.get_literal(n->get_arg(2));
            ctx.mk_gate_clause(~r,  l1,  l2);
            ctx.mk_gate_clause(~r,  l1,  l3);
            ctx.mk_gate_clause(~r,  l2,  l3);
            ctx.mk_gate_clause( r, ~l1, ~l2);
            ctx.mk_gate_clause( r, ~l1, ~l3);
            ctx.mk_gate_clause( r, ~l2, ~l3);
        }
        else {
            v = ctx.get_bool_var(n);
        }

        if (!ctx.e_internalized(n) && !gate_ctx) {
            bool suppress_args = true;
            bool merge_tf      = !gate_ctx;
            ctx.mk_enode(n, suppress_args, merge_tf, true);
            ctx.set_enode_flag(v, is_new_var);
        }
        return true;
    }

    bool theory_bv::internalize_xor3(app * n, bool gate_ctx) {
        ctx.internalize(n->get_args(), 3, true);
        bool is_new_var = false;
        bool_var v;
        if (!ctx.b_internalized(n)) {
            is_new_var  = true;
            v           = ctx.mk_bool_var(n);
            literal r(v);
            literal l1 = ctx.get_literal(n->get_arg(0));
            literal l2 = ctx.get_literal(n->get_arg(1));
            literal l3 = ctx.get_literal(n->get_arg(2));
            ctx.mk_gate_clause(~r,  l1,  l2,  l3);
            ctx.mk_gate_clause(~r, ~l1, ~l2,  l3);
            ctx.mk_gate_clause(~r, ~l1,  l2, ~l3);
            ctx.mk_gate_clause(~r,  l1, ~l2, ~l3);
            ctx.mk_gate_clause( r, ~l1,  l2,  l3);
            ctx.mk_gate_clause( r,  l1, ~l2,  l3);
            ctx.mk_gate_clause( r,  l1,  l2, ~l3);
            ctx.mk_gate_clause( r, ~l1, ~l2, ~l3);
        }
        else {
            v = ctx.get_bool_var(n);
        }

        if (!ctx.e_internalized(n) && !gate_ctx) {
            bool suppress_args = true;
            bool merge_tf      = !gate_ctx;
            ctx.mk_enode(n, suppress_args, merge_tf, true);
            ctx.set_enode_flag(v, is_new_var);
        }
        return true;
    }

    bool theory_bv::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("bv", tout << "internalizing atom: " << mk_bounded_pp(atom, m) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());
        if (approximate_term(atom)) {
            return false;
        }
        switch (atom->get_decl_kind()) {
        case OP_BIT2BOOL:   mk_bit2bool(atom); return true;
        case OP_ULEQ:       internalize_le<false>(atom); return true;
        case OP_SLEQ:       internalize_le<true>(atom); return true;
        case OP_XOR3:       return internalize_xor3(atom, gate_ctx); 
        case OP_CARRY:      return internalize_carry(atom, gate_ctx); 
        case OP_BUMUL_NO_OVFL:  internalize_umul_no_overflow(atom); return true;
        case OP_BSMUL_NO_OVFL:  internalize_smul_no_overflow(atom); return true;
        case OP_BSMUL_NO_UDFL:  internalize_smul_no_underflow(atom); return true;
        default:
            UNREACHABLE();
            return false;
        }
    }

    //
    // Determine whether bit-vector expression should be approximated
    // based on the number of bits used by the arguments.
    // 
    bool theory_bv::approximate_term(app* n) {
        if (params().m_bv_blast_max_size == INT_MAX) {
            return false;
        }
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i <= num_args; i++) {
            expr* arg = (i == num_args)?n:n->get_arg(i);
            sort* s = arg->get_sort();
            if (m_util.is_bv_sort(s) && m_util.get_bv_size(arg) > params().m_bv_blast_max_size) {                
                if (!m_approximates_large_bvs) {
                    TRACE("bv", tout << "found large size bit-vector:\n" << mk_pp(n, m) << "\n";);
                    ctx.push_trail(value_trail<bool>(m_approximates_large_bvs));
                    m_approximates_large_bvs = true;
                }
                return true;
            }
        }
        return false;
    }

    void theory_bv::apply_sort_cnstr(enode * n, sort * s) {
        if (!is_attached_to_var(n) && !approximate_term(n->get_expr())) {
            mk_bits(mk_var(n));
            if (ctx.is_relevant(n)) {
                relevant_eh(n->get_expr());
            }
        }
    }
    
    void theory_bv::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE("bv_eq", tout << "new_eq: " << mk_pp(get_enode(v1)->get_expr(), m) << " = " << mk_pp(get_enode(v2)->get_expr(), m) << "\n";);
        TRACE("bv", tout << "new_eq_eh v" << v1 << " = v" << v2 << " @ " << ctx.get_scope_level() << 
              " relevant1: " << ctx.is_relevant(get_enode(v1)) << 
              " relevant2: " << ctx.is_relevant(get_enode(v2)) << "\n";);
        m_find.merge(v1, v2);
    }

    void theory_bv::new_diseq_eh(theory_var v1, theory_var v2) {
        if (is_bv(v1)) {
            SASSERT(m_bits[v1].size() == m_bits[v2].size());
            expand_diseq(v1, v2);
        }
    }

    void theory_bv::expand_diseq(theory_var v1, theory_var v2) {
        if (!params().m_bv_eq_axioms)
            return;

        SASSERT(get_bv_size(v1) == get_bv_size(v2));
        if (v1 > v2) {
            std::swap(v1, v2);
        }
        literal_vector const & bits1        = m_bits[v1];
        literal_vector::const_iterator it1  = bits1.begin();
        literal_vector::const_iterator end1 = bits1.end();
        literal_vector const & bits2        = m_bits[v2];
        literal_vector::const_iterator it2  = bits2.begin();
        for (; it1 != end1; ++it1, ++it2) {
            if (*it1 == ~(*it2))
                return; 
            lbool val1 = ctx.get_assignment(*it1);
            lbool val2 = ctx.get_assignment(*it2);
            if (val1 != l_undef && val2 != l_undef && val1 != val2) {
                return;
            }
        }

        if (params().m_bv_watch_diseq) {
            bool_var watch_var = null_bool_var;
            it1 = bits1.begin();
            it2 = bits2.begin();
            unsigned act = m_diseq_activity[hash_u_u(v1, v2) & 0xFF]++;
            
            for (; it1 != end1 && ((act & 0x3) != 0x3); ++it1, ++it2) {
                lbool val1 = ctx.get_assignment(*it1);
                lbool val2 = ctx.get_assignment(*it2);
                
                if (val1 == l_undef) {
                    watch_var = it1->var();
                }
                else if (val2 == l_undef) {
                    watch_var = it2->var();
                }
                else {
                    continue;
                }
                
                m_diseq_watch.reserve(watch_var+1);
                m_diseq_watch[watch_var].push_back(std::make_pair(v1, v2));
                m_diseq_watch_trail.push_back(watch_var);
                return;
            }
        }

        literal_vector & lits = m_tmp_literals;
        lits.reset();
        literal eq = mk_eq(get_enode(v1)->get_expr(), get_enode(v2)->get_expr(), true);
        lits.push_back(eq);
        it1 = bits1.begin();
        it2 = bits2.begin();
        for (; it1 != end1; ++it1, ++it2) {
            expr_ref l1(m), l2(m), diff(m);
            ctx.literal2expr(*it1, l1);
            ctx.literal2expr(*it2, l2);
            m_bb.mk_xor(l1, l2, diff);
            ctx.internalize(diff, true);
            literal arg = ctx.get_literal(diff);
            lits.push_back(arg);
        }
        TRACE("bv", 
              tout << mk_pp(get_enode(v1)->get_expr(), m) << " = " << mk_pp(get_enode(v2)->get_expr(), m) << " " 
              << ctx.get_scope_level() 
              << "\n";
              ctx.display_literals_smt2(tout, lits););

        m_stats.m_num_diseq_dynamic++;
        scoped_trace_stream st(*this, lits);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
    }

    void theory_bv::assign_eh(bool_var v, bool is_true) {
        atom * a      = get_bv2a(v);
        TRACE("bv", tout << "assert: p" << v << " #" << ctx.bool_var2expr(v)->get_id() << " is_true: " << is_true << " " << ctx.inconsistent() << "\n";);
        if (a->is_bit()) {
            m_prop_queue.reset();
            bit_atom * b = static_cast<bit_atom*>(a);
            var_pos_occ * curr = b->m_occs;
            while (curr) {
                m_prop_queue.push_back(var_pos(curr->m_var, curr->m_idx));
                curr = curr->m_next;
            }
            propagate_bits();

            if (params().m_bv_watch_diseq && !ctx.inconsistent() && m_diseq_watch.size() > static_cast<unsigned>(v)) {
                unsigned sz = m_diseq_watch[v].size();
                for (unsigned i = 0; i < sz; ++i) {
                    auto const & p = m_diseq_watch[v][i];
                    expand_diseq(p.first, p.second);
                }
                m_diseq_watch[v].reset();
            }
        }
    }
    
    void theory_bv::propagate_bits() {
        for (unsigned i = 0; i < m_prop_queue.size(); i++) {
            var_pos const & entry = m_prop_queue[i];
            theory_var v          = entry.first;
            unsigned idx          = entry.second;

            if (m_wpos[v] == idx)
                find_wpos(v);            

            literal_vector & bits = m_bits[v];
            literal bit           = bits[idx];
            lbool   val           = ctx.get_assignment(bit);            
            if (val == l_undef) {
                continue;
            }
            theory_var v2         = next(v);
            TRACE("bv", tout << "propagating v" << v << " #" << get_enode(v)->get_owner_id() << "[" << idx << "] = " << val << " " << ctx.get_scope_level() << "\n";);
            literal antecedent = bit;

            if (val == l_false) {
                antecedent.neg();
            }
            while (v2 != v) {
                literal_vector & bits2   = m_bits[v2];
                literal bit2             = bits2[idx];
                lbool   val2             = ctx.get_assignment(bit2);
                TRACE("bv_bit_prop", tout << "propagating #" << get_enode(v2)->get_owner_id() << "[" << idx << "] = " << val2 << "\n";);
                TRACE("bv", tout << bit << " -> " << bit2 << " " << val << " -> " << val2 << " " << ctx.get_scope_level() << "\n";);

                if (bit == ~bit2) {
                    add_new_diseq_axiom(v, v2, idx);
                    return;
                }

                if (val != val2) {
                    literal consequent = bit2;
                    if (val == l_false) {
                        consequent.neg();
                    }
                    assign_bit(consequent, v, v2, idx, antecedent, false);
                    if (ctx.inconsistent()) {
                        TRACE("bv", tout << "inconsistent " << bit <<  " " << bit2 << "\n";);
                        m_prop_queue.reset();
                        return;
                    }
                }
                v2 = next(v2);
            }            
        }
        m_prop_queue.reset();
        TRACE("bv_bit_prop", tout << "done propagating\n";);
    }

    void theory_bv::assign_bit(literal consequent, theory_var v1, theory_var v2, unsigned idx, literal antecedent, bool propagate_eqc) {

        m_stats.m_num_bit2core++;
        SASSERT(ctx.get_assignment(antecedent) == l_true);
        SASSERT(m_bits[v2][idx].var() == consequent.var());
        SASSERT(consequent.var() != antecedent.var());
        TRACE("bv_bit_prop", tout << "assigning: " << consequent << " @ " << ctx.get_scope_level();
              tout << " using "; ctx.display_literal(tout, antecedent); 
              tout << " #" << get_enode(v1)->get_owner_id() << " #" << get_enode(v2)->get_owner_id() << " idx: " << idx << "\n";
              tout << "propagate_eqc: " << propagate_eqc << "\n";);
        if (consequent == false_literal) {
            m_stats.m_num_conflicts++;
            ctx.set_conflict(mk_bit_eq_justification(v1, v2, consequent, antecedent));
        }
        else {
            ctx.assign(consequent, mk_bit_eq_justification(v1, v2, consequent, antecedent));
            if (params().m_bv_eq_axioms) {
                literal_vector lits;
                lits.push_back(~consequent);
                lits.push_back(antecedent);
                literal eq = mk_eq(get_expr(v1), get_expr(v2), false);
                lits.push_back(~eq);
                //
                // Issue #3035:
                // merge_eh invokes assign_bit, which updates the propagation queue and includes the 
                // theory axiom for the propagated equality. When relevancy is non-zero, propagation may get
                // lost on backtracking because the propagation queue is reset on conflicts.
                // An alternative approach is to ensure the propagation queue is chronological with
                // backtracking scopes (ie., it doesn't get reset, but shrunk to a previous level, and similar
                // with a qhead indicator.
                // 
                ctx.mark_as_relevant(lits[0]);
                ctx.mark_as_relevant(lits[1]);
                ctx.mark_as_relevant(lits[2]);
                {
                    scoped_trace_stream _sts(*this, lits);
                    ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
                }
            }
     
            if (m_wpos[v2] == idx)
                find_wpos(v2);
            // REMARK: bit_eq_justification is marked as a theory_bv justification.
            // Thus, the assignment to consequent will not be notified back to the theory.
            // So, we need to propagate the assignment to other bits.
            bool_var bv = consequent.var();
            atom * a    = get_bv2a(bv);
            SASSERT(a->is_bit());
            bit_atom * b = static_cast<bit_atom*>(a);
            var_pos_occ * curr = b->m_occs;
            while (curr) {
                TRACE("assign_bit_bug", tout << "curr->m_var: v" << curr->m_var << ", curr->m_idx: " << curr->m_idx << ", v2: v" << v2 << ", idx: " << idx << "\n";
                      tout << "find(curr->m_var): v" << find(curr->m_var) << ", find(v2): v" << find(v2) << "\n";
                      tout << "is bit of #" << get_enode(curr->m_var)->get_owner_id() << "\n";
                      );
                // If find(curr->m_var) == find(v2) && curr->m_idx == idx and propagate_eqc == false, then
                // this bit will be propagated to the equivalence class of v2 by assign_bit caller.
                if (propagate_eqc || find(curr->m_var) != find(v2) || curr->m_idx != idx)
                    m_prop_queue.push_back(var_pos(curr->m_var, curr->m_idx));
                curr = curr->m_next;
            }
        }
    }

    void theory_bv::relevant_eh(app * n) {
        TRACE("arith", tout << "relevant: #" << n->get_id() << " " << ctx.e_internalized(n) << ": " << mk_pp(n, m) << "\n";);
        TRACE("bv", tout << "relevant: #" << n->get_id() << " " << ctx.e_internalized(n) << ": " << mk_pp(n, m) << "\n";);
        if (m.is_bool(n)) {
            bool_var v = ctx.get_bool_var(n);
            atom * a   = get_bv2a(v);
            if (a && !a->is_bit()) {
                le_atom * le = static_cast<le_atom*>(a);
                ctx.mark_as_relevant(le->m_def);
                if (params().m_bv_lazy_le) {
                    ctx.mk_th_axiom(get_id(), le->m_var, ~le->m_def);
                    ctx.mk_th_axiom(get_id(), ~le->m_var, le->m_def);
                }
            }
        }
        else if (params().m_bv_enable_int2bv2int && m_util.is_bv2int(n)) {
            ctx.mark_as_relevant(n->get_arg(0));
            assert_bv2int_axiom(n);
        }
        else if (params().m_bv_enable_int2bv2int && m_util.is_int2bv(n)) {
            ctx.mark_as_relevant(n->get_arg(0));
            assert_int2bv_axiom(n);
        }
        else if (ctx.e_internalized(n)) {
            enode * e    = ctx.get_enode(n);
            theory_var v = e->get_th_var(get_id());
            if (v != null_theory_var) {
                literal_vector & bits        = m_bits[v];
                TRACE("bv", tout << "mark bits relevant: " << bits.size() << ": " << bits << "\n";);
                SASSERT(!is_bv(v) || bits.size() == get_bv_size(v));
                for (literal lit : bits) {
                    ctx.mark_as_relevant(lit);
                }
            }
        }
    }

    void theory_bv::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
        // check_invariant();
        m_diseq_watch_lim.push_back(m_diseq_watch_trail.size());
    }
    
    void theory_bv::pop_scope_eh(unsigned num_scopes) {
        m_trail_stack.pop_scope(num_scopes);
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        m_bits.shrink(num_old_vars);
        m_wpos.shrink(num_old_vars);
        m_zero_one_bits.shrink(num_old_vars);
        unsigned old_trail_sz = m_diseq_watch_lim[m_diseq_watch_lim.size()-num_scopes];
        for (unsigned i = m_diseq_watch_trail.size(); i-- > old_trail_sz;) {
            if (!m_diseq_watch[m_diseq_watch_trail[i]].empty()) {
                m_diseq_watch[m_diseq_watch_trail[i]].pop_back();
            }
        }
        m_diseq_watch_trail.shrink(old_trail_sz);
        m_diseq_watch_lim.shrink(m_diseq_watch_lim.size()-num_scopes);
        theory::pop_scope_eh(num_scopes);
        TRACE("bv_verbose", m_find.display(tout << ctx.get_scope_level() << " - " 
                                   << num_scopes << " = " << (ctx.get_scope_level() - num_scopes) << "\n"););
    }

    final_check_status theory_bv::final_check_eh() {
        SASSERT(check_invariant());
        if (m_approximates_large_bvs) {
            return FC_GIVEUP;
        }
        return FC_DONE;
    }

    void theory_bv::reset_eh() {
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_bool_var2atom.reset();
        m_fixed_var_table.reset();
        theory::reset_eh();
    }

    bool theory_bv::include_func_interp(func_decl* f) {
        SASSERT(f->get_family_id() == get_family_id());
        switch (f->get_decl_kind()) {
        case OP_BSDIV0:
        case OP_BUDIV0:
        case OP_BSREM0:
        case OP_BUREM0:       
        case OP_BSMOD0:        
            return true;
        default:
            return false;
        }
        return false;
    }

    smt_params const& theory_bv::params() const { 
        return ctx.get_fparams(); 
    }

    theory_bv::theory_bv(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("bv")),
        m_util(ctx.get_manager()),
        m_autil(ctx.get_manager()),
        m_bb(ctx.get_manager(), ctx.get_fparams()),
        m_trail_stack(),
        m_find(*this),
        m_approximates_large_bvs(false) {
        memset(m_eq_activity, 0, sizeof(m_eq_activity));
        memset(m_diseq_activity, 0, sizeof(m_diseq_activity));
    }

    theory_bv::~theory_bv() {
    }

    theory* theory_bv::mk_fresh(context* new_ctx) {
        return alloc(theory_bv, *new_ctx);
    }

    
    void theory_bv::merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {
        TRACE("bv", tout << "merging: v" << v1 << " #" << get_enode(v1)->get_owner_id() << " v" << v2 << " #" << get_enode(v2)->get_owner_id() << "\n";);
        TRACE("bv_bit_prop", tout << "merging: #" << get_enode(v1)->get_owner_id() << " #" << get_enode(v2)->get_owner_id() << "\n";);
        if (!merge_zero_one_bits(r1, r2)) {
            TRACE("bv", tout << "conflict detected\n";);
            return; // conflict was detected
        }
        m_prop_queue.reset();
        SASSERT(m_bits[v1].size() == m_bits[v2].size());
        unsigned sz  = m_bits[v1].size();
        bool changed = true;
        TRACE("bv", tout << "bits size: " << sz << "\n";);
        do {
            // This outerloop is necessary to avoid missing propagation steps.
            // For example, let's assume that bits1 and bits2 contains the following
            // sequence of bits:
            //        b4 b3 b2 b1
            //        b5 b4 b3 b2
            // Let's also assume that b1 is assigned, and b2, b3, b4, and b5 are not.
            // Only the propagation from b1 to b2 is performed by the first iteration of this
            // loop. 
            //
            // In the worst case, we need to execute this loop bits1.size() times.
            //
            // Remark: the assignment to b2 is marked as a bv theory propagation,
            // then it is not notified to the bv theory.
            changed                   = false;
            for (unsigned idx = 0; idx < sz; idx++) {
                literal bit1  = m_bits[v1][idx];
                literal bit2  = m_bits[v2][idx];
                if (bit1 == ~bit2) {
                    add_new_diseq_axiom(v1, v2, idx);
                    return;
                }
                lbool val1    = ctx.get_assignment(bit1);
                lbool val2    = ctx.get_assignment(bit2);
                TRACE("bv", tout << "merge v" << v1 << " " << bit1 << ":= " << val1 << " " << bit2 << ":= " << val2 << "\n";);
                if (val1 == l_undef && !ctx.is_relevant(bit1))
                    ctx.mark_as_relevant(bit1);
                if (val2 == l_undef && !ctx.is_relevant(bit2))
                    ctx.mark_as_relevant(bit2);
                if (val1 == val2) 
                    continue;
                changed = true;
                if (val1 != l_undef && val2 != l_undef) {
                    TRACE("bv", tout << "inconsistent "; display_var(tout, v1); display_var(tout, v2); tout << "idx: " << idx << "\n";);
                }
                if (val1 != l_undef && bit2 != false_literal && bit2 != true_literal) {
                    literal antecedent = bit1;
                    literal consequent = bit2;
                    if (val1 == l_false) {
                        consequent.neg();
                        antecedent.neg();
                    }
                    assign_bit(consequent, v1, v2, idx, antecedent, true);
                }
                else if (val2 != l_undef) {
                    literal antecedent = bit2;
                    literal consequent = bit1;
                    if (val2 == l_false) {
                        consequent.neg();
                        antecedent.neg();
                    }
                    assign_bit(consequent, v2, v1, idx, antecedent, true);
                }
                if (ctx.inconsistent())
                    return;
                if (val1 != l_undef && val2 != l_undef && val1 != val2) {
                    UNREACHABLE();
                }
                
            }
        }
        while(changed);

        propagate_bits();
    }

    bool theory_bv::merge_zero_one_bits(theory_var r1, theory_var r2) {
        zero_one_bits & bits2 = m_zero_one_bits[r2];
        if (bits2.empty())
            return true;
        zero_one_bits & bits1 = m_zero_one_bits[r1];
        unsigned bv_size = get_bv_size(r1);
        SASSERT(bv_size == get_bv_size(r2));
        m_merge_aux[0].reserve(bv_size+1, null_theory_var);
        m_merge_aux[1].reserve(bv_size+1, null_theory_var);

        auto reset_merge_aux = [&]() { for (auto & zo : bits1) m_merge_aux[zo.m_is_true][zo.m_idx] = null_theory_var; };

        DEBUG_CODE(for (unsigned i = 0; i < bv_size; i++) { 
                SASSERT(m_merge_aux[0][i] == null_theory_var || m_merge_aux[1][i] == null_theory_var); }
            );
        // save info about bits1
        for (auto & zo : bits1) m_merge_aux[zo.m_is_true][zo.m_idx] = zo.m_owner;
        // check if bits2 is consistent with bits1, and copy new bits to bits1
        for (auto & zo : bits2) {
            theory_var v2 = zo.m_owner;
            theory_var v1 = m_merge_aux[!zo.m_is_true][zo.m_idx];
            if (v1 != null_theory_var) {
                // conflict was detected ... v1 and v2 have complementary bits
                SASSERT(m_bits[v1][zo.m_idx] == ~(m_bits[v2][zo.m_idx]));
                SASSERT(m_bits[v1].size() == m_bits[v2].size());
                add_new_diseq_axiom(v1, v2, zo.m_idx);
                reset_merge_aux();
                return false;
            }
            if (m_merge_aux[zo.m_is_true][zo.m_idx] == null_theory_var) {
                // copy missing variable to bits1
                bits1.push_back(zo);
            }
        }
        // reset m_merge_aux vector
        reset_merge_aux();
        DEBUG_CODE(for (unsigned i = 0; i < bv_size; i++) { SASSERT(m_merge_aux[0][i] == null_theory_var || m_merge_aux[1][i] == null_theory_var); });
        return true;
    }

    void theory_bv::propagate() {
        if (!can_propagate())
            return;
        ctx.push_trail(value_trail<unsigned>(m_prop_diseqs_qhead));
        for (; m_prop_diseqs_qhead < m_prop_diseqs.size() && !ctx.inconsistent(); ++m_prop_diseqs_qhead) {
            auto p = m_prop_diseqs[m_prop_diseqs_qhead];
            assert_new_diseq_axiom(p.v1, p.v2, p.idx);
        }
    }

    class bit_eq_justification : public justification {
        enode *   m_v1;
        enode *   m_v2;
        theory_id m_th_id; // TODO: steal 4 bits from each one of the following literas and use them to represent the th_id.
        literal   m_consequent;
        literal   m_antecedent;
    public:
        bit_eq_justification(theory_id th_id, enode * v1, enode * v2, literal c, literal a):
            m_v1(v1), m_v2(v2), m_th_id(th_id), m_consequent(c), m_antecedent(a) {}

        void get_antecedents(conflict_resolution & cr) override {
            cr.mark_eq(m_v1, m_v2);
            if (m_antecedent.var() != true_bool_var)
                cr.mark_literal(m_antecedent);
        }

        proof * mk_proof(conflict_resolution & cr) override {
            bool visited = true;
            ptr_buffer<proof> prs;
            proof * pr = cr.get_proof(m_v1, m_v2);
            if (pr)
                prs.push_back(pr);
            else 
                visited = false;
            if (m_antecedent.var() != true_bool_var) {
                proof * pr = cr.get_proof(m_antecedent);
                if (pr)
                    prs.push_back(pr);
                else
                    visited = false;
            }
            if (!visited)
                return nullptr;
            context & ctx = cr.get_context();
            ast_manager & m = cr.get_manager();
            expr_ref fact(m);
            ctx.literal2expr(m_consequent, fact);
            return m.mk_th_lemma(get_from_theory(), fact, prs.size(), prs.data());
        }

        theory_id get_from_theory() const override {
            return m_th_id;
        }

        char const * get_name() const override { return "bv-bit-eq"; }
    };

    inline justification * theory_bv::mk_bit_eq_justification(theory_var v1, theory_var v2, literal consequent, literal antecedent) {
        return ctx.mk_justification(bit_eq_justification(get_id(), get_enode(v1), get_enode(v2), consequent, antecedent));
    }

    void theory_bv::unmerge_eh(theory_var v1, theory_var v2) {
                
        // v1 was the root of the equivalence class
        // I must remove the zero_one_bits that are from v2.

        // REMARK: it is unsafe to invoke check_zero_one_bits, since
        // the enode associated with v1 and v2 may have already been
        // deleted. 
        //
        // The logical context trail_stack is popped before
        // the theories pop_scope_eh is invoked.

        zero_one_bits & bits = m_zero_one_bits[v1]; 
        if (bits.empty()) {
            // SASSERT(check_zero_one_bits(v1));
            // SASSERT(check_zero_one_bits(v2));
            return;
        }
        unsigned j  = bits.size();
        while (j > 0) {
            --j;
            zero_one_bit & bit = bits[j];
            if (find(bit.m_owner) == v1) {
                bits.shrink(j+1);
                // SASSERT(check_zero_one_bits(v1));
                // SASSERT(check_zero_one_bits(v2));
                return;
            }
        }
        bits.shrink(0);
        // SASSERT(check_zero_one_bits(v1));
        // SASSERT(check_zero_one_bits(v2));
    }

    bool theory_bv::get_lower(enode* n, rational& value) {
        theory_var v = n->get_th_var(get_id());
        if (v != null_theory_var && is_bv(v)) {
            value = 0;
            rational p(1);
            for (literal bit : m_bits[v]) {
                switch (ctx.get_assignment(bit)) {
                case l_true:
                    value += p;
                    break;
                default:
                    break;
                }
                p *= 2;
            }
            return true;
        }
        return false;
    }

    bool theory_bv::get_upper(enode* n, rational& value) {
        theory_var v = n->get_th_var(get_id());
        if (v != null_theory_var && is_bv(v)) {
            literal_vector const & bits = m_bits[v];
            rational p = rational::power_of_two(bits.size());
            value = p - 1;
            p /= 2;
            for (unsigned i = bits.size(); i-- > 0; ) {
                switch (ctx.get_assignment(bits[i])) {
                case l_false:
                    value -= p;
                    break;
                case l_true:
                    break;
                default: {                 
                    break;
                }
                }
                p /= 2;
            }
            return true;
        }
        return false;
    }

    void theory_bv::init_model(model_generator & mg) {
        m_factory = alloc(bv_factory, m);
        mg.register_factory(m_factory);
    }

    model_value_proc * theory_bv::mk_value(enode * n, model_generator & mg) {
        numeral val;
        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
#ifdef Z3DEBUG
        bool r = 
#endif
        get_fixed_value(v, val);
        SASSERT(r);
        return alloc(expr_wrapper_proc, m_factory->mk_num_value(val, get_bv_size(v)));
    }

    void theory_bv::display_var(std::ostream & out, theory_var v) const {
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " #";
        out.width(4);
        out << get_enode(v)->get_owner_id() << " -> #";
        out.width(4);
        out << get_enode(find(v))->get_owner_id();
        out << std::right << ", bits:";
        literal_vector const & bits = m_bits[v];
        for (literal lit : bits) {
            out << " " << lit << ":";
            ctx.display_literal(out, lit);
        }
        numeral val;
        if (get_fixed_value(v, val))
            out << ", value: " << val;
        out << "\n";
    }

    void theory_bv::display_bit_atom(std::ostream & out, bool_var v, bit_atom const * a) const {
        out << "#" << ctx.bool_var2expr(v)->get_id() << " ->";
        var_pos_occ * curr = a->m_occs;
        while (curr) {
            out << " #" << get_enode(curr->m_var)->get_owner_id() << "[" << curr->m_idx << "]";
            curr = curr->m_next;
        }
        out << "\n";
    }

    void theory_bv::display_atoms(std::ostream & out) const {
        out << "atoms:\n";
        unsigned num  = ctx.get_num_bool_vars();
        for (unsigned v = 0; v < num; v++) {
            atom * a = get_bv2a(v);
            if (a && a->is_bit())
                display_bit_atom(out, v, static_cast<bit_atom*>(a));
        }
    }

    void theory_bv::display(std::ostream & out) const {
        unsigned num_vars = get_num_vars();
        if (num_vars == 0) return;
        out << "Theory bv:\n";
        for (unsigned v = 0; v < num_vars; v++) {
            display_var(out, v);
        }
        display_atoms(out);
    }

    void theory_bv::collect_statistics(::statistics & st) const {
        st.update("bv conflicts", m_stats.m_num_conflicts);
        st.update("bv diseqs", m_stats.m_num_diseq_static);
        st.update("bv dynamic diseqs", m_stats.m_num_diseq_dynamic);
        st.update("bv bit2core", m_stats.m_num_bit2core);
        st.update("bv->core eq", m_stats.m_num_th2core_eq);
        st.update("bv dynamic eqs", m_stats.m_num_eq_dynamic);
    }

    bool theory_bv::check_assignment(theory_var v) {
        if (!is_root(v))
            return true;
        if (!ctx.is_relevant(get_enode(v))) {
            return true;
        }

        theory_var v2                 = v;
        literal_vector const & bits2  = m_bits[v2];
        theory_var v1                 = v2;
        do {
            literal_vector const & bits1 = m_bits[v1];
            SASSERT(bits1.size() == bits2.size());
            unsigned sz = bits1.size();
            VERIFY(ctx.is_relevant(get_enode(v1)));
            for (unsigned i = 0; i < sz; i++) {
                literal bit1 = bits1[i];
                literal bit2 = bits2[i];
                lbool val1   = ctx.get_assignment(bit1);
                lbool val2   = ctx.get_assignment(bit2);
                CTRACE("bv_bug", val1 != val2, 
                       tout << "equivalence class is inconsistent, i: " << i << "\n";
                       display_var(tout, v1);
                       display_var(tout, v2);
                       if (bit1 != true_literal && bit1 != false_literal) tout << "bit1 relevant: " << ctx.is_relevant(bit1) << " "; 
                       if (bit2 != true_literal && bit2 != false_literal) tout << "bit2 relevant: " << ctx.is_relevant(bit2) << "\n";
                       tout << "val1: " << val1 << " lvl: " << ctx.get_assign_level(bit1.var()) << " bit " << bit1 << "\n";
                       tout << "val2: " << val2 << " lvl: " << ctx.get_assign_level(bit2.var()) << " bit " << bit2 << "\n";
                       tout << "level: " << ctx.get_scope_level() << "\n";
                       );
                VERIFY(val1 == val2);
            }
            v1 = next(v1);
        }
        while (v1 != v);
        return true;
    }

    /**
       \brief Check whether m_zero_one_bits is an accurate summary of the bits in the 
       equivalence class rooted by v.
       
       \remark The method does nothing if v is not the root of the equivalence class.
    */
    bool theory_bv::check_zero_one_bits(theory_var v) {
        if (ctx.inconsistent())
            return true; // property is only valid if the context is not in a conflict.
        if (is_root(v) && is_bv(v)) {
            bool_vector bits[2];
            unsigned      num_bits = 0;
            unsigned      bv_sz    = get_bv_size(v);
            bits[0].resize(bv_sz, false);
            bits[1].resize(bv_sz, false);
            theory_var curr = v;
            do {
                literal_vector const & lits = m_bits[curr];
                for (unsigned i = 0; i < lits.size(); i++) {
                    literal l = lits[i];
                    if (l.var() == true_bool_var) {
                        unsigned is_true = (l == true_literal);
                        if (bits[!is_true][i]) {
                            // expect a conflict later on.
                            return true;
                        }
                        if (!bits[is_true][i]) {
                            bits[is_true][i] = true;
                            num_bits++;
                        }
                    }
                }
                curr = next(curr);
            }
            while (curr != v);

            zero_one_bits const & _bits = m_zero_one_bits[v];
            SASSERT(_bits.size() == num_bits);
            bool_vector already_found;
            already_found.resize(bv_sz, false);
            for (auto & zo : _bits) {
                SASSERT(find(zo.m_owner) == v);
                SASSERT(bits[zo.m_is_true][zo.m_idx]);
                SASSERT(!already_found[zo.m_idx]);
                already_found[zo.m_idx] = true;
            }
        }
        return true;
    }

    bool theory_bv::check_invariant() {
        if (m.limit().is_canceled())
            return true;
        if (ctx.inconsistent())
            return true;
        unsigned num = get_num_vars();
        for (unsigned v = 0; v < num; v++) {
            check_assignment(v);
            check_zero_one_bits(v);
        }
        return true;
    }


};
