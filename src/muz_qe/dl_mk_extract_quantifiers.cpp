/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers.cpp

Abstract:

    Remove universal quantifiers over interpreted predicates in the body.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/

#include"dl_mk_extract_quantifiers.h"
#include"ast_pp.h"
#include"dl_bmc_engine.h"
#include"smt_quantifier.h"
#include"smt_context.h"
#include"for_each_expr.h"
#include "expr_abstract.h"


namespace datalog {


    mk_extract_quantifiers::mk_extract_quantifiers(context & ctx) : 
        rule_transformer::plugin(101, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_query_pred(m)
    {}

    mk_extract_quantifiers::~mk_extract_quantifiers() {
        reset();
    }

    void mk_extract_quantifiers::set_query(func_decl* q) {
        m_query_pred = q;
    }

    void mk_extract_quantifiers::ensure_predicate(expr* e, unsigned& max_var, app_ref_vector& tail) {
        SASSERT(is_app(e));
        SASSERT(to_app(e)->get_decl()->get_family_id() == null_family_id);
        app* a = to_app(e);
        expr_ref_vector args(m);        
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr* arg = a->get_arg(i);
            if (is_var(arg) || m.is_value(arg)) {
                args.push_back(arg);
            }
            else {
                expr_ref new_var(m);
                new_var = m.mk_var(++max_var, m.get_sort(arg));
                args.push_back(new_var);
                tail.push_back(m.mk_eq(new_var, arg));
            }
        }
        tail.push_back(m.mk_app(a->get_decl(), args.size(), args.c_ptr()));
    }

    class mk_extract_quantifiers::collect_insts {
        ast_manager&     m;
        ptr_vector<expr>        m_binding;
        vector<expr_ref_vector> m_bindings;
        ptr_vector<quantifier>  m_quantifiers;
    public:
        collect_insts(ast_manager& m): m(m) { }

        void operator()(expr* n) {
            expr* not_q_or_i, *e1, *e2, *e3;
            if (m.is_quant_inst(n, not_q_or_i, m_binding)) {
                VERIFY(m.is_or(not_q_or_i, e1, e2));
                VERIFY(m.is_not(e1, e3));
                SASSERT(is_quantifier(e3));
                m_quantifiers.push_back(to_quantifier(e3));
                m_bindings.push_back(expr_ref_vector(m,m_binding.size(), m_binding.c_ptr()));
                m_binding.reset();
            }
            else if ((m.is_rewrite(n, e1, e2) ||
                      (m.is_rewrite_star(n) && 
                       (e3 = to_app(n)->get_arg(to_app(n)->get_num_args()-1),
                        e1 = to_app(e3)->get_arg(0),
                        e2 = to_app(e3)->get_arg(1),
                        true))) &&
                     is_quantifier(e1) && m.is_false(e2)) {
                quantifier* q = to_quantifier(e1);
                m_quantifiers.push_back(q);
                m_bindings.push_back(expr_ref_vector(m));
                expr_ref_vector& b = m_bindings.back();
                for (unsigned i = 0; i < q->get_num_decls(); ++i) {
                    b.push_back(m.mk_fresh_const("V", q->get_decl_sort(i)));
                }
            }
        }

        void reset() {
            m_quantifiers.reset();
            m_bindings.reset();
        }

        unsigned size() const { return m_quantifiers.size(); }
        ptr_vector<quantifier> const& quantifiers() const { return m_quantifiers; }
        vector<expr_ref_vector> const& bindings() const { return m_bindings; }        
    };


    /*
     * forall y . P1(x,y) & 
     * forall y . P2(x,y) & 
     * Body[x] & 
     * ~H[x]
     * forall y . y != binding1 => ~ P1(x,y)
     * forall y . y != binding2 => ~ P2(x,y)
     */
    void mk_extract_quantifiers::extract(rule& r, rule_set& new_rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        expr_ref_vector conjs(m);
        quantifier_ref_vector qs(m);
        for (unsigned i = utsz; i < r.get_tail_size(); ++i) {
            conjs.push_back(r.get_tail(i));
        }
        datalog::flatten_and(conjs);
        for (unsigned j = 0; j < conjs.size(); ++j) {
            expr* e = conjs[j].get();
            quantifier* q;
            if (rule_manager::is_forall(m, e, q)) {
                qs.push_back(q);
                conjs[j] = conjs.back();
                conjs.pop_back();
                --j;
            }
        }
        if (qs.empty()) {
            new_rules.add_rule(&r);
        }
        else {
            expr_ref fml(m);
            expr_ref_vector bindings(m);
            obj_map<quantifier, expr_ref_vector*> insts;
            for (unsigned i = 0; i < qs.size(); ++i) {
                insts.insert(qs[i].get(), alloc(expr_ref_vector, m));
            }

            unsigned max_inst = 10; // TODO configuration.
            
            for (unsigned i = 0; i < max_inst; ++i) {
                app_ref_vector sub(m);
                rule2formula(r, insts, fml, sub);
                bool new_binding = find_instantiations_proof_based(fml, sub, insts, bindings);
                if (!new_binding) {
                    break;
                }
            }

            expr_ref_vector fmls(m);
            for (unsigned i = 0; i < utsz; ++i) {
                fmls.push_back(r.get_tail(i));
            }
            fmls.append(bindings);
            fmls.append(conjs);
            fml = m.mk_implies(m.mk_and(fmls.size(), fmls.c_ptr()), r.get_head());
            TRACE("dl", tout << "new rule\n" << mk_pp(fml, m) << "\n";);
            rule_ref_vector rules(rm);
            proof_ref pr(m);
            if (m_ctx.generate_proof_trace()) {
                scoped_proof _scp(m);
                expr_ref fml1(m);
                r.to_formula(fml1);
                pr = m.mk_rewrite(fml1, fml);
                pr = m.mk_modus_ponens(r.get_proof(), pr);
            }
            rm.mk_rule(fml, pr, rules, r.name());
            for (unsigned i = 0; i < rules.size(); ++i) {
                new_rules.add_rule(rules[i].get());
                m_quantifiers.insert(rules[i].get(), alloc(quantifier_ref_vector, qs));
            }
            obj_map<quantifier, expr_ref_vector*>::iterator it = insts.begin(), end = insts.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
        }
    }

    void mk_extract_quantifiers::rule2formula(
        rule& r,
        obj_map<quantifier, expr_ref_vector*> const& insts,
        expr_ref& fml,
        app_ref_vector& sub)
    {
        expr_ref body(m);
        expr_ref_vector fmls(m);
        ptr_vector<sort> sorts;
        var_subst vs(m, false);
        obj_map<quantifier, expr_ref_vector*>::iterator it = insts.begin(), end = insts.end();
        for (; it != end; ++it) {
            quantifier* q = it->m_key;
            expr_ref_vector& eqs = *it->m_value;
            expr_ref_vector disj(m);
            disj.append(eqs);
            disj.push_back(m.mk_not(q->get_expr()));
            body = m.mk_or(disj.size(), disj.c_ptr());
            fml = m.update_quantifier(q, body);
            fmls.push_back(fml); 
        }
        fml = m.mk_or(fmls.size(), fmls.c_ptr());
        fmls.reset();
        fmls.push_back(fml);
        for (unsigned i = 0; i < r.get_tail_size(); ++i) {
            SASSERT(!r.is_neg_tail(i));
            fmls.push_back(r.get_tail(i));
        }
        fmls.push_back(m.mk_not(r.get_head()));
        fml = m.mk_and(fmls.size(), fmls.c_ptr());
        
        get_free_vars(fml, sorts);
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (!sorts[i]) {
                sorts[i] = m.mk_bool_sort();
            }
            sub.push_back(m.mk_const(symbol(i), sorts[i]));
        }
        vs(fml, sub.size(), (expr*const*)sub.c_ptr(), fml);        
    }
    
    bool mk_extract_quantifiers::find_instantiations_proof_based(
        expr*                        fml,
        app_ref_vector const&        var_inst,
        obj_map<quantifier, expr_ref_vector*>& insts,
        expr_ref_vector&             bindings)
    {
        datalog::scoped_proof _scp(m);
        smt_params fparams;
        fparams.m_mbqi = true; // false
        fparams.m_soft_timeout = 1000;
        smt::kernel solver(m, fparams);
        solver.assert_expr(fml);
        IF_VERBOSE(1, verbose_stream() << "check\n";);
        lbool result = solver.check();
        IF_VERBOSE(1, verbose_stream() << "checked\n";);
        TRACE("dl", tout << result << "\n";);
        if (result != l_false) {
            return false;
        }  

        map<symbol, quantifier*, symbol_hash_proc, symbol_eq_proc> qid_map;
        quantifier* q;
        
        obj_map<quantifier, expr_ref_vector*>::iterator it = insts.begin(), end = insts.end();
        for (; it != end; ++it) {
            q = it->m_key;
            qid_map.insert(q->get_qid(), q);
        }

        proof* p = solver.get_proof();
        TRACE("dl", tout << mk_pp(p, m) << "\n";);
        collect_insts collector(m);
        for_each_expr(collector, p);
        ptr_vector<quantifier> const& quants = collector.quantifiers();

        for (unsigned i = 0; i < collector.size(); ++i) {
            symbol qid = quants[i]->get_qid();
            if (!qid_map.find(qid, q)) {
                TRACE("dl", tout << "Could not find quantifier " << mk_pp(quants[i], m) << "\n";);
                continue;
            }
            expr_ref_vector const& binding = collector.bindings()[i];

            TRACE("dl", tout << "Instantiating:\n" << mk_pp(quants[i], m) << "\n";
                  for (unsigned j = 0; j < binding.size(); ++j) {
                      tout << mk_pp(binding[j], m) << " ";
                  }
                  tout << "\n";);

            expr_ref_vector instantiation(m);
            for (unsigned j = 0; j < binding.size(); ++j) {
                instantiation.push_back(binding[j]);
            }
            add_binding(var_inst, bindings, q, instantiation, insts);
        }

        return collector.size() > 0;
    }

    void mk_extract_quantifiers::add_binding(
        app_ref_vector const&        var_inst,
        expr_ref_vector&             bindings,
        quantifier*                  q, 
        expr_ref_vector const&       instantiation,
        obj_map<quantifier, expr_ref_vector*>& insts)
    {      
        if (instantiation.size() == q->get_num_decls()) {
            // Full binding. 
            apply_binding(var_inst, bindings, q, instantiation, insts);
        }
    }
     
    void mk_extract_quantifiers::apply_binding(
        app_ref_vector const&        var_inst,
        expr_ref_vector&             bindings,
        quantifier*                  q, 
        expr_ref_vector const&       instantiation,
        obj_map<quantifier, expr_ref_vector*>& insts)
    {          
        datalog::scoped_no_proof _scp(m);
        expr_ref e(m);
        expr_ref_vector eqs(m);
        var_subst vs(m, false);
        inv_var_shifter invsh(m);
        vs(q->get_expr(), instantiation.size(), instantiation.c_ptr(), e);
        invsh(e, q->get_num_decls(), e);
        expr_ref_vector inst(m);
        inst.append(var_inst.size(), (expr*const*)var_inst.c_ptr());
        inst.reverse();
        expr_abstract(m, 0, inst.size(), inst.c_ptr(), e, e);
        bindings.push_back(e);        
        for (unsigned i = 0; i < instantiation.size(); ++i) {
            e = instantiation[i];
            e = m.mk_eq(m.mk_var(i, q->get_decl_sort(i)), e);
            eqs.push_back(e);
        }
        e = m.mk_and(eqs.size(), eqs.c_ptr());
        insts.find(q)->push_back(e);

        TRACE("dl", tout << mk_pp(q, m) << "\n";
              tout << "instantiation: ";
              for (unsigned i = 0; i < instantiation.size(); ++i) {
                  tout << mk_pp(instantiation[i], m) << " ";
              }
              tout << "\n";
              tout << "inst: ";
              for (unsigned i = 0; i < var_inst.size(); ++i) {
                  tout << mk_pp(var_inst[i], m) << " ";
              }
              tout << "\n";
              tout << mk_pp(bindings.back(), m) << "\n";
              tout << "eqs: " << mk_pp(e, m) << "\n";
              );
    }


    void mk_extract_quantifiers::reset() {
        obj_map<rule const, quantifier_ref_vector*>::iterator it = m_quantifiers.begin(),
            end = m_quantifiers.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_has_quantifiers = false;
        m_quantifiers.reset();
    }
    
    rule_set * mk_extract_quantifiers::operator()(rule_set const & source) {
        reset();
        rule_set::iterator it = source.begin(), end = source.end();
        for (; !m_has_quantifiers && it != end; ++it) {
            m_has_quantifiers = (*it)->has_quantifiers();
        }
        if (!m_has_quantifiers) {
            return 0;
        }

        rule_set* rules = alloc(rule_set, m_ctx);
        it = source.begin();
        for (; it != end; ++it) {
            extract(**it, *rules);
        }

        return rules;
    }

};


