/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers2.cpp

Abstract:

    Remove universal quantifiers over interpreted predicates in the body.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/

#include"dl_mk_extract_quantifiers2.h"
#include"ast_pp.h"
#include"dl_bmc_engine.h"
#include"smt_quantifier.h"
#include"smt_context.h"

namespace datalog {


    mk_extract_quantifiers2::mk_extract_quantifiers2(context & ctx) : 
        rule_transformer::plugin(101, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_query_pred(m),
        m_quantifiers(m),
        m_refs(m)
    {}

    mk_extract_quantifiers2::~mk_extract_quantifiers2() {
        reset();
    }

    void mk_extract_quantifiers2::set_query(func_decl* q) {
        m_query_pred = q;
    }

    bool mk_extract_quantifiers2::matches_signature(func_decl* head, expr_ref_vector const& binding) {
        unsigned sz = head->get_arity();
        if (sz != binding.size()) {
            return false;
        }
        for (unsigned i = 0; i < sz; ++i) {
            if (head->get_domain(i) != m.get_sort(binding[sz-i-1])) {
                return false;
            }
        }
        return true;
    }

    bool mk_extract_quantifiers2::matches_quantifier(quantifier* q, expr_ref_vector const& binding) {
        unsigned sz = q->get_num_decls();
        if (sz != binding.size()) {
            return false;
        }
        for (unsigned i = 0; i < sz; ++i) {
            if (q->get_decl_sort(i) != m.get_sort(binding[sz-i-1])) {
                return false;
            }
        }
        return true;
    }

    bool mk_extract_quantifiers2::mk_abstract_expr(expr_ref& term) {
        if (!is_app(term)) {
            return false;
        }
        expr* r;
        if (m_map.find(term, r)) {
            term = r;
            return true;
        }
        if (to_app(term)->get_family_id() == null_family_id) {
            return false;
        }
        expr_ref_vector args(m);
        expr_ref tmp(m);
        for (unsigned i = 0; i < to_app(term)->get_num_args(); ++i) {
            tmp = to_app(term)->get_arg(i);
            if (!mk_abstract_expr(tmp)) {
                return false;
            }
            args.push_back(tmp);
        }
        tmp = m.mk_app(to_app(term)->get_decl(), args.size(), args.c_ptr());
        m_refs.push_back(tmp);
        m_map.insert(term, tmp);
        term = tmp;
        return true;
    }
    
    bool mk_extract_quantifiers2::mk_abstract_binding(expr_ref_vector const& binding, expr_ref_vector& result) {
        for (unsigned i = 0; i < binding.size(); ++i) {
            expr_ref tmp(m);
            tmp = binding[i];
            if (!mk_abstract_expr(tmp)) {
                return false;
            }
            result.push_back(tmp);
        }
        return true;
    }
    
    void mk_extract_quantifiers2::mk_abstraction_map(rule& r, expr_ref_vector const& binding) {
        m_map.reset();
        unsigned sz = binding.size();
        SASSERT(sz == r.get_decl()->get_arity());
        for (unsigned i = 0; i < sz; ++i) {
            m_map.insert(binding[sz-i-1], r.get_head()->get_arg(i));
            SASSERT(m.get_sort(binding[sz-i-1]) == m.get_sort(r.get_head()->get_arg(i)));
        }
        // todo: also make bindings for variables in rule body.
    }

    void mk_extract_quantifiers2::match_bindings(unsigned i, unsigned j, unsigned k) {
        expr_ref_vector resb(m);
        rule* r = m_qrules[i];
        quantifier* q = m_quantifiers[i].get();
        expr_ref_vector const& ruleb = m_rule_bindings[i][j];
        expr_ref_vector const& quantb = m_quantifier_bindings[i][k];
        mk_abstraction_map(*r, ruleb);
        if (!mk_abstract_binding(quantb, resb)) {
            return;
        }
        expr_ref inst(m), tmp(m);
        var_shifter shift(m);
        
        for (unsigned l = 0; l < resb.size(); ++l) {
            tmp = resb[l].get();
            shift(tmp, q->get_num_decls(), tmp);
            resb[l] = tmp;
        }

        instantiate(m, q, resb.c_ptr(), inst);
        if (!m_seen.contains(r)) {
            m_seen.insert(r, alloc(obj_hashtable<expr>));
        }
        obj_hashtable<expr>& seen = *m_seen.find(r);
        if (seen.contains(inst)) {
            return;
        }
        seen.insert(inst);
        m_refs.push_back(inst);
        if (!m_quantifier_instantiations.contains(r, q)) {
            m_quantifier_instantiations.insert(r, q, alloc(expr_ref_vector, m));
        }
        expr_ref_vector* vec = 0;
        VERIFY(m_quantifier_instantiations.find(r, q, vec));
        vec->push_back(inst);
        TRACE("dl", tout << "matched: " << mk_pp(q, m) << "\n" << mk_pp(inst, m) << "\n";);
    }

    app_ref mk_extract_quantifiers2::ensure_app(expr* e) {
        if (is_app(e)) {
            return app_ref(to_app(e), m);
        }
        else {
            return app_ref(m.mk_eq(e, m.mk_true()), m);
        }
    }

    void mk_extract_quantifiers2::extract(rule& r, rule_set& new_rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        bool has_quantifier = false;
        expr_ref_vector conjs(m);
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        datalog::flatten_and(conjs);
        for (unsigned j = 0; j < conjs.size(); ++j) {
            expr* e = conjs[j].get();
            quantifier* q;
            if (rule_manager::is_forall(m, e, q)) {
                m_quantifiers.push_back(q);
                m_qrules.push_back(&r);
                m_rule_bindings.push_back(vector<expr_ref_vector>());
                m_quantifier_bindings.push_back(vector<expr_ref_vector>());
                has_quantifier = true;
            }
        }
        if (!has_quantifier) {
            new_rules.add_rule(&r);
        }
    }

    void mk_extract_quantifiers2::apply(rule& r, rule_set& new_rules) {
        expr_ref_vector tail(m), conjs(m);
        expr_ref fml(m);
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        for (unsigned i = 0; i < utsz; ++i) {
            SASSERT(!r.is_neg_tail(i));
            tail.push_back(r.get_tail(i));
        }
        bool has_quantifier = false;
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        datalog::flatten_and(conjs);
        for (unsigned j = 0; j < conjs.size(); ++j) {
            expr* e = conjs[j].get();
            quantifier* q;
            if (rule_manager::is_forall(m, e, q)) {
                expr_ref_vector* ls;
                if (m_quantifier_instantiations.find(&r,q,ls)) {
                    tail.append(*ls);
                }
                has_quantifier = true;
            }
            else {
                tail.push_back(e);
            }
        }
        if (has_quantifier) {
            fml = m.mk_implies(m.mk_and(tail.size(), tail.c_ptr()), r.get_head());
            rule_ref_vector rules(rm);
            rm.mk_rule(fml, rules, r.name());
            for (unsigned i = 0; i < rules.size(); ++i) {
                new_rules.add_rule(rules[i].get());
            }
        }
    }

#if 0
    class mk_extract_quantifiers2::instance_plugin : public smt::quantifier_instance_plugin {
        mk_extract_quantifiers2& ex;
        ast_manager&        m;
        expr_ref_vector     m_refs;
        obj_hashtable<expr> m_bindings;
    public:
        instance_plugin(mk_extract_quantifiers2& ex): ex(ex), m(ex.m), m_refs(m) {}

        virtual void operator()(quantifier* q, unsigned num_bindings, smt::enode*const* bindings) {
            expr_ref_vector binding(m);
            ptr_vector<sort> sorts;
            for (unsigned i = 0; i < num_bindings; ++i) {
                binding.push_back(bindings[i]->get_owner());
                sorts.push_back(m.get_sort(binding[i].get()));
            }
            func_decl* f = m.mk_func_decl(symbol("T"), sorts.size(), sorts.c_ptr(), m.mk_bool_sort());
            expr_ref tup(m);
            tup = m.mk_app(f, binding.size(), binding.c_ptr());
            if (!m_bindings.contains(tup)) {
                m_bindings.insert(tup);
                m_refs.push_back(tup);
                ex.m_bindings.push_back(binding);
                TRACE("dl", tout << "insert\n" << mk_pp(q, m) << "\n" << mk_pp(tup, m) << "\n";);
            }
        }
    };

#endif

    void mk_extract_quantifiers2::reset() {
        {
            obj_pair_map<rule,quantifier, expr_ref_vector*>::iterator 
                it  = m_quantifier_instantiations.begin(),
                end = m_quantifier_instantiations.end();
            for (; it != end; ++it) {
                dealloc(it->get_value());
            }        
        }
        {
            obj_map<rule,obj_hashtable<expr>*>::iterator 
                it  = m_seen.begin(), 
                end = m_seen.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
        }
        m_quantifier_instantiations.reset();
        m_seen.reset();
        m_has_quantifiers = false;
        m_quantifiers.reset();
        m_qrules.reset();
        m_bindings.reset();
        m_rule_bindings.reset();
        m_quantifier_bindings.reset();
        m_refs.reset();
    }
    
    rule_set * mk_extract_quantifiers2::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
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

        bmc bmc(m_ctx);
        expr_ref_vector fmls(m);
        bmc.compile(source, fmls, 0); // TBD: use cancel_eh to terminate without base-case.
        bmc.compile(source, fmls, 1);
        bmc.compile(source, fmls, 2);
//        bmc.compile(source, fmls, 3);
        expr_ref query = bmc.compile_query(m_query_pred, 2);
        fmls.push_back(query);
        smt_params fparams;
        fparams.m_relevancy_lvl = 0;
        fparams.m_model = true;
        fparams.m_model_compact = true;
        fparams.m_mbqi = true;
        smt::kernel solver(m, fparams);
        TRACE("dl", 
              for (unsigned i = 0; i < fmls.size(); ++i) {
                  tout << mk_pp(fmls[i].get(), m) << "\n";
              });

        for (unsigned i = 0; i < fmls.size(); ++i) {
            solver.assert_expr(fmls[i].get());
        }
#if 0
        smt::context& ctx = solver.get_context();
        smt::quantifier_manager* qm = ctx.get_quantifier_manager();
        qm->get_plugin()->set_instance_plugin(alloc(instance_plugin, *this));
#endif
        solver.check();

        for (unsigned i = 0; i < m_bindings.size(); ++i) {
            expr_ref_vector& binding = m_bindings[i];
            for (unsigned j = 0; j < m_qrules.size(); ++j) {
                rule* r = m_qrules[j];
                if (matches_signature(r->get_decl(), binding)) {
                    m_rule_bindings[j].push_back(binding);
                }
                else if (matches_quantifier(m_quantifiers[j].get(), binding)) {
                    m_quantifier_bindings[j].push_back(binding);
                }
            }
        }
        for (unsigned i = 0; i < m_qrules.size(); ++i) {
            for (unsigned j = 0; j < m_rule_bindings[i].size(); ++j) {
                for (unsigned k = 0; k < m_quantifier_bindings[i].size(); ++k) {
                    match_bindings(i, j, k);
                }
            }
        }
        it = source.begin();
        for (; it != end; ++it) {
            apply(**it, *rules);
        }

        return rules;
    }

};


