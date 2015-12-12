/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_karr_invariants.cpp

Abstract:

    Extract integer linear invariants.

    The linear invariants are extracted according to Karr's method.
    A short description is in 
    Nikolaj Bjorner, Anca Browne and Zohar Manna. Automatic Generation 
    of Invariants and Intermediate Assertions, in CP 95.

    The algorithm is here adapted to Horn clauses.
    The idea is to maintain two data-structures for each recursive relation.
    We call them R and RD
    - R  - set of linear congruences that are true of R.
    - RD - the dual basis of of solutions for R.

    RD is updated by accumulating basis vectors for solutions 
    to R (the homogeneous dual of R)
    R is updated from the inhomogeneous dual of RD.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-09

Revision History:
           
--*/

#include"expr_safe_replace.h"
#include"bool_rewriter.h"
#include"for_each_expr.h"

#include"dl_mk_karr_invariants.h"
#include"dl_mk_backwards.h"
#include"dl_mk_loop_counter.h"

namespace datalog {


    mk_karr_invariants::mk_karr_invariants(context & ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()), 
        rm(ctx.get_rule_manager()),
        m_inner_ctx(m, ctx.get_register_engine(), ctx.get_fparams()),
        a(m),
        m_pinned(m) {
            params_ref params;
            params.set_sym("default_relation", symbol("karr_relation"));
            params.set_sym("engine", symbol("datalog"));
            params.set_bool("karr", false);
            m_inner_ctx.updt_params(params);
    }

    mk_karr_invariants::~mk_karr_invariants() { }

    matrix& matrix::operator=(matrix const& other) {
        reset();
        append(other);
        return *this;
    }

    void matrix::display_row(
        std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq) {
        for (unsigned j = 0; j < row.size(); ++j) {
            out << row[j] << " ";
        }
        out << (is_eq?" = ":" >= ") << -b << "\n";        
    }

    void matrix::display_ineq(
        std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq) {
        bool first = true;
        for (unsigned j = 0; j < row.size(); ++j) {
            if (!row[j].is_zero()) {
                if (!first && row[j].is_pos()) {
                    out << "+ ";
                }
                if (row[j].is_minus_one()) {
                    out << "- ";
                }
                if (row[j] > rational(1) || row[j] < rational(-1)) {
                    out << row[j] << "*";
                }
                out << "x" << j << " ";
                first = false;
            }
        }
        out << (is_eq?"= ":">= ") << -b << "\n";        
    }

    void matrix::display(std::ostream& out) const {
        for (unsigned i = 0; i < A.size(); ++i) {
            display_row(out, A[i], b[i], eq[i]);
        }
    }
    

    class mk_karr_invariants::add_invariant_model_converter : public model_converter {
        ast_manager&          m;
        arith_util            a;
        func_decl_ref_vector  m_funcs;
        expr_ref_vector       m_invs;
    public:
        
        add_invariant_model_converter(ast_manager& m): m(m), a(m), m_funcs(m), m_invs(m) {}

        virtual ~add_invariant_model_converter() { }

        void add(func_decl* p, expr* inv) {
            if (!m.is_true(inv)) {
                m_funcs.push_back(p);
                m_invs.push_back(inv);
            }
        }

        virtual void operator()(model_ref & mr) {
            for (unsigned i = 0; i < m_funcs.size(); ++i) {
                func_decl* p = m_funcs[i].get();
                func_interp* f = mr->get_func_interp(p);
                expr_ref body(m);                
                unsigned arity = p->get_arity();
                SASSERT(0 < arity);
                if (f) {
                    SASSERT(f->num_entries() == 0);
                    if (!f->is_partial()) {
                        bool_rewriter(m).mk_and(f->get_else(), m_invs[i].get(), body);
                    }
                }
                else {
                    f = alloc(func_interp, m, arity);
                    mr->register_decl(p, f);
                    body = m.mk_false();  // fragile: assume that relation was pruned by being infeasible.
                }
                f->set_else(body);
            }            
        }
    
        virtual model_converter * translate(ast_translation & translator) {
            add_invariant_model_converter* mc = alloc(add_invariant_model_converter, m);
            for (unsigned i = 0; i < m_funcs.size(); ++i) {
                mc->add(translator(m_funcs[i].get()), m_invs[i].get());
            }
            return mc;
        }

    private:
        void mk_body(matrix const& M, expr_ref& body) {
            expr_ref_vector conj(m);
            for (unsigned i = 0; i < M.size(); ++i) {
                mk_body(M.A[i], M.b[i], M.eq[i], conj);
            }
            bool_rewriter(m).mk_and(conj.size(), conj.c_ptr(), body);
        }

        void mk_body(vector<rational> const& row, rational const& b, bool is_eq, expr_ref_vector& conj) {
            expr_ref_vector sum(m);
            expr_ref zero(m), lhs(m);
            zero = a.mk_numeral(rational(0), true);

            for (unsigned i = 0; i < row.size(); ++i) {
                if (row[i].is_zero()) {
                    continue;
                }
                var* var = m.mk_var(i, a.mk_int());
                if (row[i].is_one()) {
                    sum.push_back(var);
                }
                else {
                    sum.push_back(a.mk_mul(a.mk_numeral(row[i], true), var));
                }
            }
            if (!b.is_zero()) {
                sum.push_back(a.mk_numeral(b, true));
            }
            lhs = a.mk_add(sum.size(), sum.c_ptr());
            if (is_eq) {
                conj.push_back(m.mk_eq(lhs, zero));
            }
            else {
                conj.push_back(a.mk_ge(lhs, zero));
            }
        }
    };
    
    rule_set * mk_karr_invariants::operator()(rule_set const & source) {
        if (!m_ctx.karr()) {
            return 0;
        }
        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            rule const& r = **it;
            if (r.has_negation()) {
                return 0;
            }
        }
        mk_loop_counter lc(m_ctx);
        mk_backwards bwd(m_ctx);

        scoped_ptr<rule_set> src_loop = lc(source);
        TRACE("dl", src_loop->display(tout << "source loop\n"););

        get_invariants(*src_loop);

        if (m.canceled()) {
            return 0;
        }

        // figure out whether to update same rules as used for saturation.
        scoped_ptr<rule_set> rev_source = bwd(*src_loop);
        get_invariants(*rev_source);        
        scoped_ptr<rule_set> src_annot = update_rules(*src_loop);
        rule_set* rules = lc.revert(*src_annot);
        rules->inherit_predicates(source);
        TRACE("dl", rules->display(tout););
        m_pinned.reset();
        m_fun2inv.reset();
        return rules;
    }

    void mk_karr_invariants::get_invariants(rule_set const& src) {
        m_inner_ctx.reset();
        rel_context_base& rctx = *m_inner_ctx.get_rel_context();
        ptr_vector<func_decl> heads;
        func_decl_set const& predicates = m_ctx.get_predicates();
        for (func_decl_set::iterator fit = predicates.begin(); fit != predicates.end(); ++fit) {
            m_inner_ctx.register_predicate(*fit, false);
        }
        m_inner_ctx.ensure_opened();
        m_inner_ctx.replace_rules(src);
        m_inner_ctx.close();
        rule_set::decl2rules::iterator dit  = src.begin_grouped_rules();
        rule_set::decl2rules::iterator dend = src.end_grouped_rules();
        for (; dit != dend; ++dit) {
            heads.push_back(dit->m_key);
        }
        m_inner_ctx.rel_query(heads.size(), heads.c_ptr());

        // retrieve invariants.
        dit = src.begin_grouped_rules();
        for (; dit != dend; ++dit) {
            func_decl* p = dit->m_key;
            expr_ref fml = rctx.try_get_formula(p);
            if (fml && !m.is_true(fml)) {
                expr* inv = 0;
                if (m_fun2inv.find(p, inv)) {
                    fml = m.mk_and(inv, fml);
                }
                m_pinned.push_back(fml);
                m_fun2inv.insert(p, fml);
            }
        }
    }        

    rule_set* mk_karr_invariants::update_rules(rule_set const& src) {
        scoped_ptr<rule_set> dst = alloc(rule_set, m_ctx);
        rule_set::iterator it = src.begin(), end = src.end();
        for (; it != end; ++it) {
            update_body(*dst, **it);
        }
        if (m_ctx.get_model_converter()) {
            add_invariant_model_converter* kmc = alloc(add_invariant_model_converter, m);
            rule_set::decl2rules::iterator git  = src.begin_grouped_rules();
            rule_set::decl2rules::iterator gend = src.end_grouped_rules();
            for (; git != gend; ++git) {
                func_decl* p = git->m_key;
                expr* fml = 0;
                if (m_fun2inv.find(p, fml)) {
                    kmc->add(p, fml);                    
                }
            }
            m_ctx.add_model_converter(kmc);
        }

        dst->inherit_predicates(src);
        return dst.detach();
    }

    void mk_karr_invariants::update_body(rule_set& rules, rule& r) { 
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz  = r.get_tail_size();
        app_ref_vector tail(m);
        expr_ref fml(m);
        for (unsigned i = 0; i < tsz; ++i) {
            tail.push_back(r.get_tail(i));
        }
        for (unsigned i = 0; i < utsz; ++i) {
            func_decl* q = r.get_decl(i); 
            expr* fml = 0;
            if (m_fun2inv.find(q, fml)) {
                expr_safe_replace rep(m);
                for (unsigned j = 0; j < q->get_arity(); ++j) {
                    rep.insert(m.mk_var(j, q->get_domain(j)), 
                               r.get_tail(i)->get_arg(j));
                }
                expr_ref tmp(fml, m);
                rep(tmp);
                tail.push_back(to_app(tmp));
            }
        }
        rule* new_rule = &r;
        if (tail.size() != tsz) {
            new_rule = rm.mk(r.get_head(), tail.size(), tail.c_ptr(), 0, r.name());
        }
        rules.add_rule(new_rule);
        rm.mk_rule_rewrite_proof(r, *new_rule); // should be weakening rule.        
    }




};

