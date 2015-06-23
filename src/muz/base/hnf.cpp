/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hnf.cpp

Abstract:

    Horn normal form conversion.

Author:

    Nikolaj Bjorner (nbjorner) 3-20-2013

Notes:

   Convert formula 

       (forall x f(x)) 

   into conjunction 
 
       (f1 xy) (f2 xy) (f3 xy)

   such that 

       (forall x f(x)) ~ /\ (forall xy (f_i xy))

   modulo definitions that are introduced.
    

   Convert proof with 
       asserted (forall xy (f' xy))

   To:      
       (forall xy (f' xy))             by mp~ 1, 2
    1. asserted/def-intro (forall xy (f xy)) 
    2. (forall xy (f xy))  ~ (forall xy (f' xy)) by trans, 3, 4
    3. (forall xy (f xy))  ~ (forall xy (f1 xy)) by pull quantifiers (rewrite)
    4. (forall xy (f1 xy)) ~ (forall xy (f' xy)) by oeq_quant_intro 5
    5. f1 xy ~ f' xy                             by sub-proof.
     
                
--*/
#include"hnf.h"
#include"warning.h"
#include"used_vars.h"
#include"well_sorted.h"
#include"var_subst.h"
#include"name_exprs.h"
#include"act_cache.h"
#include"cooperate.h"
#include"ast_pp.h"
#include"quant_hoist.h"
#include"ast_util.h"
#include"dl_util.h"
#include"for_each_ast.h"
#include"for_each_expr.h"

class hnf::imp {

    class contains_predicate_proc {
        imp const& m;
    public:
        struct found {};
        contains_predicate_proc(imp const& m): m(m) {}
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app* n) {
            if (m.is_predicate(n)) throw found();
        }
    };

    ast_manager&          m;
    bool                  m_produce_proofs;
    volatile bool         m_cancel;
    expr_ref_vector       m_todo;
    proof_ref_vector      m_proofs;
    expr_ref_vector       m_refs;
    symbol                m_name;
    svector<symbol>       m_names;
    ptr_vector<sort>      m_sorts;
    quantifier_hoister    m_qh;
    obj_map<expr, app*>   m_memoize_disj;
    obj_map<expr, proof*> m_memoize_proof;
    func_decl_ref_vector  m_fresh_predicates;
    expr_ref_vector       m_body;
    proof_ref_vector      m_defs;
    contains_predicate_proc m_proc;
    expr_free_vars        m_free_vars;
    ast_fast_mark1        m_mark1;


public:
    imp(ast_manager & m):
        m(m),
        m_produce_proofs(false),
        m_cancel(false),
        m_todo(m),
        m_proofs(m),
        m_refs(m), 
        m_name("P"),
        m_qh(m),
        m_fresh_predicates(m),
        m_body(m),
        m_defs(m),
        m_proc(*this) {
    }

    bool is_horn(expr* n) {
        expr* n1, *n2;
        while (is_forall(n)) n = to_quantifier(n)->get_expr();
        if (m.is_implies(n, n1, n2) && is_predicate(n2)) {
            app* a1 = to_app(n1);
            if (m.is_and(a1)) {
                for (unsigned i = 0; i < a1->get_num_args(); ++i) {
                    if (!is_predicate(a1->get_arg(i)) && 
                        contains_predicate(a1->get_arg(i))) {                    
                        return false;
                    }
                }
            }
            else if (!is_predicate(a1) && contains_predicate(a1)) {
                return false;
            }
            return true;
        }    
        
        return false;
    }

    void operator()(expr * n, 
                    proof* p,
                    expr_ref_vector& result, 
                    proof_ref_vector& ps) {
        if (is_horn(n)) {
            result.push_back(n);
            ps.push_back(p);
            return;
        }
        expr_ref fml(m);
        proof_ref pr(m);
        m_todo.reset();
        m_proofs.reset();
        m_refs.reset();
        m_memoize_disj.reset();
        m_memoize_proof.reset();
        m_fresh_predicates.reset();
        m_todo.push_back(n);
        m_proofs.push_back(p);
        m_produce_proofs = p != 0;
        while (!m_todo.empty() && !m_cancel) {
            fml = m_todo.back();
            pr = m_proofs.back();
            m_todo.pop_back();
            m_proofs.pop_back();
            mk_horn(fml, pr);
            if (fml) {
                result.push_back(fml);
                ps.push_back(pr);
            }
        }
        TRACE("hnf",
              tout << mk_pp(n, m) << "\n==>\n";
              for (unsigned i = 0; i < result.size(); ++i) {
                  tout << mk_pp(result[i].get(), m) << "\n";
              });
    }

    void set_cancel(bool f) {
        m_cancel = f;
    }

    void set_name(symbol const& n) {
        if (n == symbol::null) {
            m_name = symbol("P");
        }
        else {
            m_name = n;
        }
    }

    func_decl_ref_vector const& get_fresh_predicates() {
        return m_fresh_predicates;
    }

    void reset() {
        m_cancel = false;
        m_todo.reset();
        m_proofs.reset();
        m_refs.reset();
        m_memoize_disj.reset();
        m_memoize_proof.reset();
        m_fresh_predicates.reset();
    }

    ast_manager& get_manager() { return m; }

private:

    bool produce_proofs() const {
        return m_produce_proofs;
    }

    bool is_predicate(expr* p) const {
        return is_app(p) && is_predicate(to_app(p)->get_decl());
    }

    bool is_predicate(func_decl* f) const {
        return m.is_bool(f->get_range()) && f->get_family_id() == null_family_id;
    }

    bool contains_predicate(expr* fml)  {
        try {
            quick_for_each_expr(m_proc, m_mark1, fml);
            m_mark1.reset();
        }
        catch (contains_predicate_proc::found) {
            m_mark1.reset();
            return true;
        }
        return false;
    }


    void mk_horn(expr_ref& fml, proof_ref& premise) {
        SASSERT(!premise || fml == m.get_fact(premise));
        expr* e1, *e2;
        expr_ref fml0(m), fml1(m), fml2(m), head(m);
        proof_ref p(m);
        fml0 = fml;
        m_names.reset();
        m_sorts.reset();
        m_body.reset();
        m_defs.reset();
        m_qh.pull_quantifier(true, fml0, &m_sorts, &m_names);
        if (premise){
            fml1 = bind_variables(fml0);
            if (!m_sorts.empty()) {
                proof* p1 = m.mk_pull_quant(fml, to_quantifier(fml1));
                premise = mk_modus_ponens(premise, p1);
                fml = fml1;
            }
        }
        head = fml0;
        while (m.is_implies(head, e1, e2)) {
            m_body.push_back(e1);
            head = e2;
        }
        flatten_and(m_body);
        if (premise) {
            p = m.mk_rewrite(fml0, mk_implies(m_body, head));
        }

        //
        // Case:
        // A \/ B -> C
        // => 
        // A -> C
        // B -> C
        // 
        if (m_body.size() == 1 && m.is_or(m_body[0].get()) && contains_predicate(m_body[0].get())) {
            app* _or = to_app(m_body[0].get());
            unsigned sz = _or->get_num_args();
            expr* const* args = _or->get_args();
            for (unsigned i = 0; i < sz; ++i) {
                m_todo.push_back(bind_variables(m.mk_implies(args[i], head)));
                m_proofs.push_back(0);
            } 

            if (premise) {
                expr_ref f1 = bind_variables(mk_implies(m_body, head));
                expr* f2 = m.mk_and(sz, m_todo.c_ptr()+m_todo.size()-sz);
                proof_ref p2(m), p3(m);
                p2 = m.mk_def_axiom(m.mk_iff(f1, f2));
                p3 = mk_quant_intro(fml, f1, p);                    
                p2 = mk_transitivity(p3, p2);
                p2 = mk_modus_ponens(premise, p2);
                for (unsigned i = 0; i < sz; ++i) {
                    m_proofs[m_proofs.size()-sz+i] = m.mk_and_elim(p2, i);
                }
            }                
            fml = 0;
            return;
        }


        eliminate_disjunctions(m_body, m_defs);
        p = mk_congruence(p, m_body, head, m_defs);

        eliminate_quantifier_body(m_body, m_defs);
        p = mk_congruence(p, m_body, head, m_defs);          

        fml2 = mk_implies(m_body, head);

        fml = bind_variables(fml2);

        if (premise) {
            SASSERT(p);
            p = mk_quant_intro(fml1, fml, p);     
            premise = mk_modus_ponens(premise, p);
        }
    }

    proof* mk_quant_intro(expr* e1, expr* e2, proof* p) {
        if (m_sorts.empty()) {
            return p;
        }
        quantifier* q1 = to_quantifier(e1);
        quantifier* q2 = to_quantifier(e2);
        if (m.is_iff(m.get_fact(p))) {
            return m.mk_quant_intro(q1, q2, p);
        }
        if (m.is_oeq(m.get_fact(p))) {
            return m.mk_oeq_quant_intro(q1, q2, p);
        }
        UNREACHABLE();
        return p;
    }


    void eliminate_disjunctions(expr_ref_vector::element_ref& body, proof_ref_vector& proofs) {
        expr* b = body.get(); 
        expr* e1;
        bool negate_args = false;
        bool is_disj = false;
        unsigned num_disj = 0;
        expr* const* disjs = 0;
        if (!contains_predicate(b)) {
            return;
        }
        TRACE("hnf", tout << mk_pp(b, m) << "\n";);
        if (m.is_or(b)) {
            is_disj = true;
            negate_args = false;
            num_disj = to_app(b)->get_num_args();
            disjs = to_app(b)->get_args();
        }
        if (m.is_not(b, e1) && m.is_and(e1)) {
            is_disj = true;
            negate_args = true;
            num_disj = to_app(e1)->get_num_args();
            disjs = to_app(e1)->get_args();
        }
        if (is_disj) {
            app* old_head = 0;
            if (m_memoize_disj.find(b, old_head)) {
                body = old_head;
            }
            else {
                app_ref head = mk_fresh_head(b);
                proof_ref_vector defs(m);
                for (unsigned i = 0; i < num_disj; ++i) {
                    expr* e = disjs[i];
                    if (negate_args) {
                        e = m.mk_not(e);
                    }
                    m_todo.push_back(bind_variables(m.mk_implies(e, head)));
                    m_proofs.push_back(0);
                    if (produce_proofs()) {
                        defs.push_back(m.mk_def_intro(m_todo.back()));
                        m_proofs[m_proofs.size()-1] = defs.back();
                    }
                }
                if (produce_proofs()) {
                    proof* p = m.mk_apply_defs(body.get(), head, defs.size(), defs.c_ptr());
                    m_refs.push_back(p);
                    m_memoize_proof.insert(b, p);
                }
                m_memoize_disj.insert(b, head);
                m_refs.push_back(b);
                m_refs.push_back(head);
                // update the body to be the newly introduced head relation
                body = head;
            }

            if (produce_proofs()) {
                proofs.push_back(m_memoize_proof.find(b));
            }
        }
    }

    app_ref mk_fresh_head(expr* e) {
        ptr_vector<sort> sorts1;
        m_free_vars(e);
        expr_ref_vector args(m);
        for (unsigned i = 0; i < m_free_vars.size(); ++i) {
            if (m_free_vars[i]) {
                args.push_back(m.mk_var(i, m_free_vars[i]));
                sorts1.push_back(m_free_vars[i]);
            }
        }
        func_decl_ref f(m);
        f = m.mk_fresh_func_decl(m_name.str().c_str(), "", sorts1.size(), sorts1.c_ptr(), m.mk_bool_sort());
        m_fresh_predicates.push_back(f);
        return app_ref(m.mk_app(f, args.size(), args.c_ptr()), m);
    }

    void eliminate_disjunctions(expr_ref_vector& body, proof_ref_vector& proofs) {
        for (unsigned i = 0; i < body.size(); ++i) {
            expr_ref_vector::element_ref r = body[i];
            eliminate_disjunctions(r, proofs);
        }
    }

    void eliminate_quantifier_body(expr_ref_vector::element_ref& body, proof_ref_vector& proofs) {
        if (is_forall(body.get()) && contains_predicate(body.get())) {
            quantifier* q = to_quantifier(body.get());
            expr* e = q->get_expr();
            if (!is_predicate(e)) {
                app_ref head = mk_fresh_head(e);
                m_todo.push_back(bind_variables(m.mk_implies(e, head)));
                m_proofs.push_back(0);
                body = m.update_quantifier(q, head);
                if (produce_proofs()) {
                    proof* def_intro = m.mk_def_intro(m_todo.back());
                    proof* def_proof = m.mk_apply_def(e, head, def_intro);
                    proofs.push_back(m.mk_nnf_neg(q, body.get(), 1, &def_proof));
                    m_proofs[m_proofs.size()-1] = def_intro;
                }
            }
        }
    }

    void eliminate_quantifier_body(expr_ref_vector& body, proof_ref_vector& proofs) {
        for (unsigned i = 0; i < body.size(); ++i) {
            expr_ref_vector::element_ref r = body[i];
            eliminate_quantifier_body(r, proofs);
        }
    }

    app_ref mk_implies(expr_ref_vector const& body, expr* head) {
        switch (body.size()) {
        case 0: 
            return app_ref(to_app(head), m);
        case 1: 
            return app_ref(m.mk_implies(body[0], head), m);
        default:
            return app_ref(m.mk_implies(m.mk_and(body.size(), body.c_ptr()), head), m);
        }        
    }


    proof_ref mk_congruence(proof* p1, expr_ref_vector const& body, expr* head, proof_ref_vector& defs) {
        if (defs.empty()) {
            return proof_ref(p1, m);
        }
        else {
            SASSERT(p1);
            proof_ref p2(m), p3(m);
            app_ref fml = mk_implies(body, head);
            expr* fact = m.get_fact(p1);
            if (m.is_iff(fact)) {
                p1 = m.mk_iff_oeq(p1);
                fact = m.get_fact(p1);
            }
            VERIFY (m.is_oeq(fact) || m.is_eq(fact));
            app* e2 = to_app(to_app(fact)->get_arg(1));
            p2 = m.mk_oeq_congruence(e2, fml, defs.size(), defs.c_ptr());
            p3 = mk_transitivity(p1, p2);
            defs.reset();
            return proof_ref(p3, m);
        }
    }

    proof_ref mk_modus_ponens(proof* premise, proof* eq) {
        proof_ref result(m);
        result = m.mk_modus_ponens(premise, eq);
        if (m.get_fact(premise) == m.get_fact(result)) {
            result = premise;
        }
        return result;
    }

    proof* mk_transitivity(proof* p1, proof* p2) {
        if (p1) {
            app* f = to_app(m.get_fact(p1));
            if (f->get_arg(0) == f->get_arg(1)) {
                return p2;
            }
        }
        if (p2) {
            app* f = to_app(m.get_fact(p2));
            if (f->get_arg(0) == f->get_arg(1)) {
                return p1;
            }
        }
        return m.mk_transitivity(p1, p2);
    }

    expr_ref bind_variables(expr* e) {
        SASSERT(m_sorts.size() == m_names.size());
        if (m_sorts.empty()) {
            return expr_ref(e, m);
        }
        return expr_ref(m.mk_forall(m_sorts.size(), m_sorts.c_ptr(), m_names.c_ptr(), e), m);
    }

};

hnf::hnf(ast_manager & m) {
    m_imp = alloc(imp, m);
}

hnf::~hnf() {
    dealloc(m_imp);
}
    
void hnf::operator()(expr * n, proof* p, expr_ref_vector & rs, proof_ref_vector& ps) {
    m_imp->operator()(n, p, rs, ps);    
    TRACE("hnf", 
          ast_manager& m = rs.get_manager();
          tout << mk_ismt2_pp(n, m) << "\nHNF result:\n";
          for (unsigned i = 0; i < rs.size(); ++i) {
              tout << mk_pp(rs[i].get(), m) << "\n";
          }
          );
}

void hnf::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

void hnf::set_name(symbol const& n) {
    m_imp->set_name(n);
}

void hnf::reset() {
    m_imp->reset();
}

func_decl_ref_vector const& hnf::get_fresh_predicates() {
    return m_imp->get_fresh_predicates();
}
