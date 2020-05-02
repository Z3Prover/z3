/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   smt_induction.cpp

  Abstract:
   
   Add induction lemmas to context.

  Author:

    Nikolaj Bjorner 2020-04-25

  Notes:

  - work in absence of recursive functions but instead presence of quantifiers
    - relax current requirement of model sweeping when terms don't have value simplifications
  - k-induction
    - also to deal with mutually recursive datatypes
  - beyond literal induction lemmas
  - refine initialization of values when term is equal to constructor application, 
      
--*/

#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/value_sweep.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "smt/smt_context.h"
#include "smt/smt_induction.h"

using namespace smt;

/**
 * collect literals that are assigned to true, 
 * but evaluate to false under all extensions of 
 * the congruence closure.
 */

literal_vector collect_induction_literals::pre_select() {
    literal_vector result;
    for (unsigned i = m_literal_index; i < ctx.assigned_literals().size(); ++i) {
        literal lit = ctx.assigned_literals()[i];
        smt::bool_var v = lit.var();            
        if (!ctx.has_enode(v)) {                
            continue;
        }
        expr* e = ctx.bool_var2expr(v);
        if (!lit.sign() && m.is_eq(e))
            continue;
        result.push_back(lit);
    }
    TRACE("induction", ctx.display(tout << "literal index: " << m_literal_index << "\n" << result << "\n"););

    ctx.push_trail(value_trail<context, unsigned>(m_literal_index));
    m_literal_index = ctx.assigned_literals().size();
    return result;
}

void collect_induction_literals::model_sweep_filter(literal_vector& candidates) {
    expr_ref_vector terms(m);
    for (literal lit : candidates) {
        terms.push_back(ctx.bool_var2expr(lit.var()));
    }
    vector<expr_ref_vector> values;
    vs(terms, values);
    unsigned j = 0;
    for (unsigned i = 0; i < terms.size(); ++i) {
        literal lit = candidates[i];
        bool is_viable_candidate = true;
        for (auto const& vec : values) {
            if (vec[i] && lit.sign() && m.is_true(vec[i]))
                continue;
            if (vec[i] && !lit.sign() && m.is_false(vec[i]))
                continue;
            is_viable_candidate = false;
            break;
        }
        if (is_viable_candidate)
            candidates[j++] = lit;
    }
    candidates.shrink(j);
}


collect_induction_literals::collect_induction_literals(context& ctx, ast_manager& m, value_sweep& vs):
    ctx(ctx),
    m(m),
    vs(vs),
    m_literal_index(0)
{}
    
literal_vector collect_induction_literals::operator()() {    
    literal_vector candidates = pre_select();
    model_sweep_filter(candidates);
    return candidates;
}


// --------------------------------------
// create_induction_lemmas

bool create_induction_lemmas::viable_induction_sort(sort* s) {
    // potentially also induction on integers, sequences
    return m_dt.is_datatype(s) && m_dt.is_recursive(s);
}

bool create_induction_lemmas::viable_induction_parent(enode* p, enode* n) {
    app* o = p->get_owner();
    return 
        m_rec.is_defined(o) ||
        m_dt.is_constructor(o);
}

bool create_induction_lemmas::viable_induction_children(enode* n) {
    app* e = n->get_owner();
    if (m.is_value(e))
        return false;
    if (e->get_decl()->is_skolem())
        return false;
    if (n->get_num_args() == 0)
        return true;
    if (e->get_family_id() == m_rec.get_family_id()) 
        return m_rec.is_defined(e);
    if (e->get_family_id() == m_dt.get_family_id()) 
        return m_dt.is_constructor(e);
    return false;
}

bool create_induction_lemmas::viable_induction_term(enode* p, enode* n) {
    return 
        viable_induction_sort(m.get_sort(n->get_owner())) &&
        viable_induction_parent(p, n) &&
        viable_induction_children(n);
}

/**
 * positions in n that can be used for induction
 * the positions are distinct roots
 * and none of the roots are equivalent to a value in the current
 * congruence closure.
 */
enode_vector create_induction_lemmas::induction_positions(enode* n) {
    enode_vector result;
    enode_vector todo;
    auto add_todo = [&](enode* n) { 
        if (!n->is_marked()) { 
            n->set_mark(); 
            todo.push_back(n); 
        } 
    };
    add_todo(n);
    for (unsigned i = 0; i < todo.size(); ++i) {
        n = todo[i];
        for (enode* a : smt::enode::args(n)) {
            add_todo(a);        
            if (!a->is_marked2() && viable_induction_term(n, a)) {
                result.push_back(a);
                a->set_mark2();
            }
        }
    }
    for (enode* n : todo)
        n->unset_mark();
    for (enode* n : result)
        n->unset_mark2();
    return result;
}

void create_induction_lemmas::abstract1(enode* n, enode* t, expr* x, abstractions& result) {
    expr_safe_replace rep(m);
    rep.insert(t->get_owner(), x);
    expr_ref e(n->get_owner(), m);
    rep(e);
    result.push_back(abstraction(e));
}

/**
 * abstraction candidates for replacing different occurrence of t in n by x
 * it returns all possible non-empty subsets of t replaced by x.
 * 
 * TBD: add term sharing throttle.
 * TDD: add depth throttle.
 */
void create_induction_lemmas::abstract(enode* n, enode* t, expr* x, abstractions& result) {
    std::cout << "abs: " << result.size() << ": " << mk_pp(n->get_owner(), m) << "\n";
    if (n->get_root() == t->get_root()) {
        result.push_back(abstraction(m, x, n->get_owner(), t->get_owner()));
        return;
    }
    func_decl* f = n->get_owner()->get_decl();
    // check if n is a s
    if (f->is_skolem()) {
        expr_ref e(n->get_owner(), m);
        result.push_back(abstraction(e));
    }
        
    abstraction_args r1, r2;
    r1.push_back(abstraction_arg(m));
    for (enode* arg : enode::args(n)) {
        unsigned n = result.size();
        abstract(arg, t, x, result);
        std::cout << result.size() << "\n";
        for (unsigned i = n; i < result.size(); ++i) {
            abstraction& a = result[i];
            for (auto const& v : r1) {
                r2.push_back(v);
                r2.back().push_back(a);
            }
        }
        r1.swap(r2);
        r2.reset();
        result.shrink(n);
    }
    for (auto const& a : r1) {
        result.push_back(abstraction(m, m.mk_app(n->get_decl(), a.m_terms), a.m_eqs));
    }
};
    
/**
 * filter generalizations based on value_generator
 * If all evaluations are counter-examples, include 
 * candidate generalization.
 */
void create_induction_lemmas::filter_abstractions(bool sign, abstractions& abs) {
    vector<expr_ref_vector> values;
    expr_ref_vector fmls(m);
    for (auto & a : abs) fmls.push_back(a.m_term);
    std::cout << "sweep\n";
    vs(fmls, values);
    std::cout << "done sweep\n";
    unsigned j = 0;
    for (unsigned i = 0; i < fmls.size(); ++i) {
        bool all_cex = true;
        for (auto const& vec : values) {
            if (vec[i] && (m.is_true(vec[i]) == sign))
                continue;
            all_cex = false;
            break;
        }
        if (all_cex) {
            abs[j++] = abs.get(i);
        }
    }
    std::cout << "resulting size: " << j << " down from " << abs.size() << "\n";
    abs.shrink(j);
}

/*
 * Create simple induction lemmas of the form:
 *
 * lit & a.eqs() => alpha
 * alpha & is-c(sk) => ~beta
 *
 * where 
 *       lit   = is a formula containing t
 *       alpha = a.term(), a variant of lit 
 *               with some occurrences of t replaced by sk
 *       beta  = alpha[sk/access_k(sk)]
 * for each constructor c, that is recursive 
 * and contains argument of datatype sort s
 *
 * The main claim is that the lemmas are valid and that
 * they approximate induction reasoning.
 * 
 * alpha approximates minimal instance of the datatype s where 
 * the instance of s is true. In the limit one can
 * set beta to all instantiations of smaller values than sk.
 * 
 * create_hypotheses creates induction hypotheses.
 */

void create_induction_lemmas::create_hypotheses(
    unsigned depth, expr* sk0, expr_ref& alpha, expr* sk, literal_vector& lits) {
    if (depth == 0)
        return;
    sort* s = m.get_sort(sk);
    for (func_decl* c : *m_dt.get_datatype_constructors(s)) {
        func_decl* is_c = m_dt.get_constructor_recognizer(c);
        for (func_decl* acc : *m_dt.get_constructor_accessors(c)) {
            sort* rs = acc->get_range();
            if (rs != s && !m_dt.is_datatype(rs))
                continue;
            if (rs != s && !m_dt.is_recursive(rs))
                continue;

            lits.push_back(~mk_literal(m.mk_app(is_c, sk)));

            // alpha & is_c(sk) & is_c'(acc(sk)) => ~alpha[acc'(acc(sk)]
            if (rs != s && depth > 1) {
                app_ref acc_sk(m.mk_app(acc, sk), m);
                create_hypotheses(depth - 1, sk0, alpha, acc_sk, lits);
            }
            else {
                expr_ref beta(alpha);            // set beta := alpha[sk0/acc(sk)]
                expr_safe_replace rep(m);
                rep.insert(sk0, m.mk_app(acc, sk));
                rep(beta);
                literal b_lit = mk_literal(beta);

                if (lits[0].sign()) b_lit.neg(); // maintain the same sign as alpha
                
                // alpha & is_c(sk) => ~beta
                lits.push_back(~b_lit);
                literal_vector _lits(lits);      // mk_clause could make destructive updates
                add_th_lemma(_lits);               
                lits.pop_back();
            }
            lits.pop_back();
        }
    }
}

void create_induction_lemmas::create_lemmas(expr* sk, abstraction& a, literal lit) {
    std::cout << "abstraction: " << a.m_term << "\n";
    sort* s = m.get_sort(sk);
    if (!m_dt.is_datatype(s))
        return;
    expr_ref alpha = a.m_term;
    literal alpha_lit = mk_literal(alpha);
    if (lit.sign()) alpha_lit.neg();

    literal_vector lits;
    lits.push_back(~alpha_lit);
    create_hypotheses(1, sk, alpha, sk, lits);
    lits.pop_back();

    // phi & eqs => alpha
    lits.push_back(~lit);
    for (auto const& p : a.m_eqs) {
        lits.push_back(~mk_literal(m.mk_eq(p.first, p.second)));
    }
    lits.push_back(alpha_lit);
    add_th_lemma(lits);    
}

void create_induction_lemmas::add_th_lemma(literal_vector const& lits) {
    IF_VERBOSE(0, ctx.display_literals_verbose(verbose_stream() << "lemma:\n", lits) << "\n");
    ctx.mk_clause(lits.size(), lits.c_ptr(), nullptr, smt::CLS_TH_AXIOM); 
    // CLS_TH_LEMMA, but then should re-instance if GC'ed
    ++m_num_lemmas;
}

literal create_induction_lemmas::mk_literal(expr* e) {
    expr_ref _e(e, m);
    if (!ctx.e_internalized(e)) {
        ctx.internalize(e, false);
    }
    enode* n = ctx.get_enode(e);
    ctx.mark_as_relevant(n);
    return ctx.get_literal(e);
}

bool create_induction_lemmas::operator()(literal lit) {
    unsigned num = m_num_lemmas;
    enode* r = ctx.bool_var2enode(lit.var());
    unsigned position = 0;
    for (enode* n : induction_positions(r)) {
        expr* t = n->get_owner();
        sort* s = m.get_sort(t);
        expr_ref sk(m.mk_fresh_const("sk", s), m);
        std::cout << "abstract " << mk_pp(t, m) << " " << sk << "\n";
        abstractions abs;
        abstract1(r, n, sk, abs);            
        // if (ab.size() > 1) abs.pop_back(); // last position has no generalizations
        if (abs.size() > 1) filter_abstractions(lit.sign(), abs);
        for (abstraction& a : abs) {
            create_lemmas(sk, a, lit);
        }
        ++position;
    }
    return m_num_lemmas > num;
}

create_induction_lemmas::create_induction_lemmas(context& ctx, ast_manager& m, value_sweep& vs):
    ctx(ctx),
    m(m),
    vs(vs),
    m_dt(m),
    m_a(m),
    m_rec(m),
    m_num_lemmas(0)
{}

induction::induction(context& ctx, ast_manager& m):
    ctx(ctx),
    m(m),
    vs(m),
    m_collect_literals(ctx, m, vs),
    m_create_lemmas(ctx, m, vs)
{}

// TBD: use smt_arith_value to also include state from arithmetic solver
void induction::init_values() {
    for (enode* n : ctx.enodes()) 
        if (m.is_value(n->get_owner())) 
            for (enode* r : *n) 
                if (r != n) {
                    vs.set_value(r->get_owner(), n->get_owner());
                }
}

bool induction::operator()() {
    bool added_lemma = false;
    vs.reset_values();
    init_values();
    literal_vector candidates = m_collect_literals();
    for (literal lit : candidates) {
        if (m_create_lemmas(lit))
            added_lemma = true;
    }
    return added_lemma;
}

// state contains datatypes + recursive functions
// more comprehensive: 
// state contains integers / datatypes / sequences + recursive function / quantifiers

bool induction::should_try(context& ctx) {
    recfun::util u(ctx.get_manager());
    datatype::util dt(ctx.get_manager());
    theory* adt = ctx.get_theory(dt.get_family_id());
    return adt && adt->get_num_vars() > 0 && !u.get_rec_funs().empty();
}
