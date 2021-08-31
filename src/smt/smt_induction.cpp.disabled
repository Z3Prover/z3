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
#include "ast/for_each_expr.h"
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

    ctx.push_trail(value_trail<unsigned>(m_literal_index));
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
{
}
    
literal_vector collect_induction_literals::operator()() {    
    literal_vector candidates = pre_select();
    model_sweep_filter(candidates);
    return candidates;
}


// --------------------------------------
// induction_lemmas

bool induction_lemmas::viable_induction_sort(sort* s) {
    // potentially also induction on integers, sequences
    return m_dt.is_datatype(s) && m_dt.is_recursive(s);
}

bool induction_lemmas::viable_induction_parent(enode* p, enode* n) {
    app* o = p->get_expr();
    return 
        m_rec.is_defined(o) ||
        m_dt.is_constructor(o);
}

bool induction_lemmas::viable_induction_children(enode* n) {
    app* e = n->get_expr();
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

bool induction_lemmas::viable_induction_term(enode* p, enode* n) {
    return 
        viable_induction_sort(n->get_expr()->get_sort()) &&
        viable_induction_parent(p, n) &&
        viable_induction_children(n);
}

/**
 * positions in n that can be used for induction
 * the positions are distinct roots
 * and none of the roots are equivalent to a value in the current
 * congruence closure.
 */
enode_vector induction_lemmas::induction_positions(enode* n) {
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


// Collecting induction positions relative to parent.
induction_lemmas::induction_positions_t induction_lemmas::induction_positions2(enode* n) {
    induction_positions_t result;
    enode_vector todo;
    todo.push_back(n);
    n->set_mark();
    for (unsigned i = 0; i < todo.size(); ++i) {
        enode* n = todo[i];
        unsigned idx = 0;
        for (enode* a : smt::enode::args(n)) {
            if (viable_induction_term(n, a)) {
                result.push_back(induction_position_t(n, idx));
            }
            if (!a->is_marked()) {
                a->set_mark();
                todo.push_back(a);
            }
            ++idx;
        }
    }
    for (enode* n : todo) 
        n->unset_mark();
    return result;
}

void induction_lemmas::initialize_levels(enode* n) {
    expr_ref tmp(n->get_expr(), m);
    m_depth2terms.reset();
    m_depth2terms.resize(get_depth(tmp) + 1);
    m_ts++;
    for (expr* t : subterms(tmp)) {
        if (is_app(t)) {
            m_depth2terms[get_depth(t)].push_back(to_app(t));
            m_marks.reserve(t->get_id()+1, 0);
        }
    }
}

induction_lemmas::induction_combinations_t induction_lemmas::induction_combinations(enode* n) {
    initialize_levels(n); 
    induction_combinations_t result;
    auto pos = induction_positions2(n);

    if (pos.size() > 6) {
        induction_positions_t r;
        for (auto const& p : pos) {
            if (is_uninterp_const(p.first->get_expr()))
                r.push_back(p);
        }
        result.push_back(r);
        return result;
    }
    for (unsigned i = 0; i < (1ull << pos.size()); ++i) {
        induction_positions_t r;
        for (unsigned j = 0; j < pos.size(); ++j) {
            if (0 != (i & (1 << j)))
                r.push_back(pos[j]);
        }
        if (positions_dont_overlap(r))
            result.push_back(r);
    }
    for (auto const& pos : result) {
        std::cout << "position\n";
        for (auto const& p : pos) {
            std::cout << mk_pp(p.first->get_expr(), m) << ":" << p.second << "\n";
        }
    }
    return result;
}

bool induction_lemmas::positions_dont_overlap(induction_positions_t const& positions) {
    if (positions.empty())
        return false;
    m_ts++;
    auto mark = [&](expr* n) { m_marks[n->get_id()] = m_ts; };
    auto is_marked = [&](expr* n) { return m_marks[n->get_id()] == m_ts; };
    for (auto p : positions) 
        mark(p.first->get_expr());
    // no term used for induction contains a subterm also used for induction.    
    for (auto const& terms : m_depth2terms) {
        for (app* t : terms) {
            bool has_mark = false;
            for (expr* arg : *t) 
                has_mark |= is_marked(arg);
            if (is_marked(t) && has_mark)
                return false;
            if (has_mark)
                mark(t);
        }
    }
    return true;
}
 
/**
   extract substitutions for x into accessor values of the same sort.
   collect side-conditions for the accessors to be well defined.
   apply a depth-bounded unfolding of datatype constructors to collect 
   accessor values beyond a first level and for nested (mutually recursive)
   datatypes.
 */
void induction_lemmas::mk_hypothesis_substs(unsigned depth, expr* x, cond_substs_t& subst) {
    expr_ref_vector conds(m);
    mk_hypothesis_substs_rec(depth, x->get_sort(), x, conds, subst);
}

void induction_lemmas::mk_hypothesis_substs_rec(unsigned depth, sort* s, expr* y, expr_ref_vector& conds, cond_substs_t& subst) {
    sort* ys = y->get_sort();
    for (func_decl* c : *m_dt.get_datatype_constructors(ys)) {
        func_decl* is_c = m_dt.get_constructor_recognizer(c);
        conds.push_back(m.mk_app(is_c, y));
        for (func_decl* acc : *m_dt.get_constructor_accessors(c)) {
            sort* rs = acc->get_range();
            if (!m_dt.is_datatype(rs) || !m_dt.is_recursive(rs))
                continue;
            expr_ref acc_y(m.mk_app(acc, y), m);
            if (rs == s) {
                subst.push_back(std::make_pair(conds, acc_y));
            }                
            if (depth > 1) {
                mk_hypothesis_substs_rec(depth - 1, s, acc_y, conds, subst);
            }
        }
        conds.pop_back();
    }
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
 */

void induction_lemmas::mk_hypothesis_lemma(expr_ref_vector const& conds, expr_pair_vector const& subst, literal alpha) {
    expr_ref beta(m);
    ctx.literal2expr(alpha, beta);
    expr_safe_replace rep(m);
    for (auto const& p : subst) {
        rep.insert(p.first, p.second);
    }
    rep(beta);                          // set beta := alpha[sk/acc(acc2(sk))]
    // alpha & is-c(sk) => ~alpha[sk/acc(sk)]
    literal_vector lits;
    lits.push_back(~alpha);
    for (expr* c : conds) lits.push_back(~mk_literal(c));
    lits.push_back(~mk_literal(beta));
    add_th_lemma(lits);
}

void induction_lemmas::create_hypotheses(unsigned depth, expr_ref_vector const& sks, literal alpha) {
    if (sks.empty())
        return;

    // extract hypothesis substitutions
    vector<std::pair<expr*, cond_substs_t>> substs;
    for (expr* sk : sks) {
        cond_substs_t subst;
        mk_hypothesis_substs(depth, sk, subst);

        // append the identity substitution:
        expr_ref_vector conds(m);
        subst.push_back(std::make_pair(conds, expr_ref(sk, m)));
        substs.push_back(std::make_pair(sk, subst));
    }

    // create cross-product of instantiations:
    vector<std::pair<expr_ref_vector, expr_pair_vector>> s1, s2;
    s1.push_back(std::make_pair(expr_ref_vector(m), expr_pair_vector()));
    for (auto const& x2cond_sub : substs) {
        s2.reset();
        for (auto const& cond_sub : x2cond_sub.second) {
            for (auto const& cond_subs : s1) {
                expr_pair_vector pairs(cond_subs.second);
                expr_ref_vector conds(cond_subs.first);
                pairs.push_back(std::make_pair(x2cond_sub.first, cond_sub.second));
                conds.append(cond_sub.first);
                s2.push_back(std::make_pair(conds, pairs));
            }
        }
        s1.swap(s2);
    }    
    s1.pop_back(); // last substitution is the identity

    // extract lemmas from instantiations
    for (auto& p : s1) {
        mk_hypothesis_lemma(p.first, p.second, alpha);
    }
}


void induction_lemmas::add_th_lemma(literal_vector const& lits) {
    IF_VERBOSE(0, ctx.display_literals_verbose(verbose_stream() << "lemma:\n", lits) << "\n");
    ctx.mk_clause(lits.size(), lits.data(), nullptr, smt::CLS_TH_AXIOM); 
    // CLS_TH_LEMMA, but then should re-instance if GC'ed
    ++m_num_lemmas;
}

literal induction_lemmas::mk_literal(expr* e) {
    expr_ref _e(e, m);
    if (!ctx.e_internalized(e)) {
        ctx.internalize(e, false);
    }
    enode* n = ctx.get_enode(e);
    ctx.mark_as_relevant(n);
    return ctx.get_literal(e);
}



bool induction_lemmas::operator()(literal lit) {
    enode* r = ctx.bool_var2enode(lit.var());

#if 1
    auto combinations = induction_combinations(r);
    for (auto const& positions : combinations) {
        apply_induction(lit, positions);
    }
    return !combinations.empty();
#else
    unsigned num = m_num_lemmas;
    expr_ref_vector sks(m);
    expr_safe_replace rep(m);
    // have to be non-overlapping:
    for (enode* n : induction_positions(r)) {
        expr* t = n->get_owner();
        if (is_uninterp_const(t)) { // for now, to avoid overlapping terms
            sort* s = t->get_sort();
            expr_ref sk(m.mk_fresh_const("sk", s), m);
            sks.push_back(sk);
            rep.insert(t, sk);
        }
    }
    expr_ref alpha(m);
    ctx.literal2expr(lit, alpha);
    rep(alpha);
    literal alpha_lit = mk_literal(alpha);

    // alpha is the minimal instance of induction_positions where lit holds
    // alpha & is-c(sk) => ~alpha[sk/acc(sk)]
    create_hypotheses(1, sks, alpha_lit);
    if (m_num_lemmas == num)
        return false;
    // lit => alpha
    literal_vector lits;
    lits.push_back(~lit);
    lits.push_back(alpha_lit);
    add_th_lemma(lits);        
    return true;
#endif
}

void induction_lemmas::apply_induction(literal lit, induction_positions_t const & positions) {
    unsigned num = m_num_lemmas;
    obj_map<expr, expr*> term2skolem;
    expr_ref alpha(m), sk(m);
    expr_ref_vector sks(m);
    ctx.literal2expr(lit, alpha);
    induction_term_and_position_t itp(alpha, positions);
    bool found = m_skolems.find(itp, itp);
    if (found) {
        sks.append(itp.m_skolems.size(), itp.m_skolems.data());
    }
    
    unsigned i = 0;
    for (auto const& p : positions) {
        expr* t = p.first->get_expr()->get_arg(p.second);
        if (term2skolem.contains(t))
            continue;
        if (i == sks.size()) {
            sk = m.mk_fresh_const("sk", t->get_sort());
            sks.push_back(sk);
        }
        else {
            sk = sks.get(i);
        }
        term2skolem.insert(t, sk);
        ++i;
    }
    if (!found) {
        itp.m_skolems.append(sks.size(), sks.data());
        m_trail.push_back(alpha);
        m_trail.append(sks);
        m_skolems.insert(itp);
    }
    
    ptr_vector<expr> todo;
    obj_map<expr, expr*> sub;
    expr_ref_vector trail(m), args(m);
    todo.push_back(alpha);
    // replace occurrences of induction arguments.
#if 0
    std::cout << "positions\n";
    for (auto const& p : positions)
        std::cout << mk_pp(p.first->get_owner(), m) << " " << p.second << "\n";
#endif
    while (!todo.empty()) {
        expr* t = todo.back();
        if (sub.contains(t)) {
            todo.pop_back();
            continue;
        }
        SASSERT(is_app(t));
        args.reset();
        unsigned sz = todo.size();
        expr* s = nullptr;
        for (unsigned i = 0; i < to_app(t)->get_num_args(); ++i) {
            expr* arg = to_app(t)->get_arg(i);
            found = false;
            for (auto const& p : positions) {
                if (p.first->get_expr() == t && p.second == i) {
                    args.push_back(term2skolem[arg]);
                    found = true;
                    break;
                }
            }
            if (found)
                continue;
            if (sub.find(arg, s)) {
                args.push_back(s);
                continue;
            }
            todo.push_back(arg);            
        }
        if (todo.size() == sz) {
            s = m.mk_app(to_app(t)->get_decl(), args);
            trail.push_back(s);
            sub.insert(t, s);
            todo.pop_back();
        }
    }
    alpha = sub[alpha];
    std::cout << "alpha:" << alpha << "\n";
    literal alpha_lit = mk_literal(alpha);

    // alpha is the minimal instance of induction_positions where lit holds
    // alpha & is-c(sk) => ~alpha[sk/acc(sk)]
    create_hypotheses(1, sks, alpha_lit);
    if (m_num_lemmas > num) {
        // lit => alpha
        literal_vector lits;
        lits.push_back(~lit);
        lits.push_back(alpha_lit);
        add_th_lemma(lits);            
    }
}

induction_lemmas::induction_lemmas(context& ctx, ast_manager& m):
    ctx(ctx),
    m(m),
    m_dt(m),
    m_a(m),
    m_rec(m),
    m_num_lemmas(0),
    m_trail(m)
{}

induction::induction(context& ctx, ast_manager& m):
    ctx(ctx),
    m(m),
    vs(m),
    m_collect_literals(ctx, m, vs),
    m_create_lemmas(ctx, m)
{}

// TBD: use smt_arith_value to also include state from arithmetic solver
void induction::init_values() {
    for (enode* n : ctx.enodes()) 
        if (m.is_value(n->get_expr())) 
            for (enode* r : *n) 
                if (r != n) {
                    vs.set_value(r->get_expr(), n->get_expr());
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
