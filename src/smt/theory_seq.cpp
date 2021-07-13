/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_seq.cpp

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Outline:

 A cascading sequence of solvers:
 
 - simplify_and_solve_eqs
   - canonize equality
   - solve_unit_eq: x = t, where x not in t.
   - solve_binary_eq: xa = bx -> a = b, xa = bx
   - solve_nth_eq: x = unit(nth(x,0)).unit(nth(x,1)).unit(nth(x,2)...unit(nth(x,n-1))
   - solve_itos: itos(i) = "" -> i < 0   

 - check_contains
   Original
   - (f,dep) = canonize(contains(a, b))
     lit := |b| > |a|
     f := true -> conflict
     f := false -> solved
     value(lit) = l_true -> solved
     f := s = t -> dep -> s != t
     f := f1 & f2 -> dep -> ~f1 | ~f2
     f := f1 | f2 -> dep -> ~f1 & ~f2
   Revised:
   - contains(a,b) or len(a) < len(b)
   - contains(a,b) or ~prefix(b, a) 
   - contains(a,b) or ~contains(tail(a,0), b)
   - a = empty or a = unit(nth_i(a,0)) + tail(a,0)
   Note that
     len(a) < len(b) implies ~prefix(b, a) and ~contains(tail(a,0),b)
     So the recursive axioms are not instantiated in this case.

 - solve_nqs
   - s_i = t_i, d_i <- solve(s = t)
   - create literals for s_i = t_i
   - if one of created literals is false, done.
   - conflict if all created literals are true

 - fixed_length
   - len(s) = k -> s = unit(nth(0,s)).unit(nth(1,s))....unit(nth(n-1,s))

 - len_based_split
   s = x.xs t = y.ys, len(x) = len(y) -> x = y & xs = ys
   s = x.xs t = y.ys, len(x) = len(y) + offset -> y = x*Z, Z*xs = ys
   s = x.x'.xs, t = y.y'.ys, len(xs) = len(ys) -> xs = ys
   
 - check_int_string
   e := itos(n), len(e) = v, v > 0 ->      
   n := stoi(e), len(e) = v, v > 0 -> 
   -  n >= 0 & len(e) >= i + 1 => is_digit(e_i) for i = 0..k-1
   -  n >= 0 & len(e) = k => n = sum 10^i*digit(e_i)
   -  n < 0  & len(e) = k => \/_i ~is_digit(e_i) for i = 0..k-1
   -  10^k <= n < 10^{k+1}-1 => len(e) => k

 - reduce_length_eq
   x1...xn = y1...ym, len(x1...xk) = len(y1...yj) -> x1...xk = y1..yj, x{k+1}..xn = y{j+1}..ym

 - branch_unit_variable
   len(x) = n -> x = unit(a1)unit(a2)...unit(a_n)

 - branch_binary_variable
   x ++ units1 = units2 ++ y -> x is prefix of units2 or x = units2 ++ y1, y = y1 ++ y2, y2 = units2

 - branch_variable
   - branch_variable_mb
     s = xs, t = ys, each x_i, y_j has a length.
     based on length comparisons decompose into smaller equalities.

   - branch_variable_eq
     cycle through branch options

   - branch_ternary_variable1
     
   - branch_ternary_variable2

 - check_length_coherence
   len(e) >= lo => e = unit(nth(0,e)).unit(nth(1,e))....unit(nth(lo-1,e)).seq
   len(e) <= lo => seq = empty
   len(e) <= hi => len(seq) <= hi - lo

 - check_extensionality


--*/

#include <typeinfo>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_trail.h"
#include "ast/for_each_expr.h"
#include "model/value_factory.h"
#include "smt/smt_context.h"
#include "smt/theory_seq.h"
#include "smt/theory_arith.h"
#include "smt/theory_lra.h"
#include "smt/smt_kernel.h"

using namespace smt;

void theory_seq::solution_map::update(expr* e, expr* r, dependency* d) {
    if (e == r) {
        return;
    }
    m_cache.reset();
    expr_dep value;
    if (find(e, value)) {
        add_trail(DEL, e, value.e, value.d);
    }
    value.v = e;
    value.e = r;
    value.d = d;
    insert(value);
    add_trail(INS, e, r, d);
}

void theory_seq::solution_map::add_trail(map_update op, expr* l, expr* r, dependency* d) {
    m_updates.push_back(op);
    m_lhs.push_back(l);
    m_rhs.push_back(r);
    m_deps.push_back(d);
}

bool theory_seq::solution_map::is_root(expr* e) const {
    return e->get_id() >= m_map.size() || m_map[e->get_id()].e == nullptr;
}

// e1 -> ... -> e2
// e2 -> e3
// e1 -> .... -> e3

// e1 -> ... x, e2 -> ... x
void theory_seq::solution_map::find_rec(expr* e, svector<expr_dep >& finds) {
    dependency* d = nullptr;
    expr_dep value(e, e, d);
    do {
        e = value.e;
        d = m_dm.mk_join(d, value.d);
        finds.push_back(value);
    }
    while (find(e, value));
}

bool theory_seq::solution_map::find1(expr* e, expr*& r, dependency*& d) {
    expr_dep value;
    if (find(e, value)) {
        d = m_dm.mk_join(d, value.d);
        r = value.e;
        return true;
    }
    else {
        return false;
    }
}

expr* theory_seq::solution_map::find(expr* e, dependency*& d) {
    expr_dep value;
    d = nullptr;
    expr* result = e;
    while (find(result, value)) {
        d = m_dm.mk_join(d, value.d);
        SASSERT(result != value.e);
        SASSERT(e != value.e);
        result = value.e;
    }
    return result;
}

expr* theory_seq::solution_map::find(expr* e) {
    expr_dep value;
    while (find(e, value)) {
        e = value.e;
    }
    return e;
}

void theory_seq::solution_map::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;
    m_cache.reset();
    unsigned start = m_limit[m_limit.size() - num_scopes];
    for (unsigned i = m_updates.size(); i-- > start; ) {
        if (m_updates[i] == INS) {
            unsigned id = m_lhs.get(i)->get_id();
            if (id < m_map.size()) m_map[id] = expr_dep();
        }
        else {
            insert(expr_dep(m_lhs.get(i), m_rhs.get(i), m_deps[i]));
        }
    }
    m_updates.resize(start);
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_deps.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

void theory_seq::solution_map::display(std::ostream& out) const {
    for (auto const& ed : m_map) {
        if (ed.v) out << mk_bounded_pp(ed.v, m, 2) << " |-> " << mk_bounded_pp(ed.e, m, 2) << "\n";
    }
}

bool theory_seq::exclusion_table::contains(expr* e, expr* r) const {
    if (e->get_id() > r->get_id()) {
        std::swap(e, r);
    }
    return m_table.contains(std::make_pair(e, r));
}

void theory_seq::exclusion_table::update(expr* e, expr* r) {
    if (e->get_id() > r->get_id()) {
        std::swap(e, r);
    }
    if (e != r && !m_table.contains(std::make_pair(e, r))) {
        m_lhs.push_back(e);
        m_rhs.push_back(r);
        m_table.insert(std::make_pair(e, r));
    }
}

void theory_seq::exclusion_table::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;
    unsigned start = m_limit[m_limit.size() - num_scopes];
    for (unsigned i = start; i < m_lhs.size(); ++i) {
        m_table.erase(std::make_pair(m_lhs.get(i), m_rhs.get(i)));
    }
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

void theory_seq::exclusion_table::display(std::ostream& out) const {
    for (auto const& kv : m_table) {
        out << mk_bounded_pp(kv.first, m, 2) << " != " << mk_bounded_pp(kv.second, m, 2) << "\n";
    }
}


theory_seq::theory_seq(context& ctx):
    theory(ctx, ctx.get_manager().mk_family_id("seq")),
    m_rep(m, m_dm),
    m_lts_checked(false),
    m_eq_id(0),
    m_find(*this),
    m_offset_eq(*this, m),
    m_overlap_lhs(m),
    m_overlap_rhs(m),
    m_factory(nullptr),
    m_exclude(m),
    m_axioms(m),
    m_axioms_head(0),
    m_int_string(m),
    m_ubv_string(m),
    m_length(m),
    m_length_limit(m),
    m_mg(nullptr),
    m_rewrite(m),
    m_str_rewrite(m),
    m_seq_rewrite(m),
    m_util(m),
    m_autil(m),
    m_sk(m, m_rewrite),
    m_ax(*this, m_rewrite),
    m_eq(m, *this, m_ax.ax()),
    m_regex(*this),
    m_arith_value(m),
    m_trail_stack(),
    m_ls(m), m_rs(m),
    m_lhs(m), m_rhs(m),
    m_new_eqs(m),
    m_max_unfolding_depth(1),
    m_max_unfolding_lit(null_literal),
    m_unhandled_expr(nullptr),
    m_has_seq(m_util.has_seq()),
    m_new_solution(false),
    m_new_propagation(false) {
}

theory_seq::~theory_seq() {
    m_trail_stack.reset();
}

void theory_seq::init() {
    params_ref p;
    p.set_bool("coalesce_chars", false);
    m_rewrite.updt_params(p);

    std::function<void(literal, literal, literal, literal, literal)> add_ax = [&](literal l1, literal l2, literal l3, literal l4, literal l5) {
        add_axiom(l1, l2, l3, l4, l5);
    };
    std::function<literal(expr*,bool)> mk_eq_emp = [&](expr* e, bool p) { return mk_eq_empty(e, p); };
    m_ax.add_axiom5 = add_ax;
    m_ax.mk_eq_empty2 = mk_eq_emp;
    m_arith_value.init(&ctx);
}

#define TRACEFIN(s) { TRACE("seq", tout << ">>" << s << "\n";); IF_VERBOSE(20, verbose_stream() << s << "\n"); }

struct scoped_enable_trace {
    scoped_enable_trace() {
        enable_trace("seq");
    }
    ~scoped_enable_trace() {
        disable_trace("seq");
    }
};

final_check_status theory_seq::final_check_eh() {
    if (!m_has_seq) {
        return FC_DONE;
    }
    
    m_new_propagation = false;
    TRACE("seq", display(tout << "level: " << ctx.get_scope_level() << "\n"););
    TRACE("seq_verbose", ctx.display(tout););

    if (simplify_and_solve_eqs()) {
        ++m_stats.m_solve_eqs;
        TRACEFIN("solve_eqs");
        return FC_CONTINUE;
    }    
    if (check_lts()) {
        TRACEFIN("check_lts");
        return FC_CONTINUE;
    }
    if (solve_nqs(0)) {
        ++m_stats.m_solve_nqs;
        TRACEFIN("solve_nqs");
        return FC_CONTINUE;
    }
    if (m_regex.propagate()) {
        TRACEFIN("regex propagate");
        return FC_CONTINUE;
    }
    if (check_contains()) {
        ++m_stats.m_propagate_contains;
        TRACEFIN("propagate_contains");
        return FC_CONTINUE;
    }
    if (fixed_length(true)) {
        ++m_stats.m_fixed_length;
        TRACEFIN("zero_length");
        return FC_CONTINUE;
    }
    if (get_fparams().m_split_w_len && len_based_split()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("split_based_on_length");
        return FC_CONTINUE;
    }
    if (fixed_length()) {
        ++m_stats.m_fixed_length;
        TRACEFIN("fixed_length");
        return FC_CONTINUE;
    }
    if (check_int_string()) {
        ++m_stats.m_int_string;
        TRACEFIN("int_string");
        return FC_CONTINUE;
    }
    if (check_ubv_string()) {
        ++m_stats.m_ubv_string;
        TRACEFIN("ubv_string");
        return FC_CONTINUE;
    }
    if (reduce_length_eq()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("reduce_length");
        return FC_CONTINUE;
    }
    if (branch_unit_variable()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("branch_unit_variable");
        return FC_CONTINUE;
    }
    if (branch_binary_variable()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("branch_binary_variable");
        return FC_CONTINUE;
    }
    if (branch_variable()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("branch_variable");
        return FC_CONTINUE;
    }
    if (check_length_coherence()) {
        ++m_stats.m_check_length_coherence;
        TRACEFIN("check_length_coherence");
        return FC_CONTINUE;
    }
    if (!check_extensionality()) {
        ++m_stats.m_extensionality;
        TRACEFIN("extensionality");
        return FC_CONTINUE;
    }
    if (branch_nqs()) {
        ++m_stats.m_branch_nqs;
        TRACEFIN("branch_ne");
        return FC_CONTINUE;
    }    
    if (branch_itos()) {
        TRACEFIN("branch_itos");
        return FC_CONTINUE;
    }
    if (m_unhandled_expr) {
        TRACEFIN("give_up");
        TRACE("seq", tout << "unhandled: " << mk_pp(m_unhandled_expr, m) << "\n";);
        return FC_GIVEUP;
    }
    if (is_solved()) {
        //scoped_enable_trace _se;
        TRACEFIN("is_solved");
        TRACE("seq", display(tout););
        return FC_DONE;
    }
    TRACEFIN("give_up");
    return FC_GIVEUP;
}



bool theory_seq::set_empty(expr* x) {
    add_axiom(~mk_eq(m_autil.mk_int(0), mk_len(x), false), mk_eq_empty(x));
    return true;
}

bool theory_seq::enforce_length(expr_ref_vector const& es, vector<rational> & len) {
    bool all_have_length = true;
    rational val;
    zstring s;
    for (expr* e : es) {
        if (m_util.str.is_unit(e)) {
            len.push_back(rational(1));
        } 
        else if (m_util.str.is_empty(e)) {
            len.push_back(rational(0));
        }
        else if (m_util.str.is_string(e, s)) {
            len.push_back(rational(s.length()));
        }
        else if (get_length(e, val)) {
            len.push_back(val);
        }
        else {
            add_length_to_eqc(e);
            all_have_length = false;
        }
    }
    return all_have_length;
}


bool theory_seq::fixed_length(bool is_zero) {
    bool found = false;    
    for (unsigned i = 0; i < m_length.size(); ++i) {
        expr* e = m_length.get(i);
        if (fixed_length(e, is_zero)) {
            found = true;
        }
    }
    return found;
}

bool theory_seq::fixed_length(expr* len_e, bool is_zero) {
    rational lo, hi;
    expr* e = nullptr;
    VERIFY(m_util.str.is_length(len_e, e));
    if (!(is_var(e) && lower_bound(len_e, lo) && upper_bound(len_e, hi) && lo == hi
          && ((is_zero && lo.is_zero()) || (!is_zero && lo.is_unsigned())))) {
        return false;
    }
    if (m_sk.is_tail(e) || 
        m_sk.is_seq_first(e) || 
        m_sk.is_indexof_left(e) || 
        m_sk.is_indexof_right(e) ||
        m_fixed.contains(e)) {
        return false;
    }
    
    m_trail_stack.push(insert_obj_trail<expr>(m_fixed, e));
    m_fixed.insert(e);

    expr_ref seq(e, m), head(m), tail(m);

    if (lo.is_zero()) {
        seq = m_util.str.mk_empty(e->get_sort());
    }
    else if (!is_zero) {
        unsigned _lo = lo.get_unsigned();
        expr_ref_vector elems(m);        
        for (unsigned j = 0; j < _lo; ++j) {
            m_sk.decompose(seq, head, tail);
            elems.push_back(head);
            seq = tail;
        }
        seq = mk_concat(elems.size(), elems.data());
    }
    TRACE("seq", tout << "Fixed: " << mk_bounded_pp(e, m, 2) << " " << lo << "\n";);
    literal a = mk_eq(len_e, m_autil.mk_numeral(lo, true), false);
    if (ctx.get_assignment(a) == l_false)
        return false;
    literal b = mk_seq_eq(seq, e);
    if (ctx.get_assignment(b) == l_true)
        return false;
    add_axiom(~a, b);
    if (!ctx.at_base_level()) {
        m_trail_stack.push(push_replay(*this, alloc(replay_fixed_length, m, len_e)));
    }
    return true;
}


/*
    lit => s != ""
*/
void theory_seq::propagate_non_empty(literal lit, expr* s) {
    SASSERT(ctx.get_assignment(lit) == l_true);
    propagate_lit(nullptr, 1, &lit, ~mk_eq_empty(s));
}

bool theory_seq::propagate_is_conc(expr* e, expr* conc) {
    TRACE("seq", tout << mk_pp(conc, m) << " is non-empty\n";);
    literal lit = ~mk_eq_empty(e);
    if (ctx.get_assignment(lit) == l_true) {
        propagate_lit(nullptr, 1, &lit, mk_eq(e, conc, false));
        expr_ref e1(e, m), e2(conc, m);
        new_eq_eh(m_dm.mk_leaf(assumption(lit)), ctx.get_enode(e1), ctx.get_enode(e2));
        return true;
    }
    else {
        return false;
    }
}

bool theory_seq::is_unit_nth(expr* e) const {
    expr *s = nullptr;
    return m_util.str.is_unit(e, s) && m_util.str.is_nth_i(s);
}

expr_ref theory_seq::mk_nth(expr* s, expr* idx) {
    expr_ref result(m_util.str.mk_nth_i(s, idx), m);
    return result;
}

void theory_seq::mk_decompose(expr* e, expr_ref& head, expr_ref& tail) {
    m_sk.decompose(e, head, tail);
    add_axiom(~mk_eq_empty(e), mk_eq_empty(tail));;
    add_axiom(mk_eq_empty(e), mk_eq(e, mk_concat(head, tail), false));
}

/*
   \brief Check extensionality (for sequences).
 */
bool theory_seq::check_extensionality() {
    unsigned sz = get_num_vars();
    unsigned_vector seqs;
    for (unsigned v = 0; v < sz; ++v) {
        enode* n1 = get_enode(v);
        expr* o1 = n1->get_expr();
        if (n1 != n1->get_root()) {
            continue;
        }
        if (!seqs.empty() && ctx.is_relevant(n1) && m_util.is_seq(o1) && ctx.is_shared(n1)) {
            dependency* dep = nullptr;
            expr_ref e1(m);
            if (!canonize(o1, dep, e1)) {
                return false;
            }
            for (theory_var v : seqs) {
                enode* n2 = get_enode(v);
                expr* o2 = n2->get_expr();
                if (o1->get_sort() != o2->get_sort()) {
                    continue;
                }
                if (ctx.is_diseq(n1, n2) || m_exclude.contains(o1, o2)) {
                    continue;
                }
                expr_ref e2(m);
                if (!canonize(n2->get_expr(), dep, e2)) {
                    return false;
                }
                m_new_eqs.reset();
                bool change = false;
                if (!m_seq_rewrite.reduce_eq(e1, e2, m_new_eqs, change)) {
                    TRACE("seq", tout << "exclude " << mk_pp(o1, m) << " " << mk_pp(o2, m) << "\n";);
                    m_exclude.update(o1, o2);
                    continue;
                }
                bool excluded = false;
                for (auto const& p : m_new_eqs) {
                    if (m_exclude.contains(p.first, p.second)) {
                        TRACE("seq", tout << "excluded " << mk_pp(p.first, m) << " " << mk_pp(p.second, m) << "\n";);
                        excluded = true;
                        break;
                    }
                }
                if (excluded) {
                    continue;
                }
                ctx.assume_eq(n1, n2);
                return false;
            }
        }
        seqs.push_back(v);
    }
    return true;
}

/*
  \brief check negated contains constraints.
 */
bool theory_seq::check_contains() {
    for (unsigned i = 0; !ctx.inconsistent() && i < m_ncs.size(); ++i) {
        if (solve_nc(i)) {
            m_ncs.erase_and_swap(i--);
        }
    }
    return m_new_propagation || ctx.inconsistent();
}

bool theory_seq::check_lts() {
    if (m_lts.empty() || m_lts_checked) {
        return false;
    }
    unsigned sz = m_lts.size();
    m_trail_stack.push(value_trail<bool>(m_lts_checked));
    m_lts_checked = true;
    expr* a = nullptr, *b = nullptr, *c = nullptr, *d = nullptr;
    bool is_strict1, is_strict2;
    for (unsigned i = 0; i + 1 < sz; ++i) {
        expr* p1 = m_lts[i];
        VERIFY(m_util.str.is_lt(p1, a, b) || m_util.str.is_le(p1, a, b));
        literal r1 = ctx.get_literal(p1);
        if (ctx.get_assignment(r1) == l_false) {
            std::swap(a, b);
            r1.neg();
            is_strict1 = m_util.str.is_le(p1);
        }
        else {
            is_strict1 = m_util.str.is_lt(p1);
        }
        for (unsigned j = i + 1; j < sz; ++j) {
            expr* p2 = m_lts[j];
            VERIFY(m_util.str.is_lt(p2, c, d) || m_util.str.is_le(p2, c, d));
            literal r2 = ctx.get_literal(p2);
            if (ctx.get_assignment(r2) == l_false) {
                std::swap(c, d);
                r2.neg();
                is_strict2 = m_util.str.is_le(p2);
            }
            else {
                is_strict2 = m_util.str.is_lt(p2);
            }
            if (ctx.get_enode(b)->get_root() == ctx.get_enode(c)->get_root()) {

                literal eq = (b == c) ? true_literal : mk_eq(b, c, false);
                bool is_strict = is_strict1 || is_strict2; 
                if (is_strict) {
                    add_axiom(~r1, ~r2, ~eq, mk_literal(m_util.str.mk_lex_lt(a, d)));
                }
                else {
                    add_axiom(~r1, ~r2, ~eq, mk_literal(m_util.str.mk_lex_le(a, d)));
                }
            }
        }
    }
    return true;
}

/*
   - Eqs = 0
   - Diseqs evaluate to false
   - lengths are coherent.
*/

bool theory_seq::is_solved() {
    if (!m_eqs.empty()) {
        TRACE("seq", tout << "(seq.giveup " << m_eqs[0].ls << " = " << m_eqs[0].rs << " is unsolved)\n";);
        IF_VERBOSE(10, verbose_stream() << "(seq.giveup " << m_eqs[0].ls << " = " << m_eqs[0].rs << " is unsolved)\n";);
        return false;
    }
    if (!m_ncs.empty()) {
        TRACE("seq", display_nc(tout << "(seq.giveup ", m_ncs[0]); tout << " is unsolved)\n";);
        IF_VERBOSE(10, display_nc(verbose_stream() << "(seq.giveup ", m_ncs[0]); verbose_stream() << " is unsolved)\n";);
        return false;
    }

#if 0
    // debug code
    for (enode* n : ctx.enodes()) {
        expr* e = nullptr;
        rational len1, len2;
        if (m_util.str.is_length(n->get_owner(), e)) {
            VERIFY(get_length(e, len1));
            dependency* dep = nullptr;
            expr_ref r = canonize(e, dep);
            if (get_length(r, len2)) {
                SASSERT(len1 == len2);
            }
            else {
                IF_VERBOSE(0, verbose_stream() << r << "does not have a length\n");
            }
        }        
    }
#endif

    return true;
}

/**
   \brief while extracting dependency literals ensure that they have all been asserted on the context.
*/
void theory_seq::linearize(dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const {
    DEBUG_CODE(for (literal lit : lits) SASSERT(ctx.get_assignment(lit) == l_true); );
    svector<assumption> assumptions;
    const_cast<dependency_manager&>(m_dm).linearize(dep, assumptions);
    for (assumption const& a : assumptions) {
        if (a.lit != null_literal) {
            lits.push_back(a.lit);
            SASSERT(ctx.get_assignment(a.lit) == l_true);
        }
        if (a.n1 != nullptr) {
            eqs.push_back(enode_pair(a.n1, a.n2));
        }
    }
}



bool theory_seq::propagate_lit(dependency* dep, unsigned n, literal const* _lits, literal lit) {
    if (lit == true_literal) 
        return false;
    if (ctx.get_assignment(lit) == l_true)
        return false;
    
    literal_vector lits(n, _lits);

    if (lit == false_literal) {
        set_conflict(dep, lits);
        return true;
    }
    ctx.mark_as_relevant(lit);
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    TRACE("seq",
          tout << "scope: " << ctx.get_scope_level() << "\n";
          tout << lits << "\n";
          ctx.display_detailed_literal(tout << "assert:", lit);
          ctx.display_literals_verbose(tout << " <- ", lits);
          if (!lits.empty()) tout << "\n"; display_deps(tout, dep););
    justification* js =
        ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx.get_region(), lits.size(), lits.data(), eqs.size(), eqs.data(), lit));

    m_new_propagation = true;
    ctx.assign(lit, js);
    validate_assign(lit, eqs, lits);
    return true;
}

void theory_seq::set_conflict(dependency* dep, literal_vector const& _lits) {
    enode_pair_vector eqs;
    literal_vector lits(_lits);
    linearize(dep, eqs, lits);
    m_new_propagation = true;
    set_conflict(eqs, lits);
}

void theory_seq::set_conflict(enode_pair_vector const& eqs, literal_vector const& lits) {
    TRACE("seq", display_deps(tout << "assert conflict:", lits, eqs););
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), lits.size(), lits.data(), eqs.size(), eqs.data(), 0, nullptr)));
    validate_conflict(eqs, lits);
}

bool theory_seq::propagate_eq(dependency* dep, enode* n1, enode* n2) {
    if (n1->get_root() == n2->get_root()) {
        return false;
    }
    literal_vector lits;
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    TRACE("seq_verbose",
          tout << "assert: " << mk_bounded_pp(n1->get_expr(), m) << " = " << mk_bounded_pp(n2->get_expr(), m) << " <-\n";
          display_deps(tout, dep); 
          );

    TRACE("seq", 
          tout << "assert: " 
          << mk_bounded_pp(n1->get_expr(), m) << " = " << mk_bounded_pp(n2->get_expr(), m) << " <-\n"
          << lits << "\n";
          );


    justification* js = ctx.mk_justification(
        ext_theory_eq_propagation_justification(
            get_id(), ctx.get_region(), lits.size(), lits.data(), eqs.size(), eqs.data(), n1, n2));
    
    {
        std::function<expr*(void)> fn = [&]() { return m.mk_eq(n1->get_expr(), n2->get_expr()); };
        scoped_trace_stream _sts(*this, fn);
        ctx.assign_eq(n1, n2, eq_justification(js));
    }
    validate_assign_eq(n1, n2, eqs, lits);

    m_new_propagation = true;

    enforce_length_coherence(n1, n2);
    return true;
}

bool theory_seq::propagate_eq(dependency* dep, expr* e1, expr* e2, bool add_eq) {
    literal_vector lits;
    return propagate_eq(dep, lits, e1, e2, add_eq);
}

bool theory_seq::propagate_eq(dependency* dep, literal lit, expr* e1, expr* e2, bool add_to_eqs) {
    literal_vector lits;
    lits.push_back(lit);
    return propagate_eq(dep, lits, e1, e2, add_to_eqs);
}

void theory_seq::enforce_length_coherence(enode* n1, enode* n2) {
    expr* o1 = n1->get_expr();
    expr* o2 = n2->get_expr();
    if (m_util.str.is_concat(o1) && m_util.str.is_concat(o2)) {
        return;
    }
    if (has_length(o1) && !has_length(o2)) {
        add_length_to_eqc(o2);
    }
    else if (has_length(o2) && !has_length(o1)) {
        add_length_to_eqc(o1);
    }
}


bool theory_seq::lift_ite(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps) {
    if (ls.size() != 1 || rs.size() != 1) {
        return false;
    }
    expr* c = nullptr, *t = nullptr, *e = nullptr;
    expr* l = ls[0], *r = rs[0];
    if (m.is_ite(r)) {
        std::swap(l, r);
    }
    if (!m.is_ite(l, c, t, e)) {
        return false;
    }
     
    switch (ctx.find_assignment(c)) {
    case l_undef: 
        return false;
    case l_true:
        deps = mk_join(deps, ctx.get_literal(c));
        m_eqs.push_back(mk_eqdep(t, r, deps));
        return true;
    case l_false:
        deps = mk_join(deps, ~ctx.get_literal(c));
        m_eqs.push_back(mk_eqdep(e, r, deps));
        return true;
    }
    return false;
}


bool theory_seq::simplify_eq(expr_ref_vector& ls, expr_ref_vector& rs, dependency* deps) {
    expr_ref_pair_vector& new_eqs = m_new_eqs;
    new_eqs.reset();
    bool changed = false;
    TRACE("seq", 
          for (expr* l : ls) tout << "s#" << l->get_id() << " " << mk_bounded_pp(l, m, 2) << "\n";
          tout << " = \n";
          for (expr* r : rs) tout << "s#" << r->get_id() << " " << mk_bounded_pp(r, m, 2) << "\n";);

    if (!m_seq_rewrite.reduce_eq(ls, rs, new_eqs, changed)) {
        // equality is inconsistent.
        TRACE("seq_verbose", tout << ls << " != " << rs << "\n";);
        set_conflict(deps);
        return true;
    }

    if (!changed) {
        SASSERT(new_eqs.empty());
        return false;
    }
    TRACE("seq",
          tout << "reduced to\n";
          for (auto p : new_eqs) {
              tout << mk_bounded_pp(p.first, m, 2) << "\n";
              tout << " = \n";
              tout << mk_bounded_pp(p.second, m, 2) << "\n";
          }
          );
    m_seq_rewrite.add_seqs(ls, rs, new_eqs);
    if (new_eqs.empty()) {
        TRACE("seq", tout << "solved\n";);
        return true;
    }
    TRACE("seq_verbose", 
          tout << ls << " = " << rs << "\n";);
    for (auto const& p : new_eqs) {
        if (ctx.inconsistent())
            break;
        expr_ref li(p.first, m);
        expr_ref ri(p.second, m);
        seq::eq_ptr r;
        m_eq_deps = deps;
        if (m_eq.reduce(li, ri, r)) {
            if (r) {
                m_eqs.push_back(mk_eqdep(r->ls, r->rs, deps));
            }
        }
        else if (m_util.is_seq(li) || m_util.is_re(li)) {
            TRACE("seq_verbose", tout << "inserting " << li << " = " << ri << "\n";);
            m_eqs.push_back(mk_eqdep(li, ri, deps));            
        }
        else {
            propagate_eq(deps, ensure_enode(li), ensure_enode(ri));
        }
    }
    TRACE("seq_verbose",
          if (!ls.empty() || !rs.empty()) tout << ls << " = " << rs << ";\n";
          for (auto const& p : new_eqs) {
              tout << mk_pp(p.first, m) << " = " << mk_pp(p.second, m) << ";\n";
          });


    return true;
}


bool theory_seq::reduce_length(expr* l, expr* r, literal_vector& lits) {
    expr_ref len1(m), len2(m);
    lits.reset();
    if (get_length(l, len1, lits) &&
        get_length(r, len2, lits) && len1 == len2) {
        return true;
    }
    else {
        return false;
    }
}


bool theory_seq::is_var(expr* a) const {
    return m_eq.is_var(a);
}



bool theory_seq::add_solution(expr* l, expr* r, dependency* deps)  {
    if (l == r) {
        return false;
    }
    m_new_solution = true;
    m_rep.update(l, r, deps);
    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);    
    TRACE("seq", tout << mk_bounded_pp(l, m, 2) << " ==> " << mk_bounded_pp(r, m, 2) << "\n"; display_deps(tout, deps);
          tout << "#" << n1->get_owner_id() << " ==> #" << n2->get_owner_id() << "\n";
          tout << (n1->get_root() == n2->get_root()) << "\n";);         
    propagate_eq(deps, n1, n2);
    return true;
}

bool theory_seq::propagate_max_length(expr* l, expr* r, dependency* deps) {
    unsigned idx;
    expr* s;
    if (m_util.str.is_empty(l)) {
        std::swap(l, r);
    }
    rational hi;
    if (m_sk.is_tail_u(l, s, idx) && has_length(s) && m_util.str.is_empty(r) && !upper_bound(s, hi)) {
        propagate_lit(deps, 0, nullptr, m_ax.mk_le(mk_len(s), idx+1));
        return true;
    }
    return false;
}


bool theory_seq::reduce_length_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps) {
    if (ls.empty() || rs.empty()) {
        return false;
    }
    if (ls.size() <= 1 && rs.size() <= 1) {
        return false;
    }
    SASSERT(ls.size() > 1 || rs.size() > 1);

    literal_vector lits;
    expr_ref l(ls[0], m), r(rs[0], m);
    if (reduce_length(l, r, lits)) {
        expr_ref_vector lhs(m), rhs(m);
        lhs.append(ls.size()-1, ls.data() + 1);
        rhs.append(rs.size()-1, rs.data() + 1);
        SASSERT(!lhs.empty() || !rhs.empty());
        deps = mk_join(deps, lits);
        m_eqs.push_back(depeq(m_eq_id++, lhs, rhs, deps));
        TRACE("seq", tout << "Propagate equal lengths " << l << " " << r << "\n";);
        propagate_eq(deps, lits, l, r, true);
        return true;
    }

    l = ls.back(); r = rs.back();
    if (reduce_length(l, r, lits)) {
        expr_ref_vector lhs(m), rhs(m);
        lhs.append(ls.size()-1, ls.data());
        rhs.append(rs.size()-1, rs.data());
        SASSERT(!lhs.empty() || !rhs.empty());
        deps = mk_join(deps, lits);
        TRACE("seq", tout << "Propagate equal lengths " << l << " " << r << "\n" << "ls: " << ls << "\nrs: " << rs << "\n";);
        m_eqs.push_back(depeq(m_eq_id++, lhs, rhs, deps));
        propagate_eq(deps, lits, l, r, true);
        return true;
    }

    rational len1, len2, len;
    if (ls.size() > 1 && get_length(ls[0], len1) && get_length(rs[0], len2) && len1 >= len2) {
        unsigned j = 1; 
        for (; j < rs.size() && len1 > len2 && get_length(rs[j], len); ++j) { 
            len2 += len; 
        }
        if (len1 == len2 && 0 < j && j < rs.size() && reduce_length(1, j, true, ls, rs, deps)) {
            TRACE("seq", tout << "l equal\n";);
            return true;
        }
    }
    if (rs.size() > 1 && get_length(rs[0], len1) && get_length(ls[0], len2) && len1 > len2) {
        unsigned j = 1; 
        for (; j < ls.size() && len1 > len2 && get_length(ls[j], len); ++j) { 
            len2 += len; 
        }
        if (len1 == len2 && 0 < j && j < ls.size() && reduce_length(j, 1, true, ls, rs, deps)) {
            TRACE("seq", tout << "r equal\n";);
            return true;
        }
    }
    if (ls.size() > 1 && get_length(ls.back(), len1) && get_length(rs.back(), len2) && len1 >= len2) {
        unsigned j = rs.size()-1; 
        for (; j > 0 && len1 > len2 && get_length(rs[j-1], len); --j) { 
            len2 += len; 
        }
        if (len1 == len2 && 0 < j && j < rs.size() && reduce_length(ls.size()-1, rs.size()-j, false, ls, rs, deps)) {
            TRACE("seq", tout << "l suffix equal\n";);
            return true;
        }
    }
    if (rs.size() > 1 && get_length(rs.back(), len1) && get_length(ls.back(), len2) && len1 > len2) {
        unsigned j = ls.size()-1; 
        for (; j > 0 && len1 > len2 && get_length(ls[j-1], len); --j) { 
            len2 += len; 
        }
        if (len1 == len2 && 0 < j && j < ls.size() && reduce_length(ls.size()-j, rs.size()-1, false, ls, rs, deps)) {
            TRACE("seq", tout << "r suffix equal\n";);
            return true;
        }
    }
    return false;
}

bool theory_seq::reduce_length(unsigned i, unsigned j, bool front, expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps) {   
    expr* const* ls1 = ls.data();
    expr* const* ls2 = ls.data()+i;
    expr* const* rs1 = rs.data();
    expr* const* rs2 = rs.data()+j;
    unsigned l1 = i;
    unsigned l2 = ls.size()-i;
    unsigned r1 = j;
    unsigned r2 = rs.size()-j;
    if (!front) {
        std::swap(ls1, ls2);
        std::swap(rs1, rs2);
        std::swap(l1, l2);
        std::swap(r1, r2);        
    }
    SASSERT(0 < l1 && l1 < ls.size());
    SASSERT(0 < r1 && r1 < rs.size());
    expr_ref l = mk_concat(l1, ls1);
    expr_ref r = mk_concat(r1, rs1);
    expr_ref lenl = mk_len(l);
    expr_ref lenr = mk_len(r);
    literal lit = mk_eq(lenl, lenr, false);
    ctx.mark_as_relevant(lit);

    if (ctx.get_assignment(lit) == l_true) {
        expr_ref_vector lhs(m), rhs(m);
        lhs.append(l2, ls2);
        rhs.append(r2, rs2);
        for (auto const& e : m_eqs) {
            if (e.ls == lhs && e.rs == rhs) {
                return false;
            }
        }
        deps = mk_join(deps, lit);                
        m_eqs.push_back(depeq(m_eq_id++, lhs, rhs, deps));
        propagate_eq(deps, l, r, true);
        TRACE("seq", tout << "propagate eq\n" << m_eqs.size() << "\nlhs: " << lhs << "\nrhs: " << rhs << "\n";);
        return true;
    }
    else {
        return false;
    }
}

/**
   Skolem predicates for automata acceptance are stateful. 
   They depend on the shape of automata that were used when the predicates
   were created. It is unsafe to copy assertions about automata from one context
   to another.
*/
bool theory_seq::is_safe_to_copy(bool_var v) const {
    expr* e = ctx.bool_var2expr(v);
    return !m_sk.is_skolem(e);
}

bool theory_seq::get_length(expr* e, expr_ref& len, literal_vector& lits) {
    expr* s, *i, *l;
    rational r;
    if (m_util.str.is_extract(e, s, i, l)) {
        // 0 <= i <= len(s), 0 <= l, i + l <= len(s)       
        expr_ref ls = mk_len(s);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i),l), m);
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:m_ax.mk_ge(i, 0);
        literal i_lt_len_s = ~m_ax.mk_ge(mk_sub(i, ls), 0);
        literal li_ge_ls  = m_ax.mk_ge(ls_minus_i_l, 0);
        literal l_ge_zero = m_ax.mk_ge(l, 0);
        literal _lits[4] = { i_ge_0, i_lt_len_s, li_ge_ls, l_ge_zero };
        if (ctx.get_assignment(i_ge_0) == l_true &&
            ctx.get_assignment(i_lt_len_s) == l_true && 
            ctx.get_assignment(li_ge_ls) == l_true &&
            ctx.get_assignment(l_ge_zero) == l_true) {
            len = l;
            lits.append(4, _lits);
            return true;
        }
        TRACE("seq", tout << mk_pp(e, m) << "\n"; ctx.display_literals_verbose(tout, 4, _lits); tout << "\n";
              for (unsigned i = 0; i < 4; ++i) tout << ctx.get_assignment(_lits[i]) << "\n";);
    }
    else if (m_util.str.is_at(e, s, i)) {
        // has length 1 if 0 <= i < len(s)
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:m_ax.mk_ge(i, 0);
        literal i_lt_len_s = ~m_ax.mk_ge(mk_sub(i, mk_len(s)), 0);
        literal _lits[2] = { i_ge_0, i_lt_len_s};
        if (ctx.get_assignment(i_ge_0) == l_true &&
            ctx.get_assignment(i_lt_len_s) == l_true) {
            len = m_autil.mk_int(1);
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout, 2, _lits); tout << "\n";);
            return true;
        }
    }
    else if (m_sk.is_pre(e, s, i)) {
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:m_ax.mk_ge(i, 0);
        literal i_lt_len_s = ~m_ax.mk_ge(mk_sub(i, mk_len(s)), 0);
        literal _lits[2] = { i_ge_0, i_lt_len_s };
        if (ctx.get_assignment(i_ge_0) == l_true &&
            ctx.get_assignment(i_lt_len_s) == l_true) {
            len = i;
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout << "pre length", 2, _lits); tout << "\n";);
            return true;
        }
    }
    else if (m_sk.is_post(e, s, i)) {
        literal i_ge_0 = m_ax.mk_ge(i, 0);
        literal len_s_ge_i = m_ax.mk_ge(mk_sub(mk_len(s), i), 0);
        literal _lits[2] = { i_ge_0, len_s_ge_i };
        if (ctx.get_assignment(i_ge_0) == l_true && 
            ctx.get_assignment(len_s_ge_i) == l_true) {
            len = mk_sub(mk_len(s), i);
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout << "post length " << len << "\n", 2, _lits) << "\n";);
            return true;
        }
    }
    else if (m_sk.is_tail(e, s, l)) {
        // e = tail(s, l), len(s) > l => len(tail(s, l)) = len(s) - l - 1
        // e = tail(s, l), len(s) <= l => len(tail(s, l)) = 0

        expr_ref len_s = mk_len(s);
        literal len_s_gt_l = m_ax.mk_ge(mk_sub(len_s, l), 1);
        switch (ctx.get_assignment(len_s_gt_l)) {
        case l_true:
            len = mk_sub(mk_sub(len_s, l), m_autil.mk_int(1));
            lits.push_back(len_s_gt_l);
            TRACE("seq", ctx.display_literals_verbose(tout << "tail length " << len << "\n", lits) << "\n";);
            return true;
        case l_false:
            len = m_autil.mk_int(0);
            lits.push_back(~len_s_gt_l);
            TRACE("seq", ctx.display_literals_verbose(tout << "tail length " << len << "\n", lits) << "\n";);
            return true;
        default:
            break;
        }
    }
    else if (m_util.str.is_unit(e)) {
        len = m_autil.mk_int(1);
        return true;
    }
    return false;    
}




bool theory_seq::solve_nc(unsigned idx) {
    nc const& n = m_ncs[idx];
    literal len_gt = n.len_gt();
    expr_ref c(m);
    expr* a = nullptr, *b = nullptr;
    VERIFY(m_util.str.is_contains(n.contains(), a, b));
    literal pre, cnt, ctail, emp;
    lbool is_gt = ctx.get_assignment(len_gt);
    TRACE("seq", ctx.display_literal_smt2(tout << len_gt << " := " << is_gt << "\n", len_gt) << "\n";);
    
    switch (is_gt) {
    case l_true:
        add_length_to_eqc(a);
        add_length_to_eqc(b);
        return true;
    case l_undef:
        ctx.mark_as_relevant(len_gt);
        m_new_propagation = true;
        return false;
    case l_false: 
        break;
    }
    m_ax.unroll_not_contains(n.contains());
    return true;   
}

theory_seq::cell* theory_seq::mk_cell(cell* p, expr* e, dependency* d) {
    cell* c = alloc(cell, p, e, d);
    m_all_cells.push_back(c);
    return c;
}

void theory_seq::unfold(cell* c, ptr_vector<cell>& cons) {
    dependency* dep = nullptr;
    expr* a, *e1, *e2;
    if (m_rep.find1(c->m_expr, a, dep)) {
        cell* c1 = mk_cell(c, a, m_dm.mk_join(dep, c->m_dep));
        unfold(c1, cons);
    }
    else if (m_util.str.is_concat(c->m_expr, e1, e2)) {
        cell* c1 = mk_cell(c, e1, c->m_dep);
        cell* c2 = mk_cell(nullptr, e2, nullptr);
        unfold(c1, cons);
        unfold(c2, cons);
    }
    else {
        cons.push_back(c);
    }
    c->m_last = cons.size()-1;
} 
// 
// a -> a1.a2, a2 -> a3.a4 -> ...
// b -> b1.b2, b2 -> b3.a4 
// 
// e1 
//

void theory_seq::display_explain(std::ostream& out, unsigned indent, expr* e) {
    expr* e1, *e2, *a;
    dependency* dep = nullptr;
    smt2_pp_environment_dbg env(m);
    params_ref p;
    for (unsigned i = 0; i < indent; ++i) out << " ";
    ast_smt2_pp(out, e, env, p, indent);
    out << "\n";

    if (m_rep.find1(e, a, dep)) {
        display_explain(out, indent + 1, a);
    }
    else if (m_util.str.is_concat(e, e1, e2)) {
        display_explain(out, indent + 1, e1);
        display_explain(out, indent + 1, e2);        
    }
}

bool theory_seq::explain_eq(expr* e1, expr* e2, dependency*& dep) {

    if (e1 == e2) {
        return true;
    }
    expr* a1, *a2;
    ptr_vector<cell> v1, v2;
    unsigned cells_sz = m_all_cells.size();
    cell* c1 = mk_cell(nullptr, e1, nullptr);
    cell* c2 = mk_cell(nullptr, e2, nullptr);
    unfold(c1, v1);
    unfold(c2, v2);
    unsigned i = 0, j = 0;
    
    TRACE("seq", 
          tout << "1:\n";
          display_explain(tout, 0, e1);
          tout << "2:\n";
          display_explain(tout, 0, e2););

    bool result = true;
    while (i < v1.size() || j < v2.size()) {
        if (i == v1.size()) {
            while (j < v2.size() && m_util.str.is_empty(v2[j]->m_expr)) {
                dep = m_dm.mk_join(dep, v2[j]->m_dep);
                ++j;
            }
            result = j == v2.size();
            break;
        }
        if (j == v2.size()) {
            while (i < v1.size() && m_util.str.is_empty(v1[i]->m_expr)) {
                dep = m_dm.mk_join(dep, v1[i]->m_dep);
                ++i;
            }
            result = i == v1.size();
            break;
        }
        cell* c1 = v1[i];
        cell* c2 = v2[j];
        e1 = c1->m_expr;
        e2 = c2->m_expr;
        if (e1 == e2) {
            if (c1->m_parent && c2->m_parent && 
                c1->m_parent->m_expr == c2->m_parent->m_expr) {
                TRACE("seq", tout << "parent: " << mk_pp(e1, m) << " " << mk_pp(c1->m_parent->m_expr, m) << "\n";);
                c1 = c1->m_parent;
                c2 = c2->m_parent;
                v1[c1->m_last] = c1;
                i = c1->m_last;
                v2[c2->m_last] = c2;
                j = c2->m_last;
            }
            else {
                dep = m_dm.mk_join(dep, c1->m_dep);
                dep = m_dm.mk_join(dep, c2->m_dep);
                ++i;
                ++j;
            }
        }
        else if (m_util.str.is_empty(e1)) {
            dep = m_dm.mk_join(dep, c1->m_dep);
            ++i;
        }
        else if (m_util.str.is_empty(e2)) {
            dep = m_dm.mk_join(dep, c2->m_dep);
            ++j;
        }
        else if (m_util.str.is_unit(e1, a1) &&
                 m_util.str.is_unit(e2, a2)) {
            if (explain_eq(a1, a2, dep)) {
                ++i;
                ++j;
            }
            else {
                result = false;
                break;
            }
        }
        else {
            TRACE("seq", tout << "Could not solve " << mk_pp(e1, m) << " = " << mk_pp(e2, m) << "\n";);
            result = false;
            break;
        }
    }   
    m_all_cells.resize(cells_sz);
    return result;
    
}

bool theory_seq::explain_empty(expr_ref_vector& es, dependency*& dep) {
    while (!es.empty()) {
        expr* e = es.back();
        if (m_util.str.is_empty(e)) {
            es.pop_back();
            continue;
        }
        expr* a;
        if (m_rep.find1(e, a, dep)) {
            es.pop_back();
            m_util.str.get_concat_units(a, es);
            continue;
        }
        TRACE("seq", tout << "Could not set to empty: " << es << "\n";);
        return false;
    }
    return true;
}

bool theory_seq::simplify_and_solve_eqs() {
    m_new_solution = true;
    while (m_new_solution && !ctx.inconsistent()) {
        m_new_solution = false;
        solve_eqs(0);
    }
    return m_new_propagation || ctx.inconsistent();
}

void theory_seq::internalize_eq_eh(app * atom, bool_var v) {
}

bool theory_seq::internalize_atom(app* a, bool) {
    return internalize_term(a);
}

bool theory_seq::internalize_term(app* term) {
    m_has_seq = true;

    if (m_util.str.is_in_re(term)) 
        mk_var(ensure_enode(term->get_arg(0)));

    if (m_util.str.is_length(term))
        mk_var(ensure_enode(term->get_arg(0)));
    
    if (ctx.e_internalized(term)) {
        mk_var(ctx.get_enode(term));
        return true;
    }    

    if (m.is_bool(term) && 
        (m_util.str.is_in_re(term) || m_sk.is_skolem(term))) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        return true;
    }

    for (auto arg : *term)         
        mk_var(ensure_enode(arg));

    if (m.is_bool(term)) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
    }

    enode* e = nullptr;
    if (ctx.e_internalized(term)) {
        e = ctx.get_enode(term);
    }
    else {
        e = ctx.mk_enode(term, false, m.is_bool(term), true);
    }
    mk_var(e);
    if (!ctx.relevancy()) {
        relevant_eh(term);
    }

    
    return true;
}

void theory_seq::add_length(expr* l) {
    expr* e = nullptr;
    VERIFY(m_util.str.is_length(l, e));
    if (has_length(e))
        return;
    TRACE("seq", tout << mk_bounded_pp(e, m, 2) << "\n";);
    m_length.push_back(l);
    m_has_length.insert(e);
    m_trail_stack.push(insert_obj_trail<expr>(m_has_length, e));
    m_trail_stack.push(push_back_vector<expr_ref_vector>(m_length));
}

/**
   Add length limit restrictions to sequence s.
 */
void theory_seq::add_length_limit(expr* s, unsigned k, bool is_searching) {
    if (m_sk.is_indexof_left(s))
        return;
    if (m_sk.is_indexof_right(s))
        return;
    expr_ref lim_e = m_ax.add_length_limit(s, k);
    unsigned k0 = 0;
    if (m_length_limit_map.find(s, k0)) {
        SASSERT(k0 != 0);
        if (k <= k0)
            return;
    }
    m_length_limit_map.insert(s, k);
    m_length_limit.push_back(lim_e);    
    m_trail_stack.push(push_back_vector<expr_ref_vector>(m_length_limit));    
    if (k0 != 0) {
        m_trail_stack.push(remove_obj_map<expr, unsigned>(m_length_limit_map, s, k0));
    }
    m_trail_stack.push(insert_obj_map<expr, unsigned>(m_length_limit_map, s));
    if (is_searching) {
        expr_ref dlimit = m_sk.mk_max_unfolding_depth(m_max_unfolding_depth);
        add_axiom(~mk_literal(dlimit), mk_literal(lim_e));
    }
}


/*
  ensure that all elements in equivalence class occur under an application of 'length'
*/
bool theory_seq::add_length_to_eqc(expr* e) {
    enode* n = ensure_enode(e);
    enode* n1 = n;
    bool change = false;
    do {
        expr* o = n->get_expr();
        if (!has_length(o)) {
            expr_ref len(m_util.str.mk_length(o), m);
            ensure_enode(len);
            add_length(len);
            change = true;
        }
        n = n->get_next();
    }
    while (n1 != n);
    return change;
}

void theory_seq::add_ubv_string(expr* e) {
    bool has_sort = false;
    expr* b = nullptr;
    VERIFY(m_util.str.is_ubv2s(e, b));
    for (auto* e2 : m_ubv_string) {
        expr* b2 = nullptr;
        VERIFY(m_util.str.is_ubv2s(e2, b2));
        has_sort |= b2->get_sort() == b->get_sort();
    }
    if (!has_sort)
        m_ax.add_ubv2ch_axioms(b->get_sort());
    m_ubv_string.push_back(e);
    m_trail_stack.push(push_back_vector<expr_ref_vector>(m_ubv_string));
    add_length_to_eqc(e);
}

bool theory_seq::check_ubv_string() {
    bool change = false;
    for (expr* e : m_ubv_string) {
        if (check_ubv_string(e))
            change = true;
    }
    return change;
}

bool theory_seq::check_ubv_string(expr* e) {
    expr* n = nullptr;
    if (ctx.inconsistent())
        return true;
    if (m_has_ubv_axiom.contains(e))
        return false;
    expr* b = nullptr;
    bv_util bv(m);
    VERIFY(m_util.str.is_ubv2s(e, b));
    rational len;
    if (get_length(e, len) && len.is_unsigned()) 
        m_ax.add_ubv2s_len_axiom(b, len.get_unsigned());
    

    unsigned sz = bv.get_bv_size(b);
    rational value(0);
    bool all_bits_assigned = true;
    for (unsigned i = 0; i < sz; ++i) {
        expr_ref bit(bv.mk_bit2bool(b, i), m);
        literal lit = mk_literal(bit);
        switch (ctx.get_assignment(lit)) {
        case l_undef:
            ctx.mark_as_relevant(lit);
            all_bits_assigned = false;
            break;
        case l_true:
            value += rational::power_of_two(i);
            break;
        case l_false:
            break;
        }
    }
    if (!all_bits_assigned)
        return true;
    unsigned k = 0;
    while (value >= 10) {
        k++;
        value = div(value, rational(10));
    }

    m_has_ubv_axiom.insert(e);
    m_trail_stack.push(insert_obj_trail<expr>(m_has_ubv_axiom, e));
    m_ax.add_ubv2s_axiom(b, k);
    return true;
}

void theory_seq::add_int_string(expr* e) {
    m_int_string.push_back(e);
    m_trail_stack.push(push_back_vector<expr_ref_vector>(m_int_string));
}

bool theory_seq::check_int_string() {
    bool change = false;
    for (expr * e : m_int_string) {
        if (check_int_string(e))
            change = true;
    }
    return change;
}

bool theory_seq::check_int_string(expr* e) {
    expr* n = nullptr;
    if (ctx.inconsistent())
        return true;    
    if (m_util.str.is_itos(e, n) && !m_util.str.is_stoi(n) && add_length_to_eqc(e))
        return true;
    if (m_util.str.is_stoi(e, n) && !m_util.str.is_itos(n) && add_length_to_eqc(n))
        return true;

    return false;
}

bool theory_seq::branch_itos() {
    bool change = false;
    for (expr * e : m_int_string) {
        if (branch_itos(e))
            change = true;
    }
    return change;
}

bool theory_seq::branch_itos(expr* e) {
    expr* n = nullptr;
    rational val;
    if (ctx.inconsistent())
        return true;
    if (!m_util.str.is_itos(e, n))
        return false;
    if (!ctx.e_internalized(e))
        return false;
    enode* r = ctx.get_enode(e)->get_root();
    if (m_util.str.is_string(r->get_expr()))
        return false;
    if (!get_num_value(n, val))
        return false;
    if (val.is_neg())
        return false;    
    literal b = mk_eq(e, m_util.str.mk_string(val.to_string()), false);
    if (ctx.get_assignment(b) == l_true)
        return false;
    if (ctx.get_assignment(b) == l_false) {
        literal a = mk_eq(n, m_autil.mk_int(val), false);
        add_axiom(~a, b);
    }
    else {
        ctx.force_phase(b);
        ctx.mark_as_relevant(b);
    }
    return true;
}



void theory_seq::apply_sort_cnstr(enode* n, sort* s) {
    mk_var(n);
}

void theory_seq::display(std::ostream & out) const {
    if (m_eqs.empty() &&
        m_nqs.empty() &&
        m_rep.empty() &&
        m_exclude.empty()) {
        return;
    }
    out << "Theory seq\n";
    if (!m_eqs.empty()) {
        out << "Equations:\n";
        display_equations(out);
    }
    if (!m_nqs.empty()) {
        display_disequations(out);
    }
    if (!m_rep.empty()) {
        out << "Solved equations:\n";
        m_rep.display(out);
    }
    if (!m_exclude.empty()) {
        out << "Exclusions:\n";
        m_exclude.display(out);
    }

    for (auto e : m_length) {
        rational lo(-1), hi(-1);
        lower_bound(e, lo);
        upper_bound(e, hi);
        if (lo.is_pos() || !hi.is_minus_one()) {
            out << mk_bounded_pp(e, m, 3) << " [" << lo << ":" << hi << "]\n";
        }
    }

    if (!m_ncs.empty()) {
        out << "Non contains:\n";
        for (auto const& nc : m_ncs) {
            display_nc(out, nc);
        }
    }

}

std::ostream& theory_seq::display_nc(std::ostream& out, nc const& nc) const {
    out << "not " << mk_bounded_pp(nc.contains(), m, 2) << "\n";
    display_deps(out << "  <- ", nc.deps()) << "\n";
    return out;
}

std::ostream& theory_seq::display_equations(std::ostream& out) const {
    for (auto const& e : m_eqs) {
        display_equation(out, e);
    }
    return out;
}

std::ostream& theory_seq::display_equation(std::ostream& out, depeq const& e) const {
    bool first = true;
    for (expr* a : e.ls) { if (first) first = false; else out << "\n"; out << mk_bounded_pp(a, m, 2); }
    out << " = ";
    for (expr* a : e.rs) { if (first) first = false; else out << "\n"; out << mk_bounded_pp(a, m, 2); }
    out << " <- \n";
    return display_deps(out, e.dep());    
}

std::ostream& theory_seq::display_disequations(std::ostream& out) const {
    bool first = true;
    for (ne const& n : m_nqs) {
        if (first) out << "Disequations:\n";
        first = false;
        display_disequation(out, n);
    }
    return out;
}

std::ostream& theory_seq::display_disequation(std::ostream& out, ne const& e) const {
    for (literal lit : e.lits()) {
        out << lit << " ";
    }
    if (!e.lits().empty()) {
        out << "\n";
    }
    for (unsigned j = 0; j < e.eqs().size(); ++j) {
        for (expr* t : e[j].first) {
            out << mk_bounded_pp(t, m, 2) << " ";
        }
        out << " != ";
        for (expr* t : e[j].second) {
            out << mk_bounded_pp(t, m, 2) << " ";
        }
        out << "\n";
    }
    if (e.dep()) {
        display_deps(out, e.dep());
    }
    return out;
}

std::ostream& theory_seq::display_deps(std::ostream& out, literal_vector const& lits, enode_pair_vector const& eqs) const {
    smt2_pp_environment_dbg env(m);
    params_ref p;
    for (auto const& eq : eqs) {
        if (eq.first->get_root() != eq.second->get_root())
            out << "invalid: ";
        out << "  (= " << mk_bounded_pp(eq.first->get_expr(), m, 2)
            << "\n     " << mk_bounded_pp(eq.second->get_expr(), m, 2) 
            << ")\n";        
    }
    for (literal l : lits) {
        display_lit(out, l) << "\n";
    }
    return out;
}

std::ostream& theory_seq::display_deps_smt2(std::ostream& out, literal_vector const& lits, enode_pair_vector const& eqs) const {
    params_ref p;
    for (auto const& eq : eqs) {
        out << "  (= " << pp(eq.first, m)
            << "\n     " << pp(eq.second, m) 
            << ")\n";
    }
    for (literal l : lits) {
        ctx.display_literal_smt2(out, l) << "\n";
    }
    return out;
}

std::ostream& theory_seq::display_lit(std::ostream& out, literal l) const {
    if (l == true_literal) {
        out << "   true";
    }
    else if (l == false_literal) {
        out << "   false";
    }
    else {
        expr* e = ctx.bool_var2expr(l.var());
        if (l.sign()) {
            out << "  (not " << mk_bounded_pp(e, m) << ")";
        }
        else {
            out << "  " << mk_bounded_pp(e, m);
        }
    }
    return out;
}

std::ostream& theory_seq::display_deps(std::ostream& out, dependency* dep) const {
    literal_vector lits;
    enode_pair_vector eqs;
    linearize(dep, eqs, lits);
    display_deps(out, lits, eqs);
    return out;
}

void theory_seq::collect_statistics(::statistics & st) const {
    st.update("seq num splits", m_stats.m_num_splits);
    st.update("seq num reductions", m_stats.m_num_reductions);
    st.update("seq length coherence", m_stats.m_check_length_coherence);
    st.update("seq branch", m_stats.m_branch_variable);
    st.update("seq solve !=", m_stats.m_solve_nqs);
    st.update("seq solve =", m_stats.m_solve_eqs);
    st.update("seq branch !=", m_stats.m_branch_nqs);
    st.update("seq add axiom", m_stats.m_add_axiom);
    st.update("seq extensionality", m_stats.m_extensionality);
    st.update("seq fixed length", m_stats.m_fixed_length);
    st.update("seq int.to.str", m_stats.m_int_string);
    st.update("seq str.from_ubv", m_stats.m_ubv_string);
}

void theory_seq::init_search_eh() {
    auto as = get_fparams().m_arith_mode;
    if (m_has_seq && as != arith_solver_id::AS_OLD_ARITH && as != arith_solver_id::AS_NEW_ARITH) {
        throw default_exception("illegal arithmetic solver used with string solver");
    }
}

void theory_seq::init_model(expr_ref_vector const& es) {
    expr_ref new_s(m);
    for (auto e : es) {
        dependency* eqs = nullptr;
        expr_ref s(m);
        if (!canonize(e, eqs, s)) s = e;
        if (is_var(s)) {
            new_s = m_factory->get_fresh_value(s->get_sort());
            m_rep.update(s, new_s, eqs);
        }
    }
}

void theory_seq::finalize_model(model_generator& mg) {
    m_rep.pop_scope(1);
}

void theory_seq::init_model(model_generator & mg) {
    m_rep.push_scope();
    m_factory = alloc(seq_factory, get_manager(), get_family_id(), mg.get_model());
    mg.register_factory(m_factory);
    for (ne const& n : m_nqs) {
        m_factory->register_value(n.l());
        m_factory->register_value(n.r());  
    }
    for (ne const& n : m_nqs) {
        for (unsigned i = 0; i < n.eqs().size(); ++i) {
            init_model(n[i].first);
            init_model(n[i].second);
        }
    }
}

class theory_seq::seq_value_proc : public model_value_proc {
    enum source_t { unit_source, int_source, string_source };
    theory_seq&                     th;
    enode*                          m_node;
    sort*                           m_sort;
    svector<model_value_dependency> m_dependencies;
    ptr_vector<expr>                m_strings;
    svector<source_t>               m_source;
public:
    seq_value_proc(theory_seq& th, enode* n, sort* s): th(th), m_node(n), m_sort(s) {
        (void)m_node;
    }
    ~seq_value_proc() override {}
    void add_unit(enode* n) { 
        m_dependencies.push_back(model_value_dependency(n)); 
        m_source.push_back(unit_source);
    }
    void add_int(enode* n) { 
        m_dependencies.push_back(model_value_dependency(n)); 
        m_source.push_back(int_source);
    }
    void add_string(expr* n) {
        m_strings.push_back(n);
        m_source.push_back(string_source);
    }
    void get_dependencies(buffer<model_value_dependency> & result) override {
        result.append(m_dependencies.size(), m_dependencies.data());
    }

    void add_buffer(svector<unsigned>& sbuffer, zstring const& zs) {
        for (unsigned i = 0; i < zs.length(); ++i) {
            sbuffer.push_back(zs[i]);
        }
    }

    app * mk_value(model_generator & mg, expr_ref_vector const & values) override {
        SASSERT(values.size() == m_dependencies.size());
        expr_ref_vector args(th.m);
        unsigned j = 0, k = 0;
        rational val;
        bool is_string = th.m_util.is_string(m_sort);
        expr_ref result(th.m);

        if (is_string) {
            unsigned_vector sbuffer;
            unsigned ch;
            for (source_t src : m_source) {
                switch (src) {
                case unit_source: {
                    VERIFY(th.m_util.is_const_char(values[j++], ch));
                    sbuffer.push_back(ch);
                    break;
                }
                case string_source: {
                    dependency* deps = nullptr;
                    expr_ref tmp(th.m);
                    if (!th.canonize(m_strings[k], deps, tmp)) tmp = m_strings[k];
                    th.m_str_rewrite(tmp);
                    zstring zs;
                    if (th.m_util.str.is_string(tmp, zs)) {
                        add_buffer(sbuffer, zs);
                    }
                    else {
                        TRACE("seq", tout << "Not a string: " << tmp << "\n";);
                    }
                    ++k;
                    break;
                }
                case int_source: {
                    std::ostringstream strm;
                    arith_util arith(th.m);
                    VERIFY(arith.is_numeral(values[j++], val));
                    
                    if (val.is_neg()) {
                        strm << "";
                    }
                    else {
                        strm << val;
                    }
                    zstring zs(strm.str());
                    add_buffer(sbuffer, zs);
                    break;
                }
                }
                // TRACE("seq", tout << src << " " << sbuffer << "\n";);
            }
            result = th.m_util.str.mk_string(zstring(sbuffer.size(), sbuffer.data()));
        }
        else {
            for (source_t src : m_source) {
                switch (src) {
                case unit_source:                    
                    args.push_back(th.m_util.str.mk_unit(values[j++]));
                    break;
                case string_source:
                    args.push_back(m_strings[k++]);
                    break;
                case int_source:
                    UNREACHABLE();
                    break;
                }
            }
            result = th.mk_concat(args, m_sort);
            th.m_str_rewrite(result);
        }
        th.m_factory->add_trail(result);
        TRACE("seq", tout << pp(m_node, th.m) << " -> " << result << "\n";);
        return to_app(result);
    }
};

app* theory_seq::get_ite_value(expr* e) {
    expr* e1, *e2, *e3;
    while (m.is_ite(e, e1, e2, e3)) {        
        if (!ctx.e_internalized(e))
            break;
        enode* r = ctx.get_enode(e)->get_root();
        if (ctx.get_enode(e2)->get_root() == r) {
            e = e2;
        }
        else if (ctx.get_enode(e3)->get_root() == r) {
            e = e3;
        }
        else {
            break;
        }
    }
    return to_app(e);
}

model_value_proc * theory_seq::mk_value(enode * n, model_generator & mg) {
    app* e = n->get_expr();
    TRACE("seq", tout << mk_pp(e, m) << "\n";);

    // Shortcut for well-founded values to avoid some quadratic overhead
    expr* x = nullptr, *y = nullptr, *z = nullptr;
    if (false && m_util.str.is_concat(e, x, y) && m_util.str.is_unit(x, z) && 
        ctx.e_internalized(z) && ctx.e_internalized(y)) {
        sort* srt = e->get_sort();
        seq_value_proc* sv = alloc(seq_value_proc, *this, n, srt);
        sv->add_unit(ctx.get_enode(z));
        sv->add_string(y);
        return sv;
    }
    e = get_ite_value(e);    
    if (m_util.is_seq(e)) {
        unsigned start = m_concat.size();
        SASSERT(m_todo.empty());
        m_todo.push_back(e);
        get_ite_concat(m_concat, m_todo);
        sort* srt = e->get_sort();
        seq_value_proc* sv = alloc(seq_value_proc, *this, n, srt);
       
        unsigned end = m_concat.size();
        TRACE("seq", tout << "sequence: " << start << " " << end << " " << mk_pp(e, m) << "\n";);
        for (unsigned i = start; i < end; ++i) {
            expr* c = m_concat[i];
            expr *c1;
            TRACE("seq", tout << "elem: " << mk_pp(c, m) << "\n";);
            if (m_util.str.is_unit(c, c1)) {
                if (ctx.e_internalized(c1)) 
                    sv->add_unit(ctx.get_enode(c1));
                else if (m.is_value(c1))
                    sv->add_string(c);
                else {
                    TRACE("seq", tout << "not internalized " << mk_pp(c, m) << "\n";);
                }
            }
            else if (m_util.str.is_itos(c, c1)) {
                if (ctx.e_internalized(c1)) {
                    sv->add_int(ctx.get_enode(c1));
                }
            }
            else if (m_util.str.is_string(c)) {
                sv->add_string(c);
            }
            else {
                app_ref val(mk_value(to_app(c)), m);
                TRACE("seq", tout << "WARNING: " << val << " is prone to result in incorrect model\n";);
                sv->add_string(val);
            }
        }
        m_concat.shrink(start);        
        return sv;
    }
    else {
        return alloc(expr_wrapper_proc, mk_value(e));
    }
}


app* theory_seq::mk_value(app* e) {
    expr_ref result(m);
    e = get_ite_value(e);
    result = m_rep.find(e);

    if (is_var(result)) {
        SASSERT(m_factory);
        expr_ref val(m);
        val = m_factory->get_fresh_value(result->get_sort());
        if (val) {
            result = val;
        }
    }
    else {
        m_rewrite(result);
    }
    m_factory->add_trail(result);
    TRACE("seq", tout << mk_pp(e, m) << " -> " << result << "\n";);
    m_rep.update(e, result, nullptr);
    return to_app(result);
}


void theory_seq::validate_model(model& mdl) {
    return;
    for (auto const& eq : m_eqs) {
        sort* srt = eq.ls[0]->get_sort();
        expr_ref l(m_util.str.mk_concat(eq.ls, srt), m);
        expr_ref r(m_util.str.mk_concat(eq.rs, srt), m);
        if (!mdl.are_equal(l, r)) {
            IF_VERBOSE(0, verbose_stream() << "equality failed: " << l << " = " << r << "\nbut\n" << mdl(l) << " != " << mdl(r) << "\n");
        }
    }
    for (auto const& ne : m_nqs) {
        expr_ref l = ne.l();
        expr_ref r = ne.r();
        if (mdl.are_equal(l, r)) {
            IF_VERBOSE(0, verbose_stream() << "disequality failed: " << l << " != " << r << "\n" << mdl(l) << "\n" << mdl(r) << "\n");
        }
    }

    for (auto const& ex : m_exclude) {
        expr_ref l(ex.first, m);
        expr_ref r(ex.second, m);
        if (mdl.are_equal(l, r)) {
            IF_VERBOSE(0, verbose_stream() << "exclude " << l << " = " << r << " = " << mdl(l) << "\n");
        }
    }

    for (auto const& nc : m_ncs) {
        expr_ref p = nc.contains();
        if (!mdl.is_false(p)) {
            IF_VERBOSE(0, verbose_stream() << p << " evaluates to " << mdl(p) << "\n");
        }
    }

#if 0
    // to enable this check need to add m_util.str.is_skolem(f); to theory_seq::include_func_interp
    for (auto const& kv : m_rep) {
        expr_ref l(kv.m_key, m);
        expr_ref r(kv.m_value.first, m);

        if (!mdl.are_equal(l, r)) {
            enode* ln = ensure_enode(l);
            enode* rn = ensure_enode(r);
            IF_VERBOSE(0, verbose_stream() << "bad representation: " << l << " ->\n" << r << "\nbut\n" 
                       << mdl(l) << "\n->\n" << mdl(r) << "\n"
                       << "nodes: #" << ln->get_expr_id() << " #" << rn->get_expr_id() << "\n"
                       << "roots: #" << ln->get_root()->get_expr_id() << " #" << rn->get_root()->get_expr_id() << "\n";
                       );
        }
    }
#endif

#if 0
    ptr_vector<expr> fmls;
    ctx.get_asserted_formulas(fmls);
    validate_model_proc proc(*this, mdl);
    for (expr* f : fmls) {
        for_each_expr(proc, f);
    }
#endif
}

expr_ref theory_seq::elim_skolem(expr* e) {
    expr_ref result(m);
    expr_ref_vector trail(m), args(m);
    obj_map<expr, expr*> cache;
    ptr_vector<expr> todo;
    todo.push_back(e);
    expr* x = nullptr, *y = nullptr, *b = nullptr;
    while (!todo.empty()) {
        expr* a = todo.back();
        if (cache.contains(a)) {
            todo.pop_back();
            continue;
        }
        if (!is_app(a)) {
            cache.insert(a, a);
            todo.pop_back();
            continue;
        }
        if (m_sk.is_eq(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            result = m.mk_eq(x, y);
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;
        }
        if (m_sk.is_pre(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            result = m_util.str.mk_substr(x, m_autil.mk_int(0), y);
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;
        }
        if (m_sk.is_post(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            result = m_util.str.mk_length(x);
            result = m_util.str.mk_substr(x, y, m_autil.mk_sub(result, y));
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();            
            continue;
        }
        if (m_sk.is_tail(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            expr_ref y1(m_autil.mk_add(y, m_autil.mk_int(1)), m);
            expr_ref z(m_autil.mk_sub(m_util.str.mk_length(x), y1), m);
            result = m_util.str.mk_substr(x, y1, z);
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();            
            continue;
        }
        if (m_util.str.is_nth_i(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            result = m_util.str.mk_nth(x, y);
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();            
            continue;
        }
        if (m_sk.is_unit_inv(a, x) && cache.contains(x) && m_util.str.is_unit(cache[x], y)) {
            result = y;
            cache.insert(a, result);
            todo.pop_back();
            continue;            
        }
        if (m_sk.is_first(a, x) && cache.contains(x)) {
            x = cache[x];
            result = m_util.str.mk_substr(x, m_autil.mk_int(0), m_autil.mk_sub(m_util.str.mk_length(x), m_autil.mk_int(1)));
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;            
        }
        if (m_sk.is_last(a, x) && cache.contains(x)) {
            x = cache[x];
            result = m_util.str.mk_nth(x, m_autil.mk_sub(m_util.str.mk_length(x), m_autil.mk_int(1)));
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;            
        }
        if (m_sk.is_indexof_left(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            result = m_util.str.mk_substr(x, m_autil.mk_int(0), m_util.str.mk_index(x, y, m_autil.mk_int(0)));
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;                        
        }
        if (m_sk.is_indexof_right(a, x, y) && cache.contains(x) && cache.contains(y)) {
            x = cache[x];
            y = cache[y];
            expr_ref offset(m_autil.mk_add(m_util.str.mk_length(y), m_util.str.mk_index(x, y, m_autil.mk_int(0))), m);
            result = m_util.str.mk_substr(x, offset, m_util.str.mk_length(x));
            trail.push_back(result);
            cache.insert(a, result);
            todo.pop_back();
            continue;                        
        }

        args.reset();
        for (expr* arg : *to_app(a)) {
            if (cache.find(arg, b)) {
                args.push_back(b);
            }
            else {
                todo.push_back(arg);
            }
        }
        if (args.size() < to_app(a)->get_num_args()) {
            continue;
        }

        if (m_util.is_skolem(a)) {
            IF_VERBOSE(0, verbose_stream() << "unhandled skolem " << mk_pp(a, m) << "\n");
            return expr_ref(m.mk_false(), m);
        }

        todo.pop_back();
        result = m.mk_app(to_app(a)->get_decl(), args);
        trail.push_back(result);
        cache.insert(a, result);                
    }
    return expr_ref(cache[e], m);
}

void theory_seq::validate_axiom(literal_vector const& lits) {
    if (get_fparams().m_seq_validate) {
        enode_pair_vector eqs;
        literal_vector _lits;
        for (literal lit : lits) _lits.push_back(~lit);
        expr_ref_vector fmls(m);
        validate_fmls(eqs, _lits, fmls);
    }
}

void theory_seq::validate_conflict(enode_pair_vector const& eqs, literal_vector const& lits) {
    IF_VERBOSE(10, display_deps_smt2(verbose_stream() << "cn ", lits, eqs));
    if (get_fparams().m_seq_validate) {
        expr_ref_vector fmls(m);
        validate_fmls(eqs, lits, fmls);
    }
}

void theory_seq::validate_assign(literal lit, enode_pair_vector const& eqs, literal_vector const& lits) {
    IF_VERBOSE(10, display_deps_smt2(verbose_stream() << "eq ", lits, eqs); display_lit(verbose_stream(), ~lit) << "\n");
    if (get_fparams().m_seq_validate) {
        literal_vector _lits(lits);
        _lits.push_back(~lit);
        expr_ref_vector fmls(m);
        validate_fmls(eqs, _lits, fmls);
    }
}

void theory_seq::validate_assign_eq(enode* a, enode* b, enode_pair_vector const& eqs, literal_vector const& lits) {
    IF_VERBOSE(10, display_deps(verbose_stream() << "; assign-eq\n", lits, eqs);
               verbose_stream() << "(not (= " << mk_bounded_pp(a->get_expr(), m) 
               << " " << mk_bounded_pp(b->get_expr(), m) << "))\n");  
    if (get_fparams().m_seq_validate) {
        expr_ref_vector fmls(m);
        fmls.push_back(m.mk_not(m.mk_eq(a->get_expr(), b->get_expr())));
        validate_fmls(eqs, lits, fmls);
    }
}

void theory_seq::validate_fmls(enode_pair_vector const& eqs, literal_vector const& lits, expr_ref_vector& fmls) {
    smt_params fp;
    fp.m_seq_validate = false;
    fp.m_max_conflicts = 100;
    expr_ref fml(m);
    kernel k(m, fp);
    for (literal lit : lits) {
        ctx.literal2expr(lit, fml);
        fmls.push_back(fml);
    }
    for (auto const& p : eqs) {
        fmls.push_back(m.mk_eq(p.first->get_expr(), p.second->get_expr()));
    }
    TRACE("seq", tout << fmls << "\n";);

    for (unsigned i = 0; i < fmls.size(); ++i) {
        fml = elim_skolem(fmls.get(i));
        fmls[i] = fml;
    }

    for (expr* f : fmls) {
        k.assert_expr(f);
    }
    lbool r = k.check();
    if (r == l_true) {
        model_ref mdl;
        k.get_model(mdl);
        IF_VERBOSE(0, 
                   verbose_stream() << r << "\n" << fmls << "\n";
                   verbose_stream() << *mdl.get() << "\n";
                   k.display(verbose_stream()));
        UNREACHABLE();
    }

}

theory_var theory_seq::mk_var(enode* n) {
    expr* o = n->get_expr();

    if (!m_util.is_seq(o) && !m_util.is_re(o))
        return null_theory_var;

    if (is_attached_to_var(n)) 
        return n->get_th_var(get_id());

    theory_var v = theory::mk_var(n);
    m_find.mk_var();
    ctx.attach_th_var(n, this, v);
    ctx.mark_as_relevant(n);
    return v;    
}

bool theory_seq::can_propagate() {
    return m_axioms_head < m_axioms.size() || !m_replay.empty() || m_new_solution || m_regex.can_propagate();
}

bool theory_seq::canonize(expr* e, dependency*& eqs, expr_ref& result) {
    if (!expand(e, eqs, result)) {
        return false;
    }
    TRACE("seq", tout << mk_bounded_pp(e, m, 2) << " expands to\n" << mk_bounded_pp(result, m, 2) << "\n";);
    m_rewrite(result);
    TRACE("seq", tout << mk_bounded_pp(e, m, 2) << " rewrites to\n" << mk_bounded_pp(result, m, 2) << "\n";);
    return true;
}

bool theory_seq::canonize(expr* e, expr_ref_vector& es, dependency*& eqs, bool& change) {
    expr* e1, *e2;
    expr_ref e3(e, m);
    while (true) {
        if (m_util.str.is_concat(e3, e1, e2)) {
            if (!canonize(e1, es, eqs, change)) {
                return false;
            }
            e3 = e2;
            change = true;
        }
        else if (m_util.str.is_empty(e3)) {
            change = true;
            break;
        }
        else {
            expr_ref e4(m);
            if (!expand(e3, eqs, e4)) {
                return false;
            }
            change |= e4 != e3;
            m_util.str.get_concat(e4, es);
            break;
        }
    }
    return true;
}

bool theory_seq::canonize(expr_ref_vector const& es, expr_ref_vector& result, dependency*& eqs, bool& change) {
    for (expr* e : es) {
        if (!canonize(e, result, eqs, change)) 
            return false;
        SASSERT(!m_util.str.is_concat(e) || change);
    }
    return true;
}

bool theory_seq::expand(expr* e, dependency*& eqs, expr_ref& result) {
    unsigned sz = m_expand_todo.size();
    m_expand_todo.push_back(e);
    while (m_expand_todo.size() != sz) {
        expr* e = m_expand_todo.back();
        bool r = expand1(e, eqs, result);
        if (!r) {
            return false; 
        }
        if (result) {
            SASSERT(m_expand_todo.back() == e);
            m_expand_todo.pop_back();
        }
    }
    return true;
}
 
expr_ref theory_seq::try_expand(expr* e, dependency*& eqs){
    expr_ref result(m);
    expr_dep ed;
    if (m_rep.find_cache(e, ed)) {
        if (e != ed.e) {
            eqs = m_dm.mk_join(eqs, ed.d);
        }
        result = ed.e;
    }
    else {
        m_expand_todo.push_back(e);
    }
    return result;
}
bool theory_seq::expand1(expr* e0, dependency*& eqs, expr_ref& result) {
    result = try_expand(e0, eqs);
    if (result) {
        return true;
    }
    dependency* deps = nullptr;
    expr* e = m_rep.find(e0, deps);

    expr* e1, *e2, *e3;
    expr_ref arg1(m), arg2(m);
    if (m_util.str.is_concat(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = mk_concat(arg1, arg2);
    }
    else if (m_util.str.is_empty(e) || m_util.str.is_string(e)) {
        result = e;
    }    
    else if (m_util.str.is_prefix(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = m_util.str.mk_prefix(arg1, arg2);
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = m_util.str.mk_suffix(arg1, arg2);
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;        
        result = m_util.str.mk_contains(arg1, arg2);
    }
    else if (m_util.str.is_unit(e, e1)) {
        arg1 = try_expand(e1, deps);
        if (!arg1) return true;
        result = m_util.str.mk_unit(arg1);
    }
    else if (m_util.str.is_index(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = m_util.str.mk_index(arg1, arg2, m_autil.mk_int(0));
    }
    else if (m_util.str.is_index(e, e1, e2, e3)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = m_util.str.mk_index(arg1, arg2, e3);
    }
#if 0
    else if (m_util.str.is_nth_i(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        if (!arg1) return true;
        result = m_util.str.mk_nth_i(arg1, e2);
        // m_rewrite(result);
    }
#endif
    else if (m_util.str.is_last_index(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return true;
        result = m_util.str.mk_last_index(arg1, arg2);
    }
    else if (m.is_ite(e, e1, e2, e3)) {
        literal lit(mk_literal(e1));
        switch (ctx.get_assignment(lit)) {
        case l_true:
            deps = m_dm.mk_join(deps, m_dm.mk_leaf(assumption(lit)));
            result = try_expand(e2, deps);
            if (!result) return true;
            break;
        case l_false:
            deps = m_dm.mk_join(deps, m_dm.mk_leaf(assumption(~lit)));
            result = try_expand(e3, deps);
            if (!result) return true;
            break;
        case l_undef:
            ctx.mark_as_relevant(lit);
            m_new_propagation = true;
            TRACE("seq", tout << "undef: " << mk_bounded_pp(e, m, 2) << "\n";
                  tout << lit << "@ level: " << ctx.get_scope_level() << "\n";);
            return false;
        }
    }
    else {
        result = e;
    }
    if (result == e0) {
        deps = nullptr;
    }
    expr_dep edr(e0, result, deps);
    m_rep.add_cache(edr);
    eqs = m_dm.mk_join(eqs, deps);
    TRACE("seq_verbose", tout << mk_pp(e0, m) << " |--> " << result << "\n";
          if (eqs) display_deps(tout, eqs););
    return true;
}

void theory_seq::add_dependency(dependency*& dep, enode* a, enode* b) {
    if (a != b) {
        dep = m_dm.mk_join(dep, m_dm.mk_leaf(assumption(a, b)));
    }
}


void theory_seq::propagate() {
    if (m_regex.can_propagate())
        m_regex.propagate();
    while (m_axioms_head < m_axioms.size() && !ctx.inconsistent()) {
        expr_ref e(m);
        e = m_axioms.get(m_axioms_head);
        deque_axiom(e);
        ++m_axioms_head;
    }
    while (!m_replay.empty() && !ctx.inconsistent()) {
        TRACE("seq", tout << "replay at level: " << ctx.get_scope_level() << "\n";);
        apply& app = *m_replay[m_replay.size() - 1];
        app(*this);
        m_replay.pop_back();
    }
    if (m_new_solution) {
        simplify_and_solve_eqs();
        m_new_solution = false;
    }
}

void theory_seq::enque_axiom(expr* e) {
    if (!m_axiom_set.contains(e)) {
        TRACE("seq", tout << "add axiom " << mk_bounded_pp(e, m) << "\n";);
        m_axioms.push_back(e);
        m_axiom_set.insert(e);
        m_trail_stack.push(push_back_vector<expr_ref_vector>(m_axioms));
        m_trail_stack.push(insert_obj_trail<expr>(m_axiom_set, e));;
    }
}

void theory_seq::deque_axiom(expr* n) {
    TRACE("seq", tout << "deque: " << mk_bounded_pp(n, m, 2) << "\n";);
    if (m_util.str.is_length(n)) {
        add_length(n);
        m_ax.add_length_axiom(n);
        if (!ctx.at_base_level()) {
            m_trail_stack.push(push_replay(*this, alloc(replay_axiom, m, n)));
        }
    }
    else if (m_util.str.is_empty(n) && !has_length(n) && !m_has_length.empty()) {
        add_length_to_eqc(n);
    }
    else if (m_util.str.is_index(n)) {
        m_ax.add_indexof_axiom(n);
    }
    else if (m_util.str.is_last_index(n)) {
        m_ax.add_last_indexof_axiom(n);
    }
    else if (m_util.str.is_replace(n)) {
        m_ax.add_replace_axiom(n);
    }
    else if (m_util.str.is_extract(n)) {
        m_ax.add_extract_axiom(n);
    }
    else if (m_util.str.is_at(n)) {
        m_ax.add_at_axiom(n);
    }
    else if (m_util.str.is_nth_i(n)) {
        m_ax.add_nth_axiom(n);
    }
    else if (m_util.str.is_string(n)) {
        add_elim_string_axiom(n);
    }
    else if (m_util.str.is_itos(n)) {
        m_ax.add_itos_axiom(n);
        add_length_limit(n, m_max_unfolding_depth, true);
    }
    else if (m_util.str.is_stoi(n)) {
        m_ax.add_stoi_axiom(n);
        add_length_limit(n, m_max_unfolding_depth, true);
    }
    else if (m_util.str.is_lt(n)) {
        m_ax.add_lt_axiom(n);
    }
    else if (m_util.str.is_le(n)) {
        m_ax.add_le_axiom(n);
    }
    else if (m_util.str.is_unit(n)) {
        m_ax.add_unit_axiom(n);
    }
    else if (m_util.str.is_is_digit(n)) {
        m_ax.add_is_digit_axiom(n);        
    }
    else if (m_util.str.is_from_code(n)) {
        m_ax.add_str_from_code_axiom(n);        
    }
    else if (m_util.str.is_to_code(n)) {
        m_ax.add_str_to_code_axiom(n);        
    }
}

expr_ref theory_seq::add_elim_string_axiom(expr* n) {
    zstring s;
    TRACE("seq", tout << mk_pp(n, m) << "\n";);
    VERIFY(m_util.str.is_string(n, s));
    if (s.length() == 0) {
        return expr_ref(n, m);
    }
    expr_ref result(m_util.str.mk_unit(m_util.str.mk_char(s, s.length()-1)), m);
    for (unsigned i = s.length()-1; i-- > 0; ) {
        result = mk_concat(m_util.str.mk_unit(m_util.str.mk_char(s, i)), result);
    }
    add_axiom(mk_eq(n, result, false));
    m_rep.update(n, result, nullptr);
    m_new_solution = true;
    return result;
}

expr_ref theory_seq::mk_sub(expr* a, expr* b) {
    expr_ref result(m_autil.mk_sub(a, b), m);
    m_rewrite(result);
    return result;
}

expr_ref theory_seq::mk_add(expr* a, expr* b) {
    expr_ref result(m_autil.mk_add(a, b), m);
    m_rewrite(result);
    return result;
}

expr_ref theory_seq::mk_len(expr* s) {
    return m_seq_rewrite.mk_length(s);
}


template <class T>
static T* get_th_arith(context& ctx, theory_id afid, expr* e) {
    theory* th = ctx.get_theory(afid);
    if (th && ctx.e_internalized(e)) {
        return dynamic_cast<T*>(th);
    }
    else {
        return nullptr;
    }
}

bool theory_seq::get_num_value(expr* e, rational& val) const {
    return m_arith_value.get_value_equiv(e, val) && val.is_int();
}

bool theory_seq::lower_bound(expr* e, rational& lo) const {
    VERIFY(m_autil.is_int(e));
    bool is_strict = true;
    return m_arith_value.get_lo(e, lo, is_strict) && !is_strict && lo.is_int();
}

bool theory_seq::upper_bound(expr* e, rational& hi) const {
    VERIFY(m_autil.is_int(e));
    bool is_strict = true;
    return m_arith_value.get_up(e, hi, is_strict) && !is_strict && hi.is_int();
}

// The difference with lower_bound function is that since in some cases,
// the lower bound is not updated for all the enodes in the same eqc,
// we have to traverse the eqc to query for the better lower bound.
bool theory_seq::lower_bound2(expr* _e, rational& lo) {
    expr_ref e = mk_len(_e);
    bool is_strict = false;
    return m_arith_value.get_lo_equiv(e, lo, is_strict) && !is_strict;
}

bool theory_seq::get_length(expr* e, rational& val) {
    rational val1;
    expr_ref len(m), len_val(m);
    expr* e1 = nullptr, *e2 = nullptr;
    ptr_vector<expr> todo;
    todo.push_back(e);
    val.reset();
    zstring s;
    while (!todo.empty()) {
        expr* c = todo.back();
        todo.pop_back();
        if (m_util.str.is_concat(c, e1, e2)) {
            todo.push_back(e1);
            todo.push_back(e2);
        }
        else if (m_util.str.is_unit(c)) {
            val += rational(1);
        }
        else if (m_util.str.is_empty(c)) {
            continue;
        }
        else if (m_util.str.is_string(c, s)) {
            val += rational(s.length());
        }
        else if (!has_length(c)) {
            len = mk_len(c);
            add_axiom(mk_literal(m_autil.mk_ge(len, m_autil.mk_int(0))));
            TRACE("seq", tout << "literal has no length " << mk_pp(c, m) << "\n";);
            return false;            
        }
        else {            
            len = mk_len(c);
            if (m_arith_value.get_value(len, val1) && !val1.is_neg()) {
                val += val1;                
            }
            else {
                TRACE("seq", tout << "length has not been internalized " << mk_pp(c, m) << "\n";);
                return false;
            }
        }
    }
    CTRACE("seq", !val.is_int(), tout << "length is not an integer\n";);
    return val.is_int();
}


/*
    lit => s = (nth s 0) ++ (nth s 1) ++ ... ++ (nth s idx) ++ (tail s idx)
*/
void theory_seq::ensure_nth(literal lit, expr* s, expr* idx) {
    TRACE("seq", tout << "ensure-nth: " << lit << " " << mk_bounded_pp(s, m, 2) << " " << mk_bounded_pp(idx, m, 2) << "\n";);
    rational r;
    SASSERT(ctx.get_assignment(lit) == l_true);
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());
    unsigned _idx = r.get_unsigned();
    expr_ref head(m), tail(m), conc(m), len1(m), len2(m);
    expr_ref_vector elems(m);

    expr* s2 = s;
    for (unsigned j = 0; j <= _idx; ++j) {
        m_sk.decompose(s2, head, tail);
        elems.push_back(head);
        len1 = mk_len(s2);
        len2 = m_autil.mk_add(m_autil.mk_int(1), mk_len(tail));
        propagate_eq(lit, len1, len2, false);
        s2 = tail;
    }
    elems.push_back(s2);
    conc = mk_concat(elems, s->get_sort());
    propagate_eq(lit, s, conc, true);
}

literal theory_seq::mk_simplified_literal(expr * _e) {
    expr_ref e(_e, m);
    m_rewrite(e);
    return mk_literal(e);
}

literal theory_seq::mk_seq_eq(expr* a, expr* b) {
    SASSERT(m_util.is_seq(a));
    return mk_literal(m_sk.mk_eq(a, b));
}


literal theory_seq::mk_eq_empty(expr* _e, bool phase) {
    expr_ref e(_e, m);
    SASSERT(m_util.is_seq(e));
    expr_ref emp(m);
    zstring s;
    if (m_util.str.is_empty(e)) {
        return true_literal;
    }
    expr_ref_vector concats(m);
    m_util.str.get_concat_units(e, concats);
    for (auto c : concats) {
        if (m_util.str.is_unit(c)) {
            return false_literal;
        }
        if (m_util.str.is_string(c, s) && s.length() > 0) {
            return false_literal;
        }
    }
    emp = m_util.str.mk_empty(e->get_sort());

    literal lit = mk_eq(e, emp, false);
    ctx.force_phase(phase?lit:~lit);
    ctx.mark_as_relevant(lit);
    return lit;
}

void theory_seq::add_axiom(literal l1, literal l2, literal l3, literal l4, literal l5) {
    literal_vector lits;
    if (l1 == true_literal || l2 == true_literal || l3 == true_literal || 
        l4 == true_literal || l5 == true_literal) return;
    if (l1 != null_literal && l1 != false_literal) lits.push_back(l1); 
    if (l2 != null_literal && l2 != false_literal) lits.push_back(l2); 
    if (l3 != null_literal && l3 != false_literal) lits.push_back(l3); 
    if (l4 != null_literal && l4 != false_literal) lits.push_back(l4); 
    if (l5 != null_literal && l5 != false_literal) lits.push_back(l5); 
    add_axiom(lits);
}

void theory_seq::add_axiom(literal_vector & lits) {
    TRACE("seq", ctx.display_literals_verbose(tout << "assert:", lits) << "\n";);
    for (literal lit : lits)
        ctx.mark_as_relevant(lit);

    IF_VERBOSE(10, verbose_stream() << "ax ";
               for (literal l : lits) ctx.display_literal_smt2(verbose_stream() << " ", l); 
               verbose_stream() << "\n");
    m_new_propagation = true;
    ++m_stats.m_add_axiom;
    
    scoped_trace_stream _sts(*this, lits);
    validate_axiom(lits);
    ctx.mk_th_axiom(get_id(), lits.size(), lits.data());    
}


theory_seq::dependency* theory_seq::mk_join(dependency* deps, literal lit) {
    return m_dm.mk_join(deps, m_dm.mk_leaf(assumption(lit)));
}

theory_seq::dependency* theory_seq::mk_join(dependency* deps, literal_vector const& lits) {
    for (literal l : lits) {
        deps = mk_join(deps, l);
    } 
    return deps;
}

bool theory_seq::propagate_eq(literal lit, expr* e1, expr* e2, bool add_to_eqs) {
    literal_vector lits;
    lits.push_back(lit);
    return propagate_eq(nullptr, lits, e1, e2, add_to_eqs);
}

bool theory_seq::propagate_eq(dependency* deps, literal_vector const& _lits, expr* e1, expr* e2, bool add_to_eqs) {

    enode* n1 = ensure_enode(e1);
    enode* n2 = ensure_enode(e2);
    if (n1->get_root() == n2->get_root()) {
        return false;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    
    literal_vector lits(_lits);
    enode_pair_vector eqs;
    linearize(deps, eqs, lits);

    if (add_to_eqs) {
        deps = mk_join(deps, _lits);
        new_eq_eh(deps, n1, n2);
    }
    TRACE("seq_verbose",
          tout << "assert: #" << e1->get_id() << " " << mk_pp(e1, m) << " = " << mk_pp(e2, m) << " <- \n";
          if (!lits.empty()) { ctx.display_literals_verbose(tout, lits) << "\n"; });

    TRACE("seq",
          tout << "assert:" << mk_bounded_pp(e1, m, 2) << " = " << mk_bounded_pp(e2, m, 2) << " <- \n";
          tout << lits << "\n";
          tout << "#" << e1->get_id() << "\n"; 
          );

    justification* js =
        ctx.mk_justification(
            ext_theory_eq_propagation_justification(
                get_id(), ctx.get_region(), lits.size(), lits.data(), eqs.size(), eqs.data(), n1, n2));

    m_new_propagation = true;
    
    std::function<expr*(void)> fn = [&]() { return m.mk_eq(e1, e2); };
    scoped_trace_stream _sts(*this, fn);
    ctx.assign_eq(n1, n2, eq_justification(js));
    validate_assign_eq(n1, n2, eqs, lits);
    return true;
}

void theory_seq::assign_eh(bool_var v, bool is_true) {
    expr* e = ctx.bool_var2expr(v);
    expr* e1 = nullptr, *e2 = nullptr;
    expr_ref f(m);
    literal lit(v, !is_true);
    TRACE("seq", tout << (is_true?"":"not ") << mk_bounded_pp(e, m) << "\n";);
    TRACE("seq", tout << (is_true?"":"not ") << mk_bounded_pp(e, m) << " " << ctx.get_scope_level() << " " << lit << "\n";);

    if (m_util.str.is_prefix(e, e1, e2)) {
        if (is_true) {
            expr_ref se1(e1, m), se2(e2, m);
            m_rewrite(se1);
            m_rewrite(se2);
            f = m_sk.mk_prefix_inv(se1, se2);
            f = mk_concat(se1, f);
            propagate_eq(lit, f, se2, true);
            propagate_eq(lit, mk_len(f), mk_len(se2), false);
        }
        else {
            propagate_not_prefix(e);
        }
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        if (is_true) {
            expr_ref se1(e1, m), se2(e2, m);
            m_rewrite(se1);
            m_rewrite(se2);
            f = m_sk.mk_suffix_inv(se1, se2);
            f = mk_concat(f, se1);
            propagate_eq(lit, f, se2, true);
            propagate_eq(lit, mk_len(f), mk_len(se2), false);
        }
        else {
            propagate_not_suffix(e);
        }
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        // TBD: move this to cover all cases
        if (canonizes(is_true, e)) {
            return;
        }        

        expr_ref se1(e1, m), se2(e2, m);
        m_rewrite(se1);
        m_rewrite(se2);
        if (is_true) {
            expr_ref f1 = m_sk.mk_indexof_left(se1, se2);
            expr_ref f2 = m_sk.mk_indexof_right(se1, se2);
            f = mk_concat(f1, se2, f2);
            propagate_eq(lit, f, e1, true);
            propagate_eq(lit, mk_len(f), mk_len(e1), false);
        }
        else {
            propagate_non_empty(lit, se2);
            dependency* dep = m_dm.mk_leaf(assumption(lit));
            // |e1| - |e2| <= -1
            literal len_gt = m_ax.mk_le(mk_sub(mk_len(se1), mk_len(se2)), -1);
            ctx.force_phase(len_gt);
            m_ncs.push_back(nc(expr_ref(e, m), len_gt, dep));
        }
    }
    else if (m_sk.is_accept(e)) {
        if (is_true) 
            m_regex.propagate_accept(lit);
    }
    else if (m_sk.is_is_empty(e)) {
        if (is_true)
            m_regex.propagate_is_empty(lit);
    }
    else if (m_sk.is_is_non_empty(e)) {
        if (is_true)
            m_regex.propagate_is_non_empty(lit);
    }
    else if (m_sk.is_eq(e, e1, e2)) {
        if (is_true) {
            propagate_eq(lit, e1, e2, true);
        }
    }
    else if (m_util.str.is_in_re(e)) {
        m_regex.propagate_in_re(lit);
    }
    else if (m_sk.is_digit(e)) {
        // no-op
    }
    else if (m_sk.is_max_unfolding(e)) {
        // no-op
    }
    else if (m_sk.is_length_limit(e)) {
        if (is_true) {
            propagate_length_limit(e);
        }
    }
    else if (m_util.str.is_lt(e) || m_util.str.is_le(e)) {
        m_lts.push_back(e);
    }
    else if (m_util.str.is_nth_i(e) || m_util.str.is_nth_u(e)) {
        // no-op
    }
    else if (m_util.is_skolem(e)) {
        
        // no-op
    }
    else if (m_util.str.is_is_digit(e)) {
	
    }
    else {
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        UNREACHABLE();
    }
}

void theory_seq::new_eq_eh(theory_var v1, theory_var v2) {
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    expr* o1 = n1->get_expr();
    expr* o2 = n2->get_expr();
    if (!m_util.is_seq(o1) && !m_util.is_re(o1))
        return;
    if (m_util.is_re(o1)) {
        m_regex.propagate_eq(o1, o2);
        return;        
    }

    dependency* deps = m_dm.mk_leaf(assumption(n1, n2));
    new_eq_eh(deps, n1, n2);
}

void theory_seq::new_eq_eh(dependency* deps, enode* n1, enode* n2) {
    expr* e1 = n1->get_expr();
    expr* e2 = n2->get_expr();
    TRACE("seq", tout << mk_bounded_pp(e1, m) << " = " << mk_bounded_pp(e2, m) << "\n";);
    if (n1 != n2 && m_util.is_seq(e1)) {
        theory_var v1 = n1->get_th_var(get_id());
        theory_var v2 = n2->get_th_var(get_id());
        if (v1 == null_theory_var || v2 == null_theory_var)
            return;
        if (m_find.find(v1) == m_find.find(v2)) 
            return;
        
        m_find.merge(v1, v2);
        expr_ref o1(e1, m);
        expr_ref o2(e2, m);
        TRACE("seq", tout << mk_bounded_pp(o1, m) << " = " << mk_bounded_pp(o2, m) << "\n";);
        m_eqs.push_back(mk_eqdep(o1, o2, deps));
        solve_eqs(m_eqs.size()-1);
        enforce_length_coherence(n1, n2);
    }
    else if (n1 != n2 && m_util.is_re(e1)) {
        UNREACHABLE();
    }
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);    
    expr_ref e1(n1->get_expr(), m);
    expr_ref e2(n2->get_expr(), m);
    if (n1->get_root() == n2->get_root())
        return;
    if (m_util.is_re(n1->get_expr())) {        
        m_regex.propagate_ne(e1, e2);
        return;
    }
    if (!m_util.is_seq(e1))
        return;
    m_exclude.update(e1, e2);
    expr_ref eq(m.mk_eq(e1, e2), m);
    TRACE("seq", tout << "new disequality " << ctx.get_scope_level() << ": " << mk_bounded_pp(eq, m, 2) << "\n";);
    m_rewrite(eq);
    if (!m.is_false(eq)) {
        literal lit = mk_eq(e1, e2, false);
        ctx.mark_as_relevant(lit);
        if (m_util.str.is_empty(e2)) {
            std::swap(e1, e2);
        }

        dependency* dep = m_dm.mk_leaf(assumption(~lit));
        m_nqs.push_back(ne(e1, e2, dep));
        if (ctx.get_assignment(lit) != l_undef) {
            solve_nqs(m_nqs.size() - 1);
        }
    }
}

void theory_seq::push_scope_eh() {
    theory::push_scope_eh();
    m_rep.push_scope();
    m_exclude.push_scope();
    m_dm.push_scope();
    m_trail_stack.push_scope();
    m_trail_stack.push(value_trail<unsigned>(m_axioms_head));
    m_eqs.push_scope();
    m_nqs.push_scope();
    m_ncs.push_scope();
    m_lts.push_scope();
    m_regex.push_scope();
}

void theory_seq::pop_scope_eh(unsigned num_scopes) {
    m_trail_stack.pop_scope(num_scopes);
    theory::pop_scope_eh(num_scopes);
    m_dm.pop_scope(num_scopes);
    m_rep.pop_scope(num_scopes);
    m_exclude.pop_scope(num_scopes);
    m_eqs.pop_scope(num_scopes);
    m_nqs.pop_scope(num_scopes);
    m_ncs.pop_scope(num_scopes);
    m_lts.pop_scope(num_scopes);
    m_regex.pop_scope(num_scopes);
    m_rewrite.reset();    
    if (ctx.get_base_level() > ctx.get_scope_level() - num_scopes) {
        m_replay.reset();
    }
    m_offset_eq.pop_scope_eh(num_scopes);
}

void theory_seq::restart_eh() {
}

void theory_seq::relevant_eh(app* n) {
    if (m_util.str.is_index(n)   ||
        m_util.str.is_replace(n) ||
        m_util.str.is_extract(n) ||
        m_util.str.is_at(n) ||
        m_util.str.is_nth_i(n) ||
        m_util.str.is_empty(n) ||
        m_util.str.is_string(n) ||
        m_util.str.is_itos(n) || 
        m_util.str.is_stoi(n) ||
        m_util.str.is_lt(n) ||
        m_util.str.is_is_digit(n) ||
        m_util.str.is_from_code(n) ||
        m_util.str.is_to_code(n) ||
        m_util.str.is_unit(n) ||
        m_util.str.is_length(n) || 
        m_util.str.is_le(n)) {
        enque_axiom(n);
    }

    if (m_util.str.is_itos(n) ||
        m_util.str.is_stoi(n)) {
        add_int_string(n);
    }

    if (m_util.str.is_ubv2s(n))
        add_ubv_string(n);

    expr* arg = nullptr;
    if (m_sk.is_tail(n, arg)) {
        add_length_limit(arg, m_max_unfolding_depth, true);
    }

    if (m_util.str.is_length(n, arg) && !has_length(arg) && ctx.e_internalized(arg)) {
        add_length_to_eqc(arg);
    }

    if (m_util.str.is_replace_all(n) ||
        m_util.str.is_replace_re(n) ||
        m_util.str.is_replace_re_all(n) ||
        // m_util.str.is_from_code(n) ||
        // m_util.str.is_to_code(n) ||
        m_util.str.is_is_digit(n)) {
        add_unhandled_expr(n);
    }
}

void theory_seq::add_unhandled_expr(expr* n) {
    if (!m_unhandled_expr) {
        ctx.push_trail(value_trail<expr*>(m_unhandled_expr));
        m_unhandled_expr = n;
    }
}


void theory_seq::add_theory_assumptions(expr_ref_vector & assumptions) {
    if (m_has_seq) {
        TRACE("seq", tout << "add_theory_assumption\n";);
        expr_ref dlimit = m_sk.mk_max_unfolding_depth(m_max_unfolding_depth);
        m_trail_stack.push(value_trail<literal>(m_max_unfolding_lit));
        m_max_unfolding_lit = mk_literal(dlimit);        
        assumptions.push_back(dlimit);
        for (auto const& kv : m_length_limit_map) {
            if (kv.m_value > 0)
                assumptions.push_back(m_sk.mk_length_limit(kv.m_key, kv.m_value));
        }
    }
}

bool theory_seq::should_research(expr_ref_vector & unsat_core) {
    TRACE("seq", tout << unsat_core << " " << m_util.has_re() << "\n";);
    if (!m_has_seq) 
        return false;
    unsigned k_min = UINT_MAX, k = 0, n = 0;
    expr* s_min = nullptr, *s = nullptr;
    bool has_max_unfolding = false;
    for (auto & e : unsat_core) {
        if (m_sk.is_max_unfolding(e)) {
            has_max_unfolding = true;
        }
        else if (m_sk.is_length_limit(e, k, s)) {
            if (k < k_min) {
                k_min = k;
                s_min = s;
                n = 0;
            }
            else if (k == k_min && ctx.get_random_value() % (++n) == 0) {
                s_min = s;                
            }
        }
    }

    if (k_min < UINT_MAX/4) {
        m_max_unfolding_depth++;
        k_min *= 2;
        if (m_util.is_seq(s_min))
            k_min = std::max(m_util.str.min_length(s_min), k_min);
        IF_VERBOSE(1, verbose_stream() << "(smt.seq :increase-length " << mk_pp(s_min, m) << " " << k_min << ")\n");
        add_length_limit(s_min, k_min, false);
        return true;
    }
    else if (has_max_unfolding) {
        m_max_unfolding_depth = (1 + 3*m_max_unfolding_depth)/2;
        IF_VERBOSE(1, verbose_stream() << "(smt.seq :increase-depth " << m_max_unfolding_depth << ")\n");
        return true;
    }
    else if (k_min != UINT_MAX && k_min >= UINT_MAX/4) {
        throw default_exception("reached max unfolding");
    }

    return false;
}


void theory_seq::propagate_length_limit(expr* e) {
    unsigned k = 0;
    expr* s = nullptr;
    VERIFY(m_sk.is_length_limit(e, k, s));
    if (m_util.str.is_stoi(s)) {
        m_ax.add_stoi_axiom(s, k);
    }    
    if (m_util.str.is_itos(s)) {
        m_ax.add_itos_axiom(s, k);
    }
}

/*
  !prefix(e1,e2) => e1 != ""
  !prefix(e1,e2) => len(e1) > len(e2) or e1 = xcy & e2 = xdz & c != d
*/

void theory_seq::propagate_not_prefix(expr* e) {
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(m_util.str.is_prefix(e, e1, e2));
    literal lit = ctx.get_literal(e);
    SASSERT(ctx.get_assignment(lit) == l_false);
    dependency * deps = nullptr;
    expr_ref cont(m);
    if (canonize(e, deps, cont) && m.is_true(cont)) {
        propagate_lit(deps, 0, nullptr, lit);
        return;
    }
    propagate_non_empty(~lit, e1);
    m_ax.add_prefix_axiom(e);
}

/*
  !suffix(e1,e2) => e1 != ""
  !suffix(e1,e2) => len(e1) > len(e2) or e1 = ycx & e2 = zdx & c != d
*/

void theory_seq::propagate_not_suffix(expr* e) {
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(m_util.str.is_suffix(e, e1, e2));
    literal lit = ctx.get_literal(e);
    SASSERT(ctx.get_assignment(lit) == l_false);

    dependency * deps = nullptr;
    expr_ref cont(m);
    if (canonize(e, deps, cont) && m.is_true(cont)) {
        propagate_lit(deps, 0, nullptr, lit);
        return;
    }
    propagate_non_empty(~lit, e1);
    m_ax.add_suffix_axiom(e);

}

bool theory_seq::canonizes(bool is_true, expr* e) {
    dependency* deps = nullptr;
    expr_ref cont(m);
    if (!canonize(e, deps, cont)) cont = e;
    TRACE("seq", tout << is_true << ": " << mk_bounded_pp(e, m, 2) << " -> " << mk_bounded_pp(cont, m, 2) << "\n";
          if (deps) display_deps(tout, deps););
    if ((m.is_true(cont) && !is_true) ||
        (m.is_false(cont) && is_true)) {
        TRACE("seq", display(tout); tout << ctx.get_assignment(ctx.get_literal(e)) << "\n";);
        literal lit = ctx.get_literal(e);
        if (is_true) lit.neg();
        propagate_lit(deps, 0, nullptr, lit);
        return true;
    }
    if ((m.is_false(cont) && !is_true) ||
        (m.is_true(cont) && is_true)) {
        TRACE("seq", display(tout););
        return true;
    }
    return false;
}


void theory_seq::get_ite_concat(ptr_vector<expr>& concats, ptr_vector<expr>& todo) {
    expr* e1 = nullptr, *e2 = nullptr;
    while (!todo.empty()) {
        expr* e = todo.back();
        todo.pop_back();
        e = m_rep.find(e);
        e = get_ite_value(e);
        e = m_rep.find(e);
        if (m_util.str.is_concat(e, e1, e2)) {
            todo.push_back(e2, e1);
        }        
        else {
            concats.push_back(e);        
        }
    }
}
