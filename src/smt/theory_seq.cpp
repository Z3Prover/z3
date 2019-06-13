/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    theory_seq.h

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
   - (f,dep) = canonize(contains(a, b))
     lit := |b| > |a|
     f := true -> conflict
     f := false -> solved
     value(lit) = l_true -> solved
     f := s = t -> dep -> s != t
     f := f1 & f2 -> dep -> ~f1 | ~f2
     f := f1 | f2 -> dep -> ~f1 & ~f2

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
#include "ast/ast_trail.h"
#include "smt/proto_model/value_factory.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_seq.h"
#include "smt/theory_arith.h"
#include "smt/theory_lra.h"
#include "smt/smt_kernel.h"

using namespace smt;

struct display_expr {
    ast_manager& m;
    display_expr(ast_manager& m): m(m) {}
    std::ostream& display(std::ostream& out, sym_expr* e) const {
        return e->display(out);
    }
};

class seq_expr_solver : public expr_solver {
    kernel m_kernel;
public:
    seq_expr_solver(ast_manager& m, smt_params& fp):
        m_kernel(m, fp)
    {}

    lbool check_sat(expr* e) override {
        m_kernel.push();
        m_kernel.assert_expr(e);
        lbool r = m_kernel.check();
        m_kernel.pop(1);
        IF_VERBOSE(11, verbose_stream() << "is " << r << " " << mk_pp(e, m_kernel.m()) << "\n");
        return r;
    }
};


void theory_seq::solution_map::update(expr* e, expr* r, dependency* d) {
    if (e == r) {
        return;
    }
    m_cache.reset();
    std::pair<expr*, dependency*> value;
    if (m_map.find(e, value)) {
        add_trail(DEL, e, value.first, value.second);
    }
    value.first = r;
    value.second = d;
    m_map.insert(e, value);
    add_trail(INS, e, r, d);
}

void theory_seq::solution_map::add_trail(map_update op, expr* l, expr* r, dependency* d) {
    m_updates.push_back(op);
    m_lhs.push_back(l);
    m_rhs.push_back(r);
    m_deps.push_back(d);
}

bool theory_seq::solution_map::is_root(expr* e) const {
    return !m_map.contains(e);
}

// e1 -> ... -> e2
// e2 -> e3
// e1 -> .... -> e3

// e1 -> ... x, e2 -> ... x
void theory_seq::solution_map::find_rec(expr* e, svector<std::pair<expr*, dependency*> >& finds) {
    dependency* d = nullptr;
    std::pair<expr*, dependency*> value(e, d);
    do {
        e = value.first;
        d = m_dm.mk_join(d, value.second);
        finds.push_back(value);
    }
    while (m_map.find(e, value));
}

bool theory_seq::solution_map::find1(expr* e, expr*& r, dependency*& d) {
    std::pair<expr*, dependency*> value;    
    if (m_map.find(e, value)) {
        d = m_dm.mk_join(d, value.second);
        r = value.first;
        return true;
    }
    else {
        return false;
    }
}

expr* theory_seq::solution_map::find(expr* e, dependency*& d) {
    std::pair<expr*, dependency*> value;
    d = nullptr;
    expr* result = e;
    while (m_map.find(result, value)) {
        d = m_dm.mk_join(d, value.second);
        SASSERT(result != value.first);
        SASSERT(e != value.first);
        result = value.first;
    }
    return result;
}

expr* theory_seq::solution_map::find(expr* e) {
    std::pair<expr*, dependency*> value;
    while (m_map.find(e, value)) {
        e = value.first;
    }
    return e;
}

void theory_seq::solution_map::pop_scope(unsigned num_scopes) {
    if (num_scopes == 0) return;
    m_cache.reset();
    unsigned start = m_limit[m_limit.size() - num_scopes];
    for (unsigned i = m_updates.size(); i-- > start; ) {
        if (m_updates[i] == INS) {
            m_map.remove(m_lhs[i].get());
        }
        else {
            m_map.insert(m_lhs[i].get(), std::make_pair(m_rhs[i].get(), m_deps[i]));
        }
    }
    m_updates.resize(start);
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_deps.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

void theory_seq::solution_map::display(std::ostream& out) const {
    for (auto const& kv : m_map) {
        out << mk_pp(kv.m_key, m) << " |-> " << mk_pp(kv.m_value.first, m) << "\n";
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
        m_table.erase(std::make_pair(m_lhs[i].get(), m_rhs[i].get()));
    }
    m_lhs.resize(start);
    m_rhs.resize(start);
    m_limit.resize(m_limit.size() - num_scopes);
}

void theory_seq::exclusion_table::display(std::ostream& out) const {
    for (auto const& kv : m_table) {
        out << mk_pp(kv.first, m) << " != " << mk_pp(kv.second, m) << "\n";
    }
}


theory_seq::theory_seq(ast_manager& m, theory_seq_params const & params):
    theory(m.mk_family_id("seq")),
    m(m),
    m_params(params),
    m_rep(m, m_dm),
    m_reset_cache(false),
    m_eq_id(0),
    m_find(*this),
    m_overlap(m),
    m_overlap2(m),
    m_len_prop_lvl(-1),
    m_internal_nth_es(m),
    m_factory(nullptr),
    m_exclude(m),
    m_axioms(m),
    m_axioms_head(0),
    m_int_string(m),
    m_length(m),
    m_mg(nullptr),
    m_rewrite(m),
    m_seq_rewrite(m),
    m_util(m),
    m_autil(m),
    m_arith_value(m),
    m_trail_stack(*this),
    m_ls(m), m_rs(m),
    m_lhs(m), m_rhs(m),
    m_res(m),
    m_max_unfolding_depth(1),
    m_max_unfolding_lit(null_literal),
    m_new_solution(false),
    m_new_propagation(false),
    m_mk_aut(m) {
    m_prefix         = "seq.p.suffix";
    m_suffix         = "seq.s.prefix";
    m_accept         = "aut.accept";
    m_tail           = "seq.tail";
    m_seq_first      = "seq.first";
    m_seq_last       = "seq.last";
    m_indexof_left   = "seq.idx.left";
    m_indexof_right  = "seq.idx.right";
    m_aut_step       = "aut.step";
    m_pre            = "seq.pre";  // (seq.pre s l):  prefix of string s of length l
    m_post           = "seq.post"; // (seq.post s l): suffix of string s of length l
    m_eq             = "seq.eq";
    m_seq_align      = "seq.align";

}

theory_seq::~theory_seq() {
    m_trail_stack.reset();
}

void theory_seq::init(context* ctx) {
    theory::init(ctx);    
    m_arith_value.init(ctx);
}

#define TRACEFIN(s) { TRACE("seq", tout << ">>" << s << "\n";); IF_VERBOSE(31, verbose_stream() << s << "\n"); }


final_check_status theory_seq::final_check_eh() {
    if (m_reset_cache) {
        m_rep.reset_cache(); 
        m_reset_cache = false;
    }
    m_new_propagation = false;
    TRACE("seq", display(tout << "level: " << get_context().get_scope_level() << "\n"););
    TRACE("seq_verbose", get_context().display(tout););

    if (simplify_and_solve_eqs()) {
        ++m_stats.m_solve_eqs;
        TRACEFIN("solve_eqs");
        return FC_CONTINUE;
    }
    if (check_contains()) {
        ++m_stats.m_propagate_contains;
        TRACEFIN("propagate_contains");
        return FC_CONTINUE;
    }
    if (solve_nqs(0)) {
        ++m_stats.m_solve_nqs;
        TRACEFIN("solve_nqs");
        return FC_CONTINUE;
    }
    if (fixed_length(true)) {
        ++m_stats.m_fixed_length;
        TRACEFIN("zero_length");
        return FC_CONTINUE;
    }
    if (m_params.m_split_w_len && len_based_split()) {
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
    if (reduce_length_eq()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("reduce_length");
        return FC_CONTINUE;
    }
    if (branch_unit_variable()) {
        ++m_stats.m_branch_variable;
        TRACEFIN("ranch_unit_variable");
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
    if (is_solved()) {
        TRACEFIN("is_solved");
        return FC_DONE;
    }
    TRACEFIN("give_up");
    return FC_GIVEUP;
}

bool theory_seq::reduce_length_eq() {
    context& ctx = get_context();
    int start = ctx.get_random_value();

    TRACE("seq", tout << "reduce length eq\n";);
    for (unsigned i = 0; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (reduce_length_eq(e.ls(), e.rs(), e.dep())) {
            TRACE("seq", tout << "length\n";);
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_binary_variable() {
    for (auto const& e : m_eqs) {
        if (branch_binary_variable(e)) {
            TRACE("seq", display_equation(tout, e););
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_binary_variable(eq const& e) {
    if (is_complex(e)) {
        return false;
    }
    ptr_vector<expr> xs, ys;
    expr_ref x(m), y(m);
    bool is_binary = is_binary_eq(e.ls(), e.rs(), x, xs, ys, y);
    if (!is_binary) {
        is_binary = is_binary_eq(e.rs(), e.ls(), x, xs, ys, y);
    }
    if (!is_binary) {
        return false;
    }
    if (x == y) {
        return false;
    }
        
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    // x is either a prefix of ys, all of ys ++ y or ys ++ y1, such that y = y1 ++ y2, y2 = xs 
    
    rational lenX, lenY;
    context& ctx = get_context();
    if (branch_variable_eq(e)) {
        return true;
    }
    if (!get_length(x, lenX)) {
        enforce_length(x);
        return true;
    }
    if (!get_length(y, lenY)) {
        enforce_length(y);
        return true;
    }
    if (lenX + rational(xs.size()) != lenY + rational(ys.size())) {
        // |x| - |y| = |ys| - |xs|
        expr_ref a(mk_sub(mk_len(x), mk_len(y)), m);
        expr_ref b(m_autil.mk_int(ys.size()-xs.size()), m);
        propagate_lit(e.dep(), 0, nullptr, mk_eq(a, b, false));
        return true;
    }
    if (lenX <= rational(ys.size())) {
        expr_ref_vector Ys(m);
        Ys.append(ys.size(), ys.c_ptr());
        branch_unit_variable(e.dep(), x, Ys);
        return true;
    }
    expr_ref le(m_autil.mk_le(mk_len(x), m_autil.mk_int(ys.size())), m);
    literal lit = mk_literal(le);
    if (l_false == ctx.get_assignment(lit)) {
        // |x| > |ys| => x = ys ++ y1, y = y1 ++ y2, y2 = xs
        expr_ref Y1(mk_skolem(symbol("seq.left"), x, y), m);
        expr_ref Y2(mk_skolem(symbol("seq.right"), x, y), m);
        ys.push_back(Y1);
        expr_ref ysY1 = mk_concat(ys);
        expr_ref xsE = mk_concat(xs);
        expr_ref Y1Y2 = mk_concat(Y1, Y2); 
        dependency* dep = e.dep();
        propagate_eq(dep, ~lit, x, ysY1);
        propagate_eq(dep, ~lit, y, Y1Y2);
        propagate_eq(dep, ~lit, Y2, xsE);
    }
    else {
        ctx.mark_as_relevant(lit);
    }
    return true;
}

bool theory_seq::branch_unit_variable() {
    bool result = false;
    for (auto const& e : m_eqs) {
        if (is_unit_eq(e.ls(), e.rs())) {
            branch_unit_variable(e.dep(), e.ls()[0], e.rs());
            result = true;
            break;
        }
        else if (is_unit_eq(e.rs(), e.ls())) {
            branch_unit_variable(e.dep(), e.rs()[0], e.ls());
            result = true;
            break;
        }
    }
    CTRACE("seq", result, tout << "branch unit variable";);
    return result;
}

/**
  \brief ls := X... == rs := abcdef
*/
bool theory_seq::is_unit_eq(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    if (ls.empty() || !is_var(ls[0])) {
        return false;
    }

    for (auto const& elem : rs) {
        if (!m_util.str.is_unit(elem)) {
            return false;
        }
    }
    return true;
}

void theory_seq::branch_unit_variable(dependency* dep, expr* X, expr_ref_vector const& units) {
    SASSERT(is_var(X));
    context& ctx = get_context();
    rational lenX;
    if (!get_length(X, lenX)) {
        TRACE("seq", tout << "enforce length on " << mk_pp(X, m) << "\n";);
        enforce_length(X);
        return;
    }
    if (lenX > rational(units.size())) {
        expr_ref le(m_autil.mk_le(mk_len(X), m_autil.mk_int(units.size())), m);
        TRACE("seq", tout << "propagate length on " << mk_pp(X, m) << "\n";);
        propagate_lit(dep, 0, nullptr, mk_literal(le));
        return;
    }
    SASSERT(lenX.is_unsigned());
    unsigned lX = lenX.get_unsigned();
    if (lX == 0) {
        TRACE("seq", tout << "set empty length " << mk_pp(X, m) << "\n";);
        set_empty(X);
    }
    else {
        literal lit = mk_eq(m_autil.mk_int(lX), mk_len(X), false);
        if (l_true == ctx.get_assignment(lit)) {
            expr_ref R(m_util.str.mk_concat(lX, units.c_ptr()), m);
            propagate_eq(dep, lit, X, R);
            TRACE("seq", tout << "propagate " << mk_pp(X, m) << " " << R << "\n";);
        }
        else {
            TRACE("seq", tout << "set phase " << mk_pp(X, m) << "\n";);
            ctx.mark_as_relevant(lit);
            ctx.force_phase(lit);
        }
    }
}

bool theory_seq::branch_ternary_variable1() {
    int start = get_context().get_random_value();
    for (unsigned i = 0; i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (branch_ternary_variable(e) || branch_ternary_variable2(e)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_ternary_variable2() {
    int start = get_context().get_random_value();
    for (unsigned i = 0; i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (branch_ternary_variable(e, true)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::eq_unit(expr* const& l, expr* const &r) const {
    return l == r || is_unit_nth(l) || is_unit_nth(r);
}

// exists x, y, rs' != empty s.t.  (ls = x ++ rs' ++ y & rs = rs') || (ls = rs' ++ x && rs = y ++ rs')
// TBD: spec comment above doesn't seem to match what this function does.
unsigned_vector theory_seq::overlap(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    unsigned_vector result;
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l,r), m);
    if (m_overlap.find(pair, result)) {
        return result;
    }
    result.reset();
    for (unsigned i = 0; i < ls.size(); ++i) {
        if (eq_unit(ls[i], rs.back())) {
            bool same = rs.size() > i;
            for (unsigned j = 0; same && j < i; ++j) {
                same = eq_unit(ls[j], rs[rs.size() - 1 - i + j]);        
            }
            if (same)
                result.push_back(i+1);
        }
    }
    m_overlap.insert(pair, result);
    return result;
}

// exists x, y, rs' != empty s.t.  (ls = x ++ rs' ++ y & rs = rs') || (ls = x ++ rs' && rs = rs' ++ y)
unsigned_vector theory_seq::overlap2(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    unsigned_vector res;
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l,r), m);
    if (m_overlap2.find(pair, res)) {
        return res;
    }
    unsigned_vector result;
    for (unsigned i = 0; i < ls.size(); ++i) {
        if (eq_unit(ls[i],rs[0])) {
            bool same = true;
            unsigned j = i+1;
            while (j < ls.size() && j-i < rs.size()) {
                if (!eq_unit(ls[j], rs[j-i])) {
                    same = false;
                    break;
                }
                ++j;
            }
            if (same)
                result.push_back(i);
        }
    }
    m_overlap2.insert(pair, result);
    return result;
}

bool theory_seq::branch_ternary_variable_base(
    dependency* dep, unsigned_vector indexes,
    expr* const& x, expr_ref_vector const& xs, expr* const& y1, expr_ref_vector const& ys, expr* const& y2) {
    context& ctx = get_context();
    bool change = false;
    for (auto ind : indexes) {
        TRACE("seq", tout << "ind = " << ind << "\n";);
        expr_ref xs2E(m);
        if (xs.size() > ind) {
            xs2E = m_util.str.mk_concat(xs.size()-ind, xs.c_ptr()+ind);
        }
        else {
            xs2E = m_util.str.mk_empty(m.get_sort(x));
        }
        literal lit1 = mk_literal(m_autil.mk_le(mk_len(y2), m_autil.mk_int(xs.size()-ind)));
        if (ctx.get_assignment(lit1) == l_undef) {
            TRACE("seq", tout << "base case init\n";);
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
            change = true;
            continue;
        }
        else if (ctx.get_assignment(lit1) == l_true) {
            TRACE("seq", tout << "base case: true branch\n";);
            literal_vector lits;
            lits.push_back(lit1);
            propagate_eq(dep, lits, y2, xs2E, true);
            if (ind > ys.size()) {
                expr_ref xs1E(m_util.str.mk_concat(ind-ys.size(), xs.c_ptr()), m);
                expr_ref xxs1E = mk_concat(x, xs1E);
                propagate_eq(dep, lits, xxs1E, y1, true);
            }
            else if (ind == ys.size()) {
                propagate_eq(dep, lits, x, y1, true);
            }
            else {
                expr_ref ys1E(m_util.str.mk_concat(ys.size()-ind, ys.c_ptr()), m);
                expr_ref y1ys1E = mk_concat(y1, ys1E);
                propagate_eq(dep, lits, x, y1ys1E, true);
            }
            return true;
        }
        else {
            TRACE("seq", tout << "base case: false branch\n";);
            continue;
        }
    }
    return change;
}

// Equation is of the form x ++ xs = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_ternary_variable(eq const& e, bool flag1) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    bool is_ternary = is_ternary_eq(e.ls(), e.rs(), x, xs, y1, ys, y2, flag1);
    if (!is_ternary) {
        is_ternary = is_ternary_eq(e.rs(), e.ls(), x, xs, y1, ys, y2, flag1);
    }
    if (!is_ternary) {
        return false;
    }

    rational lenX, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x, lenX)) {
        enforce_length(x);
    }
    if (!get_length(y1, lenY1)) {
        enforce_length(y1);
    }
    if (!get_length(y2, lenY2)) {
        enforce_length(y2);
    }

    SASSERT(!xs.empty() && !ys.empty());
    unsigned_vector indexes = overlap(xs, ys);
    if (branch_ternary_variable_base(e.dep(), indexes, x, xs, y1, ys, y2))
        return true;
    
    // x ++ xs = y1 ++ ys ++ y2 => x = y1 ++ ys ++ z, z ++ xs = y2 
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref y1ys = mk_concat(y1, ysE);
    expr_ref Z(mk_skolem(m_seq_align, y2, xsE, x, y1ys), m);
    expr_ref ZxsE = mk_concat(Z, xsE);
    expr_ref y1ysZ = mk_concat(y1ys, Z);
    if (indexes.empty()) {
        TRACE("seq", tout << "one case\n";);
        TRACE("seq", display_equation(tout, e););
        literal_vector lits;
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x, y1ysZ, true);
        propagate_eq(dep, lits, y2, ZxsE, true);
    }
    else {
        expr_ref ge(m_autil.mk_ge(mk_len(y2), m_autil.mk_int(xs.size())), m);
        literal lit2 = mk_literal(ge);
        if (ctx.get_assignment(lit2) == l_undef) {
            TRACE("seq", tout << "rec case init\n";);
            ctx.mark_as_relevant(lit2);
            ctx.force_phase(lit2);
        }
        else if (ctx.get_assignment(lit2) == l_true) {
            TRACE("seq", tout << "true branch\n";);
            TRACE("seq", display_equation(tout, e););
            literal_vector lits;
            lits.push_back(lit2);
            dependency* dep = e.dep();
            propagate_eq(dep, lits, x, y1ysZ, true);
            propagate_eq(dep, lits, y2, ZxsE, true);
        }
        else {
            return branch_ternary_variable_base(e.dep(), indexes, x, xs, y1, ys, y2);
        }
    }
    return true;
}

bool theory_seq::branch_ternary_variable_base2(dependency* dep, unsigned_vector indexes,
        expr_ref_vector const& xs, expr* const& x, expr* const& y1, expr_ref_vector const& ys, expr* const& y2) {
    context& ctx = get_context();
    bool change = false;
    for (auto ind : indexes) {
        expr_ref xs1E(m);
        if (ind > 0) {
            xs1E = m_util.str.mk_concat(ind, xs.c_ptr());
        }
        else {
            xs1E = m_util.str.mk_empty(m.get_sort(x));
        }
        literal lit1 = mk_literal(m_autil.mk_le(mk_len(y1), m_autil.mk_int(ind)));
        if (ctx.get_assignment(lit1) == l_undef) {
            TRACE("seq", tout << "base case init\n";);
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
            change = true;
            continue;
        }
        else if (ctx.get_assignment(lit1) == l_true) {
            TRACE("seq", tout << "base case: true branch\n";);
            literal_vector lits;
            lits.push_back(lit1);
            propagate_eq(dep, lits, y1, xs1E, true);
            if (xs.size() - ind > ys.size()) {
                expr_ref xs2E(m_util.str.mk_concat(xs.size()-ind-ys.size(), xs.c_ptr()+ind+ys.size()), m);
                expr_ref xs2x = mk_concat(xs2E, x);
                propagate_eq(dep, lits, xs2x, y2, true);
            }
            else if (xs.size() - ind == ys.size()) {
                propagate_eq(dep, lits, x, y2, true);
            }
            else {
                expr_ref ys1E(m_util.str.mk_concat(ys.size()-xs.size()+ind, ys.c_ptr()+xs.size()-ind), m);
                expr_ref ys1y2 = mk_concat(ys1E, y2);
                propagate_eq(dep, lits, x, ys1y2, true);
            }
            return true;
        }
        else {
            TRACE("seq", tout << "base case: false branch\n";);
            continue;
        }
    }
    return change;
}

// Equation is of the form xs ++ x = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_ternary_variable2(eq const& e, bool flag1) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    bool is_ternary = is_ternary_eq2(e.ls(), e.rs(), xs, x, y1, ys, y2, flag1);
    if (!is_ternary) {
        is_ternary = is_ternary_eq2(e.rs(), e.ls(), xs, x, y1, ys, y2, flag1);
    }
    if (!is_ternary) {
        return false;
    }

    rational lenX, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x, lenX)) {
        enforce_length(x);
    }
    if (!get_length(y1, lenY1)) {
        enforce_length(y1);
    }
    if (!get_length(y2, lenY2)) {
        enforce_length(y2);
    }
    SASSERT(!xs.empty() && !ys.empty());
    unsigned_vector indexes = overlap2(xs, ys);
    if (branch_ternary_variable_base2(e.dep(), indexes, xs, x, y1, ys, y2))
        return true;
    
    // xs ++ x = y1 ++ ys ++ y2 => xs ++ z = y1, x = z ++ ys ++ y2 
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref ysy2 = mk_concat(ysE, y2);
    expr_ref Z(mk_skolem(m_seq_align, x, ysy2, y1, xsE), m);
    expr_ref xsZ = mk_concat(xsE, Z);
    expr_ref Zysy2 = mk_concat(Z, ysy2);
    if (indexes.empty()) {
        TRACE("seq", tout << "one case\n";);
        TRACE("seq", display_equation(tout, e););
        literal_vector lits;
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x, Zysy2, true);
        propagate_eq(dep, lits, y1, xsZ, true);
    }
    else {
        expr_ref ge(m_autil.mk_ge(mk_len(y1), m_autil.mk_int(xs.size())), m);
        literal lit2 = mk_literal(ge);
        if (ctx.get_assignment(lit2) == l_undef) {
            TRACE("seq", tout << "rec case init\n";);
            ctx.mark_as_relevant(lit2);
            ctx.force_phase(lit2);
        }
        else if (ctx.get_assignment(lit2) == l_true) {
            TRACE("seq", tout << "true branch\n";);
            TRACE("seq", display_equation(tout, e););
            literal_vector lits;
            lits.push_back(lit2);
            dependency* dep = e.dep();
            propagate_eq(dep, lits, x, Zysy2, true);
            propagate_eq(dep, lits, y1, xsZ, true);
        }
        else {
            return branch_ternary_variable_base2(e.dep(), indexes, xs, x, y1, ys, y2);
        }
    }

    return true;
}

bool theory_seq::branch_quat_variable() {
    for (auto const& e : m_eqs) {
        if (branch_quat_variable(e)) {
            return true;
        }
    }
    return false;
}

// Equation is of the form x1 ++ xs ++ x2 = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_quat_variable(eq const& e) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x1_l(m), x2(m), y1_l(m), y2(m);
    bool is_quat = is_quat_eq(e.ls(), e.rs(), x1_l, xs, x2, y1_l, ys, y2);
    if (!is_quat) {
        return false;
    }
    
    rational lenX1, lenX2, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x1_l, lenX1)) {
        enforce_length(x1_l);
    }
    if (!get_length(y1_l, lenY1)) {
        enforce_length(y1_l);
    }
    if (!get_length(x2, lenX2)) {
        enforce_length(x2);
    }
    if (!get_length(y2, lenY2)) {
        enforce_length(y2);
    }
    SASSERT(!xs.empty() && !ys.empty());
    
    xs.push_back(x2);
    expr_ref xsx2 = mk_concat(xs);
    ys.push_back(y2);
    expr_ref ysy2 = mk_concat(ys);
    expr_ref x1(x1_l, m);
    expr_ref y1(y1_l, m);
    expr_ref sub(mk_sub(mk_len(x1_l), mk_len(y1_l)), m);
    expr_ref le(m_autil.mk_le(sub, m_autil.mk_int(0)), m);
    literal lit2 = mk_literal(le);
    if (ctx.get_assignment(lit2) == l_undef) {
        TRACE("seq", tout << "init branch\n";);
        TRACE("seq", display_equation(tout, e););
        ctx.mark_as_relevant(lit2);
        ctx.force_phase(lit2);
    }
    else if (ctx.get_assignment(lit2) == l_false) {
        // |x1| > |y1| => x1 = y1 ++ z1, z1 ++ xs ++ x2 = ys ++ y2
        TRACE("seq", tout << "false branch\n";);
        TRACE("seq", display_equation(tout, e););
        expr_ref Z1(mk_skolem(m_seq_align, ysy2, xsx2, x1, y1), m);
        expr_ref y1Z1 = mk_concat(y1, Z1);
        expr_ref Z1xsx2 = mk_concat(Z1, xsx2);
        literal_vector lits;
        lits.push_back(~lit2);
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x1, y1Z1, true);
        propagate_eq(dep, lits, Z1xsx2, ysy2, true);
    }
    else if (ctx.get_assignment(lit2) == l_true) {
        // |x1| <= |y1| => x1 ++ z2 = y1, xs ++ x2 = z2 ++ ys ++ y2
        TRACE("seq", tout << "true branch\n";);
        TRACE("seq", display_equation(tout, e););
        expr_ref Z2(mk_skolem(m_seq_align, xsx2, ysy2, y1, x1), m);
        expr_ref x1Z2 = mk_concat(x1, Z2);
        expr_ref Z2ysy2 = mk_concat(Z2, ysy2);
        literal_vector lits;
        lits.push_back(lit2);
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x1Z2, y1, true);
        propagate_eq(dep, lits, xsx2, Z2ysy2, true);
    }
    return true;
}

void theory_seq::len_offset(expr* e, rational val) {
    context & ctx = get_context();
    expr *l1 = nullptr, *l2 = nullptr, *l21 = nullptr, *l22 = nullptr;
    rational fact;
    if (m_autil.is_add(e, l1, l2) && m_autil.is_mul(l2, l21, l22) &&
        m_autil.is_numeral(l21, fact) && fact.is_minus_one()) {
        if (ctx.e_internalized(l1) && ctx.e_internalized(l22)) {
            enode* r1 = get_root(l1), *n1 = r1;
            enode* r2 = get_root(l22), *n2 = r2;
            expr *e1 = nullptr, *e2 = nullptr;
            do {
                if (m_util.str.is_length(n1->get_owner(), e1))
                    break;
                n1 = n1->get_next();               
            }
            while (n1 != r1);
            do {
                if (m_util.str.is_length(n2->get_owner(), e2)) 
                    break;
                n2 = n2->get_next();                
            }
            while (n2 != r2);
            obj_map<enode, int> tmp;
            if (m_util.str.is_length(n1->get_owner(), e1)
                && m_util.str.is_length(n2->get_owner(), e2) &&                
                m_len_offset.find(r1, tmp)) {
                tmp.insert(r2, val.get_int32());
                m_len_offset.insert(r1, tmp);
                TRACE("seq", tout << "a length pair: " << mk_pp(e1, m) << ", " << mk_pp(e2, m) << "\n";);
                return;
            }
        }
    }
}

// Find the length offset from the congruence closure core
void theory_seq::prop_arith_to_len_offset() {
    context & ctx = get_context();
    obj_hashtable<enode> const_set;
    ptr_vector<enode>::const_iterator it  = ctx.begin_enodes();
    ptr_vector<enode>::const_iterator end = ctx.end_enodes();
    for (; it != end; ++it) {
        enode * root = (*it)->get_root();
        rational val;
        if (m_autil.is_numeral(root->get_owner(), val) && val.is_neg()) {
            if (const_set.contains(root)) continue;
            const_set.insert(root);
            TRACE("seq", tout << "offset: " << mk_pp(root->get_owner(), m) << "\n";);
            enode *next = root->get_next();
            while (next != root) {
                TRACE("seq", tout << "eqc: " << mk_pp(next->get_owner(), m) << "\n";);
                len_offset(next->get_owner(), val);
                next = next->get_next();
            }
        }
    }
}

int theory_seq::find_fst_non_empty_idx(expr_ref_vector const& xs) const {
    context & ctx = get_context();    
    for (unsigned i = 0; i < xs.size(); ++i) {
        expr* x = xs[i];
        if (!is_var(x)) return -1;
        expr_ref e = mk_len(x);
        if (ctx.e_internalized(e)) {
            enode* root = ctx.get_enode(e)->get_root();
            rational val;
            if (m_autil.is_numeral(root->get_owner(), val) && val.is_zero()) {
                continue;
            }
        }
        return i;
    }
    return -1;
}

expr* theory_seq::find_fst_non_empty_var(expr_ref_vector const& x) const {
    int i = find_fst_non_empty_idx(x);
    if (i >= 0)
        return x[i];
    return nullptr;
}

void theory_seq::find_max_eq_len(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    context& ctx = get_context();
    if (ls.size() >= 2 && rs.size() >= 2) {
        expr_ref len1(m_autil.mk_int(0), m), len2(m_autil.mk_int(0), m);
        int l_fst = find_fst_non_empty_idx(ls);
        int r_fst = find_fst_non_empty_idx(rs);
        if (l_fst<0 || r_fst<0)
            return;
        unsigned j = 2 + l_fst;
        rational lo1(-1), hi1(-1), lo2(-1), hi2(-1);
        if (j >= ls.size()) {
            lo1 = 0;
            hi1 = 0;
        }
        while (j < ls.size()) {
            rational lo(-1), hi(-1);
            if (m_util.str.is_unit(ls.get(j))) {
                lo = 1;
                hi = 1;
            }
            else {
                expr_ref len_s = mk_len(ls.get(j));
                lower_bound(len_s, lo);
                upper_bound(len_s, hi);
            }
            if (!lo.is_minus_one()) {
                if (lo1.is_minus_one())
                    lo1 = lo;
                else
                    lo1 += lo;
            }
            if (!hi.is_minus_one()) {
                if (hi1.is_minus_one())
                    hi1 = hi;
                else if (hi1.is_nonneg())
                    hi1 += hi;
            }
            else {
                hi1 = rational(-2);
            }
            len1 = mk_add(len1, mk_len(ls.get(j)));
            j++;
        }
        j = 2 + r_fst;
        if (j >= rs.size()) {
            lo2 = 0;
            hi2 = 0;
        }
        while (j < rs.size()) {
            rational lo(-1), hi(-1);
            if (m_util.str.is_unit(rs.get(j))) {
                lo = 1;
                hi = 1;
            }
            else {
                expr_ref len_s = mk_len(rs.get(j));
                lower_bound(len_s, lo);
                upper_bound(len_s, hi);
            }
            if (!lo.is_minus_one()) {
                if (lo2.is_minus_one())
                    lo2 = lo;
                else
                    lo2 += lo;
            }
            if (!hi.is_minus_one()) {
                if (hi2.is_minus_one())
                    hi2 = hi;
                else if (hi1.is_nonneg())
                    hi2 += hi;
            }
            else {
                hi2 = rational(-2);
            }
            len2 = mk_add(len2, mk_len(rs.get(j)));
            j++;
        }
        if (m_autil.is_numeral(len1) && m_autil.is_numeral(len2))
            return;
        TRACE("seq", tout << lo1 << ", " << hi1 << ", " << lo2 << ", " << hi2 << "\n";);
        if (!lo1.is_neg() && !hi2.is_neg() && lo1 > hi2)
            return;
        if (!lo2.is_neg() && !hi1.is_neg() && lo2 > hi1)
            return;

        literal lit1 = null_literal;
        if (hi1.is_zero()) {
            if (!is_var(rs[1 + r_fst]))
                return;
            lit1 = mk_literal(m_autil.mk_le(len2, len1));
            TRACE("seq", tout << mk_pp(len1, m) << " >= " << mk_pp(len2, m) << "\n";);
        }
        else if (hi2.is_zero()) {
            if (!is_var(ls[1 + l_fst]))
                return;
            lit1 = mk_literal(m_autil.mk_le(len1, len2));
            TRACE("seq", tout << mk_pp(len1, m) << " <= " << mk_pp(len2, m) << "\n";);
        }
        else {
            lit1 = mk_eq(len1, len2, false);
            TRACE("seq", tout << mk_pp(len1, m) << " = " << mk_pp(len2, m) << "\n";);
        }
        if (ctx.get_assignment(lit1) == l_undef) {
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
        }
    }
}

// TODO: propagate length offsets for last vars
bool theory_seq::find_better_rep(expr_ref_vector const& ls, expr_ref_vector const& rs, unsigned idx,
                                 dependency*& deps, expr_ref_vector & res) {
    context& ctx = get_context();

    if (ls.empty() || rs.empty())
        return false;
    expr* l_fst = find_fst_non_empty_var(ls);
    expr* r_fst = find_fst_non_empty_var(rs);
    if (!r_fst) return false;
    expr_ref len_r_fst = mk_len(r_fst);
    expr_ref len_l_fst(m);
    enode * root2;
    if (!ctx.e_internalized(len_r_fst)) {
        return false;
    }
    if (l_fst) {
        len_l_fst = mk_len(l_fst);
    }

    root2 = get_root(len_r_fst);

    // Offset = 0, No change
    if (l_fst && get_root(len_l_fst) == root2) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        return false;
    }

    // Offset = 0, Changed

    for (unsigned i = 0; i < idx; ++i) {
        eq const& e = m_eqs[i];
        if (e.ls() != ls) continue;
        expr* nl_fst = nullptr;
        if (e.rs().size() > 1 && is_var(e.rs().get(0)))
            nl_fst = e.rs().get(0);
        if (nl_fst && nl_fst != r_fst && root2 == get_root(mk_len(nl_fst))) {
            res.reset();
            res.append(e.rs().size(), e.rs().c_ptr());
            deps = m_dm.mk_join(e.dep(), deps);
            return true;
        }
    }
    // Offset != 0, No change
    if (l_fst && ctx.e_internalized(len_l_fst)) {
        enode * root1 = get_root(len_l_fst);
        obj_map<enode, int> tmp;
        int offset;
        if (!m_autil.is_numeral(root1->get_owner()) && !m_autil.is_numeral(root2->get_owner())) {
            if (m_len_offset.find(root1, tmp) && tmp.find(root2, offset)) {
                TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
                find_max_eq_len(ls, rs);
                return false;
            }
            else if (m_len_offset.find(root2, tmp) && tmp.find(root1, offset)) {
                TRACE("seq", tout << "(" << mk_pp(r_fst, m) << ", " << mk_pp(l_fst,m) << ")\n";);
                find_max_eq_len(ls ,rs);
                return false;
            }
        }
    }
    // Offset != 0, Changed
    obj_map<enode, int> tmp;
    if (!m_autil.is_numeral(root2->get_owner()) && m_len_offset.find(root2, tmp)) {
        for (unsigned i = 0; i < idx; ++i) {
            eq const& e = m_eqs[i];
            if (e.ls() != ls) continue;
            expr* nl_fst = nullptr;
            if (e.rs().size()>1 && is_var(e.rs().get(0)))
                nl_fst = e.rs().get(0);
            if (nl_fst && nl_fst != r_fst) {
                int offset;
                expr_ref len_nl_fst = mk_len(nl_fst);
                if (ctx.e_internalized(len_nl_fst)) {
                    enode * root1 = ctx.get_enode(len_nl_fst)->get_root();
                    if (!m_autil.is_numeral(root1->get_owner()) && tmp.find(root1, offset)) {
                        res.reset();
                        res.append(e.rs().size(), e.rs().c_ptr());
                        deps = m_dm.mk_join(e.dep(), deps);
                        find_max_eq_len(res, rs);
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

bool theory_seq::has_len_offset(expr_ref_vector const& ls, expr_ref_vector const& rs, int & offset) {
    context& ctx = get_context();

    if (ls.empty() || rs.empty()) 
        return false;
    expr* l_fst = ls[0];
    expr* r_fst = rs[0];
    if (!is_var(l_fst) || !is_var(r_fst)) 
        return false;

    expr_ref len_l_fst = mk_len(l_fst);
    if (!ctx.e_internalized(len_l_fst)) 
        return false;
    enode * root1 = ctx.get_enode(len_l_fst)->get_root();

    expr_ref len_r_fst = mk_len(r_fst);
    if (!ctx.e_internalized(len_r_fst))
        return false;
    enode* root2 = ctx.get_enode(len_r_fst)->get_root();

    if (root1 == root2) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        offset = 0;
        return true;
    }

    if (m_autil.is_numeral(root1->get_owner()) || m_autil.is_numeral(root2->get_owner())) 
        return false;

    obj_map<enode, int> tmp;
    if (m_len_offset.find(root1, tmp) && tmp.find(root2, offset)) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        return true;
    }
    if (m_len_offset.find(root2, tmp) && tmp.find(root1, offset)) {
        offset = -offset;
        TRACE("seq", tout << "(" << mk_pp(r_fst, m) << ", " << mk_pp(l_fst,m) << ")\n";);
        return true;
    }
    return false;
}

bool theory_seq::len_based_split() {
    unsigned sz = m_eqs.size();
    if (sz == 0)
        return false;

    if ((int) get_context().get_scope_level() > m_len_prop_lvl) {
        m_len_prop_lvl = get_context().get_scope_level();
        prop_arith_to_len_offset();
        if (!m_len_offset.empty()) {
            for (unsigned i = sz-1; i > 0; --i) {
                eq const& e = m_eqs[i];
                expr_ref_vector new_ls(m);
                dependency *deps = e.dep();
                if (find_better_rep(e.ls(), e.rs(), i, deps, new_ls)) {
                    expr_ref_vector rs(m);
                    rs.append(e.rs().size(), e.rs().c_ptr());
                    m_eqs.set(i, eq(m_eq_id++, new_ls, rs, deps));
                    TRACE("seq", display_equation(tout, m_eqs[i]););
                }
            }
        }
    }

    for (auto const& e : m_eqs) {
        if (len_based_split(e)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::len_based_split(eq const& e) {
    context& ctx = get_context();
    expr_ref_vector const& ls = e.ls();
    expr_ref_vector const& rs = e.rs();
    
    int offset_orig = 0;
    if (!has_len_offset(ls, rs, offset_orig))
        return false;
        
    TRACE("seq", tout << "split based on length\n";);
    TRACE("seq", display_equation(tout, e););
    expr_ref x11(m_util.str.mk_concat(1, ls.c_ptr()), m);
    expr_ref x12(m_util.str.mk_concat(ls.size()-1, ls.c_ptr()+1), m);
    expr_ref y11(m_util.str.mk_concat(1, rs.c_ptr()), m);
    expr_ref y12(m_util.str.mk_concat(rs.size()-1, rs.c_ptr()+1), m);

    expr_ref lenX11 = mk_len(x11);
    expr_ref lenY11(m);
    expr_ref Z(m);
    int offset = 0;
    if (offset_orig != 0) {
        lenY11 = m_autil.mk_add(mk_len(y11), m_autil.mk_int(offset_orig));
        if (offset_orig > 0) {
            offset = offset_orig;
            Z = mk_skolem(m_seq_align, y12, x12, x11, y11);
            y11 = mk_concat(y11, Z);
            x12 = mk_concat(Z, x12);
        }
        else {
            offset = -offset_orig;
            Z = mk_skolem(m_seq_align, x12, y12, y11, x11);
            x11 = mk_concat(x11, Z);
            y12 = mk_concat(Z, y12);
        }
    }
    else {
        lenY11 = mk_len(y11);
    }

    dependency* dep = e.dep();
    literal_vector lits;
    literal lit1 = mk_eq(lenX11, lenY11, false);
    if (ctx.get_assignment(lit1) != l_true) {
        return false;
    }
    lits.push_back(lit1);

    if (ls.size() >= 2 && rs.size() >= 2 && (ls.size() > 2 || rs.size() > 2)) {
        expr_ref len1(m_autil.mk_int(0),m), len2(m_autil.mk_int(0),m);
        for (unsigned i = 2; i < ls.size(); ++i) {
            len1 = mk_add(len1, mk_len(ls[i]));
        }
        for (unsigned i = 2; i < rs.size(); ++i) {
            len2 = mk_add(len2, mk_len(rs[i]));
        }
        literal lit2;
        if (!m_autil.is_numeral(len1) && !m_autil.is_numeral(len2)) {
            lit2 = mk_eq(len1, len2, false);           
        }
        else {
            expr_ref eq_len(m.mk_eq(len1, len2), m);
            lit2 = mk_literal(eq_len);            
        }
        
        if (ctx.get_assignment(lit2) == l_true) {           
            lits.push_back(lit2);
            TRACE("seq", tout << mk_pp(len1, m) << " = " << mk_pp(len2, m) << "\n";);
            expr_ref lhs(m), rhs(m);
            if (ls.size() > 2)
                lhs = m_util.str.mk_concat(ls.size()-2, ls.c_ptr()+2);
            else
                lhs = m_util.str.mk_empty(m.get_sort(x11));
            if (rs.size() > 2)
                rhs = m_util.str.mk_concat(rs.size()-2, rs.c_ptr()+2);
            else
                rhs = m_util.str.mk_empty(m.get_sort(x11));
            propagate_eq(dep, lits, lhs, rhs, true);
            lits.pop_back();
        }
    }

    if (offset != 0) {
        expr_ref lenZ = mk_len(Z);
        propagate_eq(dep, lits, lenZ, m_autil.mk_int(offset), false);
    }
    propagate_eq(dep, lits, y11, x11, true);
    propagate_eq(dep, lits, x12, y12, false);

    return true;
}

/**
   \brief select branching on variable equality.
   preference mb > eq > ternary > quat
   this performs much better on #1628
*/
bool theory_seq::branch_variable() {
    if (branch_variable_mb()) return true;
    if (branch_variable_eq()) return true;
    if (branch_ternary_variable1()) return true;
    if (branch_ternary_variable2()) return true;
    if (branch_quat_variable()) return true;
    return false;
}

bool theory_seq::branch_variable_mb() {
    bool change = false;
    for (auto const& e : m_eqs) {
        vector<rational> len1, len2;
        if (!is_complex(e)) {
            continue;
        }
        if (e.ls().empty() || e.rs().empty() || 
            (!is_var(e.ls()[0]) && !is_var(e.rs()[0]))) {
            continue;
        }

        if (!enforce_length(e.ls(), len1) || !enforce_length(e.rs(), len2)) {
            change = true;
            continue;
        }
        rational l1, l2;
        for (const auto& elem : len1) l1 += elem;
        for (const auto& elem : len2) l2 += elem;
        if (l1 != l2) {
            TRACE("seq", tout << "lengths are not compatible\n";);
            expr_ref l = mk_concat(e.ls());
            expr_ref r = mk_concat(e.rs());
            expr_ref lnl = mk_len(l), lnr = mk_len(r);
            propagate_eq(e.dep(), lnl, lnr, false);
            change = true;
            continue;
        }
        if (split_lengths(e.dep(), e.ls(), e.rs(), len1, len2)) {
            TRACE("seq", tout << "split lengths\n";);
            change = true;
            break;
        }
    }
    CTRACE("seq", change, tout << "branch_variable_mb\n";);
    return change;
}


bool theory_seq::is_complex(eq const& e) {
    unsigned num_vars1 = 0, num_vars2 = 0;
    for (auto const& elem : e.ls()) {
        if (is_var(elem)) ++num_vars1;
    }
    for (auto const& elem : e.rs()) {
        if (is_var(elem)) ++num_vars2;
    }
    return num_vars1 > 0 && num_vars2 > 0 && num_vars1 + num_vars2 > 2;
}

/*
  \brief Decompose ls = rs into Xa = bYc, such that 
   1. 
    - X != Y
    - |b| <= |X| <= |bY| in current model
    - b is non-empty.
   2. X != Y
    - b is empty
    - |X| <= |Y|
   3. |X| = 0
      - propagate X = empty      
*/
bool theory_seq::split_lengths(dependency* dep,
                               expr_ref_vector const& ls, expr_ref_vector const& rs, 
                               vector<rational> const& ll, vector<rational> const& rl) {
    context& ctx = get_context();
    expr_ref X(m), Y(m), b(m);
    if (ls.empty() || rs.empty()) {
        return false;
    } 
    if (is_var(ls[0]) && ll[0].is_zero()) {
        return set_empty(ls[0]);
    }
    if (is_var(rs[0]) && rl[0].is_zero()) {
        return set_empty(rs[0]);
    }
    if (is_var(rs[0]) && !is_var(ls[0])) {
        return split_lengths(dep, rs, ls, rl, ll);
    }
    if (!is_var(ls[0])) {
        return false;
    }
    X = ls[0];
    rational lenX = ll[0];
    expr_ref_vector bs(m);
    SASSERT(lenX.is_pos());
    rational lenB(0), lenY(0);
    for (unsigned i = 0; lenX > lenB && i < rs.size(); ++i) {
        bs.push_back(rs[i]);
        lenY = rl[i];
        lenB += lenY;
    }
    SASSERT(lenX <= lenB);
    SASSERT(!bs.empty());
    Y = bs.back();
    bs.pop_back();
    if (!is_var(Y) && !m_util.str.is_unit(Y)) {
        TRACE("seq", tout << "TBD: non variable or unit split: " << Y << "\n";);
        return false;
    }
    if (X == Y) {
        TRACE("seq", tout << "Cycle: " << X << "\n";);
        return false;
    }
    if (lenY.is_zero()) {
        return set_empty(Y);
    }
    b = mk_concat(bs, m.get_sort(X));

    SASSERT(X != Y);


    // |b| < |X| <= |b| + |Y| => x = bY1, Y = Y1Y2
    expr_ref lenXE = mk_len(X);
    expr_ref lenYE = mk_len(Y);
    expr_ref lenb = mk_len(b);
    expr_ref le1(m_autil.mk_le(mk_sub(lenXE, lenb), m_autil.mk_int(0)), m);
    expr_ref le2(m_autil.mk_le(mk_sub(mk_sub(lenXE, lenb), lenYE), 
                               m_autil.mk_int(0)), m);
    literal  lit1(~mk_literal(le1));
    literal  lit2(mk_literal(le2));
    literal_vector lits;
    lits.push_back(lit1);
    lits.push_back(lit2);
    
    if (ctx.get_assignment(lit1) != l_true ||
        ctx.get_assignment(lit2) != l_true) {
        ctx.mark_as_relevant(lit1);
        ctx.mark_as_relevant(lit2);
    }
    else if (m_util.str.is_unit(Y)) {
        SASSERT(lenB == lenX);
        bs.push_back(Y);
        expr_ref bY(m_util.str.mk_concat(bs), m);
        propagate_eq(dep, lits, X, bY, true);
    }
    else {
        SASSERT(is_var(Y));
        expr_ref Y1(mk_skolem(symbol("seq.left"), X, b, Y), m);
        expr_ref Y2(mk_skolem(symbol("seq.right"), X, b, Y), m);
        expr_ref bY1 = mk_concat(b, Y1);
        expr_ref Y1Y2 = mk_concat(Y1, Y2);
        propagate_eq(dep, lits, X, bY1, true);
        propagate_eq(dep, lits, Y, Y1Y2, true);
    }
    return true;
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
            enforce_length(e);
            all_have_length = false;
        }
    }
    return all_have_length;
}

bool theory_seq::branch_variable_eq() {
    context& ctx = get_context();
    unsigned sz = m_eqs.size();
    int start = ctx.get_random_value();

    for (unsigned i = 0; i < sz; ++i) {
        unsigned k = (i + start) % sz;
        eq const& e = m_eqs[k];

        if (branch_variable_eq(e)) {
            TRACE("seq", tout << "branch variable\n";);
            return true;
        }
    }
    return ctx.inconsistent();
}

bool theory_seq::branch_variable_eq(eq const& e) {
    unsigned id = e.id();
    unsigned s = find_branch_start(2*id);
    TRACE("seq", tout << s << " " << id << ": " << e.ls() << " = " << e.rs() << "\n";);
    bool found = find_branch_candidate(s, e.dep(), e.ls(), e.rs());
    insert_branch_start(2*id, s);
    if (found) {
        return true;
    }
    s = find_branch_start(2*id + 1);
    found = find_branch_candidate(s, e.dep(), e.rs(), e.ls());
    insert_branch_start(2*id + 1, s);
    
    return found;
}

void theory_seq::insert_branch_start(unsigned k, unsigned s) {
    m_branch_start.insert(k, s);
    m_trail_stack.push(pop_branch(k));
}

unsigned theory_seq::find_branch_start(unsigned k) {
    unsigned s = 0;
    if (m_branch_start.find(k, s)) {
        return s;
    }
    return 0;
}

expr_ref_vector theory_seq::expand_strings(expr_ref_vector const& es) {
    expr_ref_vector ls(m);
    for (expr* e : es) {
        zstring s;
        if (m_util.str.is_string(e, s)) {
            for (unsigned i = 0; i < s.length(); ++i) {
                ls.push_back(m_util.str.mk_unit(m_util.str.mk_char(s, i)));
            }
        }
        else {
            ls.push_back(e);
        }
    }
    return ls;
}

bool theory_seq::find_branch_candidate(unsigned& start, dependency* dep, expr_ref_vector const& _ls, expr_ref_vector const& _rs) {
    expr_ref_vector ls = expand_strings(_ls);
    expr_ref_vector rs = expand_strings(_rs);

    if (ls.empty()) {
        return false;
    }
    expr* l = ls.get(0);

    if (!is_var(l)) {
        return false;
    }

    TRACE("seq", tout << mk_pp(l, m) << ": " << get_context().get_scope_level() << " - start:" << start << "\n";);

    expr_ref v0(m);
    v0 = m_util.str.mk_empty(m.get_sort(l));
    if (can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size(), rs.c_ptr())) {
        if (l_false != assume_equality(l, v0)) {
            TRACE("seq", tout << mk_pp(l, m) << " " << v0 << "\n";);
            return true;
        }
    }
    for (; start < rs.size(); ++start) {
        unsigned j = start;
        SASSERT(!m_util.str.is_concat(rs.get(j)));
        SASSERT(!m_util.str.is_string(rs.get(j)));
        if (l == rs.get(j)) {
            return false;
        }
        if (!can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size() - j - 1, rs.c_ptr() + j + 1)) {
            continue;
        }
        v0 = mk_concat(j + 1, rs.c_ptr());
        if (l_false != assume_equality(l, v0)) {
            TRACE("seq", tout << mk_pp(l, m) << " " << v0 << "\n";);
            ++start;
            return true;
        }
    }

    bool all_units = true;
    for (expr* r : rs) {
        if (!m_util.str.is_unit(r)) {
            all_units = false;
            break;
        }
    }
    if (all_units) {
        context& ctx = get_context();
        literal_vector lits;
        lits.push_back(~mk_eq_empty(l));
        for (unsigned i = 0; i < rs.size(); ++i) {
            if (can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size() - i - 1, rs.c_ptr() + i + 1)) {
                v0 = mk_concat(i + 1, rs.c_ptr());
                lits.push_back(~mk_eq(l, v0, false));
            }
        }
        for (literal lit : lits) {
            switch (ctx.get_assignment(lit)) {
            case l_true:  break;
            case l_false: start = 0; return true;
            case l_undef: ctx.force_phase(~lit); start = 0; return true;
            }
        }
        set_conflict(dep, lits);
        TRACE("seq", 
              tout << "start: " << start << "\n";
              for (literal lit : lits) {
                  ctx.display_literal_verbose(tout << lit << ": ", lit) << "\n";
                  ctx.display(tout, ctx.get_justification(lit.var())); tout << "\n";
              });
        return true;
    }
    return false;
}

bool theory_seq::can_be_equal(unsigned szl, expr* const* ls, unsigned szr, expr* const* rs) const {
    unsigned i = 0;
    for (; i < szl && i < szr; ++i) {
        if (m.are_distinct(ls[i], rs[i])) {
            return false;
        }
        if (!m.are_equal(ls[i], rs[i])) {
            break;
        }
    }
    if (i == szr) {
        std::swap(ls, rs);
        std::swap(szl, szr);
    }
    if (i == szl && i < szr) {
        for (; i < szr; ++i) {
            if (m_util.str.is_unit(rs[i])) {
                return false;
            }
        }
    }
    return true;
}


lbool theory_seq::assume_equality(expr* l, expr* r) {
    context& ctx = get_context();
    if (m_exclude.contains(l, r)) {
        return l_false;
    }

    expr_ref eq(m.mk_eq(l, r), m);
    m_rewrite(eq);
    if (m.is_true(eq)) {
        return l_true;
    }
    if (m.is_false(eq)) {
        return l_false;
    }

    TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << "\n";);
    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() == n2->get_root()) {
        return l_true;
    }
    if (ctx.is_diseq(n1, n2)) {
        return l_false;
    }
    if (false && ctx.is_diseq_slow(n1, n2)) {
        return l_false;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    if (!ctx.assume_eq(n1, n2)) {
        return l_false;
    }
    return ctx.get_assignment(mk_eq(l, r, false));
}


bool theory_seq::propagate_length_coherence(expr* e) {
    expr_ref head(m), tail(m);
    rational lo, hi;

    if (!is_var(e) || !m_rep.is_root(e)) {
        return false;
    }
    if (!lower_bound2(e, lo) || !lo.is_pos() || lo >= rational(2048)) {
        return false;
    }
    TRACE("seq", tout << "Unsolved " << mk_pp(e, m);
          if (!lower_bound2(e, lo)) lo = -rational::one();
          if (!upper_bound(mk_len(e), hi)) hi = -rational::one();
          tout << " lo: " << lo << " hi: " << hi << "\n";
          );

    expr_ref seq(e, m);
    expr_ref_vector elems(m);
    unsigned _lo = lo.get_unsigned();
    for (unsigned j = 0; j < _lo; ++j) {
        mk_decompose(seq, head, tail);
        elems.push_back(head);
        seq = tail;
    }
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
    elems.push_back(seq);
    tail = mk_concat(elems.size(), elems.c_ptr());
    // len(e) >= low => e = tail;
    literal low(mk_literal(m_autil.mk_ge(mk_len(e), m_autil.mk_numeral(lo, true))));
    add_axiom(~low, mk_seq_eq(e, tail));
    expr_ref len_e = mk_len(e);
    if (upper_bound(len_e, hi)) {
        // len(e) <= hi => len(tail) <= hi - lo
        expr_ref high1(m_autil.mk_le(len_e, m_autil.mk_numeral(hi, true)), m);
        if (hi == lo) {
            add_axiom(~mk_literal(high1), mk_seq_eq(seq, emp));
        }
        else {
            expr_ref high2(m_autil.mk_le(mk_len(seq), m_autil.mk_numeral(hi-lo, true)), m);
            add_axiom(~mk_literal(high1), mk_literal(high2));
        }
    }
    else {
        assume_equality(seq, emp);
    }
    return true;
}


bool theory_seq::check_length_coherence(expr* e) {
    if (is_var(e) && m_rep.is_root(e)) {
        if (!check_length_coherence0(e)) {
            expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
            expr_ref head(m), tail(m);
            // e = emp \/ e = unit(head.elem(e))*tail(e)
            mk_decompose(e, head, tail);
            expr_ref conc = mk_concat(head, tail);
            if (propagate_is_conc(e, conc)) {
                assume_equality(tail, emp);
            }
        }
        return true;
    }
    return false;
}

bool theory_seq::check_length_coherence0(expr* e) {
    if (is_var(e) && m_rep.is_root(e)) {
        expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
        if (propagate_length_coherence(e) ||
            l_false != assume_equality(e, emp)) {
            if (!get_context().at_base_level()) {
                m_trail_stack.push(push_replay(alloc(replay_length_coherence, m, e)));
            }
            return true;
        }
    }
    return false;
}

bool theory_seq::check_length_coherence() {

#if 1
    for (expr* l : m_length) {
        expr* e = nullptr;
        VERIFY(m_util.str.is_length(l, e));
        if (check_length_coherence0(e)) {
            return true;
        }
    }
#endif
    for (expr* l : m_length) {
        expr* e = nullptr;
        VERIFY(m_util.str.is_length(l, e));
        if (check_length_coherence(e)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::fixed_length(bool is_zero) {
    bool found = false;
    for (auto e : m_length) {
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
    if (is_skolem(m_tail, e) || is_skolem(m_seq_first, e) || 
        is_skolem(m_indexof_left, e) || is_skolem(m_indexof_right, e) ||
        m_fixed.contains(e)) {
        return false;
    }


    context& ctx = get_context();
    
    m_trail_stack.push(insert_obj_trail<theory_seq, expr>(m_fixed, e));
    m_fixed.insert(e);

    expr_ref seq(e, m), head(m), tail(m);

    if (lo.is_zero()) {
        seq = m_util.str.mk_empty(m.get_sort(e));
    }
    else if (!is_zero) {
        unsigned _lo = lo.get_unsigned();
        expr_ref_vector elems(m);
        
        for (unsigned j = 0; j < _lo; ++j) {
            mk_decompose(seq, head, tail);
            elems.push_back(head);
            seq = tail;
        }
        seq = mk_concat(elems.size(), elems.c_ptr());
    }
    TRACE("seq", tout << "Fixed: " << mk_pp(e, m) << " " << lo << "\n";);
    add_axiom(~mk_eq(len_e, m_autil.mk_numeral(lo, true), false), mk_seq_eq(seq, e));
    if (!ctx.at_base_level()) {
        m_trail_stack.push(push_replay(alloc(replay_fixed_length, m, len_e)));
    }
    return true;
}


/*
    lit => s != ""
*/
void theory_seq::propagate_non_empty(literal lit, expr* s) {
    SASSERT(get_context().get_assignment(lit) == l_true);
    propagate_lit(nullptr, 1, &lit, ~mk_eq_empty(s));
}

bool theory_seq::propagate_is_conc(expr* e, expr* conc) {
    TRACE("seq", tout << mk_pp(conc, m) << " is non-empty\n";);
    context& ctx = get_context();
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
    return m_util.str.is_unit(e, s) && is_nth(s);
}

bool theory_seq::is_nth(expr* e) const {
    return m_util.str.is_nth(e);
}

bool theory_seq::is_nth(expr* e, expr*& e1, expr*& e2) const {
    return m_util.str.is_nth(e, e1, e2);
}

bool theory_seq::is_tail(expr* e, expr*& s, unsigned& idx) const {
    rational r;
    return
        is_skolem(m_tail, e) &&
        m_autil.is_numeral(to_app(e)->get_arg(1), r) &&
        (idx = r.get_unsigned(), s = to_app(e)->get_arg(0), true);
}

bool theory_seq::is_eq(expr* e, expr*& a, expr*& b) const {
    return is_skolem(m_eq, e) &&
        (a = to_app(e)->get_arg(0), b = to_app(e)->get_arg(1), true);
}

bool theory_seq::is_pre(expr* e, expr*& s, expr*& i) {
    return is_skolem(m_pre, e) && (s = to_app(e)->get_arg(0), i = to_app(e)->get_arg(1), true);
}

bool theory_seq::is_post(expr* e, expr*& s, expr*& i) {
    return is_skolem(m_post, e) && (s = to_app(e)->get_arg(0), i = to_app(e)->get_arg(1), true);
}



expr_ref theory_seq::mk_nth(expr* s, expr* idx) {
    expr_ref result(m_util.str.mk_nth(s, idx), m);
    if (!m_internal_nth_table.contains(result)) {
        m_internal_nth_table.insert(result);
        m_internal_nth_es.push_back(result);
    }
    return result;
}

expr_ref theory_seq::mk_sk_ite(expr* c, expr* t, expr* e) {
    return mk_skolem(symbol("seq.if"), c, t, e, nullptr, m.get_sort(t));
}

expr_ref theory_seq::mk_last(expr* s) {
    zstring str;
    if (m_util.str.is_string(s, str) && str.length() > 0) {
        return expr_ref(m_util.str.mk_char(str, str.length()-1), m);
    }
    sort* char_sort = nullptr;
    VERIFY(m_util.is_seq(m.get_sort(s), char_sort));
    return mk_skolem(m_seq_last, s, nullptr, nullptr, nullptr, char_sort);
}

expr_ref theory_seq::mk_first(expr* s) {
    zstring str;
    if (m_util.str.is_string(s, str) && str.length() > 0) {
        return expr_ref(m_util.str.mk_string(str.extract(0, str.length()-1)), m);
    }
    return mk_skolem(m_seq_first, s);
}


void theory_seq::mk_decompose(expr* e, expr_ref& head, expr_ref& tail) {
    expr* e1 = nullptr, *e2 = nullptr;
    zstring s;
    rational r;
    if (m_util.str.is_empty(e)) {
        head = m_util.str.mk_unit(mk_nth(e, m_autil.mk_int(0)));
        tail = e;
    }
    else if (m_util.str.is_string(e, s)) {
        head = m_util.str.mk_unit(m_util.str.mk_char(s, 0));
        tail = m_util.str.mk_string(s.extract(1, s.length()-1));
    }
    else if (m_util.str.is_unit(e)) {
        head = e;
        tail = m_util.str.mk_empty(m.get_sort(e));
    }
    else if (m_util.str.is_concat(e, e1, e2) && m_util.str.is_unit(e1)) {
        head = e1;
        tail = e2;
    }
    else if (is_skolem(m_tail, e) && m_autil.is_numeral(to_app(e)->get_arg(1), r)) {        
        app* a = to_app(e);
        expr* s = a->get_arg(0);        
        expr* idx = m_autil.mk_int(r.get_unsigned() + 1);
        head = m_util.str.mk_unit(mk_nth(s, idx));
        tail = mk_skolem(m_tail, s, idx);
    }
    else {
        head = m_util.str.mk_unit(mk_nth(e, m_autil.mk_int(0)));
        tail = mk_skolem(m_tail, e, m_autil.mk_int(0));
    }
}

/*
   \brief Check extensionality (for sequences).
 */
bool theory_seq::check_extensionality() {
    context& ctx = get_context();
    unsigned sz = get_num_vars();
    unsigned_vector seqs;
    for (unsigned v = 0; v < sz; ++v) {
        enode* n1 = get_enode(v);
        expr* o1 = n1->get_owner();
        if (n1 != n1->get_root()) {
            continue;
        }
        if (!seqs.empty() && ctx.is_relevant(n1) && m_util.is_seq(o1) && ctx.is_shared(n1)) {
            dependency* dep = nullptr;
            expr_ref e1 = canonize(o1, dep);
            for (unsigned i = 0; i < seqs.size(); ++i) {
                enode* n2 = get_enode(seqs[i]);
                expr* o2 = n2->get_owner();
                if (m.get_sort(o1) != m.get_sort(o2)) {
                    continue;
                }
                if (ctx.is_diseq(n1, n2) || m_exclude.contains(o1, o2)) {
                    continue;
                }
                expr_ref e2 = canonize(n2->get_owner(), dep);
                m_lhs.reset(); m_rhs.reset();
                bool change = false;
                if (!m_seq_rewrite.reduce_eq(e1, e2, m_lhs, m_rhs, change)) {
                    m_exclude.update(o1, o2);
                    continue;
                }
                bool excluded = false;
                for (unsigned j = 0; !excluded && j < m_lhs.size(); ++j) {
                    if (m_exclude.contains(m_lhs[j].get(), m_rhs[j].get())) {
                        excluded = true;
                    }
                }
                if (excluded) {
                    continue;
                }
                TRACE("seq", tout << m_lhs << " = " << m_rhs << "\n";);
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
    context & ctx = get_context();
    for (unsigned i = 0; !ctx.inconsistent() && i < m_ncs.size(); ++i) {
        if (solve_nc(i)) {
            if (i + 1 != m_ncs.size()) {
                nc n = m_ncs[m_ncs.size()-1];
                m_ncs.set(i, n);
                --i;
            }
            m_ncs.pop_back();
        }
    }
    return m_new_propagation || ctx.inconsistent();
}
/*
   - Eqs = 0
   - Diseqs evaluate to false
   - lengths are coherent.
*/

bool theory_seq::is_solved() {
    if (!m_eqs.empty()) {
        TRACE("seq", tout << "(seq.giveup " << m_eqs[0].ls() << " = " << m_eqs[0].rs() << " is unsolved)\n";);
        IF_VERBOSE(10, verbose_stream() << "(seq.giveup " << m_eqs[0].ls() << " = " << m_eqs[0].rs() << " is unsolved)\n";);
        return false;
    }
    for (unsigned i = 0; i < m_automata.size(); ++i) {
        if (!m_automata[i]) {
            TRACE("seq", tout  << "(seq.giveup regular expression did not compile to automaton)\n";);
            IF_VERBOSE(10, verbose_stream() << "(seq.giveup regular expression did not compile to automaton)\n";);
            return false;
        }
    }
    if (false && !m_nqs.empty()) {
        TRACE("seq", display_disequation(tout << "(seq.giveup ", m_nqs[0]); tout << " is unsolved)\n";);
        IF_VERBOSE(10, display_disequation(verbose_stream() << "(seq.giveup ", m_nqs[0]); verbose_stream() << " is unsolved)\n";);
        return false;
    }
    if (!m_ncs.empty()) {
        TRACE("seq", display_nc(tout << "(seq.giveup ", m_ncs[0]); tout << " is unsolved)\n";);
        IF_VERBOSE(10, display_nc(verbose_stream() << "(seq.giveup ", m_ncs[0]); verbose_stream() << " is unsolved)\n";);
        return false;
    }

    return true;
}

/**
   \brief while extracting dependency literals ensure that they have all been asserted on the context.
*/
bool theory_seq::linearize(dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const {
    context & ctx = get_context();    
    DEBUG_CODE(for (literal lit : lits) SASSERT(ctx.get_assignment(lit) == l_true); );
    bool asserted = true;
    svector<assumption> assumptions;
    const_cast<dependency_manager&>(m_dm).linearize(dep, assumptions);
    for (assumption const& a : assumptions) {
        if (a.lit != null_literal) {
            lits.push_back(a.lit);
            asserted &= ctx.get_assignment(a.lit) == l_true;
        }
        if (a.n1 != nullptr) {
            eqs.push_back(enode_pair(a.n1, a.n2));
        }
    }
    return asserted;
}



void theory_seq::propagate_lit(dependency* dep, unsigned n, literal const* _lits, literal lit) {
    if (lit == true_literal) return;

    context& ctx = get_context();
    literal_vector lits(n, _lits);

    if (lit == false_literal) {
        set_conflict(dep, lits);
        return;
    }

    ctx.mark_as_relevant(lit);
    enode_pair_vector eqs;
    if (!linearize(dep, eqs, lits)) 
        return;
    TRACE("seq",
          tout << "scope: " << ctx.get_scope_level() << "\n";
          ctx.display_detailed_literal(tout << "assert:", lit);
          ctx.display_literals_verbose(tout << " <- ", lits);
          if (!lits.empty()) tout << "\n"; display_deps(tout, dep););
    justification* js =
        ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), lit));

    m_new_propagation = true;
    ctx.assign(lit, js);    
    if (m.has_trace_stream()) {
        expr_ref expr(m);
        expr = ctx.bool_var2expr(lit.var());
        if (lit.sign()) expr = m.mk_not(expr);
        log_axiom_instantiation(expr);
        m.trace_stream() << "[end-of-instance]\n";
    }
}

void theory_seq::set_conflict(dependency* dep, literal_vector const& _lits) {
    context& ctx = get_context();
    enode_pair_vector eqs;
    literal_vector lits(_lits);
    if (!linearize(dep, eqs, lits)) 
        return;
    TRACE("seq", display_deps(tout << "assert conflict:", lits, eqs););
    m_new_propagation = true;
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), 0, nullptr)));
}

void theory_seq::propagate_eq(dependency* dep, enode* n1, enode* n2) {
    if (n1->get_root() == n2->get_root()) {
        return;
    }
    context& ctx = get_context();
    literal_vector lits;
    enode_pair_vector eqs;
    if (!linearize(dep, eqs, lits))
        return;
    TRACE("seq",
          tout << "assert: " << mk_pp(n1->get_owner(), m) << " = " << mk_pp(n2->get_owner(), m) << " <-\n";
          display_deps(tout, dep); 
          );

    justification* js = ctx.mk_justification(
        ext_theory_eq_propagation_justification(
            get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), n1, n2));
    if (m.has_trace_stream()) {
        app_ref body(m);
        body = m.mk_eq(n1->get_owner(), n2->get_owner());
        log_axiom_instantiation(body);
    }
    ctx.assign_eq(n1, n2, eq_justification(js));
    if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    m_new_propagation = true;

    enforce_length_coherence(n1, n2);
}

void theory_seq::propagate_eq(dependency* dep, expr* e1, expr* e2, bool add_eq) {
    literal_vector lits;
    propagate_eq(dep, lits, e1, e2, add_eq);
}

void theory_seq::propagate_eq(dependency* dep, literal lit, expr* e1, expr* e2, bool add_to_eqs) {
    literal_vector lits;
    lits.push_back(lit);
    propagate_eq(dep, lits, e1, e2, add_to_eqs);
}


void theory_seq::enforce_length_coherence(enode* n1, enode* n2) {
    expr* o1 = n1->get_owner();
    expr* o2 = n2->get_owner();
    if (m_util.str.is_concat(o1) && m_util.str.is_concat(o2)) {
        return;
    }
    if (has_length(o1) && !has_length(o2)) {
        enforce_length(o2);
    }
    else if (has_length(o2) && !has_length(o1)) {
        enforce_length(o1);
    }
}



bool theory_seq::simplify_eq(expr_ref_vector& ls, expr_ref_vector& rs, dependency* deps) {
    context& ctx = get_context();
    expr_ref_vector lhs(m), rhs(m);
    bool changed = false;
    TRACE("seq", tout << ls << " = " << rs << "\n";);
    if (!m_seq_rewrite.reduce_eq(ls, rs, lhs, rhs, changed)) {
        // equality is inconsistent.
        TRACE("seq", tout << ls << " != " << rs << "\n";);
        set_conflict(deps);
        return true;
    }
    if (!changed) {
        SASSERT(lhs.empty() && rhs.empty());
        return false;
    }
    SASSERT(lhs.size() == rhs.size());
    m_seq_rewrite.add_seqs(ls, rs, lhs, rhs);
    if (lhs.empty()) {
        TRACE("seq", tout << "solved\n";);
        return true;
    }
    TRACE("seq", 
          tout << ls << " = " << rs << "\n";
          tout << lhs << " = " << rhs << "\n";);
    for (unsigned i = 0; !ctx.inconsistent() && i < lhs.size(); ++i) {
        expr_ref li(lhs[i].get(), m);
        expr_ref ri(rhs[i].get(), m);
        if (solve_unit_eq(li, ri, deps)) {
            // no-op
        }
        else if (m_util.is_seq(li) || m_util.is_re(li)) {
            TRACE("seq", tout << "inserting " << li << " = " << ri << "\n";);
            m_eqs.push_back(mk_eqdep(li, ri, deps));            
        }
        else {
            propagate_eq(deps, ensure_enode(li), ensure_enode(ri));
        }
    }
    TRACE("seq",
          if (!ls.empty() || !rs.empty()) tout << ls << " = " << rs << ";\n";
          for (unsigned i = 0; i < lhs.size(); ++i) {
              tout << mk_pp(lhs[i].get(), m) << " = " << mk_pp(rhs[i].get(), m) << ";\n";
          });


    return true;
}

bool theory_seq::solve_itos(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep) {
    expr* e = nullptr;
    if (ls.size() == 1 && rs.empty() && m_util.str.is_itos(ls[0], e)) {
        literal lit = mk_simplified_literal(m_autil.mk_le(e, m_autil.mk_int(-1)));
        propagate_lit(dep, 0, nullptr, lit);
        return true;
    } 
    if (rs.size() == 1 && ls.empty() && m_util.str.is_itos(rs[0], e)) {
        literal lit = mk_simplified_literal(m_autil.mk_le(e, m_autil.mk_int(-1)));
        propagate_lit(dep, 0, nullptr, lit);
        return true;
    } 
    return false;
}

bool theory_seq::solve_nth_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep) {
    if (ls.size() != 1 || rs.size() <= 1) {
        return false;
    }
    expr* l = ls.get(0);
    rational val;
    if (!get_length(l, val) || val != rational(rs.size())) {
        return false;
    }
    for (unsigned i = 0; i < rs.size(); ++i) {
        unsigned k = 0;
        expr* ru = nullptr, *r = nullptr;
        if (m_util.str.is_unit(rs.get(i), ru) && m_util.str.is_nth(ru, r, k) && k == i && r == l) {
            continue;
        }
        return false;
    }
    add_solution(l, mk_concat(rs, m.get_sort(l)), dep);
    return true;
}

bool theory_seq::solve_unit_eq(expr_ref_vector const& l, expr_ref_vector const& r, dependency* deps) {
    if (l.size() == 1 && is_var(l[0]) && !occurs(l[0], r) && add_solution(l[0], mk_concat(r, m.get_sort(l[0])), deps)) {
        return true;
    }
    if (r.size() == 1 && is_var(r[0]) && !occurs(r[0], l) && add_solution(r[0], mk_concat(l, m.get_sort(r[0])), deps)) {
        return true;
    }
//    if (l.size() == 1 && r.size() == 1 && l[0] != r[0] && is_nth(l[0]) && add_solution(l[0], r[0], deps))
//        return true;
//    if (l.size() == 1 && r.size() == 1 && l[0] != r[0] && is_nth(r[0]) && add_solution(r[0], l[0], deps))
//        return true;

    return false;
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

bool theory_seq::solve_unit_eq(expr* l, expr* r, dependency* deps) {
    if (l == r) {
        return true;
    }
    if (is_var(l) && !occurs(l, r) && add_solution(l, r, deps)) {
        return true;
    }
    if (is_var(r) && !occurs(r, l) && add_solution(r, l, deps)) {
        return true;
    }
//    if (is_nth(l) && !occurs(l, r) && add_solution(l, r, deps))
//        return true;
//    if (is_nth(r) && !occurs(r, l) && add_solution(r, l, deps))
//        return true;

    return false;
}


bool theory_seq::occurs(expr* a, expr_ref_vector const& b) {
    for (auto const& elem : b) {
        if (a == elem || m.is_ite(elem)) return true;
    }
    return false;
}

bool theory_seq::occurs(expr* a, expr* b) {
     // true if a occurs under an interpreted function or under left/right selector.
    SASSERT(is_var(a));
    SASSERT(m_todo.empty());
    expr* e1 = nullptr, *e2 = nullptr;
    m_todo.push_back(b);
    while (!m_todo.empty()) {
        b = m_todo.back();
        if (a == b || m.is_ite(b)) {
            m_todo.reset();
            return true;
        }
        m_todo.pop_back();
        if (m_util.str.is_concat(b, e1, e2)) {
            m_todo.push_back(e1);
            m_todo.push_back(e2);
        }
    }
     return false;
}


bool theory_seq::is_var(expr* a) const {
    return
        m_util.is_seq(a) &&
        !m_util.str.is_concat(a) &&
        !m_util.str.is_empty(a)  &&
        !m_util.str.is_string(a) &&
        !m_util.str.is_unit(a) &&
        !m_util.str.is_itos(a) && 
        !m.is_ite(a);
}



bool theory_seq::add_solution(expr* l, expr* r, dependency* deps)  {
    if (l == r) {
        return false;
    }
    TRACE("seq", tout << mk_pp(l, m) << " ==> " << mk_pp(r, m) << "\n"; display_deps(tout, deps););
    m_new_solution = true;
    m_rep.update(l, r, deps);
    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() != n2->get_root()) {
        propagate_eq(deps, n1, n2);
    }
    return true;
}

bool theory_seq::solve_eqs(unsigned i) {
    context& ctx = get_context();
    bool change = false;
    for (; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[i];
        if (solve_eq(e.ls(), e.rs(), e.dep(), i)) {
            if (i + 1 != m_eqs.size()) {
                eq e1 = m_eqs[m_eqs.size()-1];
                m_eqs.set(i, e1);
                --i;
            }
            ++m_stats.m_num_reductions;
            m_eqs.pop_back();
            change = true;
        }
        TRACE("seq", display_equations(tout););
    }
    return change || m_new_propagation || ctx.inconsistent();
}

bool theory_seq::solve_eq(expr_ref_vector const& l, expr_ref_vector const& r, dependency* deps, unsigned idx) {
    context& ctx = get_context();
    expr_ref_vector& ls = m_ls;
    expr_ref_vector& rs = m_rs;
    rs.reset(); ls.reset();
    dependency* dep2 = nullptr;
    bool change = canonize(l, ls, dep2);
    change = canonize(r, rs, dep2) || change;
    deps = m_dm.mk_join(dep2, deps);
    TRACE("seq", tout << l << " = " << r << " ==> ";
          tout << ls << " = " << rs << "\n";
          display_deps(tout, deps);
          );
    if (!ctx.inconsistent() && simplify_eq(ls, rs, deps)) {
        TRACE("seq", tout << "simplified\n";);
        return true;
    }
    TRACE("seq", tout << ls << " = " << rs << "\n";);
    if (ls.empty() && rs.empty()) {
        return true;
    }
    if (!ctx.inconsistent() && solve_unit_eq(ls, rs, deps)) {
        TRACE("seq", tout << "unit\n";);
        return true;
    }
    if (!ctx.inconsistent() && solve_binary_eq(ls, rs, deps)) {
        TRACE("seq", tout << "binary\n";);
        return true;
    }
    if (!ctx.inconsistent() && solve_nth_eq(ls, rs, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_nth_eq(rs, ls, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_itos(rs, ls, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && change) {
        // The propagation step from arithmetic state (e.g. length offset) to length constraints
        if (get_context().get_scope_level() == 0) {
            prop_arith_to_len_offset();
        }
        TRACE("seq", tout << "inserting equality\n";);
        bool updated = false;
        if (!m_len_offset.empty()) {
            // Find a better equivalent term for lhs of an equation based on length constraints
            expr_ref_vector new_ls(m);
            if (find_better_rep(ls, rs, idx, deps, new_ls)) {
                eq const & new_eq = eq(m_eq_id++, new_ls, rs, deps);
                m_eqs.push_back(new_eq);
                TRACE("seq", tout << "find_better_rep\n";);
                TRACE("seq", display_equation(tout, new_eq););
                updated = true;
            }
        }
        if (!updated) {
            m_eqs.push_back(eq(m_eq_id++, ls, rs, deps));
        }
        TRACE("seq", tout << "simplified\n";);
        return true;
    }
    return false;
}

bool theory_seq::propagate_max_length(expr* l, expr* r, dependency* deps) {
    unsigned idx;
    expr* s;
    if (m_util.str.is_empty(l)) {
        std::swap(l, r);
    }
    rational hi;
    if (is_tail(l, s, idx) && has_length(s) && m_util.str.is_empty(r) && !upper_bound(s, hi)) {
        propagate_lit(deps, 0, nullptr, mk_literal(m_autil.mk_le(mk_len(s), m_autil.mk_int(idx+1))));
        return true;
    }
    return false;
}

bool theory_seq::is_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y) {
    if (ls.size() > 1 && is_var(ls[0]) &&
        rs.size() > 1 && is_var(rs.back())) {
        xs.reset();
        ys.reset();
        x = ls[0];
        y = rs.back();
        for (unsigned i = 1; i < ls.size(); ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = 0; i < rs.size()-1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.append(ls.size()-1, ls.c_ptr() + 1);
        ys.append(rs.size()-1, rs.c_ptr());
        return true;
    }
    return false;
}

bool theory_seq::is_quat_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                            expr_ref& x1, expr_ref_vector& xs, expr_ref& x2, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
    if (ls.size() > 1 && is_var(ls[0]) && is_var(ls.back()) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = 1;
        for (; l_start < ls.size()-1; ++l_start) {
            if (m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == ls.size()-1) return false;
        unsigned l_end = l_start;
        for (; l_end < ls.size()-1; ++l_end) {
            if (!m_util.str.is_unit(ls[l_end])) break;
        }
        --l_end;
        unsigned r_start = 1;
        for (; r_start < rs.size()-1; ++r_start) {
            if (m_util.str.is_unit(rs[r_start])) break;
        }
        if (r_start == rs.size()-1) return false;
        unsigned r_end = r_start;
        for (; r_end < rs.size()-1; ++r_end) {
            if (!m_util.str.is_unit(rs[r_end])) break;
        }
        --r_end;
        for (unsigned i = l_start; i < l_end+1; ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(l_end-l_start+1, ls.c_ptr()+l_start);
        x1 = m_util.str.mk_concat(l_start, ls.c_ptr());
        x2 = m_util.str.mk_concat(ls.size()-l_end-1, ls.c_ptr()+l_end+1);
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
        return true;
    }
    return false;
}

bool theory_seq::is_ternary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                               expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2, bool flag1) {
    if (ls.size() > 1 && (is_var(ls[0]) || flag1) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = ls.size()-1;
        for (; l_start > 0; --l_start) {
            if (!m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == ls.size()-1) return false;
        ++l_start;
        unsigned r_end = rs.size()-2;
        for (; r_end > 0; --r_end) {
            if (m_util.str.is_unit(rs[r_end])) break;
        }
        if (r_end == 0) return false;
        unsigned r_start = r_end;
        for (; r_start > 0; --r_start) {
            if (!m_util.str.is_unit(rs[r_start])) break;
        }
        ++r_start;
        for (unsigned i = l_start; i < ls.size(); ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(ls.size()-l_start, ls.c_ptr()+l_start);
        x = m_util.str.mk_concat(l_start, ls.c_ptr());
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
        return true;
    }
    return false;
}

bool theory_seq::is_ternary_eq2(expr_ref_vector const& ls, expr_ref_vector const& rs, 
        expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2, bool flag1) {
    if (ls.size() > 1 && (is_var(ls.back()) || flag1) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = 0;
        for (; l_start < ls.size()-1; ++l_start) {
            if (!m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == 0) return false;
        unsigned r_start = 1;
        for (; r_start < rs.size()-1; ++r_start) {
            if (m_util.str.is_unit(rs[r_start])) break;
        }
        if (r_start == rs.size()-1) return false;
        unsigned r_end = r_start;
        for (; r_end < rs.size()-1; ++r_end) {
            if (!m_util.str.is_unit(rs[r_end])) break;
        }
        --r_end;
        for (unsigned i = 0; i < l_start; ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(l_start, ls.c_ptr());
        x = m_util.str.mk_concat(ls.size()-l_start, ls.c_ptr()+l_start);
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
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
        lhs.append(ls.size()-1, ls.c_ptr() + 1);
        rhs.append(rs.size()-1, rs.c_ptr() + 1);
        SASSERT(!lhs.empty() || !rhs.empty());
        deps = mk_join(deps, lits);
        m_eqs.push_back(eq(m_eq_id++, lhs, rhs, deps));
        TRACE("seq", tout << "Propagate equal lengths " << l << " " << r << "\n";);
        propagate_eq(deps, lits, l, r, true);
        return true;
    }

    l = ls.back(); r = rs.back();
    if (reduce_length(l, r, lits)) {
        expr_ref_vector lhs(m), rhs(m);
        lhs.append(ls.size()-1, ls.c_ptr());
        rhs.append(rs.size()-1, rs.c_ptr());
        SASSERT(!lhs.empty() || !rhs.empty());
        deps = mk_join(deps, lits);
        TRACE("seq", tout << "Propagate equal lengths " << l << " " << r << "\n" << "ls: " << ls << "\nrs: " << rs << "\n";);
        m_eqs.push_back(eq(m_eq_id++, lhs, rhs, deps));
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
    context& ctx = get_context();
    expr* const* ls1 = ls.c_ptr();
    expr* const* ls2 = ls.c_ptr()+i;
    expr* const* rs1 = rs.c_ptr();
    expr* const* rs2 = rs.c_ptr()+j;
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
    if (ctx.get_assignment(lit) == l_true) {
        expr_ref_vector lhs(m), rhs(m);
        lhs.append(l2, ls2);
        rhs.append(r2, rs2);
        deps = mk_join(deps, lit);
        m_eqs.push_back(eq(m_eq_id++, lhs, rhs, deps));
        propagate_eq(deps, l, r, true);
        TRACE("seq", tout << "propagate eq\nlhs: " << lhs << "\nrhs: " << rhs << "\n";);
        return true;
    }
    else {
        return false;
    }
}

bool theory_seq::solve_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep) {
    context& ctx = get_context();
    ptr_vector<expr> xs, ys;
    expr_ref x(m), y(m);
    bool is_binary = is_binary_eq(ls, rs, x, xs, ys, y);
    if (!is_binary) {
        is_binary = is_binary_eq(rs, ls, x, xs, ys, y);
    }
    if (!is_binary) {
        return false;
    }
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    if (x != y) {
        return false;
    }
    if (xs.size() != ys.size()) {
        TRACE("seq", tout << "binary conflict\n";);
        set_conflict(dep);
        return false;
    }
    if (xs.empty()) {
        // this should have been solved already
        UNREACHABLE();
        return false;
    }

    // Equation is of the form x ++ xs = ys ++ x
    // where |xs| = |ys| are units of same length
    // then xs is a wrap-around of ys
    // x ++ ab = ba ++ x
    // 
    if (xs.size() == 1) {
        enode* n1 = ensure_enode(xs[0]);
        enode* n2 = ensure_enode(ys[0]);
        if (n1->get_root() == n2->get_root()) {
            return false;
        }
        literal eq = mk_eq(xs[0], ys[0], false);
        switch (ctx.get_assignment(eq)) {
        case l_false: {
            literal_vector conflict;
            conflict.push_back(~eq);
            TRACE("seq", tout << conflict << "\n";);
            set_conflict(dep, conflict);
            break;
        }
        case l_true:
            break;
        case l_undef: 
            ctx.mark_as_relevant(eq);
            propagate_lit(dep, 0, nullptr, eq);
            m_new_propagation = true;
            break;
        }
    }
    return false;
}

bool theory_seq::get_length(expr* e, expr_ref& len, literal_vector& lits) {
    context& ctx = get_context();
    expr* s, *i, *l;
    rational r;
    if (m_util.str.is_extract(e, s, i, l)) {
        // 0 <= i <= len(s), 0 <= l, i + l <= len(s)
        expr_ref zero(m_autil.mk_int(0), m);        
        expr_ref ls = mk_len(s);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i),l), m);
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:mk_simplified_literal(m_autil.mk_ge(i, zero));
        literal i_lt_len_s = ~mk_simplified_literal(m_autil.mk_ge(mk_sub(i, ls), zero));
        literal li_ge_ls  = mk_simplified_literal(m_autil.mk_ge(ls_minus_i_l, zero));
        literal l_ge_zero = mk_simplified_literal(m_autil.mk_ge(l, zero));
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
        expr_ref zero(m_autil.mk_int(0), m);
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:mk_simplified_literal(m_autil.mk_ge(i, zero));
        literal i_lt_len_s = ~mk_simplified_literal(m_autil.mk_ge(mk_sub(i, mk_len(s)), zero));
        literal _lits[2] = { i_ge_0, i_lt_len_s};
        if (ctx.get_assignment(i_ge_0) == l_true &&
            ctx.get_assignment(i_lt_len_s) == l_true) {
            len = m_autil.mk_int(1);
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout, 2, _lits); tout << "\n";);
            return true;
        }
    }
    else if (is_pre(e, s, i)) {
        expr_ref zero(m_autil.mk_int(0), m);
        bool i_is_zero = m_autil.is_numeral(i, r) && r.is_zero();
        literal i_ge_0 = i_is_zero?true_literal:mk_simplified_literal(m_autil.mk_ge(i, zero));
        literal i_lt_len_s = ~mk_simplified_literal(m_autil.mk_ge(mk_sub(i, mk_len(s)), zero));
        literal _lits[2] = { i_ge_0, i_lt_len_s };
        if (ctx.get_assignment(i_ge_0) == l_true &&
            ctx.get_assignment(i_lt_len_s) == l_true) {
            len = i;
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout, 2, _lits); tout << "\n";);
            return true;
        }
    }
    else if (is_post(e, s, l)) {
        expr_ref zero(m_autil.mk_int(0), m);
        literal l_ge_0 = mk_simplified_literal(m_autil.mk_ge(l, zero));
        literal l_le_len_s = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(s), l), zero));
        literal _lits[2] = { l_ge_0, l_le_len_s };
        if (ctx.get_assignment(l_ge_0) == l_true && 
            ctx.get_assignment(l_le_len_s) == l_true) {
            len = l;
            lits.append(2, _lits);
            TRACE("seq", ctx.display_literals_verbose(tout, 2, _lits); tout << "\n";);
            return true;
        }
    }
    else if (is_skolem(m_tail, e)) {
        // e = tail(s, l), len(s) > l => len(tail(s, l)) = len(s) - l - 1
        // e = tail(s, l), len(s) <= l => len(tail(s, l)) = 0

        s = to_app(e)->get_arg(0);
        l = to_app(e)->get_arg(1);
        expr_ref len_s = mk_len(s);
        literal len_s_gt_l = mk_simplified_literal(m_autil.mk_ge(mk_sub(len_s, l), m_autil.mk_int(1)));
        switch (ctx.get_assignment(len_s_gt_l)) {
        case l_true:
            len = mk_sub(len_s, mk_sub(l, m_autil.mk_int(1)));
            TRACE("seq", tout << len_s << " " << len << " " << len_s_gt_l << "\n";);
            lits.push_back(len_s_gt_l);
            return true;
        case l_false:
            len = m_autil.mk_int(0);
            TRACE("seq", tout << len_s << " " << len << " " << len_s_gt_l << "\n";);
            lits.push_back(~len_s_gt_l);
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


bool theory_seq::solve_nqs(unsigned i) {
    context & ctx = get_context();
    for (; !ctx.inconsistent() && i < m_nqs.size(); ++i) {
        if (solve_ne(i)) {
            if (i + 1 != m_nqs.size()) {
                ne n = m_nqs[m_nqs.size()-1];
                m_nqs.set(i, n);
                --i;
            }
            m_nqs.pop_back();
        }
    }
    return m_new_propagation || ctx.inconsistent();
}


bool theory_seq::solve_ne(unsigned idx) {
    context& ctx = get_context();
    ne const& n = m_nqs[idx];

    unsigned num_undef_lits = 0;
    for (literal lit : n.lits()) {
        switch (ctx.get_assignment(lit)) {
        case l_false:
            TRACE("seq", display_disequation(tout << "has false literal\n", n);
                  ctx.display_literal_verbose(tout, lit);
                  tout << "\n" << lit << " " << ctx.is_relevant(lit) << "\n";
                  );
            return true;
        case l_true:
            break;
        case l_undef:
            ++num_undef_lits;
            break;
        }
    }

    bool updated = false;
    dependency* new_deps = n.dep();
    vector<expr_ref_vector> new_ls, new_rs;
    literal_vector new_lits(n.lits());
    for (unsigned i = 0; i < n.ls().size(); ++i) {
        expr_ref_vector& ls = m_ls;
        expr_ref_vector& rs = m_rs;
        expr_ref_vector& lhs = m_lhs;
        expr_ref_vector& rhs = m_rhs;
        ls.reset(); rs.reset(); lhs.reset(); rhs.reset();
        dependency* deps = nullptr;
        bool change = false;
        change = canonize(n.ls(i), ls, deps) || change;
        change = canonize(n.rs(i), rs, deps) || change;

        if (!m_seq_rewrite.reduce_eq(ls, rs, lhs, rhs, change)) {
            TRACE("seq", display_disequation(tout << "reduces to false: ", n);
                  tout << n.ls(i) << " -> " << ls << "\n";
                  tout << n.rs(i) << " -> " << rs << "\n";);
            
            return true;
        }
        else if (!change) {
            TRACE("seq", tout << "no change " << n.ls(i) << " " << n.rs(i) << "\n";);
            if (updated) {
                new_ls.push_back(n.ls(i));
                new_rs.push_back(n.rs(i));
            }
            continue;
        }
        else {
            if (!updated) {
                for (unsigned j = 0; j < i; ++j) {
                    new_ls.push_back(n.ls(j));
                    new_rs.push_back(n.rs(j));
                }
            }
            updated = true;
            if (!ls.empty() || !rs.empty()) {
                new_ls.push_back(ls);
                new_rs.push_back(rs);
            }
            TRACE("seq",
                  tout << lhs << " != " << rhs << "\n";
                  for (unsigned j = 0; j < new_ls.size(); ++j) tout << new_ls[j] << " != " << new_rs[j] << "\n";
                  tout << n.ls(i) << " != " << n.rs(i) << "\n";);

            for (unsigned j = 0; j < lhs.size(); ++j) {
                expr* nl = lhs[j].get();
                expr* nr = rhs[j].get();
                if (m_util.is_seq(nl) || m_util.is_re(nl)) {
                    ls.reset();
                    rs.reset(); 
                    m_util.str.get_concat(nl, ls);
                    m_util.str.get_concat(nr, rs);
                    new_ls.push_back(ls);
                    new_rs.push_back(rs);
                }
                else if (nl != nr) {                
                    literal lit(mk_eq(nl, nr, false));
                    ctx.mark_as_relevant(lit);
                    new_lits.push_back(lit);
                    switch (ctx.get_assignment(lit)) {
                    case l_false:
                        return true;
                    case l_true:
                        break;
                    case l_undef:
                        ++num_undef_lits;
                        m_new_propagation = true;
                        break;
                    }
                }
            }
            new_deps = m_dm.mk_join(deps, new_deps);
        }
    }

    TRACE("seq", display_disequation(tout, n););

    if (!updated && num_undef_lits == 0) {
        return false;
    }
    if (!updated) {
        for (unsigned j = 0; j < n.ls().size(); ++j) {
            new_ls.push_back(n.ls(j));
            new_rs.push_back(n.rs(j));
        }
    }

    if (num_undef_lits == 1 && new_ls.empty()) {
        literal_vector lits;
        literal undef_lit = null_literal;
        for (literal lit : new_lits) {
            switch (ctx.get_assignment(lit)) {
            case l_true:
                lits.push_back(lit);
                break;
            case l_false:
                UNREACHABLE();
                break;
            case l_undef:
                SASSERT(undef_lit == null_literal);
                undef_lit = lit;
                break;
            }
        }
        TRACE("seq", tout << "propagate: " << undef_lit << "\n";);
        SASSERT(undef_lit != null_literal);
        propagate_lit(new_deps, lits.size(), lits.c_ptr(), ~undef_lit);
        return true;
    }
    if (updated) {
        if (num_undef_lits == 0 && new_ls.empty()) {
            TRACE("seq", tout << "conflict\n";);

            dependency* deps1 = nullptr;
            if (explain_eq(n.l(), n.r(), deps1)) {
                literal diseq = mk_eq(n.l(), n.r(), false);
                if (ctx.get_assignment(diseq) == l_false) {
                    new_lits.reset();                
                    new_lits.push_back(~diseq);
                    new_deps = deps1;
                    TRACE("seq", tout << "conflict explained\n";);
                }
            }
            set_conflict(new_deps, new_lits);
            SASSERT(m_new_propagation);
        }
        else {
            m_nqs.push_back(ne(n.l(), n.r(), new_ls, new_rs, new_lits, new_deps));
        }
    }
    return updated;
}


bool theory_seq::solve_nc(unsigned idx) {
    nc const& n = m_ncs[idx];
    dependency* deps = n.deps();    
    literal len_gt = n.len_gt();
    context& ctx = get_context();
    expr_ref c = canonize(n.contains(), deps);
    expr* a = nullptr, *b = nullptr;

    CTRACE("seq", c != n.contains(), tout << n.contains() << " => " << c << "\n";);

    
    if (m.is_true(c)) {
        literal_vector lits;
        set_conflict(deps, lits);
        return true;
    }

    if (m.is_false(c)) {
        return true;
    }

    if (ctx.get_assignment(len_gt) == l_true) {
        TRACE("seq", tout << len_gt << " is true\n";);
        return true;
    }

    if (m.is_eq(c, a, b)) {
        literal eq = mk_eq(a, b, false);
        propagate_lit(deps, 0, nullptr, ~eq);
        return true;
    }

    if (m.is_or(c)) {
        for (expr* arg : *to_app(c)) {
            expr_ref ci(arg, m);
            m_ncs.push_back(nc(ci, len_gt, deps));
        }
        m_new_propagation = true;
        return true;
    }

    if (m.is_and(c)) {
        enode_pair_vector eqs;
        literal_vector lits;
        if (!linearize(deps, eqs, lits)) {
            return false;
        }
        for (literal& lit : lits) {
            lit.neg();
        }
        for (enode_pair const& p : eqs) {
            lits.push_back(~mk_eq(p.first->get_owner(), p.second->get_owner(), false));
        }
        for (expr* arg : *to_app(c)) {
            if (m.is_eq(arg, a, b)) {
                lits.push_back(~mk_eq(a, b, false));
            }
            else {
                lits.push_back(~mk_literal(arg));
            }
        }
        TRACE("seq", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()) << "\n";);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        if (m.has_trace_stream()) {
            expr_ref_vector exprs(m);
            for (literal l : lits) {
                expr* e = ctx.bool_var2expr(l.var());
                if (l.sign()) e = m.mk_not(e);
                exprs.push_back(e);
            }
            app_ref body(m);
            body = m.mk_or(exprs.size(), exprs.c_ptr());
            log_axiom_instantiation(body);
            m.trace_stream() << "[end-of-instance]\n";
        }
        return true;
    }
    
    if (c != n.contains()) {
        m_ncs.push_back(nc(c, len_gt, deps));
        m_new_propagation = true;
        return true;
    }
    
    return false;
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
            m_util.str.get_concat(a, es);
            continue;
        }
        TRACE("seq", tout << "Could not set to empty: " << es << "\n";);
        return false;
    }
    return true;
}

bool theory_seq::simplify_and_solve_eqs() {
    context & ctx = get_context();
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
    context & ctx   = get_context();
    if (ctx.e_internalized(term)) {
        enode* e = ctx.get_enode(term);
        mk_var(e);
        return true;
    }
    for (auto arg : *term) {
        mk_var(ensure_enode(arg));
    }
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
    SASSERT(!m_length.contains(l));
    m_length.push_back(l);
    m_has_length.insert(e);
    m_trail_stack.push(insert_obj_trail<theory_seq, expr>(m_has_length, e));
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_length));
}


/*
  ensure that all elements in equivalence class occur under an application of 'length'
*/
void theory_seq::enforce_length(expr* e) {
    enode* n = ensure_enode(e);
    enode* n1 = n;
    do {
        expr* o = n->get_owner();
        if (!has_length(o)) {
            expr_ref len = mk_len(o);
            enque_axiom(len);
            add_length(len);
        }
        n = n->get_next();
    }
    while (n1 != n);
}


void theory_seq::add_int_string(expr* e) {
    m_int_string.push_back(e);
    m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_int_string));
}

bool theory_seq::check_int_string() {
    bool change = false;
    for (expr * e : m_int_string) {
        if (check_int_string(e)) {
            change = true;
        }
    }
    return change;
}

bool theory_seq::check_int_string(expr* e) {
    return 
        get_context().inconsistent() ||
        (m_util.str.is_itos(e) && add_itos_val_axiom(e)) ||
        (m_util.str.is_stoi(e) && add_stoi_val_axiom(e));
}
    

void theory_seq::add_stoi_axiom(expr* e) {
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    expr* s = nullptr;
    VERIFY (m_util.str.is_stoi(e, s));

    // stoi(s) >= -1
    literal l = mk_simplified_literal(m_autil.mk_ge(e, m_autil.mk_int(-1)));
    add_axiom(l);    

    // stoi("") = -1
    add_axiom(mk_eq(m_util.str.mk_stoi(m_util.str.mk_empty(m.get_sort(s))), m_autil.mk_int(-1), false));
}

void theory_seq::add_itos_axiom(expr* e) {
    rational val;
    expr* n = nullptr;
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    VERIFY(m_util.str.is_itos(e, n));

    // itos(n) = "" <=> n < 0
    expr_ref zero(m_autil.mk_int(0), m);
    literal eq1 = mk_literal(m_util.str.mk_is_empty(e));
    literal ge0 = mk_literal(m_autil.mk_ge(n, zero));
    // n >= 0 => itos(n) != ""
    // itos(n) = "" or n >= 0
    add_axiom(~eq1, ~ge0);
    add_axiom(eq1, ge0);
    
    // n >= 0 => stoi(itos(n)) = n
    app_ref stoi(m_util.str.mk_stoi(e), m);
    add_axiom(~ge0, mk_preferred_eq(stoi, n));

}


void theory_seq::ensure_digit_axiom() {

    if (m_si_axioms.empty()) {
        for (unsigned i = 0; i < 10; ++i) {
            expr_ref cnst(m_util.mk_char('0'+i), m);
            add_axiom(mk_eq(digit2int(cnst), m_autil.mk_int(i), false));
        }
    }
}

bool theory_seq::add_itos_val_axiom(expr* e) {
    rational val, val2;
    expr* n = nullptr;
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    VERIFY(m_util.str.is_itos(e, n));

    if (m_util.str.is_stoi(n)) {
        return false;
    }
    enforce_length(e);

    if (get_length(e, val) && val.is_pos()  && val.is_unsigned() && (!m_si_axioms.find(e, val2) || val != val2)) {
        add_si_axiom(e, n, val.get_unsigned());
        m_si_axioms.insert(e, val);
        m_trail_stack.push(push_replay(alloc(replay_is_axiom, m, e)));
        m_trail_stack.push(insert_map<theory_seq, obj_map<expr, rational>, expr*>(m_si_axioms, e));
        return true;
    }

    return false;
}

bool theory_seq::add_stoi_val_axiom(expr* e) {
    expr* n = nullptr;
    rational val, val2;
    VERIFY(m_util.str.is_stoi(e, n));    

    TRACE("seq", tout << mk_pp(e, m) << " " << get_context().get_scope_level () << " " << get_length(n, val) << " " << val << "\n";);

    if (m_util.str.is_itos(n)) {
        return false;
    }
    enforce_length(n);

    if (get_length(n, val) && val.is_pos() && val.is_unsigned() && (!m_si_axioms.find(e, val2) || val2 != val)) {
        add_si_axiom(n, e, val.get_unsigned());        
        m_si_axioms.insert(e, val);
        m_trail_stack.push(push_replay(alloc(replay_is_axiom, m, e)));
        m_trail_stack.push(insert_map<theory_seq, obj_map<expr, rational>, expr*>(m_si_axioms, e));
        return true;
    }
    
    return false;
}

literal theory_seq::is_digit(expr* ch) {
    literal isd = mk_literal(mk_skolem(symbol("seq.is_digit"), ch, nullptr, nullptr, nullptr, m.mk_bool_sort()));
    expr_ref d2i = digit2int(ch);
    expr_ref _lo(m_util.mk_le(m_util.mk_char('0'), ch), m);
    expr_ref _hi(m_util.mk_le(ch, m_util.mk_char('9')), m);
    literal lo = mk_literal(_lo);
    literal hi = mk_literal(_hi);
    add_axiom(~lo, ~hi, isd);
    add_axiom(~isd, lo);
    add_axiom(~isd, hi);
    return isd;
}

expr_ref theory_seq::digit2int(expr* ch) {
    return expr_ref(mk_skolem(symbol("seq.digit2int"), ch, nullptr, nullptr, nullptr, m_autil.mk_int()), m);
}



// n >= 0 & len(e) >= i + 1 => is_digit(e_i) for i = 0..k-1
// n >= 0 & len(e) = k => n = sum 10^i*digit(e_i)
// n < 0  & len(e) = k => \/_i ~is_digit(e_i) for i = 0..k-1
// 10^k <= n < 10^{k+1}-1 => len(e) => k

void theory_seq::add_si_axiom(expr* e, expr* n, unsigned k) {
    context& ctx = get_context();
    zstring s;
    expr_ref ith_char(m), num(m), coeff(m);
    expr_ref_vector nums(m), chars(m);
    expr_ref len = mk_len(e);
    literal len_eq_k = mk_preferred_eq(len, m_autil.mk_int(k));
    literal ge0 = mk_literal(m_autil.mk_ge(n, m_autil.mk_int(0)));
    literal_vector digits;
    digits.push_back(~len_eq_k);
    digits.push_back(ge0);
    ensure_digit_axiom();
    for (unsigned i = 0; i < k; ++i) {
        ith_char = mk_nth(e, m_autil.mk_int(i));
        literal isd = is_digit(ith_char);
        literal len_ge_i1 = mk_literal(m_autil.mk_ge(len, m_autil.mk_int(i+1)));
        add_axiom(~len_ge_i1, ~ge0, isd);
        digits.push_back(~isd);
        chars.push_back(m_util.str.mk_unit(ith_char));
        nums.push_back(digit2int(ith_char));
    }        
    ++m_stats.m_add_axiom;
    ctx.mk_th_axiom(get_id(), digits.size(), digits.c_ptr());
    rational c(1);
    for (unsigned i = k; i-- > 0; c *= rational(10)) {
        coeff = m_autil.mk_int(c);
        nums[i] = m_autil.mk_mul(coeff, nums.get(i));
    }
    num = m_autil.mk_add(nums.size(), nums.c_ptr());
    ctx.get_rewriter()(num);
    m_new_propagation = true;
    add_axiom(~len_eq_k, ~ge0, mk_preferred_eq(n, num));

    add_axiom(~len_eq_k, ~ge0, mk_preferred_eq(e, m_util.str.mk_concat(chars)));

    SASSERT(k > 0);
    rational lb = power(rational(10), k - 1);
    rational ub = power(rational(10), k) - 1;
    arith_util& a = m_autil;
    literal lbl = mk_literal(a.mk_ge(n, a.mk_int(lb)));
    literal ge_k = mk_literal(a.mk_ge(len, a.mk_int(k)));
    // n >= lb => len(s) >= k
    add_axiom(~lbl, ge_k);
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
    if (!m_re2aut.empty()) {
        out << "Regex\n";
        for (auto const& kv : m_re2aut) {
            out << mk_pp(kv.m_key, m) << "\n";
            display_expr disp(m);
            if (kv.m_value) {
                kv.m_value->display(out, disp);
            }
        }
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
            out << mk_pp(e, m) << " [" << lo << ":" << hi << "]\n";
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
    out << "not " << mk_pp(nc.contains(), m) << "\n";
    display_deps(out << "  <- ", nc.deps()) << "\n";
    return out;
}

std::ostream& theory_seq::display_equations(std::ostream& out) const {
    for (auto const& e : m_eqs) {
        display_equation(out, e);
    }
    return out;
}

std::ostream& theory_seq::display_equation(std::ostream& out, eq const& e) const {
    out << e.ls() << " = " << e.rs() << " <- \n";
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
    for (unsigned j = 0; j < e.ls().size(); ++j) {
        out << e.ls(j) << " != " << e.rs(j) << "\n";
    }
    if (e.dep()) {
        display_deps(out, e.dep());
    }
    return out;
}

std::ostream& theory_seq::display_deps(std::ostream& out, literal_vector const& lits, enode_pair_vector const& eqs) const {
    context& ctx = get_context();
    smt2_pp_environment_dbg env(m);
    params_ref p;
    for (auto const& eq : eqs) {
        out << "  (= ";
        ast_smt2_pp(out, eq.first->get_owner(), env, p, 5);
        out << "\n     ";
        ast_smt2_pp(out, eq.second->get_owner(), env, p, 5);
        out << ")\n";
    }
    for (literal l : lits) {
        if (l == true_literal) {
            out << "   true";
        }
        else if (l == false_literal) {
            out << "   false";
        }
        else {
            expr* e = ctx.bool_var2expr(l.var());
            if (l.sign()) {
                ast_smt2_pp(out << "  (not ", e, env, p, 7);
                out << ")";
            }
            else {
                ast_smt2_pp(out << "  ", e, env, p, 2);
            }
        }
        out << "\n";
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
    st.update("seq add axiom", m_stats.m_add_axiom);
    st.update("seq extensionality", m_stats.m_extensionality);
    st.update("seq fixed length", m_stats.m_fixed_length);
    st.update("seq int.to.str", m_stats.m_int_string);
    st.update("seq automata", m_stats.m_propagate_automata);
}

void theory_seq::init_search_eh() {
    m_re2aut.reset();
    m_res.reset();
    m_automata.reset();
}

void theory_seq::init_model(expr_ref_vector const& es) {
    expr_ref new_s(m);
    for (auto e : es) {
        dependency* eqs = nullptr;
        expr_ref s = canonize(e, eqs);
        if (is_var(s)) {
            new_s = m_factory->get_fresh_value(m.get_sort(s));
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
        for (unsigned i = 0; i < n.ls().size(); ++i) {
            init_model(n.ls(i));
            init_model(n.rs(i));
        }
    }
}


class theory_seq::seq_value_proc : public model_value_proc {
    enum source_t { unit_source, int_source, string_source };
    theory_seq&                     th;
    sort*                           m_sort;
    svector<model_value_dependency> m_dependencies;
    ptr_vector<expr>                m_strings;
    svector<source_t>               m_source;
public:
    seq_value_proc(theory_seq& th, sort* s): th(th), m_sort(s) {
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
        result.append(m_dependencies.size(), m_dependencies.c_ptr());
    }

    void add_buffer(svector<unsigned>& sbuffer, zstring const& zs) {
        for (unsigned i = 0; i < zs.length(); ++i) {
            sbuffer.push_back(zs[i]);
        }
    }

    app * mk_value(model_generator & mg, ptr_vector<expr> & values) override {
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
                    expr_ref tmp = th.canonize(m_strings[k], deps);
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
                    zstring zs(strm.str().c_str());
                    add_buffer(sbuffer, zs);
                    break;
                }
                }
                // TRACE("seq", tout << src << " " << sbuffer << "\n";);
            }
            result = th.m_util.str.mk_string(zstring(sbuffer.size(), sbuffer.c_ptr()));
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
            th.m_rewrite(result);
        }
        th.m_factory->add_trail(result);
        TRACE("seq", tout << result << "\n";);
        return to_app(result);
    }
};

app* theory_seq::get_ite_value(expr* e) {
    expr* e1, *e2, *e3;
    while (m.is_ite(e, e1, e2, e3)) {
        if (get_root(e2) == get_root(e)) {
            e = e2;
        }
        else if (get_root(e3) == get_root(e)) {
            e = e3;
        }
        else {
            break;
        }
    }
    return to_app(e);
}

model_value_proc * theory_seq::mk_value(enode * n, model_generator & mg) {
    app* e = n->get_owner();
    context& ctx = get_context();
    TRACE("seq", tout << mk_pp(n->get_owner(), m) << "\n";);
    e = get_ite_value(e);    
    if (m_util.is_seq(e)) {
        ptr_vector<expr> concats;
        get_ite_concat(e, concats);
        sort* srt = m.get_sort(e);
        seq_value_proc* sv = alloc(seq_value_proc, *this, srt);
       
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        for (expr* c : concats) {
            expr *c1;
            TRACE("seq", tout << mk_pp(c, m) << "\n";);
            if (m_util.str.is_unit(c, c1)) {
                if (ctx.e_internalized(c1)) {
                    sv->add_unit(ctx.get_enode(c1));
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
                sv->add_string(mk_value(to_app(c)));
            }
        }
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
        val = m_factory->get_some_value(m.get_sort(result));
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


theory_var theory_seq::mk_var(enode* n) {
    if (!m_util.is_seq(n->get_owner()) &&
        !m_util.is_re(n->get_owner())) {
        return null_theory_var;
    }
    if (is_attached_to_var(n)) {
        return n->get_th_var(get_id());
    }
    else {
        theory_var v = theory::mk_var(n);
        m_find.mk_var();
        get_context().attach_th_var(n, this, v);
        get_context().mark_as_relevant(n);
        return v;
    }
}

bool theory_seq::can_propagate() {
    return m_axioms_head < m_axioms.size() || !m_replay.empty() || m_new_solution;
}

expr_ref theory_seq::canonize(expr* e, dependency*& eqs) {
    expr_ref result = expand(e, eqs);
    TRACE("seq", tout << mk_pp(e, m) << " expands to " << result << "\n";);
    m_rewrite(result);
    TRACE("seq", tout << mk_pp(e, m) << " rewrites to " << result << "\n";);
    return result;
}

bool theory_seq::canonize(expr* e, expr_ref_vector& es, dependency*& eqs) {
    expr* e1, *e2;
    expr_ref e3(e, m);
    bool change = false;
    while (true) {
        if (m_util.str.is_concat(e3, e1, e2)) {
            canonize(e1, es, eqs);
            e3 = e2;
            change = true;
        }
        else if (m_util.str.is_empty(e3)) {
            return true;
        }
        else {
            expr_ref e4 = expand(e3, eqs);
            change |= e4 != e3;
            m_util.str.get_concat(e4, es);
            break;
        }
    }
    return change;
}

bool theory_seq::canonize(expr_ref_vector const& es, expr_ref_vector& result, dependency*& eqs) {
    bool change = false;
    for (expr* e : es) {
        change = canonize(e, result, eqs) || change;
        SASSERT(!m_util.str.is_concat(e) || change);
    }
    return change;
}

expr_ref theory_seq::expand(expr* e, dependency*& eqs) {
    unsigned sz = m_expand_todo.size();
    m_expand_todo.push_back(e);
    expr_ref result(m);
    while (m_expand_todo.size() != sz) {
        expr* e = m_expand_todo.back();
        result = expand1(e, eqs);
        if (result.get()) m_expand_todo.pop_back();
    }
    return result;
}
 
expr_ref theory_seq::try_expand(expr* e, dependency*& eqs){
    expr_ref result(m);
    expr_dep ed;
    if (m_rep.find_cache(e, ed)) {
        if (e != ed.first) {
            eqs = m_dm.mk_join(eqs, ed.second);
        }
        result = ed.first;
    }
    else {
        m_expand_todo.push_back(e);
    }
    return result;
}
expr_ref theory_seq::expand1(expr* e0, dependency*& eqs) {
    expr_ref result(m);
    result = try_expand(e0, eqs);
    if (result) return result;
    dependency* deps = nullptr;
    expr* e = m_rep.find(e0, deps);
    expr* e1, *e2, *e3;
    expr_ref arg1(m), arg2(m);
    context& ctx = get_context();
    if (m_util.str.is_concat(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = mk_concat(arg1, arg2);
    }
    else if (m_util.str.is_empty(e) || m_util.str.is_string(e)) {
        result = e;
    }    
    else if (m_util.str.is_prefix(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_prefix(arg1, arg2);
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_suffix(arg1, arg2);
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_contains(arg1, arg2);
    }
    else if (m_util.str.is_unit(e, e1)) {
        arg1 = try_expand(e1, deps);
        if (!arg1) return result;
        result = m_util.str.mk_unit(arg1);
    }
    else if (m_util.str.is_index(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_index(arg1, arg2, m_autil.mk_int(0));
    }
    else if (m_util.str.is_index(e, e1, e2, e3)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_index(arg1, arg2, e3);
    }
    else if (m_util.str.is_last_index(e, e1, e2)) {
        arg1 = try_expand(e1, deps);
        arg2 = try_expand(e2, deps);
        if (!arg1 || !arg2) return result;
        result = m_util.str.mk_last_index(arg1, arg2);
    }
    else if (m.is_ite(e, e1, e2, e3)) {
        enode* r = get_root(e);
        enode* r2 = get_root(e2);
        enode* r3 = get_root(e3);
        if (ctx.e_internalized(e) && ctx.e_internalized(e2) && r == r2 && r != r3) {
            result = try_expand(e2, deps);
            if (!result) return result;
            add_dependency(deps, ctx.get_enode(e), ctx.get_enode(e2));
        }
        else if (ctx.e_internalized(e) && ctx.e_internalized(e2) && r == r3 && r != r2) {
            result = try_expand(e3, deps);
            if (!result) return result;
            add_dependency(deps, ctx.get_enode(e), ctx.get_enode(e3));
        }
        else {
            literal lit(mk_literal(e1));
            switch (ctx.get_assignment(lit)) {
            case l_true:
                deps = m_dm.mk_join(deps, m_dm.mk_leaf(assumption(lit)));
                result = try_expand(e2, deps);
                if (!result) return result;
                break;
            case l_false:
                deps = m_dm.mk_join(deps, m_dm.mk_leaf(assumption(~lit)));
                result = try_expand(e3, deps);
                if (!result) return result;
                break;
            case l_undef:
                result = e;  
                m_reset_cache = true;
                TRACE("seq", tout << "undef: " << result << "\n";
                      tout << lit << "@ level: " << ctx.get_scope_level() << "\n";);
                break;
            }
        }
    }
    else if (m_util.str.is_itos(e, e1)) {
        rational val;
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        if (get_num_value(e1, val)) {
            TRACE("seq", tout << mk_pp(e, m) << " -> " << val << "\n";);
            expr_ref num(m), res(m);
            num = m_autil.mk_numeral(val, true);
            if (!ctx.e_internalized(num)) {
                ctx.internalize(num, false);
            }
            enode* n1 = ctx.get_enode(num);
            enode* n2 = ctx.get_enode(e1);
            res = m_util.str.mk_string(symbol(val.to_string().c_str()));
#if 1
            if (val.is_neg()) {
                result = e;
            }
            // TBD remove this: using roots is unsound for propagation.
            else if (n1->get_root() == n2->get_root()) {
                result = res;
                deps = m_dm.mk_join(deps, m_dm.mk_leaf(assumption(n1, n2)));
            }
            else {
                TRACE("seq", tout << "mk equalities\n";);
                literal l1 = mk_preferred_eq(num, e1);
                literal l2 = mk_preferred_eq(e, res);
                TRACE("seq", tout << "add axiom " << l1 << " " << l2 << "\n";);                
                add_axiom(l1, ~l2);
                add_axiom(~l1, l2);
                result = e;
            }
#else
            TRACE("seq", tout << "add axiom\n";);                
            add_axiom(~mk_eq(num, e1, false), mk_eq(e, res, false));
            add_axiom(mk_eq(num, e1, false), ~mk_eq(e, res, false));
            result = e;
#endif
        }
        else {
            result = e;
        }
    }
    else {
        result = e;
    }
    if (result == e0) {
        deps = nullptr;
    }
    expr_dep edr(result, deps);
    m_rep.add_cache(e0, edr);
    eqs = m_dm.mk_join(eqs, deps);
    TRACE("seq_verbose", tout << mk_pp(e0, m) << " |--> " << result << "\n";
          if (eqs) display_deps(tout, eqs););
    return result;
}

void theory_seq::add_dependency(dependency*& dep, enode* a, enode* b) {
    if (a != b) {
        dep = m_dm.mk_join(dep, m_dm.mk_leaf(assumption(a, b)));
    }
}


void theory_seq::propagate() {
    context & ctx = get_context();
    while (m_axioms_head < m_axioms.size() && !ctx.inconsistent()) {
        expr_ref e(m);
        e = m_axioms[m_axioms_head].get();
        deque_axiom(e);
        ++m_axioms_head;
    }
    while (!m_replay.empty() && !ctx.inconsistent()) {
        apply* app = m_replay[m_replay.size() - 1];
        TRACE("seq", tout << "replay at level: " << ctx.get_scope_level() << "\n";);
        (*app)(*this);
        m_replay.pop_back();
    }
    if (m_new_solution) {
        simplify_and_solve_eqs();
        m_new_solution = false;
    }
}

void theory_seq::enque_axiom(expr* e) {
    TRACE("seq", tout << "enqueue_axiom " << mk_pp(e, m) << " " << m_axiom_set.contains(e) << "\n";);    
    if (!m_axiom_set.contains(e)) {
        TRACE("seq", tout << "add axiom " << mk_pp(e, m) << "\n";);
        m_axioms.push_back(e);
        m_axiom_set.insert(e);
        m_trail_stack.push(push_back_vector<theory_seq, expr_ref_vector>(m_axioms));
        m_trail_stack.push(insert_obj_trail<theory_seq, expr>(m_axiom_set, e));;
    }
}

void theory_seq::deque_axiom(expr* n) {
    TRACE("seq", tout << "deque: " << mk_pp(n, m) << "\n";);
    if (m_util.str.is_length(n)) {
        add_length_axiom(n);
    }
    else if (m_util.str.is_empty(n) && !has_length(n) && !m_has_length.empty()) {
        enforce_length(n);
    }
    else if (m_util.str.is_index(n)) {
        add_indexof_axiom(n);
    }
    else if (m_util.str.is_last_index(n)) {
        add_last_indexof_axiom(n);
    }
    else if (m_util.str.is_replace(n)) {
        add_replace_axiom(n);
    }
    else if (m_util.str.is_extract(n)) {
        add_extract_axiom(n);
    }
    else if (m_util.str.is_at(n)) {
        add_at_axiom(n);
    }
    else if (m_util.str.is_nth(n)) {
        add_nth_axiom(n);
    }
    else if (m_util.str.is_string(n)) {
        add_elim_string_axiom(n);
    }
    else if (m_util.str.is_itos(n)) {
        add_itos_axiom(n);
    }
    else if (m_util.str.is_stoi(n)) {
        add_stoi_axiom(n);
    }
}


/*
  encode that s is not contained in of xs1
  where s1 is all of s, except the last element.

  s = "" or s = s1*(unit c)
  s = "" or !contains(x*s1, s)
*/
void theory_seq::tightest_prefix(expr* s, expr* x) {
    expr_ref s1 = mk_first(s);
    expr_ref c  = mk_last(s);
    expr_ref s1c = mk_concat(s1, m_util.str.mk_unit(c));
    literal s_eq_emp = mk_eq_empty(s);
    add_axiom(s_eq_emp, mk_seq_eq(s, s1c));
    add_axiom(s_eq_emp, ~mk_literal(m_util.str.mk_contains(mk_concat(x, s1), s)));
}

/*
    [[str.indexof]](w, w2, i) is the smallest n such that for some some w1, w3
    - w = w1w2w3
    - i <= n = |w1|

    if [[str.contains]](w, w2) = true, |w2| > 0 and i >= 0.

    [[str.indexof]](w,w2,i) = -1  otherwise.


  let i = Index(t, s, offset):
  // index of s in t starting at offset.

  
  |t| = 0 => |s| = 0 or indexof(t,s,offset) = -1
  |t| = 0 & |s| = 0 => indexof(t,s,offset) = 0

  offset >= len(t) => |s| = 0 or i = -1
  
  len(t) != 0 & !contains(t, s) => i = -1


  offset = 0 & len(t) != 0 & contains(t, s) => t = xsy & i = len(x)
  tightest_prefix(x, s)


  0 <= offset < len(t) => xy = t &
                          len(x) = offset &
                          (-1 = indexof(y, s, 0) => -1 = i) &
                          (indexof(y, s, 0) >= 0 => indexof(t, s, 0) + offset = i)

  offset < 0 => i = -1

  optional lemmas:
   (len(s) > len(t)  -> i = -1)
   (len(s) <= len(t) -> i <= len(t)-len(s))
*/
void theory_seq::add_indexof_axiom(expr* i) {
    expr* s = nullptr, *t = nullptr, *offset = nullptr;
    rational r;
    VERIFY(m_util.str.is_index(i, t, s) ||
           m_util.str.is_index(i, t, s, offset));
    expr_ref minus_one(m_autil.mk_int(-1), m);
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref xsy(m);
    
    literal cnt = mk_literal(m_util.str.mk_contains(t, s));
    literal i_eq_m1 = mk_eq(i, minus_one, false);
    literal i_eq_0 = mk_eq(i, zero, false);
    literal s_eq_empty = mk_eq_empty(s);
    literal t_eq_empty = mk_eq_empty(t);

    // |t| = 0 => |s| = 0 or indexof(t,s,offset) = -1
    // ~contains(t,s) <=> indexof(t,s,offset) = -1

    add_axiom(cnt,  i_eq_m1);
//    add_axiom(~cnt,  ~i_eq_m1);
    add_axiom(~t_eq_empty, s_eq_empty, i_eq_m1);

    if (!offset || (m_autil.is_numeral(offset, r) && r.is_zero())) {
        expr_ref x  = mk_skolem(m_indexof_left, t, s);
        expr_ref y  = mk_skolem(m_indexof_right, t, s);
        xsy         = mk_concat(x, s, y);
        expr_ref lenx = mk_len(x);
        // |s| = 0 => indexof(t,s,0) = 0
        // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
        add_axiom(~s_eq_empty, i_eq_0);
        add_axiom(~cnt, s_eq_empty, mk_seq_eq(t, xsy));
        add_axiom(~cnt, s_eq_empty, mk_eq(i, lenx, false));
        add_axiom(~cnt, mk_literal(m_autil.mk_ge(i, zero)));
        tightest_prefix(s, x);
    }
    else {
        // offset >= len(t) => |s| = 0 or indexof(t, s, offset) = -1
        // offset > len(t) => indexof(t, s, offset) = -1
        // offset = len(t) & |s| = 0 => indexof(t, s, offset) = offset
        expr_ref len_t = mk_len(t);
        literal offset_ge_len = mk_simplified_literal(m_autil.mk_ge(mk_sub(offset, len_t), zero));
        literal offset_le_len = mk_simplified_literal(m_autil.mk_le(mk_sub(offset, len_t), zero));
        literal i_eq_offset = mk_eq(i, offset, false);
        add_axiom(~offset_ge_len, s_eq_empty, i_eq_m1);
        add_axiom(offset_le_len, i_eq_m1);
        add_axiom(~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset);

        expr_ref x = mk_skolem(m_indexof_left, t, s, offset);
        expr_ref y = mk_skolem(m_indexof_right, t, s, offset);
        expr_ref indexof0(m_util.str.mk_index(y, s, zero), m);
        expr_ref offset_p_indexof0(m_autil.mk_add(offset, indexof0), m);
        literal offset_ge_0 = mk_simplified_literal(m_autil.mk_ge(offset, zero));

        // 0 <= offset & offset < len(t) => t = xy
        // 0 <= offset & offset < len(t) => len(x) = offset
        // 0 <= offset & offset < len(t) & -1 = indexof(y,s,0) = -1 => -1 = i
        // 0 <= offset & offset < len(t) & indexof(y,s,0) >= 0 = -1 =>
        //                  -1 = indexof(y,s,0) + offset = indexof(t, s, offset)

        add_axiom(~offset_ge_0, offset_ge_len, mk_seq_eq(t, mk_concat(x, y)));
        add_axiom(~offset_ge_0, offset_ge_len, mk_eq(mk_len(x), offset, false));
        add_axiom(~offset_ge_0, offset_ge_len,
                  ~mk_eq(indexof0, minus_one, false), i_eq_m1);
        add_axiom(~offset_ge_0, offset_ge_len,
                  ~mk_simplified_literal(m_autil.mk_ge(indexof0, zero)),
                  mk_eq(offset_p_indexof0, i, false));

        // offset < 0 => -1 = i        
        add_axiom(offset_ge_0, i_eq_m1);
    }
}

/**

  !contains(t, s) => i = -1   
  |t| = 0 => |s| = 0 or i = -1
  |t| = 0 & |s| = 0 => i = 0
  |t| != 0 & contains(t, s) => t = xsy & i = len(x) 
  |s| = 0 or s = s_head*s_tail
  |s| = 0 or !contains(s_tail*y, s)

 */
void theory_seq::add_last_indexof_axiom(expr* i) {
    expr* s = nullptr, *t = nullptr;
    VERIFY(m_util.str.is_last_index(i, t, s));
    expr_ref minus_one(m_autil.mk_int(-1), m);
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref s_head(m), s_tail(m);
    expr_ref x  = mk_skolem(symbol("seq.last_indexof_left"), t, s);
    expr_ref y  = mk_skolem(symbol("seq.last_indexof_right"), t, s);
    mk_decompose(s, s_head, s_tail);
    literal cnt  = mk_literal(m_util.str.mk_contains(t, s));
    literal cnt2 = mk_literal(m_util.str.mk_contains(mk_concat(s_tail, y), s));
    literal i_eq_m1 = mk_eq(i, minus_one, false);
    literal i_eq_0 = mk_eq(i, zero, false);
    literal s_eq_empty = mk_eq_empty(s);
    literal t_eq_empty = mk_eq_empty(t);
    expr_ref xsy         = mk_concat(x, s, y);

    add_axiom(cnt, i_eq_m1);
    add_axiom(~t_eq_empty, s_eq_empty, i_eq_m1);
    add_axiom(~t_eq_empty, ~s_eq_empty, i_eq_0);
    add_axiom(t_eq_empty, ~cnt, mk_seq_eq(t, xsy));
    add_axiom(t_eq_empty, ~cnt, mk_eq(i, mk_len(x), false));
    add_axiom(s_eq_empty, mk_eq(s, mk_concat(s_head, s_tail), false));
    add_axiom(s_eq_empty, ~cnt2);
}

/*
  let r = replace(a, s, t)

  a = "" => s = "" or r = a
  contains(a, s) or r = a
  s = "" => r = t+a
  
  tightest_prefix(s, x)
  (contains(a, s) -> r = xty & a = xsy) &
  (!contains(a, s) -> r = a)

*/
void theory_seq::add_replace_axiom(expr* r) {
    context& ctx = get_context();
    expr* a = nullptr, *s = nullptr, *t = nullptr;
    VERIFY(m_util.str.is_replace(r, a, s, t));
    expr_ref x  = mk_skolem(m_indexof_left, a, s);
    expr_ref y  = mk_skolem(m_indexof_right, a, s);
    expr_ref xty = mk_concat(x, t, y);
    expr_ref xsy = mk_concat(x, s, y);
    literal a_emp = mk_eq_empty(a, true);
    literal s_emp = mk_eq_empty(s, true);
    literal cnt = mk_literal(m_util.str.mk_contains(a, s));
    add_axiom(~a_emp, s_emp, mk_seq_eq(r, a));
    add_axiom(cnt,  mk_seq_eq(r, a));
    add_axiom(~s_emp, mk_seq_eq(r, mk_concat(t, a)));
    add_axiom(~cnt, a_emp, s_emp, mk_seq_eq(a, xsy));
    add_axiom(~cnt, a_emp, s_emp, mk_seq_eq(r, xty));
    ctx.force_phase(cnt);
    tightest_prefix(s, x);
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


/*
    let n = len(x)
    - len(a ++ b) = len(a) + len(b) if x = a ++ b
    - len(unit(u)) = 1              if x = unit(u)
    - len(str) = str.length()       if x = str
    - len(empty) = 0                if x = empty
    - len(int.to.str(i)) >= 1       if x = int.to.str(i) and more generally if i = 0 then 1 else 1+floor(log(|i|))
    - len(x) >= 0                   otherwise
 */
void theory_seq::add_length_axiom(expr* n) {
    context& ctx = get_context();
    expr* x = nullptr;
    VERIFY(m_util.str.is_length(n, x));
    if (m_util.str.is_concat(x) ||
        m_util.str.is_unit(x) ||
        m_util.str.is_empty(x) ||
        m_util.str.is_string(x)) {
        expr_ref len(n, m);
        m_rewrite(len);
        SASSERT(n != len);
        add_axiom(mk_eq(len, n, false));
    }
    else if (m_util.str.is_itos(x)) {
        add_itos_length_axiom(n);
    }   
    else {
        add_axiom(mk_literal(m_autil.mk_ge(n, m_autil.mk_int(0))));
    }
    if (!ctx.at_base_level()) {
        m_trail_stack.push(push_replay(alloc(replay_axiom, m, n)));
    }
}

void theory_seq::add_itos_length_axiom(expr* len) {
    expr* x = nullptr, *n = nullptr;
    VERIFY(m_util.str.is_length(len, x));
    VERIFY(m_util.str.is_itos(x, n));

    unsigned num_char1 = 1, num_char2 = 1;
    rational len1, len2;
    rational ten(10);
    if (get_num_value(n, len1)) {
        if (len1.is_neg()) {
            return;
        }
        // 0 <= x < 10
        // 10 <= x < 100
        // 100 <= x < 1000
        rational upper(10);
        while (len1 > upper) {
            ++num_char1;
            upper *= ten;
        }
        SASSERT(len1 <= upper);
    }
    if (get_num_value(len, len2) && len2.is_unsigned()) {
        num_char2 = len2.get_unsigned();
    }
    unsigned num_char = std::max(num_char1, num_char2);
    

    literal len_le(mk_literal(m_autil.mk_le(len, m_autil.mk_int(num_char))));
    literal len_ge(mk_literal(m_autil.mk_ge(len, m_autil.mk_int(num_char))));
    literal n_ge_0(mk_literal(m_autil.mk_ge(n, m_autil.mk_int(0))));
    add_axiom(~n_ge_0, mk_literal(m_autil.mk_ge(len, m_autil.mk_int(1))));   

    if (num_char == 1) {
        literal n_ge_10(mk_literal(m_autil.mk_ge(n, m_autil.mk_int(10))));
        add_axiom(~n_ge_0, n_ge_10, len_le);
        add_axiom(~len_le, ~n_ge_10);
        return;
    }
    rational hi(1);
    for (unsigned i = 2; i < num_char; ++i) {
        hi *= ten;
    }
    // n >= hi*10  <=>  len >= num_chars
    //  n < 100*hi    <=>  len <= num_chars
    literal n_ge_10hi  = mk_literal(m_autil.mk_ge(n, m_autil.mk_numeral(ten*hi, true)));
    literal n_ge_100hi = mk_literal(m_autil.mk_ge(n, m_autil.mk_numeral(ten*ten*hi, true)));
    
    add_axiom(~n_ge_10hi, len_ge);
    add_axiom(~n_ge_100hi, ~len_le);
}



void theory_seq::propagate_in_re(expr* n, bool is_true) {
    TRACE("seq", tout << mk_pp(n, m) << " <- " << (is_true?"true":"false") << "\n";);

    expr_ref tmp(n, m);
    m_rewrite(tmp);
    if (m.is_true(tmp)) {
        if (!is_true) {
            literal_vector lits;
            lits.push_back(mk_literal(n));
            set_conflict(nullptr, lits);
        }
        return;
    }
    else if (m.is_false(tmp)) {
        if (is_true) {
            literal_vector lits;
            lits.push_back(~mk_literal(n));
            set_conflict(nullptr, lits);
        }
        return;
    }

    expr* s = nullptr, *_re = nullptr;
    VERIFY(m_util.str.is_in_re(n, s, _re));
    expr_ref re(_re, m);
    context& ctx = get_context();
    literal lit = ctx.get_literal(n);
    if (!is_true) {
        re = m_util.re.mk_complement(re);
        lit.neg();
    }

    literal_vector lits;    
    for (unsigned i = 0; i < m_s_in_re.size(); ++i) {
        auto const& entry = m_s_in_re[i];
        if (entry.m_active && get_root(entry.m_s) == get_root(s) && entry.m_re != re) {
            m_trail_stack.push(vector_value_trail<theory_seq, s_in_re, true>(m_s_in_re, i));
            m_s_in_re[i].m_active = false;
            IF_VERBOSE(11, verbose_stream() << "intersect " << re << " " << mk_pp(entry.m_re, m) << " " << mk_pp(s, m) << " " << mk_pp(entry.m_s, m) << "\n";);
            re = m_util.re.mk_inter(entry.m_re, re);
            m_rewrite(re);
            lits.push_back(~entry.m_lit);
            enode* n1 = ensure_enode(entry.m_s);
            enode* n2 = ensure_enode(s);
            if (n1 != n2) {
                lits.push_back(~mk_eq(n1->get_owner(), n2->get_owner(), false));
            }
        }
    }

    IF_VERBOSE(11, verbose_stream() << mk_pp(s, m) << " in " << re << "\n");
    eautomaton* a = get_automaton(re);
    if (!a) {
        std::stringstream strm;
        strm << "expression " << re << " does not correspond to a supported regular expression";
        TRACE("seq", tout << strm.str() << "\n";);
        throw default_exception(strm.str());
    }

    m_s_in_re.push_back(s_in_re(lit, s, re, a));
    m_trail_stack.push(push_back_vector<theory_seq, vector<s_in_re>>(m_s_in_re));

    expr_ref len = mk_len(s);

    expr_ref zero(m_autil.mk_int(0), m);
    unsigned_vector states;
    a->get_epsilon_closure(a->init(), states);
    lits.push_back(~lit);
    expr_ref_vector exprs(m);
    
    for (unsigned st : states) {
        literal acc = mk_accept(s, zero, re, st);
        lits.push_back(acc);
        exprs.push_back(ctx.bool_var2expr(acc.var()));
    }
    if (lits.size() == 2) {
        propagate_lit(nullptr, 1, &lit, lits[1]);
    }
    else {
        TRACE("seq", ctx.display_literals_verbose(tout, lits) << "\n";);
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(n, m.mk_or(exprs.size(), exprs.c_ptr()));
            log_axiom_instantiation(body);
        }
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }
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

enode* theory_seq::ensure_enode(expr* e) {
    context& ctx = get_context();
    if (!ctx.e_internalized(e)) {
        ctx.internalize(e, false);
    }
    enode* n = ctx.get_enode(e);
    ctx.mark_as_relevant(n);
    return n;
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
    context& ctx = get_context();
    expr_ref e = mk_len(_e);
    expr_ref _lo(m);
    theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, m_autil.get_family_id(), e);
    if (!tha) {
        theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, m_autil.get_family_id(), e);
        if (!thi || !thi->get_lower(ctx.get_enode(e), _lo) || !m_autil.is_numeral(_lo, lo)) return false;
    }
    enode *ee = ctx.get_enode(e);
    if (tha && (!tha->get_lower(ee, _lo) || m_autil.is_numeral(_lo, lo))) {
        enode *next = ee->get_next();
        bool flag = false;
        while (next != ee) {
            if (!m_autil.is_numeral(next->get_owner()) && !m_util.str.is_length(next->get_owner())) {
                expr *var = next->get_owner();
                TRACE("seq", tout << mk_pp(var, m) << "\n";);
                expr_ref _lo2(m);
                rational lo2;
                if (tha->get_lower(next, _lo2) && m_autil.is_numeral(_lo2, lo2) && lo2>lo) {
                    flag = true;
                    lo = lo2;
                    literal low(mk_literal(m_autil.mk_ge(var, _lo2)));
                    add_axiom(~low, mk_literal(m_autil.mk_ge(e, _lo2)));
                }
            }
            next = next->get_next();
        }
        if (flag)
            return true;
        if (!tha->get_lower(ee, _lo))
            return false;
    }
    return true;
}


bool theory_seq::get_length(expr* e, rational& val) const {
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
            TRACE("seq", tout << "literal has no length " << mk_pp(c, m) << "\n";);
            return false;            
        }
        else {            
            len = mk_len(c);
            if (m_arith_value.get_value(len, val1)) {
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

  let e = extract(s, i, l)

  i is start index, l is length of substring starting at index.

  i < 0 => e = ""
  i >= |s| => e = ""
  l <= 0 => e = ""
  0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)

this translates to:

  0 <= i <= |s| -> s = xey 
  0 <= i <= |s| -> len(x) = i
  0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
  0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
  i >= |s| => |e| = 0
  i < 0 => |e| = 0
  l <= 0 => |e| = 0

  It follows that: 
  |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|


*/

void theory_seq::add_extract_axiom(expr* e) {
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    expr* s = nullptr, *i = nullptr, *l = nullptr;
    VERIFY(m_util.str.is_extract(e, s, i, l));
    if (is_tail(s, i, l)) {
        add_tail_axiom(e, s);
        return;
    }
    if (is_drop_last(s, i, l)) {
        add_drop_last_axiom(e, s);
        return;
    }
    if (is_extract_prefix0(s, i, l)) {
        add_extract_prefix_axiom(e, s, l);
        return;
    }
    if (is_extract_suffix(s, i, l)) {
        add_extract_suffix_axiom(e, s, i);
        return;
    }

    expr_ref x(mk_skolem(m_pre, s, i), m);
    expr_ref ls = mk_len(s);
    expr_ref lx = mk_len(x);
    expr_ref le = mk_len(e);
    expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
    expr_ref y(mk_skolem(m_post, s, ls_minus_i_l), m);
    expr_ref xe = mk_concat(x, e);
    expr_ref xey = mk_concat(x, e, y);
    expr_ref zero(m_autil.mk_int(0), m);

    literal i_ge_0    = mk_simplified_literal(m_autil.mk_ge(i, zero));
    literal ls_le_i   = mk_simplified_literal(m_autil.mk_le(mk_sub(i, ls), zero));
    literal li_ge_ls  = mk_simplified_literal(m_autil.mk_ge(ls_minus_i_l, zero));
    literal l_ge_zero = mk_simplified_literal(m_autil.mk_ge(l, zero));
    literal ls_le_0   = mk_simplified_literal(m_autil.mk_le(ls, zero));
    literal le_is_0   = mk_eq(le, zero, false);

    add_axiom(~i_ge_0, ~ls_le_i, mk_seq_eq(xey, s));
    add_axiom(~i_ge_0, ~ls_le_i, mk_eq(lx, i, false));
    add_axiom(~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false));
    add_axiom(~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false));
    add_axiom(~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false));
    add_axiom(i_ge_0,   le_is_0);
    add_axiom(ls_le_i,  le_is_0);
    add_axiom(~ls_le_0, le_is_0);
}

void theory_seq::add_tail_axiom(expr* e, expr* s) {
    expr_ref head(m), tail(m);
    mk_decompose(s, head, tail);
    literal emp = mk_eq_empty(s);
    add_axiom(emp, mk_seq_eq(s, mk_concat(head, e)));
    add_axiom(~emp, mk_eq_empty(e));
}

void theory_seq::add_drop_last_axiom(expr* e, expr* s) {
    literal emp = mk_eq_empty(s);
    add_axiom(emp, mk_seq_eq(s, mk_concat(e, m_util.str.mk_unit(mk_last(s)))));
    add_axiom(~emp, mk_eq_empty(e));
}

bool theory_seq::is_drop_last(expr* s, expr* i, expr* l) {
    rational i1;
    if (!m_autil.is_numeral(i, i1) || !i1.is_zero()) {
        return false;
    }
    expr_ref l2(m), l1(l, m);
    l2 = mk_sub(mk_len(s), m_autil.mk_int(1));
    m_rewrite(l1);
    m_rewrite(l2);
    return l1 == l2;
}

bool theory_seq::is_tail(expr* s, expr* i, expr* l) {
    rational i1;
    if (!m_autil.is_numeral(i, i1) || !i1.is_one()) {
        return false;
    }
    expr_ref l2(m), l1(l, m);
    l2 = mk_sub(mk_len(s), m_autil.mk_int(1));
    m_rewrite(l1);
    m_rewrite(l2);
    return l1 == l2;
}

bool theory_seq::is_extract_prefix0(expr* s, expr* i, expr* l) {
    rational i1;
    return m_autil.is_numeral(i, i1) && i1.is_zero();    
}

bool theory_seq::is_extract_suffix(expr* s, expr* i, expr* l) {
    expr_ref len(m_autil.mk_add(l, i), m);
    m_rewrite(len);
    return m_util.str.is_length(len, l) && l == s;
}

/*
  0 <= l <= len(s) => s = ey & l = len(e)
  len(s) < l => s = e
  l < 0 => e = empty
 */
void theory_seq::add_extract_prefix_axiom(expr* e, expr* s, expr* l) {
    TRACE("seq", tout << mk_pp(e, m) << " " << mk_pp(s, m) << " " << mk_pp(l, m) << "\n";);
    expr_ref le = mk_len(e);
    expr_ref ls = mk_len(s);
    expr_ref ls_minus_l(mk_sub(ls, l), m);
    expr_ref y(mk_skolem(m_post, s, ls_minus_l), m);
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref ey = mk_concat(e, y);
    literal l_ge_0 = mk_simplified_literal(m_autil.mk_ge(l, zero));
    literal l_le_s = mk_simplified_literal(m_autil.mk_le(mk_sub(l, ls), zero));
    add_axiom(~l_ge_0, ~l_le_s, mk_seq_eq(s, ey));
    add_axiom(~l_ge_0, ~l_le_s, mk_eq(l, le, false));
    add_axiom(~l_ge_0, ~l_le_s, mk_eq(ls_minus_l, mk_len(y), false));
    add_axiom(l_le_s, mk_eq(e, s, false));
    add_axiom(l_ge_0, mk_eq_empty(e));
}

/*
  0 <= i <= len(s) => s = xe & i = len(x)    
  i < 0 => e = empty
  i > len(s) => e = empty
 */
void theory_seq::add_extract_suffix_axiom(expr* e, expr* s, expr* i) {
    expr_ref x(mk_skolem(m_pre, s, i), m);
    expr_ref lx = mk_len(x);
    expr_ref ls = mk_len(s);
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref xe = mk_concat(x, e);
    literal le_is_0 = mk_eq_empty(e);
    literal i_ge_0 = mk_simplified_literal(m_autil.mk_ge(i, zero));
    literal i_le_s = mk_simplified_literal(m_autil.mk_le(mk_sub(i, ls), zero));
    add_axiom(~i_ge_0, ~i_le_s, mk_seq_eq(s, xe));
    add_axiom(~i_ge_0, ~i_le_s, mk_eq(i, lx, false));
    add_axiom(i_ge_0, le_is_0);
    add_axiom(i_le_s, le_is_0);
}


/*
   let e = at(s, i)

   0 <= i < len(s) -> s = xey & len(x) = i & len(e) = 1
   i < 0 \/ i >= len(s) -> e = empty

*/
void theory_seq::add_at_axiom(expr* e) {
    TRACE("seq", tout << "at-axiom: " << mk_pp(e, m) << "\n";);
    expr* s = nullptr, *i = nullptr;
    VERIFY(m_util.str.is_at(e, s, i));
    expr_ref zero(m_autil.mk_int(0), m);
    expr_ref one(m_autil.mk_int(1), m);
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
    expr_ref len_s = mk_len(s);
    literal i_ge_0 = mk_simplified_literal(m_autil.mk_ge(i, zero));
    literal i_ge_len_s = mk_simplified_literal(m_autil.mk_ge(mk_sub(i, mk_len(s)), zero));

    rational iv;
    if (m_autil.is_numeral(i, iv) && iv.is_int() && !iv.is_neg()) {
        expr_ref_vector es(m);
        expr_ref nth(m);
        unsigned k = iv.get_unsigned();
        for (unsigned j = 0; j <= k; ++j) {
            es.push_back(m_util.str.mk_unit(mk_nth(s, m_autil.mk_int(j))));
        }
        nth = es.back();
        es.push_back(mk_skolem(m_tail, s, i));
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(s, m_util.str.mk_concat(es)));
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(nth, e));        
    }
    else {
        expr_ref len_e = mk_len(e);
        expr_ref x = mk_skolem(m_pre, s, i);
        expr_ref y = mk_skolem(m_tail, s, i);
        expr_ref xey   = mk_concat(x, e, y);
        expr_ref len_x = mk_len(x);
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(s, xey));
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false));
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false));
    }

    add_axiom(i_ge_0, mk_eq(e, emp, false));
    add_axiom(~i_ge_len_s, mk_eq(e, emp, false));
}

void theory_seq::add_nth_axiom(expr* e) {
    expr* s = nullptr, *i = nullptr;
    rational n;
    zstring str;
    VERIFY(m_util.str.is_nth(e, s, i));
    if (m_util.str.is_string(s, str) && m_autil.is_numeral(i, n) && n.is_unsigned() && n.get_unsigned() < str.length()) {
        app_ref ch(m_util.str.mk_char(str[n.get_unsigned()]), m);
        add_axiom(mk_eq(ch, e, false));
    }
    else if (!m_internal_nth_table.contains(e)) {
        expr_ref zero(m_autil.mk_int(0), m);
        literal i_ge_0 = mk_simplified_literal(m_autil.mk_ge(i, zero));
        literal i_ge_len_s = mk_simplified_literal(m_autil.mk_ge(mk_sub(i, mk_len(s)), zero));
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(m_util.str.mk_unit(e), m_util.str.mk_at(s, i), false));
    }
}


/*
    lit => s = (nth s 0) ++ (nth s 1) ++ ... ++ (nth s idx) ++ (tail s idx)
*/
void theory_seq::ensure_nth(literal lit, expr* s, expr* idx) {
    TRACE("seq", tout << "ensure-nth: " << lit << " " << mk_pp(s, m) << " " << mk_pp(idx, m) << "\n";);
    rational r;
    SASSERT(get_context().get_assignment(lit) == l_true);
    VERIFY(m_autil.is_numeral(idx, r) && r.is_unsigned());
    unsigned _idx = r.get_unsigned();
    expr_ref head(m), tail(m), conc(m), len1(m), len2(m);
    expr_ref_vector elems(m);

    expr* s2 = s;
    for (unsigned j = 0; j <= _idx; ++j) {
        mk_decompose(s2, head, tail);
        elems.push_back(head);
        len1 = mk_len(s2);
        len2 = m_autil.mk_add(m_autil.mk_int(1), mk_len(tail));
        propagate_eq(lit, len1, len2, false);
        s2 = tail;
    }
    elems.push_back(s2);
    conc = mk_concat(elems, m.get_sort(s));
    propagate_eq(lit, s, conc, true);
}

literal theory_seq::mk_simplified_literal(expr * _e) {
    expr_ref e(_e, m);
    m_rewrite(e);
    return mk_literal(e);
}

literal theory_seq::mk_literal(expr* _e) {
    expr_ref e(_e, m);
    context& ctx = get_context();
    ensure_enode(e);
    return ctx.get_literal(e);
}

literal theory_seq::mk_seq_eq(expr* a, expr* b) {
    SASSERT(m_util.is_seq(a));
    return mk_literal(mk_skolem(m_eq, a, b, nullptr, nullptr, m.mk_bool_sort()));
}

literal theory_seq::mk_preferred_eq(expr* a, expr* b) {
    context& ctx = get_context();
    ctx.assume_eq(ensure_enode(a), ensure_enode(b));
    literal lit = mk_eq(a, b, false);
    ctx.force_phase(lit);
    return lit;
}

literal theory_seq::mk_eq_empty(expr* _e, bool phase) {
    context& ctx = get_context();
    expr_ref e(_e, m);
    SASSERT(m_util.is_seq(e));
    expr_ref emp(m);
    zstring s;
    if (m_util.str.is_empty(e)) {
        return true_literal;
    }
    expr_ref_vector concats(m);
    m_util.str.get_concat(e, concats);
    for (auto c : concats) {
        if (m_util.str.is_unit(c)) {
            return false_literal;
        }
        if (m_util.str.is_string(c, s) && s.length() > 0) {
            return false_literal;
        }
    }
    emp = m_util.str.mk_empty(m.get_sort(e));

    literal lit = mk_eq(e, emp, false);
    ctx.force_phase(phase?lit:~lit);
    ctx.mark_as_relevant(lit);
    return lit;
}

void theory_seq::push_lit_as_expr(literal l, expr_ref_vector& buf) {
    expr* e = get_context().bool_var2expr(l.var());
    if (l.sign()) e = m.mk_not(e);
    buf.push_back(e);
}

void theory_seq::add_axiom(literal l1, literal l2, literal l3, literal l4, literal l5) {
    context& ctx = get_context();
    literal_vector lits;
    expr_ref_vector exprs(m);
    if (l1 == true_literal || l2 == true_literal || l3 == true_literal || l4 == true_literal || l5 == true_literal) return;
    if (l1 != null_literal && l1 != false_literal) { ctx.mark_as_relevant(l1); lits.push_back(l1); push_lit_as_expr(l1, exprs); }
    if (l2 != null_literal && l2 != false_literal) { ctx.mark_as_relevant(l2); lits.push_back(l2); push_lit_as_expr(l2, exprs); }
    if (l3 != null_literal && l3 != false_literal) { ctx.mark_as_relevant(l3); lits.push_back(l3); push_lit_as_expr(l3, exprs); }
    if (l4 != null_literal && l4 != false_literal) { ctx.mark_as_relevant(l4); lits.push_back(l4); push_lit_as_expr(l4, exprs); }
    if (l5 != null_literal && l5 != false_literal) { ctx.mark_as_relevant(l5); lits.push_back(l5); push_lit_as_expr(l5, exprs); }
    TRACE("seq", ctx.display_literals_verbose(tout << "assert:\n", lits) << "\n";);
    m_new_propagation = true;
    ++m_stats.m_add_axiom;
    if (m.has_trace_stream()) {
        app_ref body(m);
        body = m.mk_or(exprs.size(), exprs.c_ptr());
        log_axiom_instantiation(body);
    }
    ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
}


expr_ref theory_seq::coalesce_chars(expr* const& e) {
    context& ctx = get_context();
    expr* s;
    unsigned ch;
    expr_ref result(m);
    if (m_util.str.is_concat(e)) {
        expr_ref_vector rs(m), concats(m);
        m_util.str.get_concat(e, concats);
        for (unsigned i = 0; i < concats.size(); ++i) {
            expr_ref tmp(coalesce_chars(concats[i].get()), m);
            if (m_util.str.is_empty(tmp)) continue;
            zstring zs, a;
            bool flag = false;
            while (m_util.str.is_string(tmp, a)) {
                if (flag)
                    zs = zs + a;
                else
                    zs = a;
                flag = true;
                if (i < concats.size()-1)
                    tmp = coalesce_chars(concats[++i].get());
                else {
                    ++i;
                    break;
                }
            }
            if (flag) {
                rs.push_back(m_util.str.mk_string(zs));
                if (i < concats.size())
                    rs.push_back(tmp);
            }
            else
                rs.push_back(tmp);
        }
        SASSERT(rs.size() > 0);
        if (rs.size() > 1) {
            return expr_ref(m_util.str.mk_concat(rs.size(), rs.c_ptr()), m);
        }
        else {
            result = e;
            return result;
        }
    }
    else if (m_util.str.is_unit(e, s) && m_util.is_const_char(s, ch) &&
             BR_FAILED != m_seq_rewrite.mk_app_core(to_app(e)->get_decl(), 1, &s, result)) {
        if (!ctx.e_internalized(result))
            ctx.internalize(result, false);
        return result;
    }
    result = e;
    return result;
}

expr_ref theory_seq::mk_skolem(symbol const& name, expr* e1, expr* e2, expr* e3, expr*e4, sort* range) {
    expr* es[4] = { e1, e2, e3, e4 };
    unsigned len = e4?4:(e3?3:(e2?2:1));

    if (!range) {
        range = m.get_sort(e1);
    }
    expr_ref_vector pinned(m);        
    if (name == m_seq_align) {
        for (unsigned i = 0; i < len; ++i) {
            pinned.push_back(coalesce_chars(es[i]));
            es[i] = pinned.back();
            TRACE("seq", tout << mk_pp(es[i], m) << "\n";);
        }
    }
    return expr_ref(m_util.mk_skolem(name, len, es, range), m);
}

bool theory_seq::is_skolem(symbol const& s, expr* e) const {
    return m_util.is_skolem(e) && to_app(e)->get_decl()->get_parameter(0).get_symbol() == s;
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

void theory_seq::propagate_eq(literal lit, expr* e1, expr* e2, bool add_to_eqs) {
    literal_vector lits;
    lits.push_back(lit);
    propagate_eq(nullptr, lits, e1, e2, add_to_eqs);
}

void theory_seq::propagate_eq(dependency* deps, literal_vector const& _lits, expr* e1, expr* e2, bool add_to_eqs) {
    context& ctx = get_context();

    enode* n1 = ensure_enode(e1);
    enode* n2 = ensure_enode(e2);
    if (n1->get_root() == n2->get_root()) {
        return;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    
    literal_vector lits(_lits);
    enode_pair_vector eqs;
    if (!linearize(deps, eqs, lits))
        return;
    
    if (add_to_eqs) {
        deps = mk_join(deps, _lits);
        new_eq_eh(deps, n1, n2);
    }
    TRACE("seq",
          tout << "assert: " << mk_pp(e1, m) << " = " << mk_pp(e2, m) << " <- \n";
          if (!lits.empty()) { ctx.display_literals_verbose(tout, lits) << "\n"; });
    justification* js =
        ctx.mk_justification(
            ext_theory_eq_propagation_justification(
                get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), n1, n2));

    m_new_propagation = true;
    if (m.has_trace_stream()) {
        app_ref body(m);
        body = m.mk_eq(e1, e2);
        log_axiom_instantiation(body);
    }
    ctx.assign_eq(n1, n2, eq_justification(js));
    if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
}


void theory_seq::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    expr* e = ctx.bool_var2expr(v);
    expr* e1 = nullptr, *e2 = nullptr;
    expr_ref f(m);
    literal lit(v, !is_true);

    if (m_util.str.is_prefix(e, e1, e2)) {
        if (is_true) {
            f = mk_skolem(m_prefix, e1, e2);
            f = mk_concat(e1, f);
            propagate_eq(lit, f, e2, true);
            //literal len1_le_len2 = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(e2), mk_len(e1)), m_autil.mk_int(0)));
            //add_axiom(~lit, len1_le_len2);
        }
        else {
            propagate_not_prefix(e);
        }
    }
    else if (m_util.str.is_suffix(e, e1, e2)) {
        if (is_true) {
            f = mk_skolem(m_suffix, e1, e2);
            f = mk_concat(f, e1);
            propagate_eq(lit, f, e2, true);
            //literal len1_le_len2 = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(e2), mk_len(e1)), m_autil.mk_int(0)));
            //add_axiom(~lit, len1_le_len2);
        }
        else {
            propagate_not_suffix(e);
        }
    }
    else if (m_util.str.is_contains(e, e1, e2)) {
        expr_ref_vector disj(m);
        // disabled pending regression on issue 1196
        if (false && m_seq_rewrite.reduce_contains(e1, e2, disj)) {
            literal_vector lits;
            literal lit = mk_literal(e);
            lits.push_back(~lit);
            for (expr* d : disj) {
                lits.push_back(mk_literal(d));
            }
            ++m_stats.m_add_axiom;            
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(e, m.mk_or(disj.size(), disj.c_ptr()));
                log_axiom_instantiation(body);
            }
            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            for (expr* d : disj) {
                add_axiom(lit, ~mk_literal(d));
            }
        }
        else if (is_true) {
            expr_ref f1 = mk_skolem(m_indexof_left, e1, e2);
            expr_ref f2 = mk_skolem(m_indexof_right, e1, e2);
            f = mk_concat(f1, e2, f2);
            propagate_eq(lit, f, e1, true);
            //literal len2_le_len1 = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(e1), mk_len(e2)), m_autil.mk_int(0)));
            //add_axiom(~lit, len2_le_len1);
        }
        else if (!canonizes(false, e)) {
            propagate_non_empty(lit, e2);
            dependency* dep = m_dm.mk_leaf(assumption(lit));
            literal len_gt = mk_simplified_literal(m_autil.mk_le(mk_sub(mk_len(e1), mk_len(e2)), 
                                                                 m_autil.mk_int(-1)));
            ctx.force_phase(len_gt);
            m_ncs.push_back(nc(expr_ref(e, m), len_gt, dep));
        }
    }
    else if (is_accept(e)) {
        if (is_true) {
            propagate_accept(lit, e);
        }
    }
    else if (is_step(e)) {
        if (is_true) {
            propagate_step(lit, e);
        }
    }
    else if (is_eq(e, e1, e2)) {
        if (is_true) {
            propagate_eq(lit, e1, e2, true);
        }
    }
    else if (m_util.str.is_in_re(e)) {
        propagate_in_re(e, is_true);
    }
    else if (is_skolem(symbol("seq.split"), e)) {
        // propagate equalities
    }
    else if (is_skolem(symbol("seq.is_digit"), e)) {
        // no-op
    }
    else if (is_max_unfolding(e)) {
        // no-op
    }
    else {
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        UNREACHABLE();
    }
}

void theory_seq::new_eq_eh(theory_var v1, theory_var v2) {
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);
    dependency* deps = m_dm.mk_leaf(assumption(n1, n2));
    new_eq_eh(deps, n1, n2);
}

lbool theory_seq::regex_are_equal(expr* r1, expr* r2) {
    if (r1 == r2) {
        return l_true;
    }
    expr* d1 = m_util.re.mk_inter(r1, m_util.re.mk_complement(r2));
    expr* d2 = m_util.re.mk_inter(r2, m_util.re.mk_complement(r1));
    expr_ref diff(m_util.re.mk_union(d1, d2), m);
    eautomaton* aut = get_automaton(diff);
    if (!aut) {
        return l_undef;
    }
    else if (aut->is_empty()) {
        return l_true;
    }
    else {
        return l_false;
    }
}


void theory_seq::new_eq_eh(dependency* deps, enode* n1, enode* n2) {
    TRACE("seq", tout << expr_ref(n1->get_owner(), m) << " = " << expr_ref(n2->get_owner(), m) << "\n";);
    if (n1 != n2 && m_util.is_seq(n1->get_owner())) {
        theory_var v1 = n1->get_th_var(get_id());
        theory_var v2 = n2->get_th_var(get_id());
        if (m_find.find(v1) == m_find.find(v2)) {
            return;
        }
        m_find.merge(v1, v2);
        expr_ref o1(n1->get_owner(), m);
        expr_ref o2(n2->get_owner(), m);
        TRACE("seq", tout << o1 << " = " << o2 << "\n";);
        m_eqs.push_back(mk_eqdep(o1, o2, deps));
        solve_eqs(m_eqs.size()-1);
        enforce_length_coherence(n1, n2);
    }
    else if (n1 != n2 && m_util.is_re(n1->get_owner())) {
        // create an expression for the symmetric difference and imply it is empty.
        enode_pair_vector eqs;
        literal_vector lits;
        context& ctx = get_context();
        switch (regex_are_equal(n1->get_owner(), n2->get_owner())) {
        case l_true:
            break;
        case l_false:
            if (!linearize(deps, eqs, lits)) {
                throw default_exception("could not linearlize assumptions");
            }
            eqs.push_back(enode_pair(n1, n2));
            ctx.set_conflict(
                ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), 0, nullptr)));
            break;
        default:
            throw default_exception("convert regular expressions into automata");            
        }
    }
}

void theory_seq::new_diseq_eh(theory_var v1, theory_var v2) {
    enode* n1 = get_enode(v1);
    enode* n2 = get_enode(v2);    
    expr_ref e1(n1->get_owner(), m);
    expr_ref e2(n2->get_owner(), m);
    SASSERT(n1->get_root() != n2->get_root());
    if (m_util.is_re(n1->get_owner())) {
        enode_pair_vector eqs;
        literal_vector lits;
        context& ctx = get_context();
        switch (regex_are_equal(e1, e2)) {
        case l_false:
            return;
        case l_true: {
            literal lit = mk_eq(e1, e2, false);
            lits.push_back(~lit);
            ctx.set_conflict(
                ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), 0, nullptr)));
            return;
        }
        default:
            throw default_exception("convert regular expressions into automata");            
        }
    }
    m_exclude.update(e1, e2);
    expr_ref eq(m.mk_eq(e1, e2), m);
    TRACE("seq", tout << "new disequality " << get_context().get_scope_level() << ": " << eq << "\n";);
    m_rewrite(eq);
    if (!m.is_false(eq)) {
        literal lit = mk_eq(e1, e2, false);

        if (m_util.str.is_empty(e2)) {
            std::swap(e1, e2);
        }

        dependency* dep = m_dm.mk_leaf(assumption(~lit));
        m_nqs.push_back(ne(e1, e2, dep));
        solve_nqs(m_nqs.size() - 1);        
    }
}

void theory_seq::push_scope_eh() {
    theory::push_scope_eh();
    m_rep.push_scope();
    m_exclude.push_scope();
    m_dm.push_scope();
    m_trail_stack.push_scope();
    m_trail_stack.push(value_trail<theory_seq, unsigned>(m_axioms_head));
    m_eqs.push_scope();
    m_nqs.push_scope();
    m_ncs.push_scope();
    m_internal_nth_lim.push_back(m_internal_nth_es.size());
}

void theory_seq::pop_scope_eh(unsigned num_scopes) {
    context& ctx = get_context();
    m_trail_stack.pop_scope(num_scopes);
    theory::pop_scope_eh(num_scopes);
    m_dm.pop_scope(num_scopes);
    m_rep.pop_scope(num_scopes);
    m_exclude.pop_scope(num_scopes);
    m_eqs.pop_scope(num_scopes);
    m_nqs.pop_scope(num_scopes);
    m_ncs.pop_scope(num_scopes);
    m_rewrite.reset();    
    if (ctx.get_base_level() > ctx.get_scope_level() - num_scopes) {
        m_replay.reset();
    }
    if (m_len_prop_lvl > (int) ctx.get_scope_level()) {
        m_len_prop_lvl = ctx.get_scope_level();
        m_len_offset.reset();
    }
    unsigned old_sz = m_internal_nth_lim[m_internal_nth_lim.size() - num_scopes];
    for (unsigned i = m_internal_nth_es.size(); i-- > old_sz; ) {
        m_internal_nth_table.erase(m_internal_nth_es.get(i));
    }
    m_internal_nth_es.shrink(old_sz);
    m_internal_nth_lim.shrink(m_internal_nth_lim.size() - num_scopes);
}

void theory_seq::restart_eh() {
}

void theory_seq::relevant_eh(app* n) {
    if (m_util.str.is_index(n)   ||
        m_util.str.is_replace(n) ||
        m_util.str.is_extract(n) ||
        m_util.str.is_at(n) ||
        m_util.str.is_nth(n) ||
        m_util.str.is_empty(n) ||
        m_util.str.is_string(n) ||
        m_util.str.is_itos(n) || 
        m_util.str.is_stoi(n)) {
        enque_axiom(n);
    }

    if (m_util.str.is_itos(n) ||
        m_util.str.is_stoi(n)) {
        add_int_string(n);
    }

    expr* arg;
    if (m_util.str.is_length(n, arg) && !has_length(arg) && get_context().e_internalized(arg)) {
        enforce_length(arg);
    }
}


eautomaton* theory_seq::get_automaton(expr* re) {
    eautomaton* result = nullptr;
    if (m_re2aut.find(re, result)) {
        return result;
    }
    if (!m_mk_aut.has_solver()) {
        m_mk_aut.set_solver(alloc(seq_expr_solver, m, get_context().get_fparams()));
    }
    result = m_mk_aut(re);
    CTRACE("seq", result, { display_expr d(m); result->display(tout, d); });
    m_automata.push_back(result);
    m_re2aut.insert(re, result);
    m_res.push_back(re);
    return result;
}

literal theory_seq::mk_accept(expr* s, expr* idx, expr* re, expr* state) {
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re).push_back(state);
    return mk_literal(m_util.mk_skolem(m_accept, args.size(), args.c_ptr(), m.mk_bool_sort()));
}

bool theory_seq::is_accept(expr* e, expr*& s, expr*& idx, expr*& re, unsigned& i, eautomaton*& aut) {
    if (is_accept(e)) {
        rational r;
        s  = to_app(e)->get_arg(0);
        idx = to_app(e)->get_arg(1);
        re = to_app(e)->get_arg(2);
        TRACE("seq", tout << mk_pp(re, m) << "\n";);
        VERIFY(m_autil.is_numeral(to_app(e)->get_arg(3), r));
        SASSERT(r.is_unsigned());
        i = r.get_unsigned();
        aut = get_automaton(re);
        return true;
    }
    else {
        return false;
    }
}

bool theory_seq::is_step(expr* e) const {
    return is_skolem(m_aut_step, e);
}

bool theory_seq::is_step(expr* e, expr*& s, expr*& idx, expr*& re, expr*& i, expr*& j, expr*& t) const {
    if (is_step(e)) {
        s    = to_app(e)->get_arg(0);
        idx  = to_app(e)->get_arg(1);
        re   = to_app(e)->get_arg(2);
        i    = to_app(e)->get_arg(3);
        j    = to_app(e)->get_arg(4);
        t    = to_app(e)->get_arg(5);
        return true;
    }
    else {
        return false;
    }
}

expr_ref theory_seq::mk_step(expr* s, expr* idx, expr* re, unsigned i, unsigned j, expr* t) {
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re);
    args.push_back(m_autil.mk_int(i));
    args.push_back(m_autil.mk_int(j));
    args.push_back(t);
    return expr_ref(m_util.mk_skolem(m_aut_step, args.size(), args.c_ptr(), m.mk_bool_sort()), m);
}

/**
   step(s, idx, re, i, j, t) -> nth(s, idx) == t & len(s) > idx
   step(s, idx, re, i, j, t) -> accept(s, idx + 1, re, j)
*/
void theory_seq::propagate_step(literal lit, expr* step) {
    SASSERT(get_context().get_assignment(lit) == l_true);
    expr* re = nullptr, *s = nullptr, *t = nullptr, *idx = nullptr, *i = nullptr, *j = nullptr;
    VERIFY(is_step(step, s, idx, re, i, j, t));
    
    TRACE("seq", tout << mk_pp(step, m) << " -> " << mk_pp(t, m) << "\n";);
    propagate_lit(nullptr, 1, &lit, mk_literal(t));

    expr_ref len_s = mk_len(s);
    rational lo;
    rational _idx;
    VERIFY(m_autil.is_numeral(idx, _idx));
    if (lower_bound(len_s, lo) && lo.is_unsigned() && lo >= _idx) {
        // skip
    }
    else {
        propagate_lit(nullptr, 1, &lit, ~mk_literal(m_autil.mk_le(len_s, idx)));
    }
    ensure_nth(lit, s, idx);

    expr_ref idx1(m_autil.mk_int(_idx + 1), m);
    propagate_lit(nullptr, 1, &lit, mk_accept(s, idx1, re, j));
}

/**
   acc(s, idx, re, i) ->  \/ step(s, idx, re, i, j, t)                if i is non-final
   acc(s, idx, re, i) -> len(s) <= idx \/ step(s, idx, re, i, j, t)   if i is final   
   acc(s, idx, re, i) -> len(s) >= idx    if i is final
   acc(s, idx, re, i) -> len(s) > idx     if i is non-final
   acc(s, idx, re, i) -> idx < max_unfolding
 */
void theory_seq::propagate_accept(literal lit, expr* acc) {
    ++m_stats.m_propagate_automata;
    expr *e = nullptr, *idx = nullptr, *re = nullptr;
    unsigned src = 0;
    context& ctx = get_context();
    rational _idx;
    eautomaton* aut = nullptr;
    VERIFY(is_accept(acc, e, idx, re, src, aut));
    VERIFY(m_autil.is_numeral(idx, _idx));
    VERIFY(aut);
    if (aut->is_sink_state(src)) {
        propagate_lit(nullptr, 1, &lit, false_literal);
        return;
    }


    expr_ref len = mk_len(e);
    literal_vector lits;
    lits.push_back(~lit);
    if (aut->is_final_state(src)) {
        lits.push_back(mk_literal(m_autil.mk_le(len, idx)));
        propagate_lit(nullptr, 1, &lit, mk_literal(m_autil.mk_ge(len, idx)));
    }
    else {
        propagate_lit(nullptr, 1, &lit, ~mk_literal(m_autil.mk_le(len, idx)));
    }


    eautomaton::moves mvs;
    aut->get_moves_from(src, mvs);
    TRACE("seq", tout << mk_pp(acc, m) << " #moves " << mvs.size() << "\n";);
    expr_ref_vector exprs(m);
    for (auto const& mv : mvs) {
        expr_ref nth = mk_nth(e, idx);
        expr_ref t = mv.t()->accept(nth);
        get_context().get_rewriter()(t);
        expr_ref step_e(mk_step(e, idx, re, src, mv.dst(), t), m);
        literal step = mk_literal(step_e);
        lits.push_back(step);
        exprs.push_back(step_e);
    }
    if (m.has_trace_stream()) {
        app_ref body(m);
        body = m.mk_implies(acc, m.mk_or(exprs.size(), exprs.c_ptr()));
        log_axiom_instantiation(body);
    }
    ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

    if (_idx.get_unsigned() > m_max_unfolding_depth && 
        m_max_unfolding_lit != null_literal && ctx.get_scope_level() > 0) {
        propagate_lit(nullptr, 1, &lit, ~m_max_unfolding_lit);
    }
}

void theory_seq::add_theory_assumptions(expr_ref_vector & assumptions) {
    TRACE("seq", tout << "add_theory_assumption " << m_util.has_re() << "\n";);
    if (m_util.has_re()) {
        expr_ref dlimit(m);
        dlimit = mk_max_unfolding_depth();
        m_trail_stack.push(value_trail<theory_seq, literal>(m_max_unfolding_lit));
        m_max_unfolding_lit = mk_literal(dlimit);        
        assumptions.push_back(dlimit);
    }
}

bool theory_seq::should_research(expr_ref_vector & unsat_core) {
    TRACE("seq", tout << unsat_core << " " << m_util.has_re() << "\n";);
    if (!m_util.has_re()) {
        return false;
    }
    for (auto & e : unsat_core) {
        if (is_max_unfolding(e)) {
            m_max_unfolding_depth = (3 * m_max_unfolding_depth) / 2 + 1;
            IF_VERBOSE(1, verbose_stream() << "(smt.seq :increase-depth " << m_max_unfolding_depth << ")\n");
            return true;
        }
    }
    return false;
}


/*
  !prefix(e1,e2) => e1 != ""
  !prefix(e1,e2) => len(e1) > len(e2) or e1 = xcy & e2 = xdz & c != d
*/

void theory_seq::propagate_not_prefix(expr* e) {
    context& ctx = get_context();
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(m_util.str.is_prefix(e, e1, e2));
    literal lit = ctx.get_literal(e);
    SASSERT(ctx.get_assignment(lit) == l_false);
    if (canonizes(false, e)) {
        return;
    }
    propagate_non_empty(~lit, e1);
    literal e1_gt_e2 = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(e1), mk_len(e2)), m_autil.mk_int(1)));
    sort* char_sort = nullptr;
    VERIFY(m_util.is_seq(m.get_sort(e1), char_sort));
    expr_ref x = mk_skolem(symbol("seq.prefix.x"), e1, e2);
    expr_ref y = mk_skolem(symbol("seq.prefix.y"), e1, e2);
    expr_ref z = mk_skolem(symbol("seq.prefix.z"), e1, e2);
    expr_ref c = mk_skolem(symbol("seq.prefix.c"), e1, e2, nullptr, nullptr, char_sort);
    expr_ref d = mk_skolem(symbol("seq.prefix.d"), e1, e2, nullptr, nullptr, char_sort);
    add_axiom(lit, e1_gt_e2, mk_seq_eq(e1, mk_concat(x, m_util.str.mk_unit(c), y)));
    add_axiom(lit, e1_gt_e2, mk_seq_eq(e2, mk_concat(x, m_util.str.mk_unit(d), z)), mk_seq_eq(e2, x));
    add_axiom(lit, e1_gt_e2, ~mk_eq(c, d, false));
}


/*
  !suffix(e1,e2) => e1 != ""
  !suffix(e1,e2) => len(e1) > len(e2) or e1 = ycx & e2 = zdx & c != d
*/

void theory_seq::propagate_not_suffix(expr* e) {
    context& ctx = get_context();
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(m_util.str.is_suffix(e, e1, e2));
    literal lit = ctx.get_literal(e);
    SASSERT(ctx.get_assignment(lit) == l_false);
    if (canonizes(false, e)) {
        return;
    }
    propagate_non_empty(~lit, e1);
    literal e1_gt_e2 = mk_simplified_literal(m_autil.mk_ge(mk_sub(mk_len(e1), mk_len(e2)), m_autil.mk_int(1)));    
    sort* char_sort = nullptr;
    VERIFY(m_util.is_seq(m.get_sort(e1), char_sort));
    expr_ref x = mk_skolem(symbol("seq.suffix.x"), e1, e2);
    expr_ref y = mk_skolem(symbol("seq.suffix.y"), e1, e2);
    expr_ref z = mk_skolem(symbol("seq.suffix.z"), e1, e2);
    expr_ref c = mk_skolem(symbol("seq.suffix.c"), e1, e2, nullptr, nullptr, char_sort);
    expr_ref d = mk_skolem(symbol("seq.suffix.d"), e1, e2, nullptr, nullptr, char_sort);
    add_axiom(lit, e1_gt_e2, mk_seq_eq(e1, mk_concat(y, m_util.str.mk_unit(c), x)));
    add_axiom(lit, e1_gt_e2, mk_seq_eq(e2, mk_concat(z, m_util.str.mk_unit(d), x)));
    add_axiom(lit, e1_gt_e2, ~mk_eq(c, d, false));
}



bool theory_seq::canonizes(bool sign, expr* e) {
    context& ctx = get_context();
    dependency* deps = nullptr;
    expr_ref cont = canonize(e, deps);
    TRACE("seq", tout << mk_pp(e, m) << " -> " << cont << "\n";
          if (deps) display_deps(tout, deps););
    if ((m.is_true(cont) && !sign) ||
        (m.is_false(cont) && sign)) {
        TRACE("seq", display(tout); tout << ctx.get_assignment(ctx.get_literal(e)) << "\n";);
        propagate_lit(deps, 0, nullptr, ctx.get_literal(e));
        return true;
    }
    if ((m.is_false(cont) && !sign) ||
        (m.is_true(cont) && sign)) {
        TRACE("seq", display(tout););
        return true;
    }
    return false;
}


void theory_seq::get_ite_concat(expr* e, ptr_vector<expr>& concats) {
    expr* e1 = nullptr, *e2 = nullptr;
    while (true) {
        e = m_rep.find(e);
        e = get_ite_value(e);
        if (m_util.str.is_concat(e, e1, e2)) {
            get_ite_concat(e1, concats);
            e = e2;
            continue;
        }        
        concats.push_back(e);        
        return;
    }
}
