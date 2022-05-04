/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_global_generalizer.cpp

Abstract:

  Global Guidance for Spacer

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "muz/spacer/spacer_global_generalizer.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_cluster.h"
#include "muz/spacer/spacer_concretize.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"

using namespace spacer;

namespace {

// LOCAL HELPER FUNCTIONS IN ANONYMOUS NAMESPACE

struct compute_lcm_proc {
    ast_manager &m;
    arith_util m_arith;
    rational m_val;
    compute_lcm_proc(ast_manager &a_m) : m(a_m), m_arith(m), m_val(1) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val)) {
            m_val = lcm(denominator(abs(val)), m_val);
        }
    }
};

/// Check whether there are Real constants in \p c
bool contains_reals(const app_ref_vector &c) {
    arith_util m_arith(c.get_manager());
    for (auto *f : c) {
        if (m_arith.is_real(f)) return true;
    }
    return false;
}

// Check whether there are Int constants in \p c
bool contains_ints(const app_ref_vector &c) {
    arith_util m_arith(c.get_manager());
    for (auto *f : c) {
        if (m_arith.is_int(f)) return true;
    }
    return false;
}

// Check whether \p sub contains a mapping to a bv_numeral.
// return bv_size of the bv_numeral in the first such mapping.
bool contains_bv(ast_manager &m, const substitution &sub, unsigned &sz) {
    bv_util m_bv(m);
    std::pair<unsigned, unsigned> v;
    expr_offset r;
    rational num;
    for (unsigned j = 0, sz = sub.get_num_bindings(); j < sz; j++) {
        sub.get_binding(j, v, r);
        if (m_bv.is_numeral(r.get_expr(), num, sz)) return true;
    }
    return false;
}

// Check whether 1) all expressions in the range of \p sub are bv_numerals 2)
// all bv_numerals in range are of size sz
bool all_same_sz(ast_manager &m, const substitution &sub, unsigned sz) {
    bv_util m_bv(m);
    std::pair<unsigned, unsigned> v;
    expr_offset r;
    rational num;
    unsigned n_sz;
    for (unsigned j = 0; j < sub.get_num_bindings(); j++) {
        sub.get_binding(j, v, r);
        if (!m_bv.is_numeral(r.get_expr(), num, n_sz) || n_sz != sz)
            return false;
    }
    return true;
}

/// Check whether there is an equivalent of function \p f in LRA
bool has_lra_equiv(const expr_ref &f) {
    ast_manager &m = f.m();
    arith_util a(m);

    // uninterpreted constants do not have arguments. So equivalent function
    // exists.
    if (is_uninterp_const(f)) return true;
    return is_app(f) &&
           to_app(f)->get_decl()->get_family_id() == a.get_family_id();
}

/// Get lcm of all the denominators of all the rational values in e
rational compute_lcm(expr *e, ast_manager &m) {
    compute_lcm_proc g(m);
    for_each_expr(g, e);
    TRACE("subsume_verb",
          tout << "lcm of " << mk_pp(e, m) << " is " << g.m_val << "\n";);
    return g.m_val;
}

// clang-format off
/// Removes all occurrences of (to_real t) from \p fml where t is a constant
///
/// Applies the following rewrites upto depth \p depth
/// v:Real                                                        --> mk_int(v) where v is a real value
/// (to_real v:Int)                                               --> v
/// (to_int v)                                                    --> (strip_to_real v)
/// (store A (to_int (to_real i0)) ... (to_int (to_real iN)) k)   --> (store A i0 ... iN
///                                                                      (strip_to_real k))
/// (select A (to_int (to_real i0)) ... (to_int (to_real iN)))    --> (select A i0 ... iN)
/// (op (to_real a0) ... (to_real aN))                            --> (op a0 ... aN) where op is an
///                                                                    arithmetic operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
// clang-format on
void strip_to_real(expr_ref &fml, unsigned depth = 3) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    rational r;

    if (arith.is_numeral(fml, r)) {
        SASSERT(denominator(r).is_one());
        fml = arith.mk_int(r);
        return;
    }

    if (depth == 0) { return; }

    if (arith.is_to_real(fml)) {
        fml = to_app(fml)->get_arg(0);
        return;
    }
    if (arith.is_to_int(fml) && arith.is_to_real(to_app(fml)->get_arg(0))) {
        expr *arg = to_app(fml)->get_arg(0);
        fml = to_app(arg)->get_arg(0);
        return;
    }

    if (!is_app(fml)) return;

    app *f_app = to_app(fml);
    expr_ref_buffer new_args(m);
    expr_ref child(m);
    for (unsigned i = 0, sz = f_app->get_num_args(); i < sz; i++) {
        child = f_app->get_arg(i);
        strip_to_real(child, depth - 1);
        new_args.push_back(child);
    }
    fml = m.mk_app(f_app->get_family_id(), f_app->get_decl_kind(),
                   new_args.size(), new_args.data());
    return;
}

/// Coerces a rational inequality to a semantically equivalent inequality with
/// integer coefficients
///
/// Works on arithmetic (in)equalities
/// if fml contains a mod, fml is not normalized
/// otherwise, lcm of fml is computed and lcm * fml is computed
void to_int_term(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);

    if (!(arith.is_arith_expr(fml) || m.is_eq(fml))) return;
    if (!contains_real(fml)) return;

    app *fml_app = to_app(fml);
    SASSERT(fml_app->get_num_args() == 2);
    expr_ref lhs(fml_app->get_arg(0), m);
    expr_ref rhs(fml_app->get_arg(1), m);

    // mod not supported
    SASSERT(!contains_mod(fml));

    rational lcm = compute_lcm(fml, m);
    SASSERT(lcm != rational::zero());

    mul_by_rat(lhs, lcm);
    mul_by_rat(rhs, lcm);

    strip_to_real(lhs);
    strip_to_real(rhs);
    fml =
        m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(), lhs, rhs);
}

/// Convert all fractional constants in \p fml to integers
void to_int(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    expr_ref_vector fml_vec(m), new_fml(m);
    expr_ref new_lit(m);

    flatten_and(fml, fml_vec);
    for (auto *lit : fml_vec) {
        new_lit = lit;
        to_int_term(new_lit);
        new_fml.push_back(new_lit);
    }
    fml = mk_and(new_fml);
}

// clang-format off
/// Wrap integer uninterpreted constants in expression \p fml with (to_real)
///
/// only supports arithmetic expressions
/// Applies the following rewrite rules upto depth \p depth
/// (to_real_term c)                                           --> (c:Real) where c is a numeral
/// (to_real_term i:Int)                                       --> (to_real i) where i is a constant/var
/// (to_real_term (select A i0:Int ... iN:Int))                --> (select A (to_int (to_real i0)) ...
///                                                                          (to_int (to_real iN)))
/// (to_real_term (store A i0:Int ... iN:Int k))               --> (store A (to_int (to_real i0)) ...
///                                                                         (to_int (to_real iN))
///                                                                         (to_real_term k))
/// (to_real_term (op (a0:Int) ... (aN:Int)))                  --> (op (to_real a0) ... (to_real aN))
///                                                                where op is
///                                                                an arithmetic
///                                                                operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
// clang-format on
static void to_real_term(expr_ref &fml, unsigned depth = 3) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    datatype_util datatype(m);
    if (!arith.is_int_real(fml)) return;
    rational r;
    if (arith.is_numeral(fml, r)) {
        fml = arith.mk_real(r);
        return;
    }
    if (is_uninterp_const(fml)) {
        if (arith.is_int(fml)) fml = arith.mk_to_real(fml);
        return;
    }
    if (arith.is_to_real(fml)) {
        expr *arg = to_app(fml)->get_arg(0);
        if (arith.is_numeral(arg, r)) fml = arith.mk_real(r);
        return;
    }

    if (is_uninterp(fml)) return;
    if (depth == 0) return;
    SASSERT(is_app(fml));
    app *fml_app = to_app(fml);
    expr *const *args = fml_app->get_args();
    unsigned num_args = fml_app->get_num_args();
    expr_ref_buffer new_args(m);
    expr_ref child(m);

    if (!has_lra_equiv(fml)) {
        new_args.push_back(args[0]);
        for (unsigned i = 1; i < num_args; i++) {
            child = args[i];
            to_real_term(child, depth - 1);
            if (arith.is_int(args[i])) child = arith.mk_to_int(child);
            SASSERT(args[i]->get_sort() == child->get_sort());
            new_args.push_back(child);
        }
        fml = m.mk_app(fml_app->get_decl(), new_args);
    } else {
        for (unsigned i = 0; i < num_args; i++) {
            child = args[i];
            to_real_term(child, depth - 1);
            new_args.push_back(child);
        }
        // The mk_app method selects the function sort based on the sort of
        // new_args
        fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                       new_args.size(), new_args.data());
    }
    return;
}

/// Wrap integer uninterpreted constants in conjunction \p fml with
/// (to_real)
void to_real(expr_ref &fml) {
    ast_manager &m = fml.get_manager();

    // cannot use an expr_ref_buffer since flatten_and operates on
    // expr_ref_vector
    expr_ref_vector fml_vec(m), new_fml(m);
    flatten_and(fml, fml_vec);

    expr_ref_buffer new_args(m);
    expr_ref kid(m), new_f(m);
    for (auto *lit : fml_vec) {
        new_args.reset();
        app *lit_app = to_app(lit);
        for (auto *arg : *lit_app) {
            kid = arg;
            to_real_term(kid);
            new_args.push_back(kid);
        }
        // Uninterpreted functions cannot be created using the mk_app api that
        // is being used.
        if (is_uninterp(lit)) new_f = lit;
        // use this api to change sorts in domain of f
        else
            new_f = m.mk_app(lit_app->get_family_id(), lit_app->get_decl_kind(),
                             new_args.size(), new_args.data());
        new_fml.push_back(new_f);
    }
    fml = mk_and(new_fml);
}

} // namespace

namespace spacer {
lemma_global_generalizer::subsumer::subsumer(ast_manager &a_m, bool use_sage,
                                             bool ground_pob)
    : m(a_m), m_arith(m), m_bv(m), m_cvx_cls(m, use_sage), m_dim_frsh_cnsts(m),
      m_dim_vars(m), m_ground_pob(ground_pob) {
    scoped_ptr<solver_factory> factory(
        mk_smt_strategic_solver_factory(symbol::null));
    m_solver = (*factory)(m, params_ref::get_empty(), false, true, false,
                          symbol::null);
}

lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()),
      m_subsumer(m, ctx.use_sage(), ctx.use_ground_pob()),
      m_do_subsume(ctx.do_subsume()) {}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    generalize(lemma);
}

void lemma_global_generalizer::subsumer::add_dim_vars(const lemma_cluster &lc) {
    expr_offset r;
    std::pair<unsigned, unsigned> v;

    unsigned n_vars = get_num_vars(lc.get_pattern());

    auto &lemmas = lc.get_lemmas();
    const substitution &sub = lemmas.get(0).get_sub();

    for (unsigned j = 0; j < n_vars; j++) {
        // get var id
        sub.get_binding(j, v, r);
        auto *sort = r.get_expr()->get_sort();

        // create a variable for jth dimension, and register with convex closure
        var *var = m.mk_var(v.first, sort);
        m_dim_vars[j] = var;
        m_cvx_cls.set_dimension(j, var);

        // create a fresh skolem constant for the jth variable
        m_dim_frsh_cnsts[j] = m.mk_fresh_const("mrg_cvx", sort);
    }
}

// Populate m_cvx_cls by 1) collecting all substitutions in the cluster \p lc
// 2) normalizing them to integer numerals
void lemma_global_generalizer::subsumer::populate_cvx_cls(
    const lemma_cluster &lc) {
    expr_offset r;
    std::pair<unsigned, unsigned> v;

    unsigned n_vars = get_num_vars(lc.get_pattern());
    const lemma_info_vector &lemmas = lc.get_lemmas();

    // compute LCM of all denominators numbers in all lemma instances
    rational lemma_lcm = rational::one(), num;
    for (const auto &lemma : lemmas) {
        const substitution &sub = lemma.get_sub();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            if (m_arith.is_numeral(r.get_expr(), num) ||
                m_bv.is_numeral(r.get_expr(), num)) {
                lemma_lcm = lcm(lemma_lcm, abs(denominator(num)));
            }
        }
    }

    m_cvx_cls.set_lcm(lemma_lcm);

    // Populate m_cvx_cls by normalized points corresponding to the
    // substitutions Each point is normalized by multiplying by LCM of all
    // denominators
    vector<rational> point;
    for (const auto &lemma : lemmas) {
        point.reset();

        const substitution &sub = lemma.get_sub();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            if (m_arith.is_numeral(r.get_expr(), num) ||
                m_bv.is_numeral(r.get_expr(), num)) {
                point.push_back(lemma_lcm * num);
            }
        }
        // -- add normalized point to convex closure
        m_cvx_cls.push_back(point);
    }
}

/// Find a representative for \p c
// TODO: replace with a symbolic representative
expr *lemma_global_generalizer::subsumer::find_repr(const model_ref &mdl,
                                                    const app *c) {
    return mdl->get_const_interp(c->get_decl());
}

/// Skolemize implicitly existentially quantified constants
///
/// Constants in \p m_dim_frsh_cnsts are existentially quantified in \p f. They
/// are replaced by specific skolem constants. The \p out vector is populated
/// with corresponding instantiations. Currently, instantiations are values
/// chosen from the model
void lemma_global_generalizer::subsumer::skolemize(expr_ref &f,
                                                   const model_ref &mdl,
                                                   app_ref_vector &out) {
    unsigned idx = out.size();
    app_ref sk(m);
    expr_ref eval(m);
    expr_safe_replace sub(m);

    expr_ref_vector f_cnsts(m);
    spacer::collect_uninterp_consts(f, f_cnsts);

    expr_fast_mark2 marks;
    for (auto *c : f_cnsts) { marks.mark(c); }

    for (unsigned i = 0, sz = m_dim_frsh_cnsts.size(); i < sz; i++) {
        app *c = m_dim_frsh_cnsts.get(i);
        if (!marks.is_marked(c)) continue;

        SASSERT(m_arith.is_int(c));
        // Make skolem constants for ground pob
        sk = mk_zk_const(m, i + idx, c->get_sort());
        eval = find_repr(mdl, c);
        SASSERT(is_app(eval));
        out.push_back(to_app(eval));
        sub.insert(c, sk);
    }
    sub(f.get(), f);
    TRACE("subsume", tout << "skolemized into " << f << "\n";);
    m_dim_frsh_cnsts.reset();
}

///\p hard is a hard constraint and \p soft is a soft constraint that have to be
/// satisfied by mdl
bool lemma_global_generalizer::subsumer::maxsat_with_model(
    const expr_ref &hard, const expr_ref &soft, model_ref &out_model) {
    TRACE("subsume_verb",
          tout << "maxsat with model " << hard << " " << soft << "\n";);
    SASSERT(is_ground(hard));

    solver::scoped_push _sp(*m_solver);
    m_solver->assert_expr(hard);

    expr_ref_buffer tags(m);
    lbool res;
    if (is_ground(soft)) {
        tags.push_back(m.mk_fresh_const("get_mdl_assump", m.mk_bool_sort()));
        m_solver->assert_expr(m.mk_implies(tags.back(), soft));
    }

    res = m_solver->check_sat(tags.size(), tags.data());

    // best-effort -- flip one of the soft constraints
    // in the current use, this is guaranteed to be sat
    if (res != l_true && !tags.empty()) {
        unsigned sz = tags.size();
        tags.set(sz - 1, m.mk_not(tags[sz - 1]));
        res = m_solver->check_sat(tags.size(), tags.data());
    }

    if (res != l_true) { return false; }

    m_solver->get_model(out_model);
    return true;
}

/// Returns false if subsumption is not supported for \p lc
bool lemma_global_generalizer::subsumer::is_handled(const lemma_cluster &lc) {
    // check whether all substitutions are to bv_numerals
    unsigned sz = 0;
    bool bv_clus = contains_bv(m, lc.get_lemmas()[0].get_sub(), sz);
    // If there are no BV numerals, cases are handled.
    // TODO: put restriction on Arrays, non linear arithmetic etc
    if (!bv_clus) return true;
    if (!all_same_sz(m, lc.get_lemmas()[0].get_sub(), sz)) {
        TRACE("subsume",
              tout << "cannot compute cvx cls of different size variables\n";);
        return false;
    }
    return true;
}

void lemma_global_generalizer::subsumer::setup(const lemma_cluster &lc) {
    unsigned n_vars = get_num_vars(lc.get_pattern());
    m_cvx_cls.reset(n_vars);

    m_dim_vars.reset();
    m_dim_vars.reserve(n_vars);

    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);

    unsigned sz = 0;
    if (contains_bv(m, lc.get_lemmas()[0].get_sub(), sz)) {
        m_cvx_cls.set_bv(sz);
    }

    // create variables and corresponding skolems for each dimension in the
    // input space
    add_dim_vars(lc);

    // Add all vectors corresponding to the substitutions of lemmas in the
    // cluster to convex closure computation
    populate_cvx_cls(lc);
}

/// Add variables introduced by cvx_cls to the list of variables
void lemma_global_generalizer::subsumer::add_cvx_cls_vars() {
    for (auto v : m_cvx_cls.get_new_vars()) {
        m_dim_vars.push_back(v);
        m_dim_frsh_cnsts.push_back(
            m.mk_fresh_const("mrg_syn_cvx", v->get_sort()));
    }
}

bool lemma_global_generalizer::subsumer::subsume(const lemma_cluster &lc,
                                                 expr_ref_vector &new_post,
                                                 app_ref_vector &bindings) {
    if (!is_handled(lc)) return false;

    setup(lc);

    // compute convex closure
    expr_ref_vector cls(m);
    bool is_syntactic = m_cvx_cls.closure(cls);

    CTRACE("subsume_verb", is_syntactic,
           tout << "Convex closure introduced new variables. Closure is "
                << mk_and(cls) << "\n";);

    // If convex closure introduced new variables, add them to
    // m_dim_frsh_cnsts
    if (is_syntactic) {
        m_st.m_num_syn_cls++;
        add_cvx_cls_vars();
    }

    cls.push_back(lc.get_pattern());

    // Ground syntactic CC by skolemizing variables
    expr_ref ground_cls(m);
    ground_free_vars(mk_and(cls), ground_cls);
    TRACE("subsume_verb", tout << "Rewrote all vars into u_consts\n"
                               << mk_and(cls) << "\n"
                               << " into "
                               << "\n"
                               << ground_cls << "\n";);

    // Skolemized syntactic cc
    expr_ref syn_cls(ground_cls, m);

    // Attempt to eliminate variables introduced by syntactic cc
    if (!eliminate_vars(ground_cls, lc,
                        is_syntactic && contains_ints(m_dim_frsh_cnsts),
                        bindings)) {
        // something failed, bail out
        return false;
    }

    // at this point ground_cls might be stronger than original syntactic
    // closure weaken it
    flatten_and(ground_cls, new_post);
    return over_approximate(new_post, syn_cls);
}

/// Eliminate m_dim_frsh_cnsts from \p cvx_cls
///
/// Uses \p lc to get a model for mbp.
/// \p mlir indicates whether \p cvx_cls contains both ints and reals.
/// all vars that could not be eliminated are skolemized and added to \p
/// bindings
bool lemma_global_generalizer::subsumer::eliminate_vars(
    expr_ref &cvx_pattern, const lemma_cluster &lc, bool mlir,
    app_ref_vector &out_bindings) {
    if (mlir) {
        // coerce to real
        to_real(cvx_pattern);
        // coerce skolem constants to real
        to_real_cnsts();

        TRACE("subsume_verb",
              tout << "To real produced " << cvx_pattern << "\n";);
    }

    // Get a model to guide MBP. Attempt to get a model that does not satisfy
    // any of the cubes in the cluster

    model_ref mdl;
    expr_ref neg_cubes(m);
    lc.get_conj_lemmas(neg_cubes);
    if (!maxsat_with_model(cvx_pattern, neg_cubes, mdl)) {
        TRACE("subsume",
              tout << "Convex closure is unsat " << cvx_pattern << "\n";);
        return false;
    }

    SASSERT(mdl.get() != nullptr);
    TRACE("subsume", tout << "calling mbp with " << cvx_pattern << " and\n"
                          << *mdl << "\n";);

    // MBP to eliminate existentially quantified variables
    qe_project(m, m_dim_frsh_cnsts, cvx_pattern, *mdl.get(), true, true,
               !m_ground_pob);

    TRACE("subsume", tout << "Pattern after mbp of computing cvx cls: "
                          << cvx_pattern << "\n";);

    if (!m_ground_pob && contains_reals(m_dim_frsh_cnsts)) {
        TRACE("subsume", {
            tout << "Could not eliminate non-integer variables\n";
            for (auto *e : m_dim_vars) tout << mk_pp(e, m);
            tout << "\n";
        });
        return false;
    }

    SASSERT(!m_ground_pob || m_dim_frsh_cnsts.empty());

    if (mlir) { to_int(cvx_pattern); }

    // If not all variables have been eliminated, skolemize and add bindings
    // This creates quantified proof obligation that will be handled by QUIC3
    if (!m_dim_frsh_cnsts.empty()) {
        SASSERT(!m_ground_pob);
        skolemize(cvx_pattern, mdl, out_bindings);
    }

    return true;
}

/// Find a weakening of \p a such that \p b ==> a
///
/// Returns true on success and sets \p a to the result
bool lemma_global_generalizer::subsumer::over_approximate(expr_ref_vector &a,
                                                          const expr_ref b) {

    // B && !(A1 && A2 && A3) is encoded as
    // B && ((tag1 && !A1) || (tag2 && !A2) || (tag3 && !A3))
    // iterate and check tags
    expr_ref_vector tags(m), tagged_a(m);
    std::string tag_prefix = "o";
    for (auto *lit : a) {
        // AG: use local constants instead of global mk_fresh_const
        tags.push_back(m.mk_fresh_const(symbol(tag_prefix), m.mk_bool_sort()));
        tagged_a.push_back(m.mk_implies(tags.back(), lit));
    }

    TRACE("subsume_verb", tout << "weakening " << mk_and(a)
                               << " to over approximate " << b << "\n";);
    solver::scoped_push _sp(*m_solver);
    m_solver->assert_expr(b);
    m_solver->assert_expr(push_not(mk_and(tagged_a)));

    while (true) {
        lbool res = m_solver->check_sat(tags.size(), tags.data());
        if (res == l_false) {
            break;
        } else if (res == l_undef) {
            break;
        }

        // flip tags for all satisfied literals of !A
        model_ref mdl;
        m_solver->get_model(mdl);

        for (unsigned i = 0, sz = a.size(); i < sz; ++i) {
            if (!m.is_not(tags.get(i)) && mdl->is_false(a.get(i))) {
                tags[i] = m.mk_not(tags.get(i));
            }
        }
    }

    expr_ref_buffer res(m);
    // remove all expressions whose tags are false
    for (unsigned i = 0, sz = tags.size(); i < sz; i++) {
        if (!m.is_not(tags.get(i))) { res.push_back(a.get(i)); }
    }
    a.reset();
    a.append(res.size(), res.data());

    if (a.empty()) {
        // could not find an over approximation
        TRACE("subsume",
              tout << "mbp did not over-approximate convex closure\n";);
        m_st.m_num_no_ovr_approx++;
        return false;
    }

    TRACE("subsume",
          tout << "over approximate produced " << mk_and(a) << "\n";);
    return true;
}

/// Attempt to set a conjecture on pob \p n.
///
/// Done by dropping literal \p lit from
/// post of \p n. \p lvl is level for conjecture pob. \p gas is the gas for
/// the conjecture pob returns true if conjecture is set
bool lemma_global_generalizer::do_conjecture(pob_ref &n, const expr_ref &lit,
                                             unsigned lvl, unsigned gas) {
    expr_ref_vector fml_vec(m);
    expr_ref n_pob(n->post(), m);
    normalize_order(n_pob, n_pob);
    fml_vec.push_back(n_pob);
    flatten_and(fml_vec);

    expr_ref_vector conj(m);
    bool is_filtered = filter_out_lit(fml_vec, lit, conj);
    SASSERT(0 < gas && gas < UINT_MAX);
    if (conj.empty()) {
        // If the pob cannot be abstracted, stop using generalization on
        // it
        TRACE("global", tout << "stop local generalization on pob " << n_pob
                             << " id is " << n_pob->get_id() << "\n";);
        n->disable_local_gen();
        return false;
    } else if (!is_filtered) {
        // The literal to be abstracted is not in the pob
        TRACE("global", tout << "cannot conjecture on " << n_pob << " with lit "
                             << lit << "\n";);
        n->disable_local_gen();
        m_st.m_num_cant_abs++;
        return false;
    }

    // There is enough gas to conjecture on pob
    n->set_conjecture_pattern(conj);
    n->set_expand_bnd();
    n->set_may_pob_lvl(lvl);
    n->set_gas(gas);
    n->disable_local_gen();
    TRACE("global", tout << "set conjecture " << conj << " at level "
                         << n->get_may_pob_lvl() << "\n";);
    return true;
}

// Decide global guidance based on lemma
void lemma_global_generalizer::generalize(lemma_ref &lemma) {
    // -- pob that the lemma blocks
    pob_ref &pob = lemma->get_pob();
    // -- cluster that the lemma belongs to
    lemma_cluster *cluster = pob->pt().clstr_match(lemma);

    /// Lemma does not belong to any cluster. return
    if (!cluster) return;

    // if the cluster does not have enough gas, stop local generalization
    // and return
    if (cluster->get_gas() == 0) {
        m_st.m_num_cls_ofg++;
        pob->disable_local_gen();
        TRACE("global", tout << "stop local generalization on pob "
                             << mk_pp(pob->post(), m) << " id is "
                             << pob->post()->get_id() << "\n";);
        return;
    }

    // -- local cluster that includes the new lemma
    lemma_cluster lc(*cluster);
    lc.add_lemma(lemma, true);

    const expr_ref &pat = lc.get_pattern();

    TRACE("global", {
        tout << "Global generalization of: " << mk_and(lemma->get_cube())
             << "\n"
             << "Cluster pattern: " << pat << "\n"
             << "Other lemmas:\n";
        for (const auto &lemma : lc.get_lemmas()) {
            tout << mk_and(lemma.get_lemma()->get_cube()) << "\n";
        }
    });

    // Concretize
    if (has_nonlinear_var_mul(pat, m)) {
        m_st.m_num_non_lin++;

        TRACE("global",
              tout << "Found non linear pattern. Marked to concretize \n";);
        // not constructing the concrete pob here since we need a model for
        // n->post()
        pob->set_concretize_pattern(pat);
        pob->set_concretize(true);
        pob->set_gas(cluster->get_pob_gas());
        cluster->dec_gas();
        return;
    }

    // Conjecture
    expr_ref lit(m);
    if (find_unique_mono_var_lit(pat, lit)) {
        // Create a conjecture by dropping literal from pob.
        TRACE("global", tout << "Conjecture with pattern " << mk_pp(pat, m)
                             << " with gas " << cluster->get_gas() << "\n";);
        unsigned gas = cluster->get_pob_gas();
        unsigned lvl = cluster->get_min_lvl();
        if (do_conjecture(pob, lit, lvl, gas)) {
            // decrease the number of times this cluster is going to be used
            // for conjecturing
            cluster->dec_gas();
            return;
        }
    }

    // if subsumption removed all the other lemmas, there is nothing to
    // generalize
    if (lc.get_size() < 2) return;

    if (!m_do_subsume) return;
    // -- new pob that is blocked by generalized lemma
    expr_ref_vector new_pob(m);
    // -- bindings for free variables of new_pob
    // -- subsumer might introduce extra free variables
    app_ref_vector bindings(lemma->get_bindings());

    if (m_subsumer.subsume(lc, new_pob, bindings)) {
        pob->set_subsume_pob(new_pob);
        pob->set_subsume_bindings(bindings);
        pob->set_may_pob_lvl(cluster->get_min_lvl());
        pob->set_gas(cluster->get_pob_gas() + 1);
        pob->set_expand_bnd();
        TRACE("global", tout << "subsume pob " << mk_and(new_pob)
                             << " at level " << cluster->get_min_lvl()
                             << " set on pob " << mk_pp(pob->post(), m)
                             << "\n";);
        // -- stop local generalization
        // -- maybe not the best choice in general. Helped with one instance
        // on
        // -- our benchmarks
        pob->disable_local_gen();
        cluster->dec_gas();
    }
}

/// Replace bound vars in \p fml with uninterpreted constants
void lemma_global_generalizer::subsumer::ground_free_vars(expr *pat,
                                                          expr_ref &out) {
    SASSERT(!is_ground(pat));
    expr_safe_replace sub(m);
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        sub.insert(m_dim_vars.get(i), m_dim_frsh_cnsts.get(i));
    }
    sub(pat, out);
    SASSERT(is_ground(out));
    return;
}

// convert all LIA constants in m_dim_frsh_cnsts to LRA constants using
// to_real
void lemma_global_generalizer::subsumer::to_real_cnsts() {
    for (unsigned i = 0, sz = m_dim_frsh_cnsts.size(); i < sz; i++) {
        auto *c = m_dim_frsh_cnsts.get(i);
        if (m_arith.is_real(c)) continue;
        m_dim_frsh_cnsts.set(i, m_arith.mk_to_real(c));
    }
}

pob *lemma_global_generalizer::mk_concretize_pob(pob &n, model_ref &model) {
    expr_ref_vector new_post(m);
    spacer::pob_concretizer proc(m, model, n.get_concretize_pattern());
    if (proc.apply(n.post(), new_post)) {
        pob *new_pob = n.pt().mk_pob(n.parent(), n.level(), n.depth(),
                                     mk_and(new_post), n.get_binding());

        TRACE("concretize", tout << "pob:\n" << mk_pp(n.post(), m)
                                 << " is concretized into:\n"
                                 << mk_pp(new_pob->post(), m) << "\n";);
        return new_pob;
    }
    return nullptr;
}

pob *lemma_global_generalizer::mk_subsume_pob(pob &n) {
    if (n.get_subsume_pob().empty() || n.get_gas() <= 0) return nullptr;

    expr_ref post = mk_and(n.get_subsume_pob());
    pob *f = n.pt().find_pob(n.parent(), post);
    if (f && f->is_in_queue()) return nullptr;

    auto level = n.get_may_pob_lvl();
    f = n.pt().mk_pob(n.parent(), level, n.depth(), post,
                      n.get_subsume_bindings());
    f->set_subsume();
    return f;
}

pob *lemma_global_generalizer::mk_conjecture_pob(pob &n) {
    if (n.get_conjecture_pattern().empty() || n.get_gas() <= 0) return nullptr;

    expr_ref post = mk_and(n.get_conjecture_pattern());
    pob *f = n.pt().find_pob(n.parent(), post);
    if (f && f->is_in_queue()) return nullptr;

    auto level = n.get_may_pob_lvl();
    f = n.pt().mk_pob(n.parent(), level, n.depth(), post, {m});
    f->set_conjecture();
    return f;
}

void lemma_global_generalizer::subsumer::collect_statistics(
    statistics &st) const {
    st.update("SPACER num no over approximate", m_st.m_num_no_ovr_approx);
    st.update("SPACER num sync cvx cls", m_st.m_num_syn_cls);
    st.update("SPACER num mbp failed", m_st.m_num_mbp_failed);
    m_cvx_cls.collect_statistics(st);
}

void lemma_global_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global", m_st.watch.get_seconds());
    st.update("SPACER cluster out of gas", m_st.m_num_cls_ofg);
    st.update("SPACER num non lin", m_st.m_num_non_lin);
    st.update("SPACER num cant abstract", m_st.m_num_cant_abs);
}

} // namespace spacer
