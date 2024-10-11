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

class to_real_stripper {
    ast_manager &m;
    arith_util m_arith;

  public:
    to_real_stripper(ast_manager &_m) : m(_m), m_arith(m) {}
    bool operator()(expr_ref &e, unsigned depth = 8) {
        rational num;
        if (m_arith.is_int(e)) return true;
        if (depth == 0) return false;
        if (!is_app(e)) return false;

        if (m_arith.is_to_real(e)) {
            // strip to_real()
            e = to_app(e)->get_arg(0);
            return true;
        } else if (m_arith.is_numeral(e, num)) {
            // convert number to an integer
            if (denominator(num).is_one()) {
                e = m_arith.mk_int(num);
                return true;
            } else {
                return false;
            }
        }

        app *e_app = to_app(e);
        expr_ref_buffer args(m);
        expr_ref kid(m);
        bool dirty = false;
        for (unsigned i = 0, sz = e_app->get_num_args(); i < sz; ++i) {
            auto *arg = e_app->get_arg(i);
            kid = arg;
            if (this->operator()(kid, depth - 1)) {
                dirty |= (kid.get() != arg);
                args.push_back(std::move(kid));
            } else {
                return false;
            }
        }

        if (dirty)
            e = m.mk_app(e_app->get_family_id(), e_app->get_decl_kind(),
                         args.size(), args.data());

        return true;
    }

    bool operator()(expr_ref_vector &vec, unsigned depth = 8) {
        bool res = true;
        expr_ref e(m);
        for (unsigned i = 0, sz = vec.size(); res && i < sz; ++i) {
            e = vec.get(i);
            res = this->operator()(e, depth);
            if (res) { vec[i] = e; }
        }
        return res;
    }
};

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

} // namespace

namespace spacer {
lemma_global_generalizer::subsumer::subsumer(ast_manager &a_m, bool ground_pob)
    : m(a_m), m_arith(m), m_bv(m), m_tags(m), m_used_tags(0), m_col_names(m),
      m_ground_pob(ground_pob) {
    scoped_ptr<solver_factory> factory(
        mk_smt_strategic_solver_factory(symbol::null));
    m_solver = (*factory)(m, params_ref::get_empty(), false, true, false,
                          symbol::null);
}

app *lemma_global_generalizer::subsumer::mk_fresh_tag() {
    if (m_used_tags == m_tags.size()) {
        auto *bool_sort = m.mk_bool_sort();
        // -- create 4 new tags
        m_tags.push_back(m.mk_fresh_const(symbol("t"), bool_sort));
        m_tags.push_back(m.mk_fresh_const(symbol("t"), bool_sort));
        m_tags.push_back(m.mk_fresh_const(symbol("t"), bool_sort));
        m_tags.push_back(m.mk_fresh_const(symbol("t"), bool_sort));
    }

    return m_tags.get(m_used_tags++);
}

lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()),
      m_subsumer(m, ctx.use_ground_pob()), m_do_subsume(ctx.do_subsume()) {}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    generalize(lemma);
}

void lemma_global_generalizer::subsumer::mk_col_names(const lemma_cluster &lc) {

    expr_offset r;
    std::pair<unsigned, unsigned> v;

    auto &lemmas = lc.get_lemmas();
    SASSERT(!lemmas.empty());
    const substitution &sub = lemmas.get(0).get_sub();

    m_col_names.reserve(sub.get_num_bindings());
    for (unsigned j = 0, sz = sub.get_num_bindings(); j < sz; j++) {
        sub.get_binding(j, v, r);
        auto *sort = r.get_expr()->get_sort();
        auto i = v.first;
        SASSERT(0 <= i && i < sz);
        if (!m_col_names.get(i) || m_col_names.get(i)->get_sort() != sort) {
            // create a fresh skolem constant for the jth variable
            // reuse variables if they are already here and have matching sort
            m_col_names[i] = m.mk_fresh_const("mrg_cvx!!", sort);
        }
    }

    // -- lcm corresponds to a column, reset them since names have potentially
    // changed
    // -- this is a just-in-case
    m_col_lcm.reset();
}

// Populate m_cvx_cls by 1) collecting all substitutions in the cluster \p lc
// 2) normalizing them to integer numerals
void lemma_global_generalizer::subsumer::setup_cvx_closure(
    convex_closure &cc, const lemma_cluster &lc) {
    expr_offset r;
    std::pair<unsigned, unsigned> v;

    mk_col_names(lc);
    const lemma_info_vector &lemmas = lc.get_lemmas();

    m_col_lcm.reset();

    unsigned n_vars = 0;
    rational num;
    bool is_first = true;
    for (const auto &lemma : lemmas) {
        const substitution &sub = lemma.get_sub();
        if (is_first) {
            n_vars = sub.get_num_bindings();
            m_col_lcm.reserve(n_vars, rational::one());
            is_first = false;
        }

        unsigned i;
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            i = v.first;
            SASSERT(0 <= i && i < n_vars);
            if (is_numeral(r.get_expr(), num)) {
                m_col_lcm[i] = lcm(m_col_lcm.get(i), abs(denominator(num)));
            }
        }
    }

    cc.reset(n_vars);

    unsigned bv_width = 0;
    if (contains_bv(m, lc.get_lemmas()[0].get_sub(), bv_width)) {
        cc.set_bv(bv_width);
    }

    for (unsigned j = 0; j < n_vars; ++j)
        cc.set_col_var(j, mk_rat_mul(m_col_lcm.get(j), m_col_names.get(j)));

    vector<rational> row;
    unsigned i = 0;
    for (const auto &lemma : lemmas) {
        row.reset();
        row.reserve(n_vars);

        const substitution &sub = lemma.get_sub();
        for (unsigned j = 0, sz = sub.get_num_bindings(); j < sz; j++) {
            sub.get_binding(j, v, r);
            i = v.first;
            VERIFY(is_numeral(r.get_expr(), num));
            row[i] = m_col_lcm.get(i) * num;
        }

        // -- add normalized row to convex closure
        cc.add_row(row);
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
void lemma_global_generalizer::subsumer::skolemize_for_quic3(
    expr_ref &f, const model_ref &mdl, app_ref_vector &out) {
    unsigned idx = out.size();
    app_ref sk(m);
    expr_ref eval(m);
    expr_safe_replace sub(m);

    expr_ref_vector f_cnsts(m);
    spacer::collect_uninterp_consts(f, f_cnsts);

    expr_fast_mark2 marks;
    for (auto *c : f_cnsts) { marks.mark(c); }

    for (unsigned i = 0, sz = m_col_names.size(); i < sz; i++) {
        app *c = m_col_names.get(i);
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
    m_col_names.reset();
}

bool lemma_global_generalizer::subsumer::find_model(
    const expr_ref_vector &cc, const expr_ref_vector &alphas, expr *bg,
    model_ref &out_model) {

    // push because we re-use the solver
    solver::scoped_push _sp(*m_solver);
    if (bg) m_solver->assert_expr(bg);

    // -- assert syntactic convex closure constraints
    m_solver->assert_expr(cc);

    // if there are alphas, we have syntactic convex closure
    if (!alphas.empty()) {
        SASSERT(alphas.size() >= 2);

        // try to get an interior point in convex closure that also satisfies bg
        {
            // push because this might be unsat
            solver::scoped_push _sp2(*m_solver);
            expr_ref zero(m_arith.mk_real(0), m);

            for (auto *alpha : alphas) {
                m_solver->assert_expr(m_arith.mk_gt(alpha, zero));
            }

            auto res = m_solver->check_sat();
            if (res == l_true) {
                m_solver->get_model(out_model);
                return true;
            }
        }
    }

    // failed, try to get any point in convex closure
    auto res = m_solver->check_sat();

    if (res == l_true) {
        m_solver->get_model(out_model);
        return true;
    }

    UNREACHABLE();

    // something went wrong and there is no model, even though one was expected
    return false;
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

void lemma_global_generalizer::subsumer::reset() {
    m_used_tags = 0;
    m_col_lcm.reset();
}

bool lemma_global_generalizer::subsumer::subsume(const lemma_cluster &lc,
                                                 expr_ref_vector &new_post,
                                                 app_ref_vector &bindings) {
    if (!is_handled(lc)) return false;

    convex_closure cvx_closure(m);

    reset();
    setup_cvx_closure(cvx_closure, lc);

    // compute convex closure
    if (!cvx_closure.compute()) { return false; }
    bool is_syntactic = cvx_closure.has_implicit();
    if (is_syntactic) { m_st.m_num_syn_cls++; }

    CTRACE("subsume_verb", is_syntactic,
           tout << "Convex closure introduced new variables. Implicit part of "
                   "closure is: "
                << mk_and(cvx_closure.get_implicit()) << "\n";);

    expr_ref grounded(m);
    ground_free_vars(lc.get_pattern(), grounded);

    expr_ref_vector vec(m);
    auto &implicit_cc = cvx_closure.get_implicit();
    auto &explicit_cc = cvx_closure.get_explicit();
    vec.append(implicit_cc.size(), implicit_cc.data());
    vec.append(explicit_cc.size(), explicit_cc.data());

    // get a model for mbp
    model_ref mdl;
    auto &alphas = cvx_closure.get_alphas();
    find_model(vec, alphas, grounded, mdl);

    app_ref_vector vars(m);
    expr_ref conj(m);
    vec.reset();

    // eliminate real-valued alphas from syntactic convex closure
    if (!implicit_cc.empty()) {
        vec.append(implicit_cc.size(), implicit_cc.data());
        conj = mk_and(vec);
        vars.append(alphas.size(),
                    reinterpret_cast<app *const *>(alphas.data()));
        qe_project(m, vars, conj, *mdl.get(), true, true, !m_ground_pob);

        // mbp failed, not expected, bail out
        if (!vars.empty()) return false;
    }

    // vec = [implicit_cc]
    // store full cc, this is what we want to over-approximate explicitly
    vec.append(explicit_cc.size(), explicit_cc.data());
    flatten_and(grounded, vec);
    // vec = [implicit_cc(alpha_j, v_i), explicit_cc(v_i), phi(v_i)]
    expr_ref full_cc(mk_and(vec), m);

    vec.reset();
    if (conj) {
        // if explicit version of implicit cc was successfully computed
        // conj is it, but need to ensure it has no to_real()
        to_real_stripper stripper(m);
        flatten_and(conj, vec);
        stripper(vec);
    }
    vec.append(explicit_cc.size(), explicit_cc.data());

    flatten_and(grounded, vec);
    // here vec is [cc(v_i), phi(v_i)], and we need to eliminate v_i from it

    vars.reset();
    vars.append(m_col_names.size(),
                reinterpret_cast<app *const *>(m_col_names.data()));
    conj = mk_and(vec);
    qe_project(m, vars, conj, *mdl.get(), true, true, !m_ground_pob);

    // failed
    if (!vars.empty()) return false;

    // at the end, new_post must over-approximate the implicit convex closure
    flatten_and(conj, new_post);
    return over_approximate(new_post, full_cc);
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
        tags.push_back(mk_fresh_tag());
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
bool lemma_global_generalizer::do_conjecture(pob_ref &n, lemma_ref &lemma,
                                             const expr_ref &lit, unsigned lvl,
                                             unsigned gas) {
    arith_util arith(m);
    expr_ref_vector fml_vec(m);
    expr_ref n_post(n->post(), m);
    normalize(n_post, n_post, false, false);
    // normalize_order(n_post, n_post);
    fml_vec.push_back(n_post);
    flatten_and(fml_vec);

    expr_ref_vector conj(m);
    bool is_filtered = filter_out_lit(fml_vec, lit, conj);
    expr *e1 = nullptr, *e2 = nullptr;
    if (!is_filtered &&
        (arith.is_le(lit, e1, e2) || arith.is_ge(lit, e1, e2))) {

        // if lit is '<=' or '>=', try matching '=='
        is_filtered =
            filter_out_lit(fml_vec, expr_ref(m.mk_eq(e1, e2), m), conj);
    }

    if (!is_filtered) {
        // -- try using the corresponding lemma instead
        conj.reset();
        n_post = mk_and(lemma->get_cube());
        normalize_order(n_post, n_post);
        fml_vec.reset();
        fml_vec.push_back(n_post);
        flatten_and(fml_vec);
        is_filtered = filter_out_lit(fml_vec, lit, conj);
    }

    SASSERT(0 < gas && gas < UINT_MAX);
    if (conj.empty()) {
        // If the pob cannot be abstracted, stop using generalization on
        // it
        TRACE("global", tout << "stop local generalization on pob " << n_post
                             << " id is " << n_post->get_id() << "\n";);
        n->disable_local_gen();
        return false;
    } else if (!is_filtered) {
        // The literal to be abstracted is not in the pob
        TRACE("global", tout << "Conjecture failed:\n"
                             << lit << "\n"
                             << n_post << "\n"
                             << "conj:" << conj << "\n";);
        n->disable_local_gen();
        m_st.m_num_cant_abs++;
        return false;
    }

    pob *root = n->parent();
    while (root->parent()) root = root->parent();
    scoped_ptr<pob> new_pob = alloc(pob, root, n->pt(), lvl, n->depth(), false);
    if (!new_pob) return false;

    new_pob->set_desired_level(n->level());

    new_pob->set_post(mk_and(conj));
    new_pob->set_conjecture();

    // -- register with current pob
    n->set_data(new_pob.detach());

    // -- update properties of the current pob itself
    n->set_expand_bnd();
    n->set_gas(gas);
    n->disable_local_gen();
    TRACE("global", tout << "set conjecture " << mk_pp(n->get_data()->post(), m)
                         << " at level " << n->get_data()->level() << "\n";);
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
    // XXX most of the time lemma clustering happens before generalization
    // XXX so `add_lemma` is likely to return false, but this does not mean
    // XXX that the lemma is not new
    bool is_new = lc.add_lemma(lemma, true);
    (void)is_new;

    const expr_ref &pat = lc.get_pattern();

    TRACE("global", {
        tout << "Global generalization of:\n"
             << mk_and(lemma->get_cube()) << "\n"
             << "at lvl: " << lemma->level() << "\n"
             << (is_new ? "new" : "old") << "\n"
             << "Using cluster:\n"
             << pat << "\n"
             << "Existing lemmas in the cluster:\n";
        for (const auto &li : cluster->get_lemmas()) {
            tout << mk_and(li.get_lemma()->get_cube())
                 << " lvl:" << li.get_lemma()->level() << "\n";
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
        TRACE("global", tout << "Conjecture with pattern\n"
                             << mk_pp(pat, m) << "\n"
                             << "with gas " << cluster->get_gas() << "\n";);
        unsigned gas = cluster->get_pob_gas();
        unsigned lvl = lc.get_min_lvl();
        if (pob) lvl = std::min(lvl, pob->level());
        if (do_conjecture(pob, lemma, lit, lvl, gas)) {
            // decrease the number of times this cluster is going to be used
            // for conjecturing
            cluster->dec_gas();
            return;
        } else {
            // -- if conjecture failed, there is nothing else to do.
            // -- the pob matched pre-condition for conjecture, so it should not
            // be subsumed
            return;
        }
    }

    // if subsumption removed all the other lemmas, there is nothing to
    // generalize
    if (lc.get_size() < 2) return;

    if (!m_do_subsume) return;
    // -- new pob that is blocked by generalized lemma
    expr_ref_vector new_post(m);
    // -- bindings for free variables of new_pob
    // -- subsumer might introduce extra free variables
    app_ref_vector bindings(lemma->get_bindings());

    if (m_subsumer.subsume(lc, new_post, bindings)) {
        class pob *root = pob->parent();
        while (root->parent()) root = root->parent();

        unsigned new_lvl = lc.get_min_lvl();
        if (pob) new_lvl = std::min(new_lvl, pob->level());
        scoped_ptr<class pob> new_pob =
            alloc(class pob, root, pob->pt(), new_lvl, pob->depth(), false);
        if (!new_pob) return;

        new_pob->set_desired_level(pob->level());
        new_pob->set_post(mk_and(new_post), bindings);
        new_pob->set_subsume();
        pob->set_data(new_pob.detach());

        // -- update properties of the pob itself
        pob->set_gas(cluster->get_pob_gas() + 1);
        pob->set_expand_bnd();
        // Stop local generalization. Perhaps not the best choice in general.
        // Helped with one instance on our benchmarks
        pob->disable_local_gen();
        cluster->dec_gas();

        TRACE("global", tout << "Create subsume pob at level " << new_lvl
                             << "\n"
                             << mk_and(new_post) << "\n";);
    }
}

/// Replace bound vars in \p fml with uninterpreted constants
void lemma_global_generalizer::subsumer::ground_free_vars(expr *pat,
                                                          expr_ref &out) {
    SASSERT(!is_ground(pat));
    var_subst vs(m, false);
    // m_col_names might be bigger since it contains previously used constants
    // relying on the fact that m_col_lcm was just set. Better to compute free
    // vars of pat
    SASSERT(m_col_lcm.size() <= m_col_names.size());
    out = vs(pat, m_col_lcm.size(),
             reinterpret_cast<expr *const *>(m_col_names.data()));
    SASSERT(is_ground(out));
}

pob *lemma_global_generalizer::mk_concretize_pob(pob &n, model_ref &model) {
    expr_ref_vector new_post(m);
    spacer::pob_concretizer proc(m, model, n.get_concretize_pattern());
    if (proc.apply(n.post(), new_post)) {
        pob *new_pob = n.pt().mk_pob(n.parent(), n.level(), n.depth(),
                                     mk_and(new_post), n.get_binding());

        TRACE("concretize", tout << "pob:\n"
                                 << mk_pp(n.post(), m)
                                 << " is concretized into:\n"
                                 << mk_pp(new_pob->post(), m) << "\n";);
        return new_pob;
    }
    return nullptr;
}

pob *lemma_global_generalizer::mk_subsume_pob(pob &n) {
    if (!(n.get_gas() >= 0 && n.has_data() && n.get_data()->is_subsume()))
        return nullptr;

    pob *data = n.get_data();

    pob *f = n.pt().find_pob(data->parent(), data->post());
    if (f && (f->is_in_queue() || f->is_closed())) {
        n.reset_data();
        return nullptr;
    }

    TRACE("global", tout << "mk_subsume_pob at level " << data->level()
                         << " with post state:\n"
                         << mk_pp(data->post(), m) << "\n";);
    f = n.pt().mk_pob(data->parent(), data->level(), data->depth(),
                      data->post(), n.get_binding());
    f->set_subsume();
    f->inherit(*data);

    n.reset_data();
    return f;
}

pob *lemma_global_generalizer::mk_conjecture_pob(pob &n) {
    if (!(n.has_data() && n.get_data()->is_conjecture() && n.get_gas() > 0))
        return nullptr;

    pob *data = n.get_data();
    pob *f = n.pt().find_pob(data->parent(), data->post());
    if (f && (f->is_in_queue() || f->is_closed())) {
        n.reset_data();
        return nullptr;
    }

    f = n.pt().mk_pob(data->parent(), data->level(), data->depth(),
                      data->post(), {m});

    // inherit all metadata from new_pob
    f->inherit(*data);

    n.reset_data();
    return f;
}

void lemma_global_generalizer::subsumer::collect_statistics(
    statistics &st) const {
    st.update("SPACER num no over approximate", m_st.m_num_no_ovr_approx);
    st.update("SPACER num sync cvx cls", m_st.m_num_syn_cls);
    st.update("SPACER num mbp failed", m_st.m_num_mbp_failed);
    // m_cvx_closure.collect_statistics(st);
}

void lemma_global_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global", m_st.watch.get_seconds());
    st.update("SPACER cluster out of gas", m_st.m_num_cls_ofg);
    st.update("SPACER num non lin", m_st.m_num_non_lin);
    st.update("SPACER num cant abstract", m_st.m_num_cant_abs);
}

} // namespace spacer
