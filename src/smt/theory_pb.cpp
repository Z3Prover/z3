/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_pb.cpp

Abstract:

    Pseudo-Boolean theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:


--*/

#include <typeinfo>
#include "theory_pb.h"
#include "smt_context.h"
#include "ast_pp.h"
#include "sorting_network.h"
#include "uint_set.h"
#include "smt_model_generator.h"
#include "pb_rewriter_def.h"
#include "sparse_matrix_def.h"
#include "simplex_def.h"


namespace smt {

    class pb_lit_rewriter_util {
    public:
        typedef std::pair<literal, rational> arg_t;
        typedef vector<arg_t> args_t;
        typedef rational numeral;
        
        literal negate(literal l) {
            return ~l;
        }

        void display(std::ostream& out, literal l) {
            out << l;
        }
        
        bool is_negated(literal l) const {
            return l.sign();
        }
       
        bool is_true(literal l) const {
            return l == true_literal;
        }
        
        bool is_false(literal l) const {
            return l == false_literal;
        }
        
        struct compare {
            bool operator()(arg_t const& a, arg_t const& b) {
                return a.first < b.first;
            }
        };
    };

    const unsigned theory_pb::null_index = UINT_MAX;


    unsigned theory_pb::arg_t::get_hash() const {
        return get_composite_hash<arg_t, arg_t::kind_hash, arg_t::child_hash>(*this, size());
    }

    bool theory_pb::arg_t::operator==(arg_t const& other) const {
        if (size() != other.size()) return false;
        for (unsigned i = 0; i < size(); ++i) {
            if (lit(i) != other.lit(i)) return false;
            if (coeff(i) != other.coeff(i)) return false;
        }
        return true;
    }

    void theory_pb::arg_t::remove_negations() {
        for (unsigned i = 0; i < size(); ++i) {
            if (lit(i).sign()) {
                (*this)[i].first.neg();
                (*this)[i].second.neg();
                m_k += coeff(i);
            }
        }
    }

    void theory_pb::arg_t::negate() {
        numeral sum(0);
        for (unsigned i = 0; i < size(); ++i) {
            (*this)[i].first.neg();
            sum += coeff(i);
        }
        m_k = sum - m_k + numeral::one();
        VERIFY(l_undef == normalize(false));
    }

    lbool theory_pb::arg_t::normalize(bool is_eq) {
        pb_lit_rewriter_util pbu;
        pb_rewriter_util<pb_lit_rewriter_util> util(pbu);
        return util.normalize(*this, m_k, is_eq);        
    }

    void theory_pb::arg_t::prune(bool is_eq) {
        pb_lit_rewriter_util pbu;
        pb_rewriter_util<pb_lit_rewriter_util> util(pbu);
        util.prune(*this, m_k, is_eq);   
    }

    std::ostream& theory_pb::arg_t::display(context& ctx, std::ostream& out, bool values) const {
        for (unsigned i = 0; i < size(); ++i) {
            literal l(lit(i));
            if (!coeff(i).is_one()) {
                out << coeff(i) << "*";
            }
            out << l;
            if (values) {
                out << "@(" << ctx.get_assignment(l);
                if (ctx.get_assignment(l) != l_undef) {
                    out << ":" << ctx.get_assign_level(l);
                }
                out << ")";
            }
            if (i + 1 < size()) {
                out << " + ";
            }
        }
        out << " ~ " << k() << "\n";
        return out;
    }

    app_ref theory_pb::arg_t::to_expr(bool is_eq, context& ctx, ast_manager& m) {
        expr_ref tmp(m);
        app_ref result(m);
        svector<rational> coeffs;
        expr_ref_vector args(m);
        for (unsigned i = 0; i < size(); ++i) {
            ctx.literal2expr(lit(i), tmp);
            args.push_back(tmp);
            coeffs.push_back(coeff(i));
        }
        pb_util pb(m);
        if (is_eq) {
            result = pb.mk_eq(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), k());
        }
        else {
            result = pb.mk_ge(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), k());
        }
        return result;
    }

    void theory_pb::ineq::reset() {
        m_max_watch.reset();
        m_watch_sz = 0;
        m_watch_sum.reset();
        m_num_propagations = 0;
        m_compilation_threshold = UINT_MAX;
        m_compiled = l_false;
        m_args[0].reset();
        m_args[0].m_k.reset();
        m_args[1].reset();
        m_args[1].m_k.reset();
        m_nfixed = 0;
        m_max_sum.reset();
        m_min_sum.reset();
    }


    void theory_pb::ineq::unique() {
        pb_lit_rewriter_util pbu;
        pb_rewriter_util<pb_lit_rewriter_util> util(pbu);
        util.unique(m_args[0], m_args[0].m_k, m_is_eq);        
    }

    void theory_pb::ineq::post_prune() {
        if (!m_args[0].empty() && is_ge()) {
            m_args[0].negate();
            m_args[0].negate();            
            m_args[1].reset();
            m_args[1].m_k = m_args[0].m_k;
            m_args[1].append(m_args[0]);
            m_args[1].negate();
            
            SASSERT(m_args[0].size() == m_args[1].size());
            SASSERT(m_args[0].well_formed());
            SASSERT(m_args[1].well_formed());
        }        
    }

    void theory_pb::ineq::negate() {
        SASSERT(!m_is_eq);
        m_lit.neg();
    }

    void theory_pb::ineq::prune() {
        m_args[0].prune(m_is_eq);
    }

    lbool theory_pb::ineq::normalize() {
        return m_args[0].normalize(m_is_eq);
    }

    app_ref theory_pb::ineq::to_expr(context& ctx, ast_manager& m) {
        return args().to_expr(m_is_eq, ctx, m);
    }

    bool theory_pb::arg_t::well_formed() const {
        SASSERT(k().is_pos());
        uint_set vars;
        numeral sum = numeral::zero();
        for (unsigned i = 0; i < size(); ++i) {
            SASSERT(coeff(i) <= k());
            SASSERT(numeral::one() <= coeff(i));
            SASSERT(lit(i) != true_literal);
            SASSERT(lit(i) != false_literal);
            SASSERT(lit(i) != null_literal);
            SASSERT(!vars.contains(lit(i).var()));
            vars.insert(lit(i).var());
            sum += coeff(i);
        }
        SASSERT(sum >= k());
        return true;
    }
    
    theory_pb::theory_pb(ast_manager& m, theory_pb_params& p):
        theory(m.mk_family_id("pb")),
        m_params(p),
        m_util(m),
        m_max_compiled_coeff(rational(8))
    {        
        m_learn_complements  = p.m_pb_learn_complements;
        m_conflict_frequency = p.m_pb_conflict_frequency;
        m_enable_compilation = p.m_pb_enable_compilation;
        m_enable_simplex     = p.m_pb_enable_simplex;
    }

    theory_pb::~theory_pb() {
        reset_eh();
    }

    theory * theory_pb::mk_fresh(context * new_ctx) { 
        return alloc(theory_pb, new_ctx->get_manager(), m_params); 
    }

    class theory_pb::remove_var : public trail<context> {
        theory_pb& pb;
        unsigned   v;
    public:
        remove_var(theory_pb& pb, unsigned v): pb(pb), v(v) {}
        virtual void undo(context& ctx) {
            pb.m_vars.remove(v);
            pb.m_simplex.unset_lower(v);
            pb.m_simplex.unset_upper(v);
        }        
    };

    class theory_pb::undo_bound : public trail<context> {
        theory_pb&         pb;
        unsigned           m_v;
        bool               m_is_lower;
        scoped_eps_numeral m_last_bound;
        bool               m_last_bound_valid;
        literal            m_last_explain;
        
    public:
        undo_bound(theory_pb& pb, unsigned v, 
                   bool is_lower, 
                   scoped_eps_numeral& last_bound, 
                   bool last_bound_valid, 
                   literal last_explain):
            pb(pb), 
            m_v(v), 
            m_is_lower(is_lower), 
            m_last_bound(last_bound), 
            m_last_bound_valid(last_bound_valid),
            m_last_explain(last_explain) {}

        virtual void undo(context& ctx) {
            if (m_is_lower) {
                if (m_last_bound_valid) {
                    pb.m_simplex.set_lower(m_v, m_last_bound);
                }
                else {
                    pb.m_simplex.unset_lower(m_v);
                }
                pb.set_explain(pb.m_explain_lower, m_v, m_last_explain);
            }
            else {
                if (m_last_bound_valid) {
                    pb.m_simplex.set_upper(m_v, m_last_bound);
                }
                else {
                    pb.m_simplex.unset_upper(m_v);
                }
                pb.set_explain(pb.m_explain_upper, m_v, m_last_explain);
            }
            m_last_bound.reset();
        }
    };

    literal theory_pb::set_explain(literal_vector& explains, unsigned var, literal expl) {
        if (var >= explains.size()) {
            explains.resize(var+1, null_literal);
        }
        literal last_explain = explains[var];
        explains[var] = expl;
        return last_explain;
    }

    bool theory_pb::update_bound(bool_var v, literal explain, bool is_lower, mpq_inf const& bound) {
        if (is_lower) {
            if (m_simplex.above_lower(v, bound)) {
                scoped_eps_numeral last_bound(m_mpq_inf_mgr);
                if (m_simplex.upper_valid(v)) {
                    m_simplex.get_upper(v, last_bound);
                    if (m_mpq_inf_mgr.gt(bound, last_bound)) {
                        literal lit = m_explain_upper.get(v, null_literal);
                        get_context().mk_clause(~lit, ~explain, justify(~lit, ~explain));
                        return false;
                    }
                }
                bool last_bound_valid = m_simplex.lower_valid(v);
                if (last_bound_valid) {
                    m_simplex.get_lower(v, last_bound);
                }
                m_simplex.set_lower(v, bound);
                literal last_explain = set_explain(m_explain_lower, v, explain);
                get_context().push_trail(undo_bound(*this, v, true, last_bound, last_bound_valid, last_explain));
            }
        }
        else {
            if (m_simplex.below_upper(v, bound)) {
                scoped_eps_numeral last_bound(m_mpq_inf_mgr);
                if (m_simplex.lower_valid(v)) {
                    m_simplex.get_lower(v, last_bound);
                    if (m_mpq_inf_mgr.gt(last_bound, bound)) {
                        literal lit = m_explain_lower.get(v, null_literal);
                        get_context().mk_clause(~lit, ~explain, justify(~lit, ~explain));
                        return false;
                    }
                }
                bool last_bound_valid = m_simplex.upper_valid(v);
                if (last_bound_valid) {
                    m_simplex.get_upper(v, last_bound);
                }
                m_simplex.set_upper(v, bound);
                literal last_explain = set_explain(m_explain_upper, v, explain);
                get_context().push_trail(undo_bound(*this, v, false, last_bound, last_bound_valid, last_explain));
            }
        }
        return true;
    };

    bool theory_pb::check_feasible() {
        context& ctx = get_context();
        lbool is_sat = m_simplex.make_feasible();
        if (l_false != is_sat) {
            return true;
        }

        row r = m_simplex.get_infeasible_row();
        // m_simplex.display_row(std::cout, r, true);
        mpz const& coeff = m_simplex.get_base_coeff(r);
        bool_var base_var = m_simplex.get_base_var(r);
        SASSERT(m_simplex.below_lower(base_var) || m_simplex.above_upper(base_var));
        bool cant_increase = m_simplex.below_lower(base_var)?m_mpz_mgr.is_pos(coeff):m_mpz_mgr.is_neg(coeff);

        literal_vector explains;
        row_iterator it = m_simplex.row_begin(r), end = m_simplex.row_end(r);        
        for (; it != end; ++it) {
            bool_var v = it->m_var;
            if (v == base_var) {
                if (m_simplex.below_lower(base_var)) {
                    explains.push_back(m_explain_lower.get(v, null_literal));
                }
                else {
                    explains.push_back(m_explain_upper.get(v, null_literal));
                }
            }
            else if (cant_increase == m_mpz_mgr.is_pos(it->m_coeff)) {
                explains.push_back(m_explain_lower.get(v, null_literal));
            }
            else {
                explains.push_back(m_explain_upper.get(v, null_literal));
            }
        }
        
        literal_vector lits;
        for (unsigned i = 0; i < explains.size(); ++i) {
            literal lit(explains[i]);
            if (lit != null_literal) {
                lits.push_back(~lit);
            }
        }

        m_stats.m_num_conflicts++;
        justification* js = 0;
        if (proofs_enabled()) {                                         
            js = alloc(theory_lemma_justification, get_id(), ctx, lits.size(), lits.c_ptr());
        }
        ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);

        return false;
    }

    bool theory_pb::internalize_atom(app * atom, bool gate_ctx) {
        context& ctx = get_context();
        if (ctx.b_internalized(atom)) {
            return false;
        }
        SASSERT(!ctx.b_internalized(atom));
        m_stats.m_num_predicates++;

        if (m_util.is_aux_bool(atom)) {
            bool_var abv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(abv, get_id());
            return true;
        }
        SASSERT(m_util.is_at_most_k(atom) || m_util.is_le(atom) || 
                m_util.is_ge(atom) || m_util.is_at_least_k(atom) || 
                m_util.is_eq(atom));



        unsigned num_args = atom->get_num_args();
        bool_var abv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(abv, get_id());

        ineq* c = alloc(ineq, m_mpz_mgr, literal(abv), m_util.is_eq(atom));
        c->m_args[0].m_k = m_util.get_k(atom);
        numeral& k = c->m_args[0].m_k;
        arg_t& args = c->m_args[0];

        // extract literals and coefficients.
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            literal l = compile_arg(arg);
            numeral c = m_util.get_coeff(atom, i);
            args.push_back(std::make_pair(l, c));
        }
        if (m_util.is_at_most_k(atom) || m_util.is_le(atom)) {
            // turn W <= k into -W >= -k
            for (unsigned i = 0; i < args.size(); ++i) {
                args[i].second = -args[i].second;
            }
            k = -k;
        }
        else {
            SASSERT(m_util.is_at_least_k(atom) || m_util.is_ge(atom) || m_util.is_eq(atom));
        }
        TRACE("pb", display(tout, *c););        
        //app_ref fml1(m), fml2(m);
        //fml1 = c->to_expr(ctx, m);
        c->unique();
        lbool is_true = c->normalize();
        c->prune();
        c->post_prune();
        //fml2 = c->to_expr(ctx, m);
        //expr_ref validate_pb = pb_rewriter(m).mk_validate_rewrite(fml1, fml2);
        //pb_rewriter(m).dump_pb_rewrite(validate_pb);

        literal lit(abv);


        TRACE("pb", display(tout, *c); tout << " := " << lit << "\n";);        
        switch(is_true) {
        case l_false: 
            lit = ~lit;
            // fall-through
        case l_true: 
            ctx.mk_th_axiom(get_id(), 1, &lit);
            dealloc(c);
            return true;
        case l_undef: 
            break;
        }
            
        if (c->k().is_one() && c->is_ge() && !m_enable_simplex) {
            literal_vector& lits = get_lits();
            lits.push_back(~lit);
            for (unsigned i = 0; i < c->size(); ++i) {
                lits.push_back(c->lit(i));
                SASSERT(c->coeff(i).is_one());
                ctx.mk_th_axiom(get_id(), lit, ~c->lit(i));
            }
            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
            return true;
        }
        
        // maximal coefficient:
        scoped_mpz& max_watch = c->m_max_watch;
        max_watch.reset();
        for (unsigned i = 0; i < args.size(); ++i) {
            mpz const& num = args[i].second.to_mpq().numerator();
            if (m_mpz_mgr.lt(max_watch, num)) {
                max_watch = num;
            }
        }

        // pre-compile threshold for cardinality
        bool enable_compile = m_enable_compilation && c->is_ge() && !c->k().is_one();
        for (unsigned i = 0; enable_compile && i < args.size(); ++i) {
            enable_compile = (args[i].second <= m_max_compiled_coeff);
        }
        if (enable_compile) {
            unsigned log = 1, n = 1;
            while (n <= args.size()) {
                ++log;
                n *= 2;
            }
            unsigned th = args.size()*log; // 10*
            c->m_compilation_threshold = th;
            IF_VERBOSE(2, verbose_stream() << "(smt.pb setting compilation threhshold to " << th << ")\n";);
            TRACE("pb", tout << "compilation threshold: " << th << "\n";);
        }
        else {
            c->m_compilation_threshold = UINT_MAX;
        }
        init_watch_var(*c);
        m_ineqs.insert(abv, c);
        m_ineqs_trail.push_back(abv);

        if (m_enable_simplex) {
            //
            // TBD: using abv as slack identity doesn't quite 
            // work if psuedo-Booleans are used 
            // in a nested way. So assume 
            //

            arg_t rep(c->args());
            rep.remove_negations();  // normalize representative
            numeral k = rep.k();
            theory_var slack;
            bool_var abv2;
            TRACE("pb", display(tout << abv <<"\n", rep););
            if (m_ineq_rep.find(rep, abv2)) {
                slack = abv2; 
                TRACE("pb", 
                      tout << "Old row: " << abv << " |-> " << slack << " ";
                      tout << m_ineq_row_info.find(abv2).m_bound << " vs. " << k << "\n";
                      display(tout, rep););
            }
            else {
                m_ineq_rep.insert(rep, abv);
                svector<unsigned> vars;
                scoped_mpz_vector coeffs(m_mpz_mgr);
                for (unsigned i = 0; i < rep.size(); ++i) {
                    unsigned v = rep.lit(i).var();
                    m_simplex.ensure_var(v);
                    vars.push_back(v);
                    if (!m_vars.contains(v)) {
                        mpq_inf zero(mpq(0),mpq(0)), one(mpq(1),mpq(0));
                        switch(ctx.get_assignment(rep.lit(i))) {
                        case l_true:
                            VERIFY(update_bound(v, literal(v), true, one));
                            m_simplex.set_lower(v, one);
                            break;
                        case l_false:
                            VERIFY(update_bound(v, ~literal(v), false, zero));
                            m_simplex.set_upper(v, zero);
                            break;
                        default:
                            m_simplex.set_lower(v, zero);
                            m_simplex.set_upper(v, one);
                            break;
                        }
                        m_vars.insert(v);
                        ctx.push_trail(remove_var(*this, v));                        
                    }
                    coeffs.push_back(rep.coeff(i).to_mpq().numerator());
                }
                slack = abv;
                m_simplex.ensure_var(slack);
                vars.push_back(slack);
                coeffs.push_back(mpz(-1));
                m_simplex.add_row(slack, vars.size(), vars.c_ptr(), coeffs.c_ptr());
                TRACE("pb", tout << "New row: " << abv << " " << k << "\n"; display(tout, rep););
            }
            m_ineq_row_info.insert(abv, row_info(slack, k, rep));
        }

        TRACE("pb", display(tout, *c););

        return true;
    }

    literal theory_pb::compile_arg(expr* arg) {
        context& ctx = get_context();
        ast_manager& m = get_manager();

        bool_var bv;
        bool has_bv = false;
        bool negate = m.is_not(arg, arg);
        SASSERT(!m.is_not(arg));
        if (!ctx.b_internalized(arg)) {
            ctx.internalize(arg, false);
        }
        if (ctx.b_internalized(arg)) {
            bv = ctx.get_bool_var(arg);
            if (is_uninterp(arg) && null_theory_var == ctx.get_var_theory(bv)) {
                ctx.set_var_theory(bv, get_id());
            }
            has_bv = (ctx.get_var_theory(bv) == get_id());
        }
        else if (m.is_true(arg)) {
            bv = true_bool_var;
            has_bv = true;
        }
        else if (m.is_false(arg)) {
            bv = true_bool_var;
            has_bv = true;
            negate = !negate;
        }

        // assumes relevancy level = 2 or 0.
        // TBD: should should have been like an uninterpreted
        // function internalize, where enodes for each argument
        // is available. 
        if (!has_bv) {
            app_ref tmp(m), fml(m);
            pb_util pb(m);
            tmp = pb.mk_fresh_bool();
            fml = m.mk_iff(tmp, arg);
            TRACE("pb", tout << "create proxy " << fml << "\n";);
            ctx.internalize(fml, false);
            SASSERT(ctx.b_internalized(tmp));
            bv = ctx.get_bool_var(tmp);
            SASSERT(get_id() == ctx.get_var_theory(bv));
            literal lit(ctx.get_bool_var(fml));
            ctx.mk_th_axiom(get_id(), 1, &lit);
            ctx.mark_as_relevant(tmp.get());
        }
        return negate?~literal(bv):literal(bv);
    }

    void theory_pb::del_watch(watch_list& watch, unsigned index, ineq& c, unsigned ineq_index) {
        SASSERT(c.is_ge());
        if (index < watch.size()) {
            std::swap(watch[index], watch[watch.size()-1]);
        }
        watch.pop_back();
        
        SASSERT(ineq_index < c.watch_size());
        scoped_mpz coeff(m_mpz_mgr);
        coeff = c.ncoeff(ineq_index);
        if (ineq_index + 1 < c.watch_size()) {
            std::swap(c.args()[ineq_index], c.args()[c.watch_size()-1]);
        }
        --c.m_watch_sz;
        c.m_watch_sum  -= coeff;
        if (coeff == c.max_watch()) {
            coeff = c.ncoeff(0);
            for (unsigned i = 1; coeff != c.max_watch() && i < c.watch_size(); ++i) {
                if (coeff < c.ncoeff(i)) coeff = c.ncoeff(i);
            }
            c.set_max_watch(coeff);
        }

        // current index of unwatched literal is c.watch_size().
    }

    void theory_pb::add_watch(ineq& c, unsigned i) {
        SASSERT(c.is_ge());
        literal lit = c.lit(i);
        scoped_mpz coeff(m_mpz_mgr);
        coeff = c.ncoeff(i);
        c.m_watch_sum += coeff;
        SASSERT(i >= c.watch_size());
        
        if (i > c.watch_size()) {
            std::swap(c.args()[i], c.args()[c.watch_size()]);
        }
        ++c.m_watch_sz;
        if (coeff > c.max_watch()) {
            c.set_max_watch(coeff);
        }
        watch_literal(lit, &c);
    }

    void theory_pb::watch_literal(literal lit, ineq* c) {
        ptr_vector<ineq>* ineqs;
        if (!m_lwatch.find(lit.index(), ineqs)) {
            ineqs = alloc(ptr_vector<ineq>);
            m_lwatch.insert(lit.index(), ineqs);
        }
        ineqs->push_back(c);
    }

    void theory_pb::watch_var(bool_var v, ineq* c) {
        ptr_vector<ineq>* ineqs;
        if (!m_vwatch.find(v, ineqs)) {
            ineqs = alloc(ptr_vector<ineq>);
            m_vwatch.insert(v, ineqs);
        }
        ineqs->push_back(c);
    }

    void theory_pb::unwatch_var(bool_var v, ineq* c) {
        ptr_vector<ineq>* ineqs = 0;            
        if (m_vwatch.find(v, ineqs)) {
            remove(*ineqs, c);
        }
    }

    void theory_pb::unwatch_literal(literal w, ineq* c) {
        ptr_vector<ineq>* ineqs = 0;            
        if (m_lwatch.find(w.index(), ineqs)) {
            remove(*ineqs, c);
        }
    }

    void theory_pb::remove(ptr_vector<ineq>& ineqs, ineq* c) {
        for (unsigned j = 0; j < ineqs.size(); ++j) {
            if (ineqs[j] == c) {                        
                std::swap(ineqs[j], ineqs[ineqs.size()-1]);
                ineqs.pop_back();
                break;
            }
        }
    }

    void theory_pb::collect_statistics(::statistics& st) const {
        st.update("pb conflicts", m_stats.m_num_conflicts);
        st.update("pb propagations", m_stats.m_num_propagations);
        st.update("pb predicates", m_stats.m_num_predicates);        
        st.update("pb compilations", m_stats.m_num_compiles);
        st.update("pb compiled clauses", m_stats.m_num_compiled_clauses);
        st.update("pb compiled vars", m_stats.m_num_compiled_vars);
        m_simplex.collect_statistics(st);
    }
    
    void theory_pb::reset_eh() {
        
        // m_watch;
        u_map<ptr_vector<ineq>*>::iterator it = m_lwatch.begin(), end = m_lwatch.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        it = m_vwatch.begin(), end = m_vwatch.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            dealloc(itc->m_value);
        }
        m_lwatch.reset();
        m_vwatch.reset();
        m_ineqs.reset();
        m_ineqs_trail.reset();
        m_ineqs_lim.reset();
        m_stats.reset();
        m_to_compile.reset();
    }

    void theory_pb::new_eq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }
    
    final_check_status theory_pb::final_check_eh() {
        TRACE("pb", display(tout););
        DEBUG_CODE(validate_final_check(););
        return FC_DONE;
    }

    void theory_pb::assign_eh(bool_var v, bool is_true) {
        ptr_vector<ineq>* ineqs = 0;
        literal nlit(v, is_true);
        TRACE("pb", tout << "assign: " << ~nlit << "\n";);
        if (m_lwatch.find(nlit.index(), ineqs)) {
            if (m_enable_simplex) {
                mpq_inf num(mpq(is_true?1:0),mpq(0));
                if (!update_bound(v, ~nlit, is_true, num)) {
                    return;
                }

                if (!check_feasible()) {
                    return;
                }
            }

            for (unsigned i = 0; i < ineqs->size(); ++i) {
                ineq* c = (*ineqs)[i]; 
                SASSERT(c->is_ge());
                if (assign_watch_ge(v, is_true, *ineqs, i)) {
                    // i was removed from watch list.
                    --i;
                }
            }
        }
        if (m_vwatch.find(v, ineqs)) {
            for (unsigned i = 0; i < ineqs->size(); ++i) {
                ineq* c = (*ineqs)[i]; 
                assign_watch(v, is_true, *c);
            }
        }
        ineq* c = 0;
        if (m_ineqs.find(v, c)) {
            if (m_enable_simplex) {
                row_info const& info = m_ineq_row_info.find(v);
                scoped_eps_numeral coeff(m_mpq_inf_mgr);
                coeff = std::make_pair(info.m_bound.to_mpq(), mpq(0));
                unsigned slack = info.m_slack;
                if (is_true) {
                    update_bound(slack, literal(v), true, coeff);
                    if (c->is_eq()) {
                        update_bound(slack, literal(v), false, coeff);
                    }
                }
                else if (c->is_ge()) {
                    m_mpq_inf_mgr.sub(coeff, std::make_pair(mpq(1),mpq(0)), coeff);
                    update_bound(slack, ~literal(v), false, coeff);
                }

                if (!check_feasible()) {
                    return;
                }
            }
            if (c->is_ge()) {
                assign_ineq(*c, is_true);
            }
            else {
                assign_eq(*c, is_true);
            }
        }
    }

    literal_vector& theory_pb::get_all_literals(ineq& c, bool negate) {
        context& ctx = get_context();
        literal_vector& lits = get_lits();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.lit(i);
            switch(ctx.get_assignment(l)) {
            case l_true: 
                lits.push_back(negate?(~l):l);
                break;
            case l_false:
                lits.push_back(negate?l:(~l));
                break;
            default:
                break;
            }
        }
        return lits;

    }

    literal_vector& theory_pb::get_helpful_literals(ineq& c, bool negate) {
        scoped_mpz sum(m_mpz_mgr);
        mpz const& k = c.mpz_k();
        context& ctx = get_context();
        literal_vector& lits = get_lits();
        for (unsigned i = 0; sum < k && i < c.size(); ++i) {
            literal l = c.lit(i);
            if (ctx.get_assignment(l) == l_true) {
                sum += c.ncoeff(i);
                if (negate) l = ~l;
                lits.push_back(l);
            }
        }
        SASSERT(sum >= k);
        return lits;
    }

    literal_vector& theory_pb::get_unhelpful_literals(ineq& c, bool negate) {
        context& ctx = get_context();
        literal_vector& lits = get_lits();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.lit(i);
            if (ctx.get_assignment(l) == l_false) {
                if (negate) l = ~l;
                lits.push_back(l);
            }
        }
        return lits;
    }

    class theory_pb::rewatch_vars : public trail<context> {
        theory_pb& pb;
        ineq&      c;
    public:
        rewatch_vars(theory_pb& p, ineq& c): pb(p), c(c) {}        
        virtual void undo(context& ctx) {
            for (unsigned i = 0; i < c.size(); ++i) {
                pb.watch_var(c.lit(i).var(), &c);
            }
        }
    };

    class theory_pb::negate_ineq : public trail<context> {
        ineq& c;
    public:
        negate_ineq(ineq& c): c(c) {}
        virtual void undo(context& ctx) {
            c.negate();
        }
    };

    /**
       \brief propagate assignment to inequality.
       This is a basic, non-optimized implementation based
       on the assumption that inequalities are mostly units
       and/or relatively few compared to number of argumets.
     */
    void theory_pb::assign_ineq(ineq& c, bool is_true) {
        context& ctx = get_context();
        ctx.push_trail(value_trail<context, scoped_mpz>(c.m_max_sum));
        ctx.push_trail(value_trail<context, scoped_mpz>(c.m_min_sum));
        ctx.push_trail(value_trail<context, unsigned>(c.m_nfixed));
        ctx.push_trail(rewatch_vars(*this, c));

        clear_watch(c);
        SASSERT(c.is_ge());
        unsigned sz = c.size();
        if (c.lit().sign() == is_true) {
            c.negate();
            ctx.push_trail(negate_ineq(c));
        }

        scoped_mpz maxsum(m_mpz_mgr), mininc(m_mpz_mgr);
        for (unsigned i = 0; i < sz; ++i) {
            lbool asgn = ctx.get_assignment(c.lit(i));
            if (asgn != l_false) {
                maxsum += c.ncoeff(i);
            }
            if (asgn == l_undef && (mininc.is_zero() || mininc > c.ncoeff(i))) {
                mininc = c.ncoeff(i);
            }
        }

        TRACE("pb", 
              tout << "assign: " << c.lit() << "\n";
              display(tout, c); );

        if (maxsum < c.mpz_k()) {
            literal_vector& lits = get_unhelpful_literals(c, false);
            lits.push_back(~c.lit());
            add_clause(c, lits);
        }
        else {
            init_watch_literal(c);
            SASSERT(c.m_watch_sum >= c.mpz_k());
            DEBUG_CODE(validate_watch(c););
        }

        // perform unit propagation
        if (maxsum >= c.mpz_k() && maxsum - mininc < c.mpz_k()) { 
            literal_vector& lits = get_unhelpful_literals(c, true);
            lits.push_back(c.lit());
            for (unsigned i = 0; i < sz; ++i) {
                if (ctx.get_assignment(c.lit(i)) == l_undef) {
                    DEBUG_CODE(validate_assign(c, lits, c.lit(i)););
                    add_assign(c, lits, c.lit(i));
                }                
            }
        }
    }

    /**
       \brief propagate assignment to equality.
    */
    void theory_pb::assign_eq(ineq& c, bool is_true) {
        SASSERT(c.is_eq());
        
    }

    /**
       Propagation rules:

       nfixed = N & minsum = k -> T
       nfixed = N & minsum != k -> F
    
       minsum > k or maxsum < k -> F
       minsum = k & = -> fix 0 variables
       nfixed+1 = N & = -> fix unassigned variable or conflict
       nfixed+1 = N & != -> maybe forced unassigned to ensure disequal
       minsum >= k -> T
       maxsum <  k -> F
    */

    void theory_pb::assign_watch(bool_var v, bool is_true, ineq& c) {
        
        context& ctx = get_context();
        unsigned i;
        literal l = c.lit();
        lbool asgn = ctx.get_assignment(l);

        if (c.max_sum() < c.mpz_k() && asgn == l_false) {
            return;
        }
        if (c.is_ge() && c.min_sum() >= c.mpz_k() && asgn == l_true) {
            return;
        }
        for (i = 0; i < c.size(); ++i) {
            if (c.lit(i).var() == v) {
                break;
            }
        }
        
        TRACE("pb", display(tout << "assign watch " << literal(v,!is_true) << " ", c, true););

        SASSERT(i < c.size());
        if (c.lit(i).sign() == is_true) {
            ctx.push_trail(value_trail<context, scoped_mpz>(c.m_max_sum));
            c.m_max_sum -= c.ncoeff(i);
        }
        else {
            ctx.push_trail(value_trail<context, scoped_mpz>(c.m_min_sum));
            c.m_min_sum += c.ncoeff(i);            
        }
        DEBUG_CODE(
            scoped_mpz sum(m_mpz_mgr);
            scoped_mpz maxs(m_mpz_mgr);
            for (unsigned i = 0; i < c.size(); ++i) {
                if (ctx.get_assignment(c.lit(i)) == l_true)  sum  += c.ncoeff(i);
                if (ctx.get_assignment(c.lit(i)) != l_false) maxs += c.ncoeff(i);
            }
            CTRACE("pb", (maxs > c.max_sum()), display(tout, c, true););
            SASSERT(c.min_sum() <= sum);
            SASSERT(sum <= maxs);
            SASSERT(maxs <= c.max_sum());
            );
        SASSERT(c.min_sum() <= c.max_sum());
        SASSERT(!m_mpz_mgr.is_neg(c.min_sum()));
        ctx.push_trail(value_trail<context, unsigned>(c.m_nfixed));
        ++c.m_nfixed;
        SASSERT(c.nfixed() <= c.size());
        if (c.is_ge() && c.min_sum() >= c.mpz_k() && asgn != l_true) {
            TRACE("pb", display(tout << "Set " << l << "\n", c, true););
            add_assign(c, get_helpful_literals(c, false), l);
        }        
        else if (c.max_sum() < c.mpz_k() && asgn != l_false) {
            TRACE("pb", display(tout << "Set " << ~l << "\n", c, true););
            add_assign(c, get_unhelpful_literals(c, true), ~l);
        }
        else if (c.is_eq() && c.nfixed() == c.size() && c.min_sum() == c.mpz_k() && asgn != l_true) {
            TRACE("pb", display(tout << "Set " << l << "\n", c, true););
            add_assign(c, get_all_literals(c, false), l);     
        }
        else if (c.is_eq() && c.nfixed() == c.size() && c.min_sum() != c.mpz_k() && asgn != l_false) {
            TRACE("pb", display(tout << "Set " << ~l << "\n", c, true););
            add_assign(c, get_all_literals(c, false), ~l);     
        }
#if 0
        else if (c.is_eq() && c.min_sum() > c.mpz_k() && asgn != l_false) {
            TRACE("pb", display(tout << "Set " << ~l << "\n", c, true););
            add_assign(c, get_all_literals(c, false), ~l);
        }
        else if (c.is_eq() && asgn == l_true && c.min_sum() == c.mpz_k() && c.max_sum() > c.mpz_k()) {
            literal_vector& lits = get_all_literals(c, false);
            lits.push_back(c.lit());
            for (unsigned i = 0; i < c.size(); ++i) {
                if (ctx.get_assignment(c.lit(i)) == l_undef) {
                    add_assign(c, lits, ~c.lit(i)); 
                }
            }
        }
#endif
        else {
            IF_VERBOSE(3, display(verbose_stream() << "no propagation ", c, true););
        }
    }


    /**
       \brief v is assigned in inequality c. Update current bounds and watch list.
       Optimize for case where the c.lit() is True. This covers the case where 
       inequalities are unit literals and formulas in negation normal form 
       (inequalities are closed under negation).       
     */
    bool theory_pb::assign_watch_ge(bool_var v, bool is_true, watch_list& watch, unsigned watch_index) {
        bool removed = false;
        context& ctx = get_context();
        ineq& c = *watch[watch_index];
        //display(std::cout << v << " ", c, true);
        unsigned w = c.find_lit(v, 0, c.watch_size());
        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        SASSERT(is_true == c.lit(w).sign());

        //
        // watch_sum is decreased.
        // Adjust set of watched literals.
        //
        
        scoped_mpz k_coeff(m_mpz_mgr), k(m_mpz_mgr);
        k = c.mpz_k();
        k_coeff = k;
        k_coeff += c.ncoeff(w);
        bool add_more = c.watch_sum() < k_coeff + c.max_watch();
        for (unsigned i = c.watch_size(); add_more && i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) != l_false) {
                add_watch(c, i);
                add_more = c.watch_sum() < k_coeff + c.max_watch();
            }
        }        
        
        if (c.watch_sum() < k_coeff) {
            //
            // L: 3*x1 + 2*x2 + x4 >= 3, but x1 <- 0, x2 <- 0
            // create clause x1 or x2 or ~L
            // 
            literal_vector& lits = get_unhelpful_literals(c, false);
            lits.push_back(~c.lit());
            add_clause(c, lits);
        }
        else {
            del_watch(watch, watch_index, c, w);
            removed = true;
            SASSERT(c.watch_sum() >= k);
            if (c.watch_sum() < k + c.max_watch()) {
                
                //
                // opportunities for unit propagation for unassigned 
                // literals whose coefficients satisfy
                // c.watch_sum() < k
                //
                // L: 3*x1 + 2*x2 + x4 >= 3, but x1 <- 0
                // Create clauses x1 or ~L or x2 
                //                x1 or ~L or x4
                //

                literal_vector& lits = get_unhelpful_literals(c, true);
                lits.push_back(c.lit());
                scoped_mpz deficit(m_mpz_mgr);
                deficit = c.watch_sum() - k;
                for (unsigned i = 0; i < c.size(); ++i) {
                    if (ctx.get_assignment(c.lit(i)) == l_undef && deficit < c.ncoeff(i)) {
                        DEBUG_CODE(validate_assign(c, lits, c.lit(i)););
                        add_assign(c, lits, c.lit(i));                  
                        // break;
                    }
                }
            }
            //
            // else: c.watch_sum() >= k + c.max_watch()
            //
        }

        TRACE("pb", 
              tout << "assign: " << literal(v,!is_true) << "\n";
              display(tout, c); );


        return removed;
    }

    struct theory_pb::psort_expr {
        context&     ctx;
        ast_manager& m;
        theory_pb&   th;
        pb_util      pb;
        typedef smt::literal literal;
        typedef smt::literal_vector literal_vector;
      
        psort_expr(context& c, theory_pb& th):
            ctx(c), 
            m(c.get_manager()),
            th(th),
            pb(m) {}

        literal fresh() {
            app_ref y(m);
            y = pb.mk_fresh_bool();
            return literal(ctx.mk_bool_var(y));
        }
        
        literal mk_max(literal a, literal b) {
            if (a == b) return a;
            expr_ref t1(m), t2(m), t3(m);
            ctx.literal2expr(a, t1);
            ctx.literal2expr(b, t2);
            t3 = m.mk_or(t1, t2);
            bool_var v = ctx.b_internalized(t3)?ctx.get_bool_var(t3):ctx.mk_bool_var(t3);
            return literal(v);
        }

        literal mk_min(literal a, literal b) {
            if (a == b) return a;
            expr_ref t1(m), t2(m), t3(m);
            ctx.literal2expr(a, t1);
            ctx.literal2expr(b, t2);
            t3 = m.mk_and(t1, t2);
            bool_var v = ctx.b_internalized(t3)?ctx.get_bool_var(t3):ctx.mk_bool_var(t3);
            return literal(v);
        }

        literal mk_not(literal a) { return ~a; }

        void mk_clause(unsigned n, literal const* ls) {
            literal_vector tmp(n, ls);
            ctx.mk_clause(n, tmp.c_ptr(), th.justify(tmp), CLS_AUX, 0);
        }

        literal mk_false() { return false_literal; }
        literal mk_true() { return true_literal; }

        std::ostream& pp(std::ostream& out, literal l) { return out << l; }
        
    };

    // for testing
    literal theory_pb::assert_ge(context& ctx, unsigned k, unsigned n, literal const* xs) {
        theory_pb_params p;
        theory_pb th(ctx.get_manager(), p);
        psort_expr ps(ctx, th);
        psort_nw<psort_expr> sort(ps);
        return sort.ge(false, k, n, xs);
    }


    void theory_pb::inc_propagations(ineq& c) {
        ++c.m_num_propagations;
        if (c.m_compiled == l_false && c.m_num_propagations > c.m_compilation_threshold) {
            c.m_compiled = l_undef;
            m_to_compile.push_back(&c);
        }
    }

    void theory_pb::restart_eh() {
        for (unsigned i = 0; i < m_to_compile.size(); ++i) {
            compile_ineq(*m_to_compile[i]);
        }
        m_to_compile.reset();
    }


    void theory_pb::compile_ineq(ineq& c) {
        ++m_stats.m_num_compiles;
        context& ctx = get_context();
        // only cardinality constraints are compiled.
        SASSERT(c.m_compilation_threshold < UINT_MAX);
        DEBUG_CODE(for (unsigned i = 0; i < c.size(); ++i) SASSERT(c.coeff(i).is_int()); );
        unsigned k = c.k().get_unsigned();
        unsigned num_args = c.size();


        literal thl = c.lit();
        literal at_least_k;

        literal_vector in;
        for (unsigned i = 0; i < num_args; ++i) {
            rational n = c.coeff(i);
            lbool val = ctx.get_assignment(c.lit()); 
            if (val != l_undef  && 
                ctx.get_assign_level(thl) == ctx.get_base_level()) {
                if (val == l_true) {
                    unsigned m = n.get_unsigned();
                    if (k < m) {
                        return;
                    }
                    k -= m;
                }
                continue;
            }
            while (n.is_pos()) {
                in.push_back(c.lit(i));
                n -= rational::one();
            }
        }
        if (ctx.get_assignment(thl) == l_true  && 
            ctx.get_assign_level(thl) == ctx.get_base_level()) {
            psort_expr ps(ctx, *this);
            psort_nw<psort_expr> sortnw(ps);
            sortnw.m_stats.reset();
            at_least_k = sortnw.ge(false, k, in.size(), in.c_ptr());
            ctx.mk_clause(~thl, at_least_k, justify(~thl, at_least_k));
            m_stats.m_num_compiled_vars += sortnw.m_stats.m_num_compiled_vars;
            m_stats.m_num_compiled_clauses += sortnw.m_stats.m_num_compiled_clauses;
        }
        else {
            psort_expr ps(ctx, *this);
            psort_nw<psort_expr> sortnw(ps);
            sortnw.m_stats.reset();
            literal at_least_k = sortnw.ge(true, k, in.size(), in.c_ptr());
            ctx.mk_clause(~thl, at_least_k, justify(~thl, at_least_k));
            ctx.mk_clause(~at_least_k, thl, justify(thl, ~at_least_k));
            m_stats.m_num_compiled_vars += sortnw.m_stats.m_num_compiled_vars;
            m_stats.m_num_compiled_clauses += sortnw.m_stats.m_num_compiled_clauses;
        }
        IF_VERBOSE(1, verbose_stream() 
                   << "(smt.pb compile sorting network bound: " 
                   << k << " literals: " << in.size() << ")\n";);

        TRACE("pb", tout << thl << "\n";);
        // auxiliary clauses get removed when popping scopes.
        // we have to recompile the circuit after back-tracking.
        c.m_compiled = l_false;
        ctx.push_trail(value_trail<context, lbool>(c.m_compiled));
        c.m_compiled = l_true;
    }


    void theory_pb::init_search_eh() {
        m_to_compile.reset();
    }

    void theory_pb::push_scope_eh() {
        m_ineqs_lim.push_back(m_ineqs_trail.size());
    }

    void theory_pb::pop_scope_eh(unsigned num_scopes) {

        // remove inequalities.
        unsigned new_lim = m_ineqs_lim.size()-num_scopes;
        unsigned sz = m_ineqs_lim[new_lim];
        while (m_ineqs_trail.size() > sz) {
            bool_var v = m_ineqs_trail.back();
            ineq* c = 0;
            VERIFY(m_ineqs.find(v, c));
            clear_watch(*c);
            m_ineqs.remove(v);
            m_ineqs_trail.pop_back();
            if (m_enable_simplex) {
                row_info r_info;
                VERIFY(m_ineq_row_info.find(v, r_info));
                m_ineq_row_info.erase(v);
                bool_var v2 = m_ineq_rep.find(r_info.m_rep);
                if (v == v2) {
                    m_simplex.del_row(r_info.m_slack);
                    m_ineq_rep.erase(r_info.m_rep);
                }
            }
            dealloc(c);
        }
        m_ineqs_lim.resize(new_lim);
    }

    void theory_pb::clear_watch(ineq& c) {
        for (unsigned i = 0; i < c.size(); ++i) {
            literal w = c.lit(i);
            unwatch_var(w.var(), &c);
            unwatch_literal(w, &c);            
        }
        c.m_watch_sum.reset();
        c.m_watch_sz = 0;
        c.m_max_watch.reset();
        c.m_nfixed = 0;
        c.m_max_sum.reset();
        c.m_min_sum.reset();
    }

    class theory_pb::unwatch_ge : public trail<context> {
        theory_pb& pb;
        ineq&      c;
    public:
        unwatch_ge(theory_pb& p, ineq& c): pb(p), c(c) {}
        
        virtual void undo(context& ctx) {
            for (unsigned i = 0; i < c.watch_size(); ++i) {
                pb.unwatch_literal(c.lit(i), &c);
            }
            c.m_watch_sz = 0;
            c.m_watch_sum.reset();
            c.m_max_watch.reset();
        }        
    };


    void theory_pb::init_watch_literal(ineq& c) {
        context& ctx = get_context();
        scoped_mpz max_k(m_mpz_mgr);
        c.m_watch_sum.reset();
        c.m_watch_sz = 0;
        c.m_max_watch.reset();
        bool watch_more = true;
        for (unsigned i = 0; watch_more && i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) != l_false) {
                add_watch(c, i);
                max_k = c.mpz_k();
                max_k += c.max_watch();
                watch_more = c.m_watch_sum < max_k;
            }       
        }        
        ctx.push_trail(unwatch_ge(*this, c));
    }

    void theory_pb::init_watch_var(ineq& c) {
        c.m_min_sum.reset();
        c.m_max_sum.reset();
        c.m_nfixed = 0;
        c.m_watch_sum.reset();
        c.m_max_watch.reset();
        c.m_watch_sz = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            watch_var(c.lit(i).var(), &c);
            c.m_max_sum += c.ncoeff(i);
        }                   
    }

    literal_vector& theory_pb::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    class theory_pb::pb_justification : public theory_propagation_justification {
        ineq& m_ineq;
    public:
        pb_justification(ineq& c, family_id fid, region & r, 
                      unsigned num_lits, literal const * lits, literal consequent):
                      theory_propagation_justification(fid, r, num_lits, lits, consequent),
                      m_ineq(c)
                      {}
        ineq& get_ineq() { return m_ineq; }
    };

    void theory_pb::add_assign(ineq& c, literal_vector const& lits, literal l) {
        inc_propagations(c);
        m_stats.m_num_propagations++;
        context& ctx = get_context();
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - "; 
              for (unsigned i = 0; i < lits.size(); ++i) {
                  tout << lits[i] << " ";
              }
              tout << "=> " << l << "\n";
              display(tout, c, true););

        ctx.assign(l, ctx.mk_justification(
                       pb_justification(
                           c, get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), l)));
    }
    
                   

    void theory_pb::add_clause(ineq& c, literal_vector const& lits) {
        inc_propagations(c);
        m_stats.m_num_conflicts++;
        context& ctx = get_context();
#if 0
        if (m_stats.m_num_conflicts == 1000) {
            display(std::cout);
        }
#endif
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - "; 
              for (unsigned i = 0; i < lits.size(); ++i) {
                  tout << lits[i] << " ";
              }
              tout << "\n";
              display(tout, c, true););

        justification* js = 0;

        if (m_conflict_frequency == 0 || (m_conflict_frequency -1 == (c.m_num_propagations % m_conflict_frequency))) {
            resolve_conflict(c);
        }
        if (proofs_enabled()) {                                         
            js = alloc(theory_lemma_justification, get_id(), ctx, lits.size(), lits.c_ptr());
        }
        ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);
    }


    void theory_pb::set_mark(bool_var v, unsigned idx) {
        SASSERT(v != null_bool_var);
        if (v >= static_cast<bool_var>(m_conseq_index.size())) {
            m_conseq_index.resize(v+1, null_index);
        }
        SASSERT(!is_marked(v) || m_conseq_index[v] == idx);
        m_marked.push_back(v);
        m_conseq_index[v] = idx;        
    }

    bool theory_pb::is_marked(bool_var v) const {
        return 
            (v < static_cast<bool_var>(m_conseq_index.size())) &&
            (m_conseq_index[v] != null_index);
    }

    void theory_pb::unset_mark(bool_var v) {
        SASSERT(v != null_bool_var);
        if (v < static_cast<bool_var>(m_conseq_index.size())) {
            m_conseq_index[v] = null_index;
        }
    }

    void theory_pb::unset_marks() {
        for (unsigned i = 0; i < m_marked.size(); ++i) {
            unset_mark(m_marked[i]);
        }
        m_marked.reset();
    }

    void theory_pb::process_antecedent(literal l, numeral coeff) {        
        context& ctx = get_context();
        bool_var v = l.var();
        unsigned lvl = ctx.get_assign_level(v);

        if (ctx.get_assignment(l) != l_false) {
            m_lemma.m_k -= coeff;
            if (m_learn_complements && is_marked(v)) {
                SASSERT(ctx.get_assignment(l) == l_true);
                numeral& lcoeff = m_lemma[m_conseq_index[v]].second; 
                lcoeff -= coeff;
                if (!lcoeff.is_pos()) {
                    // perhaps let lemma simplification change coefficient
                    // when negative?
                    remove_from_lemma(m_conseq_index[v]);                    
                }
            }
        }
        else if (lvl > ctx.get_base_level()) {
            if (is_marked(v)) {
                m_lemma[m_conseq_index[v]].second += coeff;
                SASSERT(m_lemma[m_conseq_index[v]].second.is_pos());
            }
            else {                
                if (lvl == m_conflict_lvl) {
                    TRACE("pb", tout << "add mark: " << l << " " << coeff << "\n";);
                    ++m_num_marks;
                }
                set_mark(v, m_lemma.size());
                m_lemma.push_back(std::make_pair(l, coeff));
            }
            TRACE("pb_verbose", tout  
                  << "ante: " << m_lemma.lit(m_conseq_index[v]) << "*" 
                  << m_lemma.coeff(m_conseq_index[v]) << " " << lvl << "\n";);
        }
    }

    void theory_pb::process_ineq(ineq& c, literal conseq, numeral coeff1) {

        //
        // Create CUT.
        //

        // 
        // . find coeff2
        // . find lcm of coefficients to conseq.
        // . multiply m_lemma by lcm/coeff coefficient to align.
        // . create lcm/coeff_2 to multiply on this side.
        // . cut resolve constraints.
        // 

        context& ctx = get_context();
        numeral coeff2 = (conseq==null_literal)?numeral::one():numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            if (c.lit(i) == conseq) {
                coeff2 = c.coeff(i);
                break;
            }
        }
        SASSERT(coeff2.is_pos());
        numeral lc = lcm(coeff1, coeff2);
        numeral g = lc/coeff1;
        SASSERT(g.is_int());
        if (g > numeral::one()) {
            for (unsigned i = 0; i < m_lemma.size(); ++i) {
                m_lemma[i].second *= g;
            }
            m_lemma.m_k *= g;
        }
        g = lc/coeff2;
        SASSERT(g.is_int());
        m_lemma.m_k += g*c.k();

        for (unsigned i = 0; i < c.size(); ++i) {
            process_antecedent(c.lit(i), g*c.coeff(i));
        }

        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        if (ctx.get_assign_level(c.lit()) > ctx.get_base_level()) {
            m_ineq_literals.push_back(c.lit());
        }
    }
        
    //
    // modeled after sat_solver/smt_context
    //
    bool theory_pb::resolve_conflict(ineq& c) {
       
        if (!c.is_ge()) {
            return false;
        }
        TRACE("pb", display(tout, c, true););

        bool_var v;
        literal conseq;
        context& ctx = get_context();
        unsigned& lvl = m_conflict_lvl = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) == l_false) {
                lvl = std::max(lvl, ctx.get_assign_level(c.lit(i)));
            }
        }
        if (lvl < ctx.get_assign_level(c.lit()) || lvl == ctx.get_base_level()) {
            return false;
        }

        unset_marks();
        m_num_marks = 0;
        m_lemma.reset();
        m_lemma.m_k.reset();
        m_ineq_literals.reset();
        process_ineq(c, null_literal, numeral::one()); // add consequent to lemma.

        // point into stack of assigned literals
        literal_vector const& lits = ctx.assigned_literals();        
        SASSERT(!lits.empty());
        unsigned idx = lits.size()-1;
   
        while (m_num_marks > 0) {

            TRACE("pb_verbose", display(tout << "lemma ", m_lemma););

            lbool is_sat = m_lemma.normalize(false);
            if (is_sat == l_false) {
                break;
            }
            if (is_sat == l_true) {
                IF_VERBOSE(0, verbose_stream() << "lemma already evaluated\n";);
                TRACE("pb", tout << "lemma already evaluated\n";);
                return false;
            }
            TRACE("pb", display(tout, m_lemma););
            SASSERT(m_lemma.well_formed());         

            //
            // find the next marked variable in the assignment stack
            //
            do {
                conseq = lits[idx];
                v = conseq.var();
                --idx;
            }
            while (!is_marked(v) && idx > 0);
            if (idx == 0 && !is_marked(v)) {
                //
                // Yes, this can (currently) happen because
                // the decisions for performing unit propagation
                // are made asynchronously.
                // In other words, PB unit propagation does not follow the
                // same order as the assignment stack.
                // It is not a correctness bug but causes to miss lemmas.
                //
                IF_VERBOSE(2, display_resolved_lemma(verbose_stream()););
                TRACE("pb", display_resolved_lemma(tout););
                return false;
            }
            
            unsigned conseq_index = m_conseq_index[v];
            numeral conseq_coeff = m_lemma.coeff(conseq_index);

            TRACE("pb", display(tout, m_lemma, true);
                  tout << "conseq: " << conseq << " at index: " << conseq_index << "\n";);

            SASSERT(~conseq == m_lemma.lit(conseq_index));

            remove_from_lemma(conseq_index);

            b_justification js = ctx.get_justification(v);

            //
            // Resolve selected conseq with antecedents.
            // 

            switch(js.get_kind()) {
                
            case b_justification::CLAUSE: {
                clause& cls = *js.get_clause();
                justification* cjs = cls.get_justification();
                if (cjs && !is_proof_justification(*cjs)) {
                    TRACE("pb", tout << "skipping justification for clause over: " << conseq << " " 
                          << typeid(*cjs).name() << "\n";);
                    m_ineq_literals.push_back(conseq);
                    break;
                }
                unsigned num_lits = cls.get_num_literals();
                if (cls.get_literal(0) == conseq) {
                    process_antecedent(cls.get_literal(1), conseq_coeff);
                }
                else {
                    SASSERT(cls.get_literal(1) == conseq);
                    process_antecedent(cls.get_literal(0), conseq_coeff);
                }
                for (unsigned i = 2; i < num_lits; ++i) {
                    process_antecedent(cls.get_literal(i), conseq_coeff);
                }
                TRACE("pb", for (unsigned i = 0; i < num_lits; ++i) tout << cls.get_literal(i) << " "; tout << "\n";);
                break;                
            }
            case b_justification::BIN_CLAUSE:
                process_antecedent(~js.get_literal(), conseq_coeff);
                TRACE("pb", tout << "binary: " << js.get_literal() << "\n";);
                break;
            case b_justification::AXIOM:
                if (ctx.get_assign_level(v) > ctx.get_base_level()) {
                    m_ineq_literals.push_back(conseq);
                }
                TRACE("pb", tout << "axiom " << conseq << "\n";);
                break;
            case b_justification::JUSTIFICATION: {
                justification* j = js.get_justification(); 
                pb_justification* pbj = 0;

                if (!conseq.sign() && j->get_from_theory() == get_id()) {                    
                    pbj = dynamic_cast<pb_justification*>(j);
                }
                if (pbj && pbj->get_ineq().is_eq()) {
                    // only resolve >= that are positive consequences.
                    pbj = 0;
                }
                if (pbj && pbj->get_ineq().lit() == conseq) {
                    // can't resolve against literal representing inequality.
                    pbj = 0;
                }
                if (pbj) {
                    // weaken the lemma and resolve.
                    TRACE("pb", display(tout << "resolve with inequality", pbj->get_ineq(), true););
                    process_ineq(pbj->get_ineq(), conseq, conseq_coeff);
                }
                else {
                    TRACE("pb", tout << "skipping justification for " << conseq 
                          << " from theory "  << j->get_from_theory() << " " 
                          << typeid(*j).name() << "\n";);
                    m_ineq_literals.push_back(conseq);
                }
                break;
            }
            default:
                UNREACHABLE();
            }            
        }

        TRACE("pb", 
              for (unsigned i = 0; i < m_ineq_literals.size(); ++i) {
                  tout << m_ineq_literals[i] << " ";
              }
              display(tout << "=> ", m_lemma););

        // 3x + 3y + z + u >= 4
        // ~x /\ ~y => z + u >= 

        IF_VERBOSE(4, display(verbose_stream() << "lemma1: ", m_lemma););
        hoist_maximal_values();
        lbool is_true = m_lemma.normalize(false);
        m_lemma.prune(false);

        IF_VERBOSE(4, display(verbose_stream() << "lemma2: ", m_lemma););
        //unsigned l_size = m_ineq_literals.size() + ((is_true==l_false)?0:m_lemma.size());
        //if (s_min_l_size >= l_size) {
        //    verbose_stream() << "(pb.conflict min size: " << l_size << ")\n";
        //    s_min_l_size = l_size;        
        //}
        //IF_VERBOSE(1, verbose_stream() << "(pb.conflict " << m_ineq_literals.size() << " " << m_lemma.size() << "\n";);
        switch(is_true) {
        case l_true:
            UNREACHABLE();
            return false;
        case l_false: 
            inc_propagations(c);
            m_stats.m_num_conflicts++;
            for (unsigned i = 0; i < m_ineq_literals.size(); ++i) {
                m_ineq_literals[i].neg();
            }
            ctx.mk_clause(m_ineq_literals.size(), m_ineq_literals.c_ptr(), justify(m_ineq_literals), CLS_AUX_LEMMA, 0);
            break;
        default: {
            app_ref tmp = m_lemma.to_expr(false, ctx, get_manager());
            internalize_atom(tmp, false);
            ctx.mark_as_relevant(tmp.get());
            literal l(ctx.get_bool_var(tmp));
            add_assign(c, m_ineq_literals, l);
            break;
        }
        }
        return true;    
    }

    bool theory_pb::is_proof_justification(justification const& j) const {
        return typeid(smt::justification_proof_wrapper) == typeid(j);
    }

    justification* theory_pb::justify(literal l1, literal l2) {
        literal lits[2] = { l1, l2 };
        justification* js = 0;
        if (proofs_enabled()) {                                         
            js = get_context().mk_justification(theory_axiom_justification(get_id(), get_context().get_region(), 2, lits));
        }
        return js;
    }

    justification* theory_pb::justify(literal_vector const& lits) {
        justification* js = 0;
        if (proofs_enabled()) {                                         
            js = get_context().mk_justification(theory_axiom_justification(get_id(), get_context().get_region(), lits.size(), lits.c_ptr()));
        }
        return js;        
    }

    void theory_pb::hoist_maximal_values() {
        for (unsigned i = 0; i < m_lemma.size(); ++i) {
            if (m_lemma.coeff(i) >= m_lemma.k()) {
                m_ineq_literals.push_back(~m_lemma.lit(i));
                std::swap(m_lemma[i], m_lemma[m_lemma.size()-1]);
                m_lemma.pop_back();
                --i;
            }
        }
    }

    void theory_pb::remove_from_lemma(unsigned idx) {
        // Remove conseq from lemma:
        literal lit = m_lemma.lit(idx);
        unsigned last = m_lemma.size()-1;
        if (idx != last) {
            m_lemma[idx] = m_lemma[last];
            m_conseq_index[m_lemma.lit(idx).var()] = idx;
        }
        m_lemma.pop_back();
        unset_mark(lit.var());
        --m_num_marks;
    }

    // debug methods

    void theory_pb::validate_watch(ineq const& c) const {
        scoped_mpz sum(m_mpz_mgr), max(m_mpz_mgr);
        for (unsigned i = 0; i < c.watch_size(); ++i) {
            sum += c.ncoeff(i);
            if (max < c.ncoeff(i)) {
                max = c.ncoeff(i);
            }
        }
        SASSERT(c.watch_sum() == sum);
        SASSERT(sum >= c.mpz_k());
        SASSERT(max == c.max_watch());
    }

    void theory_pb::validate_assign(ineq const& c, literal_vector const& lits, literal l) const {
        uint_set nlits;
        context& ctx = get_context();
        for (unsigned i = 0; i < lits.size(); ++i) {
            SASSERT(ctx.get_assignment(lits[i]) == l_true);
            nlits.insert((~lits[i]).index());
        }
        SASSERT(ctx.get_assignment(l) == l_undef);
        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        nlits.insert(l.index());
        numeral sum = numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lit = c.lit(i);
            if (!nlits.contains(lit.index())) {
                sum += c.coeff(i);
            }
        }
        CTRACE("pb", (sum >= c.k()),
               display(tout << "invalid assign" , c, true);
               for (unsigned i = 0; i < lits.size(); ++i) {
                   tout << lits[i] << " ";
               }
               tout << " => " << l << "\n";);
        SASSERT(sum < c.k());
    }

    void theory_pb::validate_final_check() {
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            validate_final_check(*itc->m_value);                
        }
    }

    void theory_pb::validate_final_check(ineq& c) {
        context& ctx = get_context();

        if (ctx.get_assignment(c.lit()) == l_undef) {
            return;
        }
        if (!ctx.is_relevant(c.lit())) {
            return;
        }
        numeral sum = numeral::zero(), maxsum = numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            switch(ctx.get_assignment(c.lit(i))) {
            case l_true:
                sum += c.coeff(i);
            case l_undef:
                maxsum += c.coeff(i);
                break;
            case l_false:
                break;
            }
        }
        TRACE("pb", display(tout << "validate: ", c, true);
              tout << "sum: " << sum << " " << maxsum << " ";
              tout << ctx.get_assignment(c.lit()) << "\n";
              );

        SASSERT(sum <= maxsum);
        SASSERT(!c.is_ge() || (sum >= c.k()) == (ctx.get_assignment(c.lit()) == l_true));
        SASSERT(!c.is_ge() || (maxsum < c.k()) == (ctx.get_assignment(c.lit()) == l_false));
        SASSERT(!c.is_eq() || (sum == c.k()) == (ctx.get_assignment(c.lit()) == l_true));
    }

    // display methods

    void theory_pb::display_resolved_lemma(std::ostream& out) const {
        context& ctx = get_context();
        literal_vector const& lits = ctx.assigned_literals();                
        bool_var v;
        unsigned lvl;
        out << "num marks: " << m_num_marks << "\n";
        out << "conflict level: " << m_conflict_lvl << "\n";
        for (unsigned i = 0; i < lits.size(); ++i) {
            v = lits[i].var();
            lvl = ctx.get_assign_level(v);
            out << lits[i]
                << "@ " << lvl 
                << " " << (is_marked(v)?"m":"u") 
                << "\n";
            
            if (lvl == m_conflict_lvl && is_marked(v)) {
                out << "skipped: " << lits[i] << ":"<< i << "\n";
            }
        }
        display(out, m_lemma, true); 

        unsigned nc = 0;
        for (unsigned i = 0; i < m_lemma.size(); ++i) {
            v = m_lemma.lit(i).var();
            lvl = ctx.get_assign_level(v);
            if (lvl == m_conflict_lvl) ++nc;
            out << m_lemma.lit(i) 
                << "@" << lvl 
                << " " << (is_marked(v)?"m":"u") 
                << " " << ctx.get_assignment(m_lemma.lit(i))
                << "\n";
        }
        out << "num conflicts: " << nc << "\n";
    }

    std::ostream& theory_pb::display(std::ostream& out, arg_t const& c, bool values) const {
        return c.display(get_context(), out, values);
    }

    std::ostream& theory_pb::display(std::ostream& out, ineq const& c, bool values) const {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        out << c.lit();
        if (c.lit() != null_literal) {
            if (values) {
                out << "@(" << ctx.get_assignment(c.lit());
                if (ctx.get_assignment(c.lit()) != l_undef) {
                    out << ":" << ctx.get_assign_level(c.lit());
                }
                out << ")";
            }
            expr_ref tmp(m);
            ctx.literal2expr(c.lit(), tmp);
            out << " " << tmp << "\n";
        }
        else {
            out << " ";
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l(c.lit(i));
            if (!c.coeff(i).is_one()) {
                out << c.coeff(i) << "*";
            }
            out << l;
            if (values) {
                out << "@(" << ctx.get_assignment(l);
                if (ctx.get_assignment(l) != l_undef) {
                    out << ":" << ctx.get_assign_level(l);
                }
                out << ")";
            }
            if (i + 1 == c.watch_size()) {
                out << " .w ";
            }
            if (i + 1 < c.size()) {
                out << " + ";
            }
        }
        out << (c.is_ge()?" >= ":" = ") << c.k()  << "\n";
        if (c.m_num_propagations)    out << "propagations: " << c.m_num_propagations << " ";
        if (c.m_max_watch.is_pos())  out << "max_watch: "    << c.max_watch() << " ";
        if (c.watch_size())          out << "watch size: "   << c.watch_size() << " ";
        if (c.m_watch_sum.is_pos())  out << "watch-sum: "    << c.watch_sum() << " ";
        if (!c.m_max_sum.is_zero())  out << "sum: [" << c.min_sum() << ":" << c.max_sum() << "] ";
        if (c.m_num_propagations || c.m_max_watch.is_pos() || c.watch_size() || 
            c.m_watch_sum.is_pos() || !c.m_max_sum.is_zero()) out << "\n";
        return out;
    }

    class theory_pb::pb_model_value_proc : public model_value_proc {
        app*              m_app;
        svector<model_value_dependency> m_dependencies;
    public:

        pb_model_value_proc(app* a): 
            m_app(a) {}

        void add(enode* n) { 
            m_dependencies.push_back(model_value_dependency(n)); 
        }

        virtual void get_dependencies(buffer<model_value_dependency> & result) {
            result.append(m_dependencies.size(), m_dependencies.c_ptr());
        }

        virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values) {
            ast_manager& m = mg.get_manager();
            SASSERT(values.size() == m_dependencies.size());
            SASSERT(values.size() == m_app->get_num_args());
            pb_util u(m);
            rational sum(0);
            for (unsigned i = 0; i < m_app->get_num_args(); ++i) {
                if (!m.is_true(values[i]) && !m.is_false(values[i])) {
                    return m_app;
                }
                if (m.is_true(values[i])) {
                    sum += u.get_coeff(m_app, i);
                }
            }
            rational k = u.get_k(m_app);
            switch(m_app->get_decl_kind()) {
            case OP_AT_MOST_K:
                return (sum <= k)?m.mk_true():m.mk_false();
            case OP_AT_LEAST_K:
                return (sum >= k)?m.mk_true():m.mk_false();
            case OP_PB_LE:
                return (sum <= k)?m.mk_true():m.mk_false();
            case OP_PB_GE:
                return (sum >= k)?m.mk_true():m.mk_false();
            default:
                UNREACHABLE();
                return 0;
            }
            return 0;
        }
    };

    class pb_factory : public value_factory {
    public:
        pb_factory(ast_manager& m, family_id fid):
            value_factory(m, fid) {}
        
        virtual expr * get_some_value(sort * s) {
            return m_manager.mk_true();
        }        
        virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
            v1 = m_manager.mk_true();
            v2 = m_manager.mk_false();
            return true;
        }        
        virtual expr * get_fresh_value(sort * s) {
            return 0;
        }
        virtual void register_value(expr * n) { }
    };

    void theory_pb::init_model(model_generator & m) {
        m.register_factory(alloc(pb_factory, get_manager(), get_id()));
    }

    model_value_proc * theory_pb::mk_value(enode * n, model_generator & mg) {
        context& ctx = get_context();
        app* a = n->get_owner();
        pb_model_value_proc* p = alloc(pb_model_value_proc, a);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            p->add(ctx.get_enode(a->get_arg(i)));
        }
        return p;
    }

    void theory_pb::display(std::ostream& out) const {
        u_map<ptr_vector<ineq>*>::iterator it = m_lwatch.begin(), end = m_lwatch.end();
        for (; it != end; ++it) {
            out << "watch: " << to_literal(it->m_key) << " |-> ";
            watch_list const& wl = *it->m_value;
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";
        }
        it = m_vwatch.begin(), end = m_vwatch.end();
        for (; it != end; ++it) {
            out << "watch (v): " << literal(it->m_key) << " |-> ";
            watch_list const& wl = *it->m_value;
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";
        }
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            ineq& c = *itc->m_value;
            display(out, c, true);
        }
    }


}
