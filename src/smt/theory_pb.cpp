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
#include "smt/theory_pb.h"
#include "smt/smt_context.h"
#include "smt/smt_kernel.h"
#include "ast/ast_pp.h"
#include "util/sorting_network.h"
#include "util/uint_set.h"
#include "smt/smt_model_generator.h"
#include "ast/rewriter/pb_rewriter_def.h"
#include "math/simplex/sparse_matrix_def.h"
#include "math/simplex/simplex_def.h"


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

    // -----------------------------
    // cardinality constraints

    void theory_pb::card::negate() {
        m_lit.neg();
        unsigned sz = size();
        for (unsigned i = 0; i < sz; ++i) {
            m_args[i].neg();
        }
        m_bound = sz - m_bound + 1;
        SASSERT(sz >= m_bound && m_bound > 0);
    }

    app_ref theory_pb::card::to_expr(theory_pb& th) {
        ast_manager& m = th.get_manager();
        expr_ref_vector args(m);
        for (unsigned i = 0; i < size(); ++i) {
            args.push_back(th.literal2expr(m_args[i]));
        }
        return app_ref(th.pb.mk_at_least_k(args.size(), args.c_ptr(), k()), m);        
    }

    lbool theory_pb::card::assign(theory_pb& th, literal alit) {
        // literal is assigned to false.        
        context& ctx = th.get_context();
        unsigned sz = size();
        unsigned bound = k();
        TRACE("pb", tout << "assign: " << m_lit << " " << ~alit << " " << bound << "\n";);

        SASSERT(0 < bound && bound < sz);
        SASSERT(ctx.get_assignment(alit) == l_false);
        SASSERT(ctx.get_assignment(m_lit) == l_true);
        unsigned index = 0;
        for (index = 0; index <= bound; ++index) {
            if (lit(index) == alit) {
                break;
            }
        }
        if (index == bound + 1) {
            // literal is no longer watched.
            return l_undef;
        }
        SASSERT(index <= bound);
        SASSERT(lit(index) == alit);
        
        // find a literal to swap with:
        for (unsigned i = bound + 1; i < sz; ++i) {
            literal lit2 = lit(i);
            if (ctx.get_assignment(lit2) != l_false) {
                TRACE("pb", tout << "swap " << lit2 << "\n";);
                std::swap(m_args[index], m_args[i]);
                th.watch_literal(lit2, this);
                return l_undef;
            }
        }

        // conflict
        if (bound != index && ctx.get_assignment(lit(bound)) == l_false) {
            TRACE("pb", tout << "conflict " << lit(bound) << " " << alit << "\n";);
            set_conflict(th, alit);
            return l_false;
        }

        TRACE("pb", tout << "no swap " << index << " " << alit << "\n";);
        // there are no literals to swap with,
        // prepare for unit propagation by swapping the false literal into 
        // position bound. Then literals in positions 0..bound-1 have to be
        // assigned l_true.
        if (index != bound) {
            std::swap(m_args[index], m_args[bound]);
        }
        SASSERT(th.validate_unit_propagation(*this));
        
        for (unsigned i = 0; i < bound && !ctx.inconsistent(); ++i) {
            th.add_assign(*this, lit(i));
        }

        return ctx.inconsistent() ? l_false : l_true;
    }

    /**
       \brief The conflict clause position for cardinality constraint have the following properties:
       0. The position for the literal corresponding to the cardinality constraint.
       1. The literal at position 0 of the cardinality constraint.
       2. The asserting literal.
       3. .. the remaining false literals.
     */
    
    void theory_pb::card::set_conflict(theory_pb& th, literal l) {
        SASSERT(validate_conflict(th));
        context& ctx = th.get_context();
        (void)ctx;
        literal_vector& lits = th.get_literals();
        SASSERT(ctx.get_assignment(l) == l_false);
        SASSERT(ctx.get_assignment(lit()) == l_true);
        lits.push_back(~lit()); 
        lits.push_back(l);
        unsigned sz = size();
        for (unsigned i = m_bound; i < sz; ++i) {
            SASSERT(ctx.get_assignment(m_args[i]) == l_false);
            lits.push_back(m_args[i]);
        }
        th.add_clause(*this, lits);        
    }

    bool theory_pb::card::validate_conflict(theory_pb& th) {
        context& ctx = th.get_context();
        unsigned num_false = 0;
        for (unsigned i = 0; i < size(); ++i) {
            if (ctx.get_assignment(m_args[i]) == l_false) {
                ++num_false;
            }
        }
        return size() - num_false < m_bound;
    }

    bool theory_pb::card::validate_assign(theory_pb& th, literal_vector const& lits, literal l) {
        context& ctx = th.get_context();
        VERIFY(ctx.get_assignment(l) == l_undef);
        for (unsigned i = 0; i < lits.size(); ++i) {
            SASSERT(ctx.get_assignment(lits[i]) == l_true);
        }
        return size() - lits.size() <= m_bound;
    }

    void theory_pb::card::init_watch(theory_pb& th, bool is_true) {
        context& ctx = th.get_context();
        th.clear_watch(*this);
        if (lit().sign() == is_true) {
            negate();
        }
        SASSERT(ctx.get_assignment(lit()) == l_true);
        unsigned j = 0, sz = size(), bound = k();
        if (bound == sz) {
            for (unsigned i = 0; i < sz && !ctx.inconsistent(); ++i) {
                th.add_assign(*this, lit(i));                
            }
            return;
        }
        // put the non-false literals into the head.
        for (unsigned i = 0; i < sz; ++i) {
            if (ctx.get_assignment(lit(i)) != l_false) {
                if (j != i) {
                    std::swap(m_args[i], m_args[j]);                 
                }
                ++j;
            }
        }
        DEBUG_CODE(
            bool is_false = false;
            for (unsigned k = 0; k < sz; ++k) {
                SASSERT(!is_false || ctx.get_assignment(lit(k)) == l_false);
                is_false = ctx.get_assignment(lit(k)) == l_false;
            });

        // j is the number of non-false, sz - j the number of false.
        if (j < bound) {
            SASSERT(0 < bound && bound < sz);
            literal alit = lit(j);
            
            //
            // we need the assignment level of the asserting literal to be maximal.
            // such that conflict resolution can use the asserting literal as a starting
            // point.
            //

            for (unsigned i = bound; i < sz; ++i) {                
                if (ctx.get_assign_level(alit) < ctx.get_assign_level(lit(i))) {
                    std::swap(m_args[j], m_args[i]);
                    alit = lit(j);
                }
            }
            set_conflict(th, alit);
        }
        else if (j == bound) {
            for (unsigned i = 0; i < bound && !ctx.inconsistent(); ++i) {
                th.add_assign(*this, lit(i));                
            }
        }
        else {
            for (unsigned i = 0; i <= bound; ++i) {
                th.watch_literal(lit(i), this);
            }
        }
    }


    void theory_pb::card::add_arg(literal lit) {
        if (lit == false_literal) {
            return;
        }
        else if (lit == true_literal) {
            if (m_bound > 0) {
                --m_bound;
            }
        }
        else {
            m_args.push_back(lit);
        }

    }

    void theory_pb::card::inc_propagations(theory_pb& th) {
        ++m_num_propagations;
    }

    // ------------------------
    // theory_pb

    theory_pb::theory_pb(ast_manager& m, theory_pb_params& p):
        theory(m.mk_family_id("pb")),
        m_params(p),
        pb(m),
        m_restart_lim(3),
        m_restart_inc(0),
        m_antecedent_exprs(m),
        m_cardinality_exprs(m)
    {        
        m_learn_complements  = p.m_pb_learn_complements;
        m_conflict_frequency = p.m_pb_conflict_frequency;
    }

    theory_pb::~theory_pb() {
        reset_eh();
    }

    theory * theory_pb::mk_fresh(context * new_ctx) { 
        return alloc(theory_pb, new_ctx->get_manager(), m_params); 
    }

    bool theory_pb::internalize_atom(app * atom, bool gate_ctx) {
        context& ctx = get_context();
        ast_manager& m = get_manager();

        if (ctx.b_internalized(atom)) {
            return true;
        }
        SASSERT(!ctx.b_internalized(atom));
        m_stats.m_num_predicates++;

        if (pb.is_aux_bool(atom)) {
            bool_var abv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(abv, get_id());
            return true;
        }

        if (internalize_card(atom, gate_ctx)) {
            return true;
        }

        SASSERT(pb.is_at_most_k(atom) || pb.is_le(atom) || 
                pb.is_ge(atom) || pb.is_at_least_k(atom) || 
                pb.is_eq(atom));


        unsigned num_args = atom->get_num_args();
        bool_var abv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(abv, get_id());
        literal lit(abv);

        if (pb.is_eq(atom)) {
            expr_ref_vector args(m), nargs(m);
            vector<rational> coeffs;
            rational sum(0);
            for (unsigned i = 0; i < num_args; ++i) {
                args.push_back(atom->get_arg(i));
                nargs.push_back(::mk_not(m, atom->get_arg(i)));
                rational c = pb.get_coeff(atom, i);
                coeffs.push_back(c);
                sum += c;
            }
            rational k = pb.get_k(atom);
            // ax + by + cz <= k
            // <=>
            // -ax - by - cz >= -k
            // <=>
            // a(1-x) + b(1-y) + c(1-z) >= a + b + c - k
            expr_ref le(pb.mk_ge(num_args, coeffs.c_ptr(), nargs.c_ptr(), sum - k), m);
            expr_ref ge(pb.mk_ge(num_args, coeffs.c_ptr(), args.c_ptr(), k), m);
            ctx.internalize(le, false);
            ctx.internalize(ge, false);
            literal le_lit = ctx.get_literal(le);
            literal ge_lit = ctx.get_literal(ge);
            ctx.mark_as_relevant(le_lit);
            ctx.mark_as_relevant(ge_lit);
            ctx.mk_th_axiom(get_id(), ~lit, le_lit);
            ctx.mk_th_axiom(get_id(), ~lit, ge_lit);
            ctx.mk_th_axiom(get_id(), ~le_lit, ~ge_lit, lit);
            return true;
        }

        ineq* c = alloc(ineq, m_mpz_mgr, literal(abv), pb.is_eq(atom));
        c->m_args[0].m_k = pb.get_k(atom);
        numeral& k = c->m_args[0].m_k;
        arg_t& args = c->m_args[0];

        // extract literals and coefficients.
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            literal l = compile_arg(arg);
            numeral c = pb.get_coeff(atom, i);
            switch (ctx.get_assignment(l)) {
            case l_true: 
                k -= c;
                break;
            case l_false:
                break;
            default:
                args.push_back(std::make_pair(l, c));
                break;
            }
        }

        if (pb.is_at_most_k(atom) || pb.is_le(atom)) {
            k = -k;
            for (auto& a : args) {
                a.first.neg();
                k += a.second;
            }
        }
        c->unique();
        lbool is_true = c->normalize();
        c->prune();
        c->post_prune();

        TRACE("pb", display(tout, *c); tout << " := " << lit << " " << is_true << "\n";);        
        switch (is_true) {
        case l_false: 
            lit.neg();
            // fall-through
        case l_true: 
            ctx.mk_th_axiom(get_id(), 1, &lit);
            dealloc(c);
            return true;
        case l_undef: 
            break;
        }
            
        if (c->k().is_one() && c->is_ge()) {
            literal_vector& lits = get_literals();
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
        for (auto const& a : args) {
            mpz const& num = a.second.to_mpq().numerator();
            if (m_mpz_mgr.lt(max_watch, num)) {
                max_watch = num;
            }
        }

        init_watch_ineq(*c);
        init_watch(abv);
        m_var_infos[abv].m_ineq = c;
        m_ineqs_trail.push_back(abv);
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

    void theory_pb::del_watch(ineq_watch& watch, unsigned index, ineq& c, unsigned ineq_index) {
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

    void theory_pb::init_watch(bool_var v) {
        if (m_var_infos.size() <= static_cast<unsigned>(v)) {
            m_var_infos.resize(static_cast<unsigned>(v)+100);
        }
    }

    void theory_pb::watch_literal(literal lit, ineq* c) {
        init_watch(lit.var());
        ptr_vector<ineq>* ineqs = m_var_infos[lit.var()].m_lit_watch[lit.sign()];
        if (ineqs == nullptr) {
            ineqs = alloc(ptr_vector<ineq>);
            m_var_infos[lit.var()].m_lit_watch[lit.sign()] = ineqs;
        }
        DEBUG_CODE(
            for (auto* c1 : *ineqs) {
                //if (c1 == c) return;
                SASSERT (c1 != c);
            });
        ineqs->push_back(c);
    }

    void theory_pb::unwatch_literal(literal lit, ineq* c) {
        ptr_vector<ineq>* ineqs = m_var_infos[lit.var()].m_lit_watch[lit.sign()];
        if (ineqs) {
            remove(*ineqs, c);        
        }
    }

    void theory_pb::remove(ptr_vector<ineq>& ineqs, ineq* c) {
        unsigned sz = ineqs.size();
        for (unsigned j = 0; j < sz; ++j) {
            if (ineqs[j] == c) {                        
                std::swap(ineqs[j], ineqs[sz-1]);
                ineqs.pop_back();
                return;
            }
        }   
    }

    // ----------------------------
    // cardinality constraints


    class theory_pb::card_justification : public justification {
        card& m_card;
        family_id m_fid;
        literal m_lit;
    public:
        card_justification(card& c, literal lit, family_id fid)
            : justification(true), m_card(c), m_fid(fid), m_lit(lit) {}

        card& get_card() { return m_card; }

        void get_antecedents(conflict_resolution& cr) override {
            cr.mark_literal(m_card.lit());
            for (unsigned i = m_card.k(); i < m_card.size(); ++i) {
                cr.mark_literal(~m_card.lit(i));
            }
        }

        theory_id get_from_theory() const override {
            return m_fid;
        }
        
        proof* mk_proof(smt::conflict_resolution& cr) override {
            ptr_buffer<proof> prs;
            ast_manager& m = cr.get_context().get_manager(); 
            expr_ref fact(m);
            cr.get_context().literal2expr(m_lit, fact);
            bool all_valid = true;
            proof* pr = nullptr;
            pr = cr.get_proof(m_card.lit());
            all_valid &= pr != nullptr;
            prs.push_back(pr);
            for (unsigned i = m_card.k(); i < m_card.size(); ++i) {
                pr = cr.get_proof(~m_card.lit(i));
                all_valid &= pr != nullptr;
                prs.push_back(pr);
            }
            if (!all_valid) {
                return nullptr;
            }
            else {
                return m.mk_th_lemma(m_fid, fact, prs.size(), prs.c_ptr());
            }
        }
    };


    bool theory_pb::is_cardinality_constraint(app * atom) {
        if (pb.is_ge(atom) && pb.has_unit_coefficients(atom)) {
            return true;
        }
        if (pb.is_at_least_k(atom)) {
            return true;
        }
        return false;
    }

    bool theory_pb::internalize_card(app * atom, bool gate_ctx) {
        context& ctx = get_context();
        if (ctx.b_internalized(atom)) {
            return true;
        }
        if (!is_cardinality_constraint(atom)) {
            return false;
        }       
        unsigned num_args = atom->get_num_args();
        bool_var abv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(abv, get_id());
        unsigned bound = pb.get_k(atom).get_unsigned();
        literal lit(abv);

        if (bound == 0) {
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return true;
        }
        if (bound > num_args) {
            lit.neg();
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return true;
        }
        
        // hack to differentiate constraints that come from input vs. lemmas.
        bool aux = pb.is_at_least_k(atom);

        card* c = alloc(card, lit, bound, aux);
        
        for (expr* arg : *atom) {
            c->add_arg(compile_arg(arg));
        }

        if (bound == c->size() || bound == 1) {
            //
        }
        
        if (bound == c->size()) {
            card2conjunction(*c);
            dealloc(c);
        }
        else if (1 == c->size()) {
            card2disjunction(*c);
            dealloc(c);
        }
        else {
            SASSERT(0 < c->k() && c->k() < c->size());            
            // initialize compilation thresholds, TBD                        
            init_watch(abv);
            m_var_infos[abv].m_card = c;
            m_card_trail.push_back(abv);
        }
        return true;
    }

    // \brief define cardinality constraint as conjunction.
    // 
    void theory_pb::card2conjunction(card const& c) {
        context& ctx = get_context();
        literal lit = c.lit();
        literal_vector& lits = get_literals();
        for (unsigned i = 0; i < c.size(); ++i) {
            lits.push_back(~c.lit(i));
        }
        lits.push_back(lit);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lits2[2] = { ~lit, c.lit(i) };
            ctx.mk_th_axiom(get_id(), 2, lits2);
        }
    }

    void theory_pb::card2disjunction(card const& c) {
        context& ctx = get_context();
        literal lit = c.lit();
        literal_vector& lits = get_literals();
        for (unsigned i = 0; i < c.size(); ++i) {
            lits.push_back(c.lit(i));
        }
        lits.push_back(~lit);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lits2[2] = { lit, ~c.lit(i) };
            ctx.mk_th_axiom(get_id(), 2, lits2);
        }
    }

    void theory_pb::watch_literal(literal lit, card* c) {
        init_watch(lit.var());
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_lit_cwatch[lit.sign()];
        if (cards == nullptr) {
            cards = alloc(ptr_vector<card>);
            m_var_infos[lit.var()].m_lit_cwatch[lit.sign()] = cards;
        }
        cards->push_back(c);
    }


    void theory_pb::unwatch_literal(literal lit, card* c) {
        if (m_var_infos.size() <= static_cast<unsigned>(lit.var())) {
            return;
        }
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_lit_cwatch[lit.sign()];
        if (cards) {
            remove(*cards, c);        
        }
    }

    void theory_pb::remove(ptr_vector<card>& cards, card* c) {
        for (unsigned j = 0; j < cards.size(); ++j) {
            if (cards[j] == c) {                        
                std::swap(cards[j], cards[cards.size()-1]);
                cards.pop_back();
                break;
            }
        }
    }

    std::ostream& theory_pb::display(std::ostream& out, card const& c, bool values) const {
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
            ctx.display_literal_verbose(out, c.lit()); out << "\n";
        }
        else {
            out << " ";
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.lit(i);
            out << l;
            if (values) {
                out << "@(" << ctx.get_assignment(l);
                if (ctx.get_assignment(l) != l_undef) {
                    out << ":" << ctx.get_assign_level(l);
                }
                out << ") ";
            }
        }
        out << " >= " << c.k()  << "\n";
        if (c.all_propagations())    out << "propagations: " << c.all_propagations() << "\n";
        return out;
    }

                   
    void theory_pb::add_clause(card& c, literal_vector const& lits) {
        m_stats.m_num_conflicts++;
        context& ctx = get_context();
        justification* js = nullptr;
        c.inc_propagations(*this);
        if (!resolve_conflict(c, lits)) {
            if (proofs_enabled()) {
                js = alloc(theory_lemma_justification, get_id(), ctx, lits.size(), lits.c_ptr());
            }
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_TH_LEMMA, nullptr);
        }
        SASSERT(ctx.inconsistent());
    }

    void theory_pb::add_assign(card& c, literal l) {        
        context& ctx = get_context();
        if (ctx.get_assignment(l) == l_true) {
            return;
        }
        c.inc_propagations(*this);
        m_stats.m_num_propagations++;
        TRACE("pb", tout << "#prop: " << c.num_propagations() << " - " << c.lit() << " => " << l << "\n";);
        SASSERT(validate_unit_propagation(c));
        ctx.assign(l, ctx.mk_justification(card_justification(c, l, get_id())));
    }

    void theory_pb::clear_watch(card& c) {
        unsigned sz = std::min(c.k() + 1, c.size());
        for (unsigned i = 0; i < sz; ++i) {
            unwatch_literal(c.lit(i), &c);            
        }
    }

    // 

    void theory_pb::collect_statistics(::statistics& st) const {
        st.update("pb conflicts", m_stats.m_num_conflicts);
        st.update("pb propagations", m_stats.m_num_propagations);
        st.update("pb predicates", m_stats.m_num_predicates);        
    }
    
    void theory_pb::reset_eh() {
        
        for (unsigned i = 0; i < m_var_infos.size(); ++i) {
            m_var_infos[i].reset();
        }
        m_ineqs_trail.reset();
        m_ineqs_lim.reset();
        m_card_trail.reset();
        m_card_lim.reset();
        m_stats.reset();
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
        ptr_vector<ineq>* ineqs = nullptr;
        context& ctx = get_context();
        literal nlit(v, is_true);
        init_watch(v);
        TRACE("pb", tout << "assign: " << ~nlit << "\n";);
        ineqs = m_var_infos[v].m_lit_watch[nlit.sign()];
        if (ineqs != nullptr) {
            for (unsigned i = 0; i < ineqs->size(); ++i) {
                SASSERT((*ineqs)[i]->is_ge());
                if (assign_watch_ge(v, is_true, *ineqs, i)) {
                    // i was removed from watch list.
                    --i;
                }
            }
        }
        ineq* c = m_var_infos[v].m_ineq;
        if (c != nullptr) {
            VERIFY(c->is_ge());
            assign_ineq(*c, is_true);
        }

        ptr_vector<card>* cards = m_var_infos[v].m_lit_cwatch[nlit.sign()];
        if (cards != nullptr  && !cards->empty() && !ctx.inconsistent())  {
            ptr_vector<card>::iterator it = cards->begin(), it2 = it, end = cards->end();
            for (; it != end; ++it) {
                if (ctx.get_assignment((*it)->lit()) != l_true) {
                    continue;
                }
                switch ((*it)->assign(*this, nlit)) {
                case l_false: // conflict
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    SASSERT(ctx.inconsistent());
                    cards->set_end(it2);
                    return;
                case l_undef: // watch literal was swapped
                    break;
                case l_true: // unit propagation, keep watching the literal
                    if (it2 != it) {
                        *it2 = *it;
                    }
                    ++it2;
                    break;
                }
            }
            cards->set_end(it2);
        }

        card* crd = m_var_infos[v].m_card;
        if (crd != nullptr && !ctx.inconsistent()) {
            crd->init_watch(*this, is_true);
        }

    }

    literal_vector& theory_pb::get_all_literals(ineq& c, bool negate) {
        context& ctx = get_context();
        literal_vector& lits = get_literals();
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
        literal_vector& lits = get_literals();
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
        literal_vector& lits = get_literals();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.lit(i);
            if (ctx.get_assignment(l) == l_false) {
                if (negate) l = ~l;
                lits.push_back(l);
            }
        }
        return lits;
    }

    class theory_pb::negate_ineq : public trail<context> {
        ineq& c;
    public:
        negate_ineq(ineq& c): c(c) {}
        void undo(context& ctx) override {
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
            // for (literal lit : lits) SASSERT(ctx.get_assignment(lit) == l_true);
            lits.push_back(c.lit());
            // SASSERT(ctx.get_assignment(c.lit()) == l_true);
            for (unsigned i = 0; i < sz; ++i) {
                literal lit = c.lit(i);
                if (ctx.get_assignment(lit) == l_undef) {
                    DEBUG_CODE(validate_assign(c, lits, lit););
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
        UNREACHABLE();
    }


    /**
       \brief v is assigned in inequality c. Update current bounds and watch list.
       Optimize for case where the c.lit() is True. This covers the case where 
       inequalities are unit literals and formulas in negation normal form 
       (inequalities are closed under negation).       
     */
    bool theory_pb::assign_watch_ge(bool_var v, bool is_true, ineq_watch& watch, unsigned watch_index) {
        bool removed = false;
        context& ctx = get_context();
        ineq& c = *watch[watch_index];
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
        typedef smt::literal pliteral;
        typedef smt::literal_vector pliteral_vector;
      
        psort_expr(context& c, theory_pb& th):
            ctx(c), 
            m(c.get_manager()),
            th(th),
            pb(m) {}

        literal fresh(char const* ) {
            app_ref y(m);
            y = pb.mk_fresh_bool();
            return literal(ctx.mk_bool_var(y));
        }
        
        literal mk_max(unsigned n, literal const* lits) {
            expr_ref_vector es(m);
            expr_ref tmp(m);            
            for (unsigned i = 0; i < n; ++i) {
                ctx.literal2expr(lits[i], tmp);
                es.push_back(tmp);
            }
            tmp = m.mk_or(es.size(), es.c_ptr());
            bool_var v = ctx.b_internalized(tmp)?ctx.get_bool_var(tmp):ctx.mk_bool_var(tmp);
            return literal(v);
        }
        
        literal mk_min(unsigned n, literal const* lits) {
            expr_ref_vector es(m);
            expr_ref tmp(m);            
            for (unsigned i = 0; i < n; ++i) {
                ctx.literal2expr(lits[i], tmp);
                es.push_back(tmp);
            }
            tmp = m.mk_and(es.size(), es.c_ptr());
            bool_var v = ctx.b_internalized(tmp)?ctx.get_bool_var(tmp):ctx.mk_bool_var(tmp);
            return literal(v);
        }

        literal mk_not(literal a) { return ~a; }

        void mk_clause(unsigned n, literal const* ls) {
            literal_vector tmp(n, ls);
            ctx.mk_clause(n, tmp.c_ptr(), th.justify(tmp), CLS_AUX, nullptr);
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
    }

    void theory_pb::restart_eh() {
    }

    bool theory_pb::gc() {

        context& ctx = get_context();

        unsigned z = 0, nz = 0;
        m_occs.reset();
        for (unsigned i = 0; i < m_card_trail.size(); ++i) {
            bool_var v = m_card_trail[i];
            if (v == null_bool_var) continue;
            card* c = m_var_infos[v].m_card;
            if (c) {
                c->reset_propagations();
                literal lit = c->lit();
                if (c->is_aux() && ctx.get_assign_level(lit) > ctx.get_search_level()) {
                    double activity = ctx.get_activity(v);
                    if (activity <= 0) {
                        nz++;
                    }
                    else {
                        z++;
                        clear_watch(*c);
                        m_var_infos[v].m_card = nullptr;
                        dealloc(c);
                        m_card_trail[i] = null_bool_var;
                        ctx.remove_watch(v);
                        // TBD: maybe v was used in a clause for propagation.
                        m_occs.insert(v);
                    }
                }
            }
        }
        clause_vector const& lemmas = ctx.get_lemmas();
        for (unsigned i = 0; i < lemmas.size(); ++i) {
            clause* cl = lemmas[i];
            if (!cl->deleted()) {
                for (literal lit : *cl) {
                    if (m_occs.contains(lit.var())) {
                        break;
                    }
                }
            }
        }

        //std::cout << "zs: " << z << " nzs: " << nz << " lemmas: " << ctx.get_lemmas().size() << " trail: " << m_card_trail.size() << "\n";
        return z*10 >= nz;

        m_occs.reset();
        for (unsigned i = 0; i < lemmas.size(); ++i) {
            clause* cl = lemmas[i];
            unsigned sz = cl->get_num_literals();
            for (unsigned j = 0; j < sz; ++j) {
                unsigned idx = cl->get_literal(j).index();
                m_occs.insert(idx);
            }
        }
    }


    void theory_pb::init_search_eh() {
    }

    void theory_pb::push_scope_eh() {
        m_ineqs_lim.push_back(m_ineqs_trail.size());
        m_card_lim.push_back(m_card_trail.size());
    }

    void theory_pb::pop_scope_eh(unsigned num_scopes) {

        // remove inequalities.
        unsigned new_lim = m_ineqs_lim.size()-num_scopes;
        unsigned sz = m_ineqs_lim[new_lim];
        while (m_ineqs_trail.size() > sz) {
            bool_var v = m_ineqs_trail.back();
            ineq* c = m_var_infos[v].m_ineq;
            clear_watch(*c);
            m_var_infos[v].m_ineq = nullptr;
            m_ineqs_trail.pop_back();
            dealloc(c);
        }
        m_ineqs_lim.resize(new_lim);


        new_lim = m_card_lim.size() - num_scopes;
        sz = m_card_lim[new_lim];
        while (m_card_trail.size() > sz) {
            bool_var v = m_card_trail.back();
            m_card_trail.pop_back();
            if (v != null_bool_var) {
                card* c = m_var_infos[v].m_card;
                clear_watch(*c);
                m_var_infos[v].m_card = nullptr;
                dealloc(c);
            }
        }

        m_card_lim.resize(new_lim);
    }

    void theory_pb::clear_watch(ineq& c) {
        for (unsigned i = 0; i < c.size(); ++i) {
            literal w = c.lit(i);
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
        
        void undo(context& ctx) override {
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

    void theory_pb::init_watch_ineq(ineq& c) {
        c.m_min_sum.reset();
        c.m_max_sum.reset();
        c.m_nfixed = 0;
        c.m_watch_sum.reset();
        c.m_max_watch.reset();
        c.m_watch_sz = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            c.m_max_sum += c.ncoeff(i);
        }                   
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
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - " << lits;
              tout << " => " << l << "\n";
              display(tout, c, true););

        SASSERT(validate_antecedents(lits));
        ctx.assign(l, ctx.mk_justification(
                       pb_justification(
                           c, get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), l)));
    }
    


    void theory_pb::add_clause(ineq& c, literal_vector const& lits) {
        inc_propagations(c);
        m_stats.m_num_conflicts++;
        context& ctx = get_context();
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - " << lits << "\n"; 
              display(tout, c, true);); 
        justification* js = nullptr;
        if (proofs_enabled()) {                                         
            js = alloc(theory_lemma_justification, get_id(), ctx, lits.size(), lits.c_ptr());
        }
        ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_TH_LEMMA, nullptr);
    }


    int theory_pb::get_coeff(bool_var v) const { 
        return m_coeffs.get(v, 0); 
    }

    int theory_pb::get_abs_coeff(bool_var v) const { 
        int coeff = get_coeff(v);
        if (coeff < 0) coeff = -coeff;
        return coeff;
    }

    void theory_pb::reset_coeffs() {
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            m_coeffs[m_active_vars[i]] = 0;
        }
        m_active_vars.reset();
    }

    void theory_pb::process_antecedent(literal l, int offset) {        
        context& ctx = get_context();
        SASSERT(ctx.get_assignment(l) == l_false);
        bool_var v = l.var();
        unsigned lvl = ctx.get_assign_level(v);

        if (lvl > ctx.get_base_level() && !ctx.is_marked(v) && lvl == m_conflict_lvl) {
            ctx.set_mark(v);
            ++m_num_marks;
        }
        inc_coeff(l, offset);                
    }

    void theory_pb::process_card(card& c, int offset) {
        context& ctx = get_context();
        SASSERT(c.k() <= c.size());
        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            process_antecedent(c.lit(i), offset);
        }
        for (unsigned i = 0; i < c.k(); ++i) {
            inc_coeff(c.lit(i), offset);                        
        }
        if (ctx.get_assign_level(c.lit()) > ctx.get_base_level()) {
            m_antecedents.push_back(c.lit());
        }
    }

    bool theory_pb::validate_lemma() {
        int value = -m_bound;
        context& ctx = get_context();
        normalize_active_coeffs();
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            int coeff = get_coeff(v);
            SASSERT(coeff != 0);
            if (coeff < 0 && ctx.get_assignment(v) != l_true) {
                value -= coeff;
            }
            else if (coeff > 0 && ctx.get_assignment(v) != l_false) {
                value += coeff;
            }
        }
        // std::cout << "bound: " << m_bound << " value " << value << " coeffs: " << m_active_vars.size() << " lemma is " << (value >= 0 ? "sat" : "unsat") << "\n";    
        return value < 0;
    }

    bool theory_pb::validate_implies(app_ref& A, app_ref& B) {       
        static bool validating = true; // false;
        if (validating) return true;
        validating = true;
        ast_manager& m = get_manager();
        smt_params fp;
        kernel k(m, fp);
        expr_ref notB(m.mk_not(B), m);
        k.assert_expr(A);
        k.assert_expr(notB);
        lbool is_sat = k.check();
        validating = false;
        // std::cout << is_sat << "\n";
        if (is_sat == l_true) {
            std::cout << A << "\n";
            std::cout << B << "\n";
        }
        SASSERT(is_sat != l_true);
        return true;
    }

    app_ref theory_pb::justification2expr(b_justification& js, literal conseq) {
        ast_manager& m = get_manager();
        app_ref result(m.mk_true(), m);
        expr_ref_vector args(m);
        vector<rational> coeffs;
        switch(js.get_kind()) {
            
        case b_justification::CLAUSE: {
            clause& cls = *js.get_clause();
            justification* cjs = cls.get_justification();
            if (cjs && !is_proof_justification(*cjs)) {
                break;
            }
            for (unsigned i = 0; i < cls.get_num_literals(); ++i) {
                literal lit = cls.get_literal(i);
                args.push_back(literal2expr(lit));
            }
            result = m.mk_or(args.size(), args.c_ptr());
            break;
        }
        case b_justification::BIN_CLAUSE:
            result = m.mk_or(literal2expr(conseq), literal2expr(~js.get_literal()));
            break;
        case b_justification::AXIOM:
            break;
        case b_justification::JUSTIFICATION: {
            justification* j = js.get_justification(); 
            card_justification* pbj = nullptr;
            if (j->get_from_theory() == get_id()) {
                pbj = dynamic_cast<card_justification*>(j);
            }
            if (pbj != nullptr) {
                card& c2 = pbj->get_card();
                result = card2expr(c2);
            }            
            break;
        }
        default:
            break;
        }
        return result;
    }

    int theory_pb::arg_max(int& max_coeff) {
        max_coeff = 0;
        int arg_max = -1;
        while (!m_active_coeffs.empty()) {
            max_coeff = m_active_coeffs.back();
            if (m_coeff2args[max_coeff].empty()) {
                m_active_coeffs.pop_back();
            }
            else {
                arg_max = m_coeff2args[max_coeff].back();
                m_coeff2args[max_coeff].pop_back();
                break;
            }
        }
        return arg_max;
    }

    literal theory_pb::get_asserting_literal(literal p) {
        if (get_abs_coeff(p.var()) != 0) {
            return p;
        }
        context& ctx = get_context();
        unsigned lvl = 0;
        
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            literal lit(v, get_coeff(v) < 0);
            if (ctx.get_assignment(lit) == l_false && ctx.get_assign_level(lit) > lvl) {
                p = lit;
            }
        }

        return p;
    }

    void theory_pb::reset_arg_max() {
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            int coeff = get_abs_coeff(m_active_vars[i]);
            if (static_cast<int>(m_coeff2args.size()) > coeff) {
                m_coeff2args[coeff].reset();
            }
        }
    }

    bool theory_pb::init_arg_max() {
        if (m_coeff2args.size() < (1 << 10)) {
            m_coeff2args.resize(1 << 10);
        }
        m_active_coeffs.reset();
        if (m_active_vars.empty()) {
            return false;
        }
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            int coeff = get_abs_coeff(v);
            if (coeff >= static_cast<int>(m_coeff2args.size())) {
                reset_arg_max();
                return false;
            }
            if (m_coeff2args[coeff].empty()) {
                m_active_coeffs.push_back(coeff);
            }
            m_coeff2args[coeff].push_back(v);
        }
        std::sort(m_active_coeffs.begin(), m_active_coeffs.end());
        return true;
    }

    void theory_pb::normalize_active_coeffs() {
        while (!m_active_var_set.empty()) m_active_var_set.erase();
        unsigned i = 0, j = 0, sz = m_active_vars.size();
        for (; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            if (!m_active_var_set.contains(v) && get_coeff(v) != 0) {
                m_active_var_set.insert(v);
                if (j != i) {
                    m_active_vars[j] = m_active_vars[i];
                }
                ++j;
            }
        }
        sz = j;
        m_active_vars.shrink(sz);
    }

    void theory_pb::inc_coeff(literal l, int offset) {        
        SASSERT(offset > 0);
        bool_var v = l.var();
        SASSERT(v != null_bool_var);
        if (static_cast<bool_var>(m_coeffs.size()) <= v) {
            m_coeffs.resize(v + 1, 0);
        }
        int coeff0 = m_coeffs[v];
        if (coeff0 == 0) {
            m_active_vars.push_back(v);
        }
        
        int inc = l.sign() ? -offset : offset;
        int coeff1 = inc + coeff0;
        m_coeffs[v] = coeff1;

        if (coeff0 > 0 && inc < 0) {
            m_bound -= coeff0 - std::max(0, coeff1);
        }
        else if (coeff0 < 0 && inc > 0) {
            m_bound -= std::min(0, coeff1) - coeff0;
        }
    }

    /**
       \brief attempt a cut and simplification of constraints.
     */
    void theory_pb::cut() {
        unsigned g = 0;
        for (unsigned i = 0; g != 1 && i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            int coeff = get_abs_coeff(v);
            if (coeff == 0) {
                continue;
            }
            if (m_bound < coeff) {                
                if (get_coeff(v) > 0) {
                    m_coeffs[v] = m_bound;
                }
                else {
                    m_coeffs[v] = -m_bound;
                }
                coeff = m_bound;
            }
            SASSERT(0 < coeff && coeff <= m_bound);
            if (g == 0) {
                g = static_cast<unsigned>(coeff);
            }
            else {
                g = u_gcd(g, static_cast<unsigned>(coeff));
            }
        }
        if (g >= 2) {
            normalize_active_coeffs();
            for (unsigned i = 0; i < m_active_vars.size(); ++i) {
                m_coeffs[m_active_vars[i]] /= g;                
            }
            m_bound = (m_bound + g - 1) / g;
            TRACE("pb", display_resolved_lemma(tout << "cut\n"););
        }
    }

    bool theory_pb::can_propagate() { return false; }
    
    void theory_pb::propagate() { }

    bool theory_pb::resolve_conflict(card& c, literal_vector const& confl) {
       
        TRACE("pb", display(tout, c, true); );

        bool_var v;
        context& ctx = get_context();
        ast_manager& m = get_manager();
        m_conflict_lvl = 0;
        for (literal lit : confl) {
            SASSERT(ctx.get_assignment(lit) == l_false);
            m_conflict_lvl = std::max(m_conflict_lvl, ctx.get_assign_level(lit));            
        }
        if (m_conflict_lvl < ctx.get_assign_level(c.lit()) || m_conflict_lvl == ctx.get_base_level()) {
            return false;
        }

        reset_coeffs();
        m_num_marks = 0;
        m_bound = c.k();
        m_antecedents.reset();
        m_resolved.reset();
        literal_vector ante;

        process_card(c, 1);

        app_ref A(m), B(m), C(m);
        DEBUG_CODE(A = c.to_expr(*this););
        
        // point into stack of assigned literals
        literal_vector const& lits = ctx.assigned_literals();        
        SASSERT(!lits.empty());
        unsigned idx = lits.size()-1;
        b_justification js;
        literal conseq = ~confl[2];
        int bound = 1;

        while (m_num_marks > 0) {

            v = conseq.var();

            int offset = get_abs_coeff(v);

            if (offset == 0) {
                goto process_next_resolvent;            
            }
            SASSERT(validate_lemma());
            if (offset > 1000) {
                while (m_num_marks > 0 && idx > 0) {
                    v = lits[idx].var();
                    if (ctx.is_marked(v)) {
                        ctx.unset_mark(v);
                    }
                    --idx;
                }
                return false;
            }

            SASSERT(offset > 0);

            js = ctx.get_justification(v);

            TRACE("pb", 
                  display_resolved_lemma(tout << conseq << "\n");
                  ctx.display(tout, js););

            m_resolved.push_back(conseq);

            
            //
            // Resolve selected conseq with antecedents.
            // 
            
            bound = 1;

            switch(js.get_kind()) {
                
            case b_justification::CLAUSE: {
                inc_coeff(conseq, offset);
                clause& cls = *js.get_clause();
                justification* cjs = cls.get_justification();
                if (cjs && !is_proof_justification(*cjs)) {
                    TRACE("pb", tout << "skipping justification for clause over: " << conseq << " " 
                          << typeid(*cjs).name() << "\n";);
                    break;
                }
                unsigned num_lits = cls.get_num_literals();
                if (cls.get_literal(0) == conseq) {
                   process_antecedent(cls.get_literal(1), offset);
                }
                else {
                    SASSERT(cls.get_literal(1) == conseq);
                    process_antecedent(cls.get_literal(0), offset);
                }
                for (unsigned i = 2; i < num_lits; ++i) {
                    process_antecedent(cls.get_literal(i), offset);
                }
                TRACE("pb", tout << literal_vector(cls.get_num_literals(), cls.begin()) << "\n";);
                break;                
            }
            case b_justification::BIN_CLAUSE:
                inc_coeff(conseq, offset);
                process_antecedent(~js.get_literal(), offset);
                break;
            case b_justification::AXIOM:
                bound = 0;
                break;
            case b_justification::JUSTIFICATION: {
                justification* j = js.get_justification(); 
                card_justification* pbj = nullptr;

                if (j->get_from_theory() == get_id()) {
                    pbj = dynamic_cast<card_justification*>(j);
                }
                if (pbj == nullptr) {
                    TRACE("pb", tout << "skip justification for " << conseq << "\n";);
                    bound = 0;
                    // this is possible when conseq is an assumption.
                    // The justification of conseq is itself, 
                    // don't increment the cofficient here because it assumes
                    // conseq is justified further. it isnt'. conseq becomes part of the lemma.
                }
                else {
                    card& c2 = pbj->get_card();
                    process_card(c2, offset);
                    bound = c2.k();
                }
                
                break;
            }
            default:
                UNREACHABLE();
            }            
            m_bound += offset * bound;

            DEBUG_CODE(
                B = justification2expr(js, conseq);
                C = active2expr();
                B = m.mk_and(A, B);
                validate_implies(B, C);
                A = C;);

            cut();

        process_next_resolvent:

            // find the next marked variable in the assignment stack
            //
            while (true) {
                conseq = lits[idx];
                v = conseq.var();
                if (ctx.is_marked(v)) break;
                SASSERT(idx > 0);
                --idx;
            }

            SASSERT(ctx.get_assign_level(v) == m_conflict_lvl);
            ctx.unset_mark(v);
            --idx;
            --m_num_marks;
        }
        SASSERT(validate_lemma());

        TRACE("pb", display_resolved_lemma(tout << "done\n"););
        

        normalize_active_coeffs();

        if (m_bound > 0 && m_active_vars.empty()) {
            return false;
        }

        int slack = -m_bound;
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            slack += get_abs_coeff(v);
        }

        unsigned i = 0;
        literal_vector const& alits = ctx.assigned_literals();

        literal alit = get_asserting_literal(~conseq);
        slack -= get_abs_coeff(alit.var());

        for (i = alits.size(); 0 <= slack && i-- > 0; ) {
            literal lit = alits[i];
            bool_var v = lit.var();
            // -3*x >= k 
            if (m_active_var_set.contains(v) && v != alit.var()) {
                int coeff = get_coeff(v);
                if (coeff < 0 && !lit.sign()) {
                    slack += coeff;
                    m_antecedents.push_back(lit);
                }
                else if (coeff > 0 && lit.sign()) {
                    slack -= coeff;
                    m_antecedents.push_back(lit);
                }
            }
        }
        SASSERT(slack < 0);

        SASSERT(validate_antecedents(m_antecedents));
        TRACE("pb", tout << "antecedents " << m_antecedents << "\n";);
        ctx.assign(alit, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), m_antecedents.size(), m_antecedents.c_ptr(), alit, 0, nullptr)));

        DEBUG_CODE(
            m_antecedents.push_back(~alit);
            expr_ref_vector args(m);
            for (literal lit : m_antecedents) {
                args.push_back(literal2expr(lit));
            }
            B = m.mk_not(m.mk_and(args.size(), args.c_ptr()));
            validate_implies(A, B); );
        return true;
    }

    bool theory_pb::is_proof_justification(justification const& j) const {
        return typeid(smt::justification_proof_wrapper) == typeid(j);
    }

    justification* theory_pb::justify(literal l1, literal l2) {
        literal lits[2] = { l1, l2 };
        justification* js = nullptr;
        if (proofs_enabled()) {                                         
            js = get_context().mk_justification(theory_axiom_justification(get_id(), get_context().get_region(), 2, lits));
        }
        return js;
    }

    justification* theory_pb::justify(literal_vector const& lits) {
        justification* js = nullptr;
        if (proofs_enabled()) {                                         
            js = get_context().mk_justification(theory_axiom_justification(get_id(), get_context().get_region(), lits.size(), lits.c_ptr()));
        }
        return js;        
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
        for (literal lit : lits) {
            SASSERT(get_context().get_assignment(lit) == l_true);
            nlits.insert((~lit).index());
        }
        SASSERT(get_context().get_assignment(l) == l_undef);
        SASSERT(get_context().get_assignment(c.lit()) == l_true);
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
               for (literal lit : lits) tout << lit << " ";
               tout << " => " << l << "\n";);
        SASSERT(sum < c.k());
    }

    void theory_pb::validate_final_check() {
        TRACE("pb", tout << "validate " << m_var_infos.size() << "\n";);
        for (auto & vi : m_var_infos) {
            if (vi.m_ineq) {
                validate_final_check(*vi.m_ineq);
            }
            if (vi.m_card) {
                validate_final_check(*vi.m_card);
            }
        }
    }

    void theory_pb::validate_final_check(card& c) {
        context& ctx = get_context();
        if (ctx.get_assignment(c.lit()) == l_undef) {
            TRACE("pb", display(tout << "is undef ", c, true););
            return;
        }
        if (!ctx.is_relevant(c.lit())) {
            TRACE("pb", display(tout << "not relevant ", c, true););
            return;
        }

        unsigned sum = 0, maxsum = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            switch(ctx.get_assignment(c.lit(i))) {
            case l_true:
                ++sum;
            case l_undef:
                ++maxsum;
                break;
            case l_false:
                break;
            }
        }
        TRACE("pb_verbose", display(tout << "validate: ", c, true);
              tout << "sum: " << sum << " " << maxsum << " ";
              tout << ctx.get_assignment(c.lit()) << "\n";);

        SASSERT(sum <= maxsum);
        SASSERT((sum >= c.k()) == (ctx.get_assignment(c.lit()) == l_true));
        SASSERT((maxsum < c.k()) == (ctx.get_assignment(c.lit()) == l_false));        
    }

    void theory_pb::validate_final_check(ineq& c) {
        context& ctx = get_context();

        if (ctx.get_assignment(c.lit()) == l_undef) {
            TRACE("pb", tout << c.lit() << " is undef\n";);
            return;
        }
        if (!ctx.is_relevant(c.lit())) {
            TRACE("pb", tout << c.lit() << " is not relevant\n";);
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

    bool theory_pb::validate_antecedents(literal_vector const& lits) {
        context& ctx = get_context();
        for (literal lit : lits) {
            if (ctx.get_assignment(lit) != l_true) {
                return false;
            }
        }
        return true;
    }

    bool theory_pb::validate_unit_propagation(card const& c) {
        context& ctx = get_context();
        for (unsigned i = c.k(); i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) != l_false) {
                return false;
            }
        }
        return true;
    }

    app_ref theory_pb::literal2expr(literal lit) {
        ast_manager& m = get_manager();
        app_ref arg(m.mk_const(symbol(lit.var()), m.mk_bool_sort()), m);                
        return app_ref(lit.sign() ? m.mk_not(arg) : arg, m);
    }

    app_ref theory_pb::active2expr() {
        ast_manager& m = get_manager();
        expr_ref_vector args(m);
        vector<rational> coeffs;
        normalize_active_coeffs();
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            literal lit(v, get_coeff(v) < 0);
            args.push_back(literal2expr(lit));
            coeffs.push_back(rational(get_abs_coeff(v)));
        }
        rational k(m_bound);
        return app_ref(pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), k), m);
    }

    // display methods

    void theory_pb::display_resolved_lemma(std::ostream& out) const {
        context& ctx = get_context();
        out << "num marks: " << m_num_marks << "\n";
        out << "conflict level: " << m_conflict_lvl << "\n";
        for (literal r : m_resolved) {
            out << ctx.get_assign_level(r) << ": " << r << " ";
            ctx.display(out, ctx.get_justification(r.var()));
        }

        if (!m_antecedents.empty()) {
            out << m_antecedents << " ==> ";
        }
        uint_set seen;
        bool first = true;
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            if (seen.contains(v)) {
                continue;
            }
            seen.insert(v);
            int coeff = get_coeff(v);
            if (coeff == 0) {
                continue;
            }
            if (!first) {
                out << " + ";
            }
            if (coeff == 1) {
                out << literal(v);
            }
            else if (coeff == -1) {
                out << literal(v, true);
            }
            else if (coeff > 0) {
                out << coeff << " * " << literal(v);
            }
            else {
                out << (-coeff) << " * " << literal(v, true);
            }
            first = false;
        }
        out << " >= " << m_bound << "\n";
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

        void get_dependencies(buffer<model_value_dependency> & result) override {
            result.append(m_dependencies.size(), m_dependencies.c_ptr());
        }

        app * mk_value(model_generator & mg, ptr_vector<expr> & values) override {
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
                return nullptr;
            }
            return nullptr;
        }
    };

    class pb_factory : public value_factory {
    public:
        pb_factory(ast_manager& m, family_id fid):
            value_factory(m, fid) {}
        
        expr * get_some_value(sort * s) override {
            return m_manager.mk_true();
        }        
        bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
            v1 = m_manager.mk_true();
            v2 = m_manager.mk_false();
            return true;
        }        
        expr * get_fresh_value(sort * s) override {
            return nullptr;
        }
        void register_value(expr * n) override { }
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

    void theory_pb::display_watch(std::ostream& out, bool_var v, bool sign) const {
        ineq_watch const* w = m_var_infos[v].m_lit_watch[sign];
        if (!w) return;
        ineq_watch const& wl = *w;
        out << "watch: " << literal(v, sign) << " |-> ";
        for (unsigned i = 0; i < wl.size(); ++i) {
            out << wl[i]->lit() << " ";
        }
        out << "\n";        
    }

    void theory_pb::display(std::ostream& out) const {
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            display_watch(out, vi, false);
            display_watch(out, vi, true);
        }
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            ineq* c = m_var_infos[vi].m_ineq;
            if (c) {
                display(out, *c, true);
            }
        }

        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            card* c = m_var_infos[vi].m_card;
            if (c) {
                display(out, *c, true);
            }
        }

    }


}
