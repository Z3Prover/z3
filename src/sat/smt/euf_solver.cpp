/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_solver.cpp

Abstract:

    Solver plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/pb_decl_plugin.h"
#include "ast/ast_ll_pp.h"
#include "sat/sat_solver.h"
#include "sat/smt/sat_smt.h"
#include "sat/smt/ba_solver.h"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/arith_solver.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/fpa_solver.h"

namespace euf {

    solver::solver(ast_manager& m, sat::sat_internalizer& si, params_ref const& p) :
        extension(symbol("euf"), m.mk_family_id("euf")),
        m(m),
        si(si),
        m_egraph(m),
        m_trail(*this),
        m_rewriter(m),
        m_unhandled_functions(m),
        m_lookahead(nullptr),
        m_to_m(&m),
        m_to_si(&si),
        m_reinit_exprs(m),
        m_values(m)
    {
        updt_params(p);

        std::function<void(std::ostream&, void*)> disp =
            [&](std::ostream& out, void* j) { 
            display_justification_ptr(out, reinterpret_cast<size_t*>(j)); 
        };
        m_egraph.set_display_justification(disp);
    }

    void solver::updt_params(params_ref const& p) {
        m_config.updt_params(p);
    }

    /**
    * retrieve extension that is associated with Boolean variable.
    */
    th_solver* solver::bool_var2solver(sat::bool_var v) {
        if (v >= m_var2expr.size())
            return nullptr;
        expr* e = m_var2expr[v];
        if (!e)
            return nullptr;
        return expr2solver(e);
    }

    th_solver* solver::expr2solver(expr* e) {
        if (is_app(e)) 
            return func_decl2solver(to_app(e)->get_decl());     
        if (is_forall(e) || is_exists(e))
            return quantifier2solver();
        return nullptr;
    }

    th_solver* solver::quantifier2solver() {
        family_id fid = m.mk_family_id(symbol("quant"));
        auto* ext = m_id2solver.get(fid, nullptr);
        if (ext)
            return ext;
        ext = alloc(q::solver, *this);
        ext->set_solver(m_solver);
        ext->push_scopes(s().num_scopes());
        add_solver(fid, ext);
        return ext;
    }

    th_solver* solver::get_solver(family_id fid, func_decl* f) {
        if (fid == null_family_id)
            return nullptr;
        auto* ext = m_id2solver.get(fid, nullptr);
        if (ext)
            return ext;
        if (fid == m.get_basic_family_id())
            return nullptr;
        pb_util pb(m);
        bv_util bvu(m);
        array_util au(m);
        fpa_util fpa(m);
        arith_util arith(m);
        if (pb.get_family_id() == fid) 
            ext = alloc(sat::ba_solver, *this, fid);
        else if (bvu.get_family_id() == fid) 
            ext = alloc(bv::solver, *this, fid);
        else if (au.get_family_id() == fid) 
            ext = alloc(array::solver, *this, fid);
        else if (fpa.get_family_id() == fid) 
            ext = alloc(fpa::solver, *this);
        else if (arith.get_family_id() == fid)
            ext = alloc(arith::solver, *this, fid);
        
        if (ext) {
            if (use_drat())
                s().get_drat().add_theory(fid, ext->name());
            ext->set_solver(m_solver);
            ext->push_scopes(s().num_scopes());
            add_solver(fid, ext);
            if (ext->use_diseqs())
                m_egraph.set_th_propagates_diseqs(fid);
        }
        else if (f) 
            unhandled_function(f);
        return ext;
    }

    void solver::add_solver(family_id fid, th_solver* th) {
        m_solvers.push_back(th);
        m_id2solver.setx(fid, th, nullptr);
    }

    void solver::unhandled_function(func_decl* f) {
        if (m_unhandled_functions.contains(f))
            return;
        m_unhandled_functions.push_back(f);
        m_trail.push(push_back_vector<solver, func_decl_ref_vector>(m_unhandled_functions));
        IF_VERBOSE(0, verbose_stream() << mk_pp(f, m) << " not handled\n");
    }

    void solver::init_search() {
        TRACE("before_search", s().display(tout););
        for (auto* s : m_solvers)
            s->init_search();
    }

    bool solver::is_external(bool_var v) {
        if (nullptr != m_var2expr.get(v, nullptr))
            return true;
        for (auto* s : m_solvers)
            if (s->is_external(v))
                return true;
        return false;
    }

    bool solver::propagate(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext != this);
        return ext->propagate(l, idx);
    }

    void solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector& r, bool probing) {
        m_egraph.begin_explain();
        m_explain.reset();
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext == this)
            get_antecedents(l, constraint::from_idx(idx), r, probing);
        else
            ext->get_antecedents(l, idx, r, probing);
        for (unsigned qhead = 0; qhead < m_explain.size(); ++qhead) {
            size_t* e = m_explain[qhead];
            if (is_literal(e)) 
                r.push_back(get_literal(e));            
            else {
                size_t idx = get_justification(e);
                auto* ext = sat::constraint_base::to_extension(idx);
                SASSERT(ext != this);
                sat::literal lit = sat::null_literal;
                ext->get_antecedents(lit, idx, r, probing);
            }
        }
        m_egraph.end_explain();  
        unsigned j = 0;
        for (sat::literal lit : r) 
            if (s().lvl(lit) > 0) r[j++] = lit;
        r.shrink(j);
        TRACE("euf", tout << "eplain " << l << " <- " << r << " " << probing << "\n";);
        DEBUG_CODE(for (auto lit : r) SASSERT(s().value(lit) == l_true););

        if (!probing)
            log_antecedents(l, r);
    }

    void solver::add_antecedent(enode* a, enode* b) {
        m_egraph.explain_eq<size_t>(m_explain, a, b);
    }

    bool solver::propagate(enode* a, enode* b, ext_justification_idx idx) {
        if (a->get_root() == b->get_root())
            return false;
        m_egraph.merge(a, b, to_ptr(idx));
        return true;
    }


    void solver::get_antecedents(literal l, constraint& j, literal_vector& r, bool probing) {
        expr* e = nullptr;
        euf::enode* n = nullptr;

        if (!probing && !m_drating)
            init_ackerman();

        switch (j.kind()) {
        case constraint::kind_t::conflict:
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain<size_t>(m_explain);
            break;
        case constraint::kind_t::eq:
            e = m_var2expr[l.var()];
            n = m_egraph.find(e);
            SASSERT(n);
            SASSERT(n->is_equality());
            SASSERT(!l.sign());
            m_egraph.explain_eq<size_t>(m_explain, n->get_arg(0), n->get_arg(1));
            break;
        case constraint::kind_t::lit:
            e = m_var2expr[l.var()];
            n = m_egraph.find(e);
            SASSERT(n);
            SASSERT(m.is_bool(n->get_expr()));
            m_egraph.explain_eq<size_t>(m_explain, n, (l.sign() ? mk_false() : mk_true()));
            break;
        default:
            IF_VERBOSE(0, verbose_stream() << (unsigned)j.kind() << "\n");
            UNREACHABLE();
        }
    }

    void solver::asserted(literal l) {
        expr* e = m_var2expr.get(l.var(), nullptr);
        if (!e) {
            TRACE("euf", tout << "asserted: " << l << "@" << s().scope_lvl() << "\n";);
            return;        
        }
        TRACE("euf", tout << "asserted: " << l << "@" << s().scope_lvl() << " := " << mk_bounded_pp(e, m) << "\n";);
        euf::enode* n = m_egraph.find(e);
        if (!n)
            return;
        bool sign = l.sign();                
        m_egraph.set_value(n, sign ? l_false : l_true);
        auto const & j = s().get_justification(l);
        for (auto th : enode_th_vars(n))
            m_id2solver[th.get_id()]->asserted(l);

        size_t* c = to_ptr(l);
        SASSERT(is_literal(c));
        SASSERT(l == get_literal(c));
        if (!sign && n->is_equality()) {
            SASSERT(!m.is_iff(e));
            euf::enode* na = n->get_arg(0);
            euf::enode* nb = n->get_arg(1);
            m_egraph.merge(na, nb, c);
        }
        else if (n->merge_enabled()) {
            euf::enode* nb = sign ? mk_false() : mk_true();
            m_egraph.merge(n, nb, c);
        }
        else if (sign && n->is_equality()) 
            m_egraph.new_diseq(n);        
    }


    bool solver::unit_propagate() {
        bool propagated = false;
        while (!s().inconsistent()) {
            if (m_egraph.inconsistent()) {  
                unsigned lvl = s().scope_lvl();
                s().set_conflict(sat::justification::mk_ext_justification(lvl, conflict_constraint().to_index()));
                return true;
            }
            bool propagated1 = false;
            if (m_egraph.propagate()) {
                propagate_literals();
                propagate_th_eqs();
                propagated1 = true;
            }

            for (auto* s : m_solvers) {
                if (s->unit_propagate())
                    propagated1 = true;
            }
            if (!propagated1)
                break;
            propagated = true;             
        }
        DEBUG_CODE(if (!s().inconsistent()) check_missing_eq_propagation(););
        return propagated;
    }

    void solver::propagate_literals() {
        for (; m_egraph.has_literal() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_literal()) {
            euf::enode_bool_pair p = m_egraph.get_literal();
            euf::enode* n = p.first;
            bool is_eq = p.second;
            expr* e = n->get_expr();
            expr* a = nullptr, *b = nullptr;
            bool_var v = n->bool_var();
            SASSERT(m.is_bool(e));
            size_t cnstr;
            literal lit;            
            if (is_eq) {
                VERIFY(m.is_eq(e, a, b));
                cnstr = eq_constraint().to_index();
                lit = literal(v, false);
            }
            else {
                lbool val = n->get_root()->value();
                a = e;
                b = (val == l_true) ? m.mk_true() : m.mk_false();
                SASSERT(val != l_undef);
                cnstr = lit_constraint().to_index();
                lit = literal(v, val == l_false);
            }
            unsigned lvl = s().scope_lvl();

            CTRACE("euf", s().value(lit) != l_true, tout << lit << " " << s().value(lit) << "@" << lvl << " " << is_eq << " " << mk_bounded_pp(a, m) << " = " << mk_bounded_pp(b, m) << "\n";);
            if (s().value(lit) == l_false && m_ackerman) 
                m_ackerman->cg_conflict_eh(a, b);
            switch (s().value(lit)) {
            case l_true:
                break;
            case l_undef:
            case l_false:
                s().assign(lit, sat::justification::mk_ext_justification(lvl, cnstr));
                break;
            }
        }
    }

    void solver::propagate_th_eqs() {
        for (; m_egraph.has_th_eq() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_th_eq()) {
            th_eq eq = m_egraph.get_th_eq();
            if (eq.is_eq())
                m_id2solver[eq.id()]->new_eq_eh(eq);    
            else
                m_id2solver[eq.id()]->new_diseq_eh(eq);
        }
    }

    constraint& solver::mk_constraint(constraint*& c, constraint::kind_t k) {
        if (!c) {
            void* mem = memory::allocate(sat::constraint_base::obj_size(sizeof(constraint)));
            c = new (sat::constraint_base::ptr2mem(mem)) constraint(k);
            sat::constraint_base::initialize(mem, this);
        }
        return *c;
    }

    enode* solver::mk_true() {
        VERIFY(visit(m.mk_true()));
        return m_egraph.find(m.mk_true());
    }

    enode* solver::mk_false() {
        VERIFY(visit(m.mk_false()));
        return m_egraph.find(m.mk_false());
    }

    sat::check_result solver::check() { 
        TRACE("euf", s().display(tout););
        bool give_up = false;
        bool cont = false;

        if (!init_relevancy())
            give_up = true;

        for (auto* e : m_solvers)
            switch (e->check()) {
            case sat::check_result::CR_CONTINUE: cont = true; break;
            case sat::check_result::CR_GIVEUP: give_up = true; break;
            default: break;
            }
        if (cont)
            return sat::check_result::CR_CONTINUE;
        if (give_up)
            return sat::check_result::CR_GIVEUP;
        TRACE("after_search", s().display(tout););
        return sat::check_result::CR_DONE;
    }

    void solver::push() {
        si.push();
        scope s;
        s.m_var_lim = m_var_trail.size();
        m_scopes.push_back(s);
        m_trail.push_scope();
        for (auto* e : m_solvers)
            e->push();
        m_egraph.push();
    }

    void solver::user_push() {
        push();
        if (m_dual_solver)
            m_dual_solver->push();
    }

    void solver::user_pop(unsigned n) {
        pop(n);
        if (m_dual_solver)
            m_dual_solver->pop(n);
    }

    void solver::pop(unsigned n) {
        start_reinit(n);
        m_trail.pop_scope(n);
        for (auto* e : m_solvers)
            e->pop(n);
        si.pop(n);
        m_egraph.pop(n);
        scope const & s = m_scopes[m_scopes.size() - n];
        for (unsigned i = m_var_trail.size(); i-- > s.m_var_lim; )
            m_var2expr[m_var_trail[i]] = nullptr;
        m_var_trail.shrink(s.m_var_lim);        
        m_scopes.shrink(m_scopes.size() - n);
        SASSERT(m_egraph.num_scopes() == m_scopes.size());
        TRACE("euf", display(tout << "pop to: " << m_scopes.size() << "\n"););
    }

    void solver::start_reinit(unsigned n) {
        m_reinit_exprs.reset();
        for (sat::bool_var v : s().get_vars_to_reinit()) {
            expr* e = bool_var2expr(v);
            m_reinit_exprs.push_back(e);
        }
    }

    /**
    * After a pop has completed, re-initialize the association between Boolean variables 
    * and the theories by re-creating the expression/variable mapping used for Booleans
    * and replaying internalization.
    */
    void solver::finish_reinit() {
        SASSERT(s().get_vars_to_reinit().size() == m_reinit_exprs.size());
        if (s().get_vars_to_reinit().empty())
            return;

        struct scoped_set_replay {
            solver& s;
            obj_map<expr, sat::bool_var> m;
            scoped_set_replay(solver& s) :s(s) {
                s.si.set_expr2var_replay(&m);
            }
            ~scoped_set_replay() { 
                s.si.set_expr2var_replay(nullptr); 
            }
        };
        scoped_set_replay replay(*this);
        unsigned i = 0;
        for (sat::bool_var v : s().get_vars_to_reinit()) {
            expr* e = m_reinit_exprs.get(i++);
            if (e)
                replay.m.insert(e, v);
        }
        if (replay.m.empty())
            return;
        
        TRACE("euf", for (auto const& kv : replay.m) tout << kv.m_value << "\n";);
        for (auto const& kv : replay.m) {
            TRACE("euf", tout << "replay: " << kv.m_value << " " << mk_bounded_pp(kv.m_key, m) << "\n";);
            sat::literal lit;
            expr* e = kv.m_key;
            if (si.is_bool_op(e)) 
                lit = literal(replay.m[e], false);
            else 
                lit = si.internalize(kv.m_key, true);
            VERIFY(lit.var() == kv.m_value);
            attach_lit(lit, kv.m_key);            
        }
        TRACE("euf", display(tout << "replay done\n"););
    }

    void solver::pre_simplify() {
        for (auto* e : m_solvers)
            e->pre_simplify();
    }

    void solver::simplify() {
        for (auto* e : m_solvers)
            e->simplify();
        if (m_ackerman)
            m_ackerman->propagate();
    }

    void solver::clauses_modifed() {
        for (auto* e : m_solvers)
            e->clauses_modifed();
    }

    lbool solver::get_phase(bool_var v) { 
        auto* ext = bool_var2solver(v);
        if (ext)
            return ext->get_phase(v);
        return l_undef;
    }

    bool solver::set_root(literal l, literal r) {
        expr* e = bool_var2expr(l.var());
        if (!e)
            return true;
        bool ok = true;
        for (auto* s : m_solvers)
            if (!s->set_root(l, r))
                ok = false;
        if (m.is_eq(e) && !m.is_iff(e))
            ok = false;
        euf::enode* n = get_enode(e);
        if (n && n->merge_enabled())
            ok = false;
        
        (void)ok;
        TRACE("euf", tout << ok << " " << l << " -> " << r << "\n";);
        // roots cannot be eliminated as long as the egraph contains the expressions.
        return false;
    }

    void solver::flush_roots() {
        for (auto* s : m_solvers)
            s->flush_roots();
    }

    std::ostream& solver::display(std::ostream& out) const {
        m_egraph.display(out);
        out << "bool-vars\n";
        for (unsigned v : m_var_trail) {
            expr* e = m_var2expr[v];
            out << v << ": " << e->get_id() << " " << m_solver->value(v) << " " << mk_bounded_pp(e, m, 1) << "\n";        
        }
        for (auto* e : m_solvers)
            e->display(out);
        return out; 
    }

    std::ostream& solver::display_justification_ptr(std::ostream& out, size_t* j) const {
        if (is_literal(j))
            return out << "sat: " << get_literal(j);
        else
            return display_justification(out, get_justification(j));
    }

    std::ostream& solver::display_justification(std::ostream& out, ext_justification_idx idx) const { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext == this) {
            constraint& c = constraint::from_idx(idx);
            switch (c.kind()) {
            case constraint::kind_t::conflict:
                return out << "euf conflict";
            case constraint::kind_t::eq:
                return out << "euf equality propagation";
            case constraint::kind_t::lit:
                return out << "euf literal propagation";
            default:
                UNREACHABLE();
                return out;
            }                
        }
        else 
            return ext->display_justification(out, idx);
        return out; 
    }

    std::ostream& solver::display_constraint(std::ostream& out, ext_constraint_idx idx) const { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext != this)
            return ext->display_constraint(out, idx);
        return display_justification(out, idx);
    }

    void solver::collect_statistics(statistics& st) const {
        m_egraph.collect_statistics(st);
        for (auto* e : m_solvers)
            e->collect_statistics(st);
        st.update("euf ackerman", m_stats.m_ackerman);
    }

    sat::extension* solver::copy(sat::solver* s) { 
        auto* r = alloc(solver, *m_to_m, *m_to_si);
        r->m_config = m_config;
        sat::literal true_lit = sat::null_literal;
        if (s->init_trail_size() > 0)
            true_lit = s->trail_literal(0); 
        std::function<void* (void*)> copy_justification = [&](void* x) { 
            SASSERT(true_lit != sat::null_literal); 
            return (void*)(r->to_ptr(true_lit)); 
        };
        r->m_egraph.copy_from(m_egraph, copy_justification);        
        r->set_solver(s);
        for (unsigned i = 0; i < m_id2solver.size(); ++i) {
            auto* e = m_id2solver[i];
            if (e)
                r->add_solver(i, e->clone(s, *r));
        }
        return r;
    }

    void solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        for (auto* e : m_solvers)
            e->find_mutexes(lits, mutexes);
    }

    void solver::gc() {
        for (auto* e : m_solvers)
            e->gc();
    }

    void solver::pop_reinit() {
        finish_reinit();
        for (auto* e : m_solvers)
            e->pop_reinit();
    }

    bool solver::validate() { 
        for (auto* e : m_solvers)
            if (!e->validate())
                return false;
        check_eqc_bool_assignment();
        check_missing_bool_enode_propagation();
        check_missing_eq_propagation();
        m_egraph.invariant();
        return true; 
    }

    void solver::init_use_list(sat::ext_use_list& ul) {
        for (auto* e : m_solvers)
            e->init_use_list(ul);
    }

    bool solver::is_blocked(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::constraint_base::to_extension(idx);
        if (ext != this)
            return ext->is_blocked(l, idx);
        return false; 
    }

    bool solver::check_model(sat::model const& m) const { 
        for (auto* e : m_solvers)
            if (!e->check_model(m))
                return false;
        return true;
    }

    unsigned solver::max_var(unsigned w) const { 
        for (auto* e : m_solvers)
            w = e->max_var(w);
        for (unsigned sz = m_var2expr.size(); sz-- > 0; ) {
            expr* n = m_var2expr[sz];
            if (n && m.is_bool(n)) {
                w = std::max(w, sz);
                break;
            }           
        }
        return w; 
    }

    double solver::get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const {
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext);        
        return (ext == this) ? 0 : ext->get_reward(l, idx, occs);        
    }

    bool solver::is_extended_binary(ext_justification_idx idx, literal_vector& r) {
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext);        
        return (ext != this) && ext->is_extended_binary(idx, r);
    }

    void solver::init_ackerman() {
        if (m_ackerman) 
            return;
        if (m_config.m_dack == dyn_ack_strategy::DACK_DISABLED)
            return;
        m_ackerman = alloc(ackerman, *this, m);
        std::function<void(expr*,expr*,expr*)> used_eq = [&](expr* a, expr* b, expr* lca) {
            m_ackerman->used_eq_eh(a, b, lca);
        };
        std::function<void(app*,app*)> used_cc = [&](app* a, app* b) {
            m_ackerman->used_cc_eh(a, b);
        };
        m_egraph.set_used_eq(used_eq);
        m_egraph.set_used_cc(used_cc);
    }

    bool solver::to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) {
        for (auto* th : m_solvers) {            
            if (!th->to_formulas(l2e, fmls))
                return false;
        }
        for (euf::enode* n : m_egraph.nodes()) {
            if (!n->is_root()) 
                fmls.push_back(m.mk_eq(n->get_expr(), n->get_root()->get_expr()));
        }
        return true;
    }

    bool solver::extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                            std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) {
        for (auto* e : m_solvers)
            if (!e->extract_pb(card, pb))
                return false;
        return true;
    }

    void solver::user_propagate_init(
        void* ctx,
        ::solver::push_eh_t& push_eh,
        ::solver::pop_eh_t& pop_eh,
        ::solver::fresh_eh_t& fresh_eh) {
        m_user_propagator = alloc(user::solver, *this);
        m_user_propagator->add(ctx, push_eh, pop_eh, fresh_eh);
        for (unsigned i = m_scopes.size(); i-- > 0; )
            m_user_propagator->push();
        m_solvers.push_back(m_user_propagator);
        m_id2solver.setx(m_user_propagator->get_id(), m_user_propagator, nullptr);
    }

    bool solver::watches_fixed(enode* n) const {
        return m_user_propagator && m_user_propagator->has_fixed() && n->get_th_var(m_user_propagator->get_id()) != null_theory_var;
    }

    void solver::assign_fixed(enode* n, expr* val, unsigned sz, literal const* explain) {
        theory_var v = n->get_th_var(m_user_propagator->get_id());
        m_user_propagator->new_fixed_eh(v, val, sz, explain);
    }


}
