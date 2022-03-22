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
#include "sat/smt/pb_solver.h"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/arith_solver.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/fpa_solver.h"
#include "sat/smt/dt_solver.h"
#include "sat/smt/recfun_solver.h"

namespace euf {

    std::ostream& clause_pp::display(std::ostream& out) const {
        for (auto lit : lits)
            out << s.literal2expr(lit) << " ";
        return out;
    }

    solver::solver(ast_manager& m, sat::sat_internalizer& si, params_ref const& p) :
        extension(symbol("euf"), m.mk_family_id("euf")),
        m(m),
        si(si),
        m_relevancy(*this),
        m_egraph(m),
        m_trail(),
        m_rewriter(m),
        m_unhandled_functions(m),
        m_lookahead(nullptr),
        m_to_m(&m),
        m_to_si(&si),
        m_values(m)
    {
        updt_params(p);
        m_relevancy.set_enabled(get_config().m_relevancy_lvl > 2);

        std::function<void(std::ostream&, void*)> disp =
            [&](std::ostream& out, void* j) { 
            display_justification_ptr(out, reinterpret_cast<size_t*>(j)); 
        };
        m_egraph.set_display_justification(disp);

        if (m_relevancy.enabled()) {
            std::function<void(euf::enode* root, euf::enode* other)> on_merge =
                [&](enode* root, enode* other) {
                m_relevancy.merge(root, other);
            };
            m_egraph.set_on_merge(on_merge);
        }
    }

    void solver::updt_params(params_ref const& p) {
        m_config.updt_params(p);
    }

    /**
    * retrieve extension that is associated with Boolean variable.
    */
    th_solver* solver::bool_var2solver(sat::bool_var v) {
        if (v >= m_bool_var2expr.size())
            return nullptr;
        expr* e = m_bool_var2expr[v];
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
        ext = alloc(q::solver, *this, fid);
        m_qsolver = ext;
        add_solver(ext);
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
        if (fid == m.get_user_sort_family_id())
            return nullptr;
        pb_util pb(m);
        bv_util bvu(m);
        array_util au(m);
        fpa_util fpa(m);
        arith_util arith(m);
        datatype_util dt(m);
        recfun::util rf(m);
        if (pb.get_family_id() == fid)
            ext = alloc(pb::solver, *this, fid);
        else if (bvu.get_family_id() == fid)
            ext = alloc(bv::solver, *this, fid);
        else if (au.get_family_id() == fid)
            ext = alloc(array::solver, *this, fid);
        else if (fpa.get_family_id() == fid)
            ext = alloc(fpa::solver, *this);
        else if (arith.get_family_id() == fid)
            ext = alloc(arith::solver, *this, fid);
        else if (dt.get_family_id() == fid)
            ext = alloc(dt::solver, *this, fid);
        else if (rf.get_family_id() == fid)
            ext = alloc(recfun::solver, *this);
        
        if (ext) 
            add_solver(ext);        
        else if (f) 
            unhandled_function(f);
        return ext;
    }

    void solver::add_solver(th_solver* th) {
        family_id fid = th->get_id();
        if (use_drat())
            s().get_drat().add_theory(fid, th->name());
        th->set_solver(m_solver);
        th->push_scopes(s().num_scopes() + s().num_user_scopes());
        m_solvers.push_back(th);
        m_id2solver.setx(fid, th, nullptr);
        if (th->use_diseqs())
            m_egraph.set_th_propagates_diseqs(fid);
    }

    void solver::unhandled_function(func_decl* f) {
        if (m_unhandled_functions.contains(f))
            return;
        if (m.is_model_value(f))
            return;
        m_unhandled_functions.push_back(f);
        m_trail.push(push_back_vector<func_decl_ref_vector>(m_unhandled_functions));
        IF_VERBOSE(0, verbose_stream() << mk_pp(f, m) << " not handled\n");
    }

    void solver::init_search() {
        TRACE("before_search", s().display(tout););
        for (auto* s : m_solvers)
            s->init_search();
    }

    bool solver::is_external(bool_var v) {
        if (s().is_external(v))
            return true;
        if (nullptr != m_bool_var2expr.get(v, nullptr))
            return true;
        for (auto* s : m_solvers)
            if (s->is_external(v))
                return true;
        return false;
    }

    bool solver::propagated(literal l, ext_constraint_idx idx) { 
        auto* ext = sat::constraint_base::to_extension(idx);
        SASSERT(ext != this);
        return ext->propagated(l, idx);
    }

    void solver::set_conflict(ext_constraint_idx idx) {
        s().set_conflict(sat::justification::mk_ext_justification(s().scope_lvl(), idx));
    }

    void solver::propagate(literal lit, ext_justification_idx idx) {
        mark_relevant(lit);
        s().assign(lit, sat::justification::mk_ext_justification(s().scope_lvl(), idx));
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
        TRACE("euf", tout << "explain " << l << " <- " << r << " " << probing << "\n";);
        DEBUG_CODE(for (auto lit : r) SASSERT(s().value(lit) == l_true););

        if (!probing)
            log_antecedents(l, r);
    }

    void solver::get_antecedents(literal l, th_explain& jst, literal_vector& r, bool probing) {
        for (auto lit : euf::th_explain::lits(jst))
            r.push_back(lit);
        for (auto eq : euf::th_explain::eqs(jst))
            add_antecedent(eq.first, eq.second);

        if (!probing && use_drat()) 
            log_justification(l, jst);
    }

    void solver::add_antecedent(enode* a, enode* b) {
        m_egraph.explain_eq<size_t>(m_explain, a, b);
    }

    void solver::add_diseq_antecedent(ptr_vector<size_t>& ex, enode* a, enode* b) {
        sat::bool_var v = get_egraph().explain_diseq(ex, a, b);
        SASSERT(v == sat::null_bool_var || s().value(v) == l_false);
        if (v != sat::null_bool_var) 
            ex.push_back(to_ptr(sat::literal(v, true)));
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
            e = m_bool_var2expr[l.var()];
            n = m_egraph.find(e);
            SASSERT(n);
            SASSERT(n->is_equality());
            SASSERT(!l.sign());
            m_egraph.explain_eq<size_t>(m_explain, n->get_arg(0), n->get_arg(1));
            break;
        case constraint::kind_t::lit:
            e = m_bool_var2expr[l.var()];
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

    void solver::set_eliminated(bool_var v) {
        si.uncache(literal(v, false));
        si.uncache(literal(v, true));
    }

    void solver::asserted(literal l) {

        m_relevancy.asserted(l);
        if (!m_relevancy.is_relevant(l))
            return;        

        expr* e = m_bool_var2expr.get(l.var(), nullptr);
        TRACE("euf", tout << "asserted: " << l << "@" << s().scope_lvl() << " := " << mk_bounded_pp(e, m) << "\n";);
        if (!e) 
            return;                
        euf::enode* n = m_egraph.find(e);
        if (!n)
            return;
        bool sign = l.sign();   
        m_egraph.set_value(n, sign ? l_false : l_true, justification::external(to_ptr(l)));
        for (auto const& th : enode_th_vars(n))
            m_id2solver[th.get_id()]->asserted(l);

        size_t* c = to_ptr(l);
        SASSERT(is_literal(c));
        SASSERT(l == get_literal(c));
        if (n->value_conflict()) {
            euf::enode* nb = sign ? mk_false() : mk_true();
            euf::enode* r = n->get_root();
            euf::enode* rb = sign ? mk_true() : mk_false();
            sat::literal rl(r->bool_var(), r->value() == l_false);
            m_egraph.merge(n, nb, c);
            m_egraph.merge(r, rb, to_ptr(rl));
            SASSERT(m_egraph.inconsistent());
            return;
	    }
        if (n->merge_tf()) {
            euf::enode* nb = sign ? mk_false() : mk_true();
            m_egraph.merge(n, nb, c);
        }
        if (n->is_equality()) {
            SASSERT(!m.is_iff(e));
            SASSERT(m.is_eq(e));
            if (sign)
                m_egraph.new_diseq(n);
            else                 
                m_egraph.merge(n->get_arg(0), n->get_arg(1), c);            
        }    
    }


    bool solver::unit_propagate() {
        bool propagated = false;
        while (!s().inconsistent()) {
            if (m_relevancy.enabled())
                m_relevancy.propagate();
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

            for (unsigned i = 0; i < m_solvers.size(); ++i) 
                if (m_solvers[i]->unit_propagate())
                    propagated1 = true;
            
            if (propagated1) {
                propagated = true;
                continue;
            }
            if (m_relevancy.enabled() && m_relevancy.can_propagate())
                continue;
            break;                  
        }
        DEBUG_CODE(if (!propagated && !s().inconsistent()) check_missing_eq_propagation(););
        return propagated;
    }

    void solver::propagate_literals() {
        for (; m_egraph.has_literal() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_literal()) {
            auto [n, is_eq] = m_egraph.get_literal();
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
                if (val == l_undef && m.is_false(n->get_root()->get_expr()))
                    val = l_false;
                if (val == l_undef && m.is_true(n->get_root()->get_expr()))
                    val = l_true;
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

    bool solver::is_self_propagated(th_eq const& e) {
        if (!e.is_eq())
            return false;
        
        m_egraph.begin_explain();
        m_explain.reset();
        m_egraph.explain_eq<size_t>(m_explain, e.child(), e.root());
        m_egraph.end_explain();
        if (m_egraph.uses_congruence())
            return false;
        for (auto p : m_explain) {
            if (is_literal(p))
                return false;

            size_t idx = get_justification(p);
            auto* ext = sat::constraint_base::to_extension(idx);                
            if (ext->get_id() != e.id())
                return false;
            if (ext->enable_self_propagate())
                return false;
        }
        return true;
    }

    void solver::propagate_th_eqs() {
        for (; m_egraph.has_th_eq() && !s().inconsistent() && !m_egraph.inconsistent(); m_egraph.next_th_eq()) {
            th_eq eq = m_egraph.get_th_eq();
            if (!eq.is_eq())
                m_id2solver[eq.id()]->new_diseq_eh(eq);
            else if (!is_self_propagated(eq))
                m_id2solver[eq.id()]->new_eq_eh(eq);                                
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
        ++m_stats.m_final_checks;
        TRACE("euf", s().display(tout););
        bool give_up = false;
        bool cont = false;

        if (unit_propagate())
            return sat::check_result::CR_CONTINUE;
        
        unsigned num_nodes = m_egraph.num_nodes();
        auto apply_solver = [&](th_solver* e) {
            switch (e->check()) {
            case sat::check_result::CR_CONTINUE: cont = true; break;
            case sat::check_result::CR_GIVEUP: give_up = true; break;
            default: break;
            }
        };
        if (merge_shared_bools())
            cont = true;
        for (auto* e : m_solvers) {
            if (!m.inc())
                return sat::check_result::CR_GIVEUP;
            if (e == m_qsolver)
                continue;
            apply_solver(e);
            if (s().inconsistent())
                return sat::check_result::CR_CONTINUE;
        }


        if (s().inconsistent())
            return sat::check_result::CR_CONTINUE;
        if (cont)
            return sat::check_result::CR_CONTINUE;
        if (m_qsolver)
            apply_solver(m_qsolver);
        if (num_nodes < m_egraph.num_nodes()) 
            return sat::check_result::CR_CONTINUE;
        if (cont)
            return sat::check_result::CR_CONTINUE;
        TRACE("after_search", s().display(tout););
        if (give_up)
            return sat::check_result::CR_GIVEUP;
        return sat::check_result::CR_DONE;
    }

    bool solver::merge_shared_bools() {
        bool merged = false;
        for (unsigned i = m_egraph.nodes().size(); i-- > 0; ) {
            euf::enode* n = m_egraph.nodes()[i];
            if (!is_shared(n) || !m.is_bool(n->get_expr()))
                continue;
            if (n->value() == l_true && !m.is_true(n->get_root()->get_expr())) {
                m_egraph.merge(n, mk_true(), to_ptr(sat::literal(n->bool_var())));
                merged = true;                    
            }
            if (n->value() == l_false && !m.is_false(n->get_root()->get_expr())) {
                m_egraph.merge(n, mk_false(), to_ptr(~sat::literal(n->bool_var())));
                merged = true;
            }
        }
        return merged;
    }

    void solver::push() {
        si.push();
        scope s(m_var_trail.size());
        m_scopes.push_back(s);
        m_trail.push_scope();
        for (auto* e : m_solvers)
            e->push();
        m_egraph.push();
        m_relevancy.push();
    }

    void solver::pop(unsigned n) {
        start_reinit(n);
        m_trail.pop_scope(n);
        for (auto* e : m_solvers)
            e->pop(n);
        si.pop(n);
        m_egraph.pop(n);
        m_relevancy.pop(n);
        scope const & sc = m_scopes[m_scopes.size() - n];
        for (unsigned i = m_var_trail.size(); i-- > sc.m_var_lim; ) {
            bool_var v = m_var_trail[i];
            m_bool_var2expr[v] = nullptr;
            s().set_non_external(v);
        }
        m_var_trail.shrink(sc.m_var_lim);        
        m_scopes.shrink(m_scopes.size() - n);
        SASSERT(m_egraph.num_scopes() == m_scopes.size());
        TRACE("euf_verbose", display(tout << "pop to: " << m_scopes.size() << "\n"););
    }

    void solver::user_push() {
        push();      
    }

    void solver::user_pop(unsigned n) {
        pop(n);
    }

    void solver::start_reinit(unsigned n) {
        m_reinit.reset();
        for (sat::bool_var v : s().get_vars_to_reinit()) {
            expr* e = bool_var2expr(v);
            if (e)
                m_reinit.push_back(reinit_t(expr_ref(e, m), get_enode(e)?get_enode(e)->generation():0, v));
        }
    }

    /**
    * After a pop has completed, re-initialize the association between Boolean variables 
    * and the theories by re-creating the expression/variable mapping used for Booleans
    * and replaying internalization.
    */
    void solver::finish_reinit() {
        if (m_reinit.empty())
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
        scoped_suspend_rlimit suspend_rlimit(m.limit());

        for (auto const& [e, generation, v] : m_reinit) 
            replay.m.insert(e, v);
    
        TRACE("euf", for (auto const& kv : replay.m) tout << kv.m_value << "\n";);
        for (auto const& [e, generation, v] : m_reinit) {
            scoped_generation _sg(*this, generation);
            TRACE("euf", tout << "replay: " << v << " " << e->get_id() << " " << mk_bounded_pp(e, m) << " " << si.is_bool_op(e) << "\n";);
            sat::literal lit;
            if (si.is_bool_op(e)) 
                lit = literal(replay.m[e], false);
            else 
                lit = si.internalize(e, true);
            VERIFY(lit.var() == v);     
            if (!m_egraph.find(e) && (!m.is_iff(e) && !m.is_or(e) && !m.is_and(e) && !m.is_not(e))) {
                ptr_buffer<euf::enode> args;
                if (is_app(e))
                    for (expr* arg : *to_app(e))
                        args.push_back(e_internalize(arg));
                if (!m_egraph.find(e))
                    mk_enode(e, args.size(), args.data());
            }
            attach_lit(lit, e);            
        }
        
        if (relevancy_enabled())
            for (auto const& [e, generation, v] : m_reinit)
                if (si.is_bool_op(e))
                    relevancy_reinit(e);
        TRACE("euf", display(tout << "replay done\n"););
    }

    /**
    * Boolean structure needs to be replayed for relevancy tracking.
    * Main cases for replaying Boolean functions are included. When a replay
    * is not supported, we just disable relevancy.
    */
    void solver::relevancy_reinit(expr* e) {
        TRACE("euf", tout << "internalize again " << mk_pp(e, m) << "\n";);
        if (to_app(e)->get_family_id() != m.get_basic_family_id()) {
            disable_relevancy(e);
            return;
        }
        auto lit = si.internalize(e, true);
        switch (to_app(e)->get_decl_kind()) {
        case OP_NOT: {
            auto lit2 = si.internalize(to_app(e)->get_arg(0), true);
            add_aux(lit, lit2);
            add_aux(~lit, ~lit2);
            break;
        }
        case OP_EQ: {
            if (to_app(e)->get_num_args() != 2) {
                disable_relevancy(e);
                return;
            }
            auto lit1 = si.internalize(to_app(e)->get_arg(0), true);
            auto lit2 = si.internalize(to_app(e)->get_arg(1), true);
            add_aux(~lit, ~lit1, lit2);
            add_aux(~lit, lit1, ~lit2);
            add_aux(lit, lit1, lit2);
            add_aux(lit, ~lit1, ~lit2);
            break;
        }
        case OP_OR: {
            sat::literal_vector lits;
            for (expr* arg : *to_app(e))
                lits.push_back(si.internalize(arg, true));
            for (auto lit2 : lits)
                add_aux(~lit2, lit);
            lits.push_back(~lit);
            add_aux(lits);
            break;
        }
        case OP_AND: {
            sat::literal_vector lits;
            for (expr* arg : *to_app(e))
                lits.push_back(~si.internalize(arg, true));
            for (auto nlit2 : lits)
                add_aux(~lit, ~nlit2);
            lits.push_back(lit);
            add_aux(lits);
            break;
        }
        case OP_TRUE:
            add_aux(lit);
            break;
        case OP_FALSE:
            add_aux(~lit);
            break;
        case OP_ITE: {
            auto lit1 = si.internalize(to_app(e)->get_arg(0), true);
            auto lit2 = si.internalize(to_app(e)->get_arg(1), true);
            auto lit3 = si.internalize(to_app(e)->get_arg(2), true);
            add_aux(~lit, ~lit1, lit2);
            add_aux(~lit, lit1, lit3);
            add_aux(lit, ~lit1, ~lit2);
            add_aux(lit, lit1, ~lit3);
            break;
        }
        case OP_XOR: {
            if (to_app(e)->get_num_args() != 2) {
                disable_relevancy(e);
                break;
            }
            auto lit1 = si.internalize(to_app(e)->get_arg(0), true);
            auto lit2 = si.internalize(to_app(e)->get_arg(1), true);
            add_aux(lit, ~lit1, lit2);
            add_aux(lit, lit1, ~lit2);
            add_aux(~lit, lit1, lit2);
            add_aux(~lit, ~lit1, ~lit2);
            break;
        }
        case OP_IMPLIES: {
            if (to_app(e)->get_num_args() != 2) {
                disable_relevancy(e);
                break;
            }
            auto lit1 = si.internalize(to_app(e)->get_arg(0), true);
            auto lit2 = si.internalize(to_app(e)->get_arg(1), true);
            add_aux(~lit, ~lit1, lit2);
            add_aux(lit, lit1);
            add_aux(lit, ~lit2);
            break;
        }
        default:
            UNREACHABLE();
        }
    }

    bool solver::is_relevant(bool_var v) const {
        if (m_relevancy.enabled())
            return m_relevancy.is_relevant(v);
        auto* e = bool_var2enode(v);
        return !e || is_relevant(e);
    }

    void solver::relevant_eh(euf::enode* n) {
        if (m_qsolver)
            m_qsolver->relevant_eh(n);
        for (auto const& thv : enode_th_vars(n)) {
            auto* th = m_id2solver.get(thv.get_id(), nullptr);
            if (th && th != m_qsolver)
                th->relevant_eh(n);
        }       
    }

    bool solver::enable_ackerman_axioms(expr* e) const {
        euf::enode* n = get_enode(e);
        if (!n)
            return false;
        for (auto const& thv : enode_th_vars(n)) {
            auto* th = m_id2solver.get(thv.get_id(), nullptr);
            if (th && !th->enable_ackerman_axioms(n))
                return false;
        }
        return true;
    }

    bool solver::is_fixed(euf::enode* n, expr_ref& val, sat::literal_vector& explain) {
        if (n->bool_var() != sat::null_bool_var) {
            switch (s().value(n->bool_var())) {
            case l_true:
                val = m.mk_true();
                explain.push_back(sat::literal(n->bool_var()));
                return true;                
            case l_false:
                val = m.mk_false();
                explain.push_back(~sat::literal(n->bool_var()));
                return true;
            default:
                return false;
            }
        }
        for (auto const& thv : enode_th_vars(n)) {
            auto* th = m_id2solver.get(thv.get_id(), nullptr);
            if (th && !th->is_fixed(thv.get_var(), val, explain))
                return true;
        }
        return false;
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
    
    bool solver::should_research(sat::literal_vector const& core) {
        bool result = false;
        for (auto* e : m_solvers)
            if (e->should_research(core))
                result = true;
        return result;
    }

    void solver::add_assumptions(sat::literal_set& assumptions) {
        for (auto* e : m_solvers)
            e->add_assumptions(assumptions);
    }

    bool solver::tracking_assumptions() {
        for (auto* e : m_solvers)
            if (e->tracking_assumptions())
                return true;
        return false;
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
        if (m_relevancy.enabled())
            return false;
        bool ok = true;
        for (auto* s : m_solvers)
            if (!s->set_root(l, r))
                ok = false;

        if (!ok)
            return false;
        expr* e = bool_var2expr(l.var());
        if (!e)
            return true;
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
            expr* e = m_bool_var2expr[v];
            out << v << (is_relevant(v)?"":"n") << ": " << e->get_id() << " " << m_solver->value(v) << " " << mk_bounded_pp(e, m, 1) << "\n";        
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
        st.update("euf final check", m_stats.m_final_checks);
    }

    enode* solver::copy(solver& dst_ctx, enode* src_n) {
        if (!src_n)
            return nullptr;
        ast_translation tr(m, dst_ctx.get_manager(), false);
        expr* e1 = src_n->get_expr();
        expr* e2 = tr(e1);
        euf::enode* n2 = dst_ctx.get_enode(e2);
        SASSERT(n2);
        return n2;
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
        for (euf::enode* n : r->m_egraph.nodes()) {
            auto b = n->bool_var();
            if (b != sat::null_bool_var) {
                r->m_bool_var2expr.setx(b, n->get_expr(), nullptr);
                SASSERT(r->m.is_bool(n->get_sort()));
                IF_VERBOSE(11, verbose_stream() << "set bool_var " << b << " " << r->bpp(n) << " " << mk_bounded_pp(n->get_expr(), m) << "\n");
            }
        }
        for (auto* s_orig : m_id2solver) {
            if (s_orig) {
                auto* s_clone = s_orig->clone(*r);
                r->add_solver(s_clone);
                s_clone->set_solver(s);
            }
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

#if 0
        for (enode* n : m_egraph.nodes()) {
            if (n->bool_var() != sat::null_bool_var && s().is_free(n->bool_var()))
                std::cout << "has free " << n->bool_var() << "\n";
        }
#endif
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

    void solver::gc_vars(unsigned num_vars) {
        for (auto* e : m_solvers)
            e->gc_vars(num_vars);
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
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) {
        m_user_propagator = alloc(user_solver::solver, *this);
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
