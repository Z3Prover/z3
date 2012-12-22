/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_smt_theory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#include"smt_context.h"
#include"user_smt_theory.h"
#include"ast_pp.h"
#include"smt_model_generator.h"
#include"stats.h"
#include"warning.h"

namespace smt {

    // 
    // value factory for user sorts.
    // 
    // NB. This value factory for user theories
    //     does not address theories where model
    //     values are structured objects such as
    //     arrays, records, or data-types.
    //     

    class user_smt_theory_factory : public simple_factory<unsigned> {
        app* mk_value_core(unsigned const& val, sort* s) {
            return m_manager.mk_model_value(val, s);
        }
    public:
        user_smt_theory_factory(ast_manager& m, family_id fid):
            simple_factory<unsigned>(m, fid)
        {}
    };

    user_theory::user_theory(ast_manager & m, smt_params const& p, void * ext_context, void * ext_data, char const * name, family_id fid, user_decl_plugin * dp, user_simplifier_plugin * sp):
        theory(fid),
        m_params(p),
        m_ext_context(ext_context),
        m_ext_data(ext_data),
        m_name(name),
        m_simplify_axioms(false),
        m_decl_plugin(dp),
        m_simplifier_plugin(sp),
        m_find(*this),
        m_trail_stack(*this),
        m_asserted_axioms(m),
        m_persisted_axioms(m),
        m_persisted_axioms_qhead(0),
        m_delete_fptr(0),
        m_new_app_fptr(0),
        m_new_elem_fptr(0),
        m_init_search_fptr(0),
        m_push_fptr(0),
        m_pop_fptr(0),
        m_restart_fptr(0),
        m_reset_fptr(0),
        m_final_check_fptr(0),
        m_new_eq_fptr(0),
        m_new_diseq_fptr(0),
        m_new_assignment_fptr(0),
        m_new_relevant_fptr(0),
        m_mk_fresh_fptr(0),
        m_delete_invoking(false),
        m_new_app_invoking(false),
        m_new_elem_invoking(false),
        m_init_search_invoking(false),
        m_push_invoking(false),
        m_pop_invoking(false),
        m_restart_invoking(false),
        m_reset_invoking(false),
        m_final_check_invoking(false),
        m_new_eq_invoking(false),
        m_new_diseq_invoking(false),
        m_new_assignment_invoking(false),
        m_new_relevant_invoking(false) {
    }

    user_theory::~user_theory() {
        if (m_delete_fptr != 0) {
            flet<bool> i(m_delete_invoking, true);
            m_delete_fptr(this);
        }
    }

    theory * user_theory::mk_fresh(context * new_ctx) {
        if (m_mk_fresh_fptr == 0) {
            throw default_exception("The mk_fresh_ext_data callback was not set for user theory, you must use Z3_theory_set_mk_fresh_ext_data_callback");
            return 0;
        }
        user_simplifier_plugin * new_sp = static_cast<user_simplifier_plugin*>(new_ctx->get_simplifier().get_plugin(get_family_id()));
        SASSERT(new_sp != 0);
        user_theory * new_th = alloc(user_theory, get_manager(), new_ctx->get_fparams(), m_ext_context, m_mk_fresh_fptr(this), get_name(), get_family_id(),
                                     m_decl_plugin, new_sp);
        new_sp->set_owner(new_th);

        new_th->m_delete_fptr = m_delete_fptr;
        new_th->m_new_app_fptr = m_new_app_fptr;
        new_th->m_new_elem_fptr = m_new_elem_fptr;
        new_th->m_init_search_fptr = m_init_search_fptr;
        new_th->m_push_fptr = m_push_fptr;
        new_th->m_pop_fptr = m_pop_fptr;
        new_th->m_restart_fptr = m_restart_fptr;
        new_th->m_reset_fptr = m_reset_fptr;
        new_th->m_final_check_fptr = m_final_check_fptr;
        new_th->m_new_eq_fptr = m_new_eq_fptr;
        new_th->m_new_diseq_fptr = m_new_diseq_fptr;
        new_th->m_new_assignment_fptr = m_new_assignment_fptr;
        new_th->m_new_relevant_fptr = m_new_relevant_fptr;
        new_th->m_mk_fresh_fptr = m_mk_fresh_fptr;
        return new_th;
    }

    void user_theory::assert_axiom_core(app* a) {
        if (m_asserted_axiom_set.contains(a)) {
            return;
        }
        m_asserted_axiom_set.insert(a);
        m_asserted_axioms.push_back(a);
        if (m_params.m_user_theory_persist_axioms) {
            m_persisted_axioms.push_back(a);
        }
    }

    /**
       TODO: discuss semantics of assert_axiom.
       Should we simplify axiom of not?
    */
    void user_theory::assert_axiom(ast * axiom) {
        ++m_stats.m_num_user_axioms;
        TRACE("user_smt_theory", tout << mk_pp(axiom, get_manager()) << "\n";);
        if (!is_expr(axiom)) {
            throw default_exception("invalid expression");
        }
        if (!get_manager().is_bool(to_expr(axiom))) {
            throw default_exception("invalid theory axiom: axioms must have Boolean sort");
        }
        if (!m_new_eq_invoking &&
            !m_new_diseq_invoking &&
            !m_new_assignment_invoking &&
            !m_new_relevant_invoking &&
            !m_final_check_invoking) {
            throw default_exception("theory axioms can only be invoked during callbacks "
                                    "for new (dis)equalities/assignments and final check");
        }
        context & ctx   = get_context();
        ast_manager & m = get_manager();

        if (!is_app(axiom) || !to_app(axiom)->is_ground() || 
            ctx.get_fparams().m_user_theory_preprocess_axioms) {
            asserted_formulas asf(m, ctx.get_fparams());
            asf.assert_expr(to_app(axiom));
            asf.reduce();
            unsigned sz    = asf.get_num_formulas();
            unsigned qhead = asf.get_qhead();
            while (qhead < sz) {
                expr * f   = asf.get_formula(qhead);
                assert_axiom_core(to_app(f));
                ++qhead;
            }            
        }
        else {
            if (!m_simplify_axioms) {
                m_simplifier_plugin->enable(false);
            }
            expr_ref  s_axiom(m);
            proof_ref pr(m);
            simplifier & s  = ctx.get_simplifier();
            s(to_app(axiom), s_axiom, pr);
            if (!is_app(s_axiom)) {
                throw default_exception("invalid theory axiom: axioms must be applications");
            }
            axiom = s_axiom;
            m_simplifier_plugin->enable(true);
            assert_axiom_core(to_app(axiom));
        } 
    }

    void user_theory::assume_eq(ast * _lhs, ast * _rhs) {
        if (!is_expr(_lhs) || !is_expr(_rhs)) {
            throw default_exception("assume_eq must take expressions as arguments");
        }
        expr* lhs = to_expr(_lhs);
        expr* rhs = to_expr(_rhs);
        ast_manager& m = get_manager();
        context& ctx = get_context();
        if (m.is_true(rhs)) {
            std::swap(lhs, rhs);
        }
        if (m.is_true(lhs)) {
            theory_var v2 = mk_var(rhs);     
            if (v2 == null_theory_var) {
                throw default_exception("invalid assume eq: lhs or rhs is not a theory term");
            }       
            bool_var bv = ctx.get_bool_var(rhs);
            ctx.set_true_first_flag(bv);
            ctx.mark_as_relevant(get_enode(v2));
            return;
        }
        if (m.is_bool(lhs)) {
            throw default_exception("assume_eq on Booleans must take 'true' as one of the arguments");
        }
        theory_var v1 = mk_var(lhs);
        theory_var v2 = mk_var(rhs);
        if (v1 == null_theory_var || v2 == null_theory_var) {
            throw default_exception("invalid assume eq: lhs or rhs is not a theory term");
        }
        ctx.assume_eq(get_enode(v1), get_enode(v2));
    }

    void user_theory::reset_propagation_queues() {
        m_new_eqs.reset();
        m_new_diseqs.reset();
        m_new_assignments.reset();
        m_new_relevant_apps.reset();
    }

    theory_var user_theory::get_var(ast * n) const {
        if (!is_app(n))
            return null_theory_var;
        context & ctx = get_context();
        if (ctx.e_internalized(to_app(n))) {
            enode * e = ctx.get_enode(to_app(n));
            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }

    theory_var user_theory::mk_var(ast * n) {
        theory_var v = get_var(n);
        if (v != null_theory_var || !is_app(n)) {
            return v;
        }
        app* a = to_app(n);
        if (a->get_family_id() == get_id() && 
            internalize_term(a)) {
            return mk_var(get_context().get_enode(a)); 
        }
        return v;
    }

    ast * user_theory::get_root(ast * n) const {
        theory_var v = get_var(n);
        if (v != null_theory_var) {
            theory_var r = m_find.find(v);
            return get_ast(r);
        }
        return n;
    }
        
    ast * user_theory::get_next(ast * n) const {
        theory_var v = get_var(n);
        if (v != null_theory_var) {
            theory_var r = m_find.next(v);
            return get_ast(r);
        }
        return n;
    }

    void user_theory::shrink_use_list(unsigned sz) {
        SASSERT(m_use_list.size() >= sz);
        std::for_each(m_use_list.begin() + sz, m_use_list.end(), delete_proc<ptr_vector<app> >());
        m_use_list.shrink(sz);
    }

    ptr_vector<app> * user_theory::get_non_null_use_list(theory_var v) {
        SASSERT(v != null_theory_var);
        if (m_use_list[v] == 0)
            m_use_list[v] = alloc(ptr_vector<app>);
        return m_use_list[v];
    }

    unsigned user_theory::get_num_parents(ast * n) const {
        theory_var v = get_var(n);
        if (v != null_theory_var && m_use_list[v] != 0)
            return m_use_list[v]->size();
        return 0;
    }

    
    ast * user_theory::get_parent(ast * n, unsigned i) const {
        theory_var v = get_var(n);
        if (v != null_theory_var && m_use_list[v] != 0)
            return m_use_list[v]->get(i, 0);
        return 0;
    }

    theory_var user_theory::mk_var(enode * n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var r  = theory::mk_var(n);
        theory_var r2 = m_find.mk_var();
        m_use_list.push_back(0);
        SASSERT(r == r2);
        get_context().attach_th_var(n, this, r);
        if (m_new_elem_fptr != 0) {
            flet<bool> invoking(m_new_elem_invoking, true);
            m_new_elem_fptr(this, n->get_owner());
        }
        return r;
    }

    bool user_theory::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool user_theory::internalize_term(app * term) {
        context & ctx     = get_context();
        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        // the internalization of the arguments may trigger the internalization of term.
        if (ctx.e_internalized(term))
            return true;
        m_parents.push_back(term);
        enode * e       = ctx.mk_enode(term, false, get_manager().is_bool(term), true); 
        if (get_manager().is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        // make sure every argument is attached to a theory variable...
        for (unsigned i = 0; i < num_args; i++) {
            enode * arg = e->get_arg(i);
            theory_var v_arg = mk_var(arg);
            ptr_vector<app> * arg_use_list = get_non_null_use_list(v_arg);
            arg_use_list->push_back(term);
            m_trail_stack.push(push_back_trail<user_theory, app *, false>(*arg_use_list));
        }
        if (m_new_app_fptr != 0) {
            flet<bool> invoking(m_new_app_invoking, true);
            m_new_app_fptr(this, term);
        }
        return true;
    }

    void user_theory::apply_sort_cnstr(enode * n, sort * s) {
        mk_var(n);
    }

    void user_theory::assign_eh(bool_var v, bool is_true) {
        m_new_assignments.push_back(v);
    }

    void user_theory::new_eq_eh(theory_var v1, theory_var v2) {
        m_new_eqs.push_back(var_pair(v1, v2));
    }

    void user_theory::new_diseq_eh(theory_var v1, theory_var v2) {
        m_new_diseqs.push_back(var_pair(v1, v2));
    }

    void user_theory::relevant_eh(app * n) {
        m_new_relevant_apps.push_back(n);
    }

    void user_theory::push_scope_eh() {
        SASSERT(m_new_assignments.empty());
        SASSERT(m_new_eqs.empty());
        SASSERT(m_new_diseqs.empty());
        SASSERT(m_new_relevant_apps.empty());
        theory::push_scope_eh();
        m_trail_stack.push_scope();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_asserted_axioms_old_sz = m_asserted_axioms.size();
        s.m_parents_old_sz         = m_parents.size();
        if (m_push_fptr != 0) {
            flet<bool> invoke(m_push_invoking, true);
            m_push_fptr(this);
        }
    }

    void user_theory::pop_scope_eh(unsigned num_scopes) {
        reset_propagation_queues();
        if (m_pop_fptr != 0) {
            for (unsigned i = 0; i < num_scopes; i++) {
                flet<bool> invoke(m_pop_invoking, true);
                m_pop_fptr(this);
            }
        }
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        m_parents.shrink(s.m_parents_old_sz);
        unsigned curr_sz    = m_asserted_axioms.size(); 
        unsigned old_sz     = s.m_asserted_axioms_old_sz;
        for (unsigned i = old_sz; i < curr_sz; i++) {
            m_asserted_axiom_set.erase(m_asserted_axioms.get(i));
        }
        m_asserted_axioms.shrink(old_sz);
        m_scopes.shrink(new_lvl);
        m_trail_stack.pop_scope(num_scopes);
        shrink_use_list(get_old_num_vars(num_scopes));
        theory::pop_scope_eh(num_scopes);
    }

    void user_theory::restart_eh() {
        if (m_restart_fptr != 0) {
            flet<bool> invoke(m_restart_invoking, true);
            m_restart_fptr(this);
        }
    }
    

    void user_theory::init_search_eh() {
        if (m_init_search_fptr != 0) {
            flet<bool> invoke(m_init_search_invoking, true);
            m_init_search_fptr(this);
        }
    }

    final_check_status user_theory::final_check_eh() {
        if (m_final_check_fptr != 0) {
            unsigned old_sz = m_asserted_axioms.size();
            flet<bool> invoke(m_final_check_invoking, true);
            Z3_bool r = m_final_check_fptr(this);
            if (old_sz != m_asserted_axioms.size()) {
                assert_axioms_into_context(old_sz);
                return r ? FC_CONTINUE : FC_GIVEUP;
            }
            return r ? FC_DONE : FC_GIVEUP;
        }
        return FC_DONE;
    }

    bool user_theory::can_propagate() {
        return 
            (m_persisted_axioms.size() > m_persisted_axioms_qhead) ||
            !m_new_eqs.empty() || 
            !m_new_diseqs.empty() || 
            !m_new_relevant_apps.empty() || 
            !m_new_assignments.empty();
    }

    literal user_theory::internalize_literal(expr * arg) {
        context & ctx = get_context();
        ast_manager& m = get_manager();
        if (is_app(arg) && m.is_not(arg)) {
            expr * arg_arg = to_app(arg)->get_arg(0);
            if (!ctx.b_internalized(arg_arg))
                ctx.internalize(arg_arg, true);
            return literal(ctx.get_bool_var(arg_arg), true);
        }
        else if (m.is_false(arg)) {
            return false_literal;
        }
        else if (m.is_true(arg)) {
            return true_literal;
        }
        else {
            if (!ctx.b_internalized(arg))
                ctx.internalize(arg, true);
            return literal(ctx.get_bool_var(arg));
        }
    }

    void user_theory::assert_axioms_into_context(unsigned old_sz) {
        for (unsigned i = old_sz; i < m_asserted_axioms.size(); i++) {
            expr * axiom = m_asserted_axioms.get(i);
            assert_axiom_into_context(axiom);
        }
    }

    void user_theory::mark_as_relevant(literal l) {
        if (l == false_literal || l == true_literal) return;
        get_context().mark_as_relevant(l);
    }

    void user_theory::assert_axiom_into_context(expr * axiom) {
        TRACE("user_smt_theory", tout << mk_pp(axiom, get_manager()) << "\n";);
        ast_manager & m = get_manager();
        context & ctx   = get_context();
        if (m.is_or(axiom)) {
            literal_buffer lits;
            unsigned num_args = to_app(axiom)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                lits.push_back(internalize_literal(to_app(axiom)->get_arg(i)));
                mark_as_relevant(lits.back());
            }
            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
        }
        else {
            literal l = internalize_literal(axiom);
            mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
        }
    }

    void user_theory::propagate() {

        unsigned old_sz = m_asserted_axioms.size();
        if (m_persisted_axioms_qhead < m_persisted_axioms.size()) {
            get_context().push_trail(value_trail<context, unsigned>(m_persisted_axioms_qhead));           
            for (; m_persisted_axioms_qhead < m_persisted_axioms.size(); ++m_persisted_axioms_qhead) {
                m_asserted_axioms.push_back(m_persisted_axioms[m_persisted_axioms_qhead].get());
            }
        }  
        do {
            for (unsigned i = 0; i < m_new_eqs.size(); i++) {
                var_pair & p = m_new_eqs[i];
                if (m_new_eq_fptr != 0) {
                    ++m_stats.m_num_eq;
                    flet<bool> invoke(m_new_eq_invoking, true);
                    m_new_eq_fptr(this, get_app(p.first), get_app(p.second));
                }
                m_find.merge(p.first, p.second);
            }
            m_new_eqs.reset();
            
            if (m_new_diseq_fptr != 0) {
                for (unsigned i = 0; i < m_new_diseqs.size(); i++) {
                    ++m_stats.m_num_diseq;
                    var_pair & p = m_new_diseqs[i];
                    flet<bool> invoke(m_new_diseq_invoking, true);
                    m_new_diseq_fptr(this, get_app(p.first), get_app(p.second));
                }
            }
            m_new_diseqs.reset();

            if (m_new_assignment_fptr != 0) {
                context & ctx = get_context();
                for (unsigned i = 0; i < m_new_assignments.size(); i++) {
                    ++m_stats.m_num_assignment;
                    bool_var bv = m_new_assignments[i];
                    lbool val   = ctx.get_assignment(bv);
                    SASSERT(val != l_undef);
                    flet<bool> invoke(m_new_assignment_invoking, true);
                    m_new_assignment_fptr(this, to_app(ctx.bool_var2expr(bv)), val == l_true);
                }
            }
            m_new_assignments.reset();

            if (m_new_relevant_fptr != 0) {
                for (unsigned i = 0; i < m_new_relevant_apps.size(); i++) {
                    flet<bool> invoke(m_new_relevant_invoking, true);
                    m_new_relevant_fptr(this, m_new_relevant_apps[i]);
                }
            }
            m_new_relevant_apps.reset();

            assert_axioms_into_context(old_sz);
            old_sz = m_asserted_axioms.size();
        }
        while (!m_new_eqs.empty() || !m_new_diseqs.empty() || !m_new_relevant_apps.empty() || !m_new_assignments.empty());
    }
    
    void user_theory::flush_eh() {
        reset(false);
    }

    void user_theory::reset_eh() {
        reset(true);
    }

    void user_theory::reset(bool full_reset) {
        if (m_reset_fptr != 0) {
            flet<bool> invoke(m_reset_invoking, true);
            m_reset_fptr(this);
        }
        m_trail_stack.reset();
        reset_propagation_queues();
        m_asserted_axioms.reset();
        m_asserted_axiom_set.reset();
        shrink_use_list(0);
        m_parents.reset();
        m_scopes.reset();
        m_persisted_axioms.reset();
        m_persisted_axioms_qhead = 0;
        m_stats.reset();
        if (full_reset)
            theory::reset_eh();
    }

    void user_theory::display_statistics(std::ostream & out) const {
        print_stat(out, "num. user eqs:      ", m_stats.m_num_eq);
        print_stat(out, "num. user diseq:    ", m_stats.m_num_diseq);
        print_stat(out, "num. assignments:   ", m_stats.m_num_assignment);
        print_stat(out, "num. user axioms:   ", m_stats.m_num_user_axioms);
    }

    void user_theory::display_istatistics(std::ostream & out) const {
        out << "NUM_USER_EQS   " << m_stats.m_num_eq << "\n";
        out << "NUM_USER_DISEQ " << m_stats.m_num_diseq << "\n";
        out << "NUM_ASSIGNMENTS " << m_stats.m_num_assignment << "\n";
        out << "NUM_USER_AXIOMS " << m_stats.m_num_user_axioms << "\n";
    }

    class user_smt_model_value_proc : public model_value_proc {
        func_decl_ref m_decl;
    public:
        user_smt_model_value_proc(ast_manager& m, func_decl* f) : m_decl(f, m) {}

        virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values) {
            ast_manager& m = mg.get_manager();
            return m.mk_app(m_decl, values.size(), values.c_ptr());
        }
    };

    bool user_theory::build_models() const {
        return true;
    }

    void user_theory::init_model(model_generator & m) {
        m.register_factory(alloc(user_smt_theory_factory, get_manager(), get_id()));
    }

    void user_theory::finalize_model(model_generator &) {
        // No-op
    }

    model_value_proc * user_theory::mk_value(enode * n, model_generator & mg) {
        ast_manager& m = get_manager();
        func_decl* f = n->get_decl();
        if (m_decl_plugin->is_value(f)) {
            return alloc(user_smt_model_value_proc, m, n->get_decl());
        }
        else {
            return mg.mk_model_value(n);
        }
    }

    bool user_theory::get_value(enode * n, expr_ref & r) {
        return false;
    }
    
    char const * user_theory::get_name() const {
        return m_name.c_str();
    }

    void user_theory::display(std::ostream & out) const {
        out << "Theory " << get_name() << ":\n";
    }
    
    user_theory * mk_user_theory(kernel & _s, void * ext_context, void * ext_data, char const * name) {
        context & ctx               = _s.get_context(); // HACK
        symbol _name(name);
        ast_manager & m             = ctx.get_manager();
        family_id fid               = m.mk_family_id(_name);
        user_decl_plugin * dp       = alloc(user_decl_plugin);
        m.register_plugin(fid, dp);
        simplifier & s              = ctx.get_simplifier();
        user_simplifier_plugin * sp = alloc(user_simplifier_plugin, _name, m);
        s.register_plugin(sp);
        user_theory * th            = alloc(user_theory, m, ctx.get_fparams(), ext_context, ext_data, name, fid, dp, sp);
        ctx.register_plugin(th);
        sp->set_owner(th);
        return th;
    }
};

