/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_smt_solver.cpp

Abstract:

    incremental solver based on SAT core.
    It uses the ast/simplifiers to allow incremental pre-processing that 
    produce model converters.    

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-28

Notes:


 - add back get_consequences, maybe or just have them handled by inc_sat_solver
   - could also port the layered solver used by smtfd and used by get_consequences to simplifiers

--*/


#include "util/gparams.h"
#include "ast/ast_pp.h"
#include "ast/ast_translation.h"
#include "ast/ast_util.h"
#include "solver/solver.h"
#include "model/model_smt2_pp.h"
#include "model/model_evaluator.h"
#include "sat/sat_solver.h"
#include "solver/simplifier_solver.h"
#include "params/sat_params.hpp"
#include "sat/smt/euf_solver.h"
#include "sat/tactic/goal2sat.h"
#include "sat/tactic/sat2goal.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_simplifier_params.hpp"

// incremental SAT solver.
class sat_smt_solver : public solver {

    struct dependency2assumptions {
        ast_manager&                m;
        trail_stack&                m_trail;
        expr_ref_vector             m_refs;
        obj_map<expr, expr*>        m_dep2orig; // map original dependency to uninterpreted literal

        u_map<expr*>                m_lit2dep;  // map from literal assumption to original expression
        obj_map<expr, sat::literal> m_dep2lit;  // map uninterpreted literal to sat literal
        sat::literal_vector         m_literals;
        uint_set                    m_seen;

        dependency2assumptions(ast_manager& m, trail_stack& t):
            m(m),
            m_trail(t),
            m_refs(m)
        {}

        void reset() {
            m_seen.reset();
            m_literals.reset();
            m_dep2lit.reset();
            m_lit2dep.reset();
        }

        // inserted incrementally
        void insert(expr* orig, expr* lit) {
            m_trail.push(restore_vector(m_refs));
            m_trail.push(insert_obj_map(m_dep2orig, lit));
            m_refs.push_back(lit);
            m_refs.push_back(orig);
            m_dep2orig.insert(lit, orig);
        }

        // inserted on every check-sat
        void insert(expr* dep, sat::literal lit) {
            if (m_seen.contains(lit.index()))
                return;
            m_seen.insert(lit.index());
            m_literals.push_back(lit);
            m_dep2lit.insert(dep, lit);
            m_lit2dep.insert(lit.index(), dep);
        }

        expr* lit2orig(sat::literal lit) {
            expr* e = m_lit2dep[lit.index()];
            m_dep2orig.find(e, e);
            return e;
        }

        void copy(ast_translation& tr, dependency2assumptions const& src) {
            for (auto const& [k, v] : src.m_dep2orig)
                m_dep2orig.insert(tr(k), tr(v));            
        }
    };
    
    mutable sat::solver         m_solver;
    params_ref                  m_params;
    trail_stack                 m_trail;   
    dependency2assumptions      m_dep;
    goal2sat                    m_goal2sat;
    unsigned                    m_qhead = 0;
    expr_ref_vector             m_assumptions, m_core, m_ors, m_fmls, m_internalized_fmls;
    atom2bool_var               m_map;
    mutable model_converter_ref m_cached_mc;
    mutable ref<sat2goal::mc>   m_sat_mc;
    std::string                 m_unknown = "no reason given";
    // access formulas after they have been pre-processed and handled by the sat solver.
    // this allows to access the internal state of the SAT solver and carry on partial results.
    bool                        m_internalized_converted = false; // have internalized formulas been converted back

    bool is_internalized() const { return m_qhead == m_fmls.size(); }
    
public:
    sat_smt_solver(ast_manager& m, params_ref const& p):
        solver(m),
        m_solver(p, m.limit()),
        m_dep(m, m_trail),
        m_assumptions(m), m_core(m), m_ors(m), m_fmls(m), m_internalized_fmls(m),
        m_map(m) {
        updt_params(p);
        m_solver.set_incremental(true);
    }

    solver* translate(ast_manager& dst_m, params_ref const& p) override {
        if (m_trail.get_num_scopes() > 0)
            throw default_exception("Cannot translate sat solver at non-base level");

        ast_translation tr(m, dst_m);
        m_solver.pop_to_base_level();
        sat_smt_solver* result = alloc(sat_smt_solver, dst_m, p);
        auto* ext = get_euf();
        if (ext) {
            auto& si = result->m_goal2sat.si(dst_m, m_params, result->m_solver, result->m_map, result->m_dep.m_dep2lit, true);
            euf::solver::scoped_set_translate st(*ext, dst_m, si);  
            result->m_solver.copy(m_solver);
        }
        else {
            result->m_solver.copy(m_solver);
        }
        // TODO: copy preprocess state        
        for (auto const& [k, v] : m_dep.m_dep2orig) result->m_dep.insert(tr(v), tr(k));
        for (expr* f : m_assumptions) result->m_assumptions.push_back(tr(f));
        for (auto & kv : m_map) result->m_map.insert(tr(kv.m_key), kv.m_value);
        for (expr* f : m_internalized_fmls) result->m_internalized_fmls.push_back(tr(f));
        result->m_dep.copy(tr, m_dep);
        result->m_internalized_converted = m_internalized_converted;
        return result;
    }

    void set_progress_callback(progress_callback * callback) override {}

    void init_check_sat() {
        m_solver.pop_to_base_level();
        m_core.reset();
        m_dep.reset();
        m_cached_mc = nullptr;
        init_reason_unknown();
        m_internalized_converted = false;
    }

    lbool check_sat_core(unsigned sz, expr * const * _assumptions) override {
        init_check_sat();

        if (m_solver.inconsistent())
            return l_false;

        expr_ref_vector assumptions(m);
        for (unsigned i = 0; i < sz; ++i)
            assumptions.push_back(ensure_literal(_assumptions[i]));
        TRACE("sat", tout << assumptions << "\n";);
        lbool r = internalize_formulas(assumptions);
        if (r != l_true)
            return r;

        internalize_assumptions(assumptions);
        
        try {
            r = m_solver.check(m_dep.m_literals);
        }
        catch (z3_exception& ex) {
            IF_VERBOSE(1, verbose_stream() << "exception: " << ex.what() << "\n";);
            if (m.inc()) {
                set_reason_unknown(std::string("(sat.giveup ") + ex.what() + ')');
                return l_undef;
            }
            r = l_undef;            
        }
        switch (r) {
        case l_true:
            check_assumptions();
            break;
        case l_false:
            extract_core();
            break;
        default: {
            auto* ext = get_euf();
            if (ext && ext->get_sls_model()) {
                r = l_true;
                break;
            }
            set_reason_unknown(m_solver.get_reason_unknown());
            break;
        }
        }
        return r;
    }

    void push() override {
        try {
            expr_ref_vector none(m);
            internalize_formulas(none);
        }
        catch (...) {
            push_internal();
            throw;
        }
        push_internal();
    }

    void push_internal() {   
        m_solver.user_push();
        m_goal2sat.user_push();
        m_map.push();
        m_trail.push_scope();
        m_trail.push(restore_vector(m_assumptions));
        m_trail.push(restore_vector(m_fmls));
        m_trail.push(value_trail(m_qhead));
    }

    void pop(unsigned n) override {
        n = std::min(n, m_trail.get_num_scopes()); // allow sat_smt_solver to take over for another solver.       
        m_trail.pop_scope(n);
        m_map.pop(n);
        m_goal2sat.user_pop(n);
        m_solver.user_pop(n);
    }

    void set_phase(expr* e) override { 
        bool is_not = m.is_not(e, e);
        sat::bool_var b = m_map.to_bool_var(e);
        if (b != sat::null_bool_var)
            m_solver.set_phase(sat::literal(b, is_not));
    }

    class sat_phase : public phase, public sat::literal_vector {};

    phase* get_phase() override { 
        sat_phase* p = alloc(sat_phase);
        for (unsigned v = m_solver.num_vars(); v-- > 0; ) 
            p->push_back(sat::literal(v, !m_solver.get_phase(v)));
        return p;
    }
    
    void set_phase(phase* p) override { 
        for (auto lit : *static_cast<sat_phase*>(p))
            m_solver.set_phase(lit);
    }
    
    void move_to_front(expr* e) override { 
        m.is_not(e, e);
        sat::bool_var b = m_map.to_bool_var(e);
        if (b != sat::null_bool_var)
            m_solver.move_to_front(b);
    }

    unsigned get_scope_level() const override {
        return m_trail.get_num_scopes();        
    }

    bool is_literal(expr* a) const {
        m.is_not(a, a);
        return is_uninterp_const(a);
    }

    /*
    * Ensure dependencies are literals so that pre-processing can apply to them.
    */
    expr* ensure_literal(expr* a) {
        if (is_literal(a))
            return a;
        expr* new_dep = m.mk_fresh_const("dep", m.mk_bool_sort());
        expr* fml = m.mk_iff(new_dep, a);
        m_fmls.push_back(fml);
        m_dep.insert(a, new_dep);
        return new_dep;
    }

    void assert_expr_core2(expr * t, expr * a) override {
        m_ors.reset();
        m_ors.push_back(t);
        if (m.is_and(a)) {
            for (expr* arg : *to_app(a)) {
                arg = ensure_literal(arg);
                m_ors.push_back(mk_not(m, arg));
                m_assumptions.push_back(arg);
            }
        }
        else {
            a = ensure_literal(a);
            m_assumptions.push_back(a);
            m_ors.push_back(mk_not(m, a));
        }
        flatten_or(m_ors);
        m_fmls.push_back(mk_or(m_ors));
    }

    void assert_expr_core(expr * t) override {
        m_fmls.push_back(t);
    }

    ast_manager& get_manager() const override { return m; }

    void set_produce_models(bool f) override {}
    
    void collect_param_descrs(param_descrs & r) override {
        solver::collect_param_descrs(r);
        goal2sat::collect_param_descrs(r);
        sat::solver::collect_param_descrs(r);
    }
    
    void updt_params(params_ref const & p) override {
        m_params.append(p);
        sat_params sp(p);
        m_params.set_bool("keep_cardinality_constraints", sp.cardinality_solver());
        m_params.set_sym("pb.solver", sp.pb_solver());
        m_solver.updt_params(m_params);
        m_solver.set_incremental(true);
        if (sp.smt())
            ensure_euf();
    }
    
    void collect_statistics(statistics & st) const override {
        m_solver.collect_statistics(st);
    }
    
    void get_unsat_core(expr_ref_vector & r) override {
        r.reset();
        r.append(m_core.size(), m_core.data());
    }

    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
        unsigned sz = vars.size();
        depth.resize(sz);
        for (unsigned i = 0; i < sz; ++i) {
            auto bv = m_map.to_bool_var(vars[i]);
            depth[i] = bv == sat::null_bool_var ? UINT_MAX : m_solver.lvl(bv);
        }
    }

    expr_ref_vector get_trail(unsigned max_level) override {
        expr_ref_vector result(m), lit2expr(m);
        unsigned sz = m_solver.trail_size();
        lit2expr.resize(m_solver.num_vars() * 2);
        m_map.mk_inv(lit2expr);
        for (unsigned i = 0; i < sz; ++i) {
            sat::literal lit = m_solver.trail_literal(i);
            if (m_solver.lvl(lit) > max_level)
                continue;
            expr_ref e(lit2expr.get(lit.index()), m);
            if (e)
                result.push_back(e);
        }
        return result;
    }

    proof * get_proof_core() override {
        return nullptr;
    }

    expr_ref_vector last_cube(bool is_sat) {
        expr_ref_vector result(m);
        result.push_back(is_sat ? m.mk_true() : m.mk_false());
        return result;
    }

    expr_ref_vector cube(expr_ref_vector& vs, unsigned backtrack_level) override {
        lbool r = internalize_formulas(vs);
        if (r != l_true) {
            IF_VERBOSE(0, verbose_stream() << "internalize produced " << r << "\n");
            return expr_ref_vector(m);
        }
        convert_internalized();
        if (m_solver.inconsistent())
            return last_cube(false);
        obj_hashtable<expr> _vs;
        for (expr* v : vs)
            _vs.insert(v);
        sat::bool_var_vector vars;
        for (auto& kv : m_map) 
            if (_vs.empty() || _vs.contains(kv.m_key))
                vars.push_back(kv.m_value);
        sat::literal_vector lits;
        lbool result = m_solver.cube(vars, lits, backtrack_level);
        expr_ref_vector fmls(m);
        expr_ref_vector lit2expr(m);
        lit2expr.resize(m_solver.num_vars() * 2);
        m_map.mk_inv(lit2expr);
        for (sat::literal l : lits) {
            expr* e = lit2expr.get(l.index());
            SASSERT(e);
            fmls.push_back(e);
        }
        vs.reset();
        for (sat::bool_var v : vars) {
            expr* x = lit2expr[sat::literal(v, false).index()].get();
            if (x) 
                vs.push_back(x);
        }
        switch (result) {
        case l_true:
            return last_cube(true);
        case l_false: 
            return last_cube(false);
        default: 
            break;
        }
        if (lits.empty()) 
            set_reason_unknown(m_solver.get_reason_unknown());
        return fmls;
    }

    expr* congruence_next(expr* e) override { return e; }
    expr* congruence_root(expr* e) override { return e; }
    expr_ref congruence_explain(expr* a, expr* b) override { return expr_ref(m.mk_eq(a, b), m); }
    

    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override {
        sat::literal_vector ls;
        u_map<expr*> lit2var;
        for (expr * e : vars) {
            expr* atom = e;;
            bool neg = m.is_not(e, atom);
            sat::bool_var v = m_map.to_bool_var(atom);
            if (v != sat::null_bool_var) {
                sat::literal lit(v, neg);
                ls.push_back(lit);
                lit2var.insert(lit.index(), e);
            }
        }
        vector<sat::literal_vector> ls_mutexes;
        m_solver.find_mutexes(ls, ls_mutexes);
        for (sat::literal_vector const& ls_mutex : ls_mutexes) {
            expr_ref_vector mutex(m);
            for (sat::literal l : ls_mutex) 
                mutex.push_back(lit2var.find(l.index()));            
            mutexes.push_back(mutex);
        }
        return l_true;
    }

    void init_reason_unknown() {
        m_unknown = "no reason given";
    }

    std::string reason_unknown() const override {
        return m_unknown;
    }

    void set_reason_unknown(char const* msg) override {
        m_unknown = msg;
    }

    void set_reason_unknown(std::string &&msg) {
        m_unknown = std::move(msg);
    }

    void get_labels(svector<symbol> & r) override {
    }

    unsigned get_num_assertions() const override {
        const_cast<sat_smt_solver*>(this)->convert_internalized();
        if (is_internalized() && m_internalized_converted)             
            return m_internalized_fmls.size();
        else 
            return m_fmls.size();
    }

    expr * get_assertion(unsigned idx) const override {
        if (is_internalized() && m_internalized_converted) 
            return m_internalized_fmls[idx];
        return m_fmls.get(idx);
    }

    unsigned get_num_assumptions() const override {
        return m_assumptions.size();
    }

    expr * get_assumption(unsigned idx) const override {
        return m_assumptions[idx];
    }

    model_converter_ref get_model_converter() const override {
        const_cast<sat_smt_solver*>(this)->convert_internalized();
        if (m_cached_mc)
            return m_cached_mc;
        if (is_internalized() && m_internalized_converted) {            
            if (m_sat_mc) m_sat_mc->flush_smc(m_solver, m_map);
            m_cached_mc = concat(solver::get_model_converter().get(), m_sat_mc.get());
            TRACE("sat", m_cached_mc->display(tout););
            return m_cached_mc;
        }
        else {
            return solver::get_model_converter();
        }
    }

    void convert_internalized() {
        m_solver.pop_to_base_level();
        expr_ref_vector none(m);
        internalize_formulas(none);        
        if (!is_internalized() || m_internalized_converted) 
            return;
        sat2goal s2g;
        m_cached_mc = nullptr;
        goal g(m, false, true, false);
        s2g(m_solver, m_map, m_params, g, m_sat_mc);
        m_internalized_fmls.reset();
        g.get_formulas(m_internalized_fmls);
        TRACE("sat", m_solver.display(tout); tout << m_internalized_fmls << "\n";);
        m_internalized_converted = true;
    }

    euf::solver* get_euf() {
        return dynamic_cast<euf::solver*>(m_solver.get_extension());
    }

    void init_goal2sat() {
        m_goal2sat.init(m, m_params, m_solver, m_map, m_dep.m_dep2lit, true);      
    }

    euf::solver* ensure_euf() {
        init_goal2sat();        
        return m_goal2sat.ensure_euf();
    }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        ensure_euf()->register_on_clause(ctx, on_clause);
    }
    
    void user_propagate_init(
        void*                ctx, 
        user_propagator::push_eh_t&   push_eh,
        user_propagator::pop_eh_t&    pop_eh,
        user_propagator::fresh_eh_t&  fresh_eh) override {
        ensure_euf()->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }
        
    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override {
        ensure_euf()->user_propagate_register_fixed(fixed_eh);
    }
    
    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override {
        ensure_euf()->user_propagate_register_final(final_eh);
    }
    
    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override {
        ensure_euf()->user_propagate_register_eq(eq_eh);
    }
    
    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override {
        ensure_euf()->user_propagate_register_diseq(diseq_eh);
    }
    
    void user_propagate_register_expr(expr* e) override { 
        ensure_euf()->user_propagate_register_expr(e);
    }

    void user_propagate_register_created(user_propagator::created_eh_t& r) override {
        ensure_euf()->user_propagate_register_created(r);
    }

    void user_propagate_register_decide(user_propagator::decide_eh_t& r) override {
        ensure_euf()->user_propagate_register_decide(r);
    }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        ensure_euf()->user_propagate_initialize_value(var, value);
    }


private:

    void add_assumption(expr* a) {
        init_goal2sat();
        auto lit = m_goal2sat.internalize(a);
        m_dep.insert(a, lit);
        get_euf()->add_clause(1, &lit);
    }

    void internalize_assumptions(expr_ref_vector const& asms) {     
        for (expr* a : asms)
            add_assumption(a);
        for (expr* a : m_assumptions)
            add_assumption(a);
    }

    lbool internalize_formulas(expr_ref_vector& assumptions) {

        if (is_internalized() && assumptions.empty())
            return l_true;

        TRACE("sat", tout << "qhead " << m_qhead << "\n");

        m_internalized_converted = false;

        m_solver.pop_to_base_level();
        init_goal2sat();
        m_goal2sat(m_fmls.size() - m_qhead, m_fmls.data() + m_qhead);
        if (!m_sat_mc)
            m_sat_mc = alloc(sat2goal::mc, m);
        m_sat_mc->flush_smc(m_solver, m_map);
        m_qhead = m_fmls.size();
        return m.inc() ? l_true : l_undef;
    }

    void extract_core() {
        m_core.reset();
        if (m_dep.m_literals.empty())
            return;
        for (sat::literal c : m_solver.get_core()) 
            m_core.push_back(m_dep.lit2orig(c));
        TRACE("sat",
              tout << "core: " << m_solver.get_core() << "\n";
              tout << "core: " << m_core << "\n";
              m_solver.display(tout));
    }

    void check_assumptions() {
        sat::model const& ll_m = m_solver.get_model();
        for (auto const& [k, lit] : m_dep.m_dep2lit) {
            if (sat::value_at(lit, ll_m) == l_true)
                continue;
            IF_VERBOSE(0, verbose_stream() << mk_pp(k, m) << " does not evaluate to true\n";
            verbose_stream() << m_dep.m_literals << "\n";
            m_solver.display_assignment(verbose_stream());
            m_solver.display(verbose_stream()););
            throw default_exception("bad state");
        }
    }

    void get_model_core(model_ref & mdl) override {
        TRACE("sat", tout << "retrieve model " << (m_solver.model_is_current()?"present":"absent") << "\n";);
        mdl = nullptr;
        auto ext = get_euf();
        if (ext)
            mdl = ext->get_sls_model();
        if (mdl)
            return;
        if (!m_solver.model_is_current()) 
            return;
        if (m_fmls.size() > m_qhead)
            return;
        TRACE("sat", m_solver.display_model(tout););
        CTRACE("sat", m_sat_mc, m_sat_mc->display(tout););
        sat::model ll_m = m_solver.get_model();
        mdl = alloc(model, m);
        if (m_sat_mc) 
            (*m_sat_mc)(ll_m);
        expr_ref_vector var2expr(m);
        m_map.mk_var_inv(var2expr);
        
        for (unsigned v = 0; v < var2expr.size(); ++v) {
            expr * n = var2expr.get(v);
            if (!n || !is_uninterp_const(n)) 
                continue;            
            switch (sat::value_at(v, ll_m)) {
            case l_true:
                mdl->register_decl(to_app(n)->get_decl(), m.mk_true());
                break;
            case l_false:
                mdl->register_decl(to_app(n)->get_decl(), m.mk_false());
                break;
            default:
                break;
            }
        }

        TRACE("sat", m_solver.display(tout););
        if (m_sat_mc) 
            (*m_sat_mc)(mdl);
        m_goal2sat.update_model(mdl);
    
        TRACE("sat", model_smt2_pp(tout, m, *mdl, 0););        

        if (gparams::get_ref().get_bool("model_validate", false)) {
            IF_VERBOSE(1, verbose_stream() << "Verifying solution\n";);
            model_evaluator eval(*mdl);
            eval.set_model_completion(true);
            bool all_true = true;
            for (expr* f : m_fmls) {
                if (has_quantifiers(f))
                    continue;
                expr_ref tmp(m);
                eval(f, tmp);
                if (m.limit().is_canceled())
                    return;
                CTRACE("sat", !m.is_true(tmp),
                       tout << "Evaluation failed: " << mk_pp(f, m) << " to " << tmp << "\n";
                       model_smt2_pp(tout, m, *(mdl.get()), 0););
                if (m.is_false(tmp)) {
                    IF_VERBOSE(0, verbose_stream() << "failed to verify: " << mk_pp(f, m) << "\n");
                    IF_VERBOSE(0, verbose_stream() << "evaluated to " << tmp << "\n");
                    all_true = false;
                }
            }
            if (!all_true) {
                IF_VERBOSE(0, verbose_stream() << m_params << "\n");
                IF_VERBOSE(0, for (auto const& kv : m_map) verbose_stream() << mk_pp(kv.m_key, m) << " |-> " << kv.m_value << "\n");
                exit(0);
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "solution verified\n");
            }
        }
    }
};


solver* mk_sat_smt_solver(ast_manager& m, params_ref const& p) {
    return mk_simplifier_solver(alloc(sat_smt_solver, m, p), nullptr);
}

