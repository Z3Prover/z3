/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    inc_sat_solver.cpp

Abstract:

    incremental solver based on SAT core.

Author:

    Nikolaj Bjorner (nbjorner) 2014-7-30

Notes:

--*/


#include "util/gparams.h"
#include "util/stacked_value.h"
#include "ast/ast_pp.h"
#include "ast/ast_translation.h"
#include "ast/ast_util.h"
#include "solver/solver.h"
#include "solver/tactic2solver.h"
#include "solver/parallel_params.hpp"
#include "solver/parallel_tactic.h"
#include "tactic/tactical.h"
#include "tactic/aig/aig_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/arith/card2bv_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/bv/bit_blaster_model_converter.h"
#include "model/model_smt2_pp.h"
#include "model/model_v2_pp.h"
#include "model/model_evaluator.h"
#include "sat/sat_solver.h"
#include "sat/sat_params.hpp"
#include "sat/smt/euf_solver.h"
#include "sat/tactic/goal2sat.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_simplifier_params.hpp"

// incremental SAT solver.
class inc_sat_solver : public solver {
    ast_manager&    m;
    mutable sat::solver     m_solver;
    stacked_value<bool> m_has_uninterpreted;
    goal2sat        m_goal2sat;
    params_ref      m_params;
    expr_ref_vector m_fmls;
    expr_ref_vector m_asmsf;
    unsigned_vector m_fmls_lim;
    unsigned_vector m_asms_lim;
    unsigned_vector m_fmls_head_lim;
    unsigned            m_fmls_head;
    expr_ref_vector     m_core;
    atom2bool_var       m_map;
    scoped_ptr<bit_blaster_rewriter> m_bb_rewriter;
    tactic_ref          m_preprocess;
    bool                m_is_cnf;
    unsigned            m_num_scopes;
    sat::literal_vector m_asms;
    goal_ref_buffer     m_subgoals;
    proof_converter_ref m_pc;
    sref_vector<model_converter> m_mcs;
    mutable model_converter_ref m_mc0;         // TBD: should be saved/retained under push/pop
    mutable obj_hashtable<func_decl>  m_inserted_const2bits;
    mutable ref<sat2goal::mc>   m_sat_mc;
    mutable model_converter_ref m_cached_mc;
    svector<double>     m_weights;
    std::string         m_unknown;
    // access formulas after they have been pre-processed and handled by the sat solver.
    // this allows to access the internal state of the SAT solver and carry on partial results.
    bool                m_internalized_converted; // have internalized formulas been converted back
    expr_ref_vector     m_internalized_fmls;      // formulas in internalized format

    typedef obj_map<expr, sat::literal> dep2asm_t;

    dep2asm_t          m_dep2asm;

    bool is_internalized() const { return m_fmls_head == m_fmls.size(); }
public:
    inc_sat_solver(ast_manager& m, params_ref const& p, bool incremental_mode):
        m(m), 
        m_solver(p, m.limit()),
        m_has_uninterpreted(false),
        m_fmls(m),
        m_asmsf(m),
        m_fmls_head(0),
        m_core(m),
        m_map(m),
        m_is_cnf(true),
        m_num_scopes(0),
        m_unknown("no reason given"),
        m_internalized_converted(false), 
        m_internalized_fmls(m) {
        updt_params(p);
        m_mcs.push_back(nullptr);
        init_preprocess();
        m_solver.set_incremental(incremental_mode && !override_incremental());
    }

    bool override_incremental() const {
        sat_simplifier_params p(m_params);
        return p.override_incremental();
    }

    bool is_incremental() const {
        return m_solver.get_config().m_incremental;
    }

    ~inc_sat_solver() override {}

    solver* translate(ast_manager& dst_m, params_ref const& p) override {
        if (m_num_scopes > 0) {
            throw default_exception("Cannot translate sat solver at non-base level");
        }
        ast_translation tr(m, dst_m);
        m_solver.pop_to_base_level();
        inc_sat_solver* result = alloc(inc_sat_solver, dst_m, p, is_incremental());
        auto* ext = get_euf();
        if (ext) {
            auto& si = result->m_goal2sat.si(dst_m, m_params, result->m_solver, result->m_map, result->m_dep2asm, is_incremental());
            euf::solver::scoped_set_translate st(*ext, dst_m, si);  
            result->m_solver.copy(m_solver);
        }        
        else {
            result->m_solver.copy(m_solver);
        }
        result->m_fmls_head = m_fmls_head;
        for (expr* f : m_fmls) result->m_fmls.push_back(tr(f));
        for (expr* f : m_asmsf) result->m_asmsf.push_back(tr(f));
        for (auto & kv : m_map) result->m_map.insert(tr(kv.m_key), kv.m_value);
        for (unsigned l : m_fmls_lim) result->m_fmls_lim.push_back(l);
        for (unsigned a : m_asms_lim) result->m_asms_lim.push_back(a);
        for (unsigned h : m_fmls_head_lim) result->m_fmls_head_lim.push_back(h);
        for (expr* f : m_internalized_fmls) result->m_internalized_fmls.push_back(tr(f));
        if (m_mcs.back()) result->m_mcs.push_back(m_mcs.back()->translate(tr));
        if (m_sat_mc) result->m_sat_mc = dynamic_cast<sat2goal::mc*>(m_sat_mc->translate(tr));
        result->m_has_uninterpreted = m_has_uninterpreted;
        // copy m_bb_rewriter?
        result->m_internalized_converted = m_internalized_converted;
        return result;
    }

    void set_progress_callback(progress_callback * callback) override {}

    void display_weighted(std::ostream& out, unsigned sz, expr * const * assumptions, unsigned const* weights) {
        if (weights != nullptr) {
            for (unsigned i = 0; i < sz; ++i) m_weights.push_back(weights[i]);
        }
        init_preprocess();
        m_solver.pop_to_base_level();
        m_dep2asm.reset();
        expr_ref_vector asms(m);
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref a(m.mk_fresh_const("s", m.mk_bool_sort()), m);
            expr_ref fml(m.mk_implies(a, assumptions[i]), m);
            assert_expr(fml);
            asms.push_back(a);
        }
        VERIFY(l_true == internalize_formulas());
        VERIFY(l_true == internalize_assumptions(sz, asms.data()));
        svector<unsigned> nweights;
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            nweights.push_back((unsigned) m_weights[i]);
        }
        m_weights.reset();
        m_solver.display_wcnf(out, m_asms.size(), m_asms.data(), nweights.data());
    }

    bool is_literal(expr* e) const {
        return
            is_uninterp_const(e) ||
            (m.is_not(e, e) && is_uninterp_const(e));
    }

    lbool check_sat_core(unsigned sz, expr * const * assumptions) override {
        m_solver.pop_to_base_level();
        m_core.reset();
        if (m_solver.inconsistent()) return l_false;
        expr_ref_vector _assumptions(m);
        obj_map<expr, expr*> asm2fml;
        for (unsigned i = 0; i < sz; ++i) {
            if (!is_literal(assumptions[i])) {
                expr_ref a(m.mk_fresh_const("s", m.mk_bool_sort()), m);
                expr_ref fml(m.mk_eq(a, assumptions[i]), m);
                assert_expr(fml);
                _assumptions.push_back(a);
                asm2fml.insert(a, assumptions[i]);
            }
            else {
                _assumptions.push_back(assumptions[i]);
                asm2fml.insert(assumptions[i], assumptions[i]);
            }
        }

        TRACE("sat", tout << _assumptions << "\n";);
        m_dep2asm.reset();
        lbool r = internalize_formulas();
        if (r != l_true) return r;
        r = internalize_assumptions(sz, _assumptions.data());
        if (r != l_true) return r;

        init_reason_unknown();
        m_internalized_converted = false;
        bool reason_set = false;
        try {
            // IF_VERBOSE(0, m_solver.display(verbose_stream()));
            r = m_solver.check(m_asms.size(), m_asms.data());
        }
        catch (z3_exception& ex) {
            IF_VERBOSE(1, verbose_stream() << "exception: " << ex.msg() << "\n";);
            if (m.inc()) {
                reason_set = true;
                set_reason_unknown(std::string("(sat.giveup ") + ex.msg() + ')');
            }
            r = l_undef;            
        }
        switch (r) {
        case l_true:
            if (m_has_uninterpreted()) {
                set_reason_unknown("(sat.giveup has-uninterpreted)");
                r = l_undef;
            }
            else if (sz > 0) {
                check_assumptions();
            }
            break;
        case l_false:
            // TBD: expr_dependency core is not accounted for.
            if (!m_asms.empty()) {
                extract_core(asm2fml);
            }
            break;
        default:
            if (!reason_set) {
                set_reason_unknown(m_solver.get_reason_unknown());
            }
            break;
        }
        return r;
    }

    void push() override {
        try {
            internalize_formulas();
        }
        catch (...) {
            push_internal();
            throw;
        }
        push_internal();
    }

    void push_internal() {
        m_goal2sat.user_push();
        m_solver.user_push();
        ++m_num_scopes;
        m_mcs.push_back(m_mcs.back());
        m_fmls_lim.push_back(m_fmls.size());
        m_asms_lim.push_back(m_asmsf.size());
        m_fmls_head_lim.push_back(m_fmls_head);
        if (m_bb_rewriter) m_bb_rewriter->push();
        m_map.push();
        m_has_uninterpreted.push();
    }

    void pop(unsigned n) override {
        if (n > m_num_scopes) {   // allow inc_sat_solver to
            n = m_num_scopes;     // take over for another solver.
        }
        if (m_bb_rewriter) m_bb_rewriter->pop(n);
        m_inserted_const2bits.reset();
        m_map.pop(n);
        SASSERT(n <= m_num_scopes);
        m_solver.user_pop(n);
        m_goal2sat.user_pop(n);
        m_num_scopes -= n;
        // ? m_internalized_converted = false;
        m_has_uninterpreted.pop(n);
        while (n > 0) {
            m_mcs.pop_back();
            m_fmls_head = m_fmls_head_lim.back();
            m_fmls.resize(m_fmls_lim.back());
            m_fmls_lim.pop_back();
            m_fmls_head_lim.pop_back();
            m_asmsf.resize(m_asms_lim.back());
            m_asms_lim.pop_back();
            --n;
        }
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
        for (unsigned v = m_solver.num_vars(); v-- > 0; ) {
            p->push_back(sat::literal(v, !m_solver.get_phase(v)));
        }
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
        return m_num_scopes;
    }

    void assert_expr_core2(expr * t, expr * a) override {        
        if (a) {
            m_asmsf.push_back(a);
            if (m_is_cnf && is_literal(t) && is_literal(a)) {
                assert_expr_core(m.mk_or(::mk_not(m, a), t));
            }
            else if (m_is_cnf && m.is_or(t) && is_clause(t) && is_literal(a)) {
                expr_ref_vector args(m);
                args.push_back(::mk_not(m, a));
                args.append(to_app(t)->get_num_args(), to_app(t)->get_args());
                assert_expr_core(m.mk_or(args.size(), args.data()));
            }
            else {
                m_is_cnf = false;
                assert_expr_core(m.mk_implies(a, t));
            }
        }
        else {
            assert_expr_core(t);
        }
    }

    ast_manager& get_manager() const override { return m; }
    void assert_expr_core(expr * t) override {
        TRACE("goal2sat", tout << mk_pp(t, m) << "\n";);
        m_is_cnf &= is_clause(t);
        m_fmls.push_back(t);
    }
    void set_produce_models(bool f) override {}
    void collect_param_descrs(param_descrs & r) override {
        solver::collect_param_descrs(r);
        goal2sat::collect_param_descrs(r);
        sat::solver::collect_param_descrs(r);
    }
    void updt_params(params_ref const & p) override {
        m_params.append(p);
        sat_params p1(p);
        m_params.set_bool("keep_cardinality_constraints", p1.cardinality_solver());
        m_params.set_sym("pb.solver", p1.pb_solver());
        m_solver.updt_params(m_params);
        m_solver.set_incremental(is_incremental() && !override_incremental());
        if (p1.euf() && !get_euf()) 
            ensure_euf();        
    }
    void collect_statistics(statistics & st) const override {
        if (m_preprocess) m_preprocess->collect_statistics(st);
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

    expr_ref_vector get_trail() override {
        expr_ref_vector result(m);
        unsigned sz = m_solver.trail_size();
        expr_ref_vector lit2expr(m);
        lit2expr.resize(m_solver.num_vars() * 2);
        m_map.mk_inv(lit2expr);
        for (unsigned i = 0; i < sz; ++i) {
            sat::literal lit = m_solver.trail_literal(i);
            result.push_back(lit2expr[lit.index()].get());
        }
        return result;
    }

    proof * get_proof() override {
        return nullptr;
    }

    expr_ref_vector last_cube(bool is_sat) {
        expr_ref_vector result(m);
        result.push_back(is_sat ? m.mk_true() : m.mk_false());
        return result;
    }

    expr_ref_vector cube(expr_ref_vector& vs, unsigned backtrack_level) override {
        if (!is_internalized()) {
            lbool r = internalize_formulas();
            if (r != l_true) {
                IF_VERBOSE(0, verbose_stream() << "internalize produced " << r << "\n");
                return expr_ref_vector(m);
            }
        }
        convert_internalized();
        if (m_solver.inconsistent())
            return last_cube(false);
        obj_hashtable<expr> _vs;
        for (expr* v : vs) _vs.insert(v);
        sat::bool_var_vector vars;
        for (auto& kv : m_map) {
            if (_vs.empty() || _vs.contains(kv.m_key))
                vars.push_back(kv.m_value);
        }
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
            if (x) {
                vs.push_back(x);
            }
        }
        switch (result) {
        case l_true:
            return last_cube(true);
        case l_false: 
            return last_cube(false);
        default: 
            break;
        }
        if (lits.empty()) {
            set_reason_unknown(m_solver.get_reason_unknown());
        }
        return fmls;
    }
    
    lbool get_consequences_core(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq) override {
        init_preprocess();
        TRACE("sat", tout << assumptions << "\n" << vars << "\n";);
        sat::literal_vector asms;
        sat::bool_var_vector bvars;
        vector<sat::literal_vector> lconseq;
        m_dep2asm.reset();
        obj_map<expr, expr*> asm2fml;
        m_solver.pop_to_base_level();
        lbool r = internalize_formulas();
        if (r != l_true) return r;
        r = internalize_vars(vars, bvars);
        if (r != l_true) return r;
        r = internalize_assumptions(assumptions.size(), assumptions.data());
        if (r != l_true) return r;
        r = m_solver.get_consequences(m_asms, bvars, lconseq);
        if (r == l_false) {
            if (!m_asms.empty()) {
                extract_core(asm2fml);
            }
            return r;
        }

        // build map from bound variables to
        // the consequences that cover them.
        u_map<unsigned> bool_var2conseq;
        for (unsigned i = 0; i < lconseq.size(); ++i) {
            TRACE("sat", tout << lconseq[i] << "\n";);
            bool_var2conseq.insert(lconseq[i][0].var(), i);
        }

        // extract original fixed variables
        u_map<expr*> asm2dep;
        extract_asm2dep(asm2dep);
        for (auto v : vars) {
            expr_ref cons(m);
            if (extract_fixed_variable(asm2dep, v, bool_var2conseq, lconseq, cons)) {
                conseq.push_back(cons);
            }
        }
        return r;
    }

    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override {
        sat::literal_vector ls;
        u_map<expr*> lit2var;
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr* e = vars[i];
            bool neg = m.is_not(e, e);
            sat::bool_var v = m_map.to_bool_var(e);
            if (v != sat::null_bool_var) {
                sat::literal lit(v, neg);
                ls.push_back(lit);
                lit2var.insert(lit.index(), vars[i]);
            }
        }
        vector<sat::literal_vector> ls_mutexes;
        m_solver.find_mutexes(ls, ls_mutexes);
        for (sat::literal_vector const& ls_mutex : ls_mutexes) {
            expr_ref_vector mutex(m);
            for (sat::literal l : ls_mutex) {
                mutex.push_back(lit2var.find(l.index()));
            }
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
        const_cast<inc_sat_solver*>(this)->convert_internalized();
        if (is_internalized() && m_internalized_converted) {            
            return m_internalized_fmls.size();
        }
        else {
            return m_fmls.size();
        }
    }

    expr * get_assertion(unsigned idx) const override {
        if (is_internalized() && m_internalized_converted) {
            return m_internalized_fmls[idx];
        }
        return m_fmls[idx];
    }

    unsigned get_num_assumptions() const override {
        return m_asmsf.size();
    }

    expr * get_assumption(unsigned idx) const override {
        return m_asmsf[idx];
    }

    model_converter_ref get_model_converter() const override {
        const_cast<inc_sat_solver*>(this)->convert_internalized();
        if (m_cached_mc)
            return m_cached_mc;
        if (is_internalized() && m_internalized_converted) {            
            m_sat_mc->flush_smc(m_solver, m_map);
            m_cached_mc = m_mcs.back();
            m_cached_mc = concat(solver::get_model_converter().get(), m_cached_mc.get());
            m_cached_mc = concat(m_cached_mc.get(), m_sat_mc.get());
            TRACE("sat", m_cached_mc->display(tout););
            return m_cached_mc;
        }
        else {
            return solver::get_model_converter();
        }
    }

    void convert_internalized() {
        m_solver.pop_to_base_level();
        if (!is_internalized() && m_fmls_head > 0) {
            internalize_formulas();
        }
        if (!is_internalized() || m_internalized_converted) return;
        sat2goal s2g;
        m_cached_mc = nullptr;
        goal g(m, false, true, false);
        s2g(m_solver, m_map, m_params, g, m_sat_mc);
        m_internalized_fmls.reset();
        g.get_formulas(m_internalized_fmls);
        TRACE("sat", m_solver.display(tout); tout << m_internalized_fmls << "\n";);
        m_internalized_converted = true;
    }

    void init_preprocess() {
        if (m_preprocess) {
            m_preprocess->reset();
        }
        if (!m_bb_rewriter) {
            m_bb_rewriter = alloc(bit_blaster_rewriter, m, m_params);
        }
        params_ref simp1_p = m_params;
        simp1_p.set_bool("som", true);
        simp1_p.set_bool("pull_cheap_ite", true);
        simp1_p.set_bool("push_ite_bv", false);
        simp1_p.set_bool("local_ctx", true);
        simp1_p.set_uint("local_ctx_limit", 10000000);
        simp1_p.set_bool("flat", true); // required by som
        simp1_p.set_bool("hoist_mul", false); // required by som
        simp1_p.set_bool("elim_and", true);
        simp1_p.set_bool("blast_distinct", true);

        params_ref simp2_p = m_params;
        simp2_p.set_bool("flat", false);

        sat_params sp(m_params);
        if (sp.euf()) 
            m_preprocess =
                and_then(mk_simplify_tactic(m),
                         mk_propagate_values_tactic(m));
        else 
            m_preprocess =
                and_then(mk_simplify_tactic(m),
                         mk_propagate_values_tactic(m),
                         mk_card2bv_tactic(m, m_params),                  // updates model converter
                         using_params(mk_simplify_tactic(m), simp1_p),
                         mk_max_bv_sharing_tactic(m),
                         mk_bit_blaster_tactic(m, m_bb_rewriter.get()),
                         using_params(mk_simplify_tactic(m), simp2_p)
                         );
        while (m_bb_rewriter->get_num_scopes() < m_num_scopes) {
            m_bb_rewriter->push();
        }
        m_preprocess->reset();
    }

    euf::solver* get_euf() {
        return dynamic_cast<euf::solver*>(m_solver.get_extension());
    }

    euf::solver* ensure_euf() {
        auto* ext = dynamic_cast<euf::solver*>(m_solver.get_extension());
        return ext;
    }

    void user_propagate_init(
        void*                ctx, 
        solver::push_eh_t&   push_eh,
        solver::pop_eh_t&    pop_eh,
        solver::fresh_eh_t&  fresh_eh) override {
        ensure_euf()->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }
        
    void user_propagate_register_fixed(solver::fixed_eh_t& fixed_eh) override {
        ensure_euf()->user_propagate_register_fixed(fixed_eh);
    }
    
    void user_propagate_register_final(solver::final_eh_t& final_eh) override {
        ensure_euf()->user_propagate_register_final(final_eh);
    }
    
    void user_propagate_register_eq(solver::eq_eh_t& eq_eh) override {
        ensure_euf()->user_propagate_register_eq(eq_eh);
    }
    
    void user_propagate_register_diseq(solver::eq_eh_t& diseq_eh) override {
        ensure_euf()->user_propagate_register_diseq(diseq_eh);
    }
    
    unsigned user_propagate_register(expr* e) override { 
        return ensure_euf()->user_propagate_register(e);
    }

private:

    lbool internalize_goal(goal_ref& g) {        
        m_solver.pop_to_base_level();
        if (m_solver.inconsistent()) 
            return l_false;
        
        m_pc.reset();
        m_subgoals.reset();
        init_preprocess();
        SASSERT(g->models_enabled());
        if (g->proofs_enabled()) {
            throw default_exception("generation of proof objects is not supported in this mode");
        }
        SASSERT(!g->proofs_enabled());
        TRACE("sat", m_solver.display(tout); g->display(tout););
        try {
            if (m_is_cnf) {
                m_subgoals.push_back(g.get());
            }
            else {
                (*m_preprocess)(g, m_subgoals);
            }
        }
        catch (tactic_exception & ex) {
            IF_VERBOSE(1, verbose_stream() << "exception in tactic " << ex.msg() << "\n";);
            set_reason_unknown(ex.msg());
            TRACE("sat", tout << "exception: " << ex.msg() << "\n";);
            m_preprocess = nullptr;
            m_bb_rewriter = nullptr;
            return l_undef;
        }        
        catch (...) {
            m_preprocess = nullptr;
            m_bb_rewriter = nullptr;
            throw;
        }
        if (m_subgoals.size() != 1) {
            IF_VERBOSE(0, verbose_stream() << "size of subgoals is not 1, it is: " << m_subgoals.size() << "\n");
            return l_undef;
        }
        g = m_subgoals[0];
        func_decl_ref_vector funs(m);
        m_pc = g->pc();
        m_mcs.set(m_mcs.size()-1, concat(m_mcs.back(), g->mc()));
        TRACE("sat", g->display_with_dependencies(tout););

        // ensure that if goal is already internalized, then import mc from m_solver.

        m_goal2sat(*g, m_params, m_solver, m_map, m_dep2asm, is_incremental());
        m_goal2sat.get_interpreted_funs(funs);
        if (!m_sat_mc) m_sat_mc = alloc(sat2goal::mc, m);
        m_sat_mc->flush_smc(m_solver, m_map);
        if (!funs.empty()) {
            m_has_uninterpreted = true;
            std::stringstream strm;
            strm << "(sat.giveup interpreted functions sent to SAT solver " << funs <<")";
            TRACE("sat", tout << strm.str() << "\n";);
            IF_VERBOSE(1, verbose_stream() << strm.str() << "\n";);
            set_reason_unknown(strm.str());
            return l_undef;
        }
        return l_true;
    }

    lbool internalize_assumptions(unsigned sz, expr* const* asms) {
        if (sz == 0 && get_num_assumptions() == 0) {
            m_asms.shrink(0);
            return l_true;
        }
        goal_ref g = alloc(goal, m, true, true); // models and cores are enabled.
        for (unsigned i = 0; i < sz; ++i) {
            g->assert_expr(asms[i], m.mk_leaf(asms[i]));
        }
        for (unsigned i = 0; i < get_num_assumptions(); ++i) {
            g->assert_expr(get_assumption(i), m.mk_leaf(get_assumption(i)));
        }
        lbool res = internalize_goal(g);
        if (res == l_true) {
            extract_assumptions(sz, asms);
        }
        return res;
    }

    lbool internalize_vars(expr_ref_vector const& vars, sat::bool_var_vector& bvars) {
        for (expr* v : vars) {
            internalize_var(v, bvars);
        }
        return l_true;
    }

    bool internalize_var(expr* v, sat::bool_var_vector& bvars) {
        obj_map<func_decl, expr*> const2bits;
        ptr_vector<func_decl> newbits;
        m_bb_rewriter->get_translation(const2bits, newbits);
        expr* bv;
        bv_util bvutil(m);
        bool internalized = false;
        if (is_uninterp_const(v) && m.is_bool(v)) {
            sat::bool_var b = m_map.to_bool_var(v);
            if (b != sat::null_bool_var) {
                bvars.push_back(b);
                internalized = true;
            }
        }
        else if (is_uninterp_const(v) && const2bits.find(to_app(v)->get_decl(), bv)) {
            SASSERT(bvutil.is_bv(bv));
            app* abv = to_app(bv);
            internalized = true;
            for (expr* arg : *abv) {
                SASSERT(is_uninterp_const(arg));
                sat::bool_var b = m_map.to_bool_var(arg);
                if (b == sat::null_bool_var) {
                    internalized = false;
                }
                else {
                    bvars.push_back(b);
                }
            }
            CTRACE("sat", internalized, tout << "var: " << bvars << "\n";);
        }
        else if (is_uninterp_const(v) && bvutil.is_bv(v)) {
            // variable does not occur in assertions, so is unconstrained.
        }
        CTRACE("sat", !internalized, tout << "unhandled variable " << mk_pp(v, m) << "\n";);
        return internalized;
    }

    bool extract_fixed_variable(u_map<expr*>& asm2dep, expr* v, u_map<unsigned> const& bool_var2conseq, vector<sat::literal_vector> const& lconseq, expr_ref& conseq) {

        sat::bool_var_vector bvars;
        if (!internalize_var(v, bvars)) {
            return false;
        }
        sat::literal_vector value;
        sat::literal_set premises;
        for (sat::bool_var bv : bvars) {
            unsigned index;
            if (bool_var2conseq.find(bv, index)) {
                value.push_back(lconseq[index][0]);
                for (unsigned j = 1; j < lconseq[index].size(); ++j) {
                    premises.insert(lconseq[index][j]);
                }
            }
            else {
                TRACE("sat", tout << "variable is not bound " << mk_pp(v, m) << "\n";);
                return false;
            }
        }
        expr_ref val(m);
        expr_ref_vector conj(m);
        internalize_value(value, v, val);
        while (!premises.empty()) {
            expr* e = nullptr;
            VERIFY(asm2dep.find(premises.pop().index(), e));
            conj.push_back(e);
        }
        conseq = m.mk_implies(mk_and(conj), val);
        return true;
    }

    vector<rational> m_exps;
    void internalize_value(sat::literal_vector const& value, expr* v, expr_ref& val) {
        bv_util bvutil(m);
        if (is_uninterp_const(v) && m.is_bool(v)) {
            SASSERT(value.size() == 1);
            val = value[0].sign() ? m.mk_not(v) : v;
        }
        else if (is_uninterp_const(v) && bvutil.is_bv_sort(v->get_sort())) {
            SASSERT(value.size() == bvutil.get_bv_size(v));
            if (m_exps.empty()) {
                m_exps.push_back(rational::one());
            }
            while (m_exps.size() < value.size()) {
                m_exps.push_back(rational(2)*m_exps.back());
            }
            rational r(0);
            for (unsigned i = 0; i < value.size(); ++i) {
                if (!value[i].sign()) {
                    r += m_exps[i];
                }
            }
            val = m.mk_eq(v, bvutil.mk_numeral(r, value.size()));
        }
        else {
            UNREACHABLE();
        }
    }

    bool is_literal(expr* n) {
        return is_uninterp_const(n) || (m.is_not(n, n) && is_uninterp_const(n));
    }

    bool is_clause(expr* fml) {
        if (is_literal(fml)) {
            return true;
        }
        if (!m.is_or(fml)) {
            return false;
        }
        for (expr* n : *to_app(fml)) {
            if (!is_literal(n)) {
                return false;
            }
        }
        return true;
    }

    lbool internalize_formulas() {
        if (m_fmls_head == m_fmls.size()) {
            return l_true;
        }
        goal_ref g = alloc(goal, m, true, false); // models, maybe cores are enabled
        for (unsigned i = m_fmls_head ; i < m_fmls.size(); ++i) {
            expr* fml = m_fmls.get(i);
            g->assert_expr(fml);
        }
        lbool res = internalize_goal(g);
        if (res != l_undef) {
            m_fmls_head = m_fmls.size();
        }
        m_internalized_converted = false;
        return res;
    }

    void extract_assumptions(unsigned sz, expr* const* asms) {
        m_asms.reset();
        unsigned j = 0;
        sat::literal lit;
        sat::literal_set seen;
        for (unsigned i = 0; i < sz; ++i) {
            if (m_dep2asm.find(asms[i], lit)) {
                SASSERT(lit.var() <= m_solver.num_vars());
                if (!seen.contains(lit)) {
                    m_asms.push_back(lit);
                    seen.insert(lit);
                    if (i != j && !m_weights.empty()) {
                        m_weights[j] = m_weights[i];
                    }
                    ++j;
                }
            }
        }
        for (unsigned i = 0; i < get_num_assumptions(); ++i) {
            if (m_dep2asm.find(get_assumption(i), lit)) {
                SASSERT(lit.var() <= m_solver.num_vars());
                if (!seen.contains(lit)) {
                    m_asms.push_back(lit);
                    seen.insert(lit);
                }
            }
        }
        CTRACE("sat", m_dep2asm.size() != m_asms.size(), 
               tout << m_dep2asm.size() << " vs " << m_asms.size() << "\n";
               tout << m_asms << "\n";
               for (auto const& kv : m_dep2asm) {
                   tout << mk_pp(kv.m_key, m) << " " << kv.m_value << "\n";
               });
        SASSERT(m_dep2asm.size() == m_asms.size());
    }

    void extract_asm2dep(u_map<expr*>& asm2dep) {
        for (auto const& kv : m_dep2asm) {
            asm2dep.insert(kv.m_value.index(), kv.m_key);
        }
    }

    void extract_core(obj_map<expr, expr*> const& asm2fml) {
        u_map<expr*> asm2dep;
        extract_asm2dep(asm2dep);
        sat::literal_vector const& core = m_solver.get_core();
        TRACE("sat",
              for (auto kv : m_dep2asm) {
                  tout << mk_pp(kv.m_key, m) << " |-> " << sat::literal(kv.m_value) << "\n";
              }
              tout << "asm2fml: ";
              for (auto kv : asm2fml) {
                  tout << mk_pp(kv.m_key, m) << " |-> " << mk_pp(kv.m_value, m) << "\n";
              }
              tout << "core: "; for (auto c : core) tout << c << " ";  tout << "\n";
              m_solver.display(tout);
              );

        m_core.reset();
        for (sat::literal c : core) {
            expr* e = nullptr;
            VERIFY(asm2dep.find(c.index(), e));
            if (asm2fml.contains(e)) {
                e = asm2fml.find(e);
            }
            m_core.push_back(e);            
        }
    }

    void check_assumptions() {
        sat::model const & ll_m = m_solver.get_model();
        for (auto const& kv : m_dep2asm) {
            sat::literal lit = kv.m_value;
            if (sat::value_at(lit, ll_m) != l_true) {
                IF_VERBOSE(0, verbose_stream() << mk_pp(kv.m_key, m) << " does not evaluate to true\n";
                           verbose_stream() << m_asms << "\n";
                           m_solver.display_assignment(verbose_stream());
                           m_solver.display(verbose_stream()););
                throw default_exception("bad state");
            }
        }
    }

    void get_model_core(model_ref & mdl) override {
        TRACE("sat", tout << "retrieve model " << (m_solver.model_is_current()?"present":"absent") << "\n";);
        if (!m_solver.model_is_current()) {
            mdl = nullptr;
            return;
        }
        if (m_fmls.size() > m_fmls_head) {
            mdl = nullptr;
            return;
        }
        TRACE("sat", m_solver.display_model(tout););
        CTRACE("sat", m_sat_mc, m_sat_mc->display(tout););
        sat::model ll_m = m_solver.get_model();
        mdl = alloc(model, m);
        if (m_sat_mc) {
            (*m_sat_mc)(ll_m);
        }        
        expr_ref_vector var2expr(m);
        m_map.mk_var_inv(var2expr);
        
        for (unsigned v = 0; v < var2expr.size(); ++v) {
            expr * n = var2expr.get(v);
            if (!n || !is_uninterp_const(n)) {
                continue;
            }
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
        if (m_sat_mc) {
            (*m_sat_mc)(mdl);
        }
        m_goal2sat.update_model(mdl);
        if (m_mcs.back()) {      
            TRACE("sat", m_mcs.back()->display(tout););
            (*m_mcs.back())(mdl);
        }
        TRACE("sat", model_smt2_pp(tout, m, *mdl, 0););        

        if (!gparams::get_ref().get_bool("model_validate", false)) {
            return;
        }
        IF_VERBOSE(1, verbose_stream() << "Verifying solution\n";);
        model_evaluator eval(*mdl);
        eval.set_model_completion(true);
        bool all_true = true;
        for (expr * f : m_fmls) {
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
            IF_VERBOSE(0, if (m_mcs.back()) m_mcs.back()->display(verbose_stream() << "mc0\n"));
            IF_VERBOSE(0, for (auto const& kv : m_map) verbose_stream() << mk_pp(kv.m_key, m) << " |-> " << kv.m_value << "\n");
            exit(0);
        }
        else {
            IF_VERBOSE(1, verbose_stream() << "solution verified\n");
        }
    }
};


solver* mk_inc_sat_solver(ast_manager& m, params_ref const& p, bool incremental_mode) {
    return alloc(inc_sat_solver, m, p, incremental_mode);
}


void inc_sat_display(std::ostream& out, solver& _s, unsigned sz, expr*const* soft, rational const* _weights) {
    inc_sat_solver& s = dynamic_cast<inc_sat_solver&>(_s);
    vector<unsigned> weights;
    for (unsigned i = 0; _weights && i < sz; ++i) {
        if (!_weights[i].is_unsigned()) {
            throw default_exception("Cannot display weights that are not integers");
        }
        weights.push_back(_weights[i].get_unsigned());
    }
    s.display_weighted(out, sz, soft, weights.data());
}


tactic * mk_psat_tactic(ast_manager& m, params_ref const& p) {
    parallel_params pp(p);
    return pp.enable() ? mk_parallel_tactic(mk_inc_sat_solver(m, p, false), p) : mk_sat_tactic(m);
}
