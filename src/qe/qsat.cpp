/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.cpp

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:

Notes:


--*/

#include "ast/expr_abstract.h"
#include "ast/ast_util.h"
#include "ast/rewriter/quant_hoist.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "model/model_v2_pp.h"
#include "model/model_evaluator.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include "solver/mus.h"
#include "qe/qsat.h"
#include "qe/qe_mbp.h"
#include "qe/qe.h"
#include "ast/rewriter/label_rewriter.h"

namespace qe {

    pred_abs::pred_abs(ast_manager& m):
        m(m),
        m_asms(m),
        m_trail(m),
        m_fmc(alloc(generic_model_converter, m, "qsat"))
    {
    }

    generic_model_converter* pred_abs::fmc() { 
        return m_fmc.get(); 
    }

    void pred_abs::reset() {
        m_trail.reset();
        dec_keys<expr>(m_pred2lit);
        dec_keys<app>(m_lit2pred);
        dec_keys<app>(m_asm2pred);
        dec_keys<expr>(m_pred2asm);
        m_lit2pred.reset();
        m_pred2lit.reset();
        m_asm2pred.reset();
        m_pred2asm.reset();
        m_elevel.reset();
        m_asms.reset();
        m_asms_lim.reset();
        m_preds.reset();
    }

    max_level pred_abs::compute_level(app* e) {
        unsigned sz0 = todo.size();
        todo.push_back(e);        
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (m_elevel.contains(a)) {
                todo.pop_back();
                continue;
            }
            max_level lvl, lvl0;
            bool has_new = false;
            if (m_flevel.find(a->get_decl(), lvl)) {
                lvl0.merge(lvl);
            }
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                app* arg = to_app(a->get_arg(i));
                if (m_elevel.find(arg, lvl)) {
                    lvl0.merge(lvl);
                }
                else {
                    todo.push_back(arg);
                    has_new = true;
                }
            }
            if (!has_new) {
                m_elevel.insert(a, lvl0);
                todo.pop_back();
            }
        }
        return m_elevel.find(e);
    }
    
    void pred_abs::add_pred(app* p, app* lit) {
        m.inc_ref(p);
        m_pred2lit.insert(p, lit);
        add_lit(p, lit);
    }

    void pred_abs::add_lit(app* p, app* lit) {
        if (!m_lit2pred.contains(lit)) {
            m.inc_ref(lit);
            m_lit2pred.insert(lit, p);        
        }
    }

    void pred_abs::add_asm(app* p, expr* assum) {
        SASSERT(!m_asm2pred.contains(assum));
        m.inc_ref(p);
        m.inc_ref(assum);
        m_asm2pred.insert(assum, p);
        m_pred2asm.insert(p, assum);
    }
    
    void pred_abs::push() {
        m_asms_lim.push_back(m_asms.size());
    }

    void pred_abs::pop(unsigned num_scopes) {
        unsigned l = m_asms_lim.size() - num_scopes;
        m_asms.resize(m_asms_lim[l]);
        m_asms_lim.shrink(l);            
    }
        
    void pred_abs::insert(app* a, max_level const& lvl) {
        unsigned l = lvl.max();
        if (l == UINT_MAX) l = 0;
        while (m_preds.size() <= l) {
            m_preds.push_back(app_ref_vector(m));
        }
        m_preds[l].push_back(a);            
    }

    bool pred_abs::is_predicate(app* a, unsigned l) {
        max_level lvl1;
        return m_flevel.find(a->get_decl(), lvl1) && lvl1.max() < l;
    }

    void pred_abs::get_assumptions(model* mdl, expr_ref_vector& asms) {
        unsigned level = m_asms_lim.size();
        if (level > m_preds.size()) {
            level = m_preds.size();
        }
        if (!mdl) {
            asms.append(m_asms);
            return;
        }
        if (level == 0) {
            return;
        }
        model_evaluator eval(*mdl);
        eval.set_model_completion(true);
        TRACE("qe", model_v2_pp(tout, *mdl););

        expr_ref val(m);
        for (unsigned j = 0; j < m_preds[level - 1].size(); ++j) {
            app* p = m_preds[level - 1][j].get();
            TRACE("qe", tout << "process level: " << level - 1 << ": " << mk_pp(p, m) << "\n";);
            
            eval(p, val);
            
            if (m.is_false(val)) {
                m_asms.push_back(m.mk_not(p));
            }
            else {                
                SASSERT(m.is_true(val));
                m_asms.push_back(p);
            }
        }
        asms.append(m_asms);
        
        for (unsigned i = level + 1; i < m_preds.size(); i += 2) {
            for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                app* p = m_preds[i][j].get();
                max_level lvl = m_elevel.find(p);
                bool use = 
                    (lvl.m_fa == i && (lvl.m_ex == UINT_MAX || lvl.m_ex < level)) ||
                    (lvl.m_ex == i && (lvl.m_fa == UINT_MAX || lvl.m_fa < level));
                if (use) {
                    eval(p, val);
                    if (m.is_false(val)) {
                        asms.push_back(m.mk_not(p));
                    }
                    else {
                        asms.push_back(p);
                    }
                }
            }
        }
        TRACE("qe", tout << "level: " << level << "\n";
              model_v2_pp(tout, *mdl);
              display(tout, asms););
    }
    
    void pred_abs::set_expr_level(app* v, max_level const& lvl) {
        m_elevel.insert(v, lvl);
    }

    void pred_abs::set_decl_level(func_decl* f, max_level const& lvl) {
        m_flevel.insert(f, lvl);
    }

    void pred_abs::abstract_atoms(expr* fml, expr_ref_vector& defs) {
        max_level level;
        abstract_atoms(fml, level, defs);
    }
    /** 
        \brief create propositional abstraction of formula by replacing atomic sub-formulas by fresh 
        propositional variables, and adding definitions for each propositional formula on the side.
        Assumption is that the formula is quantifier-free.
    */
    void pred_abs::abstract_atoms(expr* fml, max_level& level, expr_ref_vector& defs) {
        expr_mark mark;
        ptr_vector<expr> args;
        app_ref r(m), eq(m);
        app* p;
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        m_trail.push_back(fml);
        max_level l;
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            todo.pop_back();
            if (mark.is_marked(a)) {
                continue;
            }
            
            mark.mark(a);
            if (m_lit2pred.find(a, p)) {
                TRACE("qe", tout << mk_pp(a, m) << " " << mk_pp(p, m) << "\n";);
                level.merge(m_elevel.find(p));
                continue;
            }
            
            if (is_uninterp_const(a) && m.is_bool(a)) {
                l = m_elevel.find(a);
                level.merge(l);                
                if (!m_pred2lit.contains(a)) {
                    add_pred(a, a);
                    insert(a, l);
                }
                continue;
            }
            
            unsigned sz = a->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i);
                if (!mark.is_marked(f)) {
                    todo.push_back(f);
                }
            } 
            
            bool is_boolop = 
                (a->get_family_id() == m.get_basic_family_id()) &&
                (!m.is_eq(a)       || m.is_bool(a->get_arg(0))) && 
                (!m.is_distinct(a) || m.is_bool(a->get_arg(0)));
            
            if (!is_boolop && m.is_bool(a)) {
                TRACE("qe", tout << mk_pp(a, m) << "\n";);
                r = fresh_bool("p");
                max_level l = compute_level(a);
                add_pred(r, a);
                m_elevel.insert(r, l);
                eq = m.mk_eq(r, a);
                defs.push_back(eq);
                if (!is_predicate(a, l.max())) {
                    insert(r, l);
                }
                level.merge(l);
            }
        }
    }

    app_ref pred_abs::fresh_bool(char const* name) {
        app_ref r(m.mk_fresh_const(name, m.mk_bool_sort()), m);
        m_fmc->hide(r);
        return r;
    }


    // optional pass to replace atoms by predicates 
    // so that SMT core works on propositional
    // abstraction only.
    expr_ref pred_abs::mk_abstract(expr* fml) {
        expr_ref_vector trail(m), args(m);
        obj_map<expr, expr*> cache;
        app* b;
        expr_ref r(m);
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (cache.contains(a)) {
                todo.pop_back();
                continue;
            }
            if (m_lit2pred.find(a, b)) {
                cache.insert(a, b);
                todo.pop_back();
                continue;
            }
            unsigned sz = a->get_num_args();
            bool diff = false;
            args.reset();
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i), *f1;
                if (cache.find(f, f1)) {
                    args.push_back(f1);
                    diff |= f != f1;
                }
                else {
                    todo.push_back(f);
                }
            } 
            if (sz == args.size()) {
                if (diff) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                    trail.push_back(r);
                }
                else {
                    r = a;
                }
                cache.insert(a, r);
                todo.pop_back();
            }
        }
        return expr_ref(cache.find(fml), m);
    }

    expr_ref pred_abs::mk_assumption_literal(expr* a, model* mdl, max_level const& lvl, expr_ref_vector& defs) {
        expr_ref A(m);
        A = pred2asm(a);
        a = A;
        app_ref p(m);
        expr_ref q(m), fml(m);
        app *b;
        expr *c, *d;
        max_level lvl2;
        TRACE("qe", tout << mk_pp(a, m) << " " << lvl << "\n";);
        if (m_asm2pred.find(a, b)) {
            q = b;
        }
        else if (m.is_not(a, c) && m_asm2pred.find(c, b)) {
            q = m.mk_not(b);
        }
        else if (m_pred2asm.find(a, d)) {
            q = a;
        }
        else if (m.is_not(a, c) && m_pred2asm.find(c, d)) {
            q = a;
        }
        else {
            p = fresh_bool("def");
            if (m.is_not(a, a)) {
                if (mdl) 
                    mdl->register_decl(p->get_decl(), m.mk_false());
                q = m.mk_not(p);
            }
            else {
                if (mdl)
                    mdl->register_decl(p->get_decl(), m.mk_true());
                q = p;
            }
            m_elevel.insert(p, lvl);
            insert(p, lvl);
            fml = a;
            abstract_atoms(fml, lvl2, defs);
            fml = mk_abstract(fml);
            defs.push_back(m.mk_eq(p, fml));
            add_asm(p, a);
            TRACE("qe", tout << mk_pp(a, m) << " |-> " << p << "\n";);
        }
        return q;
    }

    void pred_abs::mk_concrete(expr_ref_vector& fmls, obj_map<expr,expr*> const& map) {
        obj_map<expr,expr*> cache;
        expr_ref_vector trail(m);
        expr* p;
        app_ref r(m);
        ptr_vector<expr> args;
        unsigned sz0 = todo.size();
        todo.append(fmls.size(), (expr*const*)fmls.c_ptr());
        while (sz0 != todo.size()) {
            app* a = to_app(todo.back());
            if (cache.contains(a)) {
                todo.pop_back();
                continue;
            }
            if (map.find(a, p)) {
                cache.insert(a, p);
                todo.pop_back();
                continue;
            }
            unsigned sz = a->get_num_args();
            args.reset();
            bool diff = false;
            for (unsigned i = 0; i < sz; ++i) {
                expr* f = a->get_arg(i), *f1;
                if (cache.find(f, f1)) {
                    args.push_back(f1);
                    diff |= f != f1;
                }
                else {
                    todo.push_back(f);
                }
            } 
            if (args.size() == sz) {
                if (diff) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                }
                else {
                    r = to_app(a);
                }
                cache.insert(a, r);
                trail.push_back(r);
                todo.pop_back();
            }
        }
        for (unsigned i = 0; i < fmls.size(); ++i) {
            fmls[i] = to_app(cache.find(fmls[i].get()));
        }        
    }
    
    void pred_abs::pred2lit(expr_ref_vector& fmls) {
        mk_concrete(fmls, m_pred2lit);
    }

    expr_ref pred_abs::pred2asm(expr* fml) {
        expr_ref_vector fmls(m);
        fmls.push_back(fml);
        mk_concrete(fmls, m_pred2asm);
        return mk_and(fmls);
    }

    void pred_abs::collect_statistics(statistics& st) const {
        st.update("qsat num predicates", m_pred2lit.size());
    }
        
    void pred_abs::display(std::ostream& out) const {
        out << "pred2lit:\n";
        obj_map<expr, expr*>::iterator it = m_pred2lit.begin(), end = m_pred2lit.end();
        for (; it != end; ++it) {
            out << mk_pp(it->m_key, m) << " |-> " << mk_pp(it->m_value, m) << "\n";
        }
        for (unsigned i = 0; i < m_preds.size(); ++i) {
            out << "level " << i << "\n";
            for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                app* p = m_preds[i][j];
                expr* e;
                if (m_pred2lit.find(p, e)) {
                    out << mk_pp(p, m) << " := " << mk_pp(e, m) << "\n";
                }
                else {
                    out << mk_pp(p, m) << "\n";
                }
            }
        }            
    }        
    
    void pred_abs::display(std::ostream& out, expr_ref_vector const& asms) const {
        max_level lvl;       
        for (unsigned i = 0; i < asms.size(); ++i) {
            expr* e = asms[i];
            bool is_not = m.is_not(asms[i], e);
            out << mk_pp(asms[i], m);
            if (m_elevel.find(e, lvl)) {
                lvl.display(out << " - ");
            }
            if (m_pred2lit.find(e, e)) {
                out << " : " << (is_not?"!":"") << mk_pp(e, m);
            }
            out << "\n";
        }
    }

    void pred_abs::get_free_vars(expr* fml, app_ref_vector& vars) {
        ast_fast_mark1 mark;
        unsigned sz0 = todo.size();
        todo.push_back(fml);
        while (sz0 != todo.size()) {
            expr* e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e) || is_var(e)) {
                continue;
            }
            mark.mark(e);
            if (is_quantifier(e)) {
                todo.push_back(to_quantifier(e)->get_expr());
                continue;
            }
            SASSERT(is_app(e));
            app* a = to_app(e);
            if (is_uninterp_const(a)) { // TBD generalize for uninterpreted functions.
                vars.push_back(a);
            }
            for (expr* arg : *a) {
                todo.push_back(arg);
            }
        }
    }

    bool pred_abs::validate_defs(model& model) const {
        bool valid = true;
        for (auto& kv : m_pred2lit) {
            expr_ref val_a(m), val_b(m);
            expr* a = kv.m_key;
            expr* b = kv.m_value;
            val_a = model(a);
            val_b = model(b);
            if ((m.is_true(val_a) && m.is_false(val_b)) || 
                (m.is_false(val_a) && m.is_true(val_b))) {
                TRACE("qe", 
                      tout << mk_pp(a, m) << " := " << val_a << "\n";
                      tout << mk_pp(b, m) << " := " << val_b << "\n";
                      tout << m_elevel.find(a) << "\n";);
                valid = false;
            }
        }
        return valid;
    }

    class kernel {
        ast_manager& m;
        params_ref   m_params;
        ref<solver>  m_solver;
        
    public:
        kernel(ast_manager& m):
            m(m),
            m_solver(mk_smt_solver(m, m_params, symbol::null))
        {
            m_params.set_bool("model", true);
            m_params.set_uint("relevancy_lvl", 0);
            m_params.set_uint("case_split_strategy", CS_ACTIVITY_WITH_CACHE);
            m_solver->updt_params(m_params);
        }
        
        
        solver& s() { return *m_solver; }
        solver const& s() const { return *m_solver; }

        void init() {
            m_solver = mk_smt_solver(m, m_params, symbol::null);
        }
        void reset_statistics() {
            init();
        }
        void clear() {
            m_solver = nullptr;
        }
        void assert_expr(expr* e) {
            m_solver->assert_expr(e);
        }
        
        void get_core(expr_ref_vector& core) {
            core.reset();
            m_solver->get_unsat_core(core);
            TRACE("qe", m_solver->display(tout << "core: " << core << "\n") << "\n";);
        }
    };

    enum qsat_mode {
        qsat_qe,
        qsat_qe_rec,
        qsat_sat,
        qsat_maximize
    };
    
    class qsat : public tactic {
        
        struct stats {
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };        
        
        ast_manager&               m;
        params_ref                 m_params;
        stats                      m_stats;
        statistics                 m_st;
        qe::mbp                    m_mbp;
        kernel                     m_fa;
        kernel                     m_ex;
        pred_abs                   m_pred_abs;
        expr_ref_vector            m_answer;
        expr_ref_vector            m_asms;
        vector<app_ref_vector>     m_vars;       // variables from alternating prefixes.
        unsigned                   m_level;
        model_ref                  m_model;
        qsat_mode                  m_mode;
        app_ref_vector             m_avars;       // variables to project
        app_ref_vector             m_free_vars;
        app*                       m_objective;
        opt::inf_eps*              m_value;
        bool                       m_was_sat;
        model_ref                  m_model_save;
        expr_ref                   m_gt;
        opt::inf_eps               m_value_save;

        
        /**
           \brief check alternating satisfiability.
           Even levels are existential, odd levels are universal.
        */
        lbool check_sat() {        
            while (true) {
                ++m_stats.m_num_rounds;
                IF_VERBOSE(3, verbose_stream() << "(check-qsat level: " << m_level << " round: " << m_stats.m_num_rounds << ")\n";);
                check_cancel();
                expr_ref_vector asms(m_asms);
                m_pred_abs.get_assumptions(m_model.get(), asms);
                if (m_model.get()) {
                    validate_assumptions(*m_model.get(), asms);
                }
                TRACE("qe", tout << asms << "\n";);
                solver& s = get_kernel(m_level).s();
                lbool res = s.check_sat(asms);
                switch (res) {
                case l_true:
                    s.get_model(m_model);
                    SASSERT(validate_defs("check_sat"));
                    SASSERT(validate_assumptions(*m_model.get(), asms));
                    SASSERT(validate_model(asms));
                    TRACE("qe", s.display(tout); display(tout << "\n", *m_model.get()); display(tout, asms); );
                    if (m_level == 0) {
                        m_model_save = m_model;
                    }
                    push();
                    if (m_level == 1 && m_mode == qsat_maximize) {
                        maximize_model();
                    }
                    break;
                case l_false:
                    switch (m_level) {
                    case 0: 
                        return l_false;
                    case 1: 
                        if (m_mode == qsat_sat) {
                            return l_true; 
                        }
                        if (m_model.get()) {
                            SASSERT(validate_assumptions(*m_model.get(), asms));
                            if (!project_qe(asms)) return l_undef;
                        }
                        else {
                            pop(1);
                        }
                        break;
                    default: 
                        if (m_model.get()) {
                            if (!project(asms)) return l_undef;
                        }
                        else {
                            pop(1);
                        }
                        break;
                    }
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }

        kernel& get_kernel(unsigned j) {        
            if (is_exists(j)) {
                return m_ex; 
            }
            else {
                return m_fa;
            }
        }
        
        bool is_exists(unsigned level) const {
            return (level % 2) == 0;
        }
        
        bool is_forall(unsigned level) const {
            return is_exists(level+1);
        }
        
        void push() {
            m_level++;
            m_pred_abs.push();
        }
        
        void pop(unsigned num_scopes) {
            m_model.reset();
            SASSERT(num_scopes <= m_level);
            m_pred_abs.pop(num_scopes);
            m_level -= num_scopes;
        }
        
        void clear() {
            m_st.reset();        
            m_fa.s().collect_statistics(m_st);
            m_ex.s().collect_statistics(m_st);        
            m_pred_abs.collect_statistics(m_st);
            m_level = 0;
            m_answer.reset();
            m_asms.reset();
            m_pred_abs.reset();
            m_vars.reset();
            m_model = nullptr;
            m_free_vars.reset();
            m_fa.clear();
            m_ex.clear();                    
        }

        void reset() override {
            clear();
            m_fa.init();
            m_ex.init();                
        }    
        
        /**
           \brief create a quantifier prefix formula.
        */
        void hoist(expr_ref& fml) {
            proof_ref pr(m);
            label_rewriter rw(m);
            rw.remove_labels(fml, pr);
            quantifier_hoister hoist(m);
            app_ref_vector vars(m);
            bool is_forall = false;        
            m_pred_abs.get_free_vars(fml, vars);
            m_vars.push_back(vars);
            vars.reset();
            if (m_mode != qsat_sat) {
                is_forall = true;
                hoist.pull_quantifier(is_forall, fml, vars);
                m_vars.push_back(vars);
                filter_vars(vars);
            }
            else {
                hoist.pull_quantifier(is_forall, fml, vars);
                m_vars.back().append(vars);
                filter_vars(vars);
            }
            do {
                is_forall = !is_forall;
                vars.reset();
                hoist.pull_quantifier(is_forall, fml, vars);
                m_vars.push_back(vars);
                filter_vars(vars);
            }
            while (!vars.empty());
            SASSERT(m_vars.back().empty()); 
            initialize_levels();
            TRACE("qe", tout << fml << "\n";);
        }

        void filter_vars(app_ref_vector const& vars) {
            for (app* v : vars) m_pred_abs.fmc()->hide(v);
        }        

        void initialize_levels() {
            // initialize levels.
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                max_level lvl;
                if (is_exists(i)) {
                    lvl.m_ex = i;
                }
                else {
                    lvl.m_fa = i;
                }
                for (unsigned j = 0; j < m_vars[i].size(); ++j) {
                    m_pred_abs.set_expr_level(m_vars[i][j].get(), lvl);
                }
            }
        }
        
        bool validate_defs(char const* msg) {
            if (m_model.get() && !m_pred_abs.validate_defs(*m_model.get())) {
                TRACE("qe", 
                      tout << msg << "\n";
                      display(tout);
                      if (m_level > 0) {
                          get_kernel(m_level-1).s().display(tout);
                      }
                      expr_ref_vector asms(m);
                      m_pred_abs.get_assumptions(m_model.get(), asms);
                      tout << asms << "\n";
                      m_pred_abs.pred2lit(asms);
                      tout << asms << "\n";);
                return false;
            }
            else {
                return true;
            }
        }

        bool get_core(expr_ref_vector& core, unsigned level) {
            SASSERT(validate_defs("get_core"));
            get_kernel(level).get_core(core);
            m_pred_abs.pred2lit(core);
            return true;
        }

        bool minimize_core(expr_ref_vector& core, unsigned level) {
            expr_ref_vector core1(m), core2(m), dels(m);
            TRACE("qe", tout << core.size() << "\n";);
            mus mus(get_kernel(level).s());
            for (unsigned i = 0; i < core.size(); ++i) {
                app* a = to_app(core[i].get());                
                max_level lvl = m_pred_abs.compute_level(a);
                if (lvl.max() + 2 <= level) {     
                    VERIFY(core1.size() == mus.add_soft(a));
                    core1.push_back(a);
                }
                else {
                    core2.push_back(a);
                    mus.add_assumption(a);
                }
            }
            TRACE("qe", tout << core1.size() << " " << core2.size() << "\n";);
            if (core1.size() > 8) {
                if (l_true != mus.get_mus(core2)) {
                    return false;
                }
                TRACE("qe", tout << core1.size() << " -> " << core2.size() << "\n";);
                core.reset();
                core.append(core2);
            }
            return true;
        }
        
        void check_cancel() {
            if (m.canceled()) {
                throw tactic_exception(m.limit().get_cancel_msg());
            }
        }
        
        void display(std::ostream& out) const {
            out << "level: " << m_level << "\n";
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                out << m_vars[i] << "\n";
            }
            m_pred_abs.display(out);
        }
        
        void display(std::ostream& out, model& model) const {
            display(out);
            model_v2_pp(out, model);
        }
        
        void display(std::ostream& out, expr_ref_vector const& asms) const {
            m_pred_abs.display(out, asms);
        }
        
        void add_assumption(expr* fml) {
            expr_ref eq(m);
            app_ref b = m_pred_abs.fresh_bool("b");        
            m_asms.push_back(b);
            eq = m.mk_eq(b, fml);
            m_ex.assert_expr(eq);
            m_fa.assert_expr(eq);
            m_pred_abs.add_pred(b, to_app(fml));
            max_level lvl;
            m_pred_abs.set_expr_level(b, lvl);
        }
        
        bool project_qe(expr_ref_vector& core) {
            SASSERT(m_level == 1);
            expr_ref fml(m);
            model& mdl = *m_model.get();
            if (!get_core(core, m_level)) {
                return false;
            }
            SASSERT(validate_core(mdl, core));
            get_vars(m_level);
            SASSERT(validate_assumptions(mdl, core));
            m_mbp(force_elim(), m_avars, mdl, core);
            SASSERT(validate_defs("project_qe"));
            if (m_mode == qsat_maximize) {
                maximize_core(core, mdl);
            }
            else {
                fml = negate_core(core);
                add_assumption(fml);
                m_answer.push_back(fml);
                m_free_vars.append(m_avars);
            }
            pop(1);
            return true;
        }
                
        bool project(expr_ref_vector& core) {
            if (!get_core(core, m_level)) return false;
            TRACE("qe", display(tout); display(tout << "core\n", core););
            SASSERT(m_level >= 2);
            expr_ref fml(m); 
            expr_ref_vector defs(m), core_save(m);
            max_level level;
            model& mdl = *m_model.get();
            SASSERT(validate_core(mdl, core));
            get_vars(m_level-1);
            SASSERT(validate_project(mdl, core));
            m_mbp(force_elim(), m_avars, mdl, core);
            m_free_vars.append(m_avars);
            fml = negate_core(core);
            unsigned num_scopes = 0;
            
            m_pred_abs.abstract_atoms(fml, level, defs);
            m_ex.assert_expr(mk_and(defs));
            m_fa.assert_expr(mk_and(defs));
            if (level.max() == UINT_MAX) {
                num_scopes = 2*(m_level/2);
            }
            else if (m_mode == qsat_qe_rec) {
                num_scopes = 2;
            }
            else {
                if (level.max() + 2 > m_level) return false;
                SASSERT(level.max() + 2 <= m_level);
                num_scopes = m_level - level.max();
                SASSERT(num_scopes >= 2);
                if ((num_scopes % 2) != 0) {
                    --num_scopes;
                }
            }
            
            pop(num_scopes); 
            TRACE("qe", tout << "backtrack: " << num_scopes << " new level: " << m_level << "\nproject:\n" << core << "\n|->\n" << fml << "\n";);
            if (m_level == 0 && m_mode != qsat_sat) {
                add_assumption(fml);
            }
            else {
                fml = m_pred_abs.mk_abstract(fml);
                get_kernel(m_level).assert_expr(fml);
            }
            SASSERT(!m_model.get());
            return true;
        }
        
        void get_vars(unsigned level) {
            m_avars.reset();
            for (unsigned i = level; i < m_vars.size(); ++i) {
                m_avars.append(m_vars[i]);
            }
        } 
        
        expr_ref negate_core(expr_ref_vector const& core) {
            return ::push_not(::mk_and(core));
        }

        bool force_elim() const {
            return m_mode != qsat_qe_rec;
        }
        
        expr_ref elim_rec(expr* fml) {
            expr_ref tmp(m);
            expr_ref_vector     trail(m);
            obj_map<expr,expr*> visited;
            ptr_vector<expr>    todo;
            trail.push_back(fml);
            todo.push_back(fml);
            expr* e = nullptr, *r = nullptr;
            
            while (!todo.empty()) {
                check_cancel();

                e = todo.back();
                if (visited.contains(e)) {
                    todo.pop_back();
                    continue;            
                }
                
                switch(e->get_kind()) {
                case AST_APP: {
                    app* a = to_app(e);
                    expr_ref_vector args(m);
                    unsigned num_args = a->get_num_args();
                    bool all_visited = true;
                    for (unsigned i = 0; i < num_args; ++i) {
                        if (visited.find(a->get_arg(i), r)) {
                            args.push_back(r);
                        }
                        else {
                            todo.push_back(a->get_arg(i));
                            all_visited = false;
                        }
                    }
                    if (all_visited) {
                        r = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
                        todo.pop_back();
                        trail.push_back(r);
                        visited.insert(e, r);
                    }
                    break;
                }
                case AST_QUANTIFIER: {
                    SASSERT(!is_lambda(e));
                    app_ref_vector vars(m);
                    quantifier* q = to_quantifier(e);
                    bool is_fa = ::is_forall(q);
                    tmp = q->get_expr();
                    extract_vars(q, tmp, vars);
                    TRACE("qe", tout << vars << " " << mk_pp(q, m) << " " << tmp << "\n";);
                    tmp = elim_rec(tmp);
                    if (is_fa) {
                        tmp = ::push_not(tmp);
                    }
                    tmp = elim(vars, tmp);
                    if (is_fa) {
                        tmp = ::push_not(tmp);
                    }
                    trail.push_back(tmp);
                    visited.insert(e, tmp);
                    todo.pop_back();
                    break;
                }
                default:
                    UNREACHABLE();
                    break;
                }        
            }    
            VERIFY (visited.find(fml, e));
            return expr_ref(e, m);
        }
        
        expr_ref elim(app_ref_vector const& vars, expr* _fml) {
            expr_ref fml(_fml, m);
            reset();
            m_vars.push_back(app_ref_vector(m));
            m_vars.push_back(vars);
            initialize_levels();
            fml = push_not(fml);            

            TRACE("qe", tout << vars << " " << fml << "\n";);
            expr_ref_vector defs(m);
            m_pred_abs.abstract_atoms(fml, defs);
            fml = m_pred_abs.mk_abstract(fml);
            m_ex.assert_expr(mk_and(defs));
            m_fa.assert_expr(mk_and(defs));
            m_ex.assert_expr(fml);
            m_fa.assert_expr(m.mk_not(fml));
            TRACE("qe", tout << "ex: " << fml << "\n";);
            lbool is_sat = check_sat();
            fml = ::mk_and(m_answer);
            TRACE("qe", tout << "ans: " << fml << "\n";
                  tout << "Free vars: " << m_free_vars << "\n";);            
            if (is_sat == l_false) {
                obj_hashtable<app> vars;
                for (unsigned i = 0; i < m_free_vars.size(); ++i) {
                    app* v = m_free_vars[i].get();
                    if (vars.contains(v)) {
                        m_free_vars[i] = m_free_vars.back();
                        m_free_vars.pop_back();
                        --i;
                    }
                    else {
                        vars.insert(v);
                    }
                }
                fml = mk_exists(m, m_free_vars.size(), m_free_vars.c_ptr(), fml);
                return fml;
            }
            else {
                return expr_ref(_fml, m);
            }
        }

        bool validate_assumptions(model& mdl, expr_ref_vector const& core) {
            for (expr* c : core) {
                if (!mdl.is_true(c)) {
                    TRACE("qe", tout << "component of core is not true: " << mk_pp(c, m) << "\n";);
                    return false;
                }
            }
            return true;
        }

        bool validate_core(model& mdl, expr_ref_vector const& core) {
            return true;
#if 0
            TRACE("qe", tout << "Validate core\n";);
            solver& s = get_kernel(m_level).s();
            expr_ref_vector fmls(m);
            fmls.append(core.size(), core.c_ptr());
            s.get_assertions(fmls);
            return check_fmls(fmls) || m.canceled();
#endif
        }

        bool check_fmls(expr_ref_vector const& fmls) {
            smt_params p;
            smt::kernel solver(m, p);
            for (unsigned i = 0; i < fmls.size(); ++i) {
                solver.assert_expr(fmls[i]);
            }
            lbool is_sat = solver.check();
            CTRACE("qe", is_sat != l_false, 
                   tout << fmls << "\nare not unsat\n";);
            return (is_sat == l_false) || m.canceled();
        }

        bool validate_model(expr_ref_vector const& asms) {
            return true;
#if 0
            TRACE("qe", tout << "Validate model\n";);
            solver& s = get_kernel(m_level).s();
            expr_ref_vector fmls(m);
            s.get_assertions(fmls);
            return 
                validate_model(*m_model, asms.size(), asms.c_ptr()) &&
                validate_model(*m_model, fmls.size(), fmls.c_ptr());
#endif
        }

        bool validate_model(model& mdl, unsigned sz, expr* const* fmls) {
            expr_ref val(m);
            for (unsigned i = 0; i < sz; ++i) {
                if (!m_model->is_true(fmls[i]) && !m.canceled()) {
                    TRACE("qe", tout << "Formula does not evaluate to true in model: " << mk_pp(fmls[i], m) << "\n";);
                    return false;
                } 
            }               
            return true;
        }

        // validate the following:
        //  proj is true in model.
        //  core is true in model.
        //  proj does not contain vars.
        //  proj => exists vars . core
        //  (core[model(vars)/vars] => proj)
              
        bool validate_project(model& mdl, expr_ref_vector const& core) {
            return true;
#if 0
            TRACE("qe", tout << "Validate projection\n";);
            if (!validate_model(mdl, core.size(), core.c_ptr())) return false;

            expr_ref_vector proj(core);
            app_ref_vector vars(m_avars);
            m_mbp(false, vars, mdl, proj);
            if (!vars.empty()) {
                TRACE("qe", tout << "Not validating partial projection\n";);
                return true;
            }
            if (!validate_model(mdl, proj.size(), proj.c_ptr())) {
                TRACE("qe", tout << "Projection is false in model\n";);
                return false;
            }
            if (m.canceled()) {
                return true;
            }
            for (unsigned i = 0; i < m_avars.size(); ++i) {
                contains_app cont(m, m_avars[i].get());
                if (cont(proj)) {
                    TRACE("qe", tout << "Projection contains free variable: " << mk_pp(m_avars[i].get(), m) << "\n";);
                    return false;
                }
            }

            //
            //  TBD: proj => exists vars . core, 
            //  e.g., extract and use realizer functions from mbp.
            //

            //  (core[model(vars)/vars] => proj)            
            expr_ref_vector fmls(m);
            fmls.append(core.size(), core.c_ptr());
            for (unsigned i = 0; i < m_avars.size(); ++i) {
                expr_ref val(m);
                VERIFY(mdl.eval(m_avars[i].get(), val));
                fmls.push_back(m.mk_eq(m_avars[i].get(), val));
            }
            fmls.push_back(m.mk_not(mk_and(proj)));
            if (!check_fmls(fmls)) {
                TRACE("qe", tout << "implication check failed, could be due to turning != into >\n";);
            }
            return true;
#endif
        }


    public:
        
        qsat(ast_manager& m, params_ref const& p, qsat_mode mode):
            m(m),
            m_mbp(m),
            m_fa(m),
            m_ex(m),
            m_pred_abs(m),
            m_answer(m),
            m_asms(m),
            m_level(0),
            m_mode(mode),
            m_avars(m),
            m_free_vars(m),
            m_objective(nullptr),
            m_value(nullptr),
            m_was_sat(false),
            m_gt(m)
        {
            reset();
        }
        
        ~qsat() override {
            clear();
        }
        
        void updt_params(params_ref const & p) override {
        }
        
        void collect_param_descrs(param_descrs & r) override {
        }

        
        void operator()(/* in */  goal_ref const & in, 
                        /* out */ goal_ref_buffer & result) override {
            tactic_report report("qsat-tactic", *in);
            ptr_vector<expr> fmls;
            expr_ref_vector defs(m);
            expr_ref fml(m);
            in->get_formulas(fmls);
            fml = mk_and(m, fmls.size(), fmls.c_ptr());
            
            // for now:
            // fail if cores.  (TBD)
            // fail if proofs. (TBD)
            
            if (m_mode == qsat_qe_rec) {
                fml = elim_rec(fml);
                in->reset();
                in->inc_depth();
                in->assert_expr(fml);                
                result.push_back(in.get());
                return;
            }
                
            reset();
            TRACE("qe", tout << fml << "\n";);
            if (m_mode != qsat_sat) {
                fml = push_not(fml);
            }
            hoist(fml);
            if (!is_ground(fml)) {
                throw tactic_exception("formula is not hoistable");
            }
            m_pred_abs.abstract_atoms(fml, defs);
            fml = m_pred_abs.mk_abstract(fml);
            m_ex.assert_expr(mk_and(defs));
            m_fa.assert_expr(mk_and(defs));
            m_ex.assert_expr(fml);
            m_fa.assert_expr(m.mk_not(fml));
            TRACE("qe", tout << "ex: " << fml << "\n";);
            lbool is_sat = check_sat();
            
            switch (is_sat) {
            case l_false:
                in->reset();
                in->inc_depth();
                if (m_mode == qsat_qe) {
                    fml = ::mk_and(m_answer);
                    in->assert_expr(fml);
                }
                else {
                    SASSERT(m_mode == qsat_sat);
                    in->assert_expr(m.mk_false());
                }
                result.push_back(in.get());
                break;
            case l_true:
                in->reset();
                in->inc_depth();
                result.push_back(in.get());
                if (in->models_enabled()) {                    
                    model_converter_ref mc;
                    mc = model2model_converter(m_model_save.get());
                    mc = concat(m_pred_abs.fmc(), mc.get());
                    in->add(mc.get());
                }
                break;
            case l_undef:
                result.push_back(in.get());
                std::string s = m_ex.s().reason_unknown();
                if (s == "ok" || s == "unknown") {
                    s = m_fa.s().reason_unknown();
                }
                throw tactic_exception(std::move(s));
            }        
        }
        
        void collect_statistics(statistics & st) const override {
            st.copy(m_st);
            m_fa.s().collect_statistics(st);
            m_ex.s().collect_statistics(st);        
            m_pred_abs.collect_statistics(st);
            st.update("qsat num rounds", m_stats.m_num_rounds); 
            m_pred_abs.collect_statistics(st);
        }
        
        void reset_statistics() override {
            m_stats.reset();
            m_fa.reset_statistics();
            m_ex.reset_statistics();
        }
        
        void cleanup() override {
            reset();
        }
        
        void set_logic(symbol const & l) override {
        }
        
        void set_progress_callback(progress_callback * callback) override {
        }
        
        tactic * translate(ast_manager & m) override {
            return alloc(qsat, m, m_params, m_mode);
        }        

        lbool maximize(expr_ref_vector const& fmls, app* t, model_ref& mdl, opt::inf_eps& value) {
            expr_ref_vector defs(m);
            expr_ref fml = mk_and(fmls);
            hoist(fml);
            m_objective = t;
            m_value = &value;
            m_was_sat = false;
            m_model_save.reset();
            m_pred_abs.abstract_atoms(fml, defs);
            fml = m_pred_abs.mk_abstract(fml);
            m_ex.assert_expr(mk_and(defs));
            m_fa.assert_expr(mk_and(defs));
            m_ex.assert_expr(fml);
            m_fa.assert_expr(m.mk_not(fml));
            lbool is_sat = check_sat();
            mdl = m_model.get();
            switch (is_sat) {
            case l_false:
                if (!m_was_sat) {
                    return l_false;
                }
                mdl = m_model_save;
                break;
            case l_true:
                UNREACHABLE();
                break;
            case l_undef:
                std::string s = m_ex.s().reason_unknown();
                if (s == "ok") {
                    s = m_fa.s().reason_unknown();
                }

                throw tactic_exception(std::move(s));
            }        
            return l_true;
        }

        void maximize_core(expr_ref_vector const& core, model& mdl) {
            SASSERT(m_value);
            SASSERT(m_objective);
            TRACE("qe", tout << "maximize: " << core << "\n";);
            m_was_sat |= !core.empty();
            expr_ref bound(m);
            *m_value = m_value_save;
            IF_VERBOSE(3, verbose_stream() << "(maximize " << *m_value << ")\n";);
            m_ex.assert_expr(m_gt);            
            m_fa.assert_expr(m_gt);            
        }

        void maximize_model() {
            SASSERT(m_level == 1 && m_mode == qsat_maximize);
            SASSERT(m_objective);
            expr_ref ge(m);
            expr_ref_vector asms(m), defs(m);
            m_pred_abs.get_assumptions(m_model.get(), asms);
            m_pred_abs.pred2lit(asms);

            SASSERT(validate_defs("maximize_model1"));

            m_value_save = m_mbp.maximize(asms, *m_model.get(), m_objective, ge, m_gt);

            SASSERT(validate_defs("maximize_model2"));
            
            // bound := val <= m_objective
            
            IF_VERBOSE(3, verbose_stream() << "(qsat-maximize-bound: " << m_value_save << ")\n";);

            max_level level;
            m_pred_abs.abstract_atoms(ge, level, defs);
            m_ex.assert_expr(mk_and(defs));
            m_fa.assert_expr(mk_and(defs));

            ge = m_pred_abs.mk_abstract(ge);

            SASSERT(is_uninterp_const(ge));
            // update model with evaluation for bound.
            if (is_uninterp_const(ge)) {
                m_model->register_decl(to_app(ge)->get_decl(), m.mk_true());
            }
            SASSERT(validate_defs("maximize_model3"));
        }

    };

    lbool maximize(expr_ref_vector const& fmls, app* t, opt::inf_eps& value, model_ref& mdl, params_ref const& p) {
        ast_manager& m = fmls.get_manager();
        qsat qs(m, p, qsat_maximize);
        return qs.maximize(fmls, t, mdl, value);
    }    


    struct qmax::imp {
        qsat m_qsat;
        imp(ast_manager& m, params_ref const& p):
            m_qsat(m, p, qsat_maximize)
        {}        
    };

    qmax::qmax(ast_manager& m, params_ref const& p) {
        m_imp = alloc(imp, m, p);        
    }

    qmax::~qmax() {
        dealloc(m_imp);
    }
    
    lbool qmax::operator()(expr_ref_vector const& fmls, app* t, opt::inf_eps& value, model_ref& mdl) {
        return m_imp->m_qsat.maximize(fmls, t, mdl, value);
    }

    void qmax::collect_statistics(statistics& st) const {
        m_imp->m_qsat.collect_statistics(st);
    }
};

tactic * mk_qsat_tactic(ast_manager& m, params_ref const& p) {
    return alloc(qe::qsat, m, p, qe::qsat_sat);
}

tactic * mk_qe2_tactic(ast_manager& m, params_ref const& p) {   
    return alloc(qe::qsat, m, p, qe::qsat_qe);
}

tactic * mk_qe_rec_tactic(ast_manager& m, params_ref const& p) {   
    return alloc(qe::qsat, m, p, qe::qsat_qe_rec);
}




