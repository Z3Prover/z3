/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    nlqsat.cpp

Abstract:

    Quantifier Satisfiability Solver for nlsat

Author:

    Nikolaj Bjorner (nbjorner) 2015-10-17

Revision History:


--*/

#include "nlqsat.h"
#include "nlsat_solver.h"
#include "nlsat_explain.h"
#include "nlsat_assignment.h"
#include "qsat.h"
#include "quant_hoist.h"
#include "goal2nlsat.h"
#include "expr2var.h"
#include "uint_set.h"
#include "ast_util.h"
#include "tseitin_cnf_tactic.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"
#include "for_each_expr.h"
#include "rewriter.h"
#include "rewriter_def.h"


namespace qe {

    enum qsat_mode_t {
        qsat_t,
        elim_t,
        interp_t
    };

    class nlqsat : public tactic {

        typedef unsigned_vector assumption_vector;
        typedef nlsat::scoped_literal_vector clause;

        struct stats {
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }            
        };
        
        ast_manager&           m;
        qsat_mode_t            m_mode;
        params_ref             m_params;
        nlsat::solver          m_solver;
        tactic_ref             m_nftactic;
        nlsat::literal_vector  m_asms;
        nlsat::literal_vector  m_cached_asms;
        unsigned_vector        m_cached_asms_lim;
        nlsat::literal         m_is_true;
        nlsat::assignment      m_rmodel;        
        svector<lbool>         m_bmodel;
        nlsat::assignment      m_rmodel0;        
        svector<lbool>         m_bmodel0;
        bool                   m_valid_model;
        vector<nlsat::var_vector>            m_bound_rvars;
        vector<svector<nlsat::bool_var> >    m_bound_bvars;
        vector<nlsat::scoped_literal_vector> m_preds;
        svector<max_level>                   m_rvar2level;
        u_map<max_level>                     m_bvar2level;
        expr2var                             m_a2b, m_t2x;
        u_map<expr*>                         m_b2a, m_x2t;
        volatile bool                        m_cancel;
        stats                                m_stats;
        statistics                           m_st;
        obj_hashtable<expr>                  m_free_vars;
        obj_hashtable<expr>                  m_aux_vars;
        expr_ref_vector                      m_answer;
        expr_safe_replace                    m_answer_simplify;
        nlsat::literal_vector                m_assumptions;
        u_map<expr*>                         m_asm2fml;
        expr_ref_vector                      m_trail;
        
        lbool check_sat() {
            while (true) {
                ++m_stats.m_num_rounds;
                check_cancel();
                init_assumptions();   
                lbool res = m_solver.check(m_asms);
                switch (res) {
                case l_true:
                    TRACE("qe", display(tout); );
                    save_model();
                    push();
                    break;
                case l_false:
                    if (0 == level()) return l_false;
                    if (1 == level() && m_mode == qsat_t) return l_true;
                    project();
                    break;
                case l_undef:
                    return res;
                }
            }
            return l_undef;
        }
        
        void init_assumptions() {
            unsigned lvl = level();
            m_asms.reset();
            m_asms.push_back(is_exists()?m_is_true:~m_is_true);
            m_asms.append(m_assumptions);
            TRACE("qe", tout << "model valid: " << m_valid_model << " level: " << lvl << " "; 
                  display_assumptions(tout);
                  m_solver.display(tout););

            if (!m_valid_model) {
                m_asms.append(m_cached_asms);
                return;
            }            
            unsave_model();
            if (lvl == 0) {
                SASSERT(m_cached_asms.empty());
                return;
            }
            if (lvl <= m_preds.size()) {
                for (unsigned j = 0; j < m_preds[lvl - 1].size(); ++j) {
                    add_literal(m_cached_asms, m_preds[lvl - 1][j]);
                }
            }
            m_asms.append(m_cached_asms);
            
            for (unsigned i = lvl + 1; i < m_preds.size(); i += 2) {
                for (unsigned j = 0; j < m_preds[i].size(); ++j) {
                    nlsat::literal l = m_preds[i][j];
                    max_level lv = m_bvar2level.find(l.var());
                    bool use = 
                        (lv.m_fa == i && (lv.m_ex == UINT_MAX || lv.m_ex < lvl)) ||
                        (lv.m_ex == i && (lv.m_fa == UINT_MAX || lv.m_fa < lvl));
                    if (use) {
                        add_literal(m_asms, l);
                    }
                }
            }
            TRACE("qe", display(tout);
                  for (unsigned i = 0; i < m_asms.size(); ++i) {
                      m_solver.display(tout, m_asms[i]); tout << "\n";
                  });
            save_model();
        }

        void add_literal(nlsat::literal_vector& lits, nlsat::literal l) {
            lbool r = m_solver.value(l);
            switch (r) {
            case l_true:
                lits.push_back(l);
                break;
            case l_false:
                lits.push_back(~l);
                break;
            default:
                UNREACHABLE();
                break; 
            }
        }

        template<class S, class T>
        void insert_set(S& set, T const& vec) {
            for (unsigned i = 0; i < vec.size(); ++i) {
                set.insert(vec[i]);
            }
        }
        

        void mbp(unsigned level, nlsat::scoped_literal_vector& result) {
            nlsat::var_vector vars;
            uint_set fvars;
            extract_vars(level, vars, fvars);
            mbp(vars, fvars, result);
        }

        void extract_vars(unsigned level, nlsat::var_vector& vars, uint_set& fvars) {
            for (unsigned i = 0; i < m_bound_rvars.size(); ++i) {
                if (i < level) {
                    insert_set(fvars, m_bound_bvars[i]);
                }
                else {
                    vars.append(m_bound_rvars[i]);
                }
            }
        }

        void mbp(nlsat::var_vector const& vars, uint_set const& fvars, clause& result) {
            // 
            // Also project auxiliary variables from clausification.
            // 
            unsave_model();
            nlsat::explain& ex = m_solver.get_explain();
            nlsat::scoped_literal_vector new_result(m_solver);
            result.reset();
            // project quantified Boolean variables.
            for (unsigned i = 0; i < m_asms.size(); ++i) {
                nlsat::literal lit = m_asms[i];
                if (!m_b2a.contains(lit.var()) || fvars.contains(lit.var())) {
                    result.push_back(lit);
                }
            }
            TRACE("qe", m_solver.display(tout, result.size(), result.c_ptr()); tout << "\n";);
            // project quantified real variables.
            // They are sorted by size, so we project the largest variables first to avoid 
            // renaming variables. 
            for (unsigned i = vars.size(); i > 0;) {
                --i;
                new_result.reset();
                ex.project(vars[i], result.size(), result.c_ptr(), new_result);
                result.swap(new_result);
                TRACE("qe", m_solver.display(tout, result.size(), result.c_ptr()); tout << "\n";);
            }
            negate_clause(result);
        }

        void negate_clause(clause& result) {
            for (unsigned i = 0; i < result.size(); ++i) {
                result.set(i, ~result[i]);
            }
        }

        void save_model() {
            m_solver.get_rvalues(m_rmodel);
            m_solver.get_bvalues(m_bmodel);
            m_valid_model = true;
            if (is_exists(level())) {
                m_rmodel0.copy(m_rmodel);
                m_bmodel0.reset();
                m_bmodel0.append(m_bmodel);
            }
        }

        void unsave_model() {
            SASSERT(m_valid_model);
            m_solver.set_rvalues(m_rmodel);
            m_solver.set_bvalues(m_bmodel);
        }
         
        void clear_model() {
            m_valid_model = false;
            m_rmodel.reset();
            m_bmodel.reset();
            m_solver.set_rvalues(m_rmodel);
        }

        unsigned level() const { 
            return m_cached_asms_lim.size();
        }

        void enforce_parity(clause& cl) {
            cl.push_back(is_exists()?~m_is_true:m_is_true);
        }

        void add_clause(clause& cl) {
            if (cl.empty()) {
                cl.push_back(~m_solver.mk_true());
            }
            SASSERT(!cl.empty());
            nlsat::literal_vector lits(cl.size(), cl.c_ptr());
            m_solver.mk_clause(lits.size(), lits.c_ptr());
        }

        max_level get_level(clause const& cl) {
            return get_level(cl.size(), cl.c_ptr());
        }

        max_level get_level(unsigned n, nlsat::literal const* ls) {
            max_level level;
            for (unsigned i = 0; i < n; ++i) {
                level.merge(get_level(ls[i]));
            }
            return level;
        }

        max_level get_level(nlsat::literal l) {
            max_level level;
            if (m_bvar2level.find(l.var(), level)) {
                return level;
            }
            nlsat::var_vector vs;
            m_solver.vars(l, vs);
            TRACE("qe", m_solver.display(tout, l); tout << "\n";);
            for (unsigned i = 0; i < vs.size(); ++i) {
                level.merge(m_rvar2level[vs[i]]);
            }
            set_level(l.var(), level);
            return level;
        }

        void set_level(nlsat::bool_var v, max_level const& level) {
            unsigned k = level.max();
            while (m_preds.size() <= k) {
                m_preds.push_back(nlsat::scoped_literal_vector(m_solver));
            }
            nlsat::literal l(v, false);
            m_preds[k].push_back(l);
            m_bvar2level.insert(v, level);            
            TRACE("qe", m_solver.display(tout, l); tout << ": " << level << "\n";);
        }
        
        void project() {
            TRACE("qe", display_assumptions(tout););
            if (!m_valid_model) {
                pop(1);
                return;
            }
            if (m_mode == elim_t) {
                project_qe();
                return;
            }
            SASSERT(level() >= 2);
            unsigned num_scopes;
            clause cl(m_solver);
            mbp(level()-1, cl);            
            
            max_level clevel = get_level(cl);
            enforce_parity(cl);
            add_clause(cl);

            if (clevel.max() == UINT_MAX) {
                num_scopes = 2*(level()/2);
            }
            else {
                SASSERT(clevel.max() + 2 <= level());
                num_scopes = level() - clevel.max();
                if ((num_scopes % 2) != 0) {
                    --num_scopes;
                }
                SASSERT(num_scopes >= 2);
            }
            
            TRACE("qe", tout << "backtrack: " << num_scopes << "\n";);
            pop(num_scopes); 
        }

        void project_qe() {
            SASSERT(level() >= 1 && m_mode == elim_t && m_valid_model);
            clause cl(m_solver);
            mbp(std::max(1u, level()-1), cl);            
            
            expr_ref fml = clause2fml(cl);
            TRACE("qe", tout << level() << ": " << fml << "\n";);
            max_level clevel = get_level(cl);
            if (level() == 1 || clevel.max() == 0) {
                add_assumption_literal(cl, fml);           
            }
            else {
                enforce_parity(cl);
            }
            add_clause(cl);

            if (level() == 1) { // is_forall() && clevel.max() == 0
                add_to_answer(fml);
            }

            if (level() == 1) {
                pop(1);
            }
            else {
                pop(2);
            }
        }

        void add_to_answer(expr_ref& fml) {
            m_answer_simplify(fml);
            expr* e;
            if (m.is_not(fml, e)) {
                m_answer_simplify.insert(e, m.mk_false());
            }
            else {
                m_answer_simplify.insert(fml, m.mk_true());
            }
            m_answer.push_back(fml);
        }

        expr_ref clause2fml(nlsat::scoped_literal_vector const& clause) {
            expr_ref_vector fmls(m);
            expr_ref fml(m);
            expr* t;
            nlsat2goal n2g(m);
            for (unsigned i = 0; i < clause.size(); ++i) {
                nlsat::literal l = clause[i];
                if (m_asm2fml.find(l.var(), t)) {
                    fml = t;
                    if (l.sign()) {
                        fml = push_not(fml);
                    }
                    SASSERT(l.sign());
                    fmls.push_back(fml);
                }
                else {
                    fmls.push_back(n2g(m_solver, m_b2a, m_x2t, l));
                }
            }
            fml = mk_or(fmls);
            return fml;
        }

        void add_assumption_literal(clause& clause, expr* fml) {
            nlsat::bool_var b = m_solver.mk_bool_var();
            clause.push_back(nlsat::literal(b, true));
            m_assumptions.push_back(nlsat::literal(b, false)); 
            m_asm2fml.insert(b, fml);
            m_trail.push_back(fml);            
            m_bvar2level.insert(b, max_level());
        }

        bool is_exists() const { return is_exists(level()); }
        bool is_forall() const { return is_forall(level()); }
        bool is_exists(unsigned level) const { return (level % 2) == 0; }        
        bool is_forall(unsigned level) const { return is_exists(level+1); }

        void check_cancel() {
            if (m_cancel) {
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
        }

        struct div {
            expr_ref num, den, name;
            div(ast_manager& m, expr* n, expr* d, expr* nm):
                num(n, m), den(d, m), name(nm, m) {}            
        };

        class div_rewriter_cfg : public default_rewriter_cfg {
            ast_manager&  m;
            arith_util    a;
            vector<div>   m_divs;
        public:
            div_rewriter_cfg(nlqsat& s): m(s.m), a(s.m) {}
            ~div_rewriter_cfg() {}
            br_status reduce_app(func_decl* f, unsigned sz, expr* const* args, expr_ref& result, proof_ref& pr) {
                if (is_decl_of(f, a.get_family_id(), OP_DIV) && sz == 2 && !a.is_numeral(args[1]) && is_ground(args[0]) && is_ground(args[1])) {
                    result = m.mk_fresh_const("div", a.mk_real());
                    m_divs.push_back(div(m, args[0], args[1], result));
                    return BR_DONE;
                }
                return BR_FAILED;
            }
            vector<div> const& divs() const { return m_divs; }
        };

        //template class rewriter_tpl<div_rewriter_cfg>;
        
        
        class div_rewriter_star : public rewriter_tpl<div_rewriter_cfg> {
            div_rewriter_cfg m_cfg;
        public:
            div_rewriter_star(nlqsat& s):
                rewriter_tpl<div_rewriter_cfg>(s.m, false, m_cfg),
                m_cfg(s)
            {}
            vector<div> const& divs() const { return m_cfg.divs(); }
        };

        class is_pure_proc {
            nlqsat&    s;
            arith_util a;
            bool       m_has_divs;
        public:
            is_pure_proc(nlqsat& s): s(s), a(s.m), m_has_divs(false) {}

            void operator()(::var * n) {
                if (!a.is_real(n) && !s.m.is_bool(n)) {
                    throw tactic_exception("not NRA");
                }
            }
            void operator()(app * n) { 
                if (n->get_family_id() == s.m.get_basic_family_id()) {
                    return;
                }
                if (is_uninterp_const(n) && (a.is_real(n) || s.m.is_bool(n))) {
                    return;
                }
                if (a.is_mul(n) || a.is_add(n) || a.is_sub(n) || a.is_uminus(n) || a.is_numeral(n) ||
                    a.is_le(n) || a.is_ge(n) || a.is_lt(n) || a.is_gt(n)) {
                    return;
                }
                expr* n1, *n2;
                if (a.is_div(n, n1, n2) && a.is_numeral(n2)) {
                    return;
                }
                rational r;
                if (a.is_power(n, n1, n2) && a.is_numeral(n2, r) && r.is_unsigned()) {
                    return;
                }
                if (a.is_div(n, n1, n2) && is_ground(n1) && is_ground(n2) && s.m_mode == qsat_t) {
                    m_has_divs = true;
                    return;
                }
                TRACE("qe", tout << "not NRA: " << mk_pp(n, s.m) << "\n";);
                throw tactic_exception("not NRA");
            }
            void operator()(quantifier * n) {}

            bool has_divs() const { return m_has_divs; }
        };

        void purify(expr_ref& fml) {
            is_pure_proc  is_pure(*this);
            {
                expr_fast_mark1 visited;
                quick_for_each_expr(is_pure, visited, fml);
            }
            if (is_pure.has_divs()) {
                arith_util arith(m);
                div_rewriter_star rw(*this);
                proof_ref pr(m);
                rw(fml, fml, pr);
                vector<div> const& divs = rw.divs();
                expr_ref_vector axioms(m);
                for (unsigned i = 0; i < divs.size(); ++i) {
                    axioms.push_back(
                        m.mk_or(m.mk_eq(divs[i].den, arith.mk_numeral(rational(0), false)), 
                                m.mk_eq(divs[i].num, arith.mk_mul(divs[i].den, divs[i].name))));                    
                    for (unsigned j = i + 1; j < divs.size(); ++j) {
                        axioms.push_back(m.mk_or(m.mk_not(m.mk_eq(divs[i].den, divs[j].den)),
                                                 m.mk_not(m.mk_eq(divs[i].num, divs[j].num)), 
                                                 m.mk_eq(divs[i].name, divs[j].name)));
                    }
                }
                axioms.push_back(fml);
                fml = mk_and(axioms);
            }
        }

        void reset() {
            //m_solver.reset();
            m_asms.reset();
            m_cached_asms.reset();
            m_cached_asms_lim.reset();
            m_is_true = nlsat::null_literal;
            m_rmodel.reset();
            m_valid_model = false;
            m_bound_rvars.reset();
            m_bound_bvars.reset();
            m_preds.reset();
            m_rvar2level.reset();
            m_bvar2level.reset();
            m_t2x.reset();
            m_a2b.reset();
            m_b2a.reset();
            m_x2t.reset();
            m_cancel = false;
            m_st.reset();        
            m_solver.collect_statistics(m_st);
            m_free_vars.reset();
            m_aux_vars.reset();
            m_answer.reset();
            m_answer_simplify.reset();
            m_assumptions.reset();
            m_asm2fml.reset();
            m_trail.reset();
        }

        void push() {
            m_cached_asms_lim.push_back(m_cached_asms.size());
        }

        void pop(unsigned num_scopes) {
            clear_model();
            unsigned new_level = level() - num_scopes;
            m_cached_asms.shrink(m_cached_asms_lim[new_level]);
            m_cached_asms_lim.shrink(new_level);
        }

        void display(std::ostream& out) {
            display_preds(out);
            display_assumptions(out);
            m_solver.display(out << "solver:\n");
        }

        void display_assumptions(std::ostream& out) {
            m_solver.display(out << "assumptions: ", m_asms.size(), m_asms.c_ptr());
            out << "\n";
        }

        void display_preds(std::ostream& out) {
            for (unsigned i = 0; i < m_preds.size(); ++i) {                
                m_solver.display(out << i << ": ", m_preds[i].size(), m_preds[i].c_ptr());
                out << "\n";
            }
        }

        // expr -> nlsat::solver

        void hoist(expr_ref& fml) {
            quantifier_hoister hoist(m);
            vector<app_ref_vector> qvars;
            app_ref_vector vars(m);
            bool is_forall = false;   
            pred_abs abs(m);
            purify(fml);
            abs.get_free_vars(fml, vars);
            insert_set(m_free_vars, vars);
            qvars.push_back(vars); 
            vars.reset();  
            if (m_mode == elim_t) {
                is_forall = true;
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.push_back(vars);
            }
            else {
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.back().append(vars);            
            }
            do {
                is_forall = !is_forall;
                vars.reset();
                hoist.pull_quantifier(is_forall, fml, vars);
                qvars.push_back(vars);
            }
            while (!vars.empty());
            SASSERT(qvars.back().empty()); 
            init_expr2var(qvars);

            goal2nlsat g2s;

            expr_ref is_true(m), fml1(m), fml2(m);
            is_true = m.mk_fresh_const("is_true", m.mk_bool_sort());
            fml = m.mk_iff(is_true, fml);
            goal_ref g = alloc(goal, m);
            g->assert_expr(fml);
            proof_converter_ref pc;
            expr_dependency_ref core(m);
            model_converter_ref mc;
            goal_ref_buffer result;
            (*m_nftactic)(g, result, mc, pc, core);
            SASSERT(result.size() == 1);
            TRACE("qe", result[0]->display(tout););
            g2s(*result[0], m_params, m_solver, m_a2b, m_t2x);

            // insert variables and their levels.
            for (unsigned i = 0; i < qvars.size(); ++i) {
                m_bound_bvars.push_back(svector<nlsat::bool_var>());
                m_bound_rvars.push_back(nlsat::var_vector());
                max_level lvl;
                if (is_exists(i)) lvl.m_ex = i; else lvl.m_fa = i;
                for (unsigned j = 0; j < qvars[i].size(); ++j) {
                    app* v = qvars[i][j].get();

                    if (m_a2b.is_var(v)) {
                        SASSERT(m.is_bool(v));
                        nlsat::bool_var b = m_a2b.to_var(v);
                        m_bound_bvars.back().push_back(b);
                        set_level(b, lvl);
                    }
                    else if (m_t2x.is_var(v)) {
                        nlsat::var w = m_t2x.to_var(v);
                        TRACE("qe", tout << mk_pp(v, m) << " |-> " << w << "\n";);
                        m_bound_rvars.back().push_back(w);
                        m_rvar2level.setx(w, lvl, max_level());
                    }
                    else {
                        TRACE("qe", tout << mk_pp(v, m) << " not found\n";);
                    }
                }
            }
            init_var2expr();
            m_is_true = nlsat::literal(m_a2b.to_var(is_true), false);
            // insert literals from arithmetical sub-formulas
            nlsat::atom_vector const& atoms = m_solver.get_atoms();
            TRACE("qe", m_solver.display(tout); );
            for (unsigned i = 0; i < atoms.size(); ++i) {
                if (atoms[i]) {
                    get_level(nlsat::literal(i, false));
                }
            }
            TRACE("qe", tout << fml << "\n";);
        }

        void init_expr2var(vector<app_ref_vector> const& qvars) {
            for (unsigned i = 0; i < qvars.size(); ++i) {
                init_expr2var(qvars[i]);
            }
        }

        void init_expr2var(app_ref_vector const& qvars) {
            for (unsigned i = 0; i < qvars.size(); ++i) {
                app* v = qvars[i];
                if (m.is_bool(v)) {
                    m_a2b.insert(v, m_solver.mk_bool_var());
                }
                else {
                    // TODO: assert it is of type Real.
                    m_t2x.insert(v, m_solver.mk_var(false));
                }
            }
        }

        void init_var2expr() {
            expr2var::iterator it = m_t2x.begin(), end = m_t2x.end();
            for (; it != end; ++it) {
                m_x2t.insert(it->m_value, it->m_key);
            }
            it = m_a2b.begin(), end = m_a2b.end();
            for (; it != end; ++it) {
                m_b2a.insert(it->m_value, it->m_key);
            }
        }

        
        // Return false if nlsat assigned noninteger value to an integer variable.
        // [copied from nlsat_tactic.cpp]
        bool mk_model(model_converter_ref & mc) {
            bool ok = true;
            model_ref md = alloc(model, m);
            arith_util util(m);
            expr2var::iterator it = m_t2x.begin(), end = m_t2x.end();
            for (; it != end; ++it) {
                nlsat::var x = it->m_value;
                expr * t = it->m_key;
                if (!is_uninterp_const(t) || !m_free_vars.contains(t) || m_aux_vars.contains(t))
                    continue;
                expr * v;
                try {
                    v = util.mk_numeral(m_rmodel0.value(x), util.is_int(t));
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception &) {
                    v = util.mk_to_int(util.mk_numeral(m_rmodel0.value(x), false));
                    ok = false;
                }
                md->register_decl(to_app(t)->get_decl(), v);
            }
            it = m_a2b.begin(), end = m_a2b.end();
            for (; it != end; ++it) {
                expr * a = it->m_key;
                nlsat::bool_var b = it->m_value;
                if (a == 0 || !is_uninterp_const(a) || b == m_is_true.var() || !m_free_vars.contains(a) || m_aux_vars.contains(a))
                    continue;
                lbool val = m_bmodel0.get(b, l_undef);
                if (val == l_undef)
                    continue; // don't care
                md->register_decl(to_app(a)->get_decl(), val == l_true ? m.mk_true() : m.mk_false());
            }
            mc = model2model_converter(md.get());
            return ok;
        }

    public:
        nlqsat(ast_manager& m, qsat_mode_t mode, params_ref const& p):
            m(m),
            m_mode(mode),
            m_params(p),
            m_solver(m.limit(), p),
            m_nftactic(0),
            m_rmodel(m_solver.am()),
            m_rmodel0(m_solver.am()),
            m_valid_model(false),
            m_a2b(m),
            m_t2x(m),
            m_cancel(false),
            m_answer(m),
            m_answer_simplify(m),
            m_trail(m)
        {
            m_solver.get_explain().set_signed_project(true);
            m_nftactic = mk_tseitin_cnf_tactic(m);
        }

        virtual ~nlqsat() {
        }

        void updt_params(params_ref const & p) {
            params_ref p2(p);
            p2.set_bool("factor", false);
            m_solver.updt_params(p2);
        }
        
        void collect_param_descrs(param_descrs & r) {
        }

        
        void operator()(/* in */  goal_ref const & in, 
                        /* out */ goal_ref_buffer & result, 
                        /* out */ model_converter_ref & mc, 
                        /* out */ proof_converter_ref & pc,
                        /* out */ expr_dependency_ref & core) {

            tactic_report report("nlqsat-tactic", *in);

            ptr_vector<expr> fmls;
            expr_ref fml(m);
            mc = 0; pc = 0; core = 0;
            in->get_formulas(fmls);
            fml = mk_and(m, fmls.size(), fmls.c_ptr());
            if (m_mode == elim_t) {
                fml = m.mk_not(fml);
            }                         
            reset();
            TRACE("qe", tout << fml << "\n";);
            hoist(fml);
            TRACE("qe", tout << "ex: " << fml << "\n";);
            lbool is_sat = check_sat();
            
            switch (is_sat) {
            case l_false:
                in->reset();
                in->inc_depth();
                if (m_mode == elim_t) {
                    fml = mk_and(m_answer);
                }
                else {
                    fml = m.mk_false();
                }
                in->assert_expr(fml);
                result.push_back(in.get());
                break;
            case l_true:
                SASSERT(m_mode == qsat_t);
                in->reset();
                in->inc_depth();
                result.push_back(in.get());
                if (in->models_enabled()) {
                    VERIFY(mk_model(mc));
                }
                break;
            case l_undef:
                result.push_back(in.get());
                std::string s = "search failed";
                throw tactic_exception(s.c_str()); 
            }        
        }


        void collect_statistics(statistics & st) const {
            st.copy(m_st);
            st.update("qsat num rounds", m_stats.m_num_rounds); 
        }

        void reset_statistics() {
            m_stats.reset();
            m_solver.reset_statistics();
        }

        void cleanup() {
            reset();
        }
        
        void set_logic(symbol const & l) {
        }
        
        void set_progress_callback(progress_callback * callback) {
        }
        
        tactic * translate(ast_manager & m) {
            return alloc(nlqsat, m, m_mode, m_params);
        }

#if 0        

        /**
         
           Algorithm:
           I := true
           while there is M, such that M |= ~B & I:
              find P, such that M => P => exists y . ~B & I
              ; forall y B => ~P
              C := core of P with respect to A
              ; A => ~ C => ~ P 
              I := I & ~C


           Alternative Algorithm: 
           R := false
           while there is M, such that M |= A & ~R:
              find I, such that M => I => forall y . B
              R := R | I              
              
         */

        lbool interpolate(expr* a, expr* b, expr_ref& result) {
            SASSERT(m_mode == interp_t);
            
            reset();
            app_ref enableA(m), enableB(m);
            expr_ref A(m), B(m), fml(m);
            expr_ref_vector fmls(m), answer(m);

            // varsB are private to B.
            nlsat::var_vector vars;
            uint_set fvars;
            private_vars(a, b, vars, fvars);
            
            enableA = m.mk_const(symbol("#A"), m.mk_bool_sort());
            enableB = m.mk_not(enableA);
            A = m.mk_implies(enableA, a);
            B = m.mk_implies(enableB, m.mk_not(b));
            fml = m.mk_and(A, B);
            hoist(fml);

            

            nlsat::literal _enableB = nlsat::literal(m_a2b.to_var(enableB), false);
            nlsat::literal _enableA = ~_enableB;

            while (true) {
                m_mode = qsat_t;
                // enable B
                m_assumptions.reset();
                m_assumptions.push_back(_enableB);
                lbool is_sat = check_sat();

                switch (is_sat) {
                case l_undef:
                    return l_undef;
                case l_true:                    
                    break;
                case l_false:
                    result = mk_and(answer);
                    return l_true;
                }

                // disable B, enable A
                m_assumptions.reset();
                m_assumptions.push_back(_enableA);
                // add blocking clause to solver.

                nlsat::scoped_literal_vector core(m_solver);
                
                m_mode = elim_t;

                mbp(vars, fvars, core);

                // minimize core.
                nlsat::literal_vector _core(core.size(), core.c_ptr());
                _core.push_back(_enableA);
                is_sat = m_solver.check(_core); // TBD: only for quantifier-free A. Generalize output of elim_t to be a core.
                switch (is_sat) {
                case l_undef: 
                    return l_undef;
                case l_true:
                    UNREACHABLE();
                case l_false:
                    core.reset();
                    core.append(_core.size(), _core.c_ptr());
                    break;
                }
                negate_clause(core);
                // keep polarity of enableA, such that clause is only 
                // used when checking satisfiability of B.
                for (unsigned i = 0; i < core.size(); ++i) {
                    if (core[i].var() == _enableA.var()) core.set(i, ~core[i]);
                }
                add_clause(core);                   // Invariant is added as assumption for B.
                answer.push_back(clause2fml(core)); // TBD: remove answer literal.
            }
        }

        /**
           \brief extract variables that are private to a (not used in b).
           vars cover the real variables, and fvars cover the Boolean variables.

           TBD: We want fvars to be the complement such that returned core contains
                Shared boolean variables, but not the ones private to B.
         */
        void private_vars(expr* a, expr* b, nlsat::var_vector& vars, uint_set& fvars) {
            app_ref_vector varsA(m), varsB(m);
            obj_hashtable<expr> varsAS;
            pred_abs abs(m);
            abs.get_free_vars(a, varsA);
            abs.get_free_vars(b, varsB);
            insert_set(varsAS, varsA);
            for (unsigned i = 0; i < varsB.size(); ++i) {
                if (varsAS.contains(varsB[i].get())) {
                    varsB[i] = varsB.back();
                    varsB.pop_back();
                    --i;
                }
            }
            for (unsigned j = 0; j < varsB.size(); ++j) {
                app* v = varsB[j].get();
                if (m_a2b.is_var(v)) {
                    fvars.insert(m_a2b.to_var(v));
                }
                else if (m_t2x.is_var(v)) {
                    vars.push_back(m_t2x.to_var(v));                    
                }
            }
        }

        lbool maximize(app* _x, expr* _fml, scoped_anum& result, bool& unbounded) {
            expr_ref fml(_fml, m);
            reset();
            hoist(fml);
            nlsat::literal_vector lits;
            lbool is_sat = l_true;
            nlsat::var x = m_t2x.to_var(_x);  
            m_mode = qsat_t;
            while (is_sat == l_true) {
                is_sat = check_sat();
                if (is_sat == l_true) {
                    // m_asms is minimized set of literals that satisfy formula.
                    nlsat::explain& ex = m_solver.get_explain();
                    polynomial::manager& pm = m_solver.pm();
                    anum_manager& am = m_solver.am();
                    ex.maximize(x, m_asms.size(), m_asms.c_ptr(), result, unbounded);
                    if (unbounded) {
                        break;
                    }
                    // TBD: assert the new bound on x using the result.
                    bool is_even = false;
                    polynomial::polynomial_ref pr(pm);
                    pr = pm.mk_polynomial(x);
                    rational r;
                    am.get_upper(result, r);
                    // result is algebraic numeral, but polynomials are not defined over extension field.
                    polynomial::polynomial* p = pr;
                    nlsat::bool_var b = m_solver.mk_ineq_atom(nlsat::atom::GT, 1, &p, &is_even);
                    nlsat::literal bound(b, false);
                    m_solver.mk_clause(1, &bound);
                }
            }
            return is_sat;
        }
#endif
    };
};

tactic * mk_nlqsat_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::qsat_t, p);
}

tactic * mk_nlqe_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::elim_t, p);
}


