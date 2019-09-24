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

#include "util/uint_set.h"
#include "util/scoped_ptr_vector.h"
#include "ast/expr2var.h"
#include "ast/ast_util.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/quant_hoist.h"
#include "qe/nlqsat.h"
#include "qe/qsat.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_explain.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/tactic/goal2nlsat.h"
#include "tactic/core/tseitin_cnf_tactic.h"


namespace qe {

    enum qsat_mode_t {
        qsat_t,
        elim_t
    };

    class nlqsat : public tactic {

        typedef unsigned_vector assumption_vector;
        typedef nlsat::scoped_literal_vector clause;

        struct stats {
            unsigned m_num_rounds;        
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }            
        };
        
        struct solver_state {
            ast_manager&           m;
            params_ref             m_params;
            nlsat::solver          m_solver;
            nlsat::literal         m_is_true;
            nlsat::assignment      m_rmodel;        
            svector<lbool>         m_bmodel;
            nlsat::assignment      m_rmodel0;        
            svector<lbool>         m_bmodel0;
            bool                   m_valid_model;
            vector<nlsat::var_vector>            m_bound_rvars;
            vector<svector<nlsat::bool_var> >    m_bound_bvars;
            scoped_ptr_vector<nlsat::scoped_literal_vector> m_preds;
            svector<max_level>                   m_rvar2level;
            u_map<max_level>                     m_bvar2level;
            expr2var                             m_a2b, m_t2x;
            u_map<expr*>                         m_b2a, m_x2t;
            nlsat::literal_vector                m_assumptions;            
            nlsat::literal_vector                m_asms;
            nlsat::literal_vector                m_cached_asms;
            unsigned_vector                      m_cached_asms_lim;
            u_map<expr*>                         m_asm2fml;
            solver_state(ast_manager& m, params_ref const& p):
                m(m),
                m_params(p),
                m_solver(m.limit(), p, true),
                m_rmodel(m_solver.am()),
                m_rmodel0(m_solver.am()),
                m_valid_model(false),
                m_a2b(m),
                m_t2x(m)
            {}

            void g2s(goal const& g) {
                goal2nlsat gs;
                gs(g, m_params, m_solver, m_a2b, m_t2x);
            }

            void init_expr2var(vector<app_ref_vector> const& qvars) {
                for (app_ref_vector const& qvs : qvars) {
                    init_expr2var(qvs);
                }
            }
            
            void init_expr2var(app_ref_vector const& qvars) {
                for (app* v : qvars) {
                    if (m.is_bool(v)) {
                        nlsat::bool_var b = m_solver.mk_bool_var();
                        m_solver.inc_ref(b);
                        m_a2b.insert(v, b);
                    }
                    else {
                        // TODO: assert it is of type Real.
                        m_t2x.insert(v, m_solver.mk_var(false));
                    }
                }
            }
            
            void init_var2expr() {
                for (auto const& kv : m_t2x) {
                    m_x2t.insert(kv.m_value, kv.m_key);
                }
                for (auto const& kv : m_a2b) {
                    m_b2a.insert(kv.m_value, kv.m_key);
                }
            }

            void save_model(bool is_exists) {
                svector<nlsat::bool_var> bvars;
                for (auto const& kv : m_bvar2level) {
                    bvars.push_back(kv.m_key);
                }
                m_solver.get_rvalues(m_rmodel);
                m_solver.get_bvalues(bvars, m_bmodel);
                m_valid_model = true;
                if (is_exists) {
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

            void add_assumption_literal(clause& clause, expr* fml) {
                nlsat::bool_var b = m_solver.mk_bool_var();
                clause.push_back(nlsat::literal(b, true));
                m_assumptions.push_back(nlsat::literal(b, false)); 
                m_solver.inc_ref(b);
                m_asm2fml.insert(b, fml);
                m_bvar2level.insert(b, max_level());
            }

            expr_ref clause2fml(nlsat::scoped_literal_vector const& clause) {
                expr_ref_vector fmls(m);
                expr_ref fml(m);
                expr* t;
                nlsat2goal n2g(m);
                for (nlsat::literal l : clause) {
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
                    lits.push_back(l);
                    break; 
                }
            }
        
            void display(std::ostream& out) {
                out << "level " << level() << "\n";
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
                    m_solver.display(out << i << ": ", m_preds[i]->size(), m_preds[i]->c_ptr());
                    out << "\n";
                }
            }

            unsigned level() const {
                return m_cached_asms_lim.size();
            }

            void reset() {
                m_asms.reset();
                m_cached_asms.reset();
                m_cached_asms_lim.reset();
                m_is_true = nlsat::null_literal;
                m_rmodel.reset();
                m_valid_model = false;
                m_bound_rvars.reset();
                m_bound_bvars.reset();
                m_preds.reset();
                for (auto const& kv : m_bvar2level) {
                    m_solver.dec_ref(kv.m_key);
                }
                m_rvar2level.reset();
                m_bvar2level.reset();
                m_t2x.reset();
                m_a2b.reset();
                m_b2a.reset();
                m_x2t.reset();
                m_assumptions.reset();
                m_asm2fml.reset();
            }
        };
        ast_manager&           m;
        solver_state           s;
        qsat_mode_t            m_mode;
        params_ref             m_params;
        tactic_ref             m_nftactic;
        stats                  m_stats;
        statistics             m_st;
        obj_hashtable<expr>    m_free_vars;
        obj_hashtable<expr>    m_aux_vars;
        expr_ref_vector        m_answer;
        expr_safe_replace      m_answer_simplify;
        expr_ref_vector        m_trail;
        
        lbool check_sat() {
            while (true) {
                ++m_stats.m_num_rounds;
                check_cancel();
                init_assumptions();   
                lbool res = s.m_solver.check(s.m_asms);
                TRACE("qe", s.display(tout << res << "\n"); );
                switch (res) {
                case l_true:
                    s.save_model(is_exists(level()));
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
            s.m_asms.reset();
            s.m_asms.push_back(is_exists()?s.m_is_true:~s.m_is_true);
            s.m_asms.append(s.m_assumptions);
            TRACE("qe", tout << "model valid: " << s.m_valid_model << " level: " << lvl << " "; 
                  s.display_assumptions(tout);
                  s.m_solver.display(tout););

            if (!s.m_valid_model) {
                s.m_asms.append(s.m_cached_asms);
                return;
            }            
            s.unsave_model();
            if (lvl == 0) {
                SASSERT(s.m_cached_asms.empty());
                return;
            }
            if (lvl <= s.m_preds.size()) {
                for (unsigned j = 0; j < s.m_preds[lvl - 1]->size(); ++j) {
                    s.add_literal(s.m_cached_asms, (*s.m_preds[lvl - 1])[j]);
                }
            }
            s.m_asms.append(s.m_cached_asms);
            
            for (unsigned i = lvl + 1; i < s.m_preds.size(); i += 2) {
                for (unsigned j = 0; j < s.m_preds[i]->size(); ++j) {
                    nlsat::literal l = (*s.m_preds[i])[j];
                    max_level lv = s.m_bvar2level.find(l.var());
                    bool use = 
                        (lv.m_fa == i && (lv.m_ex == UINT_MAX || lv.m_ex < lvl)) ||
                        (lv.m_ex == i && (lv.m_fa == UINT_MAX || lv.m_fa < lvl));
                    if (use) {
                        s.add_literal(s.m_asms, l);
                    }
                }
            }
            TRACE("qe", s.display(tout);
                  tout << "assumptions\n";
                  for (nlsat::literal a : s.m_asms) {
                      s.m_solver.display(tout, a) << "\n";
                  });
            s.save_model(is_exists(level()));
        }


        template<class S, class T>
        void insert_set(S& set, T const& vec) {
            for (auto const& v : vec) {
                set.insert(v);
            }
        }        

        void mbp(unsigned level, nlsat::scoped_literal_vector& result) {
            nlsat::var_vector vars;
            uint_set fvars;
            extract_vars(level, vars, fvars);
            mbp(vars, fvars, result);
        }

        void extract_vars(unsigned level, nlsat::var_vector& vars, uint_set& fvars) {
            for (unsigned i = 0; i < s.m_bound_rvars.size(); ++i) {
                if (i < level) {
                    insert_set(fvars, s.m_bound_bvars[i]);
                }
                else {
                    vars.append(s.m_bound_rvars[i]);
                }
            }
        }

        void display_project(std::ostream& out, nlsat::var v, nlsat::scoped_literal_vector const& r1, nlsat::scoped_literal_vector const& r2) {
            for (auto const& kv : s.m_x2t) {
                out << "(declare-const x" << kv.m_key << " Real)\n";
            }
            s.m_solver.display(out << "(assert (not (exists ((", v) << " Real)) \n";
            s.m_solver.display_smt2(out << "(and ", r1.size(), r1.c_ptr()) << "))))\n";
            s.m_solver.display_smt2(out << "(assert (and ", r2.size(), r2.c_ptr()); out << "))\n";
            out << "(check-sat)\n(reset)\n";            
        }

        void mbp(nlsat::var_vector const& vars, uint_set const& fvars, clause& result) {
            // 
            // Also project auxiliary variables from clausification.
            // 
            s.unsave_model();
            nlsat::explain& ex = s.m_solver.get_explain();
            nlsat::scoped_literal_vector new_result(s.m_solver);
            result.reset();
            // project quantified Boolean variables.
            for (nlsat::literal lit : s.m_asms) {
                if (!s.m_b2a.contains(lit.var()) || fvars.contains(lit.var())) {
                    result.push_back(lit);
                }
            }
            TRACE("qe", s.m_solver.display(tout, result.size(), result.c_ptr()); tout << "\n";);
            // project quantified real variables.
            // They are sorted by size, so we project the largest variables first to avoid 
            // renaming variables. 
            for (unsigned i = vars.size(); i-- > 0;) {
                new_result.reset();
                ex.project(vars[i], result.size(), result.c_ptr(), new_result);
                TRACE("qe", display_project(tout, vars[i], result, new_result););                
                TRACE("qe", display_project(std::cout, vars[i], result, new_result););
                result.swap(new_result);
            }
            negate_clause(result);
        }

        void negate_clause(clause& result) {
            for (unsigned i = 0; i < result.size(); ++i) {
                result.set(i, ~result[i]);
            }
        }

        unsigned level() const { 
            return s.level();
        }

        void enforce_parity(clause& cl) {
            cl.push_back(is_exists()?~s.m_is_true:s.m_is_true);
        }

        void add_clause(clause& cl) {
            if (cl.empty()) {
                cl.push_back(~s.m_solver.mk_true());
            }
            SASSERT(!cl.empty());
            nlsat::literal_vector lits(cl.size(), cl.c_ptr());
            s.m_solver.mk_clause(lits.size(), lits.c_ptr());
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
            if (s.m_bvar2level.find(l.var(), level)) {
                return level;
            }
            nlsat::var_vector vs;
            s.m_solver.vars(l, vs);
            TRACE("qe", s.m_solver.display(tout << vs << " ", l) << "\n";);
            for (unsigned v : vs) {
                level.merge(s.m_rvar2level[v]);                
            }
            set_level(l.var(), level);
            return level;
        }

        void set_level(nlsat::bool_var v, max_level const& level) {
            unsigned k = level.max();
            while (s.m_preds.size() <= k) {
                s.m_preds.push_back(alloc(nlsat::scoped_literal_vector, s.m_solver));
            }
            nlsat::literal l(v, false);
            s.m_preds[k]->push_back(l);
            s.m_solver.inc_ref(v);
            s.m_bvar2level.insert(v, level);            
            TRACE("qe", s.m_solver.display(tout, l); tout << ": " << level << "\n";);
        }
        
        void project() {
            TRACE("qe", s.display_assumptions(tout););
            if (!s.m_valid_model) {
                pop(1);
                return;
            }
            if (m_mode == elim_t) {
                project_qe();
                return;
            }
            SASSERT(level() >= 2);
            unsigned num_scopes;
            clause cl(s.m_solver);
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
                SASSERT(num_scopes >= 2);
            }
            
            TRACE("qe", tout << "backtrack: " << num_scopes << "\n";);
            pop(num_scopes); 
        }

        void project_qe() {
            SASSERT(level() >= 1 && m_mode == elim_t && s.m_valid_model);
            clause cl(s.m_solver);
            mbp(std::max(1u, level()-1), cl);            
            
            expr_ref fml = s.clause2fml(cl);
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

        void add_assumption_literal(clause& clause, expr* fml) {
            s.add_assumption_literal(clause, fml);
            m_trail.push_back(fml);            
        }

        bool is_exists() const { return is_exists(level()); }
        bool is_forall() const { return is_forall(level()); }
        bool is_exists(unsigned level) const { return (level % 2) == 0; }        
        bool is_forall(unsigned level) const { return is_exists(level+1); }

        void check_cancel() {
        }

        struct div {
            expr_ref num, den;
            app_ref name;
            div(ast_manager& m, expr* n, expr* d, app* nm):
                num(n, m), den(d, m), name(nm, m) {}            
        };

        class div_rewriter_cfg : public default_rewriter_cfg {
            ast_manager&  m;
            arith_util    a;
            expr_ref      m_zero;
            vector<div>   m_divs;
        public:
            div_rewriter_cfg(nlqsat& s): m(s.m), a(s.m), m_zero(a.mk_real(0), m) {}
            ~div_rewriter_cfg() {}
            br_status reduce_app(func_decl* f, unsigned sz, expr* const* args, expr_ref& result, proof_ref& pr) {
                rational r(1);
                if (is_decl_of(f, a.get_family_id(), OP_DIV) && 
                    sz == 2 && (!a.is_numeral(args[1], r) || r.is_zero()) &&
                    is_ground(args[0]) && is_ground(args[1])) {                    
                    result = m.mk_fresh_const("div", a.mk_real());
                    m_divs.push_back(div(m, args[0], args[1], to_app(result)));
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
                rational r;
                if (a.is_div(n, n1, n2) && a.is_numeral(n2, r) && !r.is_zero()) {
                    return;
                }
                if (a.is_power(n, n1, n2) && a.is_numeral(n2, r) && r.is_unsigned()) {
                    return;
                }
                if (a.is_div(n) && s.m_mode == qsat_t && is_ground(n)) {
                    m_has_divs = true;
                    return;
                }
                TRACE("qe", tout << "not NRA: " << mk_pp(n, s.m) << "\n";);
                throw tactic_exception("not NRA");
            }
            void operator()(quantifier * n) {}

            bool has_divs() const { return m_has_divs; }
        };

        /*
          Ackermanize division

          For each p/q:
             q != 0 => div_pq*q = p

          For each p/q, p'/q'
             p = p', q = q' => div_pq = div_pq'

         */

        void ackermanize_div(expr_ref& fml, expr_ref_vector& paxioms) {
            is_pure_proc is_pure(*this);
            {
                expr_fast_mark1 visited;
                quick_for_each_expr(is_pure, visited, fml);
            }
            if (is_pure.has_divs()) {
                arith_util arith(m);
                proof_ref pr(m);
                div_rewriter_star rw(*this);
                rw(fml, fml, pr);
                vector<div> const& divs = rw.divs();
                for (unsigned i = 0; i < divs.size(); ++i) {
                    expr_ref den_is0(m.mk_eq(divs[i].den, arith.mk_real(0)), m);
                    paxioms.push_back(m.mk_or(den_is0, m.mk_eq(divs[i].num, arith.mk_mul(divs[i].den, divs[i].name))));
                    for (unsigned j = i + 1; j < divs.size(); ++j) {
                        paxioms.push_back(m.mk_or(m.mk_not(m.mk_eq(divs[i].den, divs[j].den)),
                                                  m.mk_not(m.mk_eq(divs[i].num, divs[j].num)), 
                                                  m.mk_eq(divs[i].name, divs[j].name)));
                    }
                }
            }
        }

        void reset() override {
            s.reset();
            m_st.reset();        
            s.m_solver.collect_statistics(m_st);
            m_free_vars.reset();
            m_aux_vars.reset();
            m_answer.reset();
            m_answer_simplify.reset();
            m_trail.reset();
        }

        void push() {
            s.m_cached_asms_lim.push_back(s.m_cached_asms.size());
        }

        void pop(unsigned num_scopes) {
            s.clear_model();
            unsigned new_level = level() - num_scopes;
            s.m_cached_asms.shrink(s.m_cached_asms_lim[new_level]);
            s.m_cached_asms_lim.shrink(new_level);
        }

        // expr -> nlsat::solver

        bool hoist(expr_ref& fml) {
            expr_ref_vector paxioms(m);
            ackermanize_div(fml, paxioms);
            quantifier_hoister hoist(m);
            vector<app_ref_vector> qvars;
            app_ref_vector vars(m);
            bool is_forall = false;   
            pred_abs abs(m);
            expr_ref fml_a(m.mk_and(fml, mk_and(paxioms)), m);
            abs.get_free_vars(fml_a, vars);
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
            SASSERT(qvars.size() >= 2);
            SASSERT(qvars.back().empty()); 
            s.init_expr2var(qvars);

            expr_ref is_true(m), fml1(m), fml2(m);
            is_true = m.mk_fresh_const("is_true", m.mk_bool_sort());
            fml = m.mk_iff(is_true, fml);
            goal_ref g = alloc(goal, m);
            g->assert_expr(fml);
            for (expr* f : paxioms) {
                g->assert_expr(f);
            }
            expr_dependency_ref core(m);
            goal_ref_buffer result;
            (*m_nftactic)(g, result);
            SASSERT(result.size() == 1);
            TRACE("qe", result[0]->display(tout););
            s.g2s(*result[0]);

            // insert variables and their levels.
            for (unsigned i = 0; i < qvars.size(); ++i) {
                s.m_bound_bvars.push_back(svector<nlsat::bool_var>());
                s.m_bound_rvars.push_back(nlsat::var_vector());
                max_level lvl;
                if (is_exists(i)) lvl.m_ex = i; else lvl.m_fa = i;
                for (app* v : qvars[i]) {
                    if (s.m_a2b.is_var(v)) {
                        SASSERT(m.is_bool(v));
                        nlsat::bool_var b = s.m_a2b.to_var(v);
                        TRACE("qe", tout << mk_pp(v, m) << " |-> b" << b << "\n";);
                        s.m_bound_bvars.back().push_back(b);
                        set_level(b, lvl);
                    }
                    else if (s.m_t2x.is_var(v)) {
                        nlsat::var w = s.m_t2x.to_var(v);
                        TRACE("qe", tout << mk_pp(v, m) << " |-> x" << w << "\n";);
                        s.m_bound_rvars.back().push_back(w);
                        s.m_rvar2level.setx(w, lvl, max_level());
                    }
                    else {
                        TRACE("qe", tout << mk_pp(v, m) << " not found\n";);
                    }
                }
            }
            s.init_var2expr();
            s.m_is_true = nlsat::literal(s.m_a2b.to_var(is_true), false);
            // insert literals from arithmetical sub-formulas
            nlsat::atom_vector const& atoms = s.m_solver.get_atoms();
            TRACE("qe", s.m_solver.display(tout););
            for (unsigned i = 0; i < atoms.size(); ++i) {
                if (atoms[i]) {
                    get_level(nlsat::literal(i, false));
                }
            }
            TRACE("qe", tout << fml << "\n";);
            return true;
        }


        
        // Return false if nlsat assigned noninteger value to an integer variable.
        // [copied from nlsat_tactic.cpp]
        bool mk_model(model_converter_ref & mc) {
            bool ok = true;
            model_ref md = alloc(model, m);
            arith_util util(m);
            for (auto const& kv : s.m_t2x) {
                nlsat::var x = kv.m_value;
                expr * t = kv.m_key;
                if (!is_uninterp_const(t) || !m_free_vars.contains(t) || m_aux_vars.contains(t))
                    continue;
                expr * v;
                try {
                    v = util.mk_numeral(s.m_rmodel0.value(x), util.is_int(t));
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception &) {
                    v = util.mk_to_int(util.mk_numeral(s.m_rmodel0.value(x), false));
                    ok = false;
                }
                md->register_decl(to_app(t)->get_decl(), v);
            }
            for (auto const& kv : s.m_a2b) {
                expr * a = kv.m_key;
                nlsat::bool_var b = kv.m_value;
                if (a == nullptr || !is_uninterp_const(a) || b == s.m_is_true.var() || !m_free_vars.contains(a) || m_aux_vars.contains(a))
                    continue;
                lbool val = s.m_bmodel0.get(b, l_undef);
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
            s(m, p),
            m_mode(mode),
            m_params(p),
            m_nftactic(nullptr),
            m_answer(m),
            m_answer_simplify(m),
            m_trail(m)
        {
            s.m_solver.get_explain().set_signed_project(true);
            m_nftactic = mk_tseitin_cnf_tactic(m);
        }

        ~nlqsat() override {
        }

        void updt_params(params_ref const & p) override {
            params_ref p2(p);
            p2.set_bool("factor", false);
            s.m_solver.updt_params(p2);
        }
        
        void collect_param_descrs(param_descrs & r) override {
        }

        
        void operator()(/* in */  goal_ref const & in, 
                        /* out */ goal_ref_buffer & result) override {

            tactic_report report("nlqsat-tactic", *in);

            ptr_vector<expr> fmls;
            expr_ref fml(m);
            in->get_formulas(fmls);
            fml = mk_and(m, fmls.size(), fmls.c_ptr());
            if (m_mode == elim_t) {
                fml = m.mk_not(fml);
            }                         
            reset();
            TRACE("qe", tout << fml << "\n";);
            if (!hoist(fml)) {
                result.push_back(in.get());
                return;
            }
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
                    model_converter_ref mc;
                    VERIFY(mk_model(mc));
                    in->add(mc.get());
                }
                break;
            case l_undef:
                result.push_back(in.get());
                throw tactic_exception("search failed");
            }        
        }


        void collect_statistics(statistics & st) const override {
            st.copy(m_st);
            st.update("qsat num rounds", m_stats.m_num_rounds); 
        }

        void reset_statistics() override {
            m_stats.reset();
            s.m_solver.reset_statistics();
        }

        void cleanup() override {
            reset();
        }
        
        void set_logic(symbol const & l) override {
        }
        
        void set_progress_callback(progress_callback * callback) override {
        }
        
        tactic * translate(ast_manager & m) override {
            return alloc(nlqsat, m, m_mode, m_params);
        }
    };
};

tactic * mk_nlqsat_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::qsat_t, p);
}

tactic * mk_nlqe_tactic(ast_manager & m, params_ref const& p) {
    return alloc(qe::nlqsat, m, qe::elim_t, p);
}


