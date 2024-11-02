/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal2sat.cpp

Abstract:

    "Compile" a goal into the SAT engine.
    Atoms are "abstracted" into boolean variables.
    The mapping between boolean variables and atoms
    can be used to convert back the state of the 
    SAT engine into a goal.

    The idea is to support scenarios such as:
    1) simplify, blast, convert into SAT, and solve
    2) convert into SAT, apply SAT for a while, learn new units, and translate back into a goal.
    3) convert into SAT, apply SAT preprocessor (failed literal propagation, resolution, etc) and translate back into a goal.
    4) Convert boolean structure into SAT, convert atoms into another engine, combine engines using lazy combination, solve.

Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#include "util/ref_util.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/pb_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "model/model_evaluator.h"
#include "model/model_v2_pp.h"
#include "tactic/tactic.h"
#include "ast/converters/generic_model_converter.h"
#include "sat/sat_cut_simplifier.h"
#include "sat/sat_drat.h"
#include "sat/tactic/goal2sat.h"
#include "sat/smt/pb_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "params/sat_params.hpp"
#include<sstream>

struct goal2sat::imp : public sat::sat_internalizer {
    struct frame {
        app *    m_t;
        unsigned m_root:1;
        unsigned m_sign:1;
        unsigned m_idx;
        frame(app * t, bool r, bool s, unsigned idx):
            m_t(t), m_root(r), m_sign(s), m_idx(idx) {}
    };
    ast_manager &               m;
    pb_util                     pb;
    svector<frame>              m_frame_stack;
    svector<sat::literal>       m_result_stack;
    obj_map<app, sat::literal>  m_app2lit;
    u_map<app*>                 m_lit2app;
    unsigned_vector             m_cache_lim;
    app_ref_vector              m_cache_trail;
    obj_hashtable<expr>         m_interface_vars;
    sat::solver_core &          m_solver;
    atom2bool_var &             m_map;
    dep2asm_map &               m_dep2asm;
    obj_map<expr, sat::bool_var>* m_expr2var_replay = nullptr;
    bool                        m_ite_extra;
    unsigned long long          m_max_memory;
    expr_ref_vector             m_trail;
    func_decl_ref_vector        m_unhandled_funs;
    bool                        m_default_external;
    bool                        m_euf = false;
    bool                        m_top_level = false;
    sat::literal_vector         aig_lits;
    
    imp(ast_manager & _m, params_ref const & p, sat::solver_core & s, atom2bool_var & map, dep2asm_map& dep2asm, bool default_external):
        m(_m),
        pb(m),
        m_cache_trail(m),
        m_solver(s),
        m_map(map),
        m_dep2asm(dep2asm),
        m_trail(m),
        m_unhandled_funs(m),
        m_default_external(default_external) {
        updt_params(p);
    }

    sat::cut_simplifier* aig() {
        return m_solver.get_cut_simplifier();
    }

    void updt_params(params_ref const & p) {
        sat_params sp(p);
        m_ite_extra  = p.get_bool("ite_extra", true);
        m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_euf = sp.euf() || sp.smt();
    }

    void throw_op_not_handled(std::string const& s) {
        std::string s0 = "operator " + s + " not supported, apply simplifier before invoking translator";
        throw tactic_exception(std::move(s0));
    }

    symbol m_tseitin = symbol("tseitin");

    euf::th_proof_hint* mk_tseitin(unsigned n, sat::literal const* lits) {
        if (m_euf && ensure_euf()->use_drat())
            return ensure_euf()->mk_smt_hint(m_tseitin, n, lits);
        return nullptr;
    }

    euf::th_proof_hint* mk_tseitin(sat::literal a, sat::literal b) {
        if (m_euf && ensure_euf()->use_drat()) {
            sat::literal lits[2] = { a, b };
            return ensure_euf()->mk_smt_hint(m_tseitin, 2, lits);
        }
        return nullptr;
    }

    euf::th_proof_hint* mk_tseitin(sat::literal a, sat::literal b, sat::literal c) {
        if (m_euf && ensure_euf()->use_drat()) {
            sat::literal lits[3] = { a, b, c };
            return ensure_euf()->mk_smt_hint(m_tseitin, 3, lits);
        }
        return nullptr;
    }

    sat::status mk_status(euf::th_proof_hint* ph = nullptr) const {
        return sat::status::th(false, m.get_basic_family_id(), ph);
    }

    bool relevancy_enabled() {
        return m_euf && ensure_euf()->relevancy_enabled();
    }

    void mk_clause(sat::literal l1, sat::literal l2, euf::th_proof_hint* ph) {
        sat::literal lits[2] = { l1, l2 };
        mk_clause(2, lits, ph);
    }

    void mk_clause(sat::literal l1, sat::literal l2, sat::literal l3, euf::th_proof_hint* ph) {
        sat::literal lits[3] = { l1, l2, l3 };
        mk_clause(3, lits, ph);
    }

    void mk_clause(unsigned n, sat::literal * lits, euf::th_proof_hint* ph) {
        TRACE("goal2sat", tout << "mk_clause: "; for (unsigned i = 0; i < n; i++) tout << lits[i] << " "; tout << "\n";);
        if (relevancy_enabled())
            ensure_euf()->add_aux(n, lits);
        m_solver.add_clause(n, lits, mk_status(ph));
        add_top_level_clause(n, lits);            
    }

    void mk_root_clause(sat::literal l) {
        mk_root_clause(1, &l);
    }

    void mk_root_clause(sat::literal l1, sat::literal l2, euf::th_proof_hint* ph = nullptr) {
        sat::literal lits[2] = { l1, l2 };
        mk_root_clause(2, lits, ph);
    }

    void mk_root_clause(sat::literal l1, sat::literal l2, sat::literal l3, euf::th_proof_hint* ph = nullptr) {
        sat::literal lits[3] = { l1, l2, l3 };
        mk_root_clause(3, lits, ph);
    }

    void mk_root_clause(unsigned n, sat::literal * lits, euf::th_proof_hint* ph = nullptr) {
        TRACE("goal2sat", tout << "mk_root_clause: "; for (unsigned i = 0; i < n; i++) tout << lits[i] << " "; tout << "\n";);
        if (relevancy_enabled())
            ensure_euf()->add_root(n, lits);
        m_solver.add_clause(n, lits, ph ? mk_status(ph) : sat::status::input());
        add_top_level_clause(n, lits);
    }

    sat::bool_var add_var(bool is_ext, expr* n) {
        sat::bool_var v;
        if (m_expr2var_replay && m_expr2var_replay->find(n, v))
            return v;
        v = m_solver.add_var(is_ext);
        if (!is_ext && m_euf && ensure_euf()->use_drat())
            ensure_euf()->set_bool_var2expr(v, n);
        return v;
    }

    sat::bool_var to_bool_var(expr* e) override {
        sat::literal l;
        sat::bool_var v = m_map.to_bool_var(e);
        if (v != sat::null_bool_var) 
            return v;
        if (is_app(e) && m_app2lit.find(to_app(e), l) && !l.sign()) 
            return l.var();
        return sat::null_bool_var;
    }

    void set_expr2var_replay(obj_map<expr, sat::bool_var>* r) override {
        m_expr2var_replay = r;
    }

    sat::bool_var mk_bool_var(expr* t) {
        force_push();
        sat::bool_var v;
        if (!m_expr2var_replay || !m_expr2var_replay->find(t, v))  
            v = add_var(true, t);
        m_map.insert(t, v);
        return v;
    }

    sat::bool_var add_bool_var(expr* t) override {
        force_push();
        sat::bool_var v = m_map.to_bool_var(t);
        if (v == sat::null_bool_var) 
            v = mk_bool_var(t);
        else 
            m_solver.set_external(v);        
        return v;
    }

    unsigned m_num_scopes{ 0 };

    void force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) {
            m_map.push();
            m_cache_lim.push_back(m_cache_trail.size());
        }        
    }

    void push() override {
        ++m_num_scopes;        
    }

    void pop(unsigned n) override {
        if (n <= m_num_scopes) {
            m_num_scopes -= n;
            return;
        }
        n -= m_num_scopes;
        m_num_scopes = 0;        
        m_map.pop(n);
        unsigned k = m_cache_lim[m_cache_lim.size() - n];
        for (unsigned i = m_cache_trail.size(); i-- > k; ) {
            app* t = m_cache_trail.get(i);
            sat::literal lit;
            if (m_app2lit.find(t, lit)) {
                m_app2lit.remove(t);
                m_lit2app.remove(lit.index());
            }
        }
        m_cache_trail.shrink(k);
        m_cache_lim.shrink(m_cache_lim.size() - n);    
    }

    // remove non-external literals from cache.
    void uncache(sat::literal lit) override {    
        app* t = nullptr;
        if (m_lit2app.find(lit.index(), t)) {
            m_lit2app.remove(lit.index());
            m_app2lit.remove(t);
        }     
    }

    void cache(app* t, sat::literal l) override {
        force_push();
        SASSERT(!m_app2lit.contains(t));
        SASSERT(!m_lit2app.contains(l.index()));
        m_app2lit.insert(t, l);
        m_lit2app.insert(l.index(), t);
        m_cache_trail.push_back(t);
    }

    sat::literal get_cached(app* t) const override {
        sat::literal lit = sat::null_literal;
        m_app2lit.find(t, lit);
        return lit;
    }

    bool is_cached(app* t, sat::literal l) const override {
        sat::literal lit = get_cached(t);
        SASSERT(lit == sat::null_literal || l == lit);
        return l == lit;
    }
    
    void convert_atom(expr * t, bool root, bool sign) {       
        SASSERT(m.is_bool(t));
        sat::literal  l;
        sat::bool_var v = m_map.to_bool_var(t);
        if (v == sat::null_bool_var) {
            if (m.is_true(t)) {
                sat::literal tt = sat::literal(mk_bool_var(t), false);
                if (m_euf && ensure_euf()->use_drat())
                    ensure_euf()->set_bool_var2expr(tt.var(), t);
                mk_root_clause(tt);
                l = sign ? ~tt : tt;
            }
            else if (m.is_false(t)) {
                sat::literal ff = sat::literal(mk_bool_var(t), false);
                if (m_euf && ensure_euf()->use_drat())
                    ensure_euf()->set_bool_var2expr(ff.var(), t);
                mk_root_clause(~ff);
                l = sign ? ~ff : ff;
            }
            else if (m_euf) {
                convert_euf(t, root, sign);
                return;
            }
            else {
                if (!is_uninterp_const(t)) {
                    if (!is_app(t)) {
                        std::ostringstream strm;
                        strm << mk_ismt2_pp(t, m);
                        throw_op_not_handled(strm.str());
                    }
                    m_unhandled_funs.push_back(to_app(t)->get_decl());
                }

                v = mk_bool_var(t);
                l = sat::literal(v, sign);
                bool ext = m_default_external || !is_uninterp_const(t) || m_interface_vars.contains(t);
                if (ext)
                    m_solver.set_external(v);
                TRACE("sat", tout << "new_var: " << v << ": " << mk_bounded_pp(t, m, 2) << " " << is_uninterp_const(t) << "\n";);
            }
        }
        else {
            SASSERT(v != sat::null_bool_var);
            l = sat::literal(v, sign);
            m_solver.set_eliminated(v, false);
        }
        SASSERT(l != sat::null_literal);
        if (root)
            mk_root_clause(l);
        else
            m_result_stack.push_back(l);
    }

    bool convert_app(app* t, bool root, bool sign) {
        if (!m_euf && pb.is_pb(t)) {
            m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
            return false;
        }
        else {
            convert_atom(t, root, sign);
            return true;
        }
    }

    bool process_cached(app* t, bool root, bool sign) {
        sat::literal l = sat::null_literal;
        if (!m_app2lit.find(t, l))
            return false;
        if (sign)
            l.neg();
        if (root)
            mk_root_clause(l);
        else
            m_result_stack.push_back(l);
        return true;
    }

    bool visit(expr * t, bool root, bool sign) {
        SASSERT(m.is_bool(t));
        if (!is_app(t)) {
            convert_atom(t, root, sign);
            return true;
        }
        if (process_cached(to_app(t), root, sign))
            return true;
        if (to_app(t)->get_family_id() != m.get_basic_family_id()) 
            return convert_app(to_app(t), root, sign);   
        switch (to_app(t)->get_decl_kind()) {
        case OP_NOT:
        case OP_OR:
        case OP_AND:
        case OP_ITE:
        case OP_XOR:
        case OP_IMPLIES:
            m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
            return false;
        case OP_EQ:            
            if (m.is_bool(to_app(t)->get_arg(1))) {
                m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
                return false;
            }
            else {
                convert_atom(t, root, sign);
                return true;
            }
        case OP_DISTINCT: {
            if (m_euf) {
                convert_euf(t, root, sign);
                return true;
            }                
            TRACE("goal2sat_not_handled", tout << mk_ismt2_pp(t, m) << "\n";);
            std::ostringstream strm;
            strm << mk_ismt2_pp(t, m);
            throw_op_not_handled(strm.str());
        }
        default:
            convert_atom(t, root, sign);
            return true;
        }
    }

    void convert_or(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_or:\n" << mk_bounded_pp(t, m, 2) << " root " << root << " stack " << m_result_stack.size() << "\n";);        
        unsigned num = t->get_num_args();
        SASSERT(num <= m_result_stack.size());
        unsigned old_sz = m_result_stack.size() - num;
        if (root) {
            SASSERT(num == m_result_stack.size());
            if (sign) {
                // this case should not really happen.
                for (unsigned i = 0; i < num; i++) {
                    sat::literal l = m_result_stack[i];
                    l.neg();
                    mk_root_clause(l);
                }
            }
            else {
                mk_root_clause(m_result_stack.size(), m_result_stack.data());
            }
            m_result_stack.shrink(old_sz);
        }
        else {
            if (process_cached(t, root, sign))
                return;
            SASSERT(num <= m_result_stack.size());
            sat::bool_var k = add_var(false, t);
            sat::literal  l(k, false);
            cache(t, l);
            sat::literal * lits = m_result_stack.end() - num;       
            for (unsigned i = 0; i < num; i++) 
                mk_clause(~lits[i], l, mk_tseitin(~lits[i], l));
                       
            m_result_stack.push_back(~l);
            lits = m_result_stack.end() - num - 1;
            if (aig()) {
                aig_lits.reset();
                aig_lits.append(num, lits);
            }
            // remark: mk_clause may perform destructive updated to lits.
            // I have to execute it after the binary mk_clause above.
            mk_clause(num+1, lits, mk_tseitin(num+1, lits));
            if (aig()) 
                aig()->add_or(l, num, aig_lits.data());
                        
            m_solver.set_phase(~l);               
            m_result_stack.shrink(old_sz);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_and(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_and:\n" << mk_bounded_pp(t, m, 2) << " root: " << root  << " result stack: " << m_result_stack.size() << "\n";);

        unsigned num = t->get_num_args();
        unsigned old_sz = m_result_stack.size() - num;
        SASSERT(num <= m_result_stack.size());
        if (root) {
            if (sign) {
                for (unsigned i = 0; i < num; ++i) {
                    m_result_stack[i].neg();
                }                
                mk_root_clause(m_result_stack.size(), m_result_stack.data());
            }
            else {
                for (unsigned i = 0; i < num; ++i) {
                    mk_root_clause(m_result_stack[i]);
                }
            }
            m_result_stack.shrink(old_sz);
        }
        else {
            if (process_cached(t, root, sign))
                return;
            SASSERT(num <= m_result_stack.size());
            sat::bool_var k = add_var(false, t);
            sat::literal  l(k, false);
            cache(t, l);
            sat::literal * lits = m_result_stack.end() - num;

            // l => /\ lits
            for (unsigned i = 0; i < num; i++) {
                mk_clause(~l, lits[i], mk_tseitin(~l, lits[i]));
            }
            // /\ lits => l
            for (unsigned i = 0; i < num; ++i) {
                m_result_stack[m_result_stack.size() - num + i].neg();
            }
            m_result_stack.push_back(l);
            lits = m_result_stack.end() - num - 1;
            if (aig()) {
                aig_lits.reset();
                aig_lits.append(num, lits);
            }
            mk_clause(num+1, lits, mk_tseitin(num+1, lits));
            if (aig()) {
                aig()->add_and(l, num, aig_lits.data());
            }        
            m_solver.set_phase(l);               
            if (sign)
                l.neg();
            
            m_result_stack.shrink(old_sz);
            m_result_stack.push_back(l);
        }
    }

    void convert_ite(app * n, bool root, bool sign) {
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 3);
        sat::literal  c = m_result_stack[sz-3];
        sat::literal  t = m_result_stack[sz-2];
        sat::literal  e = m_result_stack[sz-1];
        m_result_stack.shrink(sz - 3);
        if (root) {
            SASSERT(sz == 3);
            if (sign) {
                mk_root_clause(~c, ~t);
                mk_root_clause(c,  ~e);
            }
            else {
                mk_root_clause(~c, t);
                mk_root_clause(c, e);
            }
        }
        else {
            if (process_cached(n, root, sign))
                return;
            sat::bool_var k = add_var(false, n);
            sat::literal  l(k, false);
            cache(n, l);
            mk_clause(~l, ~c, t, mk_tseitin(~l, ~c, t));
            mk_clause(~l,  c, e, mk_tseitin(~l, c, e));
            mk_clause(l,  ~c, ~t, mk_tseitin(l, ~c, ~t));
            mk_clause(l,   c, ~e, mk_tseitin(l, c, ~e));
            if (m_ite_extra) {
                mk_clause(~t, ~e, l, mk_tseitin(~t, ~e, l));
                mk_clause(t,  e, ~l, mk_tseitin(t, e, ~l));
            }
            if (aig()) aig()->add_ite(l, c, t, e);
            if (sign)
                l.neg();

            m_result_stack.push_back(l);
        }
    }

    void convert_not(app* t, bool root, bool sign) {
        SASSERT(t->get_num_args() == 1);
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 1);
        sat::literal  lit = m_result_stack[sz - 1];
        m_result_stack.shrink(sz - 1);
        if (root) {
            SASSERT(sz == 1);
            mk_root_clause(sign ? lit : ~lit);            
        }
        else {
            if (process_cached(t, root, sign))
                return;
            sat::bool_var k = add_var(false, t);
            sat::literal  l(k, false);
            cache(t, l);
            // l <=> ~lit
            mk_clause(lit, l, mk_tseitin(lit, l));
            mk_clause(~lit, ~l, mk_tseitin(~lit, ~l));
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_implies(app* t, bool root, bool sign) {
        SASSERT(t->get_num_args() == 2);
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 2);
        sat::literal  l2 = m_result_stack[sz - 1];
        sat::literal  l1 = m_result_stack[sz - 2];
        m_result_stack.shrink(sz - 2);
        if (root) {
            SASSERT(sz == 2);
            if (sign) {
                mk_root_clause(l1);
                mk_root_clause(~l2);
            }
            else {
                mk_root_clause(~l1, l2);
            }            
        }
        else {
            if (process_cached(t, root, sign))
                return;
            sat::bool_var k = add_var(false, t);
            sat::literal  l(k, false);
            cache(t, l);
            // l <=> (l1 => l2)
            mk_clause(~l, ~l1, l2, mk_tseitin(~l, ~l1, l2));
            mk_clause(l1, l, mk_tseitin(l1, l));
            mk_clause(~l2, l, mk_tseitin(~l2, l));
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_iff(app * t, bool root, bool sign) {
        if (t->get_num_args() != 2)            
            throw default_exception("unexpected number of arguments to " + mk_pp(t, m));
        SASSERT(t->get_num_args() == 2);
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 2);
        sat::literal  l1 = m_result_stack[sz-1];
        sat::literal  l2 = m_result_stack[sz-2];
        m_result_stack.shrink(sz - 2);
        if (root) {
            if (m.is_xor(t))
                sign = !sign;
            SASSERT(sz == 2);
            if (sign) {
                mk_root_clause(l1, l2);
                mk_root_clause(~l1, ~l2);
            }
            else {
                mk_root_clause(l1, ~l2);
                mk_root_clause(~l1, l2);
            }                  
        }
        else {
            if (process_cached(t, root, sign))
                return;
            sat::bool_var k = add_var(false, t);
            sat::literal  l(k, false);
            if (m.is_xor(t))
                l1.neg();
            mk_clause(~l,  l1, ~l2, mk_tseitin(~l, l1, ~l2));
            mk_clause(~l, ~l1,  l2, mk_tseitin(~l, ~l1, l2));
            mk_clause(l,   l1,  l2, mk_tseitin(l, l1, l2));
            mk_clause(l,  ~l1, ~l2, mk_tseitin(l, ~l1, ~l2));
            if (aig()) aig()->add_iff(l, l1, l2);

            cache(t, l);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    func_decl_ref_vector const& interpreted_funs() {
        auto* ext = dynamic_cast<euf::solver*>(m_solver.get_extension());
        if (ext)
            return ext->unhandled_functions();
        return m_unhandled_funs;
    }

    euf::solver* ensure_euf() {
        SASSERT(m_euf);
        sat::extension* ext = m_solver.get_extension();
        euf::solver* euf = nullptr;
        if (!ext) {
            euf = alloc(euf::solver, m, *this);
            m_solver.set_extension(euf);
#if 0
            std::function<solver*(void)> mk_solver = [&]() {
                return mk_inc_sat_solver(m, m_params, true);
            };
            euf->set_mk_solver(mk_solver);
#endif
        }
        else {
            euf = dynamic_cast<euf::solver*>(ext);
        }
        if (!euf)
            throw default_exception("cannot convert to euf");
        return euf;
    }

    void convert_euf(expr* e, bool root, bool sign) {
        SASSERT(m_euf);
        TRACE("goal2sat", tout << "convert-euf " << mk_bounded_pp(e, m, 2) << " root " << root << "\n";);
        euf::solver* euf = ensure_euf();
        sat::literal lit;
        {
            flet<bool> _top(m_top_level, false);
            lit = euf->internalize(e, sign, root);           
        }
        if (lit == sat::null_literal) 
            return;
        if (root)
            mk_root_clause(lit);
        else
            m_result_stack.push_back(lit);
    }

    void convert_ba(app* t, bool root, bool sign) {
        SASSERT(!m_euf);
        sat::extension* ext = dynamic_cast<pb::solver*>(m_solver.get_extension());
        euf::th_solver* th = nullptr;
        if (!ext) {
            th = alloc(pb::solver, m, *this, pb.get_family_id());
            m_solver.set_extension(th);
            th->push_scopes(m_solver.num_scopes());
        }
        else {
            th = dynamic_cast<euf::th_solver*>(ext);
            SASSERT(th);
        }
        auto lit = th->internalize(t, sign, root);
        m_result_stack.shrink(m_result_stack.size() - t->get_num_args());
        if (lit == sat::null_literal)
            return;
        if (root) 
            mk_root_clause(lit);        
        else 
            m_result_stack.push_back(lit);      
    }

    void convert(app * t, bool root, bool sign) {
        if (t->get_family_id() == m.get_basic_family_id()) {
            switch (to_app(t)->get_decl_kind()) {
            case OP_OR:
                convert_or(t, root, sign);
                break;
            case OP_AND:
                convert_and(t, root, sign);
                break;
            case OP_ITE:
                convert_ite(t, root, sign);
                break;
            case OP_EQ:
                convert_iff(t, root, sign);
                break;
            case OP_XOR:
                convert_iff(t, root, sign);
                break;
            case OP_IMPLIES:
                convert_implies(t, root, sign);
                break;
            case OP_NOT:
                convert_not(t, root, sign);
                break;
            default:
                UNREACHABLE();
            }
            SASSERT(!root || m_result_stack.empty());
        }
        else if (!m_euf && pb.is_pb(t)) {
            convert_ba(t, root, sign);
        }
        else {
            UNREACHABLE();
        }
    }

    struct scoped_stack {
        imp& i;
        sat::literal_vector& r;
        unsigned rsz;
        svector<frame>& frames;
        unsigned fsz;
        bool is_root;
        scoped_stack(imp& x, bool is_root) :
            i(x), r(i.m_result_stack), rsz(r.size()), frames(x.m_frame_stack), fsz(frames.size()), is_root(is_root)
        {}
        ~scoped_stack() {
            if (frames.size() > fsz) {
                frames.shrink(fsz);
                r.shrink(rsz);
                return;
            }
            SASSERT(i.m.limit().is_canceled() || frames.size() == fsz);
            SASSERT(i.m.limit().is_canceled() || !is_root || rsz == r.size());
            SASSERT(i.m.limit().is_canceled() || is_root || rsz + 1 == r.size());
        }
    };

    void process(expr* n, bool is_root) {
        TRACE("goal2sat", tout << "process-begin " << mk_bounded_pp(n, m, 2) 
            << " root: " << is_root 
            << " result-stack: " << m_result_stack.size() 
            << " frame-stack: " << m_frame_stack.size() << "\n";);
        scoped_stack _sc(*this, is_root);
        unsigned sz = m_frame_stack.size();
        if (visit(n, is_root, false)) 
            return;
        
        while (m_frame_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            unsigned fsz = m_frame_stack.size();
            frame const& _fr = m_frame_stack[fsz-1];
            app * t    = _fr.m_t;
            bool root  = _fr.m_root;
            bool sign  = _fr.m_sign;
            TRACE("goal2sat_bug", tout << "result stack\n";
            tout << "ref-count: " << t->get_ref_count() << "\n";
                  tout << mk_bounded_pp(t, m, 3) << " root: " << root << " sign: " << sign << "\n";
                  tout << m_result_stack << "\n";);
            if (_fr.m_idx == 0 && process_cached(t, root, sign)) {
                m_frame_stack.pop_back();
                continue;
            }
            if (m.is_not(t) && (root || (!m.is_not(t->get_arg(0)) && fsz != sz + 1))) {
                m_frame_stack.pop_back();
                visit(t->get_arg(0), root, !sign);
                continue;
            }
            unsigned num = t->get_num_args();
            while (m_frame_stack[fsz-1].m_idx < num) {
                expr * arg = t->get_arg(m_frame_stack[fsz-1].m_idx);
                m_frame_stack[fsz - 1].m_idx++;
                if (!visit(arg, false, false))
                    goto loop;
                TRACE("goal2sat_bug", tout << "visit " << mk_bounded_pp(arg, m, 2) << " result stack: " << m_result_stack.size() << "\n";);
            }
            TRACE("goal2sat_bug", tout << "converting\n";
                  tout << mk_bounded_pp(t, m, 2) << " root: " << root << " sign: " << sign << "\n";
                  tout << m_result_stack << "\n";);
            SASSERT(m_frame_stack.size() > sz);
            convert(t, root, sign);
            m_frame_stack.pop_back();            
        }
        TRACE("goal2sat", tout 
            << "done process: " << mk_bounded_pp(n, m, 3) 
            << " frame-stack: " << m_frame_stack.size() 
            << " result-stack: " << m_result_stack.size() << "\n";);
    }

    sat::literal internalize(expr* n) override {
        bool is_not = m.is_not(n, n);
        flet<bool> _top(m_top_level, false);
        unsigned sz = m_result_stack.size();
        (void)sz;
        SASSERT(n->get_ref_count() > 0);
        TRACE("goal2sat", tout << "internalize " << mk_bounded_pp(n, m, 2) << "\n";);
        process(n, false);
        SASSERT(m_result_stack.size() == sz + 1);
        sat::literal result = m_result_stack.back();
        TRACE("goal2sat", tout << "done internalize " << result << " " << mk_bounded_pp(n, m, 2) << "\n";);
        m_result_stack.pop_back();
        if (!result.sign() && m_map.to_bool_var(n) == sat::null_bool_var) {
            force_push();
            m_map.insert(n, result.var());    
            m_solver.set_external(result.var());
        }

        if (is_not)
            result.neg();
        return result;
    }

    bool is_bool_op(expr* t) const override {
        if (!is_app(t))
            return false;
        if (to_app(t)->get_family_id() == m.get_basic_family_id()) {
            switch (to_app(t)->get_decl_kind()) {
            case OP_OR:
            case OP_AND:             
            case OP_TRUE:
            case OP_FALSE:
            case OP_NOT:
            case OP_IMPLIES:
            case OP_XOR:
                return true;
            case OP_ITE:
            case OP_EQ:
                return m.is_bool(to_app(t)->get_arg(1));
            default:
                return false;
            }
        }
        else if (!m_euf && to_app(t)->get_family_id() == pb.get_family_id()) 
            return true;        
        else 
            return false;       
    }
    
    void process(expr * n) {
        flet<bool> _top(m_top_level, true);
        VERIFY(m_result_stack.empty());
        TRACE("goal2sat", tout << "assert: " << mk_bounded_pp(n, m, 3) << "\n";);
        process(n, true);
        CTRACE("goal2sat", !m_result_stack.empty(), tout << m_result_stack << "\n";);
        SASSERT(m_result_stack.empty());
    }

    void insert_dep(expr* dep0, expr* dep, bool sign) {
        SASSERT(sign || dep0 == dep); // !sign || (not dep0) == dep.
        SASSERT(!sign || m.is_not(dep0));
        expr_ref new_dep(m), fml(m);
        if (is_uninterp_const(dep)) {
            new_dep = dep;
        }
        else {
            new_dep = m.mk_fresh_const("dep", m.mk_bool_sort());
            m_trail.push_back(new_dep);
            m_interface_vars.insert(new_dep);
            fml = m.mk_iff(new_dep, dep);
            process(fml);            
        }
        convert_atom(new_dep, false, false);
        sat::literal lit = m_result_stack.back();
        m_dep2asm.insert(dep0, sign?~lit:lit);
        m_result_stack.pop_back();
    }

    struct scoped_reset {
        imp& i;
        scoped_reset(imp& i) :i(i) {}
        ~scoped_reset() {
            i.m_interface_vars.reset();
            i.m_app2lit.reset();
            i.m_lit2app.reset();
        }
    };
    
    void operator()(unsigned n, expr* const* fmls) {
        scoped_reset _reset(*this);
        // collect_boolean_interface(g, m_interface_vars);
        for (unsigned i = 0; i < n; ++i) 
            process(fmls[i]);
    }

    void assumptions(unsigned n, expr* const* fmls) {
        scoped_reset _reset(*this);
        // collect_boolean_interface(g, m_interface_vars);
        for (unsigned i = 0; i < n; ++i) {
            expr* f = fmls[i];
            expr* f1 = f;
            bool sign = m.is_not(f, f1);
            insert_dep(f, f1, sign);
        }
    }


    void operator()(goal const & g) {
        scoped_reset _reset(*this);
        collect_boolean_interface(g, m_interface_vars);
        unsigned size = g.size();
        expr_ref f(m), d_new(m);
        ptr_vector<expr> deps;
        expr_ref_vector  fmls(m);
        if (m_euf)
            ensure_euf();
        for (unsigned idx = 0; idx < size; idx++) {
            f = g.form(idx);
            // Add assumptions.
            if (g.dep(idx)) {
                deps.reset();
                fmls.reset();
                m.linearize(g.dep(idx), deps);
                fmls.push_back(f);
                for (expr * d : deps) {
                    expr * d1 = d;
                    SASSERT(m.is_bool(d));
                    bool sign = m.is_not(d, d1);

                    insert_dep(d, d1, sign);
                    if (d == f) {
                        goto skip_dep;
                    }
                    if (sign) {
                        d_new = d1;
                    }
                    else {
                        d_new = m.mk_not(d);
                    }
                    fmls.push_back(d_new);
                }                
                f = m.mk_or(fmls);
            }
            TRACE("goal2sat", tout << mk_bounded_pp(f, m, 2) << "\n";);
            process(f);
        skip_dep:
            ;
        }
    }

    void add_top_level_clause(unsigned n, sat::literal const* lits) {
        if (!m_top_level)
            return;
        auto* ext = dynamic_cast<euf::solver*>(m_solver.get_extension());
        if (ext)
            ext->add_clause(n, lits);
    }

    void update_model(model_ref& mdl) {
        auto* ext = dynamic_cast<euf::solver*>(m_solver.get_extension());
        if (ext)
            ext->update_model(mdl, true);
    }

    void user_push() {
        push();
    }

    void user_pop(unsigned n) {
        pop(n);
    }

};

struct unsupported_bool_proc {
    struct found {};
    ast_manager & m;
    unsupported_bool_proc(ast_manager & _m):m(_m) {}
    void operator()(var *) {}
    void operator()(quantifier *) {}
    void operator()(app * n) { 
        if (n->get_family_id() == m.get_basic_family_id()) {
            switch (n->get_decl_kind()) {
            case OP_DISTINCT:
                throw found();
            default:
                break;
            }
        }
    }
};

/**
   \brief Return true if s contains an unsupported Boolean operator.
   goal_rewriter (with the following configuration) can be used to
   eliminate unsupported operators.
      :elim-and true
      :blast-distinct true
*/
bool goal2sat::has_unsupported_bool(goal const & g) {
    return false && test<unsupported_bool_proc>(g);
}

goal2sat::goal2sat():
    m_imp(nullptr) {
}

goal2sat::~goal2sat() {
    dealloc(m_imp);
}

euf::solver* goal2sat::ensure_euf() {
    return m_imp->ensure_euf();
}


void goal2sat::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("ite_extra", CPK_BOOL, "(default: true) add redundant clauses (that improve unit propagation) when encoding if-then-else formulas");
}

void goal2sat::init(ast_manager& m, params_ref const & p, sat::solver_core & t, atom2bool_var & map, dep2asm_map& dep2asm, bool default_external) {
    if (!m_imp) {
        m_imp = alloc(imp, m, p, t, map, dep2asm, default_external);
        for (unsigned i = 0; i < m_scopes; ++i)
            m_imp->user_push();
    }
}

void goal2sat::operator()(goal const & g, params_ref const & p, sat::solver_core & t, atom2bool_var & m, dep2asm_map& dep2asm, bool default_external) {
    init(g.m(), p, t, m, dep2asm, default_external);
    (*m_imp)(g);    
}

void goal2sat::operator()(unsigned n, expr* const* fmls) {
    SASSERT(m_imp);
    (*m_imp)(n, fmls);
}

void goal2sat::assumptions(unsigned n, expr* const* fmls) {
    SASSERT(m_imp);
    m_imp->assumptions(n, fmls);
}

sat::literal goal2sat::internalize(expr* a) {
    SASSERT(m_imp);
    return m_imp->internalize(a);
}


void goal2sat::get_interpreted_funs(func_decl_ref_vector& funs) {
    if (m_imp) 
        funs.append(m_imp->interpreted_funs());
}

bool goal2sat::has_interpreted_funs() const {
    return m_imp && !m_imp->interpreted_funs().empty(); 
}

bool goal2sat::has_euf() const {
    return m_imp && m_imp->m_euf;
}

void goal2sat::update_model(model_ref& mdl) {
    if (m_imp) 
        m_imp->update_model(mdl);
}

void goal2sat::user_push() {
    if (m_imp)
        m_imp->user_push();
    else 
        m_scopes++;
}
    
void goal2sat::user_pop(unsigned n) {
    if (m_imp)
        m_imp->user_pop(n);
    else
        m_scopes -= n;
}


sat::sat_internalizer& goal2sat::si(ast_manager& m, params_ref const& p, sat::solver_core& t, atom2bool_var& a2b, dep2asm_map& dep2asm, bool default_external) {
    if (!m_imp)
        m_imp = alloc(imp, m, p, t, a2b, dep2asm, default_external);
    return *m_imp;
}
