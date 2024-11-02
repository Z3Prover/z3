/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat2goal.cpp

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
#include "sat/tactic/sat2goal.h"
#include "sat/smt/pb_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "params/sat_params.hpp"
#include<sstream>

sat2goal::mc::mc(ast_manager& m): m(m), m_var2expr(m) {}

void sat2goal::mc::flush_smc(sat::solver& s, atom2bool_var const& map) {
    s.flush(m_smc);
    m_var2expr.resize(s.num_vars());
    map.mk_var_inv(m_var2expr);
    flush_gmc();
}

void sat2goal::mc::flush_gmc() {
    sat::literal_vector updates;
    m_smc.expand(updates);    
    if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
    // now gmc owns the model converter
    sat::literal_vector clause;
    expr_ref_vector tail(m);
    expr_ref def(m);
    auto is_literal = [&](expr* e) { expr* r; return is_uninterp_const(e) || (m.is_not(e, r) && is_uninterp_const(r)); };
    
    for (unsigned i = 0; i < updates.size(); ++i) {
        sat::literal l = updates[i];
        if (l == sat::null_literal) {
            sat::literal lit0 = clause[0];
            for (unsigned i = 1; i < clause.size(); ++i) {
                tail.push_back(lit2expr(~clause[i]));
            }
            def = m.mk_or(lit2expr(lit0), mk_and(tail));
            if (lit0.sign()) {
                lit0.neg();
                def = m.mk_not(def);
            }
            expr_ref e = lit2expr(lit0);
            if (is_literal(e))
                m_gmc->add(e, def);
            clause.reset();
            tail.reset();
        }
        // short circuit for equivalences:
        else if (clause.empty() && tail.empty() && 
                 i + 5 < updates.size() && 
                 updates[i] == ~updates[i + 3] &&
                 updates[i + 1] == ~updates[i + 4] && 
                 updates[i + 2] == sat::null_literal && 
                 updates[i + 5] == sat::null_literal) {
            sat::literal r = ~updates[i+1];
            if (l.sign()) { 
                l.neg(); 
                r.neg(); 
            }
            
            expr* a = lit2expr(l);
            if (is_literal(a))
                m_gmc->add(a, lit2expr(r));
            i += 5;
        }
        else {
            clause.push_back(l);
        }
    }
}
 
model_converter* sat2goal::mc::translate(ast_translation& translator) {
    mc* result = alloc(mc, translator.to());
    result->m_smc.copy(m_smc);
    result->m_gmc = m_gmc ? dynamic_cast<generic_model_converter*>(m_gmc->translate(translator)) : nullptr;
    for (expr* e : m_var2expr) {
        result->m_var2expr.push_back(translator(e));
    }
    return result;
}

void sat2goal::mc::set_env(ast_pp_util* visitor) {
    flush_gmc();
    if (m_gmc) m_gmc->set_env(visitor);
}

void sat2goal::mc::display(std::ostream& out) {
    flush_gmc();
    if (m_gmc) m_gmc->display(out);
}

void sat2goal::mc::get_units(obj_map<expr, bool>& units) {
    flush_gmc();
    if (m_gmc) m_gmc->get_units(units);
}


void sat2goal::mc::operator()(sat::model& md) {
    m_smc(md);
}

void sat2goal::mc::operator()(model_ref & md) {
    // apply externalized model converter
    CTRACE("sat_mc", m_gmc, m_gmc->display(tout << "before sat_mc\n"); model_v2_pp(tout, *md););
    if (m_gmc) (*m_gmc)(md);
    CTRACE("sat_mc", m_gmc, m_gmc->display(tout << "after sat_mc\n"); model_v2_pp(tout, *md););
}


void sat2goal::mc::operator()(expr_ref& fml) {
    flush_gmc();
    if (m_gmc) (*m_gmc)(fml);
}

void sat2goal::mc::insert(sat::bool_var v, expr * atom, bool aux) {
    SASSERT(!m_var2expr.get(v, nullptr));
    m_var2expr.reserve(v + 1);
    m_var2expr.set(v, atom);
    if (aux) {
        SASSERT(m.is_bool(atom));
        if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
        if (is_uninterp_const(atom))
            m_gmc->hide(to_app(atom)->get_decl());
    }
    TRACE("sat_mc", tout << "insert " << v << "\n";);
}

expr_ref sat2goal::mc::lit2expr(sat::literal l) {
    sat::bool_var v = l.var();
    if (!m_var2expr.get(v)) {
        app* aux = m.mk_fresh_const(nullptr, m.mk_bool_sort());
        m_var2expr.set(v, aux);
        if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
        m_gmc->hide(aux->get_decl());
    }
    VERIFY(m_var2expr.get(v));
    expr_ref result(m_var2expr.get(v), m);
    if (l.sign()) {
        result = m.mk_not(result);
    }
    return result;
}


struct sat2goal::imp {

    typedef mc sat_model_converter;

    ast_manager &           m;
    expr_ref_vector         m_lit2expr;
    unsigned long long      m_max_memory;
    bool                    m_learned;
    
    imp(ast_manager & _m, params_ref const & p):m(_m), m_lit2expr(m) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        m_learned        = p.get_bool("learned", false);
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    }

    void checkpoint() {
        if (!m.inc())
            throw tactic_exception(m.limit().get_cancel_msg());
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
    }

    expr * lit2expr(ref<mc>& mc, sat::literal l) {
        if (!m_lit2expr.get(l.index())) {
            SASSERT(m_lit2expr.get((~l).index()) == 0);
            expr* aux = mc ? mc->var2expr(l.var()) : nullptr;
            if (!aux) {
                aux = m.mk_fresh_const(nullptr, m.mk_bool_sort());
                if (mc) {
                    mc->insert(l.var(), aux, true);
                }
            }
            sat::literal lit(l.var(), false);
            m_lit2expr.set(lit.index(), aux);
            m_lit2expr.set((~lit).index(), mk_not(m, aux));
        }        
        return m_lit2expr.get(l.index());
    }

    void assert_clauses(ref<mc>& mc, sat::solver const & s, sat::clause_vector const& clauses, goal & r, bool asserted) {
        ptr_buffer<expr> lits;
        unsigned small_lbd = 3; // s.get_config().m_gc_small_lbd;
        for (sat::clause* cp : clauses) {
            checkpoint();
            lits.reset();
            sat::clause const & c = *cp;
            if (asserted || m_learned || c.glue() <= small_lbd) {
                for (sat::literal l : c) {
                    lits.push_back(lit2expr(mc, l));
                }
                r.assert_expr(m.mk_or(lits));
            }
        }
    }

    void operator()(sat::solver & s, atom2bool_var const & map, goal & r, ref<mc> & mc) {
        if (s.at_base_lvl() && s.inconsistent()) {
            r.assert_expr(m.mk_false());
            return;
        }
        if (r.models_enabled() && !mc) {
            mc = alloc(sat_model_converter, m);
        }
        if (mc) mc->flush_smc(s, map);
        m_lit2expr.resize(s.num_vars() * 2);
        map.mk_inv(m_lit2expr);
        // collect units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            checkpoint();            
            r.assert_expr(lit2expr(mc, s.trail_literal(i)));
        }
        // collect binary clauses
        svector<sat::solver::bin_clause> bin_clauses;
        s.collect_bin_clauses(bin_clauses, m_learned, false);
        for (sat::solver::bin_clause const& bc : bin_clauses) {
            checkpoint();
            r.assert_expr(m.mk_or(lit2expr(mc, bc.first), lit2expr(mc, bc.second)));
        }
        // collect clauses
        assert_clauses(mc, s, s.clauses(), r, true);

        auto* ext = s.get_extension();
        if (ext) {
            std::function<expr_ref(sat::literal)> l2e = [&](sat::literal lit) {
                return expr_ref(lit2expr(mc, lit), m);
            };
            expr_ref_vector fmls(m);
            pb::solver* ba = dynamic_cast<pb::solver*>(ext);
            if (ba) {                
                ba->to_formulas(l2e, fmls);
            }
            else 
                dynamic_cast<euf::solver*>(ext)->to_formulas(l2e, fmls);            
            for (expr* f : fmls)
                r.assert_expr(f);            
        }
    }

    void add_clause(ref<mc>& mc, sat::literal_vector const& lits, expr_ref_vector& lemmas) {
        expr_ref_vector lemma(m);
        for (sat::literal l : lits) {
            expr* e = lit2expr(mc, l);
            if (!e) return;
            lemma.push_back(e);
        }
        lemmas.push_back(mk_or(lemma));
    }

    void add_clause(ref<mc>& mc, sat::clause const& c, expr_ref_vector& lemmas) {
        expr_ref_vector lemma(m);
        for (sat::literal l : c) {
            expr* e = lit2expr(mc, l);
            if (!e) return;
            lemma.push_back(e);
        }
        lemmas.push_back(mk_or(lemma));
    }

};

sat2goal::sat2goal():m_imp(nullptr) {
}

void sat2goal::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("learned", CPK_BOOL, "(default: false) collect also learned clauses.");
}

struct sat2goal::scoped_set_imp {
    sat2goal * m_owner; 
    scoped_set_imp(sat2goal * o, sat2goal::imp * i):m_owner(o) {
        m_owner->m_imp = i;        
    }
    ~scoped_set_imp() {
        m_owner->m_imp = nullptr;
    }
};

void sat2goal::operator()(sat::solver & t, atom2bool_var const & m, params_ref const & p,
                          goal & g, ref<mc> & mc) {
    imp proc(g.m(), p);
    scoped_set_imp set(this, &proc);
    proc(t, m, g, mc);
}
