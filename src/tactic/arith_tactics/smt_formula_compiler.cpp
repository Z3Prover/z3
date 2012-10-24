/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_formula_compiler.cpp

Abstract:

    Auxiliary class for smt::solver
    Convert Exprs into Internal data-structures.    
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:
    This was an experiment to rewrite Z3 kernel.
    It will be deleted after we finish revamping Z3 kernel.

--*/
#include"smt_formula_compiler.h"
#include"smt_solver_exp.h"
#include"assertion_set_util.h"
#include"assertion_set2sat.h"
#include"for_each_expr.h"

namespace smt {

    formula_compiler::formula_compiler(solver_exp & _s, params_ref const & p):
        s(_s),
        m_a_util(s.m),
        m_normalizer(s.m),
        m_elim_ite(s.m) {
        updt_params(p);
     
        params_ref s_p;
        s_p.set_bool(":elim-and", true);
        s_p.set_bool(":blast-distinct", true);
        s_p.set_bool(":eq2ineq", true);
        s_p.set_bool(":arith-lhs", true);
        s_p.set_bool(":gcd-rounding", true);
        s_p.set_bool(":sort-sums", true);
        s_p.set_bool(":som", true);
        m_normalizer.updt_params(s_p);
    }

    formula_compiler::~formula_compiler() {
    
    }

    // mark theory axioms: literals that do not occur in the boolean structure
    void formula_compiler::mark_axioms(assertion_set const & s, expr_fast_mark2 & axioms) {
        ast_manager & m = s.m();
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = s.form(i);
            while (m.is_not(f, f));
            if (!is_app(f) || to_app(f)->get_family_id() != m.get_basic_family_id()) {
                axioms.mark(f);
                continue;
            }
            SASSERT(is_app(f));
            SASSERT(to_app(f)->get_family_id() == m.get_basic_family_id());
            switch (to_app(f)->get_decl_kind()) {
            case OP_OR:
            case OP_IFF:
                break;
            case OP_ITE:
                SASSERT(m.is_bool(to_app(f)->get_arg(1)));
                break;
            case OP_EQ:
                if (!m.is_bool(to_app(f)->get_arg(1)))
                    axioms.mark(f);
                break;
            case OP_AND:
            case OP_XOR:
            case OP_IMPLIES:
            case OP_DISTINCT:
                UNREACHABLE();
                break;
            default:
                break;
            }
        }
    }

    struct unmark_axioms_proc {
        expr_fast_mark2 & m_axioms;
        unmark_axioms_proc(expr_fast_mark2 & axioms):m_axioms(axioms) {}
        void operator()(quantifier *) {}
        void operator()(var *) {}
        void operator()(app * t) { 
            m_axioms.reset_mark(t); 
        }
    };

    /**
       \brief Unmark atoms that occur in the boolean structure.
    */
    void formula_compiler::unmark_nested_atoms(assertion_set const & s, expr_fast_mark2 & axioms) {
        ast_manager & m = s.m();
        expr_fast_mark1 visited;
        unmark_axioms_proc proc(axioms);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = s.form(i);
            while (m.is_not(f, f));
            if (axioms.is_marked(f))
                continue;
            quick_for_each_expr(proc, visited, f);
        }
    }

    void formula_compiler::assert_axiom(expr * f, bool neg) {
        if (is_app(f)) {
            if (to_app(f)->get_family_id() == m_a_util.get_family_id())
                s.m_arith.assert_axiom(f, neg);
        }
    }

    void formula_compiler::register_atom(expr * f, sat::bool_var p) {
        if (is_app(f)) {
            if (to_app(f)->get_family_id() == m_a_util.get_family_id())
                s.m_arith.mk_atom(f, p);
        }
    }

    void formula_compiler::compile_formulas(assertion_set const & assertions) {
        ast_manager & m = assertions.m();
        expr_fast_mark2 axioms;
        mark_axioms(assertions, axioms);
        unmark_nested_atoms(assertions, axioms);
        ptr_vector<expr> formulas;

        // send axioms to theories, and save formulas to compile
        unsigned sz = assertions.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = assertions.form(i);
            bool neg = false;
            while (m.is_not(f, f))
                neg = !neg;
            if (axioms.is_marked(f)) {
                assert_axiom(f, neg);
            }
            else {
                formulas.push_back(f);
            }
        }
        
        // compile formulas into sat::solver
        m_to_sat(m, formulas.size(), formulas.c_ptr(), s.m_params, *(s.m_sat), s.m_atom2bvar);

        // register atoms nested in the boolean structure in the theories  
        atom2bool_var::recent_iterator it  = s.m_atom2bvar.begin_recent();
        atom2bool_var::recent_iterator end = s.m_atom2bvar.end_recent();
        for (; it != end; ++it) {
            expr * atom = *it;
            register_atom(atom, s.m_atom2bvar.to_bool_var(atom));
        }
        s.m_atom2bvar.reset_recent();
    }

    void formula_compiler::normalize() {
        // make sure that the assertions are in the right format.
        m_normalizer(s.m_assertions);
        m_normalizer.cleanup();
    }
    
    void formula_compiler::elim_term_ite() {
        if (has_term_ite(s.m_assertions)) {
            model_converter_ref mc;
            m_elim_ite(s.m_assertions, mc);
            s.m_mc = concat(s.m_mc.get(), mc.get());
            m_elim_ite.cleanup();
        }
    }

    void formula_compiler::operator()() {
        if (s.m_assertions.inconsistent())
            return;
        // normalization
        elim_term_ite();
        normalize();

        TRACE("before_formula_compiler", s.m_assertions.display(tout););
        
        s.init();

        compile_formulas(s.m_assertions);
        
        s.m_arith.preprocess();
        TRACE("after_formula_compiler", s.display_state(tout););
    }
    
    void formula_compiler::updt_params(params_ref const & p) {
        // TODO
    }
    
    void formula_compiler::collect_param_descrs(param_descrs & d) {
        // TODO
    }

    void formula_compiler::collect_statistics(statistics & st) {
        // TODO
    }
    
    void formula_compiler::reset_statistics() {
        // TODO
    }

    void formula_compiler::set_cancel(bool f) {
        m_normalizer.set_cancel(f);
        m_elim_ite.set_cancel(f);
        m_to_sat.set_cancel(f);
    }

};
