/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_asserted_literals.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/

#include"spc_asserted_literals.h"
#include"ast_pp.h"

namespace spc {

    asserted_literals::asserted_literals(ast_manager & m):
        m_manager(m),
        m_subst(m),
        m_tmp_eq1(2),
        m_tmp_eq2(2) {
        for (unsigned i = 0; i < 2; i++) {
            m_st[i]           = alloc(substitution_tree, m_manager);
            m_expr2clause[i]  = alloc(expr2clause);
        }
        m_subst.reserve_offsets(3);
    }

    asserted_literals::~asserted_literals() {
        for (unsigned i = 0; i < 2; i++) {
            dealloc(m_st[i]);
            dealloc(m_expr2clause[i]);
        }
    }
        
    void asserted_literals::insert(clause * cls) {
        if (cls->get_num_literals() == 1) {
            TRACE("asserted_literals", tout << "inserting clause into asserted_literals index:\n";
                  cls->display(tout, m_manager); tout << "\n";);
            literal const & l = cls->get_literal(0);
            unsigned neg = static_cast<unsigned>(l.sign());
            expr * atom  = l.atom();
            m_st[neg]->insert(to_app(atom));
            m_expr2clause[neg]->insert(atom, cls);
            m_subst.reserve_vars(m_st[neg]->get_approx_num_regs());
        }
    }

    void asserted_literals::erase(clause * cls) {
        if (cls->get_num_literals() == 1) {
            literal const & l = cls->get_literal(0);
            unsigned neg = static_cast<unsigned>(l.sign());
            expr * atom  = l.atom();
            m_expr2clause[neg]->erase(atom);
            m_st[neg]->erase(to_app(atom));
        }
    }
    
    void asserted_literals::reset() {
        for (unsigned i = 0; i < 2; i++) {
            m_st[i]->reset();
            m_expr2clause[i]->reset();
        }
    }

    struct asserted_literals_visitor : public st_visitor {
        expr * m_target;
        asserted_literals_visitor(substitution & s):st_visitor(s), m_target(0) {}
        virtual bool operator()(expr * e) {
            m_target = e;
            return false; // stop
        }
    };

    /**
       \brief Return an unit clause that is a generalization
       of the given literal.
       Return 0 if such clause does not exist.
    */
    clause * asserted_literals::gen(expr * atom, bool n) {
        if (is_app(atom)) {
            TRACE("asserted_literals", tout << "checking if there is generalizer for: " << n << "\n" << 
                  mk_pp(atom, m_manager) << "\n";);
            unsigned neg = static_cast<unsigned>(n);
            m_subst.reset_subst();
            asserted_literals_visitor visitor(m_subst); 
            TRACE("asserted_literals_bug", tout << "query: " << mk_pp(atom, m_manager) << "\n"; m_st[neg]->display(tout);
                  m_subst.display(tout););
            m_st[neg]->gen(to_app(atom), visitor);
            if (visitor.m_target != 0) {
                clause * cls = 0;
                m_expr2clause[neg]->find(visitor.m_target, cls);
                SASSERT(cls);
                return cls;
            }
            if (m_manager.is_eq(atom)) {
                m_subst.reset();
                m_tmp_eq1.copy_swapping_args(to_app(atom));
                m_st[neg]->gen(m_tmp_eq1.get_app(), visitor);
                if (visitor.m_target != 0) {
                    clause * cls = 0;
                    m_expr2clause[neg]->find(visitor.m_target, cls);
                    SASSERT(cls);
                    return cls;
                }
            }
        }
        return 0;
    }

    /**
       \brief Return an unit clause that is a generalization
       of the equality (= lhs rhs)
       Return 0 if such clause does not exist.
    */
    clause * asserted_literals::gen_eq(expr * lhs, expr * rhs) {
        expr * args[2] = { lhs, rhs };
        func_decl_ref eq_decl(m_manager.mk_func_decl(m_manager.get_basic_family_id(), OP_EQ, 0, 0, 2, args), m_manager);
        m_tmp_eq2.set_decl(eq_decl);
        m_tmp_eq2.set_arg(0, lhs);
        m_tmp_eq2.set_arg(1, rhs);
        return gen(m_tmp_eq2.get_app(), false);
    }

    /**
       \brief Return a unit equality clause (= s t) that (eq) subsumes (= lhs rhs).
       That is, lhs and rhs have the form u[s'] and u[t'] and there is 
       a substitution sigma s.t. sigma(s) = s' and sigma(t) = t'.
       Return 0 if such clause does not exist.
    */
    clause * asserted_literals::subsumes(expr * lhs, expr * rhs) {
        while (true) {
            TRACE("eq_subsumption", tout << "eq_subsumption loop:\n" << mk_pp(lhs, m_manager) << "\n" << 
                  mk_pp(rhs, m_manager) << "\n";);
            clause * subsumer = gen_eq(lhs, rhs);
            if (subsumer)
                return subsumer;
            if (!is_app(lhs) || !is_app(rhs) ||
                to_app(lhs)->get_decl() != to_app(rhs)->get_decl() || 
                to_app(lhs)->get_num_args() != to_app(rhs)->get_num_args())
                return 0;
            expr * d1 = 0;
            expr * d2 = 0;
            unsigned num_args = to_app(lhs)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * c1 = to_app(lhs)->get_arg(i);
                expr * c2 = to_app(rhs)->get_arg(i);
                if (c1 != c2) {
                    if (d1) 
                        return 0;
                    d1 = c1;
                    d2 = c2;
                }
            }
            SASSERT(d1);
            lhs = d1;
            rhs = d2;
        }
        return 0;
    }

};
