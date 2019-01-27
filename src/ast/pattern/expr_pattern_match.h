/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_pattern_match.h

Abstract:

    Search for opportune pattern matching utilities.

Author:

    Nikolaj Bjorner (nbjorner) 2007-04-10
    Leonardo (leonardo)

Notes:

--*/
#ifndef EXPR_PATTERN_MATCH_H_
#define EXPR_PATTERN_MATCH_H_

#include "ast/ast.h"
#include "util/map.h"

class expr_pattern_match {

    enum instr_kind {
        BACKTRACK,
        BIND,
        BIND_AC,
        BIND_C,
        CHOOSE_AC,
        CHOOSE_C,
        SET_VAR,
        CHECK_VAR,
        CHECK_TERM,
        SET_BOUND,
        CHECK_BOUND,        
        YIELD
    };

    struct instr {
        instr(instr_kind k) : m_kind(k) {}
        instr(instr_kind k, unsigned o, unsigned next, app* app, unsigned count):
            m_kind(k), m_offset(o), m_next(next), m_app(app), m_count(count) {}

        instr_kind      m_kind;
        unsigned        m_offset;
        unsigned        m_next;
        app*            m_app;
        expr*           m_pat;
        unsigned        m_reg;
        unsigned        m_other_reg;
        unsigned        m_count;
        unsigned        m_num_bound;
    };

    typedef obj_map<func_decl, unsigned> subst;
    typedef obj_map<var, var*> bound;

    struct inst_proc {
        ast_manager&    m_manager;
        expr_ref_vector m_pinned;
        subst&          m_subst;
        bound&          m_bound;
        obj_map<expr, expr*> m_memoize;
        ptr_vector<expr>& m_regs;
        
        
        inst_proc(ast_manager& m, subst& s, bound& b, ptr_vector<expr>& regs) : 
            m_manager(m), m_pinned(m), m_subst(s), m_bound(b), m_regs(regs) {}
                

        void operator()(ast* a) {
        }

        void operator()(expr* a) {
            m_memoize.insert(a, a);
        }

        void operator()(var* v) {
            var* b = nullptr;
            if (m_bound.find(v, b)) {
                m_memoize.insert(v, b);
            }
            else {
                UNREACHABLE();
            }
        }
                
        void operator()(app * n) {  
            unsigned r;
            ptr_vector<expr> args;
            unsigned num_args     = n->get_num_args();
            func_decl * decl = n->get_decl();
            expr* result;
            if (m_subst.find(decl, r)) {
                decl = to_app(m_regs[r])->get_decl();
            }
            for (unsigned i = 0; i < num_args; ++i) {
                expr* arg = nullptr;
                if (m_memoize.find(n->get_arg(i), arg)) {
                    SASSERT(arg);
                    args.push_back(arg);
                }
                else {
                    UNREACHABLE();
                }
            }
            if (m_manager.is_pattern(n)) {
                result = m_manager.mk_pattern(num_args, reinterpret_cast<app**>(args.c_ptr()));
            }
            else {
                result = m_manager.mk_app(decl, num_args, args.c_ptr());
            }
            m_pinned.push_back(result);
            m_memoize.insert(n, result);
            return;
        }
    };

    ast_manager &                 m_manager;
    quantifier_ref_vector         m_precompiled;
    unsigned_vector               m_first_instrs;
    svector<instr>                m_instrs;
    ptr_vector<expr>              m_regs;
    ptr_vector<var>               m_bound_dom;
    ptr_vector<var>               m_bound_rng;

 public:
    expr_pattern_match(ast_manager & manager);
    ~expr_pattern_match();
    virtual bool match_quantifier(quantifier * qf, app_ref_vector & patterns, unsigned & weight);
    virtual void initialize(char const * database);
    void display(std::ostream& out) const;

 private:
    void instantiate(expr* a, unsigned num_bound, subst& s, expr_ref& result);
    void compile(expr* q);
    bool match(expr* a, unsigned init, subst& s);
    bool match_decl(func_decl const * pat, func_decl const * d) const;
    bool is_var(func_decl* d);
    void display(std::ostream& out, instr const& pc) const;
};

#endif 
