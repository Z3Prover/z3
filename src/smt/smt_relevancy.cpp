/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_relevancy.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-04.

Revision History:

--*/
#include"smt_context.h"
#include"smt_relevancy.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"

namespace smt {

    void relevancy_eh::mark_as_relevant(relevancy_propagator & rp, expr * n) {
        rp.mark_as_relevant(n);
    }

    void relevancy_eh::mark_args_as_relevant(relevancy_propagator & rp, app * n) {
        unsigned j = n->get_num_args();
        while (j > 0) {
            --j;
            rp.mark_as_relevant(n->get_arg(j));
        }
    }

    void simple_relevancy_eh::operator()(relevancy_propagator & rp) {
        rp.mark_as_relevant(m_target);
    }

    void pair_relevancy_eh::operator()(relevancy_propagator & rp) {
        if (!rp.is_relevant(m_source1))
            return;
        if (!rp.is_relevant(m_source2))
            return;
        rp.mark_as_relevant(m_target);
    }

    class and_relevancy_eh : public relevancy_eh {
        app * m_parent;
    public:
        and_relevancy_eh(app * p):m_parent(p) {}
        virtual ~and_relevancy_eh() {}
        virtual void operator()(relevancy_propagator & rp);
    };

    class or_relevancy_eh : public relevancy_eh {
        app * m_parent;
    public:
        or_relevancy_eh(app * p):m_parent(p) {}
        virtual ~or_relevancy_eh() {}
        virtual void operator()(relevancy_propagator & rp);
    };

    class ite_relevancy_eh : public relevancy_eh {
        app * m_parent;
    public:
        ite_relevancy_eh(app * p):m_parent(p) {}
        virtual ~ite_relevancy_eh() {}
        virtual void operator()(relevancy_propagator & rp);
    };

    class ite_term_relevancy_eh : public relevancy_eh {
        app  * m_parent;
        app  * m_then_eq;
        app  * m_else_eq;
    public:
        ite_term_relevancy_eh(app * p, app * then_eq, app * else_eq):m_parent(p), m_then_eq(then_eq), m_else_eq(else_eq) {}
        virtual ~ite_term_relevancy_eh() {}
        virtual void operator()(relevancy_propagator & rp);
    };

    relevancy_propagator::relevancy_propagator(context & ctx):
        m_context(ctx) {
    }

    bool relevancy_propagator::enabled() const {
        return m_context.relevancy();
    }

    region & relevancy_propagator::get_region() const {
        return m_context.get_region();
    }

    ast_manager & relevancy_propagator::get_manager() const {
        return m_context.get_manager();
    }

    void relevancy_propagator::add_dependency(expr * src, expr * target) {
        if (!enabled())
            return;
        if (is_relevant(src))
            mark_as_relevant(target);
        else
            add_handler(src, mk_relevancy_eh(simple_relevancy_eh(target)));
    }

    relevancy_eh * relevancy_propagator::mk_or_relevancy_eh(app * n) {
        SASSERT(get_manager().is_or(n));
        return mk_relevancy_eh(or_relevancy_eh(n));
    }

    relevancy_eh * relevancy_propagator::mk_and_relevancy_eh(app * n) {
        SASSERT(get_manager().is_and(n));
        return mk_relevancy_eh(and_relevancy_eh(n));
    }
    
    relevancy_eh * relevancy_propagator::mk_ite_relevancy_eh(app * n) {
        SASSERT(get_manager().is_ite(n));
        return mk_relevancy_eh(ite_relevancy_eh(n));
    }

    relevancy_eh * relevancy_propagator::mk_term_ite_relevancy_eh(app * c, app * t, app * e) {
        return mk_relevancy_eh(ite_term_relevancy_eh(c, t, e));
    }
    
    struct relevancy_propagator_imp : public relevancy_propagator {
        unsigned                       m_qhead;
        expr_ref_vector                m_relevant_exprs; 
        obj_hashtable<expr>            m_is_relevant;
        typedef list<relevancy_eh *>   relevancy_ehs;
        obj_map<expr, relevancy_ehs *> m_relevant_ehs;
        obj_map<expr, relevancy_ehs *> m_watches[2];
        struct eh_trail {
            enum kind { POS_WATCH, NEG_WATCH, HANDLER };
            kind   m_kind;
            expr * m_node;
            eh_trail(expr * n):m_kind(HANDLER), m_node(n) {}
            eh_trail(expr * n, bool val):m_kind(val ? POS_WATCH : NEG_WATCH), m_node(n) {}
            kind get_kind() const { return m_kind; }
            expr * get_node() const { return m_node; }
        };
        svector<eh_trail>              m_trail;
        struct scope {
            unsigned m_relevant_exprs_lim;
            unsigned m_trail_lim;
        };
        svector<scope>                 m_scopes;

        relevancy_propagator_imp(context & ctx):relevancy_propagator(ctx), m_qhead(0), m_relevant_exprs(ctx.get_manager()) {}

        virtual ~relevancy_propagator_imp() {
            undo_trail(0);
        }

        relevancy_ehs * get_handlers(expr * n) {
            relevancy_ehs * r = 0;
            m_relevant_ehs.find(n, r);
            SASSERT(m_relevant_ehs.contains(n) || r == 0);
            return r;
        }

        void set_handlers(expr * n, relevancy_ehs * ehs) {
            if (ehs == 0)
                m_relevant_ehs.erase(n);
            else
                m_relevant_ehs.insert(n, ehs);
        }

        relevancy_ehs * get_watches(expr * n, bool val) {
            relevancy_ehs * r = 0;
            m_watches[val ? 1 : 0].find(n, r);
            SASSERT(m_watches[val ? 1 : 0].contains(n) || r == 0);
            return r;
        }

        void set_watches(expr * n, bool val, relevancy_ehs * ehs) {
            if (ehs == 0)
                m_watches[val ? 1 : 0].erase(n);
            else
                m_watches[val ? 1 : 0].insert(n, ehs);
        }

        void push_trail(eh_trail const & t) {
            get_manager().inc_ref(t.get_node());
            m_trail.push_back(t);
        }
        
        virtual void add_handler(expr * source, relevancy_eh * eh) {
            if (!enabled())
                return;
            if (is_relevant_core(source)) {
                eh->operator()(*this, source);
            }
            else {
                SASSERT(eh);
                push_trail(eh_trail(source));
                set_handlers(source, new (get_region()) relevancy_ehs(eh, get_handlers(source)));
            }
        }
        
        virtual void add_watch(expr * n, bool val, relevancy_eh * eh) {
            if (!enabled())
                return;
            lbool lval = m_context.find_assignment(n);
            if (!val)
                lval = ~lval;
            switch (lval) {
            case l_false:
                return;
            case l_undef:
                SASSERT(eh);
                push_trail(eh_trail(n, val));
                set_watches(n, val, new (get_region()) relevancy_ehs(eh, get_watches(n, val)));
                break;
            case l_true:
                eh->operator()(*this, n, val);
                break;
            }
        }

        virtual void add_watch(expr * n, bool val, expr * target) {
            if (!enabled())
                return;
            lbool lval = m_context.find_assignment(n);
            if (!val)
                lval = ~lval;
            switch (lval) {
            case l_false:
                return;
            case l_undef:
                add_watch(n, val, mk_relevancy_eh(simple_relevancy_eh(target)));
                break;
            case l_true:
                mark_as_relevant(target); propagate();
                break;
            }
        }
        
        bool is_relevant_core(expr * n) const { return m_is_relevant.contains(n); }
        
        virtual bool is_relevant(expr * n) const {
            return !enabled() || is_relevant_core(n);
        }

        virtual void push() {
            m_scopes.push_back(scope());
            scope & s                  = m_scopes.back();
            s.m_relevant_exprs_lim     = m_relevant_exprs.size();
            s.m_trail_lim              = m_trail.size();
        }

        virtual void pop(unsigned num_scopes) {
            SASSERT(m_context.get_scope_level() == m_scopes.size());
            unsigned lvl     = m_scopes.size();
            SASSERT(num_scopes <= lvl);
            unsigned new_lvl = lvl - num_scopes;
            scope & s        = m_scopes[new_lvl];
            unmark_relevant_exprs(s.m_relevant_exprs_lim);
            undo_trail(s.m_trail_lim);
            m_scopes.shrink(new_lvl);
        }

        /**
           \brief Unmark expressions marked as relevant.
        */
        void unmark_relevant_exprs(unsigned old_lim) {
            SASSERT(old_lim <= m_relevant_exprs.size());
            unsigned i = m_relevant_exprs.size();
            while (i != old_lim) {
                --i;
                expr * n = m_relevant_exprs.get(i);
                m_is_relevant.erase(n);
                TRACE("propagate_relevancy", tout << "unmarking:\n" << mk_ismt2_pp(n, get_manager()) << "\n";);
            }
            m_relevant_exprs.shrink(old_lim);
            m_qhead = m_relevant_exprs.size();
        }

        void undo_trail(unsigned old_lim) {
            SASSERT(old_lim <= m_trail.size());
            ast_manager & m = get_manager();
            unsigned i = m_trail.size();
            while (i != old_lim) {
                --i;
                eh_trail & t = m_trail[i];
                expr * n = t.get_node();
                relevancy_ehs * ehs;
                switch (t.get_kind()) {
                case eh_trail::POS_WATCH: ehs = get_watches(n, true); SASSERT(ehs); set_watches(n, true, ehs->tail()); break;
                case eh_trail::NEG_WATCH: ehs = get_watches(n, false); SASSERT(ehs); set_watches(n, false, ehs->tail()); break;
                case eh_trail::HANDLER:   ehs = get_handlers(n); SASSERT(ehs); set_handlers(n, ehs->tail()); break;
                default: UNREACHABLE(); break;
                }
                m.dec_ref(n);
            }
            m_trail.shrink(old_lim);
        }

        void set_relevant(expr * n) {
            m_is_relevant.insert(n);
            m_relevant_exprs.push_back(n);
            m_context.relevant_eh(n);
        }

        /**
           \brief Mark an expression as relevant and propagate
           the relevancy to its descendants.
        */
        void mark_and_propagate(expr * n) {
            if (!enabled())
                return;
            if (!is_relevant_core(n)) {
                mark_as_relevant(n);
                propagate();
            }
        }

        /**
           \brief Mark the given expression as relevant if it is not
           already marked. 
        */
        virtual void mark_as_relevant(expr * n) {
            if (!enabled())
                return;
            if (!is_relevant_core(n)) {
                enode * e    = m_context.find_enode(n);
                if (e != 0) {
                    enode * curr = e;
                    do {
                        set_relevant(curr->get_owner());
                        curr = curr->get_next();
                    }
                    while (curr != e);
                }
                else {
                    set_relevant(n);
                }
            }
        }
        
        /**
           \brief Marks the children of n as relevant.
           
           \pre n is marked as relevant.
        */
        void propagate_relevant_app(app * n) {
            SASSERT(is_relevant_core(n));
            unsigned j = n->get_num_args();
            while (j > 0) {
                --j;
                mark_as_relevant(n->get_arg(j));
            }
        }
        
        /**
           \brief Propagate relevancy for an or-application.
        */
        void propagate_relevant_or(app * n) {
            SASSERT(get_manager().is_or(n));
            
            lbool val    = m_context.find_assignment(n);
            // If val is l_undef, then the expression
            // is a root, and no boolean variable was created for it.
            if (val == l_undef)
                val = l_true;
            switch (val) {
            case l_false:
                propagate_relevant_app(n);
                break;
            case l_undef:
                break;
            case l_true: {
                expr * true_arg = 0;
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg  = n->get_arg(i);
                    if (m_context.find_assignment(arg) == l_true) {
                        if (is_relevant_core(arg))
                            return;
                        else if (!true_arg)
                            true_arg = arg;
                    }
                }
                if (true_arg)
                    mark_as_relevant(true_arg);
                break;
            } }
        }
        
        /**
           \brief Propagate relevancy for an and-application.
        */
        void propagate_relevant_and(app * n) {
            lbool val    = m_context.find_assignment(n);
            switch (val) {
            case l_false: {
                expr * false_arg = 0;
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg  = n->get_arg(i);
                    if (m_context.find_assignment(arg) == l_false) {
                        if (is_relevant_core(arg))
                            return; 
                        else if (!false_arg)
                            false_arg = arg;
                    }
                }
                if (false_arg)
                    mark_as_relevant(false_arg);
                break;
            }
            case l_undef:
                break;
            case l_true:
                propagate_relevant_app(n);
                break;
            }
        }

        /**
           \brief Propagate relevancy for an ite-expression.
        */
        void propagate_relevant_ite(app * n) {
            TRACE("propagate_relevant_ite", tout << "propagating relevancy for #" << n->get_id() << "\n" << mk_pp(n, get_manager()) << "\n";);
            mark_as_relevant(n->get_arg(0));
            switch (m_context.find_assignment(n->get_arg(0))) {
            case l_false:
                TRACE("propagate_relevant_ite", tout << "marking as relevant: " << mk_pp(n->get_arg(2), get_manager()) << "\n";);
                mark_as_relevant(n->get_arg(2));
                break;
            case l_undef:
                TRACE("propagate_relevant_ite", tout << "ite c is unassigned\n";);
                break;
            case l_true:
                TRACE("propagate_relevant_ite", tout << "marking as relevant: " << mk_pp(n->get_arg(1), get_manager()) << "\n";);
                mark_as_relevant(n->get_arg(1));
                break;
            }
        }
        
        /**
           \brief Propagate relevancy to the arguments of recently marked
           expressions. That is, expressions that are located at positions
           [m_qhead, m_relevant_exprs.size()) in the stack of 
           relevant expressions.
        */
        virtual void propagate() {
            ast_manager & m = get_manager();
            while (m_qhead < m_relevant_exprs.size()) {
                expr * n = m_relevant_exprs.get(m_qhead);
                TRACE("propagate_relevancy_to_args", tout << "propagating relevancy to args of #" << n->get_id() << "\n";);
                TRACE("propagate_relevancy", tout << "marking as relevant:\n" << mk_bounded_pp(n, m) << "\n";);
                SASSERT(is_relevant_core(n));
                m_qhead++;
                if (is_app(n)) {
                    family_id fid = to_app(n)->get_family_id();
                    if (fid == m.get_basic_family_id()) {
                        switch (to_app(n)->get_decl_kind()) {
                        case OP_OR:
                            propagate_relevant_or(to_app(n));
                            break;
                        case OP_AND:
                            propagate_relevant_and(to_app(n));
                            break;
                        case OP_ITE:
                            propagate_relevant_ite(to_app(n));
                            break;
                        default:
                            propagate_relevant_app(to_app(n));
                            break;
                        }
                    }
                    else {
                        propagate_relevant_app(to_app(n));
                    }
                }
                
                relevancy_ehs * ehs = get_handlers(n);
                while (ehs != 0) {
                    ehs->head()->operator()(*this, n);
                    ehs = ehs->tail();
                }
            }
        }

        virtual bool can_propagate() const {
            return m_qhead < m_relevant_exprs.size();
        }

        virtual void assign_eh(expr * n, bool val) {
            if (!enabled())
                return;
            ast_manager & m = get_manager();
            SASSERT(enabled());
            if (is_relevant_core(n)) {
                if (m.is_or(n))
                    propagate_relevant_or(to_app(n));
                else if (m.is_and(n))
                    propagate_relevant_and(to_app(n));
            }
            relevancy_ehs * ehs = get_watches(n, val);
            while (ehs != 0) {
                ehs->head()->operator()(*this, n, val);
                ehs = ehs->tail();
            }
        }

        virtual void display(std::ostream & out) const {
            if (enabled() && !m_relevant_exprs.empty()) {
                out << "relevant exprs:\n";
                for (unsigned i = 0; i < m_relevant_exprs.size(); i++) {
                    out << "#" << m_relevant_exprs.get(i)->get_id() << " ";
                }
                out << "\n";
            }
        }

#ifdef Z3DEBUG
        bool check_relevancy_app(app * n) const {
            SASSERT(is_relevant(n));
            unsigned num_args = n->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                CTRACE("relevancy_bug", !is_relevant(n->get_arg(i)), tout << "n: " << mk_ismt2_pp(n, get_manager()) << "\ni: " << i << "\n";);
                SASSERT(is_relevant(n->get_arg(i)));
            }
            return true;
        }
        
        virtual bool check_relevancy_or(app * n, bool root) const {
            lbool val    = root ? l_true : m_context.find_assignment(n);
            if (val == l_false)
                return check_relevancy_app(n);
            if (val == l_true) {
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = n->get_arg(i);
                    if (m_context.find_assignment(arg) == l_true && is_relevant(arg))
                        return true;
                }
                TRACE("check_relevancy", tout << "failed:\n" << mk_ll_pp(n, get_manager()); display(tout););
                UNREACHABLE();
            }
            return true;
        }
        
        bool check_relevancy_and(app * n) const {
            lbool val = m_context.find_assignment(n);
            if (val == l_true)
                return check_relevancy_app(n);
            if (val == l_false) {
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = n->get_arg(i);
                    if (m_context.find_assignment(arg) == l_false && is_relevant(arg))
                        return true;
                }
                UNREACHABLE();
            }
            return true;
        }
        
        bool check_relevancy_ite(app * n) const {
            SASSERT(is_relevant(n->get_arg(0)));
            switch (m_context.find_assignment(n->get_arg(0))) {
            case l_false:
                if (get_manager().is_bool(n)) {
                    TRACE("ite_bug", tout << mk_bounded_pp(n, get_manager()) << "\n";);
                    SASSERT(is_relevant(n->get_arg(2)));
                }
                else {
                    app_ref eq(get_manager());
                    eq = m_context.mk_eq_atom(n, n->get_arg(2));
                    SASSERT(is_relevant(eq.get()));
                }
                break;
            case l_undef:
                break;
            case l_true:
                if (get_manager().is_bool(n)) {
                    SASSERT(is_relevant(n->get_arg(1)));
                }
                else {
                    app_ref eq(get_manager());
                    eq = m_context.mk_eq_atom(n, n->get_arg(1));
                    SASSERT(is_relevant(eq.get()));
                }
                break;
            }
            return true;
        }
        
        bool check_relevancy(expr_ref_vector const & v) const {
            SASSERT(!can_propagate());
            ast_manager & m = get_manager();
            unsigned sz = v.size();
            for (unsigned i = 0; i < sz; i++) {
                expr * n    = v.get(i);
                if (is_relevant(n)) {
                    TRACE("check_relevancy", tout << "checking:\n" << mk_ll_pp(n, get_manager()) << "internalized: " << m_context.find_enode(n) << "\n";);
                    if (m.is_or(n)) {
                        SASSERT(check_relevancy_or(to_app(n), false));
                    }
                    else if (m.is_and(n)) {
                        SASSERT(check_relevancy_and(to_app(n)));
                    }
                    else if (m.is_ite(n)) {
                        SASSERT(check_relevancy_ite(to_app(n)));
                    }
                    else if (is_app(n)) {
                        SASSERT(check_relevancy_app(to_app(n)));
                    }
                    else {
                        enode * n0 = m_context.find_enode(n);
                        if (n0 != 0) {
                            enode * n = n0->get_next();
                            while (n0 != n) {
                                SASSERT(is_relevant(n->get_owner()));
                                n = n->get_next();
                            }
                        }
                    }
                }
            }
            return true;
        }
#endif
    };

    void and_relevancy_eh::operator()(relevancy_propagator & rp) {
        if (rp.is_relevant(m_parent))
            static_cast<relevancy_propagator_imp&>(rp).propagate_relevant_and(m_parent);
    }

    void or_relevancy_eh::operator()(relevancy_propagator & rp) {
        if (rp.is_relevant(m_parent))
            static_cast<relevancy_propagator_imp&>(rp).propagate_relevant_or(m_parent);
    }

    void ite_relevancy_eh::operator()(relevancy_propagator & rp) {
        if (rp.is_relevant(m_parent)) {
            static_cast<relevancy_propagator_imp&>(rp).propagate_relevant_ite(m_parent);
        }
    }

    void ite_term_relevancy_eh::operator()(relevancy_propagator & rp) {
        if (!rp.is_relevant(m_parent))
            return;
        rp.mark_as_relevant(m_parent->get_arg(0));
        switch (rp.get_context().get_assignment(m_parent->get_arg(0))) {
        case l_false:
            TRACE("ite_term_relevancy", tout << "marking else: #" << m_else_eq->get_id() << "\n";);
            rp.mark_as_relevant(m_else_eq);
            break;
        case l_undef:
            break;
        case l_true:
            TRACE("ite_term_relevancy", tout << "marking then: #" << m_then_eq->get_id() << "\n";);
            rp.mark_as_relevant(m_then_eq);
            break;
        }
    }

    relevancy_propagator * mk_relevancy_propagator(context & ctx) { return alloc(relevancy_propagator_imp, ctx); }
};


