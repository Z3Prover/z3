/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dyn_ack.cpp

Abstract:

    Dynamic Ackermann's reduction

Author:

    Leonardo de Moura (leonardo) 2007-04-24.

Revision History:

--*/
#include"smt_context.h"
#include"dyn_ack.h"
#include"ast_pp.h"

namespace smt {

    /**
       \brief Justification for dynamic ackermann clause
    */
    class dyn_ack_justification : public justification {
        app *     m_app1;
        app *     m_app2;
    public:
        dyn_ack_justification(app * n1, app * n2):
            justification(false), // dyn_ack_justifications are not stored in regions.
            m_app1(n1), 
            m_app2(n2) {
            SASSERT(m_app1->get_num_args() == m_app2->get_num_args());
            SASSERT(m_app1->get_decl() == m_app2->get_decl());
            SASSERT(m_app1->get_num_args() > 0);
            SASSERT(m_app1->get_id() < m_app2->get_id());
        }

        virtual char const * get_name() const { return "dyn-ack"; }

        virtual void get_antecedents(conflict_resolution & cr) {
        }

        virtual void display_debug_info(conflict_resolution & cr, std::ostream & out) { 
            ast_manager & m = cr.get_manager();
            out << "m_app1:\n" << mk_pp(m_app1, m) << "\n";
            out << "m_app2:\n" << mk_pp(m_app2, m) << "\n";
        }

        /**
           \brief Make a hypothesis (= lhs rhs) for the given equality.
           The arguments of the given equality eq may have been swapped. That is, \c eq is of the form (= rhs lhs).
           In this case, we also apply a symmetry rule.

           \remark if negate == true, then the hypothesis is actually (not (= lhs rhs))
        */
        proof * mk_hypothesis(ast_manager & m, app * eq, bool negate, expr * lhs, expr * rhs) {
            SASSERT(m.is_eq(eq) || m.is_iff(eq));
            SASSERT((eq->get_arg(0) == lhs && eq->get_arg(1) == rhs) ||
                    (eq->get_arg(0) == rhs && eq->get_arg(1) == lhs));
            app * h = negate ? m.mk_not(eq) : eq;
            if (eq->get_arg(0) == lhs && eq->get_arg(1) == rhs) {
                return m.mk_hypothesis(h);
            }
            else {
                return m.mk_symmetry(m.mk_hypothesis(h));
            }
        }

        virtual proof * mk_proof(conflict_resolution & cr) {
            ast_manager & m   = cr.get_manager();
            context & ctx     = cr.get_context();
            unsigned num_args = m_app1->get_num_args();
            ptr_buffer<proof> prs;
            ptr_buffer<expr>  lits;
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg1   = m_app1->get_arg(i);
                expr * arg2   = m_app2->get_arg(i);
                if (arg1 != arg2) {
                    app * eq  = ctx.mk_eq_atom(arg1, arg2);
                    app * neq = m.mk_not(eq);
                    if (std::find(lits.begin(), lits.end(), neq) == lits.end()) {
                        lits.push_back(neq);
                        prs.push_back(mk_hypothesis(m, eq, false, arg1, arg2));
                    }
                }
            }
            proof * antecedents[2];
            antecedents[0]   = m.mk_congruence(m_app1, m_app2, prs.size(), prs.c_ptr());
            app * eq         = ctx.mk_eq_atom(m_app1, m_app2);
            antecedents[1]   = mk_hypothesis(m, eq, true, m_app1, m_app2);
            proof * false_pr = m.mk_unit_resolution(2, antecedents);
            lits.push_back(eq);
            SASSERT(lits.size() >= 2);
            app * lemma      = m.mk_or(lits.size(), lits.c_ptr());
            TRACE("dyn_ack", tout << mk_pp(lemma, m) << "\n";);
            TRACE("dyn_ack", tout << mk_pp(false_pr, m) << "\n";);
            return m.mk_lemma(false_pr, lemma);
        }

    };

    dyn_ack_manager::dyn_ack_manager(context & ctx, dyn_ack_params & p):
        m_context(ctx),
        m_manager(ctx.get_manager()),
        m_params(p) {
    }

    dyn_ack_manager::~dyn_ack_manager() {
        reset_app_pairs();
        reset_app_triples();
    }

    void dyn_ack_manager::reset_app_pairs() {
        svector<app_pair>::iterator it  = m_app_pairs.begin();
        svector<app_pair>::iterator end = m_app_pairs.end();
        for (; it != end; ++it) {
            app_pair & p = *it;
            m_manager.dec_ref(p.first);
            m_manager.dec_ref(p.second);
        }
        m_app_pairs.reset();
    }


    void dyn_ack_manager::init_search_eh() {
        m_app_pair2num_occs.reset();
        reset_app_pairs();
        m_to_instantiate.reset();
        m_qhead = 0;
        m_num_instances = 0;
        m_num_propagations_since_last_gc = 0;

        m_triple.m_app2num_occs.reset();
        reset_app_triples();
        m_triple.m_to_instantiate.reset();
        m_triple.m_qhead = 0;
    }

    void dyn_ack_manager::cg_eh(app * n1, app * n2) {
        SASSERT(n1->get_decl() == n2->get_decl());
        SASSERT(n1->get_num_args() == n2->get_num_args());
        SASSERT(n1 != n2);
        if (m_manager.is_eq(n1))
            return;
        if (n1->get_id() > n2->get_id())
            std::swap(n1,n2);
        app_pair p(n1, n2);
        if (m_instantiated.contains(p))
            return;
        unsigned num_occs = 0;
        if (m_app_pair2num_occs.find(n1, n2, num_occs)) {
            TRACE("dyn_ack", tout << "used_cg_eh:\n" << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) << "\nnum_occs: " << num_occs << "\n";);
            num_occs++;
        }
        else {
            num_occs = 1;
            m_manager.inc_ref(n1);
            m_manager.inc_ref(n2);
            m_app_pairs.push_back(p);
        }
        SASSERT(num_occs > 0);
        m_app_pair2num_occs.insert(n1, n2, num_occs);
#ifdef Z3DEBUG
        unsigned num_occs2 = 0;
        SASSERT(m_app_pair2num_occs.find(n1, n2, num_occs2) && num_occs == num_occs2);
#endif
        if (num_occs == m_params.m_dack_threshold) {
            TRACE("dyn_ack", tout << "found candidate:\n" << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) << "\nnum_occs: " << num_occs << "\n";);
            m_to_instantiate.push_back(p);
        }
    }

    void dyn_ack_manager::eq_eh(app * n1, app * n2, app* r) {
        if (n1 == n2 || r == n1 || r == n2 || m_manager.is_bool(n1)) {
            return;
        }
        if (n1->get_id() > n2->get_id())
            std::swap(n1,n2);
        TRACE("dyn_ack", 
              tout << mk_pp(n1, m_manager) << " = " << mk_pp(n2, m_manager) 
              << " = " << mk_pp(r, m_manager) << "\n";);
        app_triple tr(n1, n2, r);
        if (m_triple.m_instantiated.contains(tr))
            return;
        unsigned num_occs = 0;
        if (m_triple.m_app2num_occs.find(n1, n2, r, num_occs)) {
            TRACE("dyn_ack", tout << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) 
                  << mk_pp(r, m_manager) << "\n" << "\nnum_occs: " << num_occs << "\n";);
            num_occs++;
        }
        else {
            num_occs = 1;
            m_manager.inc_ref(n1);
            m_manager.inc_ref(n2);
            m_manager.inc_ref(r);
            m_triple.m_apps.push_back(tr);
        }
        SASSERT(num_occs > 0);
        m_triple.m_app2num_occs.insert(n1, n2, r, num_occs);
#ifdef Z3DEBUG
        unsigned num_occs2 = 0;
        SASSERT(m_triple.m_app2num_occs.find(n1, n2, r, num_occs2) && num_occs == num_occs2);
#endif
        if (num_occs == m_params.m_dack_threshold) {
            TRACE("dyn_ack", tout << "found candidate:\n" << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) 
                  << "\n" << mk_pp(r, m_manager) 
                  << "\nnum_occs: " << num_occs << "\n";);
            m_triple.m_to_instantiate.push_back(tr);
        }
        
    }

    struct app_pair_lt { 
        typedef std::pair<app *, app *>          app_pair;
        typedef obj_pair_map<app, app, unsigned> app_pair2num_occs;
        app_pair2num_occs &  m_app_pair2num_occs;
        
        app_pair_lt(app_pair2num_occs & m):
            m_app_pair2num_occs(m) {
        }
        
        bool operator()(app_pair const & p1, app_pair const & p2) const {
            unsigned n1 = 0;
            unsigned n2 = 0;
            m_app_pair2num_occs.find(p1.first, p1.second, n1);
            m_app_pair2num_occs.find(p2.first, p2.second, n2);
            SASSERT(n1 > 0);
            SASSERT(n2 > 0);
            return n1 > n2;
        }
    };

    void dyn_ack_manager::gc() {
        TRACE("dyn_ack", tout << "dyn_ack GC\n";);
        unsigned num_deleted = 0;
        m_to_instantiate.reset();
        m_qhead = 0;
        svector<app_pair>::iterator it  = m_app_pairs.begin();
        svector<app_pair>::iterator end = m_app_pairs.end();
        svector<app_pair>::iterator it2 = it;
        for (; it != end; ++it) {
            app_pair & p = *it;
            if (m_instantiated.contains(p)) {
                TRACE("dyn_ack", tout << "1) erasing:\n" << mk_pp(p.first, m_manager) << "\n" << mk_pp(p.second, m_manager) << "\n";);
                m_manager.dec_ref(p.first);
                m_manager.dec_ref(p.second);
                SASSERT(!m_app_pair2num_occs.contains(p.first, p.second));
                continue;
            }
            unsigned num_occs = 0;
            m_app_pair2num_occs.find(p.first, p.second, num_occs);
            // The following invariant is not true. p.first and
            // p.second may have been instantiated, and removed from
            // m_app_pair2num_occs, but not from m_app_pairs.
            //
            // SASSERT(num_occs > 0);
            num_occs = static_cast<unsigned>(num_occs * m_params.m_dack_gc_inv_decay);
            if (num_occs <= 1) {
                num_deleted++;
                TRACE("dyn_ack", tout << "2) erasing:\n" << mk_pp(p.first, m_manager) << "\n" << mk_pp(p.second, m_manager) << "\n";);
                m_app_pair2num_occs.erase(p.first, p.second);
                m_manager.dec_ref(p.first);
                m_manager.dec_ref(p.second);
                continue;
            }
            *it2 = p;
            ++it2;
            SASSERT(num_occs > 0);
            m_app_pair2num_occs.insert(p.first, p.second, num_occs);
            if (num_occs >= m_params.m_dack_threshold)
                m_to_instantiate.push_back(p);
        }
        m_app_pairs.set_end(it2);
        app_pair_lt f(m_app_pair2num_occs);
        // app_pair_lt is not a total order on pairs of expressions.
        // So, we should use stable_sort to avoid different behavior in different platforms.
        std::stable_sort(m_to_instantiate.begin(), m_to_instantiate.end(), f);
        // IF_VERBOSE(10, if (num_deleted > 0) verbose_stream() << "dynamic ackermann GC: " << num_deleted << "\n";);
    }

    class dyn_ack_clause_del_eh : public clause_del_eh {
        dyn_ack_manager & m_manager;
    public:
        dyn_ack_clause_del_eh(dyn_ack_manager & m):
            m_manager(m) {
        }
        virtual ~dyn_ack_clause_del_eh() {}
        virtual void operator()(ast_manager & m, clause * cls) {
            m_manager.del_clause_eh(cls);
            dealloc(this);
        }
    };

    void dyn_ack_manager::del_clause_eh(clause * cls) {
        TRACE("dyn_ack", tout << "del_clause_eh: "; m_context.display_clause(tout, cls); tout << "\n";);
        m_context.m_stats.m_num_del_dyn_ack++;
        
        app_pair p((app*)0,(app*)0);
        if (m_clause2app_pair.find(cls, p)) {
            SASSERT(p.first && p.second);
            m_instantiated.erase(p);
            SASSERT(!m_app_pair2num_occs.contains(p.first, p.second));
            return;
        }
        app_triple tr(0,0,0);
        if (m_triple.m_clause2apps.find(cls, tr)) {
            SASSERT(tr.first && tr.second && tr.third);
            m_triple.m_instantiated.erase(tr);
            SASSERT(!m_triple.m_app2num_occs.contains(tr.first, tr.second, tr.third));
            return;
        }
    }

    void dyn_ack_manager::propagate_eh() {
        if (m_params.m_dack == DACK_DISABLED)
            return;
        m_num_propagations_since_last_gc++;
        if (m_num_propagations_since_last_gc > m_params.m_dack_gc) {
            gc();
            m_num_propagations_since_last_gc = 0;
        }
        unsigned max_instances  = static_cast<unsigned>(m_context.get_num_conflicts() * m_params.m_dack_factor);
        while (m_num_instances < max_instances && m_qhead < m_to_instantiate.size()) {
            app_pair & p = m_to_instantiate[m_qhead];
            m_qhead++;
            m_num_instances++;
            instantiate(p.first, p.second);
        }
        while (m_num_instances < max_instances && m_triple.m_qhead < m_triple.m_to_instantiate.size()) {
            app_triple & p = m_triple.m_to_instantiate[m_triple.m_qhead];
            m_triple.m_qhead++;
            m_num_instances++;
            instantiate(p.first, p.second, p.third);
        }
    }

    literal dyn_ack_manager::mk_eq(expr * n1, expr * n2) {
        app * eq  = m_context.mk_eq_atom(n1, n2);
        m_context.internalize(eq, true);
        literal l = m_context.get_literal(eq);
        TRACE("dyn_ack", tout << "eq:\n" << mk_pp(eq, m_manager) << "\nliteral: "; 
              m_context.display_literal(tout, l); tout << "\n";);
        return l;
    }

    void dyn_ack_manager::instantiate(app * n1, app * n2) {
        SASSERT(m_params.m_dack != DACK_DISABLED);
        SASSERT(n1->get_decl() == n2->get_decl());
        SASSERT(n1->get_num_args() == n2->get_num_args());
        SASSERT(n1 != n2);
        m_context.m_stats.m_num_dyn_ack++;
        TRACE("dyn_ack_inst", tout << "dyn_ack: " << n1->get_id() << " " << n2->get_id() << "\n";);
        TRACE("dyn_ack", tout << "expanding Ackermann's rule for:\n" << mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) << "\n";);
        unsigned num_args = n1->get_num_args();
        literal_buffer lits;
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg1 = n1->get_arg(i);
            expr * arg2 = n2->get_arg(i);
            if (arg1 != arg2)
                lits.push_back(~mk_eq(arg1, arg2));
        }
        app_pair p(n1, n2);
        SASSERT(m_app_pair2num_occs.contains(n1, n2));
        m_app_pair2num_occs.erase(n1, n2);
        // pair n1,n2 is still in m_app_pairs
        m_instantiated.insert(p);
        lits.push_back(mk_eq(n1, n2));
        clause_del_eh * del_eh = alloc(dyn_ack_clause_del_eh, *this);

        justification * js = 0;
        if (m_manager.proofs_enabled())
            js = alloc(dyn_ack_justification, n1, n2);
        clause * cls = m_context.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, del_eh);
        if (!cls) {
            dealloc(del_eh);
            return;
        }
        TRACE("dyn_ack_clause", tout << "new clause:\n"; m_context.display_clause_detail(tout, cls); tout << "\n";);
        m_clause2app_pair.insert(cls, p);
    }

    void dyn_ack_manager::reset() {
        init_search_eh();
        m_instantiated.reset();
        m_clause2app_pair.reset();
        m_triple.m_instantiated.reset();
        m_triple.m_clause2apps.reset();
    }

    void dyn_ack_manager::reset_app_triples() {
        svector<app_triple>::iterator it  = m_triple.m_apps.begin();
        svector<app_triple>::iterator end = m_triple.m_apps.end();
        for (; it != end; ++it) {
            app_triple & p = *it;
            m_manager.dec_ref(p.first);
            m_manager.dec_ref(p.second);
            m_manager.dec_ref(p.third);
        }
        m_triple.m_apps.reset();
    }

    void dyn_ack_manager::instantiate(app * n1, app * n2, app* r) {
        SASSERT(m_params.m_dack != DACK_DISABLED);
        SASSERT(n1 != n2 && n1 != r && n2 != r);
        m_context.m_stats.m_num_dyn_ack++;
        TRACE("dyn_ack_inst", tout << "dyn_ack: " << n1->get_id() << " " << n2->get_id() << " " << r->get_id() << "\n";);
        TRACE("dyn_ack", tout << "expanding Ackermann's rule for:\n" << mk_pp(n1, m_manager) << "\n" 
              << mk_pp(n2, m_manager) << "\n"
              << mk_pp(r,  m_manager) << "\n";
              );
        app_triple tr(n1, n2, r);
        SASSERT(m_triple.m_app2num_occs.contains(n1, n2, r));
        m_triple.m_app2num_occs.erase(n1, n2, r);
        // pair n1,n2 is still in m_triple.m_apps
        m_triple.m_instantiated.insert(tr);
        literal_buffer lits;
        lits.push_back(~mk_eq(n1, r));
        lits.push_back(~mk_eq(n2, r));
        lits.push_back(mk_eq(n1, n2));
        clause_del_eh * del_eh = alloc(dyn_ack_clause_del_eh, *this);

        justification * js = 0;
        if (m_manager.proofs_enabled())
            js = alloc(dyn_ack_justification, n1, n2);
        clause * cls = m_context.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, del_eh);
        if (!cls) {
            dealloc(del_eh);
            return;
        }
        TRACE("dyn_ack_clause", tout << "new clause:\n"; m_context.display_clause_detail(tout, cls); tout << "\n";);
        m_triple.m_clause2apps.insert(cls, tr);
    }


    struct app_triple_lt { 
        typedef triple<app *, app *, app*>          app_triple;
        typedef obj_triple_map<app, app, app, unsigned> app_triple2num_occs;
        app_triple2num_occs &  m_app_triple2num_occs;
        
        app_triple_lt(app_triple2num_occs & m):
            m_app_triple2num_occs(m) {
        }
        
        bool operator()(app_triple const & p1, app_triple const & p2) const {
            unsigned n1 = 0;
            unsigned n2 = 0;
            m_app_triple2num_occs.find(p1.first, p1.second, p1.third, n1);
            m_app_triple2num_occs.find(p2.first, p2.second, p2.third, n2);
            SASSERT(n1 > 0);
            SASSERT(n2 > 0);
            return n1 > n2;
        }
    };

    void dyn_ack_manager::gc_triples() {
        TRACE("dyn_ack", tout << "dyn_ack GC\n";);
        unsigned num_deleted = 0;
        m_triple.m_to_instantiate.reset();
        m_triple.m_qhead = 0;
        svector<app_triple>::iterator it  = m_triple.m_apps.begin();
        svector<app_triple>::iterator end = m_triple.m_apps.end();
        svector<app_triple>::iterator it2 = it;
        for (; it != end; ++it) {
            app_triple & p = *it;
            if (m_triple.m_instantiated.contains(p)) {
                TRACE("dyn_ack", tout << "1) erasing:\n" << mk_pp(p.first, m_manager) << "\n" << mk_pp(p.second, m_manager) << "\n";);
                m_manager.dec_ref(p.first);
                m_manager.dec_ref(p.second);
                m_manager.dec_ref(p.third);
                SASSERT(!m_triple.m_app2num_occs.contains(p.first, p.second, p.third));
                continue;
            }
            unsigned num_occs = 0;
            m_triple.m_app2num_occs.find(p.first, p.second, p.third, num_occs);
            // The following invariant is not true. p.first and
            // p.second may have been instantiated, and removed from
            // m_app_triple2num_occs, but not from m_app_triples.
            //
            // SASSERT(num_occs > 0);
            num_occs = static_cast<unsigned>(num_occs * m_params.m_dack_gc_inv_decay);
            if (num_occs <= 1) {
                num_deleted++;
                TRACE("dyn_ack", tout << "2) erasing:\n" << mk_pp(p.first, m_manager) << "\n" << mk_pp(p.second, m_manager) << "\n";);
                m_triple.m_app2num_occs.erase(p.first, p.second, p.third);
                m_manager.dec_ref(p.first);
                m_manager.dec_ref(p.second);
                m_manager.dec_ref(p.third);
                continue;
            }
            *it2 = p;
            ++it2;
            SASSERT(num_occs > 0);
            m_triple.m_app2num_occs.insert(p.first, p.second, p.third, num_occs);
            if (num_occs >= m_params.m_dack_threshold)
                m_triple.m_to_instantiate.push_back(p);
        }
        m_triple.m_apps.set_end(it2);
        app_triple_lt f(m_triple.m_app2num_occs);
        // app_triple_lt is not a total order
        std::stable_sort(m_triple.m_to_instantiate.begin(), m_triple.m_to_instantiate.end(), f);
        // IF_VERBOSE(10, if (num_deleted > 0) verbose_stream() << "dynamic ackermann GC: " << num_deleted << "\n";);
    }



#ifdef Z3DEBUG
    bool dyn_ack_manager::check_invariant() const {
        clause2app_pair::iterator it  = m_clause2app_pair.begin();
        clause2app_pair::iterator end = m_clause2app_pair.end();
        for (; it != end; ++it) {
            app_pair const & p = it->get_value();
            SASSERT(m_instantiated.contains(p));
            SASSERT(!m_app_pair2num_occs.contains(p.first, p.second));
        }

        return true;
    }
#endif

};
