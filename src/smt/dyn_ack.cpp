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
#include "smt/smt_context.h"
#include "smt/dyn_ack.h"
#include "ast/ast_pp.h"

namespace smt {

    /**
       \brief Justification for dynamic ackermann clause
    */
    class dyn_ack_cc_justification : public justification {
        app *     m_app1;
        app *     m_app2;
    public:
        dyn_ack_cc_justification(app * n1, app * n2):
            justification(false), // dyn_ack_cc_justifications are not stored in regions.
            m_app1(n1), 
            m_app2(n2) {
            SASSERT(m_app1->get_num_args() == m_app2->get_num_args());
            SASSERT(m_app1->get_decl() == m_app2->get_decl());
            SASSERT(m_app1->get_num_args() > 0);
            SASSERT(m_app1->get_id() < m_app2->get_id());
        }

        char const * get_name() const override { return "dyn-ack"; }

        void get_antecedents(conflict_resolution & cr) override {}

        void display_debug_info(conflict_resolution & cr, std::ostream & out) override {
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
            SASSERT(m.is_eq(eq));
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

        proof * mk_proof(conflict_resolution & cr) override {
            ast_manager & m   = cr.get_manager();
            unsigned num_args = m_app1->get_num_args();
            proof_ref_vector prs(m);
            expr_ref_vector lits(m);
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg1 = m_app1->get_arg(i);
                expr * arg2 = m_app2->get_arg(i);
                if (arg1 != arg2) {
                    app * eq  = m.mk_eq(arg1, arg2);
                    app_ref neq(m.mk_not(eq), m);
                    if (std::find(lits.begin(), lits.end(), neq.get()) == lits.end()) {
                        lits.push_back(neq);
                        prs.push_back(mk_hypothesis(m, eq, false, arg1, arg2));
                    }
                }
            }
            app_ref eq(m.mk_eq(m_app1, m_app2), m);
            proof_ref a1(m.mk_congruence(m_app1, m_app2, prs.size(), prs.data()), m);
            proof_ref a2(mk_hypothesis(m, eq, true, m_app1, m_app2), m);
            proof * antecedents[2] = { a1.get(), a2.get() };
            proof_ref false_pr(m.mk_unit_resolution(2, antecedents), m);
            lits.push_back(eq);
            SASSERT(lits.size() >= 2);
            app_ref lemma(m.mk_or(lits), m);
            TRACE("dyn_ack", tout << lemma << "\n";);
            TRACE("dyn_ack", tout << false_pr << "\n";);
            return m.mk_lemma(false_pr, lemma);
        }

    };

    class dyn_ack_eq_justification : public justification {
        app *     m_app1;
        app *     m_app2;
        app *     m_r;
        app *     m_eq1;
        app *     m_eq2;
        app *     m_eq3;
    public:
        dyn_ack_eq_justification(app * n1, app * n2, app* r, app* eq1, app* eq2, app* eq3):
            justification(false), // dyn_ack_cc_justifications are not stored in regions.
            m_app1(n1), 
            m_app2(n2), 
            m_r(r),
            m_eq1(eq1),
            m_eq2(eq2),
            m_eq3(eq3) {
        }
        char const * get_name() const override { return "dyn-ack-eq"; }
        void get_antecedents(conflict_resolution & cr) override {}
        void display_debug_info(conflict_resolution & cr, std::ostream & out) override {
            ast_manager & m = cr.get_manager();
            out << mk_pp(m_eq1, m) << " " << mk_pp(m_eq2, m) << " => " << mk_pp(m_eq3, m) << "\n";
        }

        /**
         *   Create a proof of (or ~eq1 ~eq2 eq3)
         *   eq1 := app1 = r         or symmetric
         *   eq2 := app2 = r         or symmetric
         *   eq3 := app1 = app2      or symmetric
         * 
         *   p1: trans: hyp(eq1), hyp(eq2) |- eq3
         *   p2: unit-resolution: p1, hyp(~eq3) |- false
         *   p3: lemma: (or ~eq1 ~eq2 eq3)
         */
        proof * mk_proof(conflict_resolution & cr) override {            
            ast_manager & m   = cr.get_manager();
            proof* p1, *p2, *p3, *p4, *p5, *p6;
            expr* x = nullptr, *y = nullptr;
            (void)x; (void)y;
            p1 = m.mk_hypothesis(m_eq1);
            if (m_eq1->get_arg(1) == m_app1) p1 = m.mk_symmetry(p1);
            p2 = m.mk_hypothesis(m_eq2);
            if (m_eq2->get_arg(0) == m_app2) p2 = m.mk_symmetry(p2);
            (void)m_r;
            SASSERT(m.is_eq(m.get_fact(p1), x, y) && x == m_app1 && y == m_r);
            SASSERT(m.is_eq(m.get_fact(p2), x, y) && x == m_r && y == m_app2);
            p3 = m.mk_transitivity(p1, p2);
            SASSERT(m.is_eq(m.get_fact(p3), x, y) && x == m_app1 && y == m_app2);
            if (m.get_fact(p3) != m_eq3) p3 = m.mk_symmetry(p3);
            SASSERT(m.get_fact(p3) == m_eq3);
            p4 = m.mk_hypothesis(m.mk_not(m_eq3));
            proof* ps[2] = { p3, p4 };
            p5 = m.mk_unit_resolution(2, ps);
            SASSERT(m.get_fact(p5) == m.mk_false());
            expr* eqs[3] = { m.mk_not(m_eq1), m.mk_not(m_eq2), m_eq3 };
            expr_ref conclusion(m.mk_or(3, eqs), m);
            p6 = m.mk_lemma(p5, conclusion);
            return p6;
        }
    };

    dyn_ack_manager::dyn_ack_manager(context & ctx, dyn_ack_params & p):
        m_context(ctx),
        m(ctx.get_manager()),
        m_params(p) {
    }

    dyn_ack_manager::~dyn_ack_manager() {
        reset_app_pairs();
        reset_app_triples();
    }

    void dyn_ack_manager::reset_app_pairs() {
        for (app_pair& p : m_app_pairs) {
            m.dec_ref(p.first);
            m.dec_ref(p.second);
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
        if (m.is_eq(n1)) {
            return;
        }
        if (n1->get_id() > n2->get_id())
            std::swap(n1,n2);
        app_pair p(n1, n2);
        if (m_instantiated.contains(p)) {
            return;
        }
        unsigned num_occs = 0;
        if (m_app_pair2num_occs.find(n1, n2, num_occs)) {
            TRACE("dyn_ack", tout << "used_cg_eh:\n" << mk_pp(n1, m) << "\n" << mk_pp(n2, m) << "\nnum_occs: " << num_occs << "\n";);
            num_occs++;
        }
        else {
            num_occs = 1;
            m.inc_ref(n1);
            m.inc_ref(n2);
            m_app_pairs.push_back(p);
        }
        SASSERT(num_occs > 0);
        m_app_pair2num_occs.insert(n1, n2, num_occs);
#ifdef Z3DEBUG
        unsigned num_occs2 = 0;
        SASSERT(m_app_pair2num_occs.find(n1, n2, num_occs2) && num_occs == num_occs2);
#endif
        if (num_occs == m_params.m_dack_threshold) {
            TRACE("dyn_ack", tout << "found candidate:\n" << mk_pp(n1, m) << "\n" << mk_pp(n2, m) << "\nnum_occs: " << num_occs << "\n";);
            m_to_instantiate.push_back(p);
        }
    }

    void dyn_ack_manager::eq_eh(app * n1, app * n2, app* r) {
        if (n1 == n2 || r == n1 || r == n2 || m.is_bool(n1)) {
            return;
        }
        if (n1->get_id() > n2->get_id())
            std::swap(n1,n2);
        TRACE("dyn_ack", 
              tout << mk_pp(n1, m) << " = " << mk_pp(n2, m) << " = " << mk_pp(r, m) << "\n";);
        app_triple tr(n1, n2, r);
        if (m_triple.m_instantiated.contains(tr)) {
            return;
        }
        unsigned num_occs = 0;
        if (m_triple.m_app2num_occs.find(n1, n2, r, num_occs)) {
            TRACE("dyn_ack", tout << mk_pp(n1, m) << "\n" << mk_pp(n2, m) << "\n"
                  << mk_pp(r, m) << "\n" << "\nnum_occs: " << num_occs << "\n";);
            num_occs++;
        }
        else {
            num_occs = 1;
            m.inc_ref(n1);
            m.inc_ref(n2);
            m.inc_ref(r);
            m_triple.m_apps.push_back(tr);
        }
        SASSERT(num_occs > 0);
        m_triple.m_app2num_occs.insert(n1, n2, r, num_occs);
#ifdef Z3DEBUG
        unsigned num_occs2 = 0;
        SASSERT(m_triple.m_app2num_occs.find(n1, n2, r, num_occs2) && num_occs == num_occs2);
#endif
        if (num_occs == m_params.m_dack_threshold) {
            TRACE("dyn_ack", tout << "found candidate:\n" << mk_pp(n1, m) << "\n" << mk_pp(n2, m) 
                  << "\n" << mk_pp(r, m) 
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
                TRACE("dyn_ack", tout << "1) erasing:\n" << mk_pp(p.first, m) << "\n" << mk_pp(p.second, m) << "\n";);
                m.dec_ref(p.first);
                m.dec_ref(p.second);
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
                TRACE("dyn_ack", tout << "2) erasing:\n" << mk_pp(p.first, m) << "\n" << mk_pp(p.second, m) << "\n";);
                m_app_pair2num_occs.erase(p.first, p.second);
                m.dec_ref(p.first);
                m.dec_ref(p.second);
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
        dyn_ack_manager & m;
    public:
        dyn_ack_clause_del_eh(dyn_ack_manager & m):
            m(m) {
        }
        ~dyn_ack_clause_del_eh() override {}
        void operator()(ast_manager & _m, clause * cls) override {
            m.del_clause_eh(cls);
            dealloc(this);
        }
    };

    void dyn_ack_manager::del_clause_eh(clause * cls) {
        m_context.m_stats.m_num_del_dyn_ack++;
        app_pair p((app*)nullptr,(app*)nullptr);
        if (m_clause2app_pair.find(cls, p)) {
            SASSERT(p.first && p.second);
            m_instantiated.erase(p);
            m_clause2app_pair.erase(cls);
            SASSERT(!m_app_pair2num_occs.contains(p.first, p.second));
            return;
        }
        app_triple tr(0,0,0);
        if (m_triple.m_clause2apps.find(cls, tr)) {
            SASSERT(tr.first && tr.second && tr.third);
            m_triple.m_instantiated.erase(tr);
            m_triple.m_clause2apps.erase(cls);
            SASSERT(!m_triple.m_app2num_occs.contains(tr.first, tr.second, tr.third));
            return;
        }
    }

    void dyn_ack_manager::propagate_eh() {
        if (m_params.m_dack == dyn_ack_strategy::DACK_DISABLED)
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
		app_ref eq(m.mk_eq(n1, n2), m);
        m_context.internalize(eq, true);
        literal l = m_context.get_literal(eq);
        TRACE("dyn_ack", tout << "eq:\n" << mk_pp(eq, m) << "\nliteral: "; 
              m_context.display_literal(tout, l); tout << "\n";);
        return l;
    }

    void dyn_ack_manager::instantiate(app * n1, app * n2) {
        SASSERT(m_params.m_dack != dyn_ack_strategy::DACK_DISABLED);
        SASSERT(n1->get_decl() == n2->get_decl());
        SASSERT(n1->get_num_args() == n2->get_num_args());
        SASSERT(n1 != n2);
        m_context.m_stats.m_num_dyn_ack++;
        TRACE("dyn_ack_inst", tout << "dyn_ack: " << n1->get_id() << " " << n2->get_id() << "\n";);
        TRACE("dyn_ack", tout << "expanding Ackermann's rule for:\n" << mk_pp(n1, m) << "\n" << mk_pp(n2, m) << "\n";);
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

        justification * js = nullptr;
        if (m.proofs_enabled())
            js = alloc(dyn_ack_cc_justification, n1, n2);
        clause * cls = m_context.mk_clause(lits.size(), lits.data(), js, CLS_TH_LEMMA, del_eh);
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
        for (app_triple& p : m_triple.m_apps) {
            m.dec_ref(p.first);
            m.dec_ref(p.second);
            m.dec_ref(p.third);
        }
        m_triple.m_apps.reset();
    }

    void dyn_ack_manager::instantiate(app * n1, app * n2, app* r) {
        context& ctx = m_context;
        SASSERT(m_params.m_dack != dyn_ack_strategy::DACK_DISABLED);
        SASSERT(n1 != n2 && n1 != r && n2 != r);
        ctx.m_stats.m_num_dyn_ack++;
        TRACE("dyn_ack_inst", tout << "dyn_ack: " << n1->get_id() << " " << n2->get_id() << " " << r->get_id() << "\n";);
        TRACE("dyn_ack", tout << "expanding Ackermann's rule for:\n" << mk_pp(n1, m) << "\n" 
              << mk_pp(n2, m) << "\n"
              << mk_pp(r,  m) << "\n";
              );
        app_triple tr(n1, n2, r);
        SASSERT(m_triple.m_app2num_occs.contains(n1, n2, r));
        m_triple.m_app2num_occs.erase(n1, n2, r);
        // pair n1,n2 is still in m_triple.m_apps
        m_triple.m_instantiated.insert(tr);
        literal_buffer lits;
        literal eq1 = mk_eq(n1, r);
        literal eq2 = mk_eq(n2, r);
        literal eq3 = mk_eq(n1, n2);
        lits.push_back(~eq1);
        lits.push_back(~eq2);
        lits.push_back(eq3);
        clause_del_eh * del_eh = alloc(dyn_ack_clause_del_eh, *this);
        justification * js = nullptr;
        if (m.proofs_enabled()) {
            js = alloc(dyn_ack_eq_justification, n1, n2, r, 
                       m.mk_eq(n1, r),
                       m.mk_eq(n2, r),
                       m.mk_eq(n1, n2));
        }
        clause * cls = ctx.mk_clause(lits.size(), lits.data(), js, CLS_TH_LEMMA, del_eh);
        if (!cls) {
            dealloc(del_eh);
            return;
        }
        TRACE("dyn_ack_clause", ctx.display_clause_detail(tout << "new clause:\n", cls); tout << "\n";);
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
                TRACE("dyn_ack", tout << "1) erasing:\n" << mk_pp(p.first, m) << "\n" << mk_pp(p.second, m) << "\n";);
                m.dec_ref(p.first);
                m.dec_ref(p.second);
                m.dec_ref(p.third);
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
                TRACE("dyn_ack", tout << "2) erasing:\n" << mk_pp(p.first, m) << "\n" << mk_pp(p.second, m) << "\n";);
                m_triple.m_app2num_occs.erase(p.first, p.second, p.third);
                m.dec_ref(p.first);
                m.dec_ref(p.second);
                m.dec_ref(p.third);
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
        for (auto const& kv : m_clause2app_pair) {
            app_pair const & p = kv.get_value();
            SASSERT(m_instantiated.contains(p));
            SASSERT(!m_app_pair2num_occs.contains(p.first, p.second));
        }

        return true;
    }
#endif

};
