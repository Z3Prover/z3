/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    theory_array_bapa.cpp

Abstract:

   Saturation procedure for BAPA predicates.
   Assume there is a predicate

           Size(S, n)   for S : Array(T, Bool) and n : Int

   The predicate is true if S is a set of size n.


                 Size(S, n), Size(T, m)      
          S, T are intersecting. n != m or S != T
D  ---------------------------------------------------------
   Size(S, n) => Size(S\T, k1), Size(S n T, k2), n = k1 + k2
   Size(T, m) => Size(T\S, k3), SIze(S n T, k2), m = k2 + k3   

        Size(S, n)
P  --------------------
   Size(S, n) => n >= 0

   Size(S, n), is infinite domain
B  ------------------------------
   Size(S, n) => default(S) = false

   Size(S, n), Size(S, m)
F  --------------------------------
   Size(S, n), Size(S, m) =>  n = m

   Fixing values during final check:
      Size(S, n)
V  -------------------
   assume value(n) = n 
   
    Size(S, n), S[i1], ..., S[ik]
O  -------------------------------
   ~distinct(i1, ... ik) or n >= k

                  Size(S,n)
Ak -------------------------------------------------- 
   S[i1] & .. & S[ik] & distinct(i1, .., ik) or n < k

Q: Is this sufficient? Axiom A1 could be adjusted to add new elements i' until there are k witnesses for Size(S, k).
This is quite bad when k is very large. Instead rely on stably infiniteness or other domain properties of the theories.

When A is finite domain, or there are quantifiers there could be constraints that force domain sizes so domain sizes may have 
to be enforced. A succinct way would be through domain comprehension assertions. 

Finite domains:

   Size(S, n), is finite domain
   ----------------------------
          S <= |A|

     Size(S, n), !S[i1], .... !S[ik],  S is finite domain  
   ----------------------------------------------------------
   default(S) = false or ~distinct(i1,..,ik) or |A| - k <= n


    ~Size(S, m) is negative on all occurrences, S is finite domain
    ---------------------------------------------------------------
                     Size(S, n) n fresh.

    Model construction for infinite domains when all Size(S, m) are negative for S.

Author:

    Nikolaj Bjorner 2019-04-13

Revision History:

 */

#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/array_rewriter.h"
#include "smt/smt_context.h"
#include "smt/smt_arith_value.h"
#include "smt/theory_array_full.h"
#include "smt/theory_array_bapa.h"

#if 0
- set of native select terms that are true
- set of auxiliary select terms.
- n1, n2, n3, n4.
- a1, a2, a3, a4, a5.
- 
- add select terms, such that first 
#endif

namespace smt {
    
    class theory_array_bapa::imp {
        struct sz_info {
            bool                  m_is_leaf;   // has it been split into disjoint subsets already?
            rational              m_size;      // set to >= integer if fixed in final check, otherwise -1
            literal               m_literal;   // literal that enforces value is set.
            obj_map<enode, expr*> m_selects;
            sz_info(): m_is_leaf(true), m_size(rational::minus_one()), m_literal(null_literal) {}
        };

        typedef std::pair<func_decl*, func_decl*> func_decls;

        ast_manager&              m;
        theory_array_full&        th;
        arith_util                m_arith;
        array_util                m_autil;
        th_rewriter               m_rw;
        arith_value               m_arith_value;
        ast_ref_vector            m_pinned;
        obj_map<app, sz_info*>    m_sizeof;
        obj_map<expr, rational>   m_size_limit;
        obj_map<sort, func_decls> m_index_skolems;
        obj_map<sort, func_decl*> m_size_limit_sort2skolems;
        unsigned                  m_max_set_enumeration;

        context& ctx() { return th.get_context(); }

        void reset() {
            for (auto& kv : m_sizeof) {
                dealloc(kv.m_value);
            }
        }

        bool is_true(expr* e) { return is_true(ctx().get_literal(e)); }
        bool is_true(enode* e) { return is_true(e->get_owner()); }
        bool is_true(literal l) { return ctx().is_relevant(l) && ctx().get_assignment(l) == l_true; }
        bool is_leaf(sz_info& i) const { return i.m_is_leaf; }
        bool is_leaf(sz_info* i) const { return is_leaf(*i); }
        enode* get_root(expr* e) { return ctx().get_enode(e)->get_root(); }
        bool is_select(enode* n) { return th.is_select(n); }
        app_ref mk_select(expr* a, expr* i) { expr* args[2] = { a, i }; return app_ref(m_autil.mk_select(2, args), m); }
        literal get_literal(expr* e) { return ctx().get_literal(e); }
        literal mk_literal(expr* e) { if (!ctx().e_internalized(e)) ctx().internalize(e, false); literal lit = get_literal(e); ctx().mark_as_relevant(lit); return lit; }
        literal mk_eq(expr* a, expr* b) { literal lit = th.mk_eq(a, b, false); ctx().mark_as_relevant(lit); return lit; }
        void mk_th_axiom(literal l1, literal l2) {
            literal lits[2] = { l1, l2 };
            mk_th_axiom(2, lits);
        }
        void mk_th_axiom(literal l1, literal l2, literal l3) {
            literal lits[3] = { l1, l2, l3 };
            mk_th_axiom(3, lits);
        }
        void mk_th_axiom(unsigned n, literal* lits) {
            TRACE("array", ctx().display_literals_verbose(tout, n, lits) << "\n";);
            ctx().mk_th_axiom(th.get_id(), n, lits);            
        }

        void update_indices() {
            for (auto const& kv : m_sizeof) {     
                app* k = kv.m_key;
                sz_info& v = *kv.m_value;
                v.m_selects.reset();
                if (is_true(k) && is_leaf(v)) {
                    enode* set = get_root(k->get_arg(0));
                    for (enode* parent : enode::parents(set)) {
                        if (is_select(parent) && parent->get_arg(0)->get_root() == set) {
                            if (is_true(parent)) {
                                v.m_selects.insert(parent->get_arg(1)->get_root(), parent->get_owner());
                            }
                        }
                    }                    
                }
            }
        }

        /**
            F: Size(S, k1) & Size(S, k2) => k1 = k2
         */
        lbool ensure_functional() {
            lbool result = l_true;
            obj_map<enode, app*> parents;
            for (auto const& kv : m_sizeof) {     
                app* sz1 = kv.m_key;
                if (!is_true(sz1)) {
                    continue;
                }
                enode* r = get_root(sz1->get_arg(0));
                app* sz2 = nullptr;
                if (parents.find(r, sz2)) {
                    expr* k1 = sz1->get_arg(1);
                    expr* k2 = sz2->get_arg(1);
                    if (get_root(k1) != get_root(k2)) {
                        mk_th_axiom(~get_literal(sz1), ~get_literal(sz2), mk_eq(k1, k2));
                        result = l_false;
                    }
                }
                else {
                    parents.insert(r, sz1);
                }
            }
            return result;
        }

        /**
           Enforce D
         */
        lbool ensure_disjoint() {
            auto i = m_sizeof.begin(), end = m_sizeof.end();
            for (; i != end; ++i) {
                auto& kv = *i;
                if (!kv.m_value->m_is_leaf) {
                    continue;
                }
                for (auto j = i; ++j != end; ) {
                    if (j->m_value->m_is_leaf && !ensure_disjoint(i->m_key, j->m_key)) {
                        return l_false;
                    }
                }
            }
            return l_true;
        }

        bool ensure_disjoint(app* sz1, app* sz2) {
            sz_info& i1 = *m_sizeof[sz1];
            sz_info& i2 = *m_sizeof[sz2];
            SASSERT(i1.m_is_leaf);
            SASSERT(i2.m_is_leaf);
            expr* s = sz1->get_arg(0);
            expr* t = sz2->get_arg(0);
            if (m.get_sort(s) != m.get_sort(t)) {
                return true;
            }
            enode* r1 = get_root(s);
            enode* r2 = get_root(t);
            if (r1 == r2) {
                return true;
            }
            if (!ctx().is_diseq(r1, r2) && ctx().assume_eq(r1, r2)) {
                return false;
            }
            if (do_intersect(i1.m_selects, i2.m_selects)) {
                add_disjoint(sz1, sz2);
                return false;
            }
            return true;
        }

        bool do_intersect(obj_map<enode, expr*> const& s, obj_map<enode, expr*> const& t) const {
            if (s.size() > t.size()) {
                return do_intersect(t, s);
            }
            for (auto const& idx : s)
                if (t.contains(idx.m_key)) 
                    return true;
            return false;
        }

        void add_disjoint(app* sz1, app* sz2) {
            sz_info& i1 = *m_sizeof[sz1];
            sz_info& i2 = *m_sizeof[sz2];
            SASSERT(i1.m_is_leaf);
            SASSERT(i2.m_is_leaf);
            expr* t = sz1->get_arg(0);
            expr* s = sz2->get_arg(0);
            expr_ref tms = mk_subtract(t, s);
            expr_ref smt = mk_subtract(s, t);
            expr_ref tns = mk_intersect(t, s);
#if 0
            std::cout << tms << "\n";
            std::cout << smt << "\n";
            std::cout << tns << "\n";
#endif
            if (tns == sz1) {
                std::cout << "SEEN " << tms << "\n";
            }
            if (tns == sz2) {
                std::cout << "SEEN " << smt << "\n";                
            }
            ctx().push_trail(value_trail<context, bool>(i1.m_is_leaf, false));
            ctx().push_trail(value_trail<context, bool>(i2.m_is_leaf, false));
            expr_ref k1(m), k2(m), k3(m);
            expr_ref sz_tms(m), sz_tns(m), sz_smt(m);
            k1 = m_autil.mk_card(tms);
            k2 = m_autil.mk_card(tns);
            k3 = m_autil.mk_card(smt);
            sz_tms = m_autil.mk_has_size(tms, k1);
            sz_tns = m_autil.mk_has_size(tns, k2);
            sz_smt = m_autil.mk_has_size(smt, k3);
            propagate(sz1, sz_tms);
            propagate(sz1, sz_tns);
            propagate(sz2, sz_smt);
            propagate(sz2, sz_tns);
            propagate(sz1, mk_eq(k1 + k2, sz1->get_arg(1)));
            propagate(sz2, mk_eq(k3 + k2, sz2->get_arg(1)));
        }

        expr_ref mk_subtract(expr* t, expr* s) {
            expr_ref d(m_autil.mk_setminus(t, s), m);
            m_rw(d);
            return d;
        }

        expr_ref mk_intersect(expr* t, expr* s) {
            expr_ref i(m_autil.mk_intersection(t, s), m);
            m_rw(i);
            return i;
        }

        void propagate(expr* assumption, expr* conseq) {
            propagate(assumption, mk_literal(conseq));
        }

        void propagate(expr* assumption, literal conseq) {
            mk_th_axiom(~mk_literal(assumption), conseq);
        }

        /**
           Enforce V
         */
        lbool ensure_values_assigned() {
            lbool result = l_true;
            for (auto const& kv : m_sizeof) {
                app* k = kv.m_key;
                sz_info& i = *kv.m_value;
                if (is_leaf(&i) && (i.m_literal == null_literal || !is_true(i.m_literal))) {
                    rational value;
                    expr* sz  = k->get_arg(1);
                    if (!m_arith_value.get_value(sz, value)) {
                        return l_undef;
                    }  
                    literal lit = mk_eq(sz, m_arith.mk_int(value));
                    ctx().set_true_first_flag(lit.var());
                    ctx().push_trail(value_trail<context, literal>(i.m_literal, lit));
                    ctx().push_trail(value_trail<context, rational>(i.m_size, value));
                    result = l_false;
                }
            }
            return result;
        }

        /**
           Enforce Ak,
        */
        lbool ensure_non_empty() {
            for (auto const& kv : m_sizeof) {
                sz_info& i = *kv.m_value;
                app* set_sz = kv.m_key;
                if (is_true(set_sz) && is_leaf(i) && i.m_selects.size() < i.m_size) {
                    expr* set = set_sz->get_arg(0);
                    expr_ref le(m_arith.mk_le(set_sz->get_arg(1), m_arith.mk_int(0)), m);
                    literal le_lit = mk_literal(le);
                    literal sz_lit = mk_literal(set_sz);
                    for (unsigned k = i.m_selects.size(); rational(k) < i.m_size; ++k) {
                        expr_ref idx = mk_index_skolem(set_sz, set, k);
                        app_ref sel(mk_select(set, idx), m);
                        mk_th_axiom(~sz_lit, le_lit, mk_literal(sel));
                        TRACE("array", tout << idx << " " << sel << " " << i.m_size << "\n";);
                    }
                    return l_false;
                }
            }
            return l_true;
        }

        // create skolem function that is injective on integers (ensures uniqueness).
        expr_ref mk_index_skolem(app* sz, expr* a, unsigned n) {
            func_decls fg;
            sort* s = m.get_sort(a);
            if (!m_index_skolems.find(s, fg)) {
                sort* idx_sort = get_array_domain(s, 0);
                sort* dom1[2] = { s, m_arith.mk_int() };
                sort* dom2[1] = { idx_sort };
                func_decl* f = m.mk_fresh_func_decl("to-index",   "", 2, dom1, idx_sort);
                func_decl* g = m.mk_fresh_func_decl("from-index", "", 1, dom2, m_arith.mk_int());
                fg = std::make_pair(f, g);
                m_index_skolems.insert(s, fg);
                m_pinned.push_back(f);
                m_pinned.push_back(g);
                m_pinned.push_back(s);
            }
            expr_ref nV(m_arith.mk_int(n), m);
            expr_ref result(m.mk_app(fg.first, a, nV), m);   
            expr_ref le(m_arith.mk_le(sz->get_arg(1), nV), m);
            // set-has-size(a, k) => k <= n or g(f(a,n)) = n 
            mk_th_axiom(~mk_literal(sz), mk_literal(le), mk_eq(nV, m.mk_app(fg.second, result)));
            return result;
        }


        /**
           Enforce O
        */
        lbool ensure_no_overflow() {
            for (auto const& kv : m_sizeof) {
                if (is_true(kv.m_key) && is_leaf(kv.m_value)) {
                    lbool r = ensure_no_overflow(kv.m_key, *kv.m_value);
                    if (r != l_true) return r;
                }
            }
            return l_true;
        }

        lbool ensure_no_overflow(app* sz, sz_info& info) {
            SASSERT(!info.m_size.is_neg());
            if (info.m_size < info.m_selects.size()) {
                for (auto i = info.m_selects.begin(), e = info.m_selects.end(); i != e; ++i) {
                    for (auto j = i; ++j != e; ) {
                        if (ctx().assume_eq(i->m_key, j->m_key)) {
                            return l_false;
                        }
                    } 
                }                
                // if all is exhausted, then add axiom: set-has-size(s, n) & s[indices] & all-diff(indices) => n >= |indices|
                literal_vector lits;
                lits.push_back(~mk_literal(sz));
                for (auto const& kv : info.m_selects) {
                    lits.push_back(~mk_literal(kv.m_value));
                }
                if (info.m_selects.size() > 1) {
                    ptr_vector<expr> args;
                    for (auto const& kv : info.m_selects) {
                        args.push_back(kv.m_key->get_owner());
                    }
                    expr_ref diff(m.mk_distinct(args.size(), args.c_ptr()), m);
                    lits.push_back(~mk_literal(diff));
                }
                expr_ref ge(m_arith.mk_ge(sz->get_arg(1), m_arith.mk_int(info.m_selects.size())), m);
                lits.push_back(mk_literal(ge));
                mk_th_axiom(lits.size(), lits.c_ptr());
                return l_false;
            }
            return l_true;
        }

        class remove_sz : public trail<context> {
            obj_map<app, sz_info*> & m_table;
            app*                     m_obj;
        public:
            remove_sz(obj_map<app, sz_info*>& tab, app* t): m_table(tab), m_obj(t) {}
            ~remove_sz() override {}
            void undo(context& ctx) override { dealloc(m_table[m_obj]); m_table.remove(m_obj); }
        };

        std::ostream& display(std::ostream& out) {
            for (auto const& kv : m_sizeof) {
                display(out << mk_pp(kv.m_key, m) << ": ", *kv.m_value);
            }
            return out;
        }

        std::ostream& display(std::ostream& out, sz_info& sz) {
            return out << (sz.m_is_leaf ? "leaf": "") << " size: " << sz.m_size << " selects: " << sz.m_selects.size() << "\n";
        }
        
    public:
        imp(theory_array_full& th):
            m(th.get_manager()),
            th(th),
            m_arith(m),
            m_autil(m),
            m_rw(m),
            m_arith_value(m),
            m_pinned(m)
        {
            context& ctx = th.get_context();
            m_arith_value.init(&ctx);
            m_max_set_enumeration = 4;
        }

        ~imp() {
            reset();
        }

        void internalize_term(app* term) {
            if (th.is_set_has_size(term)) {
                internalize_size(term);
            }
            else if (th.is_set_card(term)) {
                internalize_card(term);
            }
        }

        /**
         *  Size(S, n) => n >= 0, default(S) = false
         */
        void internalize_size(app* term) {
            SASSERT(ctx().e_internalized(term));
            literal lit = mk_literal(term);
            expr* s = term->get_arg(0);
            expr* n = term->get_arg(1);
            mk_th_axiom(~lit, mk_literal(m_arith.mk_ge(n, m_arith.mk_int(0))));
            sort_size const& sz = m.get_sort(s)->get_num_elements();
            if (sz.is_infinite()) {
                mk_th_axiom(~lit, mk_eq(th.mk_default(s), m.mk_false()));
            }
            else {
                warning_msg("correct handling of finite domains is TBD");
                // add upper bound on size of set.
                // add case where default(S) = true, and add negative elements.
            }
            m_sizeof.insert(term, alloc(sz_info));
            m_size_limit.insert(s, rational(2));
            assert_size_limit(s, n);
            ctx().push_trail(remove_sz(m_sizeof, term));
        }

        /**
           \brief whenever there is a cardinality function, it includes an axiom
           that entails the set is finite.
         */
        void internalize_card(app* term) {
            SASSERT(ctx().e_internalized(term));
            app_ref has_size(m_autil.mk_has_size(term->get_arg(0), term), m);
            literal lit = mk_literal(has_size);
            ctx().assign(lit, nullptr);
        }

        lbool trace_call(char const* msg, lbool r) {
            if (r != l_true) {
                IF_VERBOSE(2, verbose_stream() << msg << "\n");
            }
            return r;
        }

        final_check_status final_check() {            
            final_check_status st = m_arith_value.final_check();
            if (st != FC_DONE) return st;
            lbool r = trace_call("ensure_functional", ensure_functional());
            if (r == l_true) update_indices();
            if (r == l_true) r = trace_call("ensure_disjoint", ensure_disjoint());
            if (r == l_true) r = trace_call("eensure_values_assigned", ensure_values_assigned());
            if (r == l_true) r = trace_call("ensure_non_empty", ensure_non_empty());
            if (r == l_true) r = trace_call("ensure_no_overflow", ensure_no_overflow());
            CTRACE("array", r != l_true, display(tout););
            switch (r) {
            case l_true:
                return FC_DONE;
            case l_false:
                return FC_CONTINUE;
            case l_undef:
                return FC_GIVEUP;
            }
            return FC_GIVEUP;
        }

        void init_model() {
            for (auto const& kv : m_sizeof) {
                sz_info& i = *kv.m_value;
                app* sz = kv.m_key;
                if (is_true(sz) && is_leaf(i) && rational(i.m_selects.size()) != i.m_size) {
                    warning_msg("models for BAPA is TBD");
                    break;
                }
            }
        }

        bool should_research(expr_ref_vector & unsat_core) {
            expr* set, *sz;
            for (auto & e : unsat_core) {
                if (is_app(e) && is_size_limit(to_app(e), set, sz)) {
                    inc_size_limit(set, sz);
                    return true;
                }
            }
            return false;
        }

        void inc_size_limit(expr* set, expr* sz) {
            IF_VERBOSE(2, verbose_stream() << "inc value " << mk_pp(set, m) << "\n");
            m_size_limit[set] *= rational(2);
            assert_size_limit(set, sz);
        }
        
        bool is_size_limit(app* e, expr*& set, expr*& sz) {
            func_decl* d = nullptr;
            if (e->get_num_args() > 0 && m_size_limit_sort2skolems.find(m.get_sort(e->get_arg(0)), d) && d == e->get_decl()) {
                set = e->get_arg(0);
                sz  = e->get_arg(1);
                return true;
            }
            else {
                return false;
            }
        }

        // has-size(s,n) & size-limit(s, n, k)  => n <= k

        app_ref mk_size_limit(expr* set, expr* sz) {
            func_decl* sk = nullptr;
            sort* s = m.get_sort(set);
            if (!m_size_limit_sort2skolems.find(s, sk)) {
                sort* dom[3] = { s, m_arith.mk_int(), m_arith.mk_int() };
                sk = m.mk_fresh_func_decl("value-limit", "", 3, dom, m.mk_bool_sort());
                m_pinned.push_back(sk);                    
                m_size_limit_sort2skolems.insert(s, sk);
            }             
            return app_ref(m.mk_app(sk, set, sz, m_arith.mk_int(m_size_limit[set])), m);            
        }

        void assert_size_limit(expr* set, expr* sz) {
            app_ref set_sz(m_autil.mk_has_size(set, sz), m);
            app_ref lim(m_arith.mk_int(m_size_limit[set]), m);
            app_ref size_limit = mk_size_limit(set, sz);
            mk_th_axiom(~mk_literal(set_sz), ~mk_literal(size_limit), mk_literal(m_arith.mk_le(sz, lim)));
        }

        void add_theory_assumptions(expr_ref_vector & assumptions) {
            for (auto const& kv : m_sizeof) {
                expr* set = kv.m_key->get_arg(0);
                expr* sz =  kv.m_key->get_arg(1);
                assumptions.push_back(mk_size_limit(set, sz));
            }            
            TRACE("array", tout << "ASSUMPTIONS: " << assumptions << "\n";);
        }
    
    };

    theory_array_bapa::theory_array_bapa(theory_array_full& th) { m_imp = alloc(imp, th);  }

    theory_array_bapa::~theory_array_bapa() { dealloc(m_imp); }

    void theory_array_bapa::internalize_term(app* term) { m_imp->internalize_term(term); }

    final_check_status theory_array_bapa::final_check() { return m_imp->final_check(); }

    void theory_array_bapa::init_model() { m_imp->init_model(); }

    bool theory_array_bapa::should_research(expr_ref_vector & unsat_core) { return m_imp->should_research(unsat_core); }

    void theory_array_bapa::add_theory_assumptions(expr_ref_vector & assumptions) { m_imp->add_theory_assumptions(assumptions); }

}
