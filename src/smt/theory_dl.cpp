/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_dl.h

Abstract:

    Theory for DL constants.
    DL constants are discrete and ordered by the linear order LT.
    Constants have a parameter which indicates the numeric value that ranges
    from 0 up to the size of the domain.
   
    The procedure works by a simple reduction to bit-vectors. We enforce an injection into bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2011-1-10

Revision History:

--*/

#include "ast/dl_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "model/value_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_bv.h"
#include "smt/smt_context.h"

// Basic approach: reduce theory to bit-vectors:
//
// rep(c(n)) = n
// LT(x,y) <=> rep(x) < rep(y)
// val(rep(x)) = x
// 0 <= rep(x) <= max_value
// 


namespace smt {


    class dl_factory : public simple_factory<unsigned> {
        datalog::dl_decl_util& m_util;
    public:
        dl_factory(datalog::dl_decl_util& u, proto_model& m):
            simple_factory<unsigned>(u.get_manager(), u.get_family_id()),
            m_util(u)
        {}

        app * mk_value_core(unsigned const & val, sort * s) override {
            return m_util.mk_numeral(val, s);
        }
    };

    class theory_dl : public theory {
        datalog::dl_decl_util   m_util;
        bv_util        m_bv;
        ast_ref_vector m_trail;
        obj_map<sort,func_decl*> m_reps;
        obj_map<sort,func_decl*> m_vals;

        ast_manager& m() { return get_manager(); }
        datalog::dl_decl_util& u() { return m_util; }
        bv_util& b() { return m_bv; }

        class dl_value_proc : public smt::model_value_proc {
            theory_dl&                  m_th;
            smt::enode*                 m_node;
        public:
            
            dl_value_proc(theory_dl& th, smt::enode* n) : m_th(th), m_node(n) {}
            
            void get_dependencies(buffer<smt::model_value_dependency> & result) override {}
            
            app * mk_value(smt::model_generator & mg, expr_ref_vector const & ) override {
                smt::context& ctx = m_th.get_context();
                app* result = nullptr;
                expr* n = m_node->get_owner();
                sort* s = m_th.m().get_sort(n);
                func_decl* r, *v;
                m_th.get_rep(s, r, v);
                app_ref rep_of(m_th.m());
                rep_of = m_th.m().mk_app(r, m_node->get_owner());
                theory_id bv_id = m_th.m().mk_family_id("bv");
                theory_bv* th_bv = dynamic_cast<theory_bv*>(ctx.get_theory(bv_id));
                SASSERT(th_bv);
                rational val;
                if (ctx.e_internalized(rep_of) && th_bv && 
                    th_bv->get_fixed_value(rep_of.get(), val)) {
                    result = m_th.u().mk_numeral(val.get_int64(), s);
                }
                else {
                    result = m_th.u().mk_numeral(0, s);
                }
                TRACE("theory_dl", tout << mk_pp(result, m_th.m()) << "\n";);
                return result;
            }        
        };
        
    public:
        theory_dl(ast_manager& m):
            theory(m.mk_family_id("datalog_relation")),
            m_util(m),
            m_bv(m),
            m_trail(m)
        {
        }


        char const * get_name() const override { return "datalog"; }

        bool internalize_atom(app * atom, bool gate_ctx) override {
            TRACE("theory_dl", tout << mk_pp(atom, m()) << "\n";);
            context& ctx = get_context();
            if (ctx.b_internalized(atom)) {
                return true;
            }
            switch(atom->get_decl_kind()) {
            case datalog::OP_DL_LT: {
                app* a = to_app(atom->get_arg(0));
                app* b = to_app(atom->get_arg(1));
                ctx.internalize(a, false);
                ctx.internalize(b, false);
                literal l(ctx.mk_bool_var(atom));
                ctx.set_var_theory(l.var(), get_id());                
                mk_lt(a,b);
                return true;
            }
            default:
                break;
            }
            return false;
        }

        bool internalize_term(app * term) override {
            TRACE("theory_dl", tout << mk_pp(term, m()) << "\n";);
            if (u().is_finite_sort(term)) {
                return mk_rep(term);
            }
            else {
                return false;
            }
        }

        void new_eq_eh(theory_var v1, theory_var v2) override {
            
        }

        void new_diseq_eh(theory_var v1, theory_var v2) override {

        }

        theory * mk_fresh(context * new_ctx) override {
            return alloc(theory_dl, new_ctx->get_manager());
        }

        void init_model(smt::model_generator & m) override {
            m.register_factory(alloc(dl_factory, m_util, m.get_model()));
        }
        
        smt::model_value_proc * mk_value(smt::enode * n, smt::model_generator&) override {
            return alloc(dl_value_proc, *this, n);
        }

        void apply_sort_cnstr(enode * n, sort * s) override {
            app* term = n->get_owner();
            if (u().is_finite_sort(term)) {
                mk_rep(term);
            }
        }

        
        void relevant_eh(app * n) override {
            if (u().is_finite_sort(n)) {
                sort* s = m().get_sort(n);
                func_decl* r, *v;
                get_rep(s, r, v);
                
                if (n->get_decl() != v) {
                    expr* rep = m().mk_app(r, n);
                    uint64_t vl;
                    if (u().is_numeral_ext(n, vl)) {
                        assert_cnstr(m().mk_eq(rep, mk_bv_constant(vl, s)));
                    }
                    else {
                        assert_cnstr(m().mk_eq(m().mk_app(v,rep), n));
                        assert_cnstr(b().mk_ule(rep, max_value(s)));
                    }
                }
            }
        }

        void display(std::ostream & out) const override {
        }


    private:

        void get_rep(sort* s, func_decl*& r, func_decl*& v) {
            if(!m_reps.find(s, r) || !m_vals.find(s,v)) {
                SASSERT(!m_reps.contains(s));
                sort* bv = b().mk_sort(64);
                r = m().mk_func_decl(m_util.get_family_id(), datalog::OP_DL_REP, 0, nullptr, 1, &s, bv);
                v = m().mk_func_decl(m_util.get_family_id(), datalog::OP_DL_ABS, 0, nullptr, 1, &bv, s);
                m_reps.insert(s, r);
                m_vals.insert(s, v);
                add_trail(r);
                add_trail(v);
                get_context().push_trail(insert_obj_map<context,sort,func_decl*>(m_reps, s));
                get_context().push_trail(insert_obj_map<context,sort,func_decl*>(m_vals, s));
            }
        }

        bool mk_rep(app* n) {
            context & ctx     = get_context();
            unsigned num_args = n->get_num_args();
            enode * e = nullptr;
            for (unsigned i = 0; i < num_args; i++) {
                ctx.internalize(n->get_arg(i), false);
            }
            if (ctx.e_internalized(n)) {
                e = ctx.get_enode(n);
            }
            else {
                e = ctx.mk_enode(n, false, false, true);
            }
            if (is_attached_to_var(e)) {
                return false;
            }
            TRACE("theory_dl", tout << mk_pp(n, m()) << "\n";);
            theory_var var = mk_var(e);
            ctx.attach_th_var(e, this, var);
            return true;
        }

        app* mk_bv_constant(uint64_t val, sort* s) {
            return b().mk_numeral(rational(val, rational::ui64()), 64);
        }

        app* max_value(sort* s) {
            uint64_t sz;
            VERIFY(u().try_get_size(s, sz));
            SASSERT(sz > 0);
            return mk_bv_constant(sz-1, s);
        }

        void mk_lt(app* x, app* y) {
            sort* s = m().get_sort(x);
            func_decl* r, *v;
            get_rep(s, r, v);
            app_ref lt(m()), le(m());
            lt = u().mk_lt(x,y);
            le = b().mk_ule(m().mk_app(r,y),m().mk_app(r,x)); 
            context& ctx = get_context();
            if (m().has_trace_stream()) {
                app_ref body(m());
                body = m().mk_eq(lt, le);
                log_axiom_instantiation(body);
            }
            ctx.internalize(lt, false);
            ctx.internalize(le, false);
            literal lit1(ctx.get_literal(lt));
            literal lit2(ctx.get_literal(le));
            ctx.mark_as_relevant(lit1);
            ctx.mark_as_relevant(lit2);
            literal lits1[2] = { lit1, lit2 };
            literal lits2[2] = { ~lit1, ~lit2 };
            ctx.mk_th_axiom(get_id(), 2, lits1);
            ctx.mk_th_axiom(get_id(), 2, lits2);
            if (m().has_trace_stream()) m().trace_stream() << "[end-of-instance]\n";
        }

        void assert_cnstr(expr* e) {
            TRACE("theory_dl", tout << mk_pp(e, m()) << "\n";);
            context& ctx = get_context();
            if (m().has_trace_stream()) log_axiom_instantiation(e);
            ctx.internalize(e, false);
            if (m().has_trace_stream()) m().trace_stream() << "[end-of-instance]\n";
            literal lit(ctx.get_literal(e));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        }

        void add_trail(ast* a) {
            m_trail.push_back(a);
            get_context().push_trail(push_back_vector<context,ast_ref_vector>(m_trail));
        }
                
    };

    theory* mk_theory_dl(ast_manager& m) { return alloc(theory_dl, m); }

};
