/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_datalog.cpp

Abstract:
    Datalog API

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include "api/api_datalog.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ast_pp.h"
#include "api/api_ast_vector.h"
#include "api/api_log_macros.h"
#include "api/api_stats.h"
#include "muz/fp/datalog_parser.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "muz/fp/dl_cmds.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/rel/dl_external_relation.h"
#include "ast/dl_decl_plugin.h"
#include "muz/rel/rel_context.h"

namespace api {

    class fixedpoint_context : public datalog::external_relation_context {
        void *                       m_state;
        reduce_app_callback_fptr     m_reduce_app;
        reduce_assign_callback_fptr  m_reduce_assign;
        datalog::register_engine     m_register_engine;
        datalog::context             m_context;    
        ast_ref_vector               m_trail;        
    public:
        fixedpoint_context(ast_manager& m, smt_params& p): 
            m_state(nullptr),
            m_reduce_app(nullptr),
            m_reduce_assign(nullptr),
            m_context(m, m_register_engine, p),
            m_trail(m) {}

        ~fixedpoint_context() override {}
        family_id get_family_id() const override { return const_cast<datalog::context&>(m_context).get_decl_util().get_family_id(); }
        void set_state(void* state) {
            SASSERT(!m_state);
            m_state = state;
            symbol name("datalog_relation");
            ast_manager& m = m_context.get_manager();
            if (!m.has_plugin(name)) {
                m.register_plugin(name, alloc(datalog::dl_decl_plugin));
            }        
            datalog::rel_context_base* rel = m_context.get_rel_context();
            if (rel) {
                datalog::relation_manager& r = rel->get_rmanager();
                r.register_plugin(alloc(datalog::external_relation_plugin, *this, r));
            }
        }
        void set_reduce_app(reduce_app_callback_fptr f) { 
            m_reduce_app = f; 
        }
        void set_reduce_assign(reduce_assign_callback_fptr f) { 
            m_reduce_assign = f; 
        }
        void reduce(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result) override {
            expr* r = nullptr;
            if (m_reduce_app) {
                m_reduce_app(m_state, f, num_args, args, &r);
                result = r;
                m_trail.push_back(f);
                for (unsigned i = 0; i < num_args; ++i) {
                    m_trail.push_back(args[i]);
                }
                m_trail.push_back(r);
            }
            // allow fallthrough.
            if (r == nullptr) {
                ast_manager& m = m_context.get_manager();
                result = m.mk_app(f, num_args, args);
            }
        }
        void reduce_assign(func_decl* f, unsigned num_args, expr * const* args, unsigned num_out, expr* const* outs) override {
            if (m_reduce_assign) {
                m_trail.push_back(f);
                for (unsigned i = 0; i < num_args; ++i) {
                    m_trail.push_back(args[i]);
                }
                m_reduce_assign(m_state, f, num_args, args, num_out, outs);
            }
        }
        datalog::context& ctx() { return m_context; }
        void add_rule(expr* rule, symbol const& name) {
            m_context.add_rule(rule, name);
        }
        void update_rule(expr* rule, symbol const& name) {
            m_context.update_rule(rule, name);
        }
        void add_table_fact(func_decl* r, unsigned num_args, unsigned args[]) {
            m_context.add_table_fact(r, num_args, args);
        }
        std::string get_last_status() {
            datalog::execution_result status = m_context.get_status();
            switch(status) {
            case datalog::INPUT_ERROR:
                return "input error";        
            case datalog::OK:
                return "ok";
            case datalog::TIMEOUT:            
                return "timeout";
            case datalog::APPROX:
                return "approximated";
            default:
                UNREACHABLE();
                return "unknown";
            }
        }
        std::string to_string(unsigned num_queries, expr* const* queries) {
            std::stringstream str;
            m_context.display_smt2(num_queries, queries, str);
            return str.str();
        }
        unsigned get_num_levels(func_decl* pred) {
            return m_context.get_num_levels(pred);
        }
        expr_ref get_cover_delta(int level, func_decl* pred) {
            return m_context.get_cover_delta(level, pred);
        }
        void add_cover(int level, func_decl* pred, expr* predicate) {
            m_context.add_cover(level, pred, predicate);
        }
        void collect_param_descrs(param_descrs & p) { m_context.collect_params(p); }
        void updt_params(params_ref const& p) { m_context.updt_params(p); }
    };         
};

extern "C" {
    
    ////////////////////////////////////
    // Datalog utilities
    // 


    unsigned Z3_API Z3_get_relation_arity(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_get_relation_arity(c, s);
        RESET_ERROR_CODE();  
        sort * r = to_sort(s);
        if (Z3_get_sort_kind(c, s) != Z3_RELATION_SORT) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "sort should be a relation");
            return 0;
        }
        return r->get_num_parameters();
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_get_relation_column(Z3_context c, Z3_sort s, unsigned col) {
        Z3_TRY;
        LOG_Z3_get_relation_column(c, s, col);
        RESET_ERROR_CODE();  
        sort * r = to_sort(s);
        if (Z3_get_sort_kind(c, s) != Z3_RELATION_SORT) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "sort should be a relation");
            RETURN_Z3(nullptr);
        }
        if (col >= r->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        parameter const& p = r->get_parameter(col);
        if (!p.is_ast() || !is_sort(p.get_ast())) {
            UNREACHABLE();
            warning_msg("Sort parameter expected at %d", col);
            SET_ERROR_CODE(Z3_INTERNAL_FATAL, "sort parameter expected");
            RETURN_Z3(nullptr);
        }
        Z3_sort res = of_sort(to_sort(p.get_ast()));
        RETURN_Z3(res);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_mk_finite_domain_sort(Z3_context c, Z3_symbol name, uint64_t size) {
        Z3_TRY;
        LOG_Z3_mk_finite_domain_sort(c, name, size);
        RESET_ERROR_CODE();
        sort* s = mk_c(c)->datalog_util().mk_sort(to_symbol(name), size);
        mk_c(c)->save_ast_trail(s);
        RETURN_Z3(of_sort(s));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_bool Z3_API Z3_get_finite_domain_sort_size(Z3_context c, Z3_sort s, uint64_t * out) {
        Z3_TRY;
        if (out) {
            *out = 0;
        }
        if (Z3_get_sort_kind(c, s) != Z3_FINITE_DOMAIN_SORT) {
            return Z3_FALSE;
        }
        if (!out) {
            return Z3_FALSE;
        }
        // must start loggging here, since function uses Z3_get_sort_kind above
        LOG_Z3_get_finite_domain_sort_size(c, s, out);
        RESET_ERROR_CODE();  
        VERIFY(mk_c(c)->datalog_util().try_get_size(to_sort(s), *out));
        return Z3_TRUE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_fixedpoint Z3_API Z3_mk_fixedpoint(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_fixedpoint(c);
        RESET_ERROR_CODE();
        Z3_fixedpoint_ref * d = alloc(Z3_fixedpoint_ref, *mk_c(c));
        d->m_datalog = alloc(api::fixedpoint_context, mk_c(c)->m(), mk_c(c)->fparams());
        mk_c(c)->save_object(d);
        Z3_fixedpoint r = of_datalog(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_fixedpoint_inc_ref(Z3_context c, Z3_fixedpoint s) {
        Z3_TRY;
        LOG_Z3_fixedpoint_inc_ref(c, s);
        RESET_ERROR_CODE();
        to_fixedpoint(s)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_dec_ref(Z3_context c, Z3_fixedpoint s) {
        Z3_TRY;
        LOG_Z3_fixedpoint_dec_ref(c, s);
        RESET_ERROR_CODE();
        to_fixedpoint(s)->dec_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_assert(Z3_context c, Z3_fixedpoint d, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_fixedpoint_assert(c, d, a);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_fixedpoint_ref(d)->ctx().assert_expr(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_add_rule(Z3_context c, Z3_fixedpoint d, Z3_ast a, Z3_symbol name) {
        Z3_TRY;
        LOG_Z3_fixedpoint_add_rule(c, d, a, name);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_fixedpoint_ref(d)->add_rule(to_expr(a), to_symbol(name));
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_add_fact(Z3_context c, Z3_fixedpoint d, 
                                       Z3_func_decl r, unsigned num_args, unsigned args[]) {
        Z3_TRY;
        LOG_Z3_fixedpoint_add_fact(c, d, r, num_args, args);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->add_table_fact(to_func_decl(r), num_args, args);
        Z3_CATCH;
    }

    Z3_lbool Z3_API Z3_fixedpoint_query(Z3_context c,Z3_fixedpoint d, Z3_ast q) {
        Z3_TRY;
        LOG_Z3_fixedpoint_query(c, d, q);
        RESET_ERROR_CODE();
        lbool r = l_undef;
        unsigned timeout = to_fixedpoint(d)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit  = to_fixedpoint(d)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        {
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            cancel_eh<reslimit> eh(mk_c(c)->m().limit());
            api::context::set_interruptable si(*(mk_c(c)), eh);        
            scoped_timer timer(timeout, &eh);
            try {
                r = to_fixedpoint_ref(d)->ctx().query(to_expr(q));
            }
            catch (z3_exception& ex) {
                r = l_undef;
                mk_c(c)->handle_exception(ex);                
            }
            to_fixedpoint_ref(d)->ctx().cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_lbool Z3_API Z3_fixedpoint_query_relations(
        Z3_context c,Z3_fixedpoint d, 
        unsigned num_relations, Z3_func_decl const relations[]) {
        Z3_TRY;
        LOG_Z3_fixedpoint_query_relations(c, d, num_relations, relations);
        RESET_ERROR_CODE();
        lbool r = l_undef;
        unsigned timeout = to_fixedpoint(d)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_timer timer(timeout, &eh);
            try {
                r = to_fixedpoint_ref(d)->ctx().rel_query(num_relations, to_func_decls(relations));
            }
            catch (z3_exception& ex) {
                mk_c(c)->handle_exception(ex);
                r = l_undef;
            }
            to_fixedpoint_ref(d)->ctx().cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_ast Z3_API Z3_fixedpoint_get_answer(Z3_context c, Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_answer(c, d);
        RESET_ERROR_CODE();
        expr* e = to_fixedpoint_ref(d)->ctx().get_answer_as_formula();
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_fixedpoint_get_reason_unknown(Z3_context c,Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_reason_unknown(c, d);
        RESET_ERROR_CODE();
        return mk_c(c)->mk_external_string(to_fixedpoint_ref(d)->get_last_status());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_fixedpoint_to_string(
        Z3_context c, 
        Z3_fixedpoint d,
        unsigned num_queries,
        Z3_ast _queries[]) {
        Z3_TRY;
        expr*const* queries = to_exprs(_queries);        
        LOG_Z3_fixedpoint_to_string(c, d, num_queries, _queries);
        RESET_ERROR_CODE();
        return mk_c(c)->mk_external_string(to_fixedpoint_ref(d)->to_string(num_queries, queries));
        Z3_CATCH_RETURN("");
    }

    Z3_ast_vector Z3_fixedpoint_from_stream(
        Z3_context    c,
        Z3_fixedpoint d,
        std::istream& s) {
        ast_manager& m = mk_c(c)->m();
        dl_collected_cmds coll(m);
        cmd_context ctx(false, &m);
        install_dl_collect_cmds(coll, ctx);
        ctx.set_ignore_check(true);
        if (!parse_smt2_commands(ctx, s)) {
            SET_ERROR_CODE(Z3_PARSER_ERROR, nullptr);
            return nullptr;
        }

        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        for (unsigned i = 0; i < coll.m_queries.size(); ++i) {
            v->m_ast_vector.push_back(coll.m_queries[i].get());
        }
        for (unsigned i = 0; i < coll.m_rels.size(); ++i) {
            to_fixedpoint_ref(d)->ctx().register_predicate(coll.m_rels[i].get(), true);
        }
        for (unsigned i = 0; i < coll.m_rules.size(); ++i) {
            to_fixedpoint_ref(d)->add_rule(coll.m_rules[i].get(), coll.m_names[i]);
        }
        for (expr * e : ctx.assertions()) {
            to_fixedpoint_ref(d)->ctx().assert_expr(e);
        }

        return of_ast_vector(v);
    }

    Z3_ast_vector Z3_API Z3_fixedpoint_from_string(
        Z3_context    c,
        Z3_fixedpoint d,
        Z3_string     s) {
        Z3_TRY;
        LOG_Z3_fixedpoint_from_string(c, d, s);
        std::string str(s);
        std::istringstream is(str);
        RETURN_Z3(Z3_fixedpoint_from_stream(c, d, is));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_fixedpoint_from_file(
        Z3_context    c,
        Z3_fixedpoint d,
        Z3_string     s) {
        Z3_TRY;
        LOG_Z3_fixedpoint_from_file(c, d, s);
        std::ifstream is(s);
        if (!is) {
            SET_ERROR_CODE(Z3_PARSER_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(Z3_fixedpoint_from_stream(c, d, is));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_stats Z3_API Z3_fixedpoint_get_statistics(Z3_context c,Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_statistics(c, d);
        RESET_ERROR_CODE();
        Z3_stats_ref * st = alloc(Z3_stats_ref, (*mk_c(c)));
        to_fixedpoint_ref(d)->ctx().collect_statistics(st->m_stats);
        mk_c(c)->save_object(st);
        Z3_stats r = of_stats(st);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    void Z3_API Z3_fixedpoint_register_relation(Z3_context c,Z3_fixedpoint d, Z3_func_decl f) {
        Z3_TRY;
        LOG_Z3_fixedpoint_register_relation(c, d, f);
        to_fixedpoint_ref(d)->ctx().register_predicate(to_func_decl(f), true);
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_set_predicate_representation(
        Z3_context c,
        Z3_fixedpoint d, 
        Z3_func_decl f, 
        unsigned num_relations, 
        Z3_symbol const relation_kinds[]) {
        Z3_TRY;
        LOG_Z3_fixedpoint_set_predicate_representation(c, d, f, num_relations, relation_kinds);
        svector<symbol> kinds;
        for (unsigned i = 0; i < num_relations; ++i) {
            kinds.push_back(to_symbol(relation_kinds[i]));
        }
        to_fixedpoint_ref(d)->ctx().set_predicate_representation(to_func_decl(f), num_relations, kinds.c_ptr());
        Z3_CATCH;
    }


    Z3_ast_vector Z3_API Z3_fixedpoint_get_rules(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_rules(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        expr_ref_vector rules(m), queries(m);
        svector<symbol> names;
        
        to_fixedpoint_ref(d)->ctx().get_rules_as_formulas(rules, queries, names);
        for (unsigned i = 0; i < rules.size(); ++i) {
            v->m_ast_vector.push_back(rules[i].get());
        }
        for (unsigned i = 0; i < queries.size(); ++i) {
            v->m_ast_vector.push_back(m.mk_not(queries[i].get()));
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_fixedpoint_get_assertions(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_assertions(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        unsigned num_asserts = to_fixedpoint_ref(d)->ctx().get_num_assertions();
        for (unsigned i = 0; i < num_asserts; ++i) {
            v->m_ast_vector.push_back(to_fixedpoint_ref(d)->ctx().get_assertion(i));
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }
    
    void Z3_API Z3_fixedpoint_set_reduce_assign_callback(
        Z3_context c, Z3_fixedpoint d, Z3_fixedpoint_reduce_assign_callback_fptr f) {
        Z3_TRY;
        // no logging
        to_fixedpoint_ref(d)->set_reduce_assign((reduce_assign_callback_fptr)f);
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_set_reduce_app_callback(
        Z3_context c, Z3_fixedpoint d, Z3_fixedpoint_reduce_app_callback_fptr f) {
        Z3_TRY;
        // no logging
        to_fixedpoint_ref(d)->set_reduce_app((reduce_app_callback_fptr)f);       
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_init(Z3_context c,Z3_fixedpoint d, void* state) {
        Z3_TRY;
        // not logged
        to_fixedpoint_ref(d)->set_state(state);
        Z3_CATCH;
    }


    void Z3_API Z3_fixedpoint_update_rule(Z3_context c, Z3_fixedpoint d, Z3_ast a, Z3_symbol name) {
        Z3_TRY;
        LOG_Z3_fixedpoint_update_rule(c, d, a, name);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_fixedpoint_ref(d)->update_rule(to_expr(a), to_symbol(name));
        Z3_CATCH;
    }

    unsigned Z3_API Z3_fixedpoint_get_num_levels(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_num_levels(c, d, pred);
        RESET_ERROR_CODE();
        return to_fixedpoint_ref(d)->get_num_levels(to_func_decl(pred));
        Z3_CATCH_RETURN(0)
    }

    Z3_ast Z3_API Z3_fixedpoint_get_cover_delta(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_cover_delta(c, d, level, pred);
        RESET_ERROR_CODE();
        expr_ref r = to_fixedpoint_ref(d)->get_cover_delta(level, to_func_decl(pred));
        mk_c(c)->save_ast_trail(r);        
        RETURN_Z3(of_expr(r.get()));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_fixedpoint_add_cover(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred, Z3_ast property) {
        Z3_TRY;
        LOG_Z3_fixedpoint_add_cover(c, d, level, pred, property);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->add_cover(level, to_func_decl(pred), to_expr(property));        
        Z3_CATCH;
    }

    Z3_string Z3_API Z3_fixedpoint_get_help(Z3_context c, Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_help(c, d);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        to_fixedpoint_ref(d)->collect_param_descrs(descrs);
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_param_descrs Z3_API Z3_fixedpoint_get_param_descrs(Z3_context c, Z3_fixedpoint f) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_param_descrs(c, f);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref, *mk_c(c));
        mk_c(c)->save_object(d);
        to_fixedpoint_ref(f)->collect_param_descrs(d->m_descrs);
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    void Z3_API Z3_fixedpoint_set_params(Z3_context c, Z3_fixedpoint d, Z3_params p) {
        Z3_TRY;
        LOG_Z3_fixedpoint_set_params(c, d, p);
        RESET_ERROR_CODE();
        param_descrs descrs;
        to_fixedpoint_ref(d)->collect_param_descrs(descrs);
        to_params(p)->m_params.validate(descrs);
        to_fixedpoint_ref(d)->updt_params(to_param_ref(p));
        to_fixedpoint(d)->m_params = to_param_ref(p);
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_push(Z3_context c,Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_push(c, d);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->ctx().push();
        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_pop(Z3_context c,Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_pop(c, d);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->ctx().pop();
        Z3_CATCH;

    }

    void Z3_API Z3_fixedpoint_add_callback(Z3_context c, Z3_fixedpoint d,
                                            void *state,
                                            Z3_fixedpoint_new_lemma_eh new_lemma_eh,
                                            Z3_fixedpoint_predecessor_eh predecessor_eh,
                                            Z3_fixedpoint_unfold_eh unfold_eh){
        Z3_TRY;
            // not logged
            to_fixedpoint_ref(d)->ctx().add_callback(state,
                                                     reinterpret_cast<datalog::t_new_lemma_eh>(new_lemma_eh),
                                                     reinterpret_cast<datalog::t_predecessor_eh>(predecessor_eh),
                                                     reinterpret_cast<datalog::t_unfold_eh>(unfold_eh));

        Z3_CATCH;
    }

    void Z3_API Z3_fixedpoint_add_constraint (Z3_context c, Z3_fixedpoint d, Z3_ast e, unsigned lvl){
        to_fixedpoint_ref(d)->ctx().add_constraint(to_expr(e), lvl);
    }

    Z3_lbool Z3_API Z3_fixedpoint_query_from_lvl (Z3_context c, Z3_fixedpoint d, Z3_ast q, unsigned lvl) {
        Z3_TRY;
        LOG_Z3_fixedpoint_query_from_lvl (c, d, q, lvl);
        RESET_ERROR_CODE();
        lbool r = l_undef;
        unsigned timeout = to_fixedpoint(d)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit  = to_fixedpoint(d)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        {
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            cancel_eh<reslimit> eh(mk_c(c)->m().limit());
            api::context::set_interruptable si(*(mk_c(c)), eh);        
            scoped_timer timer(timeout, &eh);
            try {
                r = to_fixedpoint_ref(d)->ctx().query_from_lvl (to_expr(q), lvl);
            }
            catch (z3_exception& ex) {
                mk_c(c)->handle_exception(ex);
                r = l_undef;
            }
            to_fixedpoint_ref(d)->ctx().cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_ast Z3_API Z3_fixedpoint_get_ground_sat_answer(Z3_context c, Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_ground_sat_answer(c, d);
        RESET_ERROR_CODE();
        expr* e = to_fixedpoint_ref(d)->ctx().get_ground_sat_answer();
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_fixedpoint_get_rules_along_trace(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_rules_along_trace(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        expr_ref_vector rules(m);
        svector<symbol> names;
        
        to_fixedpoint_ref(d)->ctx().get_rules_along_trace_as_formulas(rules, names);
        for (unsigned i = 0; i < rules.size(); ++i) {
            v->m_ast_vector.push_back(rules[i].get());
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_symbol Z3_API Z3_fixedpoint_get_rule_names_along_trace(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_rule_names_along_trace(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        expr_ref_vector rules(m);
        svector<symbol> names;
        std::stringstream ss;
        
        to_fixedpoint_ref(d)->ctx().get_rules_along_trace_as_formulas(rules, names);
        for (unsigned i = 0; i < names.size(); ++i) {
            ss << ";" << names[i].str();
        }
        RETURN_Z3(of_symbol(symbol(ss.str().substr(1).c_str())));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_fixedpoint_add_invariant(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred, Z3_ast property) {
        Z3_TRY;
        LOG_Z3_fixedpoint_add_invariant(c, d, pred, property);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->ctx ().add_invariant(to_func_decl(pred), to_expr(property));        
        Z3_CATCH;
    }

    Z3_ast Z3_API Z3_fixedpoint_get_reachable(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_reachable(c, d, pred);
        RESET_ERROR_CODE();
        expr_ref r = to_fixedpoint_ref(d)->ctx().get_reachable(to_func_decl(pred));
        mk_c(c)->save_ast_trail(r);        
        RETURN_Z3(of_expr(r.get()));
        Z3_CATCH_RETURN(nullptr);
    }



};
