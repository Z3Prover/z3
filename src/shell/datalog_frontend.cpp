/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datalog_frontend.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/

#include<iostream>
#include<time.h>
#include<signal.h>
#include"stopwatch.h"
#ifdef _CYGWIN
#undef min
#undef max
#endif
#include"front_end_params.h"
#include"datalog_parser.h"
#include"arith_decl_plugin.h"
#include"dl_compiler.h"
#include"dl_context.h"
#include"dl_mk_filter_rules.h"
#include"dl_finite_product_relation.h"
#include"datalog_frontend.h"
#include"timeout.h"

static stopwatch g_overall_time;
static stopwatch g_piece_timer;
static unsigned t_parsing = 0;

static datalog::context * g_ctx = 0;
static datalog::rule_set * g_orig_rules;
static datalog::instruction_block * g_code;
static datalog::execution_context * g_ectx;
static front_end_params * g_params;

datalog_params::datalog_params():
    m_default_table("sparse"),
    m_default_table_checked(false)
{}

void datalog_params::register_params(ini_params& p) {
    p.register_symbol_param("DEFAULT_TABLE", m_default_table, "Datalog engine: default table (sparse)");
    p.register_bool_param("DEFAULT_TABLE_CHECKED", m_default_table_checked, "Wrap default table with a sanity checker");
}

static void display_statistics(
    std::ostream& out,
    datalog::context& ctx,
    datalog::rule_set& orig_rules,
    datalog::instruction_block& code,
    datalog::execution_context& ex_ctx,
    front_end_params& params,
    bool verbose
    ) 
{
    g_piece_timer.stop();
    unsigned t_other = static_cast<int>(g_piece_timer.get_seconds()*1000);
    g_overall_time.stop();

    code.process_all_costs();
    {
        params_ref p(ctx.get_params());
        p.set_bool(":output-profile", true);
        p.set_uint(":profile-milliseconds-threshold", 100);
        ctx.updt_params(p);

        out << "--------------\n";
        out << "original rules\n";
        orig_rules.display(out);

        out << "---------------\n";
        out << "generated rules\n";
        ctx.display_rules(out);

        out << "--------------\n";
        out << "instructions  \n";
        code.display(ctx, out);

        out << "--------------\n";
        out << "big relations \n";
        ex_ctx.report_big_relations(1000, out);
    }
    out << "--------------\n";
    out << "relation sizes\n";
    ctx.get_rmanager().display_relation_sizes(out);

    if (verbose) {
        out << "--------------\n";
        out << "rules\n";
        ctx.display_rules(out);
    }

    out << "Time: " << static_cast<int>(g_overall_time.get_seconds()*1000) << "ms\n";
    out << "Parsing: " << t_parsing << "ms, other: " << t_other << "ms\n";
}


static void display_statistics() {
    if (g_ctx) {
        display_statistics(std::cout, *g_ctx, *g_orig_rules, *g_code, *g_ectx, *g_params, true);
    }
}

static void on_timeout() {
    display_statistics();
    exit(0);
}

static void on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}


unsigned read_datalog(char const * file, datalog_params const& dl_params, front_end_params & front_end_params) {
    IF_VERBOSE(1, verbose_stream() << "Z3 Datalog Engine\n";);
    ast_manager m;
    g_overall_time.start();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    params_ref params;
    params.set_sym(":engine", symbol("datalog"));
    params.set_sym(":default-table", dl_params.m_default_table);
    params.set_bool(":default-table-checked", dl_params.m_default_table_checked);

    datalog::context ctx(m, front_end_params, params);
    size_t watermark = front_end_params.m_memory_high_watermark;
    if (watermark == 0) {
        memory::set_high_watermark(static_cast<size_t>(UINT_MAX));
    }
    datalog::relation_manager & rmgr = ctx.get_rmanager();
    datalog::relation_plugin & inner_plg = *rmgr.get_relation_plugin(symbol("tr_hashtable"));
    SASSERT(&inner_plg);
    rmgr.register_plugin(alloc(datalog::finite_product_relation_plugin, inner_plg, rmgr));
    
    g_piece_timer.reset();
    g_piece_timer.start();

    bool wpa_benchmark = datalog::is_directory(std::string(file));
    if (wpa_benchmark) {
        scoped_ptr<datalog::wpa_parser> parser = datalog::wpa_parser::create(ctx, m);
        if (!parser->parse_directory(file)) {
            std::cerr << "ERROR: failed to parse file\n";
            return 1;
        }
    }
    else {
        scoped_ptr<datalog::parser> parser = datalog::parser::create(ctx, m);
        if (!parser->parse_file(file)) {
            std::cerr << "ERROR: failed to parse file\n";
            return 1;
        }
    }

    g_piece_timer.stop();
    t_parsing = static_cast<int>(g_piece_timer.get_seconds()*1000);
    IF_VERBOSE(1, verbose_stream() << "parsing finished\n";);
    IF_VERBOSE(1, verbose_stream() << "running saturation...\n";);
    g_piece_timer.reset();
    g_piece_timer.start();
    //all rules were added
    ctx.close();

    TRACE("dl_compiler", ctx.display(tout););

    datalog::rule_set original_rules(ctx.get_rules());
    datalog::decl_set original_predicates;
    ctx.collect_predicates(original_predicates);

    datalog::instruction_block rules_code;
    datalog::instruction_block termination_code;
    datalog::execution_context ex_ctx(ctx);

    IF_VERBOSE(10, original_rules.display_deps(verbose_stream()););

    g_ctx = &ctx;
    g_orig_rules = &original_rules;
    g_code = &rules_code;
    g_ectx = &ex_ctx;
    g_params = &front_end_params;

    try {    
        g_piece_timer.reset();
        g_piece_timer.start();
        
        bool early_termination;
        unsigned timeout = ctx.initial_restart_timeout(); 
        if(timeout == 0) {
            timeout = UINT_MAX;
        }
        do {
            model_converter_ref mc; // ignored
            proof_converter_ref pc; // ignored
            ctx.transform_rules(mc, pc);
            
            datalog::compiler::compile(ctx, ctx.get_rules(), rules_code, termination_code);
            
            TRACE("dl_compiler", rules_code.display(ctx, tout););
            
            rules_code.make_annotations(ex_ctx);
            
            ex_ctx.set_timelimit(timeout);
            SASSERT(!ex_ctx.should_terminate());
            
            early_termination = !rules_code.perform(ex_ctx);
            if(early_termination) {
                IF_VERBOSE(10, ex_ctx.report_big_relations(1000, verbose_stream()););
                if (memory::above_high_watermark()) {
                    throw out_of_memory_error();
                }
            }
            ex_ctx.reset_timelimit();
            TRUSTME( termination_code.perform(ex_ctx) );
            ctx.saturation_was_run();
            
            if (early_termination) {
                IF_VERBOSE(1, verbose_stream() << "restarting saturation\n";);
                
                uint64 new_timeout = static_cast<uint64>(timeout)*ctx.initial_restart_timeout(); 
                if(new_timeout>UINT_MAX) {
                    timeout=UINT_MAX;
                }
                else {
                    timeout=static_cast<unsigned>(new_timeout);
                }
                
                rules_code.process_all_costs();
                rules_code.reset();
                termination_code.reset();
                ex_ctx.reset();
                ctx.reopen();
                ctx.restrict_predicates(original_predicates);
                ctx.replace_rules(original_rules);
                ctx.close();
            }
        } while (early_termination);
        

        TRACE("dl_compiler", ctx.display(tout);
              rules_code.display(ctx, tout););
        
        if (ctx.get_params().get_bool(":output-tuples", true)) { 
            ctx.display_output_facts(std::cout);
        }

        display_statistics(
            std::cout,
            ctx,
            original_rules, 
            rules_code,
            ex_ctx,
            front_end_params,
            false);

    }
    catch (out_of_memory_error) {
        std::cout << "\n\nOUT OF MEMORY!\n\n";        
        display_statistics(
            std::cout,
            ctx,
            original_rules, 
            rules_code,
            ex_ctx,
            front_end_params,
            true);
        return ERR_MEMOUT;
    }
    register_on_timeout_proc(0);
    return 0;
}

