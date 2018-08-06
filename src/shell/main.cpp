/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    main.cpp

Abstract:

    Z3 command line tool.

Author:

    Leonardo de Moura (leonardo) 2006-10-10.
    Nikolaj Bjorner   (nbjorner) 

Revision History:

--*/
#include<iostream>
#include "util/memory_manager.h"
#include "util/trace.h"
#include "util/debug.h"
#include "util/util.h"
#include "ast/pp.h"
#include "shell/smtlib_frontend.h"
#include "shell/z3_log_frontend.h"
#include "util/warning.h"
#include "util/version.h"
#include "shell/dimacs_frontend.h"
#include "shell/datalog_frontend.h"
#include "shell/opt_frontend.h"
#include "util/timeout.h"
#include "util/z3_exception.h"
#include "util/error_codes.h"
#include "util/file_path.h"
#include "util/gparams.h"
#include "util/env_params.h"
#include "util/file_path.h"
#include "shell/lp_frontend.h"

typedef enum { IN_UNSPECIFIED, IN_SMTLIB_2, IN_DATALOG, IN_DIMACS, IN_WCNF, IN_OPB, IN_LP, IN_Z3_LOG, IN_MPS } input_kind;

std::string         g_aux_input_file;
char const *        g_input_file          = nullptr;
bool                g_standard_input      = false;
input_kind          g_input_kind          = IN_UNSPECIFIED;
bool                g_display_statistics  = false;
bool                g_display_istatistics = false;

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: z3 -h\n";
    exit(ERR_CMD_LINE);
}

#define STRINGIZE(x) #x
#define STRINGIZE_VALUE_OF(x) STRINGIZE(x)

void display_usage() {
    std::cout << "Z3 [version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER;
    std::cout << " - ";
#ifdef _AMD64_
    std::cout << "64";
#else
    std::cout << "32";
#endif
    std::cout << " bit";
#ifdef Z3GITHASH
    std::cout << " - build hashcode " << STRINGIZE_VALUE_OF(Z3GITHASH);
#endif
    std::cout << "]. (C) Copyright 2006-2016 Microsoft Corp.\n";
    std::cout << "Usage: z3 [options] [-file:]file\n";
    std::cout << "\nInput format:\n";
    std::cout << "  -smt2       use parser for SMT 2 input format.\n";
    std::cout << "  -dl         use parser for Datalog input format.\n";
    std::cout << "  -dimacs     use parser for DIMACS input format.\n";
    std::cout << "  -wcnf       use parser for Weighted CNF DIMACS input format.\n";
    std::cout << "  -opb        use parser for PB optimization input format.\n";
    std::cout << "  -lp         use parser for a modest subset of CPLEX LP input format.\n";
    std::cout << "  -log        use parser for Z3 log input format.\n";
    std::cout << "  -in         read formula from standard input.\n";
    std::cout << "\nMiscellaneous:\n";
    std::cout << "  -h, -?      prints this message.\n";
    std::cout << "  -version    prints version number of Z3.\n";
    std::cout << "  -v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  -nw         disable warning messages.\n";
    std::cout << "  -p          display Z3 global (and module) parameters.\n";
    std::cout << "  -pd         display Z3 global (and module) parameter descriptions.\n";
    std::cout << "  -pm:name    display Z3 module ('name') parameters.\n";
    std::cout << "  -pp:name    display Z3 parameter description, if 'name' is not provided, then all module names are listed.\n";
    std::cout << "  --"      << "          all remaining arguments are assumed to be part of the input file name. This option allows Z3 to read files with strange names such as: -foo.smt2.\n";
    std::cout << "\nResources:\n";
    // timeout and memout are now available on Linux and OSX too.
    std::cout << "  -T:timeout  set the timeout (in seconds).\n";
    std::cout << "  -t:timeout  set the soft timeout (in milli seconds). It only kills the current query.\n";
    std::cout << "  -memory:Megabytes  set a limit for virtual memory consumption.\n";
    // 
    std::cout << "\nOutput:\n";
    std::cout << "  -st         display statistics.\n";
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  -tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  -dbg:tag    enable assertions tagged with <tag>.\n";
#endif
    std::cout << "\nParameter setting:\n";
    std::cout << "Global and module parameters can be set in the command line.\n";
    std::cout << "  param_name=value              for setting global parameters.\n";
    std::cout << "  module_name.param_name=value  for setting module parameters.\n";
    std::cout << "Use 'z3 -p' for the complete list of global and module parameters.\n";
}
   
void parse_cmd_line_args(int argc, char ** argv) {
    int i = 1;
    char * eq_pos = nullptr;
    while (i < argc) {
        char * arg = argv[i];    

        if (arg[0] == '-' && arg[1] == '-' && arg[2] == 0) {
            // Little hack used to read files with strange names such as -foo.smt2
            // z3 -- -foo.smt2
            i++;
            g_aux_input_file = "";
            for (; i < argc; i++) {
                g_aux_input_file += argv[i];
                if (i < argc - 1)
                    g_aux_input_file += " ";
            }
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = g_aux_input_file.c_str();
            }
            break;
        }
        
        if (arg[0] == '-' 
#ifdef _WINDOWS
            || arg[0] == '/'
#endif
            ) {
            char * opt_name = arg + 1;
            // allow names such as --help
            if (*opt_name == '-')
                opt_name++;
            char * opt_arg  = nullptr;
            char * colon    = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon  = 0;
            }
            if (strcmp(opt_name, "h") == 0 || strcmp(opt_name, "?") == 0 || strcmp(opt_name, "help") == 0) {
                display_usage();
                exit(0);
            }
            if (strcmp(opt_name, "version") == 0) {
                std::cout << "Z3 version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER;
                std::cout << " - ";
#ifdef _AMD64_
                std::cout << "64";
#else
                std::cout << "32";
#endif
                std::cout << " bit";
#ifdef Z3GITHASH
                std::cout << " - build hashcode " << STRINGIZE_VALUE_OF(Z3GITHASH);
#endif
                std::cout << "\n";
                exit(0);
            }
            else if (strcmp(opt_name, "smt2") == 0) {
                g_input_kind = IN_SMTLIB_2;
            }
            else if (strcmp(opt_name, "dl") == 0) {
                g_input_kind = IN_DATALOG;
            }
            else if (strcmp(opt_name, "in") == 0) {
                g_standard_input = true;
            }
            else if (strcmp(opt_name, "dimacs") == 0) {
                g_input_kind = IN_DIMACS;
            }
            else if (strcmp(opt_name, "wcnf") == 0) {
                g_input_kind = IN_WCNF;
            }
            else if (strcmp(opt_name, "pbo") == 0) {
                g_input_kind = IN_OPB;
            }
            else if (strcmp(opt_name, "lp") == 0) {
                g_input_kind = IN_LP;
            }
            else if (strcmp(opt_name, "log") == 0) {
                g_input_kind = IN_Z3_LOG;
            }
            else if (strcmp(opt_name, "st") == 0) {
                g_display_statistics = true; 
                gparams::set("stats", "true");
            }
            else if (strcmp(opt_name, "ist") == 0) {
                g_display_istatistics = true; 
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (-v:level) is missing.");
                long lvl = strtol(opt_arg, nullptr, 10);
                set_verbosity_level(lvl);
            }
            else if (strcmp(opt_name, "file") == 0) {
                g_input_file = opt_arg;
            }
            else if (strcmp(opt_name, "T") == 0) {
                if (!opt_arg)
                    error("option argument (-T:timeout) is missing.");
                long tm = strtol(opt_arg, nullptr, 10);
                set_timeout(tm * 1000);
            }
            else if (strcmp(opt_name, "t") == 0) {
                if (!opt_arg)
                    error("option argument (-t:timeout) is missing.");
                gparams::set("timeout", opt_arg);
            }
            else if (strcmp(opt_name, "nw") == 0) {
                enable_warning_messages(false);
            }
            else if (strcmp(opt_name, "p") == 0) {
                gparams::display(std::cout, 0, false, false);
                exit(0);
            }
            else if (strcmp(opt_name, "pd") == 0) {
                gparams::display(std::cout, 0, false, true);
                exit(0);
            }
            else if (strcmp(opt_name, "pm") == 0) {
                if (opt_arg) {
                    gparams::display_module(std::cout, opt_arg);
                }
                else {
                    gparams::display_modules(std::cout);
                    std::cout << "\nUse -pm:name to display all parameters available at module 'name'\n";
                }
                exit(0);
            }
            else if (strcmp(opt_name, "pp") == 0) {
                if (!opt_arg)
                    error("option argument (-pp:name) is missing.");
                gparams::display_parameter(std::cout, opt_arg);
                exit(0);
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (-tr:tag) is missing.");
                enable_trace(opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (-dbg:tag) is missing.");
                enable_debug(opt_arg);
            }
#endif
            else if (strcmp(opt_name, "memory") == 0) {
                if (!opt_arg)
                    error("option argument (-memory:val) is missing.");
                gparams::set("memory_max_size", opt_arg);
            }
            else {
                std::cerr << "Error: invalid command line option: " << arg << "\n";
                std::cerr << "For usage information: z3 -h\n";
                exit(ERR_CMD_LINE);
            }
        }
        else if (argv[i][0] != '"' && (eq_pos = strchr(argv[i], '='))) {
            char * key   = argv[i];
            *eq_pos      = 0;
            char * value = eq_pos+1; 
            gparams::set(key, value);
        }
        else {
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = arg;
            }
        }
        i++;
    }
}


int STD_CALL main(int argc, char ** argv) {
#ifdef DUMP_ARGS
     std::cout << "args are: ";
     for (int i = 0; i < argc; i++)
         std::cout << argv[i] <<" ";
     std::cout << std::endl;
#endif
     try{
        unsigned return_value = 0;
        memory::initialize(0);
        memory::exit_when_out_of_memory(true, "ERROR: out of memory");
        parse_cmd_line_args(argc, argv);
        env_params::updt_params();

        if (g_input_file && g_standard_input) {
            error("using standard input to read formula.");
        }
        if (!g_input_file && !g_standard_input) {
            error("input file was not specified.");
        }
        
        if (g_input_kind == IN_UNSPECIFIED) {
            g_input_kind = IN_SMTLIB_2;
            char const * ext = get_extension(g_input_file);
            if (ext) {
                if (strcmp(ext, "datalog") == 0 || strcmp(ext, "dl") == 0) {
                    g_input_kind = IN_DATALOG;
                }
                else if (strcmp(ext, "dimacs") == 0 || strcmp(ext, "cnf") == 0) {
                    g_input_kind = IN_DIMACS;
                }
                else if (strcmp(ext, "wcnf") == 0) {
                    g_input_kind = IN_WCNF;
                }
                else if (strcmp(ext, "opb") == 0) {
                    g_input_kind = IN_OPB;
                }
                else if (strcmp(ext, "lp") == 0) {
                    g_input_kind = IN_LP;
                }
                else if (strcmp(ext, "log") == 0) {
                    g_input_kind = IN_Z3_LOG;
                }
                else if (strcmp(ext, "smt2") == 0) {
                    g_input_kind = IN_SMTLIB_2;
                }
                else if (strcmp(ext, "mps") == 0 || strcmp(ext, "sif") == 0 ||
                         strcmp(ext, "MPS") == 0 || strcmp(ext, "SIF") == 0) {
                    g_input_kind = IN_MPS;
                }
            }
    }
        switch (g_input_kind) {
        case IN_SMTLIB_2:
            memory::exit_when_out_of_memory(true, "(error \"out of memory\")");
            return_value = read_smtlib2_commands(g_input_file);
            break;
        case IN_DIMACS:
            return_value = read_dimacs(g_input_file);
            break;
        case IN_WCNF:
            return_value = parse_opt(g_input_file, wcnf_t);
            break;
        case IN_OPB:
            return_value = parse_opt(g_input_file, opb_t);
            break;
        case IN_LP:
            return_value = parse_opt(g_input_file, lp_t);
            break;
        case IN_DATALOG:
            read_datalog(g_input_file);
            break;
        case IN_Z3_LOG:
            replay_z3_log(g_input_file);
            break;
        case IN_MPS:
            return_value = read_mps_file(g_input_file);
            break;
        default:
            UNREACHABLE();
        }
        memory::finalize();
#ifdef _WINDOWS
        _CrtDumpMemoryLeaks();
#endif
        return return_value;
    }
    catch (z3_exception & ex) {
        // unhandled exception
        std::cerr << "ERROR: " << ex.msg() << "\n";
        if (ex.has_error_code())
            return ex.error_code();
        else
            return ERR_INTERNAL_FATAL;
    }
}

