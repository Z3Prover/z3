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
#include"memory_manager.h"
#include"trace.h"
#include"debug.h"
#include"util.h"
#include"pp.h"
#include"smtlib_frontend.h"
#include"z3_log_frontend.h"
#include"warning.h"
#include"version.h"
#include"datalog_frontend.h"
#include"dimacs_frontend.h"
#include"timeout.h"
#include"z3_exception.h"
#include"error_codes.h"

typedef enum { IN_UNSPECIFIED, IN_SMTLIB, IN_SMTLIB_2, IN_DATALOG, IN_DIMACS, IN_Z3_LOG } input_kind;

std::string         g_aux_input_file;
char const *        g_input_file          = 0;
bool                g_standard_input      = false;
input_kind          g_input_kind          = IN_UNSPECIFIED;
front_end_params *  g_front_end_params    = 0;
bool                g_display_statistics  = false;
bool                g_display_istatistics = false;

#ifdef _WINDOWS
#define OPT "/"
#else
#define OPT "-"
#endif

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: z3 " << OPT << "h\n";
    exit(ERR_CMD_LINE);
}

void display_usage() {
    std::cout << "Z3 [version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << " - ";
#ifdef _AMD64_
    std::cout << "64";
#else
    std::cout << "32";
#endif
    std::cout << " bit]. (C) Copyright 2006 Microsoft Corp.\n";
    std::cout << "Usage: z3 [options] [" << OPT << "file:]file\n";
    std::cout << "\nInput format:\n";
    std::cout << "  " << OPT << "smt        use parser for SMT input format.\n";
    std::cout << "  " << OPT << "smt2       use parser for SMT 2 input format.\n";
    std::cout << "  " << OPT << "dl         use parser for Datalog input format.\n";
    std::cout << "  " << OPT << "dimacs     use parser for DIMACS input format.\n";
    std::cout << "  " << OPT << "log        use parser for Z3 log input format.\n";
    std::cout << "  " << OPT << "in         read formula from standard input.\n";
    std::cout << "\nMiscellaneous:\n";
    std::cout << "  " << OPT << "h, " << OPT << "?      prints this message.\n";
    std::cout << "  " << OPT << "version    prints version number of Z3.\n";
    std::cout << "  " << OPT << "v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  " << OPT << "nw         disable warning messages.\n";
    std::cout << "  " << OPT << "ini:file   configuration file.\n";
    std::cout << "  " << OPT << "ini?       display all available INI file parameters.\n";
    std::cout << "  --"      << "          all remaining arguments are assumed to be part of the input file name. This option allows Z3 to read files with strange names such as: -foo.smt2.\n";
    std::cout << "\nResources:\n";
    // timeout and memout are now available on Linux and OSX too.
    std::cout << "  " << OPT << "T:timeout  set the timeout (in seconds).\n";
    std::cout << "  " << OPT << "t:timeout  set the soft timeout (in seconds). It only kills the current query.\n";
    std::cout << "  " << OPT << "memory:Megabytes  set a limit for virtual memory consumption.\n";
    // 
    std::cout << "\nOutput:\n";
    std::cout << "  " << OPT << "st         display statistics.\n";
    std::cout << "\nSearch heuristics:\n";
    std::cout << "  " << OPT << "rs:num     random seed.\n";
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  " << OPT << "tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  " << OPT << "dbg:tag    enable assertions tagged with <tag>.\n";
#endif
}

class extra_params : public datalog_params {
    bool &   m_statistics;
public:
    extra_params():
        m_statistics(g_display_statistics) {
    }

    virtual ~extra_params() {}

    virtual void register_params(ini_params & p) {
        datalog_params::register_params(p);
        p.register_bool_param("STATISTICS", m_statistics, "display statistics");
    }
};

ini_params*         g_params = 0;
extra_params*       g_extra_params = 0;
bool                g_params_initialized = false;

void init_params() {
    if (!g_params_initialized) {
        z3_bound_num_procs();
        g_front_end_params = new front_end_params();
        g_params = new ini_params();
        g_extra_params = new extra_params();
        register_verbosity_level(*g_params);
        register_warning(*g_params);
        register_pp_params(*g_params);
        g_front_end_params->register_params(*g_params);
        g_extra_params->register_params(*g_params);
        g_params_initialized = true;
    }
}

void del_params() {
    if (g_front_end_params != NULL)
        g_front_end_params->close_trace_file();
    delete g_extra_params;
    delete g_params;
    delete g_front_end_params;
    g_extra_params = 0;
    g_params = 0;
    g_front_end_params = 0;
}

    
void read_ini_file(const char * file_name) {
    std::ifstream in(file_name);
    if (in.bad() || in.fail()) {
        std::cerr << "Error: failed to open init file \"" << file_name << "\".\n"; 
        exit(ERR_INI_FILE);
    }
    g_params->read_ini_file(in);
}

void display_ini_help() {
    g_params->display_params(std::cout);
}

void display_config() {
    if (g_front_end_params->m_display_config) {
        display_ini_help();
    }
}

void display_ini_doc() {
    g_params->display_params_documentation(std::cout);
}

void parse_cmd_line_args(int argc, char ** argv) {
    int i = 1;
    char * eq_pos = 0;
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
            if (g_front_end_params->m_interactive) {
                warning_msg("ignoring input file in interactive mode.");
            }
            else if (g_input_file) {
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
            char * opt_arg  = 0;
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
                std::cout << "Z3 version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "\n";
                exit(0);
            }
            else if (strcmp(opt_name, "smt") == 0) {
                g_input_kind = IN_SMTLIB;
            }
            else if (strcmp(opt_name, "smt2") == 0) {
                g_input_kind = IN_SMTLIB_2;
            }
            else if (strcmp(opt_name, "in") == 0) {
                g_standard_input = true;
            }
            else if (strcmp(opt_name, "dimacs") == 0) {
                g_input_kind = IN_DIMACS;
            }
            else if (strcmp(opt_name, "log") == 0) {
                g_input_kind = IN_Z3_LOG;
            }
            else if (strcmp(opt_name, "st") == 0) {
                g_display_statistics = true; 
            }
            else if (strcmp(opt_name, "ist") == 0) {
                g_display_istatistics = true; 
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (/v:level) is missing.");
                long lvl = strtol(opt_arg, 0, 10);
                set_verbosity_level(lvl);
            }
            else if (strcmp(opt_name, "vldt") == 0) {
                g_front_end_params->m_model_validate = true;
            }
            else if (strcmp(opt_name, "file") == 0) {
                g_input_file = opt_arg;
            }
            else if (strcmp(opt_name, "r") == 0) {
                if (!opt_arg) {
                    error("optional argument (/r:level) is missing.");
                }
                g_front_end_params->m_relevancy_lvl = strtol(opt_arg, 0, 10);
            }
            else if (strcmp(opt_name, "rd") == 0) {
                if (!opt_arg) {
                    error("optional argument (/rd:num) is missing.");
                }
                g_front_end_params->m_random_var_freq = static_cast<double>(strtol(opt_arg, 0, 10)) / 100.0;
            }
            else if (strcmp(opt_name, "rs") == 0) {
                if (!opt_arg) {
                    error("optional argument (/rs:num) is missing.");
                }
                long seed = strtol(opt_arg, 0, 10);
                g_front_end_params->m_random_seed = seed;
                g_front_end_params->m_arith_random_seed = seed;
            }
            else if (strcmp(opt_name, "T") == 0) {
                if (!opt_arg)
                    error("option argument (/T:timeout) is missing.");
                long tm = strtol(opt_arg, 0, 10);
                set_timeout(tm * 1000);
            }
            else if (strcmp(opt_name, "t") == 0) {
                if (!opt_arg)
                    error("option argument (/t:timeout) is missing.");
                long tm = strtol(opt_arg, 0, 10);
                g_front_end_params->m_soft_timeout = tm*1000;
            }
            else if (strcmp(opt_name, "nw") == 0) {
                enable_warning_messages(false);
            }
            else if (strcmp(opt_name, "ini") == 0) {
                if (!opt_arg)
                    error("option argument (/ini:file) is missing.");
                read_ini_file(opt_arg);
            }
            else if (strcmp(opt_name, "ini?") == 0) {
                display_ini_help();
                exit(0);
            }
            else if (strcmp(opt_name, "geninidoc") == 0) {
                display_ini_doc();
                exit(0);
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (/tr:tag) is missing.");
                enable_trace(opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (/dbg:tag) is missing.");
                enable_debug(opt_arg);
            }
#endif
            else if (strcmp(opt_name, "memory") == 0) {
                if (!opt_arg)
                    error("option argument (/memory:val) is missing.");
                g_front_end_params->m_memory_high_watermark = strtoul(opt_arg, 0, 10);
            }
            else {
                std::cerr << "Error: invalid command line option: " << arg << "\n";
                std::cerr << "For usage information: z3 " << OPT << "h\n";
                exit(ERR_CMD_LINE);
            }
        }
        else if (argv[i][0] != '"' && (eq_pos = strchr(argv[i], '='))) {
            char * key   = argv[i];
            *eq_pos      = 0;
            char * value = eq_pos+1; 
            g_params->set_param_value(key, value);
        }
        else {
            if (g_front_end_params->m_interactive) {
                warning_msg("ignoring input file in interactive mode.");
            }
            else if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = arg;
            }
        }
        i++;
    }
}

char const * get_extension(char const * file_name) {
    if (file_name == 0)
        return 0;
    char const * last_dot = 0;
    for (;;) {
        char const * tmp = strchr(file_name, '.');
        if (tmp == 0) {
            return last_dot;
        }
        last_dot  = tmp + 1;
        file_name = last_dot;
    }
}

class global_state_initialiser {
public:
    global_state_initialiser() {
        memory::initialize(0);
#if defined(_WINDOWS) && defined(_Z3_BUILD_PARALLEL_SMT)
        memory::mem->set_threaded_mode(true);
#endif
        init_params();
    }

    void reset() {
        del_params();
        memory::finalize();
    }

    ~global_state_initialiser() {
        reset();
    }
};

int main(int argc, char ** argv) {
    try{
        unsigned return_value = 0;
        global_state_initialiser global_state;
        memory::exit_when_out_of_memory(true, "ERROR: out of memory");
        parse_cmd_line_args(argc, argv);
        memory::set_high_watermark(static_cast<size_t>(g_front_end_params->m_memory_high_watermark) * 1024 * 1024);
        memory::set_max_size(static_cast<size_t>(g_front_end_params->m_memory_max_size) * 1024 * 1024);
        g_front_end_params->open_trace_file();
        DEBUG_CODE(
                   if (g_front_end_params->m_copy_params != -1) {
                       g_front_end_params->copy_params(g_front_end_params->m_copy_params);
                       TRACE("copy_params", g_params->display_params(tout););
                   });
        if (g_input_file && g_standard_input) {
            error("using standard input to read formula.");
        }
        if (!g_input_file && !g_front_end_params->m_interactive && !g_standard_input) {
            error("input file was not specified.");
        }
        
        if (g_input_kind == IN_UNSPECIFIED) {
            g_input_kind = IN_SMTLIB;
            char const * ext = get_extension(g_input_file);
            if (ext) {
                if (strcmp(ext, "datalog") == 0 || strcmp(ext, "dl") == 0) {
                    g_input_kind = IN_DATALOG;
                }
                else if (strcmp(ext, "dimacs") == 0 || strcmp(ext, "cnf") == 0) {
                    g_input_kind = IN_DIMACS;
                }
                else if (strcmp(ext, "log") == 0) {
                    g_input_kind = IN_Z3_LOG;
                }
                else if (strcmp(ext, "smt2") == 0) {
                    g_input_kind = IN_SMTLIB_2;
                }
                else if (strcmp(ext, "smt") == 0) {
                    g_input_kind = IN_SMTLIB;
                }
            }
	}
        switch (g_input_kind) {
        case IN_SMTLIB:
            return_value = read_smtlib_file(g_input_file, *g_front_end_params);
            break;
        case IN_SMTLIB_2:
            memory::exit_when_out_of_memory(true, "(error \"out of memory\")");
            return_value = read_smtlib2_commands(g_input_file, *g_front_end_params);
            break;
        case IN_DIMACS:
            return_value = read_dimacs(g_input_file, *g_front_end_params);
            break;
        case IN_DATALOG:
            read_datalog(g_input_file, *g_extra_params, *g_front_end_params);
            break;
        case IN_Z3_LOG:
            replay_z3_log(g_input_file);
            break;
        default:
            UNREACHABLE();
        }
        global_state.reset();
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

