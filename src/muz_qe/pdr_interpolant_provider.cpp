/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_interpolant_provider.cpp

Abstract:

    Interface for obtaining interpolants.

    This file is Windows specific.

Author:

    Krystof Hoder (t-khoder) 2011-10-19.

Revision History:

--*/

//disables the warning on deprecation of fgets function -- didn't really find by what it should be replaced
#ifdef _WINDOWS
#pragma warning(disable: 4995)
#endif

#include <sstream>
#include "ast_smt_pp.h"
#include "cmd_context.h"
#include "for_each_expr.h"
#include "obj_hashtable.h"
#include "smt2parser.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "pdr_util.h"
#include "pdr_interpolant_provider.h"
#include "expr_context_simplifier.h"

#ifdef _WINDOWS
#include <windows.h> 
#include <cstdio> 
#include <strsafe.h>
#include <process.h>

/**
Requirements for the use of this object:

The directory where the expcutable is must contain also executable 
PdrInterpolator.exe.

This executable takes one argument with a file name that contains
two SMTLIB problem instances, each terminated by string "\n##next##\n".

The output of the executable is given to the standard output and
is also terminated by the "\n##next##\n" string.

If formulas in the two input problems are unsatisfiable, they problem 
is printed at the output in the format
(assert FORM)

If the formulas are satisfiable, "0" is output and if the result cannot
be determined, the output is "?". (Both are still followed by "\n##next##\n").

*/
class interpolant_provider_impl : public interpolant_provider
{
    static std::string s_terminator_str;
    static std::string s_satisfiable_str;
    static std::string s_unknown_str;

    std::string m_exec_name;
    params_ref const & m_params;

    /**
    If non-empty, contains name of a temporary file that is used for passing the
    interpolation problem to the interpolating engine.
    */
    std::string m_tmp_file_name;

    simplifier m_simpl;

    PROCESS_INFORMATION m_pi;
    STARTUPINFOA        m_si;
    HANDLE m_in_rd;
    HANDLE m_out_rd;
    HANDLE m_in_wr;
    HANDLE m_out_wr;


    class used_symbol_inserter {
        typedef obj_hashtable<func_decl> func_decl_set;
        typedef obj_hashtable<sort> sort_set;

        ast_manager& m;
        cmd_context& m_cctx;

        func_decl_set m_funcs;
        sort_set m_sorts;

        void handle_sort(sort * s) {
            if(s->get_family_id()!=null_family_id || m_sorts.contains(s)) {
                return;
            }
            m_sorts.insert(s);
            NOT_IMPLEMENTED_YET();
            //we should insert it into the context somehow, but now not sure how and 
            //we don't deal with user defined sorts (yet)...
            //m_cctx.insert(s);
        }
        void handle_func_decl(func_decl * fn) {
            if(fn->get_family_id()!=null_family_id || m_funcs.contains(fn)) {
                return;
            }
            m_funcs.insert(fn);
            m_cctx.insert(fn);
        }

    public:        

        used_symbol_inserter(cmd_context& cctx) : m(cctx.m()), m_cctx(cctx) {}

        void operator()(var * n) {
            handle_sort(n->get_sort());
        }
        void operator()(app * n)        { 
            if (is_uninterp(n)) {
                handle_func_decl(n->get_decl());
            }
            handle_sort(n->get_decl()->get_range());
        }
        void operator()(quantifier * n) {
            unsigned sz = n->get_num_decls();
            for(unsigned i=0; i<sz; ++i) {
                handle_sort(n->get_decl_sort(i));
            }
        }
    };

    class form_fixer_cfg : public default_rewriter_cfg
    {
        ast_manager& m;
    public:
        form_fixer_cfg(ast_manager& m) : m(m) {}

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
            proof_ref & result_pr)
        {
            if(m.is_or(f) && num==0) { 
                result = m.mk_false();
                return BR_DONE;
            }
            return BR_FAILED;
        }
    };


    std::string get_tmp_file_name();

    std::string execute_interpolator(std::string input);

    void simplify_expr(expr* f, expr_ref& result);
    void output_interpolant_problem(std::ostream& out, expr * f1, expr * f2);

public:

    interpolant_provider_impl(ast_manager& m, params_ref const& params, std::string exec_name)
        : interpolant_provider(m),
          m_params(params),
          m_exec_name(exec_name),
          m_simpl(m) {
        memset(&m_si, 0, sizeof(m_si));
        memset(&m_pi, 0, sizeof(m_pi));
    }

    ~interpolant_provider_impl();


    /**
    If (f1 /\ f2) is unsatisfiable, return true and into res assign a formula
    I such that f1 --> I, I --> ~f2, and the language if I is in the intersection 
    of languages of f1 and f2.

    If (f1 /\ f2) is satisfiable, return false.
    */
    virtual lbool get_interpolant(expr * f1, expr * f2, expr_ref& res);
};

std::string interpolant_provider_impl::s_terminator_str = ";##next##";
std::string interpolant_provider_impl::s_satisfiable_str = ";#sat#";
std::string interpolant_provider_impl::s_unknown_str = ";#unknown#";

interpolant_provider_impl::~interpolant_provider_impl() {
    if(m_tmp_file_name.size()!=0) {
        DeleteFileA(m_tmp_file_name.c_str());
    }
    CloseHandle(m_pi.hProcess);
    CloseHandle(m_pi.hThread);
    CloseHandle(m_in_rd);
    CloseHandle(m_in_wr);
    CloseHandle(m_out_rd);
    CloseHandle(m_out_wr);
}

void interpolant_provider_impl::simplify_expr(expr* f, expr_ref& result) {
    expr_ref rwr_f(m);
    form_fixer_cfg fixer(m);
    rewriter_tpl<form_fixer_cfg> rwr(m, false, fixer);
    rwr(f, rwr_f);
    proof_ref pr(m);
    m_simpl(rwr_f, result, pr);
}


std::string interpolant_provider_impl::get_tmp_file_name() {
    //return "c:\\test.txt";
    if(m_tmp_file_name.length()!=0) {
        return m_tmp_file_name;
    }
    char path[MAX_PATH];
    if(GetTempPathA(256, path)==0) {
        throw default_exception("cannot get temp directory");
    }

    std::stringstream name_prefix_builder;

    name_prefix_builder<<"pdr"<<GetCurrentProcessId();

    char file[MAX_PATH];
    if(GetTempFileNameA(path, name_prefix_builder.str().c_str(), 1, file)==0) {
        throw default_exception("cannot get temp file");
    }
    m_tmp_file_name = file;
    return m_tmp_file_name;
}

void interpolant_provider_impl::output_interpolant_problem(std::ostream& out, expr * f1, expr * f2) {
    expr_ref t1(m), t2(m);
    simplify_expr(f1, t1);
    simplify_expr(f2, t2);
    
    ast_smt_pp pp(m);
    pp.add_assumption(t1);    
    pp.display(out, t2);
    out << "\n" << s_terminator_str << "\n";
}

std::string interpolant_provider_impl::execute_interpolator(std::string input)
{
    if (!m_pi.hProcess) {
        SECURITY_ATTRIBUTES sa;
        sa.nLength = sizeof(SECURITY_ATTRIBUTES); 
        sa.bInheritHandle = TRUE; 
        sa.lpSecurityDescriptor = NULL; 
        if (!CreatePipe(&m_out_rd, &m_out_wr, &sa, 0)) {
            throw default_exception("Could not create pipe");            
        }
        if (!CreatePipe(&m_in_rd, &m_in_wr, &sa, 0)) {
            throw default_exception("Could not create pipe");            
        }
        m_si.cb = sizeof(m_si);
        m_si.hStdError = 0;
        m_si.hStdOutput = m_out_wr;
        m_si.hStdInput = m_in_rd;
        m_si.dwFlags |= STARTF_USESTDHANDLES;
        if(!CreateProcessA(
               NULL, 
               (LPSTR)m_exec_name.c_str(), // command line 
               NULL,          // process security attributes 
               NULL,          // primary thread security attributes 
               TRUE,          // handles are inherited 
               0,             // creation flags 
               NULL,          // use parent's environment 
               NULL,          // use parent's current directory 
               &m_si,         // STARTUPINFO pointer 
               &m_pi)) {      // receives PROCESS_INFORMATION
            throw default_exception("Could not create process");
        }        
    }
    DWORD wr = 0, rd = 0;
    if (!WriteFile(m_in_wr, input.c_str(), static_cast<unsigned>(input.size()), &wr, 0)) {
        throw default_exception("Cold not write to pipe");
    }

    std::string result;
    char line[256];
    while (true) {
        memset(line, 0, sizeof(line));
        if (!ReadFile(m_out_rd, line, sizeof(line)-1, &rd, 0)) {
            throw default_exception("Cold not write to pipe");
        }
        result += line;     
        if (strstr(result.c_str(), s_terminator_str.c_str())) { 
            return result;
        }
    }
}

lbool interpolant_provider_impl::get_interpolant(expr * f1, expr * f2, expr_ref& res) {
    std::ostringstream prb;
    output_interpolant_problem(prb, f1, f2);
    std::string res_text = execute_interpolator(prb.str());
    if(strstr(res_text.c_str(), s_satisfiable_str.c_str())) {
        return l_false;
    }
    if(strstr(res_text.c_str(), s_unknown_str.c_str())) {
        return l_undef;
    }

    front_end_params dummy_params;
    cmd_context cctx(&dummy_params, false, &m);
    for_each_expr(used_symbol_inserter(cctx), f1);

    parse_smt2_commands(cctx, std::istringstream(res_text), false);

    ptr_vector<expr>::const_iterator ait = cctx.begin_assertions();
    ptr_vector<expr>::const_iterator aend = cctx.end_assertions();
    if(ait+1!=aend) {
        throw default_exception("invalid interpolator output");
    }
    res = *ait;
    if (m_params.get_bool(":dump-interpolants", false)) {
        interpolant_provider::output_interpolant(m, f1, f2, res);
    }
    return l_true;
}

interpolant_provider * interpolant_provider::mk(ast_manager& m, params_ref const& p)
{
    char self_name[MAX_PATH];
    GetModuleFileNameA(NULL, self_name, MAX_PATH);
    char * last_backslash = strrchr(self_name,'\\');
    if(last_backslash==NULL) {
        throw default_exception("GetModuleFileNameA did not return full path to the executable");
    }
    //we cut the string at the last backslash
    *last_backslash = 0;

    std::string exec_name = self_name + std::string(".\\PdrInterpolator.exe");

    return alloc(interpolant_provider_impl, m, p, exec_name);
}

#else

interpolant_provider * 
interpolant_provider::mk(ast_manager& m, params_ref const& p) {
    // interpolations are windows specific and private.
    return 0;
}


#endif


void interpolant_provider::output_interpolant(ast_manager& m, expr* A, expr* B, expr* I) {
    static unsigned file_num = 0;
    
    std::ostringstream filename;
    filename << "interpolation_" << file_num++ << ".smt";
    std::ofstream out(filename.str().c_str());

    ast_smt_pp pp(m);
    pp.add_assumption(A);
    pp.display(out, B);
    std::ostringstream strm;
    strm << ";" << mk_pp(I, m) << "\n";

    buffer<char> buff;
    std::string s = strm.str();
    char const* i_str = s.c_str();
    while (*i_str) {
        buff.push_back(*i_str);
        if (*i_str == '\n') {
            buff.push_back(';');
        }
        ++i_str;
    }
    buff.push_back(0);
    out << buff.c_ptr();
    out << "##next##\n";
    out.close();
}
