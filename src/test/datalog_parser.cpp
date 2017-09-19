
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/fp/datalog_parser.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "smt/params/smt_params.h"
#include "ast/reg_decl_plugins.h"

using namespace datalog;


static void dparse_string(char const* str) {
    ast_manager m;
    smt_params params;
    reg_decl_plugins(m);
    register_engine re;
    context ctx(m, re, params);
    parser* p = parser::create(ctx,m);

    bool res = p->parse_string(str);

    if (res) {
        std::cout << "Parsed\n"<<str<<"\n";
    }
    else {
        std::cout << "Parser did not succeed on string\n"<<str<<"\n";
    }
    dealloc(p);
}

static void dparse_file(char const* file) {
    ast_manager m;
    smt_params params;
    reg_decl_plugins(m);
    register_engine re;

    context ctx(m, re, params);
    parser* p = parser::create(ctx,m);

    if (!p->parse_file(file)) {
        std::cout << "Failed to parse file\n";
    }
    dealloc(p);
}



void tst_datalog_parser() {
    dparse_string("\nH :- C1(X,a,b), C2(Y,a,X) .");
    dparse_string("N 128\n\nH :- C1(X,a,b), C2(Y,a,X) .");
    dparse_string("N 128\nI 128\n\nC1(x : N, y : N, z : I)\nC2(x : N, y : N, z : N)\nH :- C1(X,a,b), C2(Y,a,X) .");
    dparse_string("\nH :- C1(X,a,b), nC2(Y,a,X) .");
    dparse_string("\nH :- C1(X,a,b),nC2(Y,a,X).");
    dparse_string("\nH :- C1(X,a,b),\\\nC2(Y,a,X).");
    dparse_string("\nH :- C1(X,a\\,\\b), C2(Y,a,X) .");
}

void tst_datalog_parser_file(char** argv, int argc, int & i) {
    if (i + 1 < argc) {
        dparse_file(argv[i+1]);
        i++;
    }
}


