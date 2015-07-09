/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtparser.h

Abstract:

    SMT parsing utilities

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-25

Revision History:

--*/
#ifndef SMT_PARSER_H_
#define SMT_PARSER_H_

#include<iostream>
#include"ast.h"
#include"vector.h"
#include"smtlib.h"

namespace smtlib {
    class parser {
    public:        
        static parser * create(ast_manager & ast_manager, bool ignore_user_patterns = false);

        virtual ~parser() {}

        virtual void add_builtin_op(char const *, family_id fid, decl_kind kind) = 0;
        virtual void add_builtin_type(char const *, family_id fid, decl_kind kind) = 0;

        virtual void initialize_smtlib() = 0;

        virtual void set_error_stream(std::ostream& strm) = 0;

        virtual bool parse_file(char const * path) = 0;
        virtual bool parse_string(char const * string) = 0;

        virtual benchmark * get_benchmark() = 0;
    };
};

#endif
