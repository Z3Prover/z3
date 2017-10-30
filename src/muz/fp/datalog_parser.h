/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    datalog_parser.h

Abstract:

    Parser for Datalogish files

Author:

    Nikolaj Bjorner (nbjorner) 2010-5-17

Revision History:

--*/
#ifndef DATALOG_PARSER_H_
#define DATALOG_PARSER_H_

#include "ast/ast.h"
#include "muz/base/dl_context.h"

namespace datalog {

    class parser {
    public:        
        static parser * create(context& ctx, ast_manager & ast_manager);

        virtual ~parser() {}

        virtual bool parse_file(char const * path) = 0;
        virtual bool parse_string(char const * string) = 0;
    };

    class wpa_parser {
    public:        
        static wpa_parser * create(context& ctx, ast_manager & ast_manager);

        virtual ~wpa_parser() {}

        virtual bool parse_directory(char const * path) = 0;
    };

};

#endif
