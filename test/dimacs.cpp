/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_dimacs.cpp

Abstract:

    Test dimacs parser

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

--*/

#include <iostream>
#include <fstream>
#ifdef _WINDOWS
#include <windows.h>
#include <strsafe.h>
#endif
#include"trace.h"
#include"dimacs_parser.h"

class dummy_sat {
    unsigned m_num_vars;
public:
    dummy_sat():m_num_vars(0) {}
    unsigned get_num_vars() { 
        return m_num_vars;
    }
    void mk_var() {
        TRACE("dimacs", tout << "making variable: p" << m_num_vars << "\n";);
        m_num_vars++;
    }
    void mk_clause(literal_vector & lits) {
        TRACE("dimacs", tout << "making clause: " << lits << "\n";);
    }
};

static void tst1()
{
#ifdef _WINDOWS
    dummy_sat solver;
    const char * base = ".";
    std::string pattern(base);
    pattern += "\\*.cnf";

    char buffer[MAX_PATH];
    
    WIN32_FIND_DATAA data;
    HANDLE h = FindFirstFileA(pattern.c_str(),&data);

    while (h != INVALID_HANDLE_VALUE) {
        StringCchPrintfA(buffer, ARRAYSIZE(buffer), "%s\\%s", base, data.cFileName);       
        
        TRACE("dimacs", tout << "Parsing: " << buffer << "\n";);
        
        std::ifstream s(buffer);

        parse_dimacs(s, solver);

        if (!FindNextFileA(h,&data))
            break;
    }
#endif
}

void tst_dimacs() {
    tst1();
}
