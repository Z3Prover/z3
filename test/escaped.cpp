/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    escaped_str.cpp

Abstract:

    Escaped strings

Author:

    Leonardo de Moura (leonardo) 2011-03-01.

Revision History:

--*/
#include"util.h"

void tst_escaped() {
    std::cout << "[" << escaped("\"hello\"\"world\"\n\n") << "]\n";
    std::cout << "[" << escaped("\"hello\"\nworld\"\n\n\n", true) << "]\n";
    std::cout << "[" << escaped("\"hello\"\nworld\"\n", true) << "]\n";
    std::cout << "[" << escaped("\"hello\"\nworld\"", true) << "]\n";
    std::cout << "[" << escaped("\"hello\"\n\"world\"\n\n") << "]\n";
    std::cout << "[" << escaped("\n\n\n", true) << "]\n";
    std::cout << "[" << escaped("\n\n\n") << "]\n";
    std::cout << "[" << escaped("\n", true) << "]\n";
    std::cout << "[" << escaped("\n") << "]\n";
    std::cout << "[" << escaped("", true) << "]\n";
    std::cout << "[" << escaped("") << "]\n";
    std::cout << "[" << escaped(0, true) << "]\n";
    std::cout << "[" << escaped(0) << "]\n";
}
