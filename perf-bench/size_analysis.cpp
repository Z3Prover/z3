#include <iostream>
#include "ast/ast.h"

// Simple program to analyze struct sizes and memory layout
int main() {
    std::cout << "AST Structure Size Analysis" << std::endl;
    std::cout << "===========================" << std::endl;

    std::cout << "sizeof(ast): " << sizeof(ast) << " bytes" << std::endl;
    std::cout << "sizeof(app): " << sizeof(app) << " bytes" << std::endl;
    std::cout << "sizeof(expr): " << sizeof(expr) << " bytes" << std::endl;
    std::cout << "sizeof(func_decl): " << sizeof(func_decl) << " bytes" << std::endl;

    std::cout << std::endl;
    std::cout << "Memory alignment:" << std::endl;
    std::cout << "alignof(ast): " << alignof(ast) << " bytes" << std::endl;
    std::cout << "alignof(app): " << alignof(app) << " bytes" << std::endl;

    return 0;
}