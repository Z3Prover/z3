#ifdef _WINDOWS
#include <iostream>
#include <strstream>
#include <fstream>
#include <sstream>
#include "smtparser.h"
#include "for_each_file.h"
#include "array_decl_plugin.h"
#include "bv_decl_plugin.h"


class for_each_file_smt : public for_each_file_proc {
public:
    for_each_file_smt() {}
    
    bool operator()(char const * file_path) {
        bool result = true;
        std::cout << "Parsing: " << file_path << std::endl;

        ast_manager ast_manager;
        smtlib::parser* parser = smtlib::parser::create(ast_manager);
        ast_manager.register_decl_plugins();

        parser->initialize_smtlib();

        if (!parser->parse_file(file_path)) {
            std::cout << "Could not parse file : " << file_path << std::endl;
            result = false;
        }
        dealloc(parser);
        return result;
    }
};


static bool test_directory(char const * base) {
    for_each_file_smt foreach;
    return for_each_file(foreach, base, "*.smt");
}

void tst_smtparser(char** argv, int argc, int & i) {
    bool result = true;
    if (i + 1 < argc) {
        result = test_directory(argv[i+1]);
        i += 1;
    }
    SASSERT(result);
}
#else
void tst_smtparser(char** argv, int argc, int & i) {
}
#endif
