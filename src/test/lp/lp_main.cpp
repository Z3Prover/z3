void        gparams_register_modules(){}
void mem_initialize() {}
void mem_finalize() {}
#include "util/rational.h"
namespace lp {
void test_lp_local(int argc, char**argv);
}
int main(int argn, char**argv){
    rational::initialize();
    lp::test_lp_local(argn, argv);
    rational::finalize();
    return 0;
}

