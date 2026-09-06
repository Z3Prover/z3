#include <z3.h>

int main(void) {
    unsigned major, minor, build, revision;
    Z3_get_version(&major, &minor, &build, &revision);
    return 0;
}
