#include "util/debug.h"
#include "util/trace.h"
#include "util/zstring.h"

// Encode and check for roundtrip all printable ASCII characters.
static void tst_ascii_roundtrip() {
    unsigned ascii_min = 0x20; // ' '
    unsigned ascii_max = 0x7E; // '~'

    for (unsigned i = ascii_min; i <= ascii_max; i++) {
        zstring input(i);
        std::string expected(1, i);
        bool roundtrip_ok = input.encode() == expected;

        if (!roundtrip_ok) {
            std::cout << "Failed to roundtrip printable ASCII char: " << expected
                      << "\n" << std::flush;
            ENSURE(roundtrip_ok);
        }
    }
}

void tst_zstring() {
    tst_ascii_roundtrip();
}
