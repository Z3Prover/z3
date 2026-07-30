/*++
Module Name:

    scanner_io.cpp

Abstract:

    Regression test: a scanner must distinguish a FAILED input stream from an
    EXHAUSTED one.

    scanner::read_char() (src/parsers/util/scanner.cpp) does:

        m_stream.read(m_buffer.data()+1, m_buffer.size()-1);
        m_bend = 1 + static_cast<unsigned>(m_stream.gcount());
        m_bpos = 1;
        ...
        } else {
            ++m_bpos;
            return -1;
        }

    std::istream::gcount() returns 0 when the stream is exhausted AND when the
    read fails. So on a failed read m_bend == 1 == m_bpos, and read_char()
    returns -1 -- the identical value it returns for a cleanly finished file.
    bad(), fail() and exceptions() do not appear in that translation unit.

    The same shape is in smt2scanner.cpp, which is the path an input FILE takes
    (confirmed under gdb: smt2::scanner::scan -> smt2::parser::operator() ->
    parse_smt2_commands -> read_smtlib2_commands).

    Observed on Z3 5.0.0 with the read(2) failing under fault injection:

        errno     stdout      exit
        (none)    unsat       0     baseline
        EIO       (empty)     0     no answer, reported as success
        ENOSPC    (empty)     0     no answer, reported as success
        EINTR     unsat       0     recovered -- libstdc++ retries

    Note z3 ALREADY diagnoses a file it cannot OPEN (exit 108, "failed to open
    file"). The gap is a file it can open and cannot read.

    No wrong answer was observed: output was empty, never incorrect.

--*/
#include "parsers/util/scanner.h"
#include "util/warning.h"
#include <istream>
#include <sstream>

namespace {

    unsigned drain(scanner & s) {
        unsigned n = 0;
        while (s.scan() != scanner::EOF_TOKEN && n < 10000) ++n;
        return n;
    }
}

void tst_scanner_io() {
    // CONTROL -- a good stream must scan to completion, or the test proves
    // nothing about the failing case.
    {
        std::istringstream good("(assert (> x 5))");
        std::ostringstream err;
        scanner s(good, err, true /*smt2*/, false);
        unsigned n = drain(s);
        ENSURE(n > 0);
    }

    // THE TEST -- a stream in a failed state must not be reported as a clean
    // end of input. Today read_char() returns -1 for both, so the scanner
    // reports EOF_TOKEN and the caller sees a valid, empty document.
    {
        std::istringstream bad("(assert (> x 5))");
        bad.setstate(std::ios::badbit);
        std::ostringstream err;
        scanner s(bad, err, true /*smt2*/, false);

        // The scanner has an ERROR_TOKEN in its own enum (scanner.h:37). A
        // failed stream is exactly what it is for. Accept any signal: the
        // error token, a message on `err`, or an exception -- anything but
        // silence.
        bool signalled = false;
        try {
            scanner::token t;
            unsigned n = 0;
            while ((t = s.scan()) != scanner::EOF_TOKEN && n++ < 10000) {
                if (t == scanner::ERROR_TOKEN) { signalled = true; break; }
            }
            signalled = signalled || !err.str().empty();
        }
        catch (...) {
            signalled = true;
        }
        ENSURE(signalled);
    }
}
