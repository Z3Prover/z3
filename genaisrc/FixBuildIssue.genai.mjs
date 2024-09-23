
def("FILE", env.files)

def("ERR", "/home/nbjorner/z3/src/nlsat/nlsat_simple_checker.cpp: In member function ‘bool nlsat::simple_checker::imp::Endpoint::operator==(const nlsat::simple_checker::imp::Endpoint&) const’:\
/home/nbjorner/z3/src/nlsat/nlsat_simple_checker.cpp:63:82: warning: C++20 says that these are ambiguous, even though the second is reversed:\
   63 |                 if (!m_inf && !rhs.m_inf && m_open == rhs.m_open && m_val == rhs.m_val) {\
      |                                                                                  ^~~~~\
In file included from /home/nbjorner/z3/src/util/mpz.h:26,\
                 from /home/nbjorner/z3/src/util/mpq.h:21,\
                 from /home/nbjorner/z3/src/util/rational.h:21,\
                 from /home/nbjorner/z3/src/math/polynomial/algebraic_numbers.h:21,\
                 from /home/nbjorner/z3/src/nlsat/nlsat_simple_checker.h:20,\
                 from /home/nbjorner/z3/src/nlsat/nlsat_simple_checker.cpp:1:\
/home/nbjorner/z3/src/util/scoped_numeral.h:96:17: note: candidate 1: ‘bool operator==(const _scoped_numeral<algebraic_numbers::manager>&, const _scoped_numeral<algebraic_numbers::manager>::numeral&)’\
   96 |     friend bool operator==(_scoped_numeral const & a, numeral const & b) {\
      |                 ^~~~~~~~\
/home/nbjorner/z3/src/util/scoped_numeral.h:96:17: note: candidate 2: ‘bool operator==(const _scoped_numeral<algebraic_numbers::manager>&, const _scoped_numeral<algebraic_numbers::manager>::numeral&)’ (reversed)")

$`You are an expert C++ programmer.
Your task is to fix the compilation bug reported in the error message ERR.
How should FILE be changed to fix the error message?`
