#include "simplex_polynomial.h"

void tst_simplex_polynomial()
{
    polynomial p1, p2, p3, p4;
    simplex_variable v1(1), v2(2), v3(3), v4(4), v5(5);
    monomial m1(v1), m2(v2), m3(v3), m4(v4);

    m1 = monomial(v1);
    m1 *= monomial(v2);
    m1 *= monomial(v1);

    m1.display(std::cout) << std::endl;
    m1.normalize();
    m1.display(std::cout) << std::endl;
    
    m2 = m1;
    SASSERT(m1 == m2);

    p1 = polynomial(rational(1,2));
    SASSERT(p1.is_const());

    p1 += polynomial(v1);
    SASSERT(!p1.is_const());

    p1 += polynomial(v2);
    p1 *= polynomial(v2);
    p1 -= polynomial(v3);
    p1 += polynomial(rational(2,3));

    p1.normalize();
    p1.display(std::cout) << std::endl;
    SASSERT(p1[0].size() == 0); // first element is a constant.


    p1 = polynomial(v1);
    p2 = polynomial(v2);
    p3 = polynomial(v3);
    p3 += p2;
    p3 *= p1;

    p3.display(std::cout) << std::endl; // multiplication distributes.
    SASSERT(p3.size() == 2);

}
