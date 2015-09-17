/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial_factorization.cpp

Abstract:

    Implementation of polynomial factorization.

Author:

    Dejan (t-dejanj) 2011-11-15

Notes:

   [1] Elwyn Ralph Berlekamp. Factoring Polynomials over Finite Fields. Bell System Technical Journal, 
       46(8-10):1853-1859, 1967.
   [2] Donald Ervin Knuth. The Art of Computer Programming, volume 2: Seminumerical Algorithms. Addison Wesley, third 
       edition, 1997.
   [3] Henri Cohen. A Course in Computational Algebraic Number Theory. Springer Verlag, 1993.

--*/
#if 0
// disabled for reorg

#include"trace.h"
#include"util.h"
#include"polynomial_factorization.h"
#include"upolynomial_factorization_int.h"
#include"prime_generator.h"

using namespace std;

namespace polynomial {

typedef upolynomial::manager::scoped_numeral scoped_numeral;

/**
   Generates a substitution of values for f -> f_univariate in order to reduce the factorization to the 
   univariate case.
   
   @param f multivariate polynomial (square-free, primitive, vars(f) > 1)
   @param x the variable we want to keep as the univarate one
   @param f_lc the leading coefficient of f in x
   @param vars the vector of all variables from f witouth x
   @param size the bound to use for selecting the values, i.e. |a_i| <= size
   @param a the output values corresponding to vairables in (place place for x should be ignored)
   @param f_univariate the output substitution
*/
void generate_substitution_values(
    polynomial_ref const & f, var x, polynomial_ref const & f_lc, var_vector const & vars, unsigned & size, 
    upolynomial::numeral_vector & a, upolynomial::manager upm, upolynomial::numeral_vector & f_u) {

    SASSERT(a.size() == vars.size());

    TRACE("polynomial::factorization", tout << "polynomial::generate_substitution_values(f = " << f << ", f_lc = " << f_lc << ")";);
    
    // f = f_n x^n + ... + f_0, square-free and primitive
    // this means 
    // f_lc = f_n
    // since f is primitive, 
    // we are looking for numbers a_i such that 
    // (1) f_lc doesn't vanish
    // (2) f_u = f(a_0, ..., a_n, x) is square-free

    manager & pm = f.m();
    numeral_manager & nm = pm.m();

    // polynomial to use for subtituting into the lc(f)
    polynomial_ref f_lc_subst(pm);    

    // random generator
    random_gen generator;
    
    // increase the size every once in a while (RETHINK THIS)
    unsigned inc_size_c = 0;
    unsigned inc_size_c_max = size;

    while (true) {
    
        // see if we should increase the size of the substitution
        if ((++ inc_size_c) % inc_size_c_max == 0) {
            size ++;
            inc_size_c = 0;
            inc_size_c_max *= 2;
        }

        // the head coefficient we'll substitute in
        f_lc_subst = f_lc;

        bool vanished = false;
        for (unsigned i = 0; i < vars.size() && !vanished; ++ i) {
            SASSERT(vars[i] != x);
        
            // the value for x_i
            nm.set(a[i], (int)generator(2*size+1) - (int)size);

            // substitute
            f_lc_subst = pm.substitute(f_lc_subst, x, a[i]);

            // did it vanish
            vanished = pm.is_zero(f_lc_subst);
        }

        if (vanished) {
            // leading coefficient vanished, try again
            continue;
        }

        // substitute into f and get the univariate one
        polynomial_ref f_subst(pm);
        f_subst = pm.substitute(f, vars.size(), vars.c_ptr(), a.c_ptr());
        upm.to_numeral_vector(f_subst, f_u);

        // if the result is not square-free we try again
        if (!upm.is_square_free(f_u))
            continue;

        // found it, break
        break;
    }
}

/** 
   \brief Bound for the coefficients of the factorst of the multivariate polynomial f. R
   Returns power of p -> p^e that covers the bound

   We use the gelfond bound here:
     d_i: degree of x_i in f(x1, ..., x_n)
     bound = |f| * 2^(\sum d_i - (n-1)/2))
*/
void multivariate_factor_coefficient_bound(polynomial_ref const & f, var x, numeral const & p, unsigned & e, numeral & p_e, var2degree & d) {
    manager & pm = f.m();
    numeral_manager & nm = pm.m();
    
    // compute g = lc(f)*f
    polynomial_ref f_lc(pm), g(pm);    
    f_lc = pm.coeff(f, x, pm.degree(f, x));    
    g = pm.mul(f, f_lc);
    
    // get the norm
    scoped_numeral g_norm(nm);
    pm.abs_norm(g, g_norm);

    // get the variable degrees
    var_vector vars;
    pm.vars(f, vars);
    unsigned power = 0;
    for (unsigned i = 0; i < vars.size(); ++ i) {
        unsigned c_d = pm.degree(g, vars[i]);
        d.set_degree(vars[i], c_d + 1);
        power += c_d;
    }
    power = power - (vars.size()-1)/2;

    // compute the bound
    scoped_numeral bound(nm);
    nm.set(bound, 2);
    nm.power(bound, power, bound);
    nm.mul(g_norm, bound, bound);
 
    // return the first power of two that is bigger than the norm
    e = 1;
    nm.set(p_e, p);
    while (nm.lt(p_e, bound)) {
        nm.mul(p_e, p_e, p_e);
        e *= 2;
    }
}

// check that A*S+B*T=C in zp mod ideal
bool check_solve(zp_manager & zp_pm, var2degree const & ideal,
    zp_polynomial_ref const & A, zp_polynomial_ref const & B, zp_polynomial_ref const & C,
    zp_polynomial_ref const & S, zp_polynomial_ref const & T) {
    zp_polynomial_ref AS(zp_pm), BT(zp_pm), sum(zp_pm);
    AS = zp_pm.mul(A, S); AS = zp_pm.mod_d(AS, ideal);
    BT = zp_pm.mul(B, T); BT = zp_pm.mod_d(BT, ideal);
    sum = zp_pm.add(AS, BT);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "zp_pm = Z_" << zp_pm.m().m().to_string(zp_pm.m().p()) << endl;
          tout << "ideal = " << ideal << endl;
          tout << "A = " << A << endl;
          tout << "B = " << B << endl;
          tout << "S = " << S << endl;
          tout << "T = " << T << endl;
          tout << "C = " << C << endl;
          tout << "sum = " << sum << endl;
          );
    
    bool result = zp_pm.eq(sum, C);
    return result;
}
    
/**
   Solve the equation A*S + B*T = C, given, AU + BV = 1, with deg(T) < deg(A)
   S = U*C + tB
   T = V*C - tA
   we divide VC with  A to get (T, t)
*/
template<typename output_manager>
void solve(zp_manager & zp_pm, var x, var2degree const & ideal,
           zp_polynomial_ref const & A, zp_polynomial_ref const & U, 
           zp_polynomial_ref const & B, zp_polynomial_ref const & V, 
           zp_polynomial_ref const & C, 
           output_manager & out_pm,
           typename output_manager::polynomial_ref & S_out, 
           typename output_manager::polynomial_ref & T_out) {
    TRACE("polynomial::factorization::multivariate", 
          tout << "polynomial::solve(" << endl;
          tout << "zp_pm = Z_" << zp_pm.m().m().to_string(zp_pm.m().p()) << endl;
          tout << "ideal = " << ideal << endl;
          tout << "A = " << A << endl;
          tout << "B = " << B << endl;
          tout << "U = " << U << endl;
          tout << "V = " << V << endl;
          tout << "C = " << C << endl;
          );
    
    // solution is S = C*U + tB, T = C*V - tA
    zp_polynomial_ref CV(zp_pm);
    CV = zp_pm.mul(C, V); CV = zp_pm.mod_d(CV, ideal);
    zp_polynomial_ref CU(zp_pm);
    CU = zp_pm.mul(C, U); CU = zp_pm.mod_d(CU, ideal);
    zp_polynomial_ref t(zp_pm), T(zp_pm);
    zp_pm.exact_pseudo_division_mod_d(CV, A, x, ideal, t, T); 
    
    zp_polynomial_ref tB(zp_pm);
    tB = zp_pm.mul(t, B); tB = zp_pm.mod_d(tB, ideal);
    zp_polynomial_ref S(zp_pm);
    S = zp_pm.add(CU, tB);
    
    SASSERT(check_solve(zp_pm, ideal, A, B, C, S, T));
    
    // convert to the other manager
    S_out = convert(zp_pm, S, out_pm);
    T_out = convert(zp_pm, T, out_pm);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "CU = " << CU << endl;
          tout << "CV = " << CV << endl;
          tout << "t = " << t << endl;
          tout << "--- solution ---" << endl;
          tout << "S = " << S_out << endl;
          tout << "T = " << T_out << endl;
          );
}

/**
   A, B, U, V: multivariate polynomials in Z_p[x, ...], mod ..., also the output polynomials, y is not there
   C: C = A*B in Z_p[x, ...] mod p, ...
   
   ideal: all the vars we care about in the ideal
   
   y, the variable we are lifting is not in ideal_vars, we will add it

   A monic, A*U+B*V = 1
   
   p is not necessary prime, it's a power of a prime

   we're doing quadratic lifting here

   output: added y, i.e.
   * all polynomials in Z_p[x, ..., y] mod (..., y^d)
*/
void multivariate_hansel_lift_ideal(
    zp_manager & zp_pm, var x,
        zp_polynomial_ref const & C, 
        zp_polynomial_ref & A, zp_polynomial_ref & U, zp_polynomial_ref & B, zp_polynomial_ref & V,
        var2degree & ideal, var y, unsigned d) {
    numeral_manager & nm = zp_pm.m().m();
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "polynomial::multiratiate_hensel_lift_ideal" << endl;
          tout << "zp_pm is Z_" << zp_pm.m().m().to_string(zp_pm.m().p()) << endl;
          tout << "x = x" << x << endl;
          tout << "y = x" << y << endl;
          tout << "C = " << C << endl;
          tout << "A = " << A << endl;
          tout << "B = " << B << endl;
          tout << "U = " << U << endl;
          tout << "V = " << V << endl;
          tout << "ideal = " << ideal << endl;
          );
    
    // constant 1
    scoped_numeral one(nm);
    nm.set(one, 1);
    zp_polynomial_ref one_p(zp_pm);
    one_p = zp_pm.mk_const(one);
    
    SASSERT(zp_pm.degree(A, y) == 0 && zp_pm.degree(B, y) == 0 && zp_pm.degree(U, y) == 0 && zp_pm.degree(V, y) == 0);
    
    // update the ideal, and start with y
    ideal.set_degree(y, 1);
    unsigned current_d = 1;                 
    zp_polynomial_ref current_power(zp_pm); 
    current_power = zp_pm.mk_polynomial(y);
    
    // lift quadratic until we are over the asked for
    while (current_d < d) {
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "zp_pm = Z_" << nm.to_string(zp_pm.m().p()) << endl;
              tout << "ideal = " << ideal << endl;
              tout << "C = " << C << endl;
              tout << "A = " << A << endl;
              tout << "B = " << B << endl;
              );
        
        // again, classic hensel:
        // since C = A*B mod (p, ideal, y^k) we know that (C - A*B) = 0 mod (p, ideal, y^k)
        // f = (C - A*B) mod (p, ideal, y^k) and thus divisible by y^current_d = current_power
        zp_polynomial_ref f(zp_pm);
        f = zp_pm.mul(A, B); 
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "zp_pm = Z_" << nm.to_string(zp_pm.m().p()) << endl;
              tout << "ideal = " << ideal << endl;
              tout << "C = " << C << endl;
              tout << "A = " << A << endl;
              tout << "B = " << B << endl;
              tout << "f = " << f << endl;
              );
        
        f = zp_pm.sub(C, f); 
        f = zp_pm.exact_div(f, current_power); 
        f = zp_pm.mod_d(f, ideal);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "A = " << A << endl;
              tout << "B = " << B << endl;
              );
    
        // get the S, T, solution to A*S+B*T = f, with d(T, x) < d(A, x)
        // but we know that S = U*f + Bt, T = V*f - At, so we do division
        zp_polynomial_ref S(zp_pm), T(zp_pm);
        solve<zp_manager>(zp_pm, x, ideal, A, U, B, V, f, zp_pm, S, T);
        // now, lets lift A and B
        // we want A1 = A + T*y^d, B1 = B + S*y^d with A1*B1 = C mod (ideal, y^(2*k))
        // hence A*B + y^d*(A*S+B*T) = C
        S = zp_pm.mul(S, current_power); 
        T = zp_pm.mul(T, current_power);         
        A = zp_pm.add(A, T);
        B = zp_pm.add(B, S);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "A = " << A << endl;
              tout << "B = " << B << endl;
              );
        
        // again, classic quadratic hensel
        // we need A*U1 + B*V1 = 1 mod (p, ideal, y^2), from above
        // U1 = U + S*y^d, V1 = V + T*y^d, hence A*U + B*V + y^d(S + T) = 1 mod new ideal^2
        // we know that y^d divides (1-UA-BV) so we compute f = (1-UA-BV)/y^d
        // UA + VB + y^d(SA + TB) = 1 (mod ideal^2) 
        // SA + TB = f (mod ideal) 
        // we solve for S, T again, and do as above
        zp_polynomial_ref UA(zp_pm), BV(zp_pm);
        f = zp_pm.mk_const(one);
        UA = zp_pm.mul(U, A); 
        BV = zp_pm.mul(V, B);
        f = zp_pm.sub(f, UA); f = zp_pm.sub(f, BV);

        TRACE("polynomial::factorization::multivariate", 
              tout << "ideal = " << ideal << endl;
              tout << "current_power = " << current_power << endl;
              tout << "UA = " << UA << endl;
              tout << "BV = " << BV << endl;
              tout << "f = " << f << endl;
              tout << "x = x" << x << endl;
              tout << "y = x" << y << endl;
              );
        
        f = zp_pm.exact_div(f, current_power);    
        f = zp_pm.mod_d(f, ideal);
        
        // get the S, T, solution to A*S+B*T = f, with d(T, x) < d(A, x)
        solve<zp_manager>(zp_pm, x, ideal, A, U, B, V, f, zp_pm, S, T);
        // now, lets lift U and V
        S = zp_pm.mul(S, current_power);
        U = zp_pm.add(U, S);
        T = zp_pm.mul(T, current_power); 
        V = zp_pm.add(V, T);

        // lift the ideal
        current_d *= 2;
        current_power = zp_pm.mul(current_power, current_power);
        ideal.set_degree(y, current_d);

        // move, A, B, C, D into the ideal
        A = zp_pm.mod_d(A, ideal);
        B = zp_pm.mod_d(B, ideal);
        S = zp_pm.mod_d(S, ideal);
        T = zp_pm.mod_d(T, ideal);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "current_d = " << d << endl;
              tout << "zp_pm is Z_" << zp_pm.m().m().to_string(zp_pm.m().p()) << endl;
              tout << "x = x" << x << endl;
              tout << "y = x" << y << endl;
              tout << "C = " << C << endl;
              tout << "A = " << A << endl;
              tout << "B = " << B << endl;
              tout << "U = " << U << endl;
              tout << "V = " << V << endl;
              tout << "ideal = " << ideal << endl;
              );
        
        SASSERT(check_solve(zp_pm, ideal, A, B, one_p, U, V));
    }
}

template<typename manager_to_check, typename manager_1, typename manager_2>
bool are_equal_in(
    manager_to_check pm, 
    typename manager_1::polynomial_ref const & A, 
    typename manager_2::polynomial_ref const & B) {
    typename manager_to_check::polynomial_ref A_pm(pm), B_pm(pm);
    
    A_pm = convert(A.m(), A, pm);
    B_pm = convert(B.m(), B, pm);
    
    bool equal = pm.eq(A_pm, B_pm);
    return equal;
}
    
/**
   C: target multivariate polynomial mod ideal, p^e, the manager is in p^e
   x: main variable
   A, B, U, V: univariate polynomials in Z_p[x] such that U*A+B*V=1 mod ideal, these guys managers are in Z_p

   output: A_lifted, B_lifted, A = A_lifted mod ideal
   A_lifted*B_lifted = f mod x_i^d_i, p^e
*/
void multivariate_hansel_lift_zp(
    manager & pm, zp_manager & zp_pm, zp_manager & zpe_pm,
    zp_polynomial_ref const & C_pe, var x, unsigned e,
        zp_polynomial_ref const & A_p, zp_polynomial_ref const & U_p, 
        zp_polynomial_ref const & B_p, zp_polynomial_ref const & V_p,
    var2degree const & ideal, 
    zp_polynomial_ref & A_lifted, zp_polynomial_ref & B_lifted) {
    TRACE("polynomial::factorization::multivariate", 
          tout << "polynomial::multiratiate_hensel_lift_zp:" << endl;
          tout << "zp_pm = Z_" << zp_pm.m().m().to_string(zp_pm.m().p()) << endl;
          tout << "zpe_pm = Z_" << zpe_pm.m().m().to_string(zpe_pm.m().p()) << endl;            
          tout << "x = x" << x << endl;
          tout << "ideal = " << ideal << endl;
          tout << "C_pe = " << C_pe << "," << endl;
          tout << "A_p = " << A_p << "," << endl;
          tout << "B_p = " << B_p << "," << endl;
          );
    
    // fixed zpe_pm
    // upolynomial::zp_numeral_manager & zpe_nm = zpe_pm.m();
    // numeral const & pe = zpe_nm.p();
    // fixed zp_pm
    upolynomial::zp_numeral_manager & zp_nm = zp_pm.m();
    numeral const & p = zp_nm.p();
    // regular numeral manager and mangager
    numeral_manager & nm = zp_nm.m();
    
    // sliding zpk_pm mod p^k
    upolynomial::zp_numeral_manager zpk_nm(nm, p);
    zp_manager zpk_pm(zpk_nm, &zp_pm.mm()); // in the end we copy the result over to zpe
    unsigned k = 1;
    upolynomial::scoped_numeral pk(nm);
    nm.set(pk, zpk_nm.p());
    
    // constant 1
    scoped_numeral one(nm);
    nm.set(one, 1);
    zp_polynomial_ref one_p(zpk_pm);
    one_p = zpk_pm.mk_const(one);
    
    // lift until you get over the requested power of e
    zp_polynomial_ref A_pk(zpk_pm), B_pk(zpk_pm), U_pk(zpk_pm), V_pk(zpk_pm);
    
    A_pk = convert(zp_pm, A_p, zpk_pm); 
    B_pk = convert(zp_pm, B_p, zpk_pm);
    U_pk = convert(zp_pm, U_p, zpk_pm);
    V_pk = convert(zp_pm, V_p, zpk_pm);
    
    TRACE("polynomial::factorization::multivariate",             
          tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;            
          tout << "A_pk = " << A_pk << endl;
          tout << "B_pk = " << B_pk << endl;
          tout << "U_pk = " << U_pk << endl;
          tout << "V_pk = " << V_pk << endl;
          );
    
    SASSERT(check_solve(zpk_pm, ideal, A_pk, B_pk, one_p, U_pk, V_pk));
    
    while (k < e) {
        
        // standard hensel:
        // (C - AB) and is divisible by p^k, so we compute f = (C - AB)/p^k mod ideal in Z[...]
        zp_polynomial_ref f_pk(zpk_pm);
        polynomial_ref A_pk_in_Z(pm), B_pk_in_Z(pm), AB_in_Z(pm), f_in_Z(pm);
        f_in_Z = convert(zpe_pm, C_pe, pm);
        A_pk_in_Z = convert(zpk_pm, A_pk, pm);
        B_pk_in_Z = convert(zpk_pm, B_pk, pm);
        AB_in_Z = pm.mul(A_pk_in_Z, B_pk_in_Z); 
        AB_in_Z = pm.mod_d(AB_in_Z, ideal);
        f_in_Z = pm.sub(f_in_Z, AB_in_Z); 
        f_in_Z = pm.exact_div(f_in_Z, pk);
        f_in_Z = pm.mod_d(f_in_Z, ideal);
        f_pk = convert(pm, f_in_Z, zpk_pm);
        
        TRACE("polynomial::factorization::multivariate",             
              tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;            
              tout << "f_pk = " << f_pk << endl;
              );
        
        // standard hensel we need to lift to p^(2k)
        // we have U*A+V*B = 1, C = A*B, so p^k divides C - AB
        // we want A1 = A + p^k*S, B1 = B + p^k*T, and also        
        // C - (A + p^k*S)*(B + p^k*T) = 0 mod (p^2k)        
        // C - A*B = p^k (T*A + S*B), i.e.
        // f = (C - A*B)/p^k = (T*A + S*B), so we solve this equation in Z_p^k
        polynomial_ref S_in_Z(pm), T_in_Z(pm);
        solve<manager>(zpk_pm, x, ideal, A_pk, U_pk, B_pk, V_pk, f_pk, pm, T_in_Z, S_in_Z);
        
        TRACE("polynomial::factorization::multivariate",             
              tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;            
              tout << "S_in_Z = " << S_in_Z << endl;
              tout << "T_in_Z = " << T_in_Z << endl;
              );
        
        // lift A and B to, A = A + p^k*S, B = B + p^k*T
        polynomial_ref A_next_in_Z(pm), B_next_in_Z(pm);
        S_in_Z = pm.mul(pk, S_in_Z); 
        S_in_Z = pm.mod_d(S_in_Z, ideal);
        A_next_in_Z = convert(zpk_pm, A_pk, pm);
        A_next_in_Z = pm.add(A_next_in_Z, S_in_Z);
        T_in_Z = pm.mul(pk, T_in_Z); 
        T_in_Z = pm.mod_d(T_in_Z, ideal);
        B_next_in_Z = convert(zpk_pm, B_pk, pm);
        B_next_in_Z = pm.add(B_next_in_Z, T_in_Z);
        
        TRACE("polynomial::factorization::multivariate",             
              tout << "pk = " << nm.to_string(pk) << endl;            
              tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;            
              tout << "S_in_Z = " << S_in_Z << endl;
              tout << "T_in_Z = " << T_in_Z << endl;
              tout << "A_pk = " << A_pk << endl;
              tout << "B_pk = " << B_pk << endl;
              tout << "A_next_in_Z = " << A_next_in_Z << endl;
              tout << "B_next_in_Z = " << B_next_in_Z << endl;
              );
        
        bool eq1 = are_equal_in<zp_manager, manager, zp_manager>(zpk_pm, A_next_in_Z, A_pk);
        SASSERT(eq1);
        bool eq2 = are_equal_in<zp_manager, manager, zp_manager>(zpk_pm, B_next_in_Z, B_pk);
        SASSERT(eq2);
        
        // again, classic quadratic hensel
        // we need A*U1 + B*V1 = 1 mod p^2k, from above
        // U1 = U + p^k*S, V1 = V + p^k*T, hence A*U + B*V + p^k*(S + T) = 1 mod (p^2k)
        // we know that p^k divides (1-UA-BV) so we compute f = (1-UA-BV)/p^k
        // UA + VB + p^k(SA + TB) = 1 (mod p^k) 
        // SA + TB = f (mod ideal) 
        // we solve for S, T again, and do as above
        polynomial_ref U_pk_in_Z(pm), V_pk_in_Z(pm), UA_in_Z(pm), BV_in_Z(pm);
        U_pk_in_Z = convert(zpk_pm, U_pk, pm);
        V_pk_in_Z = convert(zpk_pm, V_pk, pm);
        f_in_Z = pm.mk_const(one);
        UA_in_Z = pm.mul(U_pk_in_Z, A_next_in_Z); 
        UA_in_Z = pm.mod_d(UA_in_Z, ideal);
        BV_in_Z = pm.mul(V_pk_in_Z, B_next_in_Z); 
        BV_in_Z = pm.mod_d(BV_in_Z, ideal);
        f_in_Z = pm.sub(f_in_Z, UA_in_Z); 
        f_in_Z = pm.sub(f_in_Z, BV_in_Z);
        
        TRACE("polynomial::factorization::multivariate",
              tout << "pk = " << nm.to_string(pk) << endl;
              tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;
              tout << "U_pk_in_Z = " << U_pk_in_Z << endl;
              tout << "V_pk_in_Z = " << V_pk_in_Z << endl;
              tout << "UA_in_Z = " << UA_in_Z << endl;
              tout << "BV_in_Z = " << BV_in_Z << endl;
              tout << "f_in_Z = " << f_in_Z << endl;
              );
        
        f_in_Z = pm.exact_div(f_in_Z, pk); 
        f_pk = convert(pm, f_in_Z, zpk_pm);
        
        // get the S, T, solution to A*S+B*T = f, with d(T, x) < d(A, x)
        solve<manager>(zpk_pm, x, ideal, A_pk, U_pk, B_pk, V_pk, f_pk, pm, S_in_Z, T_in_Z);

        TRACE("polynomial::factorization::multivariate", 
              tout << "pk = " << nm.to_string(pk) << endl;
              tout << "zpk_pm = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;
              tout << "S_in_Z = " << S_in_Z << endl;
              tout << "T_in_Z = " << T_in_Z << endl;
              );
        
        // go to the next zpk
        scoped_numeral next_pk(nm);
        nm.mul(pk, pk, next_pk);
        zpk_nm.set_p(next_pk);

        TRACE("polynomial::factorization::multivariate", 
              tout << "zp_pk = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;
              );
        
        // lift U
        zp_polynomial_ref S_pk(zpk_pm);
        S_in_Z = pm.mul(pk, S_in_Z);
        S_pk = convert(pm, S_in_Z, zpk_pm);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "S_pk = " << S_pk << endl;
              );
        
        U_pk = zpk_pm.add(U_pk, S_pk);
        // lift V
        zp_polynomial_ref T_pk(zpk_pm);
        T_in_Z = pm.mul(pk, T_in_Z); 
        T_pk = convert(pm, T_in_Z, zpk_pm);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "T_pk = " << T_pk << endl;
              );
        
        V_pk = zpk_pm.add(V_pk, T_pk);
        
        // lift A and B
        TRACE("polynomial::factorization::multivariate", 
              tout << "A_pk_in_Z = " << A_pk_in_Z << endl;
              tout << "B_pk_in_Z = " << B_pk_in_Z << endl;
              );
        A_pk = convert(pm, A_pk_in_Z, zpk_pm);
        B_pk = convert(pm, B_pk_in_Z, zpk_pm);
        
        // move to the next pk
        k *= 2;
        nm.set(pk, next_pk);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "zp_pk = Z_" << zpk_pm.m().m().to_string(zpk_pm.m().p()) << endl;
              tout << "A_pk = " << A_pk << endl;
              tout << "B_pk = " << B_pk << endl;
              tout << "U_pk = " << U_pk << endl;
              tout << "V_pk = " << V_pk << endl;
              tout << "C_pe = " << C_pe << endl;
              );
        
        SASSERT(check_solve(zpk_pm, ideal, A_pk, B_pk, one_p, U_pk, V_pk));
    } 
    
    // now convert to the non-sliding zpe_manager 
    SASSERT(k == e);
    A_lifted = convert(zpk_pm, A_pk, zpe_pm);
    B_lifted = convert(zpk_pm, B_pk, zpe_pm);
}
    
/**
   f: target multivariate polynomial mod x_i^d_i, p^e
   x: main variable
   all_vars: all variables (including x)
   A, B, U, V: univariate polynomials in Z_p[x] such that U*A+B*V=1 from ext gcd

   output: A_lifted, B_lifted d(A) = d(A_lifted), A = A_lifted mod x_i^d_i, p
   A_lifted*B_lifted = f mod x_i^d_i, p^e
*/
void multivariate_hensel_lift(
    manager & pm, zp_manager & zp_pm, zp_manager & zpe_pm,
        zp_polynomial_ref const & f, var x, unsigned e, var_vector const & all_vars,
        upolynomial::zp_manager & zp_upm, 
        upolynomial::numeral_vector const & U, upolynomial::numeral_vector const & A, 
        upolynomial::numeral_vector const & V, upolynomial::numeral_vector const & B, 
        var2degree & target_ideal, zp_polynomial_ref & A_lifted, zp_polynomial_ref & B_lifted) {    
    upolynomial::zp_numeral_manager & zp_nm = zp_upm.m();
    upolynomial::numeral_manager & nm = zp_nm.m();
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "polynomial::multiratiate_hensel_lift(" << endl;
          tout << "f = " << f << "," << endl;
          tout << "x = x" << x << "," << endl;
          tout << "e = " << e << "," << endl;
          tout << "U = "; zp_upm.display(tout, U); tout << "," << endl;
          tout << "A = "; zp_upm.display(tout, A); tout << "," << endl;
          tout << "V = "; zp_upm.display(tout, V); tout << "," << endl;
          tout << "B = "; zp_upm.display(tout, B); tout << "," << endl;
          tout << "target_ideal = " << target_ideal << "," << endl;
          tout << "p = " << nm.to_string(zp_pm.m().p()) << endl;
          tout << "pe = " << nm.to_string(zpe_pm.m().p()) << endl;
          );
    
    // multivariate versions of A, B, U, V that we keep lifting over ideal x_i^d_i
    zp_polynomial_ref A_m_p(zp_pm), B_m_p(zp_pm), U_m_p(zp_pm), V_m_p(zp_pm);
    A_m_p = zp_pm.to_polynomial(A, x);
    B_m_p = zp_pm.to_polynomial(B, x);
    U_m_p = zp_pm.to_polynomial(U, x);
    V_m_p = zp_pm.to_polynomial(V, x);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "A_m_p = " << A_m_p << endl;
          tout << "B_m_p = " << B_m_p << endl;
          tout << "U_m_p = " << U_m_p << endl;
          tout << "V_m_p = " << V_m_p << endl;
          );
    
    // the the target in Z_p[...]        
    zp_polynomial_ref C_m_p(zp_pm);
    C_m_p = convert(zpe_pm, f, zp_pm);
    
    // lift each variable individually
    var2degree lifted_ideal;
    unsigned_vector lifted_degs;
    for (unsigned i = 0; i < all_vars.size(); ++ i) {
        if (all_vars[i] == x) {
            // skip the main variable
            continue;
        }        
        // current variable and degree we are lifting to, y^(d_y), at least
        var y = all_vars[i];
        // lift to y^(d_y)
        multivariate_hansel_lift_ideal(zp_pm, x, C_m_p, A_m_p, U_m_p, B_m_p, V_m_p, lifted_ideal, y, target_ideal.degree(y));
    }

    TRACE("polynomial::factorization::multivariate", 
          tout << "A_m_p = " << A_m_p << endl;
          tout << "B_m_p = " << B_m_p << endl;
          tout << "U_m_p = " << U_m_p << endl;
          tout << "V_m_p = " << V_m_p << endl;
          tout << "lifted_ideal = " << lifted_ideal << endl;
          );
    
    // now lift it all to p^e
    multivariate_hansel_lift_zp(pm, zp_pm, zpe_pm, f, x, e, A_m_p, U_m_p, B_m_p, V_m_p, lifted_ideal, A_lifted, B_lifted);
}
    

/**
    f: multivariate polynomial
    x: main variable
    all_vars: all variables (including x)
    f_u: f mod x_1, ..., x_n (excluding mod x), i.e. this is f(0, x), f_u is square_free
    f_u_zp_factors: monic factors of f_u (mod p), pairvise gcd = 1

    we're lifting the factors to mod x_1^d_1, ..., x_n&d_n (excliding x), mod p^e
    i.e. such that f congruent to the new factors. output goes to f_zpe factors.
*/
void multivariate_hensel_lift(
    manager & pm, zp_manager & zp_pm, zp_manager & zpe_pm,
        polynomial_ref const & f, var x, unsigned e, var_vector const & all_vars, 
        upolynomial::manager & upm, upolynomial::numeral_vector const & f_u, 
        upolynomial::zp_factors const & f_u_zp_factors, 
        var2degree & target_ideal,
        zp_factors & f_zpe_factors) {
    SASSERT(f_u_zp_factors.distinct_factors() > 1);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "polynomial::multivariate_hensel_lift(" << endl;
          tout << "f = " << f << "," << endl;
          tout << "x = x" << x << "," << endl;
          tout << "e = " << e << "," << endl;
          tout << "f_u = "; upm.display(tout, f_u); tout << "," << endl;
          tout << "f_u_zp_factors" << f_u_zp_factors << "," << endl;
          tout << "target_ideal = " << target_ideal << "," << endl;
          tout << "f_zpe_factors = " << f_zpe_factors << ")" << endl;
          );
    
    // managers and all
    numeral_manager & nm = pm.m();
    upolynomial::zp_manager & zp_upm = f_u_zp_factors.upm();
    // upolynomial::zp_numeral_manager & zp_nm = zp_upm.m();    
    upolynomial::zp_numeral_manager & zpe_nm = zpe_pm.m();
    upolynomial::zp_manager zpe_upm(zpe_nm);
    
    // the targed product we want (mod x_i^d_i, mod p^e)
    zp_polynomial_ref f_target_zpe(zpe_pm);
    f_target_zpe = convert(pm, f, zpe_pm);
    f_target_zpe = zpe_pm.mod_d(f_target_zpe, target_ideal);
    
    TRACE("polynomial::factorization::multivariate", 
        tout << "target_ideal = " << target_ideal << endl;
        tout << "f_target_zpe = " << f_target_zpe << endl;
    );

    // we do the product by doing individual lifting like in the univarate case
    zp_polynomial_ref B(zp_pm), C_p(zp_pm);
    zp_polynomial_ref A_lifted(zpe_pm), B_lifted(zpe_pm);
    upolynomial::scoped_numeral_vector B_u(nm), C_u(nm), tmp_u(nm);
    upolynomial::scoped_numeral_vector U(nm), V(nm);
    for (int i = 0, i_end = f_u_zp_factors.distinct_factors() - 1; i < i_end; ++ i) 
    {        
        // get the univarate ones to lift now
        upolynomial::numeral_vector const & A_u = f_u_zp_factors[i];
        // current starting product is f_target_zpe(0, x) in *Z_p*
        zp_upm.to_numeral_vector(f_target_zpe, x, C_u);
        // we get the rest into B (mod p)
        zp_upm.exact_div(C_u, A_u, B_u);
        
        TRACE("polynomial::factorization::multivariate", 
              tout << "p = " << nm.to_string(zp_upm.m().p()) << endl;
              tout << "f_target_zpe = " << f_target_zpe << endl;
              tout << "A_u = "; upm.display(tout, A_u); tout << endl;
              tout << "B_u = "; upm.display(tout, B_u); tout << endl;
              tout << "C_u = "; upm.display(tout, C_u); tout << endl;
              );
        
        // and get the U, V, such that A*U+B*V = 1
        zp_upm.ext_gcd(A_u, B_u, U, V, tmp_u);
        
        TRACE("polynomial::factorization::multivariate",             
              tout << "U = "; upm.display(tout, U); tout << endl;
              tout << "V = "; upm.display(tout, V); tout << endl;
              tout << "gcd = "; upm.display(tout, tmp_u); tout << endl;
              );
        
        // do the lifting for this pair
        multivariate_hensel_lift(pm, zp_pm, zpe_pm, f_target_zpe, x, e, all_vars, zp_upm, U, A_u, V, B_u, target_ideal, A_lifted, B_lifted);
        
        // add the lifted A to the output
        f_zpe_factors.push_back(A_lifted, 1);    
        // move to the new target by dividing with the lifted A
        f_target_zpe = zpe_pm.exact_div(f_target_zpe, A_lifted);
    }
    
    // add the last f_target
    f_zpe_factors.push_back(f_target_zpe, 1);    
}

class mfactorization_combination_iterator : public upolynomial::factorization_combination_iterator_base<zp_factors> {
    
    /** main variable */
    var m_x;
    
public:
    
    mfactorization_combination_iterator(zp_factors const & factors, var x)
        : upolynomial::factorization_combination_iterator_base<zp_factors>(factors)
    {}
    
    /**
       \brief Filter the ones not in the degree set.
    */
    bool filter_current() const {
        return false;
    }
    
    /** 
        \brief Returns the degree of the current selection.
    */
    unsigned current_degree() const {
        unsigned degree = 0;
        zp_manager & pm = m_factors.pm();
        for (unsigned i = 0; i < left_size(); ++ i) {
            degree += pm.degree(m_factors[m_current[i]], m_x);
        }
        return degree;
    } 
    
    void left(zp_polynomial_ref & out) const {
        SASSERT(m_current_size > 0);
        zp_manager & zp_pm = m_factors.pm();
        out = m_factors[m_current[0]];
        for (int i = 1; i < m_current_size; ++ i) {
            out = zp_pm.mul(out, m_factors[m_current[i]]);
        }
    }
    
    void get_left_tail_coeff(numeral const & m, numeral & out) {
        zp_manager & zp_pm = m_factors.pm();
        upolynomial::zp_numeral_manager & zp_nm = zp_pm.m();
        zp_nm.set(out, m);
        for (int i = 0; i < m_current_size; ++ i) {                
            zp_nm.mul(out, zp_pm.numeral_tc(m_factors[m_current[i]]), out);
        }
    }
    
    void get_right_tail_coeff(numeral const & m, numeral & out) {
        zp_manager & zp_pm = m_factors.pm();
        upolynomial::zp_numeral_manager & zp_nm = zp_pm.m();
        zp_nm.set(out, m);
        
        unsigned current = 0;
        unsigned selection_i = 0;
        
        // selection is ordered, so we just take the ones in between that are not disable
        while (current <  m_factors.distinct_factors()) {
            if (!m_enabled[current]) {
                // by skipping the disabled we never skip a selected one
                current ++;
            } else {   
                if (selection_i >= m_current.size() || (int) current < m_current[selection_i]) {
                    SASSERT(m_factors.get_degree(current) == 1);
                    zp_nm.mul(out, zp_pm.numeral_tc(m_factors[current]), out);
                    current ++;
                } else {
                    current ++;
                    selection_i ++;
                }
            }
        }
    }
    
    void right(zp_polynomial_ref & out) const {
        SASSERT(m_current_size > 0);
        zp_manager & zp_pm = m_factors.pm();
        upolynomial::zp_numeral_manager & zp_nm  = zp_pm.m();
        
        unsigned current = 0;
        unsigned selection_i = 0;
        
        numeral one;
        zp_nm.set(one, 1);
        out = zp_pm.mk_const(one);
        
        // selection is ordered, so we just take the ones in between that are not disable
        while (current <  m_factors.distinct_factors()) {
            if (!m_enabled[current]) {
                // by skipping the disabled we never skip a selected one
                current ++;
            } else {   
                if (selection_i >= m_current.size() || (int) current < m_current[selection_i]) {
                    SASSERT(m_factors.get_degree(current) == 1);
                    out = zp_pm.mul(out, m_factors[current]);
                    current ++;
                } else {
                    current ++;
                    selection_i ++;
                }
            }
        }
    }
};
    
    
// the multivariate factorization
bool factor_square_free_primitive(polynomial_ref const & f, factors & f_factors) {

    TRACE("polynomial::factorization", tout << "polynomial::factor_square_free_primitive(f = " << f << ", factors = " << f_factors << ")" << endl;);
    
    manager & pm = f.m();
    numeral_manager & nm = pm.m();

    // to start with, maybe this should be part of input
    var x = pm.max_var(f);
    // get all the variables
    var_vector vars, vars_no_x;    
    pm.vars(f, vars);       
    for(unsigned i = 0; i < vars.size(); ++ i) {
        if (vars[i] != x) {
            vars_no_x.push_back(vars[i]);
        }
    }
    SASSERT(vars.size() > 1);
    
    // degree of the main variable
    unsigned x_degree = pm.degree(f, x);
    // the leading coefficient 
    polynomial_ref f_lc(pm);
    f_lc = pm.coeff(f, x, x_degree);

    // the vector of values we substitute
    upolynomial::scoped_numeral_vector a(nm);

    // the univariate polynomial
    upolynomial::manager upm(nm);
    upolynomial::scoped_numeral_vector f_u(upm);

    // generate the values to substitute and substitute them to get f_u(x) = f(a, x), the univariate version of f
    unsigned size = 1;
    a.resize(vars_no_x.size());
    for (unsigned i = 0; i < a.size(); ++ i) { nm.reset(a[i]); }
    generate_substitution_values(f, x, f_lc, vars_no_x, size, a, upm, f_u);    

    TRACE("polynomial::factorization::multivariate", 
          tout << "f_u = "; upm.display(tout, f_u); tout << endl;
          tout << "substitution:" << endl;
          for (unsigned i = 0; i < vars_no_x.size(); ++ i) {
              tout << "x" << vars[i] << " -> " << nm.to_string(a[i]) << endl;
          });
    
    // the primitive part of f_u
    scoped_numeral f_u_lc(nm);
    upolynomial::scoped_numeral_vector f_u_pp(nm);
    upm.get_primitive_and_content(f_u, f_u_pp, f_u_lc);

    TRACE("polynomial::factorization::multivariate", 
          tout << "f_u_lc" << nm.to_string(f_u_lc) << endl;
          tout << "f_u_pp = "; upm.display(tout, f_u_pp); tout << endl;
          );
    
    // factor the univariate one
    upolynomial::factors factors_u(upm);
    upolynomial::factor_square_free(upm, f_u, factors_u);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "factors_u = " << factors_u << endl;
          );
    
    // if there is no univariate factors, it's irreducible
    if (factors_u.distinct_factors() == 1) {
        f_factors.push_back(f, 1);
        return false;
    }
    
    // translate f with a, so that we work modulo x_i^k and not (x_i - a_i)^k
    polynomial_ref f_t(pm);
    // Do the translation, we must have that a[x] = 0
    pm.translate(f, vars_no_x, a, f_t);
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "f_t = " << f_t << endl;
          );
    
    // the zp manager stuff, we'll be changing the base
    upolynomial::zp_numeral_manager zp_nm(nm, 2);
    upolynomial::zp_manager zp_upm(zp_nm);

    // get the first prime number p that keeps f square-free
    scoped_numeral p(nm);
    prime_iterator prime_it;
    upolynomial::scoped_numeral_vector f_u_pp_zp(nm);
    do {
        // create Z_p with the next prime
        nm.set(p, prime_it.next());
        // translate to Zp[x]
        zp_nm.set_p(p);    
        upolynomial::to_zp_manager(zp_upm, f_u_pp, f_u_pp_zp);
    } while (!zp_upm.is_square_free(f_u_pp_zp));
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "p = " << p << endl;
          tout << "f_t = " << f_t << endl;
          );
    
    // convert factors of f to factors modulo p (monic ones)
    upolynomial::zp_factors factors_u_zp(zp_upm);
    upolynomial::scoped_numeral_vector current_factor(nm);
    for (unsigned i = 0; i < factors_u.distinct_factors(); ++ i) {
        upolynomial::to_zp_manager(zp_upm, factors_u[i], current_factor);
        zp_upm.mk_monic(current_factor);
        factors_u_zp.push_back_swap(current_factor, 1);
    }
    
    TRACE("polynomial::factorization::multivariate", 
          tout << "factors_u_zp = " << factors_u_zp << endl;
          );
    
    // compute factor coefficient bound (pover p^e) of the translated f with the leading coefficient added, i.e. 
    // f_t*lc(f_t, x) = f_t*lc(f, x)
    unsigned e;
    scoped_numeral p_e(nm);
    var2degree target_ideal;
    upolynomial::scoped_numeral f_t_lc(nm);
    nm.set(f_t_lc, pm.numeral_lc(f_t, x));
    polynomial_ref f_t_with_lc(pm);
    f_t_with_lc = pm.mul(f_t_lc, f_t);
    multivariate_factor_coefficient_bound(f_t_with_lc, x, p, e, p_e, target_ideal);

    TRACE("polynomial::factorization::multivariate", 
          tout << "target_ideal = " << target_ideal << endl;
          );
    
    // do the multivariate lifting of the translated one f_t
    upolynomial::zp_numeral_manager zpe_nm(nm, p_e);
    zp_manager zpe_pm(zpe_nm, &pm.mm());
    zp_manager zp_pm(zp_nm, &pm.mm());
    zp_factors factors_zpe(zpe_pm);
    multivariate_hensel_lift(pm, zp_pm, zpe_pm, f_t, x, e, vars, upm, f_u_pp_zp, factors_u_zp, target_ideal, factors_zpe);

    TRACE("polynomial::factorization::multivariate", 
        tout << "factors_zpe = " << factors_zpe << endl;
          );
    
    // try the factors from the lifted combinations
    factors f_t_factors(pm);
    bool remove = false;
    mfactorization_combination_iterator it(factors_zpe, x);
    unsigned max_degre = pm.degree(f_t, x) / 2;
    zp_polynomial_ref zpe_trial_factor(zpe_pm);    
    while (it.next(remove)) {
        //
        // our bound ensures we can extract the right factors of degree at most 1/2 of the original
        // so, if out trial factor has degree bigger than 1/2, we need to take the rest of the factors
        // but, if we take the rest and it works, it doesn't meen that the rest is factorized, so we still take out
        // the original factor
        //
        bool using_left = it.current_degree() <= max_degre;
        if (using_left) {
            // do a quick check first
            it.left(zpe_trial_factor);
        } else {
            // do a quick check first
            it.right(zpe_trial_factor);
        }
        // add the lc(f_pp) to the trial divisor
        zpe_trial_factor = zpe_pm.mul(f_t_lc, zpe_trial_factor);        
        polynomial_ref trial_factor(pm), trial_factor_quo(pm);
        trial_factor = convert(zpe_pm, zpe_trial_factor, pm);
        bool true_factor = true;
        trial_factor_quo = pm.exact_div(f_t_with_lc, trial_factor);        
        // if division is precise we have a factor
        if (true_factor) {
            if (!using_left) {
                // as noted above, we still use the original factor
                trial_factor.swap(trial_factor_quo);
            }
            // We need to get the content out of the factor 
            upolynomial::scoped_numeral trial_factor_cont(nm);
            pm.int_content(f_t, trial_factor_cont);
            trial_factor = pm.exact_div(trial_factor, trial_factor_cont);
            // add the factor
            f_t_factors.push_back(trial_factor, 1);
            // we continue with the int-primitive quotient (with the lc added back)
            // but we also have to keep lc(f_t)*f_t
            pm.int_content(trial_factor_quo, f_t_lc); // content
            trial_factor_quo = pm.exact_div(trial_factor_quo, f_t_lc);
            nm.set(f_t_lc, pm.numeral_lc(trial_factor_quo, x));
            f_t = pm.mul(f_t_lc, trial_factor_quo);
            // but we also remove it from the iterator
            remove = true;
        } else {
            // don't remove this combination
            remove = false;
        }
    }

    // translate the factor back
    for (unsigned i = 0; i < a.size(); ++ i) {
        nm.neg(a[i]);
    }
    for (unsigned i = 0; i < f_t_factors.distinct_factors(); ++ i) {
        polynomial_ref factor(pm);
        pm.translate(f_t_factors[i], vars_no_x, a, factor);
        f_factors.push_back(factor, 1); 
    }

    TRACE("polynomial::factorization", tout << "polynomial::factor_square_free_primitive(f = " << f << ") => " << f_factors << endl;);
    return true;
}

}; // end polynomial namespace

#endif
