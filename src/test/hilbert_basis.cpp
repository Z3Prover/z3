#include "hilbert_basis.h"


static vector<rational> vec(int i, int j, int k) {
    vector<rational> nv;
    nv.resize(3);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    return nv;
}

static vector<rational> vec(int i, int j, int k, int l) {
    vector<rational> nv;
    nv.resize(4);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    nv[3] = rational(l);
    return nv;
}

static vector<rational> vec(int i, int j, int k, int l, int x, int y, int z) {
    vector<rational> nv;
    nv.resize(7);
    nv[0] = rational(i);
    nv[1] = rational(j);
    nv[2] = rational(k);
    nv[3] = rational(l);
    nv[4] = rational(x);
    nv[5] = rational(y);
    nv[6] = rational(z);
    return nv;
}

static void saturate_basis(hilbert_sl_basis& hb) {
    lbool is_sat = hb.saturate();

    switch(is_sat) {
    case l_true:  
        std::cout << "sat\n"; 
        hb.display(std::cout);
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    case l_undef: 
        std::cout << "undef\n"; 
        break;       
    }
    statistics st;
    hb.collect_statistics(st);
    st.display(std::cout);
}


static void saturate_basis(hilbert_basis& hb) {
    lbool is_sat = hb.saturate();

    switch(is_sat) {
    case l_true:  
        std::cout << "sat\n"; 
        hb.display(std::cout);
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    case l_undef: 
        std::cout << "undef\n"; 
        break;       
    }
    statistics st;
    hb.collect_statistics(st);
    st.display(std::cout);
}


// example 9, Ajili, Contenjean
// x + y - 2z = 0
// x - z = 0
// -y + z <= 0

static void tst1() {
    hilbert_basis hb;
    hb.add_eq(vec(1,1,-2));
    hb.add_eq(vec(1,0,-1));
    hb.add_le(vec(0,1,-1));
    saturate_basis(hb);
}


// example 10, Ajili, Contenjean
// 23x - 12y - 9z <= 0
// x   - 8y  - 8z <= 0
void tst2() {
    hilbert_basis hb;

    hb.add_eq(vec(-23,12,9));
    hb.add_eq(vec(-1,8,8));

    saturate_basis(hb);
}

// example 6, Ajili, Contenjean
// 3x + 2y - z - 2u <= 0
static void tst3() {
    hilbert_basis hb;
    hb.add_le(vec(3,2,-1,-2));
    saturate_basis(hb);
}

#define R rational

// Sigma_1, table 1, Ajili, Contejean
static void tst4() {
    hilbert_sl_basis hb;
    hb.add_le(vec( 0,-2, 1, 3, 2,-2, 3), R(3));
    hb.add_le(vec(-1, 7, 0, 1, 3, 5,-4), R(2));
    hb.add_le(vec( 0,-1, 1,-1,-1, 0, 0), R(2));
    hb.add_le(vec(-2, 0, 1, 4, 0, 0,-2), R(1));
    hb.add_le(vec(-3, 2,-2, 2,-4,-1, 0), R(8));
    hb.add_le(vec( 3,-2, 2,-2, 4, 1, 0), R(3));
    hb.add_le(vec( 1, 0, 0,-1, 0, 1, 0), R(4));
    hb.add_le(vec( 1,-2, 0, 0, 0, 0, 0), R(2));
    hb.add_le(vec( 1, 1, 0, 0,-1, 0, 1), R(4));
    hb.add_le(vec( 1, 0, 0, 0,-1, 0, 0), R(9));
    saturate_basis(hb);
}

// Sigma_2 table 1,  Ajili, Contejean
static void tst5() {
    hilbert_sl_basis hb;
    hb.add_le(vec( 1, 2,-1, 1), R(3));
    hb.add_le(vec( 2, 4, 1, 2), R(12));
    hb.add_le(vec( 1, 4, 2, 1), R(9));
    hb.add_le(vec( 1, 1, 0,-1), R(10));
    hb.add_le(vec( 1, 1,-1, 0), R(6));
    hb.add_le(vec( 1,-1, 0, 0), R(0));
    hb.add_le(vec( 0, 0, 1,-1), R(2));
    saturate_basis(hb);
}

// Sigma_3 table 1,  Ajili, Contejean
static void tst6() {
    hilbert_sl_basis hb;
    hb.add_le(vec( 4, 3, 0), R(6));
    hb.add_le(vec(-3,-4, 0), R(-1));
    hb.add_le(vec( 4, 0,-3), R(3));
    hb.add_le(vec(-3, 0, 4), R(7));
    hb.add_le(vec( 4, 0,-3), R(23));
    hb.add_le(vec( 0,-3, 4), R(11));
    saturate_basis(hb);
}

// Sigma_4 table 1,  Ajili, Contejean
static void tst7() {
    hilbert_sl_basis hb;
    hb.add_le(vec( 2, 1, 0, 1),  R(6));
    hb.add_le(vec( 1, 2, 1, 1),  R(7));
    hb.add_le(vec( 1, 3,-1, 2),  R(8));
    hb.add_le(vec( 1, 2,-9,-12), R(-11));
    hb.add_le(vec( 0, 0,-1, 3),  R(10));
    saturate_basis(hb);
}


void tst_hilbert_basis() {
    std::cout << "hilbert basis test\n";
    tst1();
    tst2();
    tst3();
#if 0
    tst4();
    tst5();
    tst6();
    tst7();
#endif
}
