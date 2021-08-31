
/*++
Copyright (c) 2015 Microsoft Corporation

--*/
#include "util/rlimit.h"
#include "math/hilbert/hilbert_basis.h"

/*
  Test generation of linear congruences a la Karr.

 */
namespace karr {

    struct matrix {
        vector<vector<rational> > A;
        vector<rational>          b;

        unsigned size() const { return A.size(); }

        void reset() {
            A.reset();
            b.reset();
        }

        matrix& operator=(matrix const& other) {
            reset();
            append(other);
            return *this;
        }

        void append(matrix const& other) {
            A.append(other.A);
            b.append(other.b);
        }

        void display(std::ostream& out) {
            for (unsigned i = 0; i < A.size(); ++i) {
                for (unsigned j = 0; j < A[i].size(); ++j) {
                    out << A[i][j] << " ";
                }
                out << " = " << -b[i] << "\n";
            }
        }
    };

    // treat src as a homogeneous matrix.
    void dualizeH(matrix& dst, matrix const& src) {
        reslimit rl;
        hilbert_basis hb(rl);
        for (unsigned i = 0; i < src.size(); ++i) {
            vector<rational> v(src.A[i]);
            v.push_back(src.b[i]);
            hb.add_eq(v, rational(0));
        }
        for (unsigned i = 0; i < 1 + src.A[0].size(); ++i) {
            hb.set_is_int(i);
        }
        lbool is_sat = hb.saturate();
        hb.display(std::cout);
        VERIFY(is_sat == l_true);
        dst.reset();
        unsigned basis_size = hb.get_basis_size();
        for (unsigned i = 0; i < basis_size; ++i) {
            bool is_initial;
            vector<rational> soln;
            hb.get_basis_solution(i, soln, is_initial);
            if (!is_initial) {
                dst.b.push_back(soln.back());
                soln.pop_back();
                dst.A.push_back(soln);
            }
        }
    }

    // treat src as an inhomegeneous matrix.
    void dualizeI(matrix& dst, matrix const& src) {
        reslimit rl;
        hilbert_basis hb(rl);
        for (unsigned i = 0; i < src.size(); ++i) {
            hb.add_eq(src.A[i], -src.b[i]);
        }
        for (unsigned i = 0; i < src.A[0].size(); ++i) {
            hb.set_is_int(i);
        }
        lbool is_sat = hb.saturate();
        hb.display(std::cout);
        VERIFY(is_sat == l_true);
        dst.reset();
        unsigned basis_size = hb.get_basis_size();
        bool first_initial = true;
        for (unsigned i = 0; i < basis_size; ++i) {
            bool is_initial;
            vector<rational> soln;
            hb.get_basis_solution(i, soln, is_initial);
            if (is_initial && first_initial) {
                dst.A.push_back(soln);
                dst.b.push_back(rational(1));
                first_initial = false;
            }
            else if (!is_initial) {
                dst.A.push_back(soln);
                dst.b.push_back(rational(0));
            }
        }
    }

    void juxtapose(matrix& dst, matrix const& M, matrix const& N) {
        dst = M;
        dst.append(N);
    }

    void join(matrix& dst, matrix const& M, matrix const& N) {
        matrix MD, ND, dstD;
        dualizeI(MD, M);
        dualizeI(ND, N);
        juxtapose(dstD, MD, ND);
        dualizeH(dst, dstD);
    }

    void joinD(matrix& dst, matrix const& MD, matrix const& ND) {
        matrix dstD;
        juxtapose(dstD, MD, ND);
        dualizeH(dst, dstD);
    }

    void transition(
        matrix& dst,
        matrix const& src,
        matrix const& Ab) {
        matrix T;
        // length of rows in Ab are twice as long as
        // length of rows in src.
        ENSURE(2*src.A[0].size() == Ab.A[0].size());
        vector<rational> zeros;
        for (unsigned i = 0; i < src.A[0].size(); ++i) {
            zeros.push_back(rational(0));
        }
        for (unsigned i = 0; i < src.size(); ++i) {
            T.A.push_back(src.A[i]);
            T.A.back().append(zeros);
        }
        T.b.append(src.b);
        T.append(Ab);

        T.display(std::cout << "T:\n");
        matrix TD;
        dualizeI(TD, T);
        TD.display(std::cout << "TD:\n");
        for (unsigned i = 0; i < TD.size(); ++i) {
            vector<rational> v;
            v.append(src.size(), TD.A[i].data() + src.size());
            dst.A.push_back(v);
            dst.b.push_back(TD.b[i]);
        }
        dst.display(std::cout << "dst\n");
    }

    static vector<rational> V(int i, int j) {
        vector<rational> v;
        v.push_back(rational(i));
        v.push_back(rational(j));
        return v;
    }

    static vector<rational> V(int i, int j, int k, int l) {
        vector<rational> v;
        v.push_back(rational(i));
        v.push_back(rational(j));
        v.push_back(rational(k));
        v.push_back(rational(l));
        return v;
    }

#if 0
    static vector<rational> V(int i, int j, int k, int l, int m) {
        vector<rational> v;
        v.push_back(rational(i));
        v.push_back(rational(j));
        v.push_back(rational(k));
        v.push_back(rational(l));
        v.push_back(rational(m));
        return v;
    }
#endif

    static vector<rational> V(int i, int j, int k, int l, int x, int y, int z) {
        vector<rational> v;
        v.push_back(rational(i));
        v.push_back(rational(j));
        v.push_back(rational(k));
        v.push_back(rational(l));
        v.push_back(rational(x));
        v.push_back(rational(y));
        v.push_back(rational(z));
        return v;
    }

#define R(_x_) rational(_x_)


    static void tst1() {
        matrix Theta;
        matrix Ab;

        //
        Theta.A.push_back(V(1, 0));
        Theta.b.push_back(R(0));
        Theta.A.push_back(V(0, 1));
        Theta.b.push_back(R(-2));

        Theta.display(std::cout << "Theta\n");

        Ab.A.push_back(V(-1,  0, 1, 0));
        Ab.b.push_back(R(1));
        Ab.A.push_back(V(-1, -2, 0, 1));
        Ab.b.push_back(R(1));

        Ab.display(std::cout << "Ab\n");

        matrix ThetaD;
        dualizeI(ThetaD, Theta);
        ThetaD.display(std::cout);

        matrix t1D, e1;
        transition(t1D, Theta, Ab);
        joinD(e1, t1D, ThetaD);

        t1D.display(std::cout << "t1D\n");
        e1.display(std::cout << "e1\n");

        matrix t2D, e2;
        transition(t2D, e1, Ab);
        joinD(e2, t2D, ThetaD);

        t2D.display(std::cout << "t2D\n");
        e2.display(std::cout << "e2\n");
    }

    void tst2() {
        /**
           0 0 0 0 0 0 0  = 0
           0 0 0 0 0 0 0  = 0
           0 0 0 0 0 0 0  = 0
           0 0 0 0 0 0 0  = 0
           0 0 0 0 1 0 0  = 0
           0 0 0 0 -1 0 0  = 0
           0 1 0 0 0 0 0  = 0
           0 -1 0 0 0 0 0  = 0
           0 0 0 2 0 0 0  = 0
           0 0 0 -2 0 0 0  = 0
        */

        matrix ND;
        ND.A.push_back(V(0,0,0,0,1,0,0));  ND.b.push_back(R(0));
        ND.A.push_back(V(0,0,0,0,-1,0,0));  ND.b.push_back(R(0));
        ND.A.push_back(V(0,1,0,0,0,0,0));  ND.b.push_back(R(0));
        ND.A.push_back(V(0,-1,0,0,0,0,0));  ND.b.push_back(R(0));
        ND.A.push_back(V(0,0,0,2,0,0,0));  ND.b.push_back(R(0));
        ND.A.push_back(V(0,0,0,-2,0,0,0));  ND.b.push_back(R(0));

        ND.display(std::cout << "ND\n");

        matrix N;
        dualizeH(N, ND);

        N.display(std::cout << "N\n");


    }

    void tst3() {
        /**
           0 0 0 0 1 0 0  = 0
           0 0 0 0 -1 0 0  = 0
           0 1 0 0 0 0 0  = 0
           0 -1 0 0 0 0 0  = 0
           0 0 0 2 0 0 0  = 0
           0 0 0 -2 0 0 0  = 0
        */

        matrix ND;
        ND.A.push_back(V(1,0));   ND.b.push_back(R(0));
        ND.A.push_back(V(0,2));   ND.b.push_back(R(0));

        ND.display(std::cout << "ND\n");

        matrix N;
        dualizeH(N, ND);

        N.display(std::cout << "N\n");


    }

};

void tst_karr() {
    karr::tst3();
    return;
    karr::tst1();
}
