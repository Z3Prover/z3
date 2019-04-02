
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/base/dl_util.h"

using namespace datalog;


void dl_util_two_array_sort() {
    const unsigned num = 97;
    unsigned a1[num];
    unsigned a2[num];

    for(unsigned i=0; i<num; i++) {
        a1[i]=(i*30)%num;
        a2[i]=(i*30)%num+3;
    }

    datalog::sort_two_arrays(num, a1, a2);

    for(unsigned i=0; i<num; i++) {
        ENSURE(a2[i]==i+3);
    }
}

void dl_util_cycle_from_permutation() {
    unsigned permutation_arr[] = { 0, 1, 4, 3, 2, 5, 6, 7 };
    vector<unsigned> perm(sizeof(permutation_arr)/sizeof(unsigned), permutation_arr);
    vector<unsigned> cycle;

    datalog::cycle_from_permutation(perm, cycle);
    ENSURE(cycle.size()==2);
    ENSURE(cycle[0]==2 || cycle[0]==4);
    ENSURE(cycle[1]==2 || cycle[1]==4);
    ENSURE((cycle[0]==2) == (cycle[1]==4));

    unsigned permutation_arr2[] = { 1, 2, 3, 4, 5, 6, 7, 0 };
    unsigned len2 = sizeof(permutation_arr2)/sizeof(unsigned);
    vector<unsigned> perm2(len2, permutation_arr2);
    cycle.clear();
    datalog::cycle_from_permutation(perm2, cycle);

    for(unsigned i=0; i<len2; i++) {
        ENSURE( (cycle[i]+1)%len2==cycle[(i+1)%len2] );
    }
}

void tst_dl_util() {
    dl_util_two_array_sort();
    dl_util_cycle_from_permutation();
}



