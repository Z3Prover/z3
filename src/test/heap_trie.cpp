
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "heap_trie.h"

struct unsigned_le {
    static bool le(unsigned i, unsigned j) { return i <= j; }
};


typedef heap_trie<unsigned, unsigned_le, unsigned_hash, unsigned > heap_trie_t;

static void find_le(heap_trie_t& ht, unsigned num_keys, unsigned const* keys) {
    statistics st;
    vector<unsigned> vals;
    ht.find_all_le(keys, vals);
    std::cout << "find_le: ";
    for (unsigned i = 0; i < num_keys; ++i) {
        std::cout << keys[i] << " ";
    }
    std::cout << " |-> ";
    for (unsigned i = 0; i < vals.size(); ++i) {
        std::cout << vals[i] << " ";
    }
    std::cout << "\n";
    ht.collect_statistics(st);
    st.display(std::cout);

}


void tst_heap_trie() {
    unsigned_le le;
    heap_trie_t ht(le);

    ht.reset(3);
    unsigned keys1[3] = { 1, 2, 3};
    ht.insert(keys1, 1);
    unsigned keys2[3] = { 2, 2, 3};
    ht.insert(keys2, 2);
    unsigned keys3[3] = { 1, 1, 3};
    ht.insert(keys3, 3);
    unsigned keys4[3] = { 2, 1, 3};
    unsigned keys5[3] = { 2, 3, 3};

    unsigned val;

    VERIFY (ht.find_eq(keys1, val) && val == 1);
    VERIFY (ht.find_eq(keys2, val) && val == 2);
    VERIFY (ht.find_eq(keys3, val) && val == 3);
    VERIFY (!ht.find_eq(keys4, val));

    find_le(ht, 3, keys1);
    find_le(ht, 3, keys2);
    find_le(ht, 3, keys3);
    find_le(ht, 3, keys4);
    find_le(ht, 3, keys5);

    ht.display(std::cout);
    
}
