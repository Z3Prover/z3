/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fvi.cpp

Abstract:

    Feature Vector Indexing.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifdef _WINDOWS
#include"fvi_def.h"
#include"trace.h"

typedef vector<int> data;

static int to_feature(int val) {
    return val % 4;
}

static std::ostream & operator<<(std::ostream & out, data const & d) {
    out << "["; 
    data::const_iterator it  = d.begin();
    data::const_iterator end = d.end();
    for (bool first = true; it != end; ++it, first = false)
        out << (first ? "" : " ") << *it << ":" << to_feature(*it);
    out << "]";
    return out;
}

#define NUM_FEATURES 5

struct to_feature_vector {
    unsigned m_num_features;

    to_feature_vector(unsigned n):m_num_features(n) {}

    void operator()(data * d, unsigned * f) {
        for (unsigned i = 0; i < m_num_features; i++) {
            f[i] = to_feature((*d)[i]);
        }
    }
};

struct data_hash {
    unsigned operator()(data * d) const {
        unsigned r = 0;
        data::iterator it  = d->begin();
        data::iterator end = d->end();
        for (; it != end; ++it) 
            r += *it;
        return r;
    } 
};

ptr_vector<data> g_datas;

static void collect() {
    std::for_each(g_datas.begin(), g_datas.end(), delete_proc<data>());
}

static data * mk_random_data() {
    data * d = alloc(data);
    for (unsigned i = 0; i < NUM_FEATURES; i++)
        d->push_back(rand() % 1000);
    g_datas.push_back(d);
    return d;
}

struct le_visitor {
    data * m_data;

    le_visitor(data * d):m_data(d) {}

    bool operator()(data * other) {
        // TRACE("fvi", tout << *other << " <= " << *m_data << "\n";);
        for (unsigned i = 0; i < NUM_FEATURES; i++) {
            SASSERT(to_feature((*other)[i]) <= to_feature((*m_data)[i]));
        }
        return true;
    }
};

static void tst1(unsigned n1) {
    typedef fvi<data, to_feature_vector, data_hash> data_set;
    data_set index1(NUM_FEATURES, to_feature_vector(NUM_FEATURES));
    ptr_vector<data> index2;
    
    for (unsigned i = 0; i < n1; i++) {
        int op = rand()%6;
        if (op < 3) {
            data * d = mk_random_data();
            if (!index1.contains(d)) {
                // TRACE("fvi", tout << "inserting: " << *d << "\n";);
                index1.insert(d);
                index2.push_back(d);
                SASSERT(std::find(index2.begin(), index2.end(), d) != index2.end());
                SASSERT(index1.contains(d));
            }
        }
        else if (op < 4) {
            if (!index2.empty()) {
                unsigned idx = rand() % index2.size();
                if (index2[idx]) {
                    SASSERT(index1.contains(index2[idx]));
                }
            }
        }
        else if (op < 5) {
            if (!index2.empty()) {
                unsigned idx = rand() % index2.size();
                if (index2[idx]) {
                    // TRACE("fvi", tout << "erasing: " << *(index2[idx]) << "\n";);
                    index1.erase(index2[idx]);
                    SASSERT(!index1.contains(index2[idx]));
                    index2[idx] = 0;
                }
            }
        }
        else {
            if (!index2.empty()) {
                unsigned idx = rand() % index2.size();
                data * d = index2[idx];
                if (d)
                    index1.visit(d, le_visitor(d));
            }
        }
    }

    TRACE("fvi",
          data_set::statistics s;
          index1.stats(s);
          tout << "size:           " << s.m_size << "\n";
          tout << "num. nodes:     " << s.m_num_nodes << "\n";
          tout << "num. leaves:    " << s.m_num_leaves << "\n";
          tout << "min. leaf size: " << s.m_min_leaf_size << "\n";
          tout << "max. leaf size: " << s.m_max_leaf_size << "\n";
          );
}

void tst_fvi() {
    for (unsigned i = 0; i < 1000; i++) 
        tst1(100);
    tst1(10000);
    collect();
}
#else
void tst_fvi() {
}
#endif 
