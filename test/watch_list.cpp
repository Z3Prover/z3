/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_watch_list.cpp

Abstract:

    Test watch list data structure.

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

--*/
#include"vector.h"
#include"sat_types.h"

static void tst1() {
    watch_list wl;
    for(unsigned i = 0; i < 10; i++)
	wl.insert_clause(reinterpret_cast<clause*>(static_cast<size_t>(i+1)));
}

static void tst2() {
    ptr_vector<clause> clause_list;
    vector<literal>   lit_list;
    watch_list wl;
    unsigned n = rand()%1000;
    for (unsigned i = 0; i < n; i++) {
	unsigned op = rand()%7;
	if (op <= 1) {
	    clause * c = reinterpret_cast<clause*>(static_cast<size_t>(rand()));
	    wl.insert_clause(c);
	    clause_list.push_back(c);
	}
	else if (op <= 3) {
	    literal l = to_literal(rand());
	    wl.insert_literal(l);
	    lit_list.push_back(l);
	}
	else if (op <= 4) {
	    if (!clause_list.empty()) {
		int idx = rand() % (clause_list.size());
		clause * c = clause_list[idx];
		wl.remove_clause(c);
		ptr_vector<clause>::iterator it = std::find(clause_list.begin(), clause_list.end(), c);
		SASSERT(it);
		clause_list.erase(it);
	    }
	}
	else if (op <= 5) {
	    ptr_vector<clause>::iterator it = clause_list.begin();
	    ptr_vector<clause>::iterator end = clause_list.end();
	    watch_list::clause_iterator it2 = wl.begin_clause();
	    watch_list::clause_iterator end2 = wl.end_clause();
	    for (; it != end; ++it, ++it2) {
		SASSERT(it2 != end2);
		SASSERT(*it == *it2);
	    }
	}
	else if (op <= 6) {
	    vector<literal>::iterator begin = lit_list.begin();
	    vector<literal>::iterator it    = lit_list.end();
	    watch_list::literal_iterator it2 = wl.begin_literals();
	    watch_list::literal_iterator end2 = wl.end_literals();
	    while (it != begin) {
		--it;
		SASSERT(it2 != end2);
		SASSERT(*it == *it2);
		++it2;
	    }
	}
    }
}

static void tst3() {
    for (unsigned i = 0; i < 1000; i++)
	tst2();
}

void tst_watch_list() {
    tst1();
    tst3();
}

