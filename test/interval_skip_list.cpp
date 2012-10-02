/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    interval_skip_list.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-10-05.

Revision History:

--*/

#include"interval_skip_list.h"
#include"map.h"
#include"vector.h"

typedef sl_manager_base<unsigned> slist_manager;
template class interval_skip_list<unsigned_interval_skip_list_traits<unsigned, default_eq<unsigned>, 4, 4, false, slist_manager> >;
typedef interval_skip_list<unsigned_interval_skip_list_traits<unsigned, default_eq<unsigned>, 4, 4, false, slist_manager> > slist;
typedef u_map<unsigned> u2u_map;
typedef unsigned_isp_set<4, 4, slist_manager> uset;

static void tst1() {
    slist_manager m;
    slist l(m);
    SASSERT(l.check_invariant());
    SASSERT(l.empty());
    // l.display_physical(std::cout);
    l.insert(m, 20, 30, 5);
    l.insert(m, 31, 32, 5);
    l.insert(m, 18, 19, 5);
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    l.insert(m, 10, 15, 8);
    SASSERT(l.check_invariant());
    // l.display_physical(std::cout);
    l.insert(m, 5, 25, 7);
    SASSERT(l.check_invariant());
    // l.display_physical(std::cout);
    l.insert(m, 23, 27, 5);
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst2() {
    slist_manager(m);
    slist l(m);
    for(unsigned i = 0; i < 50; i++) {
        l.insert(m,i,i,i*10);
    }
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    for (unsigned i = 0; i < 25; i++) {
        l.insert(m,i*2,i*2+1,i*20+1);
    }
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    for (unsigned i = 0; i < 15; i++) {
        l.insert(m,i*3,i*3+2,i*30+1);
    }
    SASSERT(l.check_invariant());
    // l.display_physical(std::cout);
    // l.compress(4);
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static bool check_interval(slist & l, unsigned k1, unsigned k2, unsigned val) {
    for (unsigned i = k1; i <= k2; i++) {
        DEBUG_CODE({
            unsigned _val;
            SASSERT(l.contains(i, _val) && _val == val);
        });
    }
    return true;
}

static bool check_no_interval(slist & l, unsigned k1, unsigned k2) {
    for (unsigned i = k1; i <= k2; i++) {
        DEBUG_CODE({
            unsigned _val;
            SASSERT(!l.contains(i, _val));
        });
    }
    return true;
}

static void tst4() {
    slist_manager m;
    slist l(m);
    l.insert(m, 1, 10, 0);
    l.insert(m, 2, 5, 1);
    SASSERT(check_no_interval(l,0,0));
    SASSERT(check_interval(l,1,1,0));
    SASSERT(check_interval(l,2,5,1));
    SASSERT(check_interval(l,6,10,0));
    SASSERT(check_no_interval(l,11,20));
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst5() {
    slist_manager m;
    slist l(m);
    l.insert(m, 1, 5, 0);
    l.insert(m, 8, 100, 1);
    l.insert(m, 8, 20, 1);
    SASSERT(check_no_interval(l,0,0));
    SASSERT(check_interval(l,1,5,0));
    SASSERT(check_no_interval(l,6,7));
    SASSERT(check_interval(l,8,100,1));
    SASSERT(check_no_interval(l,101,200));
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst6() {
    slist_manager m;
    slist l(m);
    l.insert(m, 1, 5, 0);
    l.insert(m, 8, 100, 1);
    l.insert(m, 3, 20, 1);
    SASSERT(check_no_interval(l,0,0));
    SASSERT(check_interval(l,1,2,0));
    SASSERT(check_interval(l,3,100,1));
    SASSERT(check_no_interval(l,101,200));
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst7() {
    slist_manager m;
    slist l(m);
    l.insert(m, 1, 5, 0);
    l.insert(m, 8, 100, 1);
    l.insert(m, 2, 12, 0);
    SASSERT(check_no_interval(l,0,0));
    SASSERT(check_interval(l,1,12,0));
    SASSERT(check_interval(l,13,100,1));
    SASSERT(check_no_interval(l,101,200));
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst8() {
    slist_manager m;
    slist l(m);
    for (unsigned i = 0; i < 100; i++) {
        l.insert(m, 10*i, 10*i+5, i);
    }
    SASSERT(!l.empty());
    l.insert(m, 0, 10000, 0);
    SASSERT(!l.has_more_than_k_entries(1));
    // l.display_physical(std::cout);
    l.deallocate(m);
}

struct for_each_contains {
    slist const & m_other;
    
    for_each_contains(slist const & other):m_other(other) {}

    bool operator()(unsigned b, unsigned e, unsigned v) {
        for (unsigned i = b; i <= e; i++) {
            DEBUG_CODE({
                unsigned _v;
                SASSERT(m_other.contains(i, _v));
                SASSERT(v == _v);
            });
        }
        return true;
    }
};

static void random_tsts(unsigned num_ops, unsigned max_key, unsigned max_val, unsigned max_interval_size) {
    slist_manager m;
    slist   m1(m);
    u2u_map m2;
    for (unsigned i = 0; i < num_ops; i++) {
        SASSERT(m1.check_invariant());
        TRACE("interval_skip_list", tout << "i: " << i << "\n"; m1.display_physical(tout););
        // std::cout << i << std::endl;
        int op = rand()%8;
        if (op < 3) {
            unsigned bg  = rand() % max_key;
            unsigned sz  = rand() % max_interval_size;
            if (sz == 0) sz = 1;
            unsigned val = rand() % max_val;
            m1.insert(m, bg, bg+sz, val);
            for (unsigned j = bg; j <= bg+sz; j++) {
                DEBUG_CODE({
                    unsigned _val;
                    SASSERT(m1.contains(j, _val));
                    CTRACE("interval_skip_list", val != _val, tout << "i: " << i << ", j: " << j << ", val: " << val << ", _val: " << _val << "\n"; m1.display_physical(tout););
                    SASSERT(val == _val);
                    TRACE("interval_skip_list", tout << "[insert]: " << j << " -> " << val << "\n";);
                });
                m2.insert(j, val);
            }
        }
        else if (op < 4) {
            unsigned bg  = rand() % max_key;
            unsigned sz  = rand() % max_interval_size;
            if (sz == 0) sz = 1;
            m1.erase(m, bg, bg+sz);
            for (unsigned i = bg; i <= bg+sz; i++) {
                m2.erase(i);
            }
        }
        else if (op < 5) {
            slist m1_copy(m);
            m1_copy.copy(m, m1);
            for_each_contains proc1(m1);
            for_each_contains proc2(m1_copy);
            m1.for_each(proc2);
            m1_copy.for_each(proc1);
            // m1.display_physical(std::cout);
            // std::cout << "COPY===>\n";
            // m1_copy->display_physical(std::cout);
            m1_copy.deallocate(m);
        }
        else if (op < 6) {
            m1.compress(m, 3);
        }
        else { 
            SASSERT(m1.check_invariant());
            u2u_map::iterator it  = m2.begin();
            u2u_map::iterator end = m2.end();
            for (; it != end; ++it) {
                DEBUG_CODE({
                    unsigned _val;
                    CTRACE("interval_skip_list", !m1.contains(it->m_key, _val), 
                           tout << it->m_key << " -> " << it->m_value << "\n"; 
                           m1.display_physical(tout););
                    SASSERT(m1.contains(it->m_key, _val));
                    SASSERT(it->m_value == _val);
                });
            }
        }
    }
    // m1.display_physical(std::cout);
    // m1.compress(4);
    // m1.display_physical(std::cout);
    m1.deallocate(m);
}

static void tst9() {
    slist_manager m;
    slist l(m);
    l.insert(m,10,10,1);
    l.insert(m,9,9,0);
    l.insert(m,8,8,2);
    l.insert(m,7,7,3);
    l.insert(m,6,8,3);
    SASSERT(!l.has_more_than_k_buckets(1));
    SASSERT(check_no_interval(l,0,5));
    SASSERT(check_interval(l,6,8,3));
    SASSERT(check_interval(l,9,9,0));
    SASSERT(check_interval(l,10,10,1));
    SASSERT(check_no_interval(l,11,20));
    l.deallocate(m);
}

static void tst10() {
    slist_manager m;
    slist l(m);
    l.insert(m,10,10,1);
    l.insert(m,13,16,2);
    l.insert(m,17,28,3);
    l.remove(m,12,19);
    SASSERT(l.check_invariant());
    SASSERT(check_no_interval(l,0,9));
    SASSERT(check_interval(l,10,10,1));
    SASSERT(check_no_interval(l,12,19));
    SASSERT(check_interval(l,20,28,3));
    SASSERT(check_no_interval(l,29,100));
    l.remove(m,10,11);
    SASSERT(l.check_invariant());
    SASSERT(check_no_interval(l,0,19));
    SASSERT(check_interval(l,20,28,3));
    SASSERT(check_no_interval(l,29,100));
    l.remove(m,0,1000);
    SASSERT(l.empty());
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

static void tst11() {
    slist_manager m;
    slist l(m);
    l.insert(m,11,20,1);
    l.insert(m,21,30,2);
    l.insert(m,31,40,3);
    l.insert(m,41,50,4);
    l.insert(m,51,60,5);
    l.compress(m,4);
    SASSERT(check_no_interval(l,0,10));
    SASSERT(check_interval(l,11,20,1));
    SASSERT(check_interval(l,21,30,2));
    SASSERT(check_interval(l,31,40,3));
    SASSERT(check_interval(l,41,50,4));
    SASSERT(check_interval(l,51,60,5));
    SASSERT(check_no_interval(l,61,100));
    SASSERT(l.check_invariant());
    l.remove(m, 25, 26);
    SASSERT(check_no_interval(l,0,10));
    SASSERT(check_interval(l,11,20,1));
    SASSERT(check_interval(l,21,24,2));
    SASSERT(check_no_interval(l,25,26));
    SASSERT(check_interval(l,27,30,2));
    SASSERT(check_interval(l,31,40,3));
    SASSERT(check_interval(l,41,50,4));
    SASSERT(check_interval(l,51,60,5));
    SASSERT(check_no_interval(l,61,100));
    SASSERT(l.check_invariant());
    l.remove(m, 44,48);
    SASSERT(check_no_interval(l,0,10));
    SASSERT(check_interval(l,11,20,1));
    SASSERT(check_interval(l,21,24,2));
    SASSERT(check_no_interval(l,25,26));
    SASSERT(check_interval(l,27,30,2));
    SASSERT(check_interval(l,31,40,3));
    SASSERT(check_interval(l,41,43,4));
    SASSERT(check_no_interval(l,44,48));
    SASSERT(check_interval(l,49,50,4));
    SASSERT(check_interval(l,51,60,5));
    SASSERT(check_no_interval(l,61,100));
    SASSERT(l.check_invariant());
    l.remove(m, 22,24);
    SASSERT(check_no_interval(l,0,10));
    SASSERT(check_interval(l,11,20,1));
    SASSERT(check_interval(l,21,21,2));
    SASSERT(check_no_interval(l,22,26));
    SASSERT(check_interval(l,27,30,2));
    SASSERT(check_interval(l,31,40,3));
    SASSERT(check_interval(l,41,43,4));
    SASSERT(check_no_interval(l,44,48));
    SASSERT(check_interval(l,49,50,4));
    SASSERT(check_interval(l,51,60,5));
    SASSERT(check_no_interval(l,61,100));
    SASSERT(l.check_invariant());
    l.remove(m, 42,49);
    SASSERT(check_no_interval(l,0,10));
    SASSERT(check_interval(l,11,20,1));
    SASSERT(check_interval(l,21,21,2));
    SASSERT(check_no_interval(l,22,26));
    SASSERT(check_interval(l,27,30,2));
    SASSERT(check_interval(l,31,40,3));
    SASSERT(check_interval(l,41,41,4));
    SASSERT(check_no_interval(l,42,49));
    SASSERT(check_interval(l,50,50,4));
    SASSERT(check_interval(l,51,60,5));
    SASSERT(check_no_interval(l,61,100));
    SASSERT(l.check_invariant());
    // l.display_physical(std::cout);
    l.deallocate(m);
}

static void tst12() {
    slist_manager m;
    slist l(m);
    l.insert(m,10,10,0);
    l.insert(m,9,9,0);
    SASSERT(l.check_invariant());
    l.insert(m,8,9,1);
    SASSERT(l.check_invariant());
    l.insert(m,7,7,2);
    SASSERT(l.check_invariant());
    l.insert(m,6,6,3);
    SASSERT(l.check_invariant());
    l.insert(m,4,5,2);
    SASSERT(l.check_invariant());
    l.insert(m,3,9,0);
    // l.display_physical(std::cout);
    l.deallocate(m);
}

static void tst13() {
    slist_manager m;
    uset s(m);
    s.insert(m, 10, 30);
    s.insert(m, 32, 40);
    s.display(std::cout);
    std::cout << ", mem: " << s.memory() << "\n";
    s.deallocate(m);
}

struct obj {
    unsigned m_val;
    unsigned m_ref_count;
    void inc_ref() {
        m_ref_count++;
    }
    void dec_ref() {
        SASSERT(m_ref_count > 0);
        m_ref_count--;
        if (m_ref_count == 0)
            dealloc(this);
    }
    obj(unsigned v):m_val(v), m_ref_count(0) {
    }
};

std::ostream & operator<<(std::ostream & out, obj * o) {
    out << o->m_val << "{" << o->m_ref_count << "}";
    return out;
}

struct obj_slist_manager : public sl_manager_base<obj*> {
    void inc_ref_eh(obj * v) {
        v->inc_ref();
    }

    void dec_ref_eh(obj * v) {
        v->dec_ref();
    }
};

struct inc_ref_functor {
    unsigned_vector & refs;
    inc_ref_functor(unsigned_vector & r):refs(r) {}
    bool operator()(unsigned b, unsigned e, obj * val) {
        refs[val->m_val]++;
        return true;
    }
};

template class interval_skip_list<unsigned_interval_skip_list_traits<obj*, default_eq<obj*>, 16, 16, true, obj_slist_manager> >;
typedef interval_skip_list<unsigned_interval_skip_list_traits<obj*, default_eq<obj*>, 16, 16, true, obj_slist_manager> > obj_slist;

void random_tsts_ref(unsigned num_ops, unsigned num_objs, unsigned max_key, unsigned max_interval_size) {
    obj_slist_manager m;
    obj_slist l(m);
    ptr_vector<obj> objs;
    unsigned_vector refs;
    for (unsigned i = 0; i < num_objs; i++) {
        objs.push_back(alloc(obj, i));
        objs.back()->inc_ref();
        refs.push_back(1);
    }

    for (unsigned i = 0; i < num_ops; i++) {
        SASSERT(l.check_invariant());
        TRACE("interval_skip_list", tout << "i: " << i << "\n"; l.display_physical(tout); tout << "\n";);
        int op = rand()%5;
        if (op < 3) {
            unsigned bg  = rand() % max_key;
            unsigned sz  = rand() % max_interval_size;
            if (sz == 0) sz = 1;
            unsigned val = rand() % num_objs;
            TRACE("interval_skip_list", tout << "[inserting]: [" << bg << ", " << (bg+sz) << "] -> " << objs[val] << "\n";);
            l.insert(m, bg, bg+sz, objs[val]);
            SASSERT(objs[val]->m_ref_count > 1);
        }
        else if (op < 4) {
            unsigned bg  = rand() % max_key;
            unsigned sz  = rand() % max_interval_size;
            if (sz == 0) sz = 1;
            TRACE("interval_skip_list", tout << "[erasing]: [" << bg << ", " << (bg+sz) << "]\n";);
            l.erase(m, bg, bg+sz);
        }
        else if (op < 5) {
            obj_slist l_copy(m);
            l_copy.copy(m, l);
            TRACE("interval_skip_list", tout << "[copying]\n";);
            l_copy.deallocate(m);
            TRACE("interval_skip_list", tout << "[deleting copy]\n";);
        }
        else {
            TRACE("interval_skip_list", tout << "[compressing]\n";);
            l.compress(m, 3);
        }
        // check ref-counts
        inc_ref_functor proc(refs);
        l.for_each(proc);
        for (unsigned i = 0; i < num_objs; i++) {
            CTRACE("interval_skip_list", refs[i] != objs[i]->m_ref_count, 
                   tout << "i: " << i << ", objs[i]: " << objs[i] << ", refs[i]: " << refs[i] << "\n\n";
                   l.display_physical(tout););
            SASSERT(refs[i] == objs[i]->m_ref_count);
            refs[i] = 1; 
        }
    }
    l.deallocate(m);
    for (unsigned i = 0; i < num_objs; i++) {
        SASSERT(objs[i]->m_ref_count == 1);
        objs[i]->dec_ref();
    }
}

void tst_ref() {
    obj_slist_manager m;
    obj_slist l(m);
    for (unsigned i = 0; i < 30; i++) {
        obj * n = alloc(obj, i);
        l.insert(m, i*10, i*10+3, n);
        // l.display_physical(std::cout);
        // std::cout << "memory: " << l.memory() << "\n";
    }
    l.deallocate(m);
    
}

void tst_push_back_aux(slist::push_back_proc & push_back, unsigned num_ops, unsigned max_int, unsigned max_sep, unsigned max_val) {
    unsigned prev_key;
    
    if (push_back.empty())
        prev_key = 0;
    else
        prev_key = push_back.last_key();
    
    for (unsigned i = 0; i < num_ops; i++) {
        unsigned next_key = prev_key + 1;
        next_key += (rand() % max_sep);
        unsigned sz  = rand() % max_int;
        if (sz == 0) sz = 1;
        unsigned val = rand() % max_val;
        push_back(next_key, next_key+sz, val);
        SASSERT(!push_back.empty());
        prev_key = push_back.last_key();
    }
}

void tst_push_back1(unsigned num_ops, unsigned max_int, unsigned max_sep, unsigned max_val) {
    slist_manager m;
    slist l(m);
    slist::push_back_proc push_back(m, l);
    
    tst_push_back_aux(push_back, num_ops, max_int, max_sep, max_val);
    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

void tst_push_back2(unsigned num_ops, unsigned max_int, unsigned max_sep, unsigned max_val) {
    slist_manager m;
    slist l(m);
    
    // insert some random values before creating push_back functor
    for (unsigned i = 0; i < num_ops; i++) {
        unsigned next_key = rand() % (num_ops * max_int/2);
        unsigned sz  = rand() % max_int;
        if (sz == 0) sz = 1;
        unsigned val = rand() % max_val;
        l.insert(m, next_key, next_key+sz, val);
    }
    
    slist::push_back_proc push_back(m, l);
    
    tst_push_back_aux(push_back, num_ops, max_int, max_sep, max_val);

    // l.display_physical(std::cout);
    SASSERT(l.check_invariant());
    l.deallocate(m);
}

void tst_find_geq1() {
    slist_manager m;
    slist l(m);
    l.insert(m, 10, 20, 4);
    l.insert(m, 23, 30, 3);
    l.insert(m, 40, 45, 10);
    l.insert(m, 50, 66, 1);
    l.insert(m, 100, 120, 21);
    l.insert(m, 140, 200, 2);
    slist::iterator it = l.find_geq(22);
    SASSERT(it->begin_key() == 23);
    it = l.find_geq(42);
    SASSERT(it->begin_key() == 40);
    it.move_to(130);
    SASSERT(it->begin_key() == 140);
    it.move_to(400);
    SASSERT(it == l.end());
    it = l.find_geq(300);
    SASSERT(it == l.end());
    it = l.find_geq(9);
    SASSERT(it->begin_key() == 10);
    it.move_to(105);
    SASSERT(it->begin_key() == 100);
    it = l.find_geq(15);
    SASSERT(it->begin_key() == 10);
    it.move_to(31);
    SASSERT(it->begin_key() == 40);
    it = l.find_geq(22);
    SASSERT(it->begin_key() == 23);
    it = l.find_geq(124);
    SASSERT(it->begin_key() == 140);
    it = l.find_geq(102);
    SASSERT(it->begin_key() == 100);
    // l.display_physical(std::cout);
    l.deallocate(m);
} 

struct add42 {
    unsigned operator()(unsigned v) { return v + 42; }
};

void tst_move_to() {
    slist_manager m;
    slist l(m);
    for (unsigned i = 0; i < 500; i++)
        l.insert(m, i*10, i*10 + 5, i);
    l.compress(m, 4);
    slist::iterator it = l.find_geq(137);
    SASSERT(it->begin_key() == 140);
    it.move_to(947);
    SASSERT(it->begin_key() == 950);
    it.move_to(4955);
    SASSERT(it->begin_key() == 4950);
    it.move_to(4955);
    SASSERT(it->begin_key() == 4950);
    it.move_to(4956);
    SASSERT(it->begin_key() == 4960);
    it.move_to(4982);
    SASSERT(it->begin_key() == 4980);
    it.move_to(4987);
    SASSERT(it->begin_key() == 4990);
    it.move_to(4990);
    SASSERT(it->begin_key() == 4990);
    it.move_to(4995);
    SASSERT(it->begin_key() == 4990);
    it.move_to(4996);
    SASSERT(it.at_end());
    // l.display_physical(std::cout);
    add42 f;
    // l.display(std::cout); std::cout << "\n";
    l.update_values(m, f);
    // l.display(std::cout); std::cout << "\n";
    l.deallocate(m);
}

static void tst_ext_iterator() {
    slist_manager m;
    slist l(m);
    for (unsigned i = 0; i < 20; i++)
        l.insert(m, i*10, i*10 + 5, i);
    l.compress(m, 4);
    l.display_physical(std::cout); std::cout << "\n";
    slist::ext_iterator it;
    slist::ext_iterator end;
    SASSERT(end.at_end());
    l.move_geq(it, 92);
    SASSERT(!it.at_end());
    SASSERT(it->begin_key() == 90);
    it++;
    SASSERT(it->begin_key() == 100);
    it.erase(m);
    SASSERT(it->begin_key() == 110);
    it.erase(m);
    SASSERT(it->begin_key() == 120);
    it.erase(m);
    it.erase(m);
    it.erase(m);
    it.erase(m);
    SASSERT(it->begin_key() == 160);
    SASSERT(l.check_invariant());
    l.display_physical(std::cout); std::cout << "\n";
    l.move_geq(it, 0);
    SASSERT(it->begin_key() == 0);
    it.erase(m);
    SASSERT(it->begin_key() == 10);
    it.erase(m);
    SASSERT(it->begin_key() == 20);
    it.erase(m);
    SASSERT(it->begin_key() == 30);
    it.erase(m);
    SASSERT(it->begin_key() == 40);
    it.erase(m);
    SASSERT(it->begin_key() == 50);
    l.display_physical(std::cout); std::cout << "\n";
    l.deallocate(m);
}

void tst_interval_skip_list() {
    std::cout << "unsigned map stats:\n";
    slist::display_size_info(std::cout);
    std::cout << "\nunsigned set stats:\n";
    uset::display_size_info(std::cout);
    std::cout << "\n";
    tst1();
//     enable_trace("interval_skip_list_insert_bug");
//     enable_trace("interval_skip_list_bug");
//     enable_trace("del_entries_upto_bug");
//     enable_trace("insert_inside_bug");
//     enable_trace("insert_at_bug");
    tst2();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    tst_find_geq1();
    tst_move_to();
    tst_push_back1(300, 4, 2, 10);
    tst_push_back2(300, 4, 2, 10);
    random_tsts(1000, 20, 20, 5);
    random_tsts_ref(1000, 20, 20, 5);
    tst_ref();
    tst_ext_iterator();
}


