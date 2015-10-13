/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3scopes.cpp

  Abstract:

  Calculations with scopes, for both sequence and tree interpolation.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#include <assert.h>

#include <algorithm>

#include "iz3scopes.h"


/** computes the least common ancestor of two nodes in the tree, or SHRT_MAX if none */
int scopes::tree_lca(int n1, int n2){
    if(!tree_mode())
        return std::max(n1,n2);
    if(n1 == SHRT_MIN) return n2;
    if(n2 == SHRT_MIN) return n1;
    if(n1 == SHRT_MAX || n2 == SHRT_MAX) return SHRT_MAX;
    while(n1 != n2){
        if(n1 == SHRT_MAX || n2 == SHRT_MAX) return SHRT_MAX;
        assert(n1 >= 0 && n2 >= 0 && n1 < (int)parents.size() && n2 < (int)parents.size());
        if(n1 < n2) n1 = parents[n1];
        else n2 = parents[n2];
    }
    return n1;
}

/** computes the greatest common descendant two nodes in the tree, or SHRT_MIN if none */
int scopes::tree_gcd(int n1, int n2){
    if(!tree_mode())
        return std::min(n1,n2);
    int foo = tree_lca(n1,n2);
    if(foo == n1) return n2;
    if(foo == n2) return n1;
    return SHRT_MIN;
}

#ifndef FULL_TREE

/** test whether a tree node is contained in a range */
bool scopes::in_range(int n, const range &rng){
    return tree_lca(rng.lo,n) == n && tree_gcd(rng.hi,n) == n;
}

/** test whether two ranges of tree nodes intersect */
bool scopes::ranges_intersect(const range &rng1, const range &rng2){
    return tree_lca(rng1.lo,rng2.hi) == rng2.hi && tree_lca(rng1.hi,rng2.lo) == rng1.hi;
}


bool scopes::range_contained(const range &rng1, const range &rng2){
    return tree_lca(rng2.lo,rng1.lo) == rng1.lo
        && tree_lca(rng1.hi,rng2.hi) == rng2.hi;
}

scopes::range scopes::range_lub(const range &rng1, const range &rng2){
    range res;
    res.lo = tree_gcd(rng1.lo,rng2.lo);
    res.hi = tree_lca(rng1.hi,rng2.hi);
    return res;
}
  
scopes::range scopes::range_glb(const range &rng1, const range &rng2){
    range res;
    res.lo = tree_lca(rng1.lo,rng2.lo);
    res.hi = tree_gcd(rng1.hi,rng2.hi);
    return res;
}

#else
  

namespace std {
    template <>
    class hash<scopes::range_lo > {
    public:
        size_t operator()(const scopes::range_lo &p) const {
            return p.lo + (size_t)p.next;
        }
    };
}

template <> inline
size_t stdext::hash_value<scopes::range_lo >(const scopes::range_lo& p)
{    
    std::hash<scopes::range_lo> h;
    return h(p);
}

namespace std {
    template <>
    class less<scopes::range_lo > {
    public:
        bool operator()(const scopes::range_lo &x, const scopes::range_lo &y) const {
            return x.lo < y.lo || x.lo == y.lo && (size_t)x.next < (size_t)y.next;
        }
    };
}
 

struct range_op {
    scopes::range_lo *x, *y;
    int hi;
    range_op(scopes::range_lo *_x, scopes::range_lo *_y, int _hi){
        x = _x; y = _y; hi = _hi;
    }
};

namespace std {
    template <>
    class hash<range_op > {
    public:
        size_t operator()(const range_op &p) const {
            return (size_t) p.x + (size_t)p.y + p.hi;
        }
    };
}

template <> inline
size_t stdext::hash_value<range_op >(const range_op& p)
{    
    std::hash<range_op> h;
    return h(p);
}

namespace std {
    template <>
    class less<range_op > {
    public:
        bool operator()(const range_op &x, const range_op &y) const {
            return (size_t)x.x < (size_t)y.x || x.x == y.x &&
                ((size_t)x.y < (size_t)y.y || x.y == y.y && x.hi < y.hi);
        }
    };
}

struct range_tables {
    hash_map<scopes::range_lo, scopes::range_lo *> unique;
    hash_map<range_op,scopes::range_lo *> lub;
    hash_map<range_op,scopes::range_lo *> glb;
};


scopes::range_lo *scopes::find_range_lo(int lo, range_lo *next){
    range_lo foo(lo,next);
    std::pair<range_lo,range_lo *> baz(foo,(range_lo *)0);
    std::pair<hash_map<range_lo,scopes::range_lo *>::iterator,bool> bar = rt->unique.insert(baz);
    if(bar.second)
        bar.first->second = new range_lo(lo,next);
    return bar.first->second;
    //std::pair<hash_set<scopes::range_lo>::iterator,bool> bar = rt->unique.insert(foo);
    // const range_lo *baz = &*(bar.first); 
    // return (range_lo *)baz; // coerce const
}

scopes::range_lo *scopes::range_lub_lo(range_lo *rng1, range_lo *rng2){
    if(!rng1) return rng2;
    if(!rng2) return rng1;
    if(rng1->lo > rng2->lo)
        std::swap(rng1,rng2);
    std::pair<range_op,range_lo *> foo(range_op(rng1,rng2,0),(range_lo *)0);
    std::pair<hash_map<range_op,scopes::range_lo *>::iterator,bool> bar = rt->lub.insert(foo);
    range_lo *&res = bar.first->second;
    if(!bar.second) return res;
    if(!(rng1->next && rng1->next->lo <= rng2->lo)){
        for(int lo = rng1->lo; lo <= rng2->lo; lo = parents[lo])
            if(lo == rng2->lo)
                {rng2 = rng2->next; break;}
    }
    range_lo *baz = range_lub_lo(rng1->next,rng2);
    res = find_range_lo(rng1->lo,baz);
    return res;
}
  

scopes::range_lo *scopes::range_glb_lo(range_lo *rng1, range_lo *rng2, int hi){
    if(!rng1) return rng1;
    if(!rng2) return rng2;
    if(rng1->lo > rng2->lo)
        std::swap(rng1,rng2);
    std::pair<range_op,range_lo *> cand(range_op(rng1,rng2,hi),(range_lo *)0);
    std::pair<hash_map<range_op,scopes::range_lo *>::iterator,bool> bar = rt->glb.insert(cand);
    range_lo *&res = bar.first->second;
    if(!bar.second) return res;
    range_lo *foo;
    if(!(rng1->next && rng1->next->lo <= rng2->lo)){
        int lim = hi;
        if(rng1->next) lim = std::min(lim,rng1->next->lo);
        int a = rng1->lo, b = rng2->lo;
        while(a != b && b <= lim){
            a = parents[a];
            if(a > b)std::swap(a,b);
        }
        if(a == b && b <= lim){
            foo = range_glb_lo(rng1->next,rng2->next,hi);
            foo = find_range_lo(b,foo);
        }
        else
            foo = range_glb_lo(rng2,rng1->next,hi);
    }
    else foo = range_glb_lo(rng1->next,rng2,hi);
    res = foo;
    return res;
}

/** computes the lub (smallest containing subtree) of two ranges */
scopes::range scopes::range_lub(const range &rng1, const range &rng2){
    int hi = tree_lca(rng1.hi,rng2.hi);
    if(hi == SHRT_MAX) return range_full();
    range_lo *lo = range_lub_lo(rng1.lo,rng2.lo);
    return range(hi,lo);
}

/** computes the glb (intersection) of two ranges */
scopes::range scopes::range_glb(const range &rng1, const range &rng2){
    if(rng1.hi == SHRT_MAX) return rng2;
    if(rng2.hi == SHRT_MAX) return rng1;
    int hi = tree_gcd(rng1.hi,rng2.hi);
    range_lo *lo = hi == SHRT_MIN ? 0 : range_glb_lo(rng1.lo,rng2.lo,hi);
    if(!lo) hi = SHRT_MIN;
    return range(hi,lo);
}

/** is this range empty? */
bool scopes::range_is_empty(const range &rng){
    return rng.hi == SHRT_MIN;
}

/** return an empty range */
scopes::range scopes::range_empty(){
    return range(SHRT_MIN,0);
}

/** return a full range */
scopes::range scopes::range_full(){
    return range(SHRT_MAX,0);
}

/** return the maximal element of a range */
int scopes::range_max(const range &rng){
    return rng.hi;
}

/** return a minimal (not necessarily unique) element of a range */
int scopes::range_min(const range &rng){
    if(rng.hi == SHRT_MAX) return SHRT_MIN;
    return rng.lo ? rng.lo->lo : SHRT_MAX;
}


/** return range consisting of downward closure of a point */
scopes::range scopes::range_downward(int _hi){
    std::vector<bool> descendants(parents.size());
    for(int i = descendants.size() - 1; i >= 0 ; i--)
        descendants[i] = i == _hi || parents[i] < parents.size() && descendants[parents[i]];
    for(unsigned i = 0; i < descendants.size() - 1; i++)
        if(parents[i] < parents.size())
            descendants[parents[i]] = false;
    range_lo *foo = 0;
    for(int i = descendants.size() - 1; i >= 0; --i)
        if(descendants[i]) foo = find_range_lo(i,foo);
    return range(_hi,foo);
}

/** add an element to a range */
void scopes::range_add(int i, range &n){
    range foo = range(i, find_range_lo(i,0));
    n = range_lub(foo,n);
}

/** Choose an element of rng1 that is near to rng2 */
int scopes::range_near(const range &rng1, const range &rng2){

    int frame;
    int thing = tree_lca(rng1.hi,rng2.hi);
    if(thing != rng1.hi) return rng1.hi;
    range line = range(rng1.hi,find_range_lo(rng2.hi,(range_lo *)0));
    line = range_glb(line,rng1);
    return range_min(line);
}


/** test whether a tree node is contained in a range */
bool scopes::in_range(int n, const range &rng){
    range r = range_empty();
    range_add(n,r);
    r = range_glb(rng,r);
    return !range_is_empty(r);
}

/** test whether two ranges of tree nodes intersect */
bool scopes::ranges_intersect(const range &rng1, const range &rng2){
    range r = range_glb(rng1,rng2);
    return !range_is_empty(r);
}


bool scopes::range_contained(const range &rng1, const range &rng2){
    range r = range_glb(rng1,rng2);
    return r.hi == rng1.hi && r.lo == rng1.lo;
}


#endif


