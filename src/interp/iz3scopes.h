/* Copyright 2011 Microsoft Research. */

#ifndef IZ3SOPES_H
#define IZ3SOPES_H

#include <vector>
#include <limits.h>

class scopes {

 public:
  /** Construct from parents vector. */
  scopes(const std::vector<int> &_parents){
    parents = _parents;
  }

  /** The parents vector defining the tree structure */
  std::vector<int> parents;

  // #define FULL_TREE
#ifndef FULL_TREE
  struct range {
    range(){
      lo = SHRT_MAX;
      hi = SHRT_MIN;
    }
    short lo, hi;
  };

  /** computes the lub (smallest containing subtree) of two ranges */
  range range_lub(const range &rng1, const range &rng2);
  
  /** computes the glb (intersection) of two ranges */
  range range_glb(const range &rng1, const range &rng2);

  /** is this range empty? */
  bool range_is_empty(const range &rng){
	  return rng.hi < rng.lo;
  }

  /** return an empty range */
  range range_empty(){
     range res;
	 res.lo = SHRT_MAX;
	 res.hi = SHRT_MIN;
	 return res;
  }

  /** return an empty range */
  range range_full(){
     range res;
	 res.lo = SHRT_MIN;
	 res.hi = SHRT_MAX;
	 return res;
  }

  /** return the maximal element of a range */
  int range_max(const range &rng){
	  return rng.hi;
  }

  /** return a minimal (not necessarily unique) element of a range */
  int range_min(const range &rng){
	  return rng.lo;
  }

  /** return range consisting of downward closure of a point */
  range range_downward(int _hi){
    range foo;
    foo.lo = SHRT_MIN;
    foo.hi = _hi;
    return foo;
  }

  void range_add(int i, range &n){
	if(i < n.lo) n.lo = i;
    if(i > n.hi) n.hi = i;
  }

  /** Choose an element of rng1 that is near to rng2 */
  int range_near(const range &rng1, const range &rng2){
    int frame;
    int thing = tree_lca(rng1.lo,rng2.hi);
    if(thing == rng1.lo) frame = rng1.lo;
    else frame = tree_gcd(thing,rng1.hi);
	return frame;
  }
#else

  struct range_lo {
    int lo;
    range_lo *next;
    range_lo(int _lo, range_lo *_next){
      lo = _lo;
      next = _next;
    }
  };

  struct range {
    int hi;
    range_lo *lo;
    range(int _hi, range_lo *_lo){
      hi = _hi;
      lo = _lo;
    }
    range(){
      hi = SHRT_MIN;
      lo = 0;
    }
  };

  range_tables *rt;

  /** computes the lub (smallest containing subtree) of two ranges */
  range range_lub(const range &rng1, const range &rng2);
  
  /** computes the glb (intersection) of two ranges */
  range range_glb(const range &rng1, const range &rng2);

  /** is this range empty? */
  bool range_is_empty(const range &rng);

  /** return an empty range */
  range range_empty();

  /** return a full range */
  range range_full();

  /** return the maximal element of a range */
  int range_max(const range &rng);

  /** return a minimal (not necessarily unique) element of a range */
  int range_min(const range &rng);

  /** return range consisting of downward closure of a point */
  range range_downward(int _hi);

  /** add an element to a range */
  void range_add(int i, range &n);

  /** Choose an element of rng1 that is near to rng2 */
  int range_near(const range &rng1, const range &rng2);

  range_lo *find_range_lo(int lo, range_lo *next);
  range_lo *range_lub_lo(range_lo *rng1, range_lo *rng2);
  range_lo *range_glb_lo(range_lo *rng1, range_lo *rng2, int lim);

#endif
  
  /** test whether a tree node is contained in a range */
  bool in_range(int n, const range &rng);
  
  /** test whether two ranges of tree nodes intersect */
  bool ranges_intersect(const range &rng1, const range &rng2);

  /** test whether range rng1 contained in range rng2 */
  bool range_contained(const range &rng1, const range &rng2);

 private:
  int tree_lca(int n1, int n2);
  int tree_gcd(int n1, int n2);
  bool tree_mode(){return parents.size() != 0;}



};
#endif
