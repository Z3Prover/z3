/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    iz3hash.h

Abstract:

   Wrapper for stl hash tables

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

// pull in the headers for has_map and hash_set
// these live in non-standard places

#ifndef IZ3_HASH_H
#define IZ3_HASH_H

//#define USE_UNORDERED_MAP
#ifdef USE_UNORDERED_MAP

#define stl_ext std
#define hash_space std
#include <unordered_map>
#include <unordered_set>
#define hash_map unordered_map
#define hash_set unordered_set

#else

#if __GNUC__ >= 3
#undef __DEPRECATED
#define stl_ext __gnu_cxx
#define hash_space stl_ext
#include <ext/hash_map>
#include <ext/hash_set>
#else
#ifdef WIN32
#define stl_ext stdext
#define hash_space std
#include <hash_map>
#include <hash_set>
#else
#define stl_ext std
#define hash_space std
#include <hash_map>
#include <hash_set>
#endif
#endif

#endif

#include <string>

// stupid STL doesn't include hash function for class string

#ifndef WIN32 

namespace stl_ext {
  template <>
    class hash<std::string> {
    stl_ext::hash<char *> H;
  public:
    size_t operator()(const std::string &s) const {
      return H(s.c_str());
    }
  };
}

#endif

namespace hash_space {
  template <>
    class hash<std::pair<int,int> > {
  public:
    size_t operator()(const std::pair<int,int> &p) const {
      return p.first + p.second;
    }
  };
}

#ifdef WIN32 
template <> inline
size_t stdext::hash_value<std::pair<int,int> >(const std::pair<int,int>& p)
{	// hash _Keyval to size_t value one-to-one
	return p.first + p.second;
}
#endif

namespace hash_space {
  template <class T>
    class hash<std::pair<T *, T *> > {
  public:
    size_t operator()(const std::pair<T *,T *> &p) const {
      return (size_t)p.first + (size_t)p.second;
    }
  };
}

#if 0
template <class T> inline
size_t stdext::hash_value<std::pair<T *, T *> >(const std::pair<T *, T *>& p)
{	// hash _Keyval to size_t value one-to-one
  return (size_t)p.first + (size_t)p.second;
}
#endif

#ifdef WIN32

namespace std {
    template <>
	   class less<std::pair<int,int> > {
	   public:
		   bool operator()(const pair<int,int> &x, const pair<int,int> &y) const {
		      return x.first < y.first || x.first == y.first && x.second < y.second;
		   }
	   };
	
}
  
namespace std {
    template <class T>
	   class less<std::pair<T *,T *> > {
	   public:
		   bool operator()(const pair<T *,T *> &x, const pair<T *,T *> &y) const {
		     return (size_t)x.first < (size_t)y.first || (size_t)x.first == (size_t)y.first && (size_t)x.second < (size_t)y.second;
		   }
	   };
	
}

#endif


#ifndef WIN32

#if 0
namespace stl_ext {
  template <class T>
    class hash<T *> {
  public:
    size_t operator()(const T *p) const {
      return (size_t) p;
    }
  };
}
#endif

#endif

#ifdef WIN32




template <class K, class T>
class hash_map : public stl_ext::hash_map<K,T,stl_ext::hash_compare<K,std::less<K> > > {};

template <class K>
class hash_set : public stl_ext::hash_set<K,stl_ext::hash_compare<K,std::less<K> > > {};

#endif

#endif
