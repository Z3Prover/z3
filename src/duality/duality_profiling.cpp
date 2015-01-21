/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    duality_profiling.cpp

Abstract:

   collection performance information for duality

Author:

    Ken McMillan (kenmcmil)

Revision History:


--*/


#include <map>
#include <iostream>
#include <string>
#include <string.h>
#include <stdlib.h>

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#endif

#include "duality_wrapper.h"
#include "iz3profiling.h"

namespace Duality {
  
  void show_time(){
    output_time(std::cout,current_time());
    std::cout << "\n";
  }

  typedef std::map<const char*, struct node> nmap;
  
  struct node {
    std::string name;
    clock_t time;
    clock_t start_time;
    nmap sub;
    struct node *parent;
    
    node();
  } top;
  
  node::node(){
    time =  0;
    parent = 0;
  }
  
  struct node *current;
  
  struct init {
    init(){
      top.name = "TOTAL";
      current = &top;
    }
  } initializer;
  
  struct time_entry {
    clock_t t;
    time_entry(){t = 0;};
    void add(clock_t incr){t += incr;}
  };
  
  struct ltstr
  {
    bool operator()(const char* s1, const char* s2) const
    {
      return strcmp(s1, s2) < 0;
    }
  };
  
  typedef  std::map<const char*, time_entry, ltstr> tmap;

  static std::ostream *pfs;

  void print_node(node &top, int indent, tmap &totals){
    for(int i = 0; i < indent; i++) (*pfs) << "  ";
    (*pfs) << top.name;
    int dots = 70 - 2 * indent - top.name.size();
    for(int i = 0; i <dots; i++) (*pfs) << ".";
    output_time(*pfs, top.time);
    (*pfs) << std::endl;
    if(indent != 0)totals[top.name.c_str()].add(top.time);
    for(nmap::iterator it = top.sub.begin(); it != top.sub.end(); it++)
      print_node(it->second,indent+1,totals);
  }
  
  void print_profile(std::ostream &os) {
    pfs = &os;
    top.time = 0;
    for(nmap::iterator it = top.sub.begin(); it != top.sub.end(); it++)
      top.time += it->second.time;
    tmap totals;
    print_node(top,0,totals);
    (*pfs) << "TOTALS:" << std::endl;
    for(tmap::iterator it = totals.begin(); it != totals.end(); it++){
      (*pfs) << (it->first) << " ";
      output_time(*pfs, it->second.t);
      (*pfs) << std::endl;
    }
    profiling::print(os); // print the interpolation stats
  }
  
  void timer_start(const char *name){
    node &child = current->sub[name];
    if(child.name.empty()){ // a new node
      child.parent = current;
      child.name = name;
    }
    child.start_time = current_time();
    current = &child;
  }

  void timer_stop(const char *name){
      if (current->name != name || !current->parent) {
#if 0
          std::cerr << "imbalanced timer_start and timer_stop";
          exit(1);
#endif
          // in case we lost a timer stop due to an exception
          while (current->name != name && current->parent)
              current = current->parent;
          if (current->parent) {
              current->time += (current_time() - current->start_time);
              current = current->parent;
          }
          return;
      }
    current->time += (current_time() - current->start_time);
    current = current->parent;
  }
}
