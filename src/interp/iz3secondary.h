/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3secondary

  Abstract:

  Interface for secondary provers.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/


#ifndef IZ3SECONDARY_H
#define IZ3SECONDARY_H

/** Interface class for secondary provers. */

#include "iz3base.h"
#include <vector>

class iz3secondary : public iz3mgr {
 public:
    virtual int interpolate(const std::vector<ast> &frames, std::vector<ast> &interpolants) = 0;
    virtual ~iz3secondary(){}

 protected:
 iz3secondary(const iz3mgr &mgr) : iz3mgr(mgr) {}
};



#endif
