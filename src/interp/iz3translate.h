/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3translate.h

  Abstract:

  Interface for proof translations from Z3 proofs to interpolatable
  proofs.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/


#ifndef IZ3TRANSLATION_H
#define IZ3TRANSLATION_H

#include "iz3proof.h"
#include "iz3secondary.h"

// This is a interface class for translation from Z3 proof terms to
// an interpolatable proof

class iz3translation : public iz3base {
 public:
    virtual iz3proof::node translate(ast, iz3proof &) = 0;
    virtual ast quantify(ast e, const range &rng){return e;}
    virtual ~iz3translation(){}

    /** This is thrown when the proof cannot be translated. */
    struct unsupported: public iz3_exception {
        unsupported(): iz3_exception("unsupported") {}
    };

    static iz3translation *create(iz3mgr &mgr,
                                  iz3secondary *secondary,
                                  const std::vector<std::vector<ast> > &frames,
                                  const std::vector<int> &parents,
                                  const std::vector<ast> &theory);

 protected:
 iz3translation(iz3mgr &mgr,
		const std::vector<std::vector<ast> > &_cnsts,
		const std::vector<int> &_parents,
		const std::vector<ast> &_theory)
     : iz3base(mgr,_cnsts,_parents,_theory)  {}
};

// To use a secondary prover, define IZ3_TRANSLATE_DIRECT instead of this
#define IZ3_TRANSLATE_FULL

#endif



