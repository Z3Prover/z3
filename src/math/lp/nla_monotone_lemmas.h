/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
   Lev Nachmanson (levnach)
   Nikolaj Bjorner (nbjorner)
  --*/
#pragma once
#include "util/hashtable.h"
#include "util/hash.h"

namespace nla {
    class core;
    class monotone : common {    
    public:
        monotone(core *core);
        void monotonicity_lemma();
        
        // Structure to represent the key parameters for throttling monotonicity_lemma
        struct monotone_key {
            short mvar;
            bool is_lt;
            
            // Default constructor for hashtable
            monotone_key() : mvar(0), is_lt(false) {}
            
            monotone_key(lpvar mvar, bool is_lt)
                : mvar(static_cast<short>(mvar)), is_lt(is_lt) {}
                
            bool operator==(const monotone_key& other) const {
                return mvar == other.mvar && is_lt == other.is_lt;
            }
        };
        
        struct monotone_key_hash {
            unsigned operator()(const monotone_key& k) const {
                return combine_hash(static_cast<unsigned>(k.mvar), 
                                  static_cast<unsigned>(k.is_lt));
            }
        };
        
    private:
        hashtable<monotone_key, monotone_key_hash, default_eq<monotone_key>> m_processed_monotone;
        bool throttle_monotone(const monic& m, bool is_lt);
        
        void monotonicity_lemma(monic const& m);
        void monotonicity_lemma_gt(const monic& m);    
        void monotonicity_lemma_lt(const monic& m);
    };
}
