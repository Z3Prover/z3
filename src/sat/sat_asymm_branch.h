/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_asymm_branch.h

Abstract:

    SAT solver asymmetric branching

Author:

    Leonardo de Moura (leonardo) 2011-05-30.

Revision History:

--*/
#ifndef SAT_ASYMM_BRANCH_H_
#define SAT_ASYMM_BRANCH_H_

#include "sat/sat_types.h"
#include "sat/sat_big.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;
    class scoped_detach;

    class asymm_branch {
        struct report;
        
        solver &   s;
        params_ref m_params;
        int64_t    m_counter;
        random_gen m_rand;
        unsigned   m_calls;
        
        // config
        bool       m_asymm_branch;
        unsigned   m_asymm_branch_rounds;
        unsigned   m_asymm_branch_delay;
        bool       m_asymm_branch_sampled;
        bool       m_asymm_branch_all;
        int64_t    m_asymm_branch_limit;

        // stats
        unsigned   m_elim_literals;
        unsigned   m_elim_learned_literals;
        unsigned   m_tr;

        literal_vector m_pos, m_neg; // literals (complements of literals) in clauses sorted by discovery time (m_left in BIG).
        svector<std::pair<literal, unsigned>> m_pos1, m_neg1;
        literal_vector m_to_delete;
        literal_vector m_tmp;
       
        struct compare_left;

        void sort(big& big, literal const* begin, literal const* end);
        void sort(big & big, clause const& c);
        void radix_sort(big & big, literal_vector& lits);

        bool uhle(scoped_detach& scoped_d, big & big, clause & c);

        void uhle(big & big);

        bool uhte(big & big, clause & c);

        bool re_attach(scoped_detach& scoped_d, clause& c, unsigned new_sz);

        bool process(bool learned);

        bool process(big& big, bool learned);

        bool process(clause & c);

        bool process_sampled(big& big, clause & c);

        void process(big* big, clause_vector & c);
        
        bool process_all(clause & c);

        void process_bin(big& big);
        
        bool flip_literal_at(clause const& c, unsigned flip_index, unsigned& new_sz);
        
        bool cleanup(scoped_detach& scoped_d, clause& c, unsigned skip_index, unsigned new_sz);

        bool propagate_literal(clause const& c, literal l);

    public:
        asymm_branch(solver & s, params_ref const & p);

        void operator()(bool force);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        void minimize(big& big, literal_vector& lemma);

        void init_search() { m_calls = 0; }

        inline void dec(unsigned c) { m_counter -= c; }
    };

};

#endif
