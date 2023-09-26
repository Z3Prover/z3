/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_trim.h

  Abstract:
   
    proof replay and trim

  Author:

    Nikolaj Bjorner 2023-10-04

  Notes:
  

--*/

#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"

namespace sat {

    class proof_trim {
        solver         s;
        literal_vector m_clause, m_clause2, m_conflict;
        uint_set       m_in_deps;
        uint_set       m_in_clause;
        uint_set       m_in_coi;
        clause*        m_conflict_clause = nullptr;
        vector<std::tuple<unsigned, literal_vector, clause*, bool, bool>> m_trail;
        vector<std::pair<unsigned, unsigned_vector>> m_result;
        
        struct hash {
            unsigned operator()(literal_vector const& v) const {
                return string_hash((char const*)v.begin(), v.size()*sizeof(literal), 3);
            }
        };
        struct eq {
            bool operator()(literal_vector const& a, literal_vector const& b) const {
                return a == b;
            }
        };

        
        struct clause_info {
            clause_vector m_clauses;
            unsigned      m_id = 0;
            bool          m_in_core = false;
        };

        
        map<literal_vector, clause_info, hash, eq>   m_clauses;
        bool_vector                         m_propagated;

        void del(literal_vector const& cl, clause* cp);

        void prune_trail(literal_vector const& cl, clause* cp);
        void conflict_analysis_core(literal_vector const& cl, clause* cp);

        void add_dependency(literal lit);
        void add_dependency(justification j);
        void add_core(bool_var v);
        void add_core(literal l, justification j);
        bool in_core(literal_vector const& cl) const;
        void revive(literal_vector const& cl, clause* cp);        
        clause* del(literal_vector const& cl);

        void insert_dep(unsigned dep);

        uint_set m_units;
        bool unit_or_binary_occurs();
        void set_conflict(literal_vector const& c, clause* cp) { m_conflict.reset(); m_conflict.append(c); m_conflict_clause = cp;}
        
    public:

        proof_trim(params_ref const& p, reslimit& lim);

        bool_var mk_var() { return s.mk_var(true, true); }
        void init_clause() { m_clause.reset(); }
        void add_literal(bool_var v, bool sign) { m_clause.push_back(literal(v, sign)); }
        unsigned num_vars() { return s.num_vars(); }

        void assume(unsigned id, bool is_initial = true);
        void del();
        void infer(unsigned id);
        void updt_params(params_ref const& p) { s.updt_params(p); }

        vector<std::pair<unsigned, unsigned_vector>> trim();

    };
}
