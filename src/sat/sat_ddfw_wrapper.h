/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_ddfw_wrapper.h


  --*/
#pragma once

#include "util/uint_set.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "util/ema.h"
#include "util/sat_sls.h"
#include "util/map.h"
#include "ast/sls/sat_ddfw.h"
#include "sat/sat_types.h"

namespace sat {
    class solver;
    class parallel;


    class ddfw_wrapper : public i_local_search {
    protected:
        ddfw m_ddfw;
        parallel* m_par = nullptr;
        unsigned m_parsync_count = 0;
        uint64_t m_parsync_next = 0;

        void do_parallel_sync();
        bool should_parallel_sync();

    public:

        ddfw_wrapper() {}
        
        ~ddfw_wrapper() override {}

        void set_plugin(local_search_plugin* p) { m_ddfw.set_plugin(p); }

        lbool check(unsigned sz, literal const* assumptions, parallel* p) override;

        void updt_params(params_ref const& p) override { m_ddfw.updt_params(p); }

        model const& get_model() const override { return m_ddfw.get_model(); }

        reslimit& rlimit() override { return m_ddfw.rlimit(); }

        void set_seed(unsigned n) override { m_ddfw.set_seed(n); }

        void add(solver const& s) override;

        bool get_value(bool_var v) const override { return m_ddfw.get_value(v); }
       
        std::ostream& display(std::ostream& out) const { return m_ddfw.display(out); }

        // for parallel integration
        unsigned num_non_binary_clauses() const override { return m_ddfw.num_non_binary_clauses(); }
        
        void reinit(solver& s, bool_vector const& phase) override;

        void collect_statistics(statistics& st) const override {} 

        double get_priority(bool_var v) const override { return m_ddfw.get_priority(v); }

        // access clause information and state of Boolean search
        indexed_uint_set& unsat_set() { return m_ddfw.unsat_set(); }
        
        vector<clause_info> const& clauses() const { return m_ddfw.clauses(); }

        clause_info& get_clause_info(unsigned idx) { return m_ddfw.get_clause_info(idx); }

        void remove_assumptions() { m_ddfw.remove_assumptions(); }

        void flip(bool_var v) { m_ddfw.flip(v); }

        inline double get_reward(bool_var v) const { return m_ddfw.reward(v); }

        void add(unsigned sz, literal const* c) { m_ddfw.add(sz, c); }

        void reinit() { m_ddfw.reinit(); }


    };
}

