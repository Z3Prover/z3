/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    fixed_bits

Abstract:

    Associates every pdd with the set of already fixed bits and justifications for this

--*/
#pragma once

#include "types.h"
#include "util/hash.h"
#include "util/optional.h"
#include "util/tbv.h"


namespace polysat {

    class solver;

    using bit_dependency = vector<std::pair<pdd, unsigned>>;

    struct bit_justication {
        constraint* m_constraint = nullptr;

        // variables + resp., bit-index
        // (a variable might occur multiple times if more bits are relevant)
        bit_dependency m_dependencies;

    public:
        bit_justication(constraint *pRaint, bit_dependency vector) = default;
        bit_justication(constraint* c) : m_constraint(c) { }
        bit_justication(constraint* c, bit_dependency&& dep) : m_constraint(c), m_dependencies(dep) { }
    };

    class fixed_bits {

        solver& m_solver;

        scoped_ptr_vector<tbv_manager> m_tbv_managers;

        char_vector m_aux_values;

        //using pdd_to_tbv_key = optional<pdd>;
        //using pdd_to_tbv_eq = default_eq<pdd_to_tbv_key>;
        //struct pdd_to_tbv_hash {
        //    unsigned operator()(pdd_to_tbv_key const& args) const {
        //        return args ? args->hash() : 0;
        //    }
        //};
        //using pdd_to_tbv_map = map<pdd_to_tbv_key, tbv_ref, pdd_to_tbv_hash, pdd_to_tbv_eq>;

        using tbv_to_justification_key = std::pair<tbv*, unsigned>;
        using tbv_to_justification_eq = default_eq<tbv_to_justification_key>;
        struct tbv_to_justification_hash {
            unsigned operator()(tbv_to_justification_key const& args) const {
                return combine_hash((unsigned)args.first, args.second);
            }
        };
        using tbv_to_justification_map = map<tbv_to_justification_key, bit_justication, tbv_to_justification_hash, tbv_to_justification_eq>;

        vector<optional<tbv_ref>> m_var_to_tbv;
        tbv_to_justification_map m_tbv_to_justification;

        tbv_manager& get_manager(const pdd& v);
        tbv_manager& get_manager(unsigned sz);

        void add(tbv_ref& in_out, const tbv_ref& in2);
        void multiply(tbv_ref& in_out, const tbv_ref& in2);

        tbv_ref& get_tbv(pvar v, unsigned sz);
        tbv_ref& get_tbv(const pdd& p);

    public:

        fixed_bits(solver& s) : m_solver(s) {}

        // #count [min; max]
        static std::pair<unsigned, unsigned> leading_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> leading_ones(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_ones(const tbv_ref& ref);
        static std::pair<rational, rational> min_max(const tbv_ref& ref);

        tbit get_value(const pdd& p, unsigned idx); // More efficient than calling "eval" and accessing the returned tbv elements
        bool fix_value(solver& s, const pdd& p, unsigned idx, tbit val, constraint* c, bit_dependency& dep);
        bool fix_value(solver& s, const pdd& p, unsigned idx, tbit val, constraint* c, std::pair<pdd, unsigned> v1, std::pair<pdd, unsigned> v2) {
            bit_dependency dep(2);
            dep.push_back(v1);
            dep.push_back(v2);
            return fix_value(s, p, idx, val, c, dep);
        }
        void clear_value(const pdd& p, unsigned idx);

        tbv_ref eval(const pdd& p);

    };
}
