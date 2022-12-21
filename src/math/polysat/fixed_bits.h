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
    class constraint;
    class fixed_bits;
    
    struct bit_dependency {
        optional<pdd> m_pdd;
        unsigned m_bit_idx;
        
        bit_dependency() : m_pdd(optional<pdd>::undef()), m_bit_idx(0) {}
        bit_dependency(const bit_dependency& v) = default;
        bit_dependency(bit_dependency&& v) = default;
        
        bit_dependency(const pdd& pdd, unsigned bit_idx) : m_pdd(pdd), m_bit_idx(bit_idx) {}
                    
        bool operator==(const bit_dependency& other) const {
            return m_pdd == other.m_pdd && m_bit_idx == other.m_bit_idx;
        }
        
    };
    
    using bit_dependencies = vector<bit_dependency>;
    
    class bit_justication {
    protected:
        static bit_justication* get_other_justification(const fixed_bits& fixed, const pdd& p, unsigned idx);
        static const tbv_ref& get_tbv(fixed_bits& fixed, const pdd& p);
        static bool fix_value(fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j);
    public:
        virtual bool has_constraint(constraint*& constr) { return false; }
        virtual void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) = 0;
    };
    
    class bit_justication_constraint : public bit_justication {
        
        constraint* m_constraint = nullptr;
    
        // A pdd might occur multiple times if more bits of it are relevant
        bit_dependencies m_dependencies;
        
        bit_justication_constraint(constraint* c) : m_constraint(c) { }
        bit_justication_constraint(constraint* c, bit_dependencies&& dep) : m_constraint(c), m_dependencies(dep) { }
        
    public:
        
        bit_justication_constraint() = default;
        
        bool has_constraint(constraint*& constr) { 
            constr = m_constraint;
            return true;
        }
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
        
        static bit_justication_constraint* mk_assignment(constraint* c) { return alloc(bit_justication_constraint, c ); }
        static bit_justication_constraint* mk_unary(constraint* c, bit_dependency v) {
            bit_dependencies dep(1);
            dep.push_back(std::move(v));
            return alloc(bit_justication_constraint, c, std::move(dep));
        }
        static bit_justication_constraint* mk_binary(constraint* c, bit_dependency v1, bit_dependency v2) {
            bit_dependencies dep(2);
            dep.push_back(std::move(v1));
            dep.push_back(std::move(v2));
            return alloc(bit_justication_constraint, c, std::move(dep));
        }
        // gives the highest bits such that they already enforce a value of "tbv" that is at least "val"
        static bit_justication_constraint* mk_justify_at_least(constraint *c, const pdd& v, const tbv_ref& tbv, const rational& least);
        // similar to mk_justify_at_least: gives the highest bits such that they already enforce a value of "tbv" that is at most "val"
        static bit_justication_constraint* mk_justify_at_most(constraint *c, const pdd& v, const tbv_ref& tbv, const rational& most);
        // a combination of mk_justify_at_least and mk_justify_at_most
        static bit_justication_constraint* mk_justify_between(constraint *c, const pdd& v, const tbv_ref& tbv, rational least, rational most);
        
    };
    
    // lazy generation of the justifications. Generating them eagerly can generate a huge overhead
    class bit_justication_mul : public bit_justication {
        
        unsigned m_idx;
        optional<pdd> m_c1, m_c2;
        
    public:
        
        bit_justication_mul() = default;
        bit_justication_mul(unsigned idx, const pdd& c1, const pdd& c2) : m_idx(idx), m_c1(c1), m_c2(c2) {}
        
        static tbv_ref& mul(fixed_bits& fixed, const pdd& p, const tbv_ref& in1, const tbv_ref& in2);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
    };
    
    class bit_justication_add : public bit_justication {
        
        unsigned m_idx;
        optional<pdd> m_c1, m_c2;
        
    public:
        
        bit_justication_add() = default;
        bit_justication_add(unsigned idx, const pdd& c1, const pdd& c2) : m_idx(idx), m_c1(c1), m_c2(c2) {}
        
        static tbv_ref& add(fixed_bits& fixed, const pdd& p, const tbv_ref& in1, const tbv_ref& in2);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
    };
    

    class fixed_bits {

        friend bit_justication;
        
        solver& m_solver;
        scoped_ptr_vector<tbv_manager> m_tbv_managers;
        
        using pdd_to_tbv_key = optional<pdd>;
        using pdd_to_tbv_eq = default_eq<pdd_to_tbv_key>;
        struct pdd_to_tbv_hash {
            unsigned operator()(pdd_to_tbv_key const& args) const {
                return args ? args->hash() : 0;
            }
        };
        using pdd_to_tbv_map = map<pdd_to_tbv_key, optional<tbv_ref>, pdd_to_tbv_hash, pdd_to_tbv_eq>;
        
        using tbv_to_justification_key = bit_dependency;
        using tbv_to_justification_eq = default_eq<tbv_to_justification_key>;
        struct tbv_to_justification_hash {
            unsigned operator()(tbv_to_justification_key const& args) const {
                return combine_hash((*args.m_pdd).hash(), args.m_bit_idx);
            }
        };
        using tbv_to_justification_map = map<tbv_to_justification_key, bit_justication*, tbv_to_justification_hash, tbv_to_justification_eq>;

        //vector<optional<tbv_ref>> m_var_to_tbv;
        pdd_to_tbv_map m_var_to_tbv;
        tbv_to_justification_map m_tbv_to_justification; // the elements are pointers. Deallocate them before replacing them
        
        bool m_consistent = true; // in case evaluating results in a bit-conflict

        tbv_manager& get_manager(const pdd& v);
        tbv_manager& get_manager(unsigned sz);
        
        clause_ref get_explanation(solver& s, bit_justication* j1, bit_justication* j2);
        bool fix_value(const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j);
        
    public:

        fixed_bits(solver& s) : m_solver(s) {}        
        
        tbv_ref& get_tbv(const pdd& p);

        // #count [min; max]
        static std::pair<unsigned, unsigned> leading_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> leading_ones(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_ones(const tbv_ref& ref);
        static std::pair<rational, rational> min_max(const tbv_ref& ref);

        tbit get_value(const pdd& p, unsigned idx); // More efficient than calling "eval" and accessing the returned tbv elements
        // call this function also if we already know that the correct value is written there. We might decrease the decision level (for "replay")
        bool fix_value(solver& s, const pdd& p, unsigned idx, tbit val, bit_justication* j);
        void clear_value(const pdd& p, unsigned idx);

        tbv_ref& eval(solver& s, const pdd& p);

};
}
