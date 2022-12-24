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
    
    class bit_dependency {
        optional<pdd> m_pdd;
        unsigned m_bit_idx;
        
    public:
        
        bit_dependency() : m_pdd(optional<dd::pdd>::undef()), m_bit_idx(0) {}
        bit_dependency(const bit_dependency& v) = default;
        bit_dependency(bit_dependency&& v) = default;
        
        bit_dependency(const pdd& pdd, unsigned bit_idx) : m_pdd(pdd), m_bit_idx(bit_idx) {}
                    
        bool operator==(const bit_dependency& other) const {
            return m_pdd == other.m_pdd && m_bit_idx == other.m_bit_idx;
        }
        
        bit_dependency& operator=(bit_dependency&& other) {
            m_pdd = other.m_pdd;
            m_bit_idx = other.m_bit_idx;
            return *this;
        }
        
        bit_dependency& operator=(bit_dependency& other) {
            m_pdd = other.m_pdd;
            m_bit_idx = other.m_bit_idx;
            return *this;
        }
        
        unsigned idx() const { return m_bit_idx; }
        const pdd& pdd() const { return *m_pdd; }
    };
    
    using bit_dependencies = vector<bit_dependency>;
    
    class bit_justication {
    protected:
        static bit_justication* get_other_justification(const fixed_bits& fixed, const pdd& p, unsigned idx);
        static const tbv_ref* get_tbv(fixed_bits& fixed, const pdd& p);
        static bool fix_value_core(solver& s, fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication** j);
        static bool fix_value_core(solver& s, fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j);
    public:
        virtual bool can_dealloc() { return true; }
        virtual bool has_constraint(constraint*& constr) { return false; }
        virtual void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) = 0; // returns if element may be deallocated after call (usually true)
    };
    
    // if multiple bits are justified by the same justification
    class bit_justication_shared : public bit_justication {
        bit_justication* m_justification;
        unsigned m_references = 0;
    public:
        bit_justication_shared() = default;
        bit_justication_shared(bit_justication* j) : m_justification(j), m_references(1) {}
        
        bit_justication* get_justification() { return m_justification; }
        
        virtual bool can_dealloc() {
            m_references = m_references == 0 ? 0 : m_references - 1;
            if (m_references != 0)
                return false;
            if (m_justification->can_dealloc()) {
                dealloc(m_justification);
                m_justification = nullptr;
            }
            return true;
        }
        
        virtual void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override {
            SASSERT(m_justification);
            m_justification->get_dependencies(fixed, to_process);
        }
        
        void inc_ref() { m_references++; }
    };
    
    class bit_justication_constraint : public bit_justication {
        
        constraint* m_constraint = nullptr;
    
        // A pdd might occur multiple times if more bits of it are relevant
        bit_dependencies m_dependencies;
        
        bit_justication_constraint(constraint* c) : m_constraint(c) {}
        bit_justication_constraint(constraint* c, const bit_dependencies& dep) : m_constraint(c), m_dependencies(dep) {}
        bit_justication_constraint(constraint* c, bit_dependencies&& dep) : m_constraint(c), m_dependencies(dep) {}
        
    public:
        
        bit_justication_constraint() = default;
        
        bool has_constraint(constraint*& constr) { 
            constr = m_constraint;
            return true;
        }
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
        
        static bit_justication_constraint* mk_assignment(constraint* c) { return alloc(bit_justication_constraint, c ); }
        static bit_justication_constraint* mk_unary(constraint* c, bit_dependency v) {
            bit_dependencies dep;
            dep.push_back(std::move(v));
            return alloc(bit_justication_constraint, c, std::move(dep));
        }
        static bit_justication_constraint* mk_binary(constraint* c, bit_dependency v1, bit_dependency v2) {
            bit_dependencies dep;
            dep.push_back(std::move(v1));
            dep.push_back(std::move(v2));
            return alloc(bit_justication_constraint, c, std::move(dep));
        }
        static bit_justication_constraint* mk(constraint* c, const bit_dependencies& dep) { return alloc(bit_justication_constraint, c, dep); }
        
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
        optional<pdd> m_p, m_q, m_r;
        unsigned_vector m_bit_indexes;
        
    public:
        
        bit_justication_mul() = default;
        bit_justication_mul(unsigned idx, const pdd& p, const pdd& q) : m_idx(idx), m_p(p), m_q(q) {}
        bit_justication_mul(unsigned idx, const pdd& p, const pdd& q, const pdd& r) : m_idx(idx), m_p(p), m_q(q), m_r(r) {}
        
        // propagates from p, q => r (forward) and r, p/q => q/p (backward)
        static void propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd &p, const pdd &q);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
        void get_dependencies_forward(fixed_bits &fixed, bit_dependencies &to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range);
        void get_dependencies_backward(fixed_bits& fixed, bit_dependencies& to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range);
    };
    
    class bit_justication_add : public bit_justication {
        
        unsigned m_idx;
        optional<pdd> m_c1, m_c2;
        
    public:
        
        bit_justication_add() = default;
        bit_justication_add(unsigned idx, const pdd& c1, const pdd& c2) : m_idx(idx), m_c1(c1), m_c2(c2) {}
        
        static void propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd& p, const pdd& q);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
    };
    

    class fixed_bits final {

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
        using pdd_to_tbv_map = map<pdd_to_tbv_key, tbv_ref*, pdd_to_tbv_hash, pdd_to_tbv_eq>;
        
        using tbv_to_justification_key = bit_dependency;
        using tbv_to_justification_eq = default_eq<tbv_to_justification_key>;
        struct tbv_to_justification_hash {
            unsigned operator()(tbv_to_justification_key const& args) const {
                return combine_hash(args.pdd().hash(), args.idx());
            }
        };
        using tbv_to_justification_map = map<tbv_to_justification_key, bit_justication*, tbv_to_justification_hash, tbv_to_justification_eq>;

        //vector<optional<tbv_ref>> m_var_to_tbv;
        pdd_to_tbv_map m_var_to_tbv; // TODO: free tbv_ref pointers
        tbv_to_justification_map m_tbv_to_justification; // the elements are pointers. Deallocate them before replacing them
        
        bool m_consistent = true; // in case evaluating results in a bit-conflict

        tbv_manager& get_manager(const pdd& v);
        tbv_manager& get_manager(unsigned sz);
        
        clause_ref get_explanation(solver& s, bit_justication* j1, bit_justication* j2);
        bool fix_value_core(const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j);
        bool fix_value(solver& s, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j);
        
        void propagate_to_subterm(solver& s, const pdd& p);
        
    public:

        fixed_bits(solver& s) : m_solver(s) {}        
        
        ~fixed_bits() {
            for (auto& tbv : m_var_to_tbv) {
                dealloc(tbv.m_value);
            }
        }
        
        tbv_ref* get_tbv(const pdd& p);

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

        tbv_ref* eval(solver& s, const pdd& p);

};
}
