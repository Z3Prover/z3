/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    fixed_bits

Abstract:

    Associates every pdd with the set of already fixed bits and justifications for this

--*/
#pragma once

#include "math/polysat/constraint.h"
#include "math/polysat/types.h"
#include "util/hash.h"
#include "util/optional.h"
#include "util/tbv.h"


namespace polysat {

    class solver;
    class constraint;
    class fixed_bits;
    class bitvec_info;

    struct bvpos {
        optional<pdd> m_pdd;
        unsigned m_bit_idx;
        
    public:
        
        bvpos() : m_pdd(optional<dd::pdd>::undef()), m_bit_idx(0) {}
        bvpos(const bvpos& v) = default;
        bvpos(bvpos&& v) = default;
        
        bvpos(const pdd& pdd, unsigned bit_idx) : m_pdd(pdd), m_bit_idx(bit_idx) {}
                    
        bool operator==(const bvpos& other) const {
            return m_pdd == other.m_pdd && m_bit_idx == other.m_bit_idx;
        }
        
        bvpos& operator=(bvpos&& other) {
            m_pdd = other.m_pdd;
            m_bit_idx = other.m_bit_idx;
            return *this;
        }
        
        bvpos& operator=(bvpos& other) {
            m_pdd = other.m_pdd;
            m_bit_idx = other.m_bit_idx;
            return *this;
        }
        
        unsigned get_idx() const { return m_bit_idx; }
        const pdd& get_pdd() const { return *m_pdd; }
    };
    
    using bit_dependencies = vector<bvpos>;
    
    class bit_justification {
    protected:
        static bit_justification* get_justification(fixed_bits& fixed, const pdd& p, unsigned idx);
        static unsigned get_level(fixed_bits& fixed, const pdd& p, unsigned idx);
        static const tbv_ref* get_tbv(fixed_bits& fixed, const pdd& p);

        bit_justification() = default;
    public:
        virtual ~bit_justification() = default;

         // if we reduce this value we would have to reduce some decision levels of justifications depending on it.
         // However, we don't do this for now. (Should be still correct but generate weaker justifications)
         // This value is used for comparing which of two justifications is better. Does not have to be 100% correct
         unsigned m_decision_level = UINT32_MAX; // maybe better "weight"?
        
        virtual bool can_dealloc() { return true; } // we may not dealloc if the justification is used for multiple bits
        virtual bool has_constraint(constraint*& constr) { return false; }
        virtual void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) = 0; // returns if element may be deallocated after call (usually true)
    };
    
    // if multiple bits are justified by the same justification
    // All elements have to be in the same decision-level
    class bit_justification_shared : public bit_justification {
        bit_justification* m_justification;
        unsigned m_references = 0;
    public:
        bit_justification_shared(bit_justification* j) : m_justification(j), m_references(1) {
            SASSERT(j);
            m_decision_level = j->m_decision_level;
        }
        
        bit_justification* get_justification() { return m_justification; }
        
        bool can_dealloc() override {
            m_references = m_references == 0 ? 0 : m_references - 1;
            if (m_references != 0)
                return false;
            if (m_justification->can_dealloc()) {
                dealloc(m_justification);
                m_justification = nullptr;
            }
            return true;
        }
        
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override {
            SASSERT(m_justification);
            m_justification->get_dependencies(fixed, to_process);
        }
        
        void inc_ref() { m_references++; }
    };
    
    class bit_justification_constraint : public bit_justification {
        
        constraint* m_constraint = nullptr;
    
        // A pdd might occur multiple times if more bits of it are relevant
        bit_dependencies m_dependencies;
        
        bit_justification_constraint(solver& s, constraint* c, bit_dependencies&& dep);
        bit_justification_constraint(solver& s, constraint* c, const bit_dependencies& dep) : bit_justification_constraint(s, c, bit_dependencies(dep)) {}
        bit_justification_constraint(solver& s, constraint* c) : bit_justification_constraint(s, c, bit_dependencies()) {}

    public:

        bool has_constraint(constraint*& constr) override {
            constr = m_constraint;
            return true;
        }
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
        
        static bit_justification_constraint* mk_assignment(solver& s, constraint* c) { return alloc(bit_justification_constraint, s, c); }
        static bit_justification_constraint* mk_unary(solver& s, constraint* c, bvpos v) {
            bit_dependencies dep;
            dep.push_back(std::move(v));
            return alloc(bit_justification_constraint, s, c, std::move(dep));
        }
        static bit_justification_constraint* mk_binary(solver& s, constraint* c, bvpos v1, bvpos v2) {
            bit_dependencies dep;
            dep.push_back(std::move(v1));
            dep.push_back(std::move(v2));
            return alloc(bit_justification_constraint, s, c, std::move(dep));
        }
        static bit_justification_constraint* mk(solver& s, constraint* c, const bit_dependencies& dep) { return alloc(bit_justification_constraint, s, c, dep); }
        
        // gives the highest bits such that they already enforce a value of "tbv" that is at least "val"
        static bit_justification_constraint* mk_justify_at_least(solver& s, constraint *c, const pdd& v, const tbv_ref& tbv, const rational& least);
        // similar to mk_justify_at_least: gives the highest bits such that they already enforce a value of "tbv" that is at most "val"
        static bit_justification_constraint* mk_justify_at_most(solver& s, constraint *c, const pdd& v, const tbv_ref& tbv, const rational& most);
        // a combination of mk_justify_at_least and mk_justify_at_most
        static bit_justification_constraint* mk_justify_between(solver& s, constraint *c, const pdd& v, const tbv_ref& tbv, rational least, rational most);
        
    };
    
    // lazy generation of the justifications. Generating them eagerly can generate a huge overhead
    class bit_justification_mul : public bit_justification {
        
        unsigned m_idx;
        optional<pdd> m_p, m_q, m_r;
        unsigned_vector m_bit_indexes;
        
    public:
        
        bit_justification_mul(unsigned idx, const pdd& p, const pdd& q, const pdd& r) : m_idx(idx), m_p(p), m_q(q), m_r(r) {
            // we can also track the decision level but multiplications are unpleasant anyway.
            // We prefer any other justification (Othw. take the max of all coefficients that influence the result)
            m_decision_level = UINT32_MAX;
        }
        bit_justification_mul(unsigned idx, const pdd& p, const pdd& q) : m_idx(idx), m_p(p), m_q(q) {
            m_decision_level = UINT32_MAX;
        }

        // propagates from p, q => r (forward) and r, p/q => q/p (backward)
        static void propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd &p, const pdd &q);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
        void get_dependencies_forward(fixed_bits &fixed, bit_dependencies &to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range);
        void get_dependencies_backward(fixed_bits& fixed, bit_dependencies& to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range);
    };
    
    class bit_justification_add : public bit_justification {
        
        unsigned m_idx;
        optional<pdd> m_c1, m_c2;
        
    public:
        
        bit_justification_add(unsigned lvl, unsigned idx, const pdd& c1, const pdd& c2) : m_idx(idx), m_c1(c1), m_c2(c2) {
            m_decision_level = lvl;
        }
        
        static void propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd& p, const pdd& q);
        void get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) override;
    };
    
    struct justified_bvpos : public bvpos {
        bit_justification* m_justification;
        
        justified_bvpos() = default;
        
        justified_bvpos(const pdd & pdd, unsigned idx, bit_justification* jstfc) :
            bvpos(pdd, idx), m_justification(jstfc) {}
            
        justified_bvpos(const bvpos& pos, bit_justification* jstfc) :
            bvpos(pos), m_justification(jstfc) {}

        void set(bit_justification* new_justification){
            if (m_justification && m_justification->can_dealloc())
                dealloc(m_justification);
            m_justification = new_justification;
        }
    };

    class bitvec_info {
        tbv_ref* m_bits = nullptr;
        justified_bvpos* m_justifications = nullptr; // do not alter this pointer (except setting it 0 for moving - we refer to it in trail)
        unsigned m_unset = 0; // For constant pdds this value is completely ignored/not maintained

    public:

        bitvec_info() = default;
        bitvec_info(tbv_ref* bits) : m_bits(bits), m_justifications(alloc_vect<justified_bvpos>(bits->num_tbits())), m_unset(bits->num_tbits()) {}
        bitvec_info(bitvec_info&& other) : m_bits(other.m_bits), m_justifications(other.m_justifications), m_unset(other.m_unset) {
            other.m_bits = nullptr;
            other.m_justifications = nullptr;
        }

        bitvec_info& operator=(bitvec_info&& other) {
            m_bits = other.m_bits;
            m_justifications = other.m_justifications;
            m_unset = other.m_unset;

            other.m_bits = nullptr;
            other.m_justifications = nullptr;
            return *this;
        }

        ~bitvec_info() {
            SASSERT((bool)m_bits == (bool)m_justifications);
            if (!m_bits)
                return;

            unsigned cnt = num_tbits();
            for (unsigned i = 0; i < cnt; i++) {
                if (m_justifications[i].m_justification->can_dealloc())
                    dealloc(m_justifications[i].m_justification);
            }
            dealloc_svect(m_justifications);
            dealloc(m_bits);
        }

        bool is_determined() const {
            return m_unset == 0;
        };

        unsigned num_tbits() const {
            return m_bits->num_tbits();
        }

        void inc_unset() {
            SASSERT(m_unset < num_tbits());
            m_unset++;
        }

        void dec_unset() {
            SASSERT(m_unset > 0);
            m_unset--;
        }

        rational get_value() const {
            SASSERT(is_determined());
            rational value(0);
            unsigned cnt = num_tbits();
            for (unsigned i = cnt; i > 0; i--) {
                SASSERT((*m_bits)[i - 1] == BIT_0 || (*m_bits)[i - 1] == BIT_1);
                value *= 2;
                value += (*m_bits)[i - 1] == BIT_1;
            }
            return value;
        }

        void set_bit(unsigned idx, tbit v) {
            SASSERT(v != BIT_x); // We don't use don't-cares
            m_bits->manager().set(**m_bits, idx, v);
        }

        tbit get_bit(unsigned idx) const {
            return (*m_bits)[idx];
        }

        const tbv_ref* get_tbv() const {
            return m_bits;
        }

        justified_bvpos& justification(unsigned idx) {
            return m_justifications[idx];
        }

        const justified_bvpos& justification(unsigned idx) const {
            return m_justifications[idx];
        }
    };

    class fixed_bits final {

        friend bit_justification;
        
        solver& m_solver;
        scoped_ptr_vector<tbv_manager> m_tbv_managers;

        using pdd_to_info_eq = default_eq<optional<pdd>>;
        struct pdd_to_info_hash {
            unsigned operator()(optional<pdd> const& args) const {
                return args->hash();
            }
        };
        using pdd_to_info_map = map<optional<pdd>, bitvec_info, pdd_to_info_hash, pdd_to_info_eq>;

        //vector<optional<tbv_ref>> m_var_to_tbv;
        pdd_to_info_map m_pdd_to_info;
        
        svector<justified_bvpos*> m_trail;
        unsigned_vector m_trail_size; 
        
        bool m_consistent = true; // in case evaluating results in a bit-conflict

        tbv_manager& get_manager(const pdd& p);
        tbv_manager& get_manager(unsigned sz);

        bitvec_info& get_bit_info(const pdd& p);

        clause_ref get_explanation(solver& s, bit_justification** js, unsigned cnt, bool free, signed_constraint* consequence);
        clause_ref get_explanation_assignment(solver& s, const pdd& p);
        clause_ref get_explanation_conflict(solver& s, bit_justification* j1, bit_justification* j2);
        clause_ref get_explanation_conflict(solver& s, bit_justification* j); // Conflict with constant
        bool fix_value_core(const pdd& p, bitvec_info& info, unsigned idx, tbit val, bit_justification* j);
        void clear_value(const pdd& p, unsigned idx);
        void replace_justification(justified_bvpos& jstfc, bit_justification* new_j);
        
        void propagate_to_subterm(solver& s, const pdd& p);
        
    public:

        fixed_bits(solver& s) : m_solver(s) {}

        const tbv_ref* get_tbv(const pdd& p);

        // #count [min; max]
        static std::pair<unsigned, unsigned> leading_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_zeros(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> leading_ones(const tbv_ref& ref);
        static std::pair<unsigned, unsigned> trailing_ones(const tbv_ref& ref);
        static std::pair<rational, rational> min_max(const tbv_ref& ref);

        tbit get_value(const pdd& p, unsigned idx); // More efficient than calling "eval" and accessing the returned tbv elements
        // call this function also if we already know that the correct value is written there. We might decrease the decision level (for "replay")
        bool fix_bit(solver& s, const pdd& p, unsigned idx, tbit val, bit_justification** j, bool recursive);
        bool fix_bit(solver& s, const pdd& p, unsigned idx, tbit val, bit_justification* j, bool recursive);
        void push();
        void pop(unsigned pop_cnt = 1);
        
        const tbv_ref* eval(solver& s, const pdd& p);

};
}
