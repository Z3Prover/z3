/*++
Copyright (c) 2017 Microsoft Corporation

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#pragma once
#include "util/vector.h"
#include "math/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "math/lp/lar_solver.h"
#include "math/lp/monic.h"
#include "math/lp/nla_core.h"
namespace nra {
    class solver;
}
namespace nla {
    class core;
    // nonlinear integer incremental linear solver
    class solver {
        core* m_core;
    public:

        solver(lp::lar_solver& s, params_ref const& p, reslimit& limit);
        ~solver();
        const auto& monics_with_changed_bounds() const { return m_core->monics_with_changed_bounds(); }
        void add_monic(lpvar v, unsigned sz, lpvar const* vs);
        void add_idivision(lpvar q, lpvar x, lpvar y);
        void add_rdivision(lpvar q, lpvar x, lpvar y);
        void add_bounded_division(lpvar q, lpvar x, lpvar y);
        void check_bounded_divisions();
        void set_relevant(std::function<bool(lpvar)>& is_relevant);
        void push();
        void pop(unsigned scopes);
        bool need_check();
        lbool check();
        void propagate();
        void simplify() { m_core->simplify(); }
        lbool check_power(lpvar r, lpvar x, lpvar y);
        bool is_monic_var(lpvar) const;
        bool influences_nl_var(lpvar) const;
        std::ostream& display(std::ostream& out) const;
        bool use_nra_model() const;
        core& get_core();
        nlsat::anum_manager& am();
        nlsat::anum const& am_value(lp::lpvar v) const;
        scoped_anum& tmp1();
        scoped_anum& tmp2();
        vector<nla::ineq> const& literals() const;
        vector<lp::fixed_equality> const& fixed_equalities() const;
        vector<lp::equality> const& equalities() const;
        bool should_check_feasible() const { return m_core->should_check_feasible(); }
        
        // Iterator class for filtering out empty lemmas
        class non_empty_lemma_iterator {
            vector<nla::lemma>::const_iterator current_;
            vector<nla::lemma>::const_iterator end_;
            
            void advance_to_non_empty() {
                while (current_ != end_ && current_->is_empty()) {
                    std::cout << "skip\n";
                    ++current_;
                }
            }
            
        public:
            non_empty_lemma_iterator(vector<nla::lemma>::const_iterator start, 
                                   vector<nla::lemma>::const_iterator end) 
                : current_(start), end_(end) {
                advance_to_non_empty();
            }
            
            const nla::lemma& operator*() const { return *current_; }
            const nla::lemma* operator->() const { return &*current_; }
            
            non_empty_lemma_iterator& operator++() {
                ++current_;
                advance_to_non_empty();
                return *this;
            }
            
            bool operator!=(const non_empty_lemma_iterator& other) const {
                return current_ != other.current_;
            }
            
            bool operator==(const non_empty_lemma_iterator& other) const {
                return current_ == other.current_;
            }
        };
        
        // Helper class to provide range-based iteration over non-empty lemmas
        class non_empty_lemmas_range {
            const vector<nla::lemma>& lemmas_;
        public:
            non_empty_lemmas_range(const vector<nla::lemma>& lemmas) : lemmas_(lemmas) {}
            
            non_empty_lemma_iterator begin() const {
                return non_empty_lemma_iterator(lemmas_.begin(), lemmas_.end());
            }
            
            non_empty_lemma_iterator end() const {
                return non_empty_lemma_iterator(lemmas_.end(), lemmas_.end());
            }
            
            bool empty() const {
                return begin() == end();
            }
        };
        
        non_empty_lemmas_range lemmas() const;
        
    };
}
