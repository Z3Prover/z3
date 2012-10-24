/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_subsumption.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-13.

Revision History:

--*/
#ifndef _SPC_SUBSUMPTION_H_
#define _SPC_SUBSUMPTION_H_

#include"spc_asserted_literals.h"
#include"matcher.h"
#include"fvi.h"
#include"spc_params.h"
#include"obj_hashtable.h"

namespace spc {

    class subsumption {
        ast_manager &         m_manager;
        spc_params &          m_params;
        asserted_literals &   m_asserted_literals;
        substitution          m_subst;
        matcher               m_matcher;

        // A pair representing the association between l1 and l2 where
        // first is the position of l1 in lits1 and second the position of l2 in
        // lits2.
        typedef std::pair<unsigned, unsigned> assoc; 
        typedef vector<assoc> stack;
        stack m_stack;

        template<bool ResetSubst>
        bool match_literal(literal const & l1, literal const & l2);

        bool can_subsume(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2);
        bool quick_check(clause * cls1, clause * cls2);
        bool subsumes_core(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2);
        bool subsumes_core(literal const & l1, unsigned num_lits2, literal * lits2);
        bool ground_subsumes_core(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2);

        enum feature_kind {
            F_GROUND,
            F_NUM_POS_LITS,
            F_NUM_NEG_LITS,
            F_DEPTH,
            F_CONST_COUNT,
            F_SYM_COUNT,
            F_NUM_NEG_FUNCS,
            F_NUM_POS_FUNCS
        };

        struct feature {
            feature_kind m_kind;
            func_decl *  m_decl;
            feature(feature_kind k = F_GROUND):m_kind(k) {}
            feature(func_decl * decl, bool neg):m_kind(neg ? F_NUM_NEG_FUNCS : F_NUM_POS_FUNCS), m_decl(decl) {}
        };

        vector<feature> m_features;

        bit_vector            m_found_decl_set;
        func_decl_ref_vector  m_found_decls; // domain of m_found_decl_set;

        /**
           \brief Return true if the function symbol is considered for feature vector indexing.
        */
        bool fvi_candidate(func_decl * f) {
            return f->get_family_id() == null_family_id || f->get_arity() > 0;
        }
        
        typedef obj_hashtable<func_decl> found_func_decl_set;
        found_func_decl_set   m_cls_found_decl_set; // temporary set used to track the func_decl's found in a clause
        ptr_vector<func_decl> m_cls_found_decls;

        bool mark_func_decl(func_decl * f);

        typedef obj_map<func_decl, unsigned> decl2nat;
        bool        m_refining_index; // if true keep collecting data to refine index.
        decl2nat    m_f_count[2];     // temporary field used to track the num. of occurs. of function symbols in neg/pos literals.
        decl2nat    m_f_min[2];
        decl2nat    m_f_max[2];
        decl2nat    m_f_freq;
        
        void inc_f_count(func_decl * f, bool neg);
        void update_min_max(func_decl * f);
        void update_neg_pos_func_counts(clause * cls);
        
        void compute_features(clause * cls, unsigned * fvector);
        
        struct to_feature_vector;
        friend struct to_feature_vector;

        struct to_feature_vector {
            subsumption & m_owner;
            to_feature_vector(subsumption & o):m_owner(o) {}
            void operator()(clause * cls, unsigned * fvector) {
                m_owner.compute_features(cls, fvector);
            }
        };

        typedef fvi<clause, to_feature_vector, obj_ptr_hash<clause>, ptr_eq<clause> > index;
        index *    m_index;
        unsigned   m_num_processed_clauses;
        unsigned   m_opt_threshold;

        void init_indexes();

        struct f_lt;
        friend struct f_lt;

        unsigned get_value_range(func_decl * f, bool neg) const;
        unsigned get_value_range(func_decl * f) const;

        struct f_lt {
            subsumption & m_owner;
            f_lt(subsumption & o):m_owner(o) {}
            bool operator()(func_decl * f1, func_decl * f2) const;
        };
        
        void optimize_feature_index();

        clause * unit_forward(clause * cls);
        clause * non_unit_forward(clause * cls);
        clause * eq_subsumption(expr * lhs, expr * rhs);
        clause * eq_subsumption(clause * cls);

    public:
        subsumption(ast_manager & m, asserted_literals & al, spc_params & params);
        ~subsumption();

        bool operator()(clause * cls1, clause * cls2);
        void insert(clause * cls);
        void erase(clause * cls);
        void reset();
        clause * forward(clause * cls);
        void backward(clause * cls, ptr_buffer<clause> & result);

        ast_manager & get_manager() { return m_manager; }
    };

};

#endif /* _SPC_SUBSUMPTION_H_ */

