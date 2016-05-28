/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_unbound_compressor.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-4.

Revision History:

--*/
#ifndef DL_MK_UNBOUND_COMPRESSOR_H_
#define DL_MK_UNBOUND_COMPRESSOR_H_

#include<utility>

#include"map.h"
#include"obj_pair_hashtable.h"

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Functor for introducing auxiliary predicates to avoid unbound variables in
       rule heads.

       A rule
       P(x,_) :- T(x).
       is replaced by 
       P1(x) :- T(x).
       and for each occurrence of P in a tail of a rule, a new rule is added with P1 in 
       its place.
    */
    class mk_unbound_compressor : public rule_transformer::plugin {
        /** predicate and index of compressed argument */
        typedef std::pair<func_decl*,unsigned> c_info;
        typedef pair_hash<ptr_hash<func_decl>,unsigned_hash> c_info_hash;
        /** predicates that are results of compression */
        typedef map<c_info, func_decl*, c_info_hash, default_eq<c_info> > c_map;
        typedef hashtable<c_info, c_info_hash, default_eq<c_info> > in_progress_table;
        typedef svector<c_info> todo_stack;

        context &	    m_context;
        ast_manager &       m;
        rule_manager &      rm;
        rule_ref_vector     m_rules;
        bool                m_modified;
        todo_stack          m_todo;
        in_progress_table   m_in_progress;
        c_map               m_map;

        /**
        Relations that contain facts
        */
        func_decl_set       m_non_empty_rels;

        ast_counter         m_head_occurrence_ctr;

        ast_ref_vector      m_pinned;


        bool is_unbound_argument(rule * r, unsigned head_index);
        bool has_unbound_head_var(rule * r);

        void detect_tasks(rule_set const& source, unsigned rule_index);
        void add_task(func_decl * pred, unsigned arg_index);
        lbool try_compress(rule_set const& source, unsigned rule_index);
        void add_decompression_rules(rule_set const& source, unsigned rule_index);
        rule_ref mk_decompression_rule(rule * r, unsigned tail_index, unsigned arg_index);
        void add_decompression_rule(rule_set const& source, rule * r, unsigned tail_index, unsigned arg_index);
        void replace_by_decompression_rule(rule_set const& source, unsigned rule_index, unsigned tail_index, unsigned arg_index);

        void add_in_progress_indices(unsigned_vector& arg_indices, app* p);
        bool decompress_rule(rule_set const& source, rule* r, unsigned_vector const& cmpressed_tail_pred_arg_indexes, unsigned rule_index, unsigned tail_index);
        void reset();
    public:
        mk_unbound_compressor(context & ctx);
        
        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_UNBOUND_COMPRESSOR_H_ */

