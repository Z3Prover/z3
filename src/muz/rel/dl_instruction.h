/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_instruction.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/
#ifndef DL_INSTRUCTION_H_
#define DL_INSTRUCTION_H_

#include<iostream>
#include<string>
#include<utility>
#include "ast.h"
#include "vector.h"
#include "dl_base.h"
#include "dl_costs.h"
#include "dl_context.h"

namespace datalog {

    class execution_context;
    class instruction_block;
    class rel_context;

    inline void check_overflow(unsigned i) {
        if (i == UINT_MAX) {
            throw out_of_memory_error();
        }
    }

    // -----------------------------------
    //
    // execution_context
    //
    // -----------------------------------

    class execution_context {
    public:
        typedef relation_base * reg_type;
        typedef vector<reg_type> reg_vector;
        typedef unsigned reg_idx;

        /**
           \brief A register number that should never be referenced to. Can stand e.g. for a tail 
           table in a rule with no tail.
        */
        static const reg_idx void_register = UINT_MAX;
    private:
        typedef u_map<std::string> reg_annotations;

        context &           m_context;
        reg_vector          m_registers;

        reg_annotations     m_reg_annotation;
        stopwatch *         m_stopwatch;
        unsigned            m_timelimit_ms; //zero means no limit
    public:
        execution_context(context & context);
        ~execution_context();

        void reset();

        rel_context & get_rel_context();
        rel_context const & get_rel_context() const;

        void set_timelimit(unsigned time_in_ms);
        void reset_timelimit();
        bool should_terminate();

        struct stats {
            unsigned m_join;
            unsigned m_project;
            unsigned m_filter;
            unsigned m_total;
            unsigned m_unary_singleton;
            unsigned m_filter_by_negation;
            unsigned m_select_equal_project;
            unsigned m_join_project;
            unsigned m_project_rename;
            unsigned m_union;
            unsigned m_filter_interp_project;
            unsigned m_filter_id;
            unsigned m_filter_eq;
            unsigned m_min;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        stats m_stats;

        void collect_statistics(statistics& st) const;

        /**
           \brief Return reference to \c i -th register that contains pointer to a relation.

           If register contains zero, it should be treated as if it contains an empty relation.
        */
        reg_type reg(reg_idx i) const { 
            if (i >= m_registers.size()) {
                return 0;
            }
            return m_registers[i];
        }
        /**
           \brief Return value of the register and assign zero into it place.
        */
        reg_type release_reg(reg_idx i) {
            SASSERT(i < m_registers.size());
            SASSERT(m_registers[i]);
            reg_type res = m_registers[i];
            m_registers[i] = 0;
            return res;
        }

        /**
           \brief Assign value to a register. If it was non-empty, deallocate its content first.
        */
        void set_reg(reg_idx i, reg_type val) {
            if (i >= m_registers.size()) {
                check_overflow(i);
                m_registers.resize(i+1,0);
            }
            if (m_registers[i]) {
                m_registers[i]->deallocate();
            }
            m_registers[i] = val;
        }

        void make_empty(reg_idx i) {
            if (reg(i)) {
                set_reg(i, 0);
            }
        }

        unsigned register_count() const {
            return m_registers.size();
        }

        bool get_register_annotation(reg_idx reg, std::string & res) const {
            return m_reg_annotation.find(reg, res);
        }

        void set_register_annotation(reg_idx reg, std::string str) {
            m_reg_annotation.insert(reg, str);
        }

        void report_big_relations(unsigned threshold, std::ostream & out) const;
    };



    // -----------------------------------
    //
    // instruction
    //
    // -----------------------------------


    /**
    \brief Base class for instructions used in datalog saturation.

    A relation in a register is owned by that register and is not referenced from anywhere else.

    Instructions that move context of one register to another leave the source register empty
    and deallocate the previous content of the target register.
    */
    class instruction : public accounted_object {
        typedef u_map<base_relation_fn *> fn_cache;

        fn_cache m_fn_cache;


        static const int rk_encode_base = 1024;

        inline static unsigned encode_kind(family_id k)
        { SASSERT(k<rk_encode_base); return k; }
        inline static unsigned encode_kinds(family_id k1, family_id k2) 
        { SASSERT(k1<rk_encode_base && k2<rk_encode_base); return (k1+1)*rk_encode_base + k2; }
        inline static unsigned encode_kinds(family_id k1, family_id k2, family_id k3) { 
            SASSERT(k1<rk_encode_base && k2<rk_encode_base && k3<rk_encode_base); 
            return ((k1+1)*rk_encode_base + k2)*rk_encode_base + k3;
        }

    protected:
        friend class instruction_block;

        template<typename T>
        bool find_fn(const relation_base & r, T* & result) const
        { return m_fn_cache.find(encode_kind(r.get_kind()), reinterpret_cast<base_relation_fn*&>(result)); }

        template<typename T>
        bool find_fn(const relation_base & r1, const relation_base & r2, T*& result) const
        { return m_fn_cache.find(encode_kinds(r1.get_kind(), r2.get_kind()), reinterpret_cast<base_relation_fn*&>(result)); }

        template<typename T>
        bool find_fn(const relation_base & r1, const relation_base & r2, const relation_base & r3, T * & result) const
        { return m_fn_cache.find(encode_kinds(r1.get_kind(), r2.get_kind(), r3.get_kind()), reinterpret_cast<base_relation_fn*&>(result)); }

        void store_fn(const relation_base & r, base_relation_fn * fn)
        { m_fn_cache.insert(encode_kind(r.get_kind()), fn); }
        void store_fn(const relation_base & r1, const relation_base & r2, base_relation_fn * fn)
        { m_fn_cache.insert(encode_kinds(r1.get_kind(), r2.get_kind()), fn); }
        void store_fn(const relation_base & r1, const relation_base & r2, const relation_base & r3, 
            base_relation_fn * fn)
        { m_fn_cache.insert(encode_kinds(r1.get_kind(), r2.get_kind(), r3.get_kind()), fn); }

        /**
           Process not only costs associated with the current instruction, but in case of
           block instructions, process also costs associated with its child instructions.
        */
        virtual void process_all_costs();

        /**
           \brief Output one line header of the current instruction.

           The newline character at the end should not be printed.
        */
        virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
            out << "<instruction>";
        }
        /**
           \brief If relevant, output the body of the current instruction.

           Each line must be prepended by \c indentation and ended by a newline character.
        */
        virtual void display_body_impl(execution_context const & ctx, std::ostream & out, std::string indentation) const {}
        void log_verbose(execution_context& ctx);

    public:
        typedef execution_context::reg_type reg_type;
        typedef execution_context::reg_idx reg_idx;

        virtual ~instruction();

        virtual bool perform(execution_context & ctx) = 0;

        virtual void make_annotations(execution_context & ctx)  = 0;

        void display(execution_context const& ctx, std::ostream & out) const {
            display_indented(ctx, out, "");
        }
        void display_indented(execution_context const & ctx, std::ostream & out, std::string indentation) const;

        static instruction * mk_load(ast_manager & m, func_decl * pred, reg_idx tgt);
        /**
           \brief The store operation moves the relation from a register into the context. The register
           is set to zero after the operation.
        */
        static instruction * mk_store(ast_manager & m, func_decl * pred, reg_idx src);
        static instruction * mk_dealloc(reg_idx reg); //maybe not necessary
        static instruction * mk_clone(reg_idx from, reg_idx to);
        static instruction * mk_move(reg_idx from, reg_idx to);

        /**
           \brief Return instruction that performs \c body as long as at least one register
           in \c control_regs contains non-empty relation.

           The instruction object takes over the ownership of the \c body object.
        */
        static instruction * mk_while_loop(unsigned control_reg_cnt, const reg_idx * control_regs, 
            instruction_block * body);

        static instruction * mk_join(reg_idx rel1, reg_idx rel2, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2, reg_idx result);
        static instruction * mk_filter_equal(ast_manager & m, reg_idx reg, const relation_element & value, unsigned col);
        static instruction * mk_filter_identical(reg_idx reg, unsigned col_cnt, const unsigned * identical_cols);
        static instruction * mk_filter_interpreted(reg_idx reg, app_ref & condition);
        static instruction * mk_filter_interpreted_and_project(reg_idx src, app_ref & condition,
            unsigned col_cnt, const unsigned * removed_cols, reg_idx result);
        static instruction * mk_union(reg_idx src, reg_idx tgt, reg_idx delta);
        static instruction * mk_widen(reg_idx src, reg_idx tgt, reg_idx delta);
        static instruction * mk_projection(reg_idx src, unsigned col_cnt, const unsigned * removed_cols, 
            reg_idx tgt);
        static instruction * mk_join_project(reg_idx rel1, reg_idx rel2, unsigned joined_col_cnt,
            const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols, reg_idx result);
        static instruction * mk_min(reg_idx source, reg_idx target, const unsigned_vector & group_by_cols,
            const unsigned min_col);
        static instruction * mk_rename(reg_idx src, unsigned cycle_len, const unsigned * permutation_cycle, 
            reg_idx tgt);
        static instruction * mk_filter_by_negation(reg_idx tgt, reg_idx neg_rel, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2);
        static instruction * mk_select_equal_and_project(ast_manager & m, reg_idx src, 
            const relation_element & value, unsigned col, reg_idx result);
        
        static instruction * mk_unary_singleton(ast_manager & m, func_decl* pred, const relation_sort & s, const relation_element & val, reg_idx tgt);
        static instruction * mk_total(const relation_signature & sig, func_decl* pred, reg_idx tgt);

        /**
           \brief The mark_saturated instruction marks a relation as saturated, so that after
           next restart it does not have to be part of the saturation again.
         */
        static instruction * mk_mark_saturated(ast_manager & m, func_decl * pred);

        static instruction * mk_assert_signature(const relation_signature & s, reg_idx tgt);

        void collect_statistics(statistics& st) const;

    };


    // -----------------------------------
    //
    // instruction_block
    //
    // -----------------------------------

    class instruction_block {
    public:
        struct instruction_observer {
            virtual ~instruction_observer() {}
            virtual void notify(instruction * i) {}
        };
    private:
        typedef ptr_vector<instruction> instr_seq_type;
        instr_seq_type m_data;
        instruction_observer* m_observer;
    public:
        instruction_block() : m_observer(0) {}
        ~instruction_block();
        void reset();

        void push_back(instruction * i) { 
            m_data.push_back(i);
            if (m_observer) {
                m_observer->notify(i);
            }
        }
        void set_observer(instruction_observer * o) { 
            SASSERT(o==0 || m_observer==0);
            m_observer = o;
        }

        void collect_statistics(statistics& st) const;

        /**
           \brief Perform instructions in the block. If the run was interrupted before completion,
           return false; otherwise return true.

           The execution can terminate before completion if the function 
           \c execution_context::should_terminate() returns true.
        */
        bool perform(execution_context & ctx) const;

        void process_all_costs();

        void make_annotations(execution_context & ctx);

        void display(execution_context const & ctx, std::ostream & out) const {
            display_indented(ctx, out, "");
        }
        void display_indented(execution_context const & ctx, std::ostream & out, std::string indentation) const;

        unsigned num_instructions() const { return m_data.size(); }
    };


};

#endif /* DL_INSTRUCTION_H_ */

