/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_bv.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-03.

Revision History:

--*/
#ifndef _THEORY_BV_H_
#define _THEORY_BV_H_

#include"smt_theory.h"
#include"theory_bv_params.h"
#include"bit_blaster.h"
#include"trail.h"
#include"union_find.h"
#include"simplifier.h"
#include"bv_simplifier_plugin.h"
#include"arith_decl_plugin.h"
#include"arith_simplifier_plugin.h"
#include"numeral_factory.h"

namespace smt {
    
    struct theory_bv_stats {
        unsigned   m_num_diseq_static, m_num_diseq_dynamic, m_num_bit2core, m_num_th2core_eq, m_num_conflicts;
        void reset() { memset(this, 0, sizeof(theory_bv_stats)); }
        theory_bv_stats() { reset(); }
    };

    class theory_bv : public theory {
        typedef rational numeral;
        typedef trail_stack<theory_bv> th_trail_stack;
        typedef union_find<theory_bv>  th_union_find;
        typedef std::pair<theory_var, unsigned> var_pos;

        class atom {
        public:
            virtual ~atom() {}
            virtual bool is_bit() const = 0;
        };

        struct var_pos_occ {
            theory_var    m_var;
            unsigned      m_idx;
            var_pos_occ * m_next;
            var_pos_occ(theory_var v = null_theory_var, unsigned idx = 0, var_pos_occ * next = 0):m_var(v), m_idx(idx), m_next(next) {} 
        };

        struct bit_atom : public atom {
            var_pos_occ * m_occs;
            bit_atom():m_occs(0) {}
            virtual ~bit_atom() {}
            virtual bool is_bit() const { return true; }
        };

        struct le_atom : public atom {
            literal    m_var;
            literal    m_def;
            le_atom(literal v, literal d):m_var(v), m_def(d) {}
            virtual ~le_atom() {}
            virtual bool is_bit() const { return false; }
        };

        /**
           \brief Structure used to store the position of a bitvector variable that
           contains the true_literal/false_literal.
           
           Remark: the implementation assumes that bitvector variables containing
           complementary bits are never merged. I assert a disequality (not (= x y))
           whenever x and y contain complementary bits. However, this is too expensive
           when the bit is the true_literal or false_literal. The number of disequalities
           is too big. To avoid this problem, each equivalence class has a set
           of its true_literal and false_literal bits in the form of svector<zero_one_bit>.
           
           Before merging two classes we just check if the merge is valid by traversing these
           vectors.
        */
        struct zero_one_bit {
            theory_var m_owner;    //!< variable that owns the bit: useful for backtracking
            unsigned   m_idx:31;
            unsigned   m_is_true:1;
            zero_one_bit(theory_var v = null_theory_var, unsigned idx = UINT_MAX, bool is_true = false):
                m_owner(v), m_idx(idx), m_is_true(is_true) {}
        };

        typedef svector<zero_one_bit> zero_one_bits;

#ifdef SPARSE_MAP
        typedef u_map<atom *>    bool_var2atom;
        void insert_bv2a(bool_var bv, atom * a) { m_bool_var2atom.insert(bv, a); }
        void erase_bv2a(bool_var bv) { m_bool_var2atom.erase(bv); }
        atom * get_bv2a(bool_var bv) const { atom * a; m_bool_var2atom.find(bv, a); return a; }
#else
        typedef ptr_vector<atom> bool_var2atom;
        void insert_bv2a(bool_var bv, atom * a) { m_bool_var2atom.setx(bv, a, 0); }
        void erase_bv2a(bool_var bv) { m_bool_var2atom[bv] = 0; }
        atom * get_bv2a(bool_var bv) const { return m_bool_var2atom.get(bv, 0); }
#endif
        theory_bv_stats          m_stats;
        theory_bv_params const & m_params;
        bv_util                  m_util;
        arith_util               m_autil;
        simplifier *             m_simplifier;
        bit_blaster              m_bb;
        th_trail_stack           m_trail_stack;
        th_union_find            m_find;
        vector<literal_vector>   m_bits;     // per var, the bits of a given variable.
        svector<unsigned>        m_wpos;     // per var, watch position for fixed variable detection. 
        vector<zero_one_bits>    m_zero_one_bits; // per var, see comment in the struct zero_one_bit
        bool_var2atom            m_bool_var2atom;
        typedef svector<theory_var> vars;

        typedef std::pair<numeral, unsigned> value_sort_pair;
        typedef pair_hash<obj_hash<numeral>, unsigned_hash> value_sort_pair_hash;
        typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
        value2var                m_fixed_var_table;

        literal_vector           m_tmp_literals;
        svector<var_pos>         m_prop_queue;
        bool                     m_approximates_large_bvs;

        theory_var find(theory_var v) const { return m_find.find(v); }
        theory_var next(theory_var v) const { return m_find.next(v); }
        bool is_root(theory_var v) const { return m_find.is_root(v); }
        unsigned get_bv_size(app const * n) const { return m_util.get_bv_size(n); }
        unsigned get_bv_size(enode const * n) const { return m_util.get_bv_size(n->get_owner()); }
        unsigned get_bv_size(theory_var v) const { return get_bv_size(get_enode(v)); }
        bool is_bv(app const* n) const { return m_util.is_bv_sort(get_manager().get_sort(n)); }
        bool is_bv(enode const* n) const { return is_bv(n->get_owner()); }
        bool is_bv(theory_var v) const { return is_bv(get_enode(v)); }
        region & get_region() { return m_trail_stack.get_region(); }

        bool is_numeral(theory_var v) const { return m_util.is_numeral(get_enode(v)->get_owner()); }
        app * mk_bit2bool(app * bv, unsigned idx);
        void mk_bits(theory_var v);
        friend class mk_atom_trail;
        void mk_bit2bool(app * n);
        void process_args(app * n);
        enode * mk_enode(app * n);
        theory_var get_var(enode * n);
        enode * get_arg(enode * n, unsigned idx);
        theory_var get_arg_var(enode * n, unsigned idx);
        void get_bits(theory_var v, expr_ref_vector & r);
        void get_bits(enode * n, expr_ref_vector & r);
        void get_arg_bits(enode * n, unsigned idx, expr_ref_vector & r);
        void get_arg_bits(app * n, unsigned idx, expr_ref_vector & r);
        friend class add_var_pos_trail;
        void simplify_bit(expr * s, expr_ref & r);
        void mk_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx);
        friend class register_true_false_bit_trail;
        void register_true_false_bit(theory_var v, unsigned idx);
        void find_new_diseq_axioms(var_pos_occ * occs, theory_var v, unsigned idx);
        void add_bit(theory_var v, literal l);
        void init_bits(enode * n, expr_ref_vector const & bits);
        void find_wpos(theory_var v);
        friend class fixed_eq_justification;
        void fixed_var_eh(theory_var v);
        bool get_fixed_value(theory_var v, numeral & result) const;
        void internalize_num(app * n);
        void internalize_add(app * n);
        void internalize_mul(app * n);
        void internalize_udiv(app * n);
        void internalize_sdiv(app * n);
        void internalize_urem(app * n);
        void internalize_srem(app * n);
        void internalize_smod(app * n);
        void internalize_shl(app * n);
        void internalize_lshr(app * n);
        void internalize_ashr(app * n);
        void internalize_ext_rotate_left(app * n);
        void internalize_ext_rotate_right(app * n);
        void internalize_and(app * n);
        void internalize_or(app * n);
        void internalize_not(app * n);
        void internalize_nand(app * n);
        void internalize_nor(app * n);
        void internalize_xor(app * n);
        void internalize_xnor(app * n);
        void internalize_concat(app * n);
        void internalize_sign_extend(app * n);
        void internalize_zero_extend(app * n);
        void internalize_extract(app * n);
        void internalize_redand(app * n);
        void internalize_redor(app * n);
        void internalize_comp(app * n);
        void internalize_rotate_left(app * n);
        void internalize_rotate_right(app * n);
        void internalize_bv2int(app* n);
        void internalize_int2bv(app* n);
        void internalize_mkbv(app* n);
        void internalize_umul_no_overflow(app *n);
        void internalize_smul_no_overflow(app *n);
        void internalize_smul_no_underflow(app *n);

        bool approximate_term(app* n);

        template<bool Signed>
        void internalize_le(app * atom);
        bool internalize_xor3(app * n, bool gate_ctx);
        bool internalize_carry(app * n, bool gate_ctx);
        justification * mk_bit_eq_justification(theory_var v1, theory_var v2, literal consequent, literal antecedent);
        void propagate_bits();
        void assign_bit(literal consequent, theory_var v1, theory_var v2, unsigned idx, literal antecedent, bool propagate_eqc);
        void assert_int2bv_axiom(app* n);
        void assert_bv2int_axiom(app* n);
        arith_simplifier_plugin & arith_simp() const {
            SASSERT(m_simplifier != 0);
            arith_simplifier_plugin * as = static_cast<arith_simplifier_plugin*>(m_simplifier->get_plugin(m_autil.get_family_id()));
            SASSERT(as != 0);
            return *as;
        }

    protected:
        virtual void init(context * ctx);
        virtual theory_var mk_var(enode * n);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void apply_sort_cnstr(enode * n, sort * s);
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual void new_diseq_eh(theory_var v1, theory_var v2);
        virtual void expand_diseq(theory_var v1, theory_var v2);
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void relevant_eh(app * n);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual final_check_status final_check_eh();
        virtual void reset_eh();
        svector<theory_var>   m_merge_aux[2]; //!< auxiliary vector used in merge_zero_one_bits
        bool merge_zero_one_bits(theory_var r1, theory_var r2);

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------
        bv_factory *    m_factory;
        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

    public:
        theory_bv(ast_manager & m, theory_bv_params const & params, bit_blaster_params const & bb_params);
        virtual ~theory_bv();
        
        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_bv, get_manager(), m_params, m_bb.get_params()); }

        virtual char const * get_name() const { return "bit-vector"; }

        th_trail_stack & get_trail_stack() { return m_trail_stack; }
        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { SASSERT(check_zero_one_bits(r1)); }
        void unmerge_eh(theory_var v1, theory_var v2);

        void display_var(std::ostream & out, theory_var v) const;
        void display_bit_atom(std::ostream & out, bool_var v, bit_atom const * a) const;
        void display_atoms(std::ostream & out) const;
        virtual void display(std::ostream & out) const;
        virtual void collect_statistics(::statistics & st) const;

        bool get_fixed_value(app* x, numeral & result) const;


#ifdef Z3DEBUG
        bool check_assignment(theory_var v) const;
        bool check_invariant() const;
        bool check_zero_one_bits(theory_var v) const;
#endif
    };
};

#endif /* _THEORY_BV_H_ */

