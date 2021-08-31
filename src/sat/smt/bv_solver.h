/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_solver.h

Abstract:

    Theory plugin for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "sat/smt/bv_ackerman.h"
#include "ast/rewriter/bit_blaster/bit_blaster.h"

namespace euf {
    class solver;
}

namespace bv {

    class solver : public euf::th_euf_solver {
        typedef rational numeral;
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef sat::literal literal;
        typedef sat::bool_var bool_var;
        typedef sat::literal_vector literal_vector;
        typedef svector<euf::theory_var> vars;
        typedef std::pair<numeral, unsigned> value_sort_pair;
        typedef pair_hash<obj_hash<numeral>, unsigned_hash> value_sort_pair_hash;
        typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
        typedef union_find<solver, euf::solver>  bv_union_find;
        typedef std::pair<theory_var, unsigned> var_pos;

        friend class ackerman;

        struct stats {
            unsigned   m_num_diseq_static, m_num_diseq_dynamic,  m_num_conflicts;
            unsigned   m_num_bit2eq, m_num_bit2ne, m_num_eq2bit, m_num_ne2bit;
            unsigned   m_ackerman;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        struct bv_justification {
            enum kind_t { eq2bit, ne2bit, bit2eq, bit2ne };
            kind_t     m_kind;
            unsigned   m_idx{ UINT_MAX };
            theory_var m_v1{ euf::null_theory_var };
            theory_var m_v2 { euf::null_theory_var };
            sat::literal m_consequent;
            sat::literal m_antecedent;
            bv_justification(theory_var v1, theory_var v2, sat::literal c, sat::literal a) :
                m_kind(bv_justification::kind_t::eq2bit), m_v1(v1), m_v2(v2), m_consequent(c), m_antecedent(a) {}
            bv_justification(theory_var v1, theory_var v2):
                m_kind(bv_justification::kind_t::bit2eq), m_v1(v1), m_v2(v2) {}
            bv_justification(unsigned idx, sat::literal c) :
                m_kind(bv_justification::kind_t::bit2ne), m_idx(idx), m_consequent(c) {}
            bv_justification(unsigned idx, theory_var v1, theory_var v2, sat::literal c, sat::literal a) :
                m_kind(bv_justification::kind_t::ne2bit), m_idx(idx), m_v1(v1), m_v2(v2), m_consequent(c), m_antecedent(a) {}
            sat::ext_constraint_idx to_index() const { 
                return sat::constraint_base::mem2base(this); 
            }
            static bv_justification& from_index(size_t idx) {
                return *reinterpret_cast<bv_justification*>(sat::constraint_base::from_index(idx)->mem());
            }
            static size_t get_obj_size() { return sat::constraint_base::obj_size(sizeof(bv_justification)); }
        };

        sat::justification mk_eq2bit_justification(theory_var v1, theory_var v2, sat::literal c, sat::literal a);
        sat::ext_justification_idx mk_bit2eq_justification(theory_var v1, theory_var v2);
        sat::justification mk_bit2ne_justification(unsigned idx, sat::literal c);
        sat::justification mk_ne2bit_justification(unsigned idx, theory_var v1, theory_var v2, sat::literal c, sat::literal a);
        void log_drat(bv_justification const& c);
 

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
            zero_one_bit(theory_var v = euf::null_theory_var, unsigned idx = UINT_MAX, bool is_true = false):
                m_owner(v), m_idx(idx), m_is_true(is_true) {}
            std::ostream& display(std::ostream& out) const {
                return out << "v" << m_owner << " @ " << m_idx << " " << (m_is_true?"T":"F");
            }
        };

        typedef svector<zero_one_bit> zero_one_bits;

        struct eq_occurs {
            sat::bool_var m_bv1;
            sat::bool_var m_bv2;
            unsigned    m_idx;
            theory_var  m_v1;
            theory_var  m_v2;
            sat::literal m_literal;
            euf::enode* m_node;
            eq_occurs* m_next;
            eq_occurs* m_prev;
            eq_occurs(sat::bool_var b1, sat::bool_var b2, unsigned idx, theory_var v1, theory_var v2, sat::literal lit, euf::enode* n, eq_occurs* next = nullptr) :
                m_bv1(b1), m_bv2(b2), m_idx(idx), m_v1(v1), m_v2(v2), m_literal(lit), m_node(n), m_next(next), m_prev(nullptr) {}
        };

        class eq_occurs_it {
            eq_occurs* m_first;
        public:
            eq_occurs_it(eq_occurs* c) : m_first(c) {}
            eq_occurs const& operator*() { return *m_first; }
            eq_occurs_it& operator++() { m_first = m_first->m_next; return *this; }
            eq_occurs_it operator++(int) { eq_occurs_it tmp = *this; ++*this; return tmp; }
            bool operator==(eq_occurs_it const& other) const { return m_first == other.m_first; }
            bool operator!=(eq_occurs_it const& other) const { return !(*this == other); }
        };

        class eqs_iterator {
            eq_occurs* o;
        public:
            eqs_iterator(eq_occurs* o) :o(o) {}
            eq_occurs_it begin() const { return eq_occurs_it(o); }
            eq_occurs_it end() const { return eq_occurs_it(nullptr); }
        };

        struct var_pos_occ {
            var_pos       m_vp;
            var_pos_occ* m_next;
            var_pos_occ(theory_var v = euf::null_theory_var, unsigned idx = 0, var_pos_occ* next = nullptr) :m_vp(v, idx), m_next(next) {}
        };

        class var_pos_it {
            var_pos_occ* m_first;
        public:
            var_pos_it(var_pos_occ* c) : m_first(c) {}
            var_pos operator*() { return m_first->m_vp; }
            var_pos_it& operator++() { m_first = m_first->m_next; return *this; }
            var_pos_it operator++(int) { var_pos_it tmp = *this; ++* this; return tmp; }
            bool operator==(var_pos_it const& other) const { return m_first == other.m_first; }
            bool operator!=(var_pos_it const& other) const { return !(*this == other); }
        };

        struct atom {
            bool_var      m_bv;
            eq_occurs*    m_eqs;
            var_pos_occ * m_occs;
            svector<std::pair<atom*, eq_occurs*>> m_bit2occ;
            literal    m_var { sat::null_literal };
            literal    m_def { sat::null_literal };
            atom(bool_var b) :m_bv(b), m_eqs(nullptr), m_occs(nullptr) {}
            ~atom() { m_bit2occ.clear(); }
            var_pos_it begin() const { return var_pos_it(m_occs); }
            var_pos_it end() const { return var_pos_it(nullptr); }
            eqs_iterator eqs() const { return eqs_iterator(m_eqs); }  
        };

        struct propagation_item {
            var_pos m_vp { var_pos(0, 0) };
            atom* m_atom{ nullptr };
            explicit propagation_item(atom* a) : m_atom(a) {}
            explicit propagation_item(var_pos const& vp) : m_vp(vp) {}            
            bool operator==(propagation_item const& other) const { if (m_atom) return m_atom == other.m_atom; return false; }
        };


        class bit_trail;
        class add_var_pos_trail;
        class add_eq_occurs_trail;
        class del_eq_occurs_trail;
        class mk_atom_trail;
        class bit_occs_trail;
        typedef ptr_vector<atom> bool_var2atom;
        typedef vector<literal_vector> bits_vector;

        bv_util                  bv;
        arith_util               m_autil;
        stats                    m_stats;
        ackerman                 m_ackerman;
        bit_blaster              m_bb;
        bv_union_find            m_find;
        bits_vector              m_bits;     // per var, the bits of a given variable.
        unsigned_vector          m_wpos;     // per var, watch position for fixed variable detection. 
        vector<zero_one_bits>    m_zero_one_bits; // per var, see comment in the struct zero_one_bit
        bool_var2atom            m_bool_var2atom;
        value2var                m_fixed_var_table;
        mutable vector<rational>   m_power2;
        literal_vector             m_tmp_literals;
        svector<propagation_item>  m_prop_queue;
        unsigned_vector            m_prop_queue_lim;
        unsigned                   m_prop_queue_head { 0 };
        sat::literal               m_true { sat::null_literal };

        // internalize
        void insert_bv2a(bool_var bv, atom * a) { m_bool_var2atom.setx(bv, a, 0); }
        void erase_bv2a(bool_var bv) { m_bool_var2atom[bv] = 0; }
        atom * get_bv2a(bool_var bv) const { return m_bool_var2atom.get(bv, 0); }
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        unsigned get_bv_size(euf::enode* n);
        unsigned get_bv_size(theory_var v);
        theory_var get_var(euf::enode* n);
        euf::enode* get_arg(euf::enode* n, unsigned idx);
        inline theory_var get_arg_var(euf::enode* n, unsigned idx);
        void get_bits(theory_var v, expr_ref_vector& r);
        void get_bits(euf::enode* n, expr_ref_vector& r);
        void get_arg_bits(app* n, unsigned idx, expr_ref_vector& r);
        void fixed_var_eh(theory_var v);
        bool is_bv(theory_var v) const { return bv.is_bv(var2expr(v)); }
        void register_true_false_bit(theory_var v, unsigned i);
        void add_bit(theory_var v, sat::literal lit);
        atom* mk_atom(sat::bool_var b);
        void eq_internalized(sat::bool_var b1, sat::bool_var b2, unsigned idx, theory_var v1, theory_var v2, sat::literal eq, euf::enode* n);
        void del_eq_occurs(atom* a, eq_occurs* occ);

        void set_bit_eh(theory_var v, literal l, unsigned idx);
        void init_bits(expr* e, expr_ref_vector const & bits);
        void mk_bits(theory_var v);
        void add_def(sat::literal def, sat::literal l);
        bool internalize_circuit(app* a);
        void internalize_unary(app* n, std::function<void(unsigned, expr* const*, expr_ref_vector&)>& fn);
        void internalize_binary(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref_vector&)>& fn);
        void internalize_par_unary(app* n, std::function<void(unsigned, expr* const*, unsigned p, expr_ref_vector&)>& fn);
        void internalize_novfl(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref&)>& fn);
        void internalize_interp(app* n, std::function<expr*(expr*, expr*)>& ibin, std::function<expr*(expr*)>& un);
        void internalize_num(app * n);       
        void internalize_concat(app * n);        
        void internalize_bv2int(app* n);
        void internalize_int2bv(app* n);
        void internalize_mkbv(app* n);
        void internalize_xor3(app* n);
        void internalize_carry(app* n);
        void internalize_sub(app* n);
        void internalize_extract(app* n);
        void internalize_repeat(app* n);
        void internalize_bit2bool(app* n);
        void internalize_udiv_i(app* n);
        template<bool Signed, bool Reverse, bool Negated>
        void internalize_le(app* n);
        void assert_bv2int_axiom(app * n);
        void assert_int2bv_axiom(app* n);
        void assert_ackerman(theory_var v1, theory_var v2);
        bool reflect() const { return get_config().m_bv_reflect; }

        // delay internalize
        enum class internalize_mode {
            delay_i,
            no_delay_i,
            init_bits_only_i
        };

        obj_map<expr, internalize_mode> m_delay_internalize;
        bool m_cheap_axioms{ true };
        bool should_bit_blast(app * n);
        bool check_delay_internalized(expr* e);
        bool check_mul(app* e);
        bool check_mul_invertibility(app* n, expr_ref_vector const& arg_values, expr* value);
        bool check_mul_zero(app* n, expr_ref_vector const& arg_values, expr* value1, expr* value2);
        bool check_mul_one(app* n, expr_ref_vector const& arg_values, expr* value1, expr* value2);
        bool check_umul_no_overflow(app* n, expr_ref_vector const& arg_values, expr* value);
        bool check_bv_eval(euf::enode* n);
        bool check_bool_eval(euf::enode* n);
        void encode_msb_tail(expr* x, expr_ref_vector& xs);
        void encode_lsb_tail(expr* x, expr_ref_vector& xs);
        internalize_mode get_internalize_mode(expr* e);
        void set_delay_internalize(expr* e, internalize_mode mode);
        expr_ref eval_args(euf::enode* n, expr_ref_vector& eargs);
        expr_ref eval_bv(euf::enode* n);
        
        // solving
        theory_var find(theory_var v) const { return m_find.find(v); }
        void find_wpos(theory_var v);
        void find_new_diseq_axioms(atom& a, theory_var v, unsigned idx);
        void mk_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx);
        bool get_fixed_value(theory_var v, numeral& result) const;
        void add_fixed_eq(theory_var v1, theory_var v2);      
        svector<theory_var>   m_merge_aux[2]; //!< auxiliary vector used in merge_zero_one_bits
        bool merge_zero_one_bits(theory_var r1, theory_var r2);
        bool assign_bit(literal consequent, theory_var v1, theory_var v2, unsigned idx, literal antecedent, bool propagate_eqc);
        bool propagate_bits(var_pos entry);
        bool propagate_eq_occurs(eq_occurs const& occ);
        numeral const& power2(unsigned i) const;
        sat::literal mk_true();


        // invariants
        bool check_zero_one_bits(theory_var v);
        void check_missing_propagation() const;
        void validate_atoms() const;
        
        std::ostream& display(std::ostream& out, atom const& a) const;
       
    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override {}
        void set_lookahead(sat::lookahead* s) override { }
        void init_search() override {}
        double get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r, bool probing) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        void push_core() override;
        void pop_core(unsigned n) override;   
        void simplify() override;
        bool set_root(literal l, literal r) override;
        void flush_roots() override;
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        extension* copy(sat::solver* s) override;       
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override {}
        void gc() override {}
        void pop_reinit() override;
        bool validate() override;
        void init_use_list(sat::ext_use_list& ul) override;
        bool is_blocked(literal l, sat::ext_constraint_idx) override;
        bool check_model(sat::model const& m) const override;
        void finalize_model(model& mdl) override;

        void new_eq_eh(euf::th_eq const& eq) override;
        void new_diseq_eh(euf::th_eq const& ne) override;
        bool use_diseqs() const override { return true; }
        bool unit_propagate() override;

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;

        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override { return false; }

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override { return false; }
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        void eq_internalized(euf::enode* n) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode * n, sort * s) override;

        
        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { SASSERT(check_zero_one_bits(r1)); }
        void unmerge_eh(theory_var v1, theory_var v2);
        trail_stack& get_trail_stack();

        // diagnostics
        std::ostream& display(std::ostream& out, theory_var v) const;        
        typedef std::pair<solver const*, theory_var> pp_var;
        pp_var pp(theory_var v) const { return pp_var(this, v); }

        friend std::ostream& operator<<(std::ostream& out, solver::zero_one_bit const& zo) { return zo.display(out); }

    };

    inline std::ostream& operator<<(std::ostream& out, solver::pp_var const& p) { return p.first->display(out, p.second); }



}
