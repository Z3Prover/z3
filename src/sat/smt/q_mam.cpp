/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    euf_mam.cpp

Abstract:

    Matching Abstract Machine

Author:

    Leonardo de Moura (leonardo) 2007-02-13.
    Nikolaj Bjorner (nbjorner) 2021-01-22.

Revision History:

    Ported to self-contained egraph 

--*/
#include <algorithm>

#include "util/pool.h"
#include "util/trail.h"
#include "util/stopwatch.h"
#include "util/approx_set.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_egraph.h"
#include "sat/smt/q_mam.h"
#include "sat/smt/q_ematch.h"
#include "sat/smt/euf_solver.h"



// #define _PROFILE_MAM

// -----------------------------------------
// Flags for _PROFILE_MAM
//
// send profiling information to stdout
#define _PROFILE_MAM_TO_STDOUT
// threshold in secs for being considered expensive
#define _PROFILE_MAM_THRESHOLD 30.0
// dump expensive (> _PROFILE_MAM_THRESHOLD) code trees whenever execute_core is executed.
#define _PROFILE_MAM_EXPENSIVE
//
#define _PROFILE_MAM_EXPENSIVE_FREQ 100000
//
// -----------------------------------------

// #define _PROFILE_PATH_TREE
// -----------------------------------------
// Flags for _PROFILE_PATH_TREE
//
#define _PROFILE_PATH_TREE_THRESHOLD 20000
//
// -----------------------------------------

#define IS_CGR_SUPPORT true

namespace q {
    // ------------------------------------
    //
    // Trail
    //
    // ------------------------------------

    class mam_impl;


    template<typename T>
    class mam_value_trail : public value_trail<T> {
    public:
        mam_value_trail(T & value):value_trail<T>(value) {}
    };

    unsigned get_max_generation(unsigned n, enode* const* nodes) {
        unsigned g = 0;
        for (unsigned i = 0; i < n; ++i) 
            g = std::max(g, nodes[i]->generation());
        return g;
    }


    // ------------------------------------
    //
    // Auxiliary
    //
    // ------------------------------------
    class label_hasher {
        svector<signed char>             m_lbl2hash;        // cache: lbl_id -> hash

        void mk_lbl_hash(unsigned lbl_id) {
            unsigned a = 17;
            unsigned b = 3;
            unsigned c = lbl_id;
            mix(a, b, c);
            m_lbl2hash[lbl_id] = c & (APPROX_SET_CAPACITY - 1);
        }

    public:
        unsigned char operator()(func_decl * lbl) {
            unsigned lbl_id = lbl->get_small_id();
            if (lbl_id >= m_lbl2hash.size())
                m_lbl2hash.resize(lbl_id + 1, -1);
            if (m_lbl2hash[lbl_id] == -1) {
                mk_lbl_hash(lbl_id);
            }
            SASSERT(m_lbl2hash[lbl_id] >= 0);
            return m_lbl2hash[lbl_id];
        }

        void display(std::ostream & out) const {
            out << "lbl-hasher:\n";
            bool first = true;
            for (unsigned i = 0; i < m_lbl2hash.size(); i++) {
                if (m_lbl2hash[i] != -1) {
                    if (first)
                        first = false;
                    else
                        out << ", ";
                    out << i << " -> " << static_cast<int>(m_lbl2hash[i]);
                }
            }
            out << "\n";
        }
    };

    // ------------------------------------
    //
    // Instructions
    //
    // ------------------------------------
    typedef enum {
        INIT1=0, INIT2,  INIT3,  INIT4,  INIT5,  INIT6,  INITN,
        BIND1,   BIND2,  BIND3,  BIND4,  BIND5,  BIND6,  BINDN,
        YIELD1,  YIELD2, YIELD3, YIELD4, YIELD5, YIELD6, YIELDN,
        COMPARE, CHECK, FILTER, CFILTER, PFILTER, CHOOSE, NOOP, CONTINUE,
        GET_ENODE,
        GET_CGR1, GET_CGR2, GET_CGR3, GET_CGR4, GET_CGR5, GET_CGR6, GET_CGRN,
        IS_CGR
    } opcode;

    struct instruction {
        opcode         m_opcode;
        instruction *  m_next;
#ifdef _PROFILE_MAM
        unsigned       m_counter; // how often it was executed
#endif
        bool is_init() const {
            return m_opcode >= INIT1 && m_opcode <= INITN;
        }
    };

    struct initn : public instruction {
        // We need that because starting at Z3 3.0, some associative
        // operators (e.g., + and *) are represented using n-ary
        // applications.
        // We do not need the extra field for INIT1, ..., INIT6.
        unsigned       m_num_args;
    };

    struct compare : public instruction {
        unsigned       m_reg1;
        unsigned       m_reg2;
    };

    struct check : public instruction {
        unsigned       m_reg;
        enode *        m_enode;
    };

    struct filter : public instruction {
        unsigned       m_reg;
        approx_set     m_lbl_set;
    };

    struct pcheck : public instruction {
        enode *        m_enode;
        approx_set     m_lbl_set;
    };

    /**
       \brief Copy m_enode to register m_oreg
    */
    struct get_enode_instr : public instruction {
        unsigned  m_oreg;
        enode *   m_enode;
    };

    struct choose: public instruction {
        choose *       m_alt;
    };

    /**
       \brief A depth-2 joint. It is used in CONTINUE instruction.
       There are 3 forms of joints
       1) Variables:   (f ... X ...)
       2) Ground terms: (f ... t ...)
       3) depth 2 joint: (f ... (g ... X ...) ...)
          Joint2 stores the declaration g, and the position of variable X, and its idx.

       \remark Z3 has no support for depth 3 joints (f ... (g ... (h ... X ...) ...) ....)
    */
    struct joint2 {
        func_decl * m_decl;
        unsigned    m_arg_pos;
        unsigned    m_reg;    // register that contains the variable
        joint2(func_decl * f, unsigned pos, unsigned r):m_decl(f), m_arg_pos(pos), m_reg(r) {}
    };

#define NULL_TAG        0
#define GROUND_TERM_TAG 1
#define VAR_TAG         2
#define NESTED_VAR_TAG  3

    struct cont: public instruction {
        func_decl *     m_label;
        unsigned short  m_num_args;
        unsigned        m_oreg;
        approx_set      m_lbl_set; // singleton set containing m_label
        /*
          The following field is an array of tagged pointers.
          Each position contains:
          1- null (no joint), NULL_TAG
          2- a boxed integer (i.e., register that contains the variable bind) VAR_TAG
          3- an enode pointer (ground term)  GROUND_TERM_TAG
          4- or, a joint2 pointer.    NESTED_VAR_TAG

          The size of the array is m_num_args.
        */
        enode *         m_joints[0];
    };

    struct bind : public instruction {
        func_decl *    m_label;
        unsigned short m_num_args;
        unsigned       m_ireg;
        unsigned       m_oreg;
    };

    struct get_cgr : public instruction {
        func_decl *    m_label;
        approx_set     m_lbl_set;
        unsigned short m_num_args;
        unsigned       m_oreg;
        unsigned       m_iregs[0];
    };

    struct yield : public instruction {
        quantifier *      m_qa;
        app *             m_pat;
        unsigned short    m_num_bindings;
        unsigned          m_bindings[0];
    };

    struct is_cgr : public instruction {
        unsigned       m_ireg;
        func_decl *    m_label;
        unsigned short m_num_args;
        unsigned       m_iregs[0];
    };

    void display_num_args(std::ostream & out, unsigned num_args) {
        if (num_args <= 6) {
            out << num_args;
        }
        else {
            out << "N";
        }
    }

    void display_bind(std::ostream & out, const bind & b) {
        out << "(BIND";
        display_num_args(out, b.m_num_args);
        out << " " << b.m_label->get_name() << " " << b.m_ireg << " " << b.m_oreg << ")";
    }

    void display_get_cgr(std::ostream & out, const get_cgr & c) {
        out << "(GET_CGR";
        display_num_args(out, c.m_num_args);
        out << " " << c.m_label->get_name() << " " << c.m_oreg;
        for (unsigned i = 0; i < c.m_num_args; i++)
            out << " " << c.m_iregs[i];
        out << ")";
    }

    void display_is_cgr(std::ostream & out, const is_cgr & c) {
        out << "(IS_CGR " << c.m_label->get_name() << " " << c.m_ireg;
        for (unsigned i = 0; i < c.m_num_args; i++)
            out << " " << c.m_iregs[i];
        out << ")";
    }

    void display_yield(std::ostream & out, const yield & y) {
        out << "(YIELD";
        display_num_args(out, y.m_num_bindings);
        out << " #" << y.m_qa->get_id();
        for (unsigned i = 0; i < y.m_num_bindings; i++) {
            out << " " << y.m_bindings[i];
        }
        out << ")";
    }

    void display_joints(std::ostream & out, unsigned num_joints, enode * const * joints) {
        for (unsigned i = 0; i < num_joints; i++) {
            if (i > 0)
                out << " ";
            enode * bare = joints[i];
            switch (GET_TAG(bare)) {
            case NULL_TAG: out << "nil"; break;
            case GROUND_TERM_TAG: out << "#" << UNTAG(enode*, bare)->get_expr_id(); break;
            case VAR_TAG: out << UNBOXINT(bare); break;
            case NESTED_VAR_TAG: out << "(" << UNTAG(joint2*, bare)->m_decl->get_name() << " " << UNTAG(joint2*, bare)->m_arg_pos << " " << UNTAG(joint2*, bare)->m_reg << ")"; break;
            }
        }
    }

    void display_continue(std::ostream & out, const cont & c) {
        out << "(CONTINUE " << c.m_label->get_name() << " " << c.m_num_args << " " << c.m_oreg << " "
            << c.m_lbl_set << " (";
        display_joints(out, c.m_num_args, c.m_joints);
        out << "))";
    }

    void display_filter(std::ostream & out, char const * op, filter const & instr) {
        out << "(" << op << " " << instr.m_reg
            << " " << instr.m_lbl_set << ")";
    }

    std::ostream & operator<<(std::ostream & out, const instruction & instr) {
        switch (instr.m_opcode) {
        case INIT1: case INIT2: case INIT3: case INIT4: case INIT5: case INIT6: case INITN:
            out << "(INIT";
            if (instr.m_opcode <= INIT6)
                out << (instr.m_opcode - INIT1 + 1);
            else
                out << "N";
            out << ")";
            break;
        case BIND1: case BIND2: case BIND3: case BIND4: case BIND5: case BIND6: case BINDN:
            display_bind(out, static_cast<const bind &>(instr));
            break;
        case GET_CGR1: case GET_CGR2: case GET_CGR3: case GET_CGR4: case GET_CGR5: case GET_CGR6: case GET_CGRN:
            display_get_cgr(out, static_cast<const get_cgr &>(instr));
            break;
        case IS_CGR:
            display_is_cgr(out, static_cast<const is_cgr &>(instr));
            break;
        case YIELD1: case YIELD2: case YIELD3: case YIELD4: case YIELD5: case YIELD6: case YIELDN:
            display_yield(out, static_cast<const yield &>(instr));
            break;
        case CONTINUE:
            display_continue(out, static_cast<const cont &>(instr));
            break;
        case COMPARE:
            out << "(COMPARE " << static_cast<const compare &>(instr).m_reg1 << " "
                << static_cast<const compare &>(instr).m_reg2 << ")";
            break;
        case CHECK:
            out << "(CHECK " << static_cast<const check &>(instr).m_reg
                << " #" << static_cast<const check &>(instr).m_enode->get_expr_id() << ")";
            break;
        case FILTER:
            display_filter(out, "FILTER", static_cast<const filter &>(instr));
            break;
        case CFILTER:
            display_filter(out, "CFILTER", static_cast<const filter &>(instr));
            break;
        case PFILTER:
            display_filter(out, "PFILTER", static_cast<const filter &>(instr));
            break;
        case GET_ENODE:
            out << "(GET_ENODE " << static_cast<const get_enode_instr &>(instr).m_oreg << " #" <<
                static_cast<const get_enode_instr &>(instr).m_enode->get_expr_id() << ")";
            break;
        case CHOOSE:
            out << "(CHOOSE)";
            break;
        case NOOP:
            out << "(NOOP)";
            break;
        }
#ifdef _PROFILE_MAM
        out << "[" << instr.m_counter << "]";
#endif
        return out;
    }

    // ------------------------------------
    //
    // Code Tree
    //
    // ------------------------------------

    inline enode * mk_enode(egraph & egraph, quantifier * qa, app * n) {
        enode * e = egraph.find(n);
        SASSERT(e);
        return e;
    }

    class code_tree {
        label_hasher &             m_lbl_hasher;
        func_decl *                m_root_lbl;
        unsigned                   m_num_args; //!< we need this information to avoid the nary *,+ crash bug
        bool                       m_filter_candidates;
        unsigned                   m_num_regs;
        unsigned                   m_num_choices = 0;
        instruction *              m_root = nullptr;
        enode_vector               m_candidates;
        unsigned                   m_qhead = 0;
#ifdef Z3DEBUG
        egraph *                   m_egraph = nullptr;
        svector<std::pair<quantifier*, app*>>            m_patterns;
#endif
#ifdef _PROFILE_MAM
        stopwatch                  m_watch;
        unsigned                   m_counter = 0;
#endif
        friend class compiler;
        friend class code_tree_manager;

        void spaces(std::ostream& out, unsigned indent) const {
            for (unsigned i = 0; i < indent; i++) 
                out << "    ";
        }

        void display_seq(std::ostream & out, instruction * head, unsigned indent) const {
            spaces(out, indent);
            instruction * curr = head;
            out << *curr;
            curr = curr->m_next;
            while (curr != nullptr && curr->m_opcode != CHOOSE && curr->m_opcode != NOOP) {
                out << "\n";
                spaces(out, indent);
                out << *curr;
                curr = curr->m_next;
            }
            out << "\n";
            if (curr != nullptr) {
                display_children(out, static_cast<choose*>(curr), indent + 1);
            }
        }

        void display_children(std::ostream & out, choose * first_child, unsigned indent) const {
            choose * curr = first_child;
            while (curr != nullptr) {
                display_seq(out, curr, indent);
                curr = curr->m_alt;
            }
        }

#ifdef Z3DEBUG
        inline enode * get_enode(egraph & ctx, app * n) const {
            enode * e = ctx.find(n);
            SASSERT(e);
            return e;
        }

        void display_label_hashes_core(std::ostream & out, app * p) const {
            if (is_ground(p)) {
                enode * e = get_enode(*m_egraph, p);
                SASSERT(e->has_lbl_hash());
                out << "#" << e->get_expr_id() << ":" << e->get_lbl_hash() << " ";
            }
            else {
                out << p->get_decl()->get_name() << ":" << m_lbl_hasher(p->get_decl()) << " ";
                for (expr* arg : *p)
                    if (is_app(arg))
                        display_label_hashes(out, to_app(arg));
            }
        }

        void display_label_hashes(std::ostream & out, app * p) const {
            ast_manager & m = m_egraph->get_manager();
            if (m.is_pattern(p)) {
                for (expr* arg : *p) 
                    if (is_app(arg)) {
                        display_label_hashes_core(out, to_app(arg));
                        out << "\n";
                    }
            }
            else {
                display_label_hashes_core(out, p);
                out << "\n";
            }
        }
#endif

    public:
        code_tree(label_hasher & h, func_decl * lbl, unsigned short num_args, bool filter_candidates):
            m_lbl_hasher(h),
            m_root_lbl(lbl),
            m_num_args(num_args),
            m_filter_candidates(filter_candidates),
            m_num_regs(num_args + 1) {
            (void)m_lbl_hasher;
        }

#ifdef _PROFILE_MAM
        ~code_tree() {
#ifdef _PROFILE_MAM_TO_STDOUT
            std::cout << "killing code tree for: " << m_root_lbl->get_name() << " " << static_cast<unsigned long long>(m_watch.get_seconds() * 1000) << "\n"; display(std::cout);
#endif
        }

        stopwatch & get_watch() {
            return m_watch;
        }

        void inc_counter() {
            m_counter++;
        }

        unsigned get_counter() const {
            return m_counter;
        }
#endif

        unsigned expected_num_args() const {
            return m_num_args;
        }

        unsigned get_num_regs() const {
            return m_num_regs;
        }

        unsigned get_num_choices() const {
            return m_num_choices;
        }

        func_decl * get_root_lbl() const {
            return m_root_lbl;
        }

        bool filter_candidates() const {
            return m_filter_candidates;
        }

        const instruction * get_root() const {
            return m_root;
        }

        void add_candidate(euf::solver& ctx, enode * n) {
            m_candidates.push_back(n);
            ctx.push(push_back_trail<enode*, false>(m_candidates));
        }

        void unmark(unsigned head) {
            for (unsigned i = m_candidates.size(); i-- > head; ) {
                enode* app = m_candidates[i];
                if (app->is_marked3())
                    app->unmark3();
            }
        }

        struct scoped_unmark {
            unsigned   m_qhead;
            code_tree* t;
            scoped_unmark(code_tree* t) : m_qhead(t->m_qhead), t(t) {}
            ~scoped_unmark() { t->unmark(m_qhead); }
        };


        bool has_candidates() const {
            return m_qhead < m_candidates.size();
        }

        void save_qhead(euf::solver& ctx) {
            ctx.push(value_trail<unsigned>(m_qhead));
        }

        enode* next_candidate() {
            if (m_qhead < m_candidates.size())
                return m_candidates[m_qhead++];
            else
                return nullptr;
        }

        enode_vector const & get_candidates() const {
            return m_candidates;
        }

#ifdef Z3DEBUG
        void set_egraph(egraph * ctx) {
            SASSERT(m_egraph == nullptr);
            m_egraph = ctx;
        }

        svector<std::pair<quantifier*, app*>> & get_patterns() {
            return m_patterns;
        }
#endif

        void display(std::ostream & out) const {
#ifdef Z3DEBUG
            if (m_egraph) {
                ast_manager & m = m_egraph->get_manager();
                out << "patterns:\n";
                for (auto [q, a] : m_patterns) 
                    out << q->get_id() << ": " << mk_pp(q, m) << " " << mk_pp(a, m) << "\n";
            }
#endif
            out << "function: " << m_root_lbl->get_name();
#ifdef _PROFILE_MAM
            out << " " << m_watch.get_seconds() << " secs, [" << m_counter << "]";
#endif
            out << "\n";
            out << "num. regs:    " << m_num_regs << "\n"
                << "num. choices: " << m_num_choices << "\n";
            display_seq(out, m_root, 0);
        }
    };

    std::ostream & operator<<(std::ostream & out, code_tree const & tree) {
        tree.display(out);
        return out;
    }

    // ------------------------------------
    //
    // Code Tree Manager
    //
    // ------------------------------------

    class code_tree_manager {
        euf::solver &     ctx;
        label_hasher &    m_lbl_hasher;
        region &          m_region;

        template<typename OP>
        OP * mk_instr(opcode op, unsigned size) {
            void * mem = m_region.allocate(size);
            OP * r = new (mem) OP;
            r->m_opcode = op;
            r->m_next   = nullptr;
#ifdef _PROFILE_MAM
            r->m_counter = 0;
#endif
            return r;
        }

        instruction * mk_init(unsigned n) {
            SASSERT(n >= 1);
            opcode op = n <= 6 ? static_cast<opcode>(INIT1 + n - 1) : INITN;
            if (op == INITN) {
                // We store the actual number of arguments for INITN.
                // Starting at Z3 3.0, some associative operators
                // (e.g., + and *) are represented using n-ary
                // applications.
                initn * r = mk_instr<initn>(op, sizeof(initn));
                r->m_num_args = n;
                return r;
            }
            else {
                return mk_instr<instruction>(op, sizeof(instruction));
            }
        }

    public:
        code_tree_manager(label_hasher & h, euf::solver& ctx):
            ctx(ctx),
            m_lbl_hasher(h),
            m_region(ctx.get_region()) {
        }

        code_tree * mk_code_tree(func_decl * lbl, unsigned short num_args, bool filter_candidates) {
            code_tree * r = alloc(code_tree,m_lbl_hasher, lbl, num_args, filter_candidates);
            r->m_root     = mk_init(num_args);
            return r;
        }

        joint2 * mk_joint2(func_decl * f, unsigned pos, unsigned reg) {
            return new (m_region) joint2(f, pos, reg);
        }

        compare * mk_compare(unsigned reg1, unsigned reg2) {
            compare * r = mk_instr<compare>(COMPARE, sizeof(compare));
            r->m_reg1 = reg1;
            r->m_reg2 = reg2;
            return r;
        }

        check * mk_check(unsigned reg, enode * n) {
            check * r = mk_instr<check>(CHECK, sizeof(check));
            r->m_reg   = reg;
            r->m_enode = n;
            return r;
        }

        filter * mk_filter_core(opcode op, unsigned reg, approx_set s) {
            filter * r = mk_instr<filter>(op, sizeof(filter));
            r->m_reg      = reg;
            r->m_lbl_set  = s;
            return r;
        }

        filter * mk_filter(unsigned reg, approx_set s) {
            return mk_filter_core(FILTER, reg, s);
        }

        filter * mk_pfilter(unsigned reg, approx_set s) {
            return mk_filter_core(PFILTER, reg, s);
        }

        filter * mk_cfilter(unsigned reg, approx_set s) {
            return mk_filter_core(CFILTER, reg, s);
        }

        get_enode_instr * mk_get_enode(unsigned reg, enode * n) {
            get_enode_instr * s = mk_instr<get_enode_instr>(GET_ENODE, sizeof(get_enode_instr));
            s->m_oreg  = reg;
            s->m_enode = n;
            return s;
        }

        choose * mk_choose(choose * alt) {
            choose * r  = mk_instr<choose>(CHOOSE, sizeof(choose));
            r->m_alt = alt;
            return r;
        }

        choose * mk_noop() {
            choose * r  = mk_instr<choose>(NOOP, sizeof(choose));
            r->m_alt = nullptr;
            return r;
        }

        bind * mk_bind(func_decl * lbl, unsigned short num_args, unsigned ireg, unsigned oreg) {
            SASSERT(num_args >= 1);
            opcode op = num_args <= 6 ? static_cast<opcode>(BIND1 + num_args - 1) : BINDN;
            bind * r = mk_instr<bind>(op, sizeof(bind));
            r->m_label    = lbl;
            r->m_num_args = num_args;
            r->m_ireg     = ireg;
            r->m_oreg     = oreg;
            return r;
        }

        get_cgr * mk_get_cgr(func_decl * lbl, unsigned oreg, unsigned num_args, unsigned const * iregs) {
            SASSERT(num_args >= 1);
            opcode op = num_args <= 6 ? static_cast<opcode>(GET_CGR1 + num_args - 1) : GET_CGRN;
            get_cgr * r   = mk_instr<get_cgr>(op, sizeof(get_cgr) + num_args * sizeof(unsigned));
            r->m_label    = lbl;
            r->m_lbl_set.insert(m_lbl_hasher(lbl));
            r->m_oreg     = oreg;
            r->m_num_args = num_args;
            memcpy(r->m_iregs, iregs, sizeof(unsigned) * num_args);
            return r;
        }

        is_cgr * mk_is_cgr(func_decl * lbl, unsigned ireg, unsigned num_args, unsigned const * iregs) {
            SASSERT(num_args >= 1);
            is_cgr * r   = mk_instr<is_cgr>(IS_CGR, sizeof(is_cgr) + num_args * sizeof(unsigned));
            r->m_label    = lbl;
            r->m_ireg     = ireg;
            r->m_num_args = num_args;
            memcpy(r->m_iregs, iregs, sizeof(unsigned) * num_args);
            return r;
        }

        yield * mk_yield(quantifier * qa, app * pat, unsigned num_bindings, unsigned * bindings) {
            SASSERT(num_bindings >= 1);
            opcode op         = num_bindings <= 6 ? static_cast<opcode>(YIELD1 + num_bindings - 1) : YIELDN;
            yield * y         = mk_instr<yield>(op, sizeof(yield) + num_bindings * sizeof(unsigned));
            y->m_qa           = qa;
            y->m_pat          = pat;
            y->m_num_bindings = num_bindings;
            memcpy(y->m_bindings, bindings, sizeof(unsigned) * num_bindings);
            return y;
        }

        cont * mk_cont(func_decl * lbl, unsigned short num_args, unsigned oreg,
                       approx_set const & s, enode * const * joints) {
            SASSERT(num_args >= 1);
            cont * r        = mk_instr<cont>(CONTINUE, sizeof(cont) + num_args * sizeof(enode*));
            r->m_label      = lbl;
            r->m_num_args   = num_args;
            r->m_oreg       = oreg;
            r->m_lbl_set    = s;
            memcpy(r->m_joints, joints, num_args * sizeof(enode *));
            return r;
        }

        void set_next(instruction * instr, instruction * new_next) {
            ctx.push(mam_value_trail<instruction*>(instr->m_next));
            instr->m_next = new_next;
        }

        void save_num_regs(code_tree * tree) {
            ctx.push(mam_value_trail<unsigned>(tree->m_num_regs));
        }

        void save_num_choices(code_tree * tree) {
            ctx.push(mam_value_trail<unsigned>(tree->m_num_choices));
        }

        void insert_new_lbl_hash(filter * instr, unsigned h) {
            ctx.push(mam_value_trail<approx_set>(instr->m_lbl_set));
            instr->m_lbl_set.insert(h);
        }
    };

    // ------------------------------------
    //
    // Compiler: Pattern ---> Code Tree
    //
    // ------------------------------------

    class compiler {
        egraph &                m_egraph;
        ast_manager &           m;
        code_tree_manager &     m_ct_manager;
        label_hasher &          m_lbl_hasher;
        bool                    m_use_filters;
        ptr_vector<expr>        m_registers;
        unsigned_vector         m_todo; // list of registers that have patterns to be processed.
        unsigned_vector         m_aux;
        int_vector              m_vars; // -1 the variable is unbound, >= 0 is the register that contains the variable
        quantifier *            m_qa;
        app *                   m_mp;
        code_tree *             m_tree;
        unsigned                m_num_choices;
        bool                    m_is_tmp_tree;
        bool_vector             m_mp_already_processed;
        obj_map<expr, unsigned> m_matched_exprs;

        struct pcheck_checked {
            func_decl * m_label;
            enode *     m_enode;
        };

        typedef enum { NOT_CHECKED,
                       CHECK_SET,
                       CHECK_SINGLETON } check_mark;

        svector<check_mark>     m_mark;
        unsigned_vector         m_to_reset;
        ptr_vector<instruction> m_compatible;
        ptr_vector<instruction> m_incompatible;
        ptr_vector<instruction> m_seq;

        void set_register(unsigned reg, expr * p) {
            m_registers.setx(reg, p, nullptr);
        }

        check_mark get_check_mark(unsigned reg) const {
            return m_mark.get(reg, NOT_CHECKED);
        }

        void set_check_mark(unsigned reg, check_mark cm) {
            m_mark.setx(reg, cm, NOT_CHECKED);
        }

        void init(code_tree * t, quantifier * qa, app * mp, unsigned first_idx) {
            SASSERT(m.is_pattern(mp));
#ifdef Z3DEBUG
            for (auto cm : m_mark) {
                SASSERT(cm == NOT_CHECKED);
            }
#endif
            m_tree        = t;
            m_qa          = qa;
            m_mp          = mp;
            m_num_choices = 0;
            m_todo.reset();
            m_registers.fill(0);

            app * p = to_app(mp->get_arg(first_idx));
            SASSERT(t->get_root_lbl() == p->get_decl());
            unsigned num_args = p->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                set_register(i+1, p->get_arg(i));
                m_todo.push_back(i+1);
            }
            unsigned num_decls = m_qa->get_num_decls();
            if (num_decls > m_vars.size()) {
                m_vars.resize(num_decls, -1);
            }
            for (unsigned j = 0; j < num_decls; j++) {
                m_vars[j] = -1;
            }
        }

        /**
           \brief Return true if all arguments of n are bound variables.
           That is, during execution time, the variables will be already bound
         */
        bool all_args_are_bound_vars(app * n) {
            for (expr* arg : *n) {
                if (!is_var(arg))
                    return false;
                if (m_vars[to_var(arg)->get_idx()] == -1)
                    return false;
            }
            return true;
        }

        /**
           \see get_stats
        */
        void get_stats_core(app * n, unsigned & sz, unsigned & num_unbound_vars) {
            sz++;
            if (n->is_ground()) {
                return;
            }
            for (expr* arg : *n) {
                if (is_var(arg)) {
                    sz++;
                    unsigned var_id = to_var(arg)->get_idx();
                    if (m_vars[var_id] == -1)
                        num_unbound_vars++;
                }
                else if (is_app(arg)) {
                    get_stats_core(to_app(arg), sz, num_unbound_vars);
                }
            }
        }

        /**
           \brief Return statistics for the given pattern
           \remark Patterns are small. So, it doesn't hurt to use a recursive function.
        */
        void get_stats(app * n, unsigned & sz, unsigned & num_unbound_vars) {
            sz = 0;
            num_unbound_vars = 0;
            get_stats_core(n, sz, num_unbound_vars);
        }

        /**
           \brief Process registers in m_todo. The registers in m_todo
           that produce non-BIND operations are processed first. Then,
           a single BIND operation b is produced.

           After executing this method m_todo will contain the
           registers in m_todo that produce BIND operations and were
           not processed, and the registers generated when the
           operation b was produced.

           \remark The new operations are appended to m_seq.
        */
        void linearise_core() {
            m_aux.reset();
            app *         first_app = nullptr;
            unsigned      first_app_reg = 0;
            unsigned      first_app_sz = 0;
            unsigned      first_app_num_unbound_vars = 0;
            // generate first the non-BIND operations
            for (unsigned reg : m_todo) {
                expr *  p    = m_registers[reg];
                SASSERT(!is_quantifier(p));
                TRACE("mam", tout << "lin: " << reg << " " << get_check_mark(reg) << " " << is_var(p) << "\n";);
                if (is_var(p)) {
                    unsigned var_id = to_var(p)->get_idx();
                    if (m_vars[var_id] != -1)
                        m_seq.push_back(m_ct_manager.mk_compare(m_vars[var_id], reg));
                    else
                        m_vars[var_id] = reg;
                    continue;
                }


                SASSERT(is_app(p));

                if (to_app(p)->is_ground()) {
                    // ground applications are viewed as constants, and eagerly
                    // converted into enodes.
                    enode * e = m_egraph.find(p);
                    m_seq.push_back(m_ct_manager.mk_check(reg, e));
                    set_check_mark(reg, NOT_CHECKED); // reset mark, register was fully processed.
                    continue;
                }

                unsigned matched_reg;
                if (m_matched_exprs.find(p, matched_reg) && reg != matched_reg) {
                    m_seq.push_back(m_ct_manager.mk_compare(matched_reg, reg));
                    set_check_mark(reg, NOT_CHECKED); // reset mark, register was fully processed.
                    continue;
                }
                m_matched_exprs.insert(p, reg);

                if (m_use_filters && get_check_mark(reg) != CHECK_SINGLETON) {
                    func_decl * lbl = to_app(p)->get_decl();
                    approx_set s(m_lbl_hasher(lbl));
                    m_seq.push_back(m_ct_manager.mk_filter(reg, s));
                    set_check_mark(reg, CHECK_SINGLETON);
                }

                if (first_app) {
                    // Try to select the best first_app
                    if (first_app_num_unbound_vars == 0) {
                        // first_app doesn't have free vars... so it is the best choice...
                        m_aux.push_back(reg);
                    }
                    else {
                        unsigned sz;
                        unsigned num_unbound_vars;
                        get_stats(to_app(p), sz, num_unbound_vars);
                        if (num_unbound_vars == 0 ||
                            sz > first_app_sz ||
                            (sz == first_app_sz && num_unbound_vars < first_app_num_unbound_vars)) {
                            // change the first_app
                            m_aux.push_back(first_app_reg);
                            first_app     = to_app(p);
                            first_app_reg = reg;
                            first_app_sz  = sz;
                            first_app_num_unbound_vars = num_unbound_vars;
                        }
                        else {
                            m_aux.push_back(reg);
                        }
                    }
                }
                else {
                    first_app     = to_app(p);
                    first_app_reg = reg;
                    get_stats(first_app, first_app_sz, first_app_num_unbound_vars);
                }
            }

            if (first_app) {
                // m_todo contains at least one (non-ground) application.
                func_decl * lbl         = first_app->get_decl();
                unsigned short num_args = first_app->get_num_args();
                if (IS_CGR_SUPPORT && all_args_are_bound_vars(first_app)) {
                    // use IS_CGR instead of BIND
                    sbuffer<unsigned> iregs;                    
                    for (unsigned i = 0; i < num_args; i++) {
                        expr * arg = to_app(first_app)->get_arg(i);
                        SASSERT(is_var(arg));
                        SASSERT(m_vars[to_var(arg)->get_idx()] != -1);
                        iregs.push_back(m_vars[to_var(arg)->get_idx()]);
                    }
                    m_seq.push_back(m_ct_manager.mk_is_cgr(lbl, first_app_reg, num_args, iregs.data()));
                }
                else {
                    // Generate a BIND operation for this application.
                    unsigned oreg           = m_tree->m_num_regs;
                    m_tree->m_num_regs     += num_args;
                    for (unsigned j = 0; j < num_args; j++) {
                        set_register(oreg + j, first_app->get_arg(j));
                        m_aux.push_back(oreg + j);
                    }
                    m_seq.push_back(m_ct_manager.mk_bind(lbl, num_args, first_app_reg, oreg));
                    m_num_choices++;
                }
                set_check_mark(first_app_reg, NOT_CHECKED); // reset mark, register was fully processed.
            }

            // make m_aux the new todo list.
            m_todo.swap(m_aux);
        }

        /**
           \brief Return the number of already bound vars in n.

           \remark Patterns are small. So, it doesn't hurt to use a recursive function.
        */
        unsigned get_num_bound_vars_core(app * n, bool & has_unbound_vars) {
            unsigned r = 0;
            if (n->is_ground()) {
                return 0;
            }
            for (expr * arg : *n) {
                if (is_var(arg)) {
                    unsigned var_id = to_var(arg)->get_idx();
                    if (m_vars[var_id] != -1)
                        r++;
                    else
                        has_unbound_vars = true;
                }
                else if (is_app(arg)) {
                    r += get_num_bound_vars_core(to_app(arg), has_unbound_vars);
                }
            }
            return r;
        }

        unsigned get_num_bound_vars(app * n, bool & has_unbound_vars) {
            has_unbound_vars = false;
            return get_num_bound_vars_core(n, has_unbound_vars);
        }

        /**
           \brief Compile a pattern where all free variables are already bound.
           Return the register where the enode congruent to f will be stored.
        */
        unsigned gen_mp_filter(app * n) {
            if (is_ground(n)) {
                unsigned oreg        = m_tree->m_num_regs;
                m_tree->m_num_regs  += 1;
                enode * e = m_egraph.find(n);
                m_seq.push_back(m_ct_manager.mk_get_enode(oreg, e));
                return oreg;
            }

            sbuffer<unsigned> iregs;
            for (expr* arg : *n) {
                if (is_var(arg)) {
                    SASSERT(m_vars[to_var(arg)->get_idx()] != -1);
                    if (m_vars[to_var(arg)->get_idx()] == -1)
                        verbose_stream() << "BUG.....\n";
                    iregs.push_back(m_vars[to_var(arg)->get_idx()]);
                }
                else {
                    iregs.push_back(gen_mp_filter(to_app(arg)));
                }
            }
            unsigned oreg        = m_tree->m_num_regs;
            m_tree->m_num_regs  += 1;
            m_seq.push_back(m_ct_manager.mk_get_cgr(n->get_decl(), oreg, n->get_num_args(), iregs.data()));
            return oreg;
        }

        /**
           \brief Process the rest of a multi-pattern. That is the patterns different from first_idx
        */
        void linearise_multi_pattern(unsigned first_idx) {
            unsigned num_args = m_mp->get_num_args();
            // multi_pattern support
            for (unsigned i = 1; i < num_args; i++) {
                // select the pattern with the biggest number of bound variables
                app *    best  = nullptr;
                unsigned best_num_bvars = 0;
                unsigned best_j = 0;
                bool     found_bounded_mp = false;
                for (unsigned j = 0; j < m_mp->get_num_args(); j++) {
                    if (m_mp_already_processed[j])
                        continue;
                    app * p            = to_app(m_mp->get_arg(j));
                    bool has_unbound_vars = false;
                    unsigned num_bvars = get_num_bound_vars(p, has_unbound_vars);
                    if (!has_unbound_vars) {
                        best             = p;
                        best_j           = j;
                        found_bounded_mp = true;
                        break;
                    }
                    if (best == nullptr || (num_bvars > best_num_bvars)) {
                        best           = p;
                        best_num_bvars = num_bvars;
                        best_j         = j;
                    }
                }
                m_mp_already_processed[best_j] = true;
                SASSERT(best != 0);
                app * p                 = best;
                func_decl * lbl         = p->get_decl();
                unsigned short num_args = p->get_num_args();
                approx_set s;
                if (m_use_filters)
                    s.insert(m_lbl_hasher(lbl));

                if (found_bounded_mp) {
                    gen_mp_filter(p);
                }
                else {
                    // USE CONTINUE
                    unsigned oreg           = m_tree->m_num_regs;
                    m_tree->m_num_regs     += num_args;
                    ptr_buffer<enode>       joints;
                    bool has_depth1_joint   = false; // VAR_TAG or GROUND_TERM_TAG
                    for (unsigned j = 0; j < num_args; j++) {
                        expr * curr = p->get_arg(j);
                        SASSERT(!is_quantifier(curr));
                        set_register(oreg + j, curr);
                        m_todo.push_back(oreg + j);

                        if ((is_var(curr) && m_vars[to_var(curr)->get_idx()] >= 0)
                            ||
                            (is_app(curr) && (to_app(curr)->is_ground())))
                            has_depth1_joint = true;
                    }

                    if (has_depth1_joint) {
                        for (expr * curr : *p) {

                            if (is_var(curr)) {
                                unsigned var_id = to_var(curr)->get_idx();
                                if (m_vars[var_id] >= 0)
                                    joints.push_back(BOXTAGINT(enode *, m_vars[var_id], VAR_TAG));
                                else
                                    joints.push_back(NULL_TAG);
                                continue;
                            }

                            SASSERT(is_app(curr));

                            if (is_ground(curr)) {
                                enode * e = m_egraph.find(curr);
                                joints.push_back(TAG(enode *, e, GROUND_TERM_TAG));
                                continue;
                            }

                            joints.push_back(0);
                        }
                    }
                    else {
                        // Only try to use depth2 joints if there is no depth1 joint.
                        for (expr * curr : *p) {
                            if (!is_app(curr)) {
                                joints.push_back(0);
                                continue;
                            }
                            unsigned num_args2 = to_app(curr)->get_num_args();
                            unsigned k = 0;
                            for (; k < num_args2; k++) {
                                expr * arg = to_app(curr)->get_arg(k);
                                if (!is_var(arg))
                                    continue;
                                unsigned var_id = to_var(arg)->get_idx();
                                if (m_vars[var_id] < 0)
                                    continue;
                                joint2 * new_joint = m_ct_manager.mk_joint2(to_app(curr)->get_decl(), k, m_vars[var_id]);
                                joints.push_back(TAG(enode *, new_joint, NESTED_VAR_TAG));
                                break; // found a new joint
                            }
                            if (k == num_args2)
                                joints.push_back(0); // didn't find joint
                        }
                    }
                    SASSERT(joints.size() == num_args);
                    m_seq.push_back(m_ct_manager.mk_cont(lbl, num_args, oreg, s, joints.data()));
                    m_num_choices++;
                    while (!m_todo.empty())
                        linearise_core();
                }
            }
        }

        /**
           \brief Produce the operations for the registers in m_todo.
        */
        void linearise(instruction * head, unsigned first_idx) {
            m_seq.reset();
            m_matched_exprs.reset();
            while (!m_todo.empty())
                linearise_core();

            if (m_mp->get_num_args() > 1) {
                m_mp_already_processed.reset();
                m_mp_already_processed.resize(m_mp->get_num_args());
                m_mp_already_processed[first_idx] = true;
                linearise_multi_pattern(first_idx);
            }
            for (unsigned i = 0; i < m_qa->get_num_decls(); i++) 
                if (m_vars[i] == -1)
                    return;
            
            SASSERT(head->m_next == 0);
            m_seq.push_back(m_ct_manager.mk_yield(m_qa, m_mp, m_qa->get_num_decls(), reinterpret_cast<unsigned*>(m_vars.begin())));

            for (instruction * curr : m_seq) {
                head->m_next = curr;
                head = curr;
            }
        }

        void set_next(instruction * instr, instruction * new_next) {
            if (m_is_tmp_tree)
                instr->m_next = new_next;
            else
                m_ct_manager.set_next(instr, new_next);
        }

        /*
          The nodes in the bottom of the code-tree can have a lot of children in big examples.
          Example:
            parent-node:
              (CHOOSE) (CHECK #1 10) (YIELD ...)
              (CHOOSE) (CHECK #2 10) (YIELD ...)
              (CHOOSE) (CHECK #3 10) (YIELD ...)
              (CHOOSE) (CHECK #4 10) (YIELD ...)
              (CHOOSE) (CHECK #5 10) (YIELD ...)
              (CHOOSE) (CHECK #6 10) (YIELD ...)
              (CHOOSE) (CHECK #7 10) (YIELD ...)
              (CHOOSE) (CHECK #8 10) (YIELD ...)
              ...
          The method find_best_child will traverse this big list, and usually will not find
          a compatible child. So, I limit the number of simple code sequences that can be
          traversed.
        */
#define FIND_BEST_CHILD_THRESHOLD 64

        choose * find_best_child(choose * first_child) {
            unsigned num_too_simple    = 0;
            choose * best_child        = nullptr;
            unsigned max_compatibility = 0;
            choose * curr_child        = first_child;
            while (curr_child != nullptr) {
                bool simple = false;
                unsigned curr_compatibility = get_compatibility_measure(curr_child, simple);
                if (simple) {
                    num_too_simple++;
                    if (num_too_simple > FIND_BEST_CHILD_THRESHOLD)
                        return nullptr; // it is unlikely we will find a compatible node
                }
                if (curr_compatibility > max_compatibility) {
                    TRACE("mam", tout << "better child " << best_child << " -> " << curr_child << "\n";);
                    best_child         = curr_child;
                    max_compatibility  = curr_compatibility;
                }
                curr_child = curr_child->m_alt;
            }
            return best_child;
        }

        bool is_compatible(bind * instr) const {
            unsigned ireg = instr->m_ireg;
            expr * n      = m_registers[ireg];
            return
                n != nullptr &&
                is_app(n) &&
                // It is wasteful to use a bind of a ground term.
                // Actually, in the rest of the code I assume that.
                !is_ground(n) &&
                to_app(n)->get_decl() == instr->m_label &&
                to_app(n)->get_num_args() == instr->m_num_args;
        }

        bool is_compatible(compare * instr) const {
            unsigned reg1 = instr->m_reg1;
            unsigned reg2 = instr->m_reg2;
            return
                m_registers[reg1] != nullptr &&
                m_registers[reg1] == m_registers[reg2];
        }

        bool is_compatible(check * instr) const {
            unsigned reg  = instr->m_reg;
            enode *  n    = instr->m_enode;
            if (!m_registers[reg])
                return false;
            if (!is_app(m_registers[reg]))
                return false;
            if (!to_app(m_registers[reg])->is_ground())
                return false;
            enode * n_prime = m_egraph.find(m_registers[reg]);
            // it is safe to compare the roots because the modifications
            // on the code tree are chronological.
            return n->get_root() == n_prime->get_root();
        }

        /**
           \brief Get the label hash of the pattern stored at register reg.

           If the pattern is a ground application, then it is viewed as a
           constant. In this case, we use the field get_lbl_hash() in the enode
           associated with it.
        */
        unsigned get_pat_lbl_hash(unsigned reg) const {
            SASSERT(m_registers[reg] != 0);
            SASSERT(is_app(m_registers[reg]));
            app * p = to_app(m_registers[reg]);
            if (p->is_ground()) {
                enode * e = m_egraph.find(p);
                if (!e->has_lbl_hash())
                    m_egraph.set_lbl_hash(e);
                return e->get_lbl_hash();
            }
            else {
                func_decl * lbl = p->get_decl();
                return m_lbl_hasher(lbl);
            }
        }

        /**
           \brief We say a check operation is semi compatible if
           it access a register that was not yet processed,
           and given reg = instr->m_reg
             1- is_ground(m_registers[reg])
             2- get_pat_lbl_hash(reg) == m_enode->get_lbl_hash()

           If that is the case, then a CFILTER is created
        */
        bool is_semi_compatible(check * instr) const {
            unsigned reg  = instr->m_reg;
            if (instr->m_enode && !instr->m_enode->has_lbl_hash())
                m_egraph.set_lbl_hash(instr->m_enode);
            return
                m_registers[reg] != 0 &&
                // if the register was already checked by another filter, then it doesn't make sense
                // to check it again.
                get_check_mark(reg) == NOT_CHECKED &&
                is_ground(m_registers[reg]) &&
                get_pat_lbl_hash(reg) == instr->m_enode->get_lbl_hash();
        }

        /**
           \brief FILTER is not compatible with ground terms anymore.
           See CFILTER is the filter used for ground terms.
        */
        bool is_compatible(filter * instr) const {
            unsigned reg = instr->m_reg;
            if (m_registers[reg] != 0 && is_app(m_registers[reg]) && !is_ground(m_registers[reg])) {
                // FILTER is fully compatible if it already contains
                // the label hash of the pattern stored at reg.
                unsigned elem = get_pat_lbl_hash(reg);
                return instr->m_lbl_set.may_contain(elem);
            }
            return false;
        }

        bool is_cfilter_compatible(filter * instr) const {
            unsigned reg = instr->m_reg;
            // only ground terms are considered in CFILTERS
            if (m_registers[reg] != 0 && is_ground(m_registers[reg])) {
                // FILTER is fully compatible if it already contains
                // the label hash of the pattern stored at reg.
                unsigned elem = get_pat_lbl_hash(reg);
                return instr->m_lbl_set.may_contain(elem);
            }
            return false;
        }

        /**
           \brief See comments at is_semi_compatible(check * instr) and is_compatible(filter * instr).
           Remark: FILTER is not compatible with ground terms anymore
        */
        bool is_semi_compatible(filter * instr) const {
            unsigned reg = instr->m_reg;
            return
                m_registers[reg] != nullptr &&
                get_check_mark(reg) == NOT_CHECKED &&
                is_app(m_registers[reg]) &&
                !is_ground(m_registers[reg]);
        }

        bool is_compatible(cont * instr) const {
            unsigned oreg = instr->m_oreg;
            for (unsigned i = 0; i < instr->m_num_args; i++)
                if (m_registers[oreg + i] != 0)
                    return false;
            return true;
        }

        // Threshold for a code sequence (in number of instructions) to be considered simple.
#define SIMPLE_SEQ_THRESHOLD 4

        /**
           \brief Return a "compatibility measure" that quantifies how
           many operations in the branch starting at child are compatible
           with the patterns in the registers stored in m_todo.

           Set simple to true, if the tree starting at child is too simple
           (no branching and less than SIMPLE_SEQ_THRESHOLD instructions)
        */
        unsigned get_compatibility_measure(choose * child, bool & simple) {
            simple = true;
            m_to_reset.reset();
            unsigned weight    = 0;
            unsigned num_instr = 0;
            instruction * curr = child->m_next;
            while (curr != nullptr && curr->m_opcode != CHOOSE && curr->m_opcode != NOOP) {
                num_instr++;
                switch (curr->m_opcode) {
                case BIND1: case BIND2: case BIND3: case BIND4: case BIND5: case BIND6: case BINDN:
                    if (is_compatible(static_cast<bind*>(curr))) {
                        weight += 4; // the weight of BIND is bigger than COMPARE and CHECK
                        unsigned ireg     = static_cast<bind*>(curr)->m_ireg;
                        app * n           = to_app(m_registers[ireg]);
                        unsigned oreg     = static_cast<bind*>(curr)->m_oreg;
                        unsigned num_args = static_cast<bind*>(curr)->m_num_args;
                        SASSERT(n->get_num_args() == num_args);
                        for (unsigned i = 0; i < num_args; i++) {
                            set_register(oreg + i, n->get_arg(i));
                            m_to_reset.push_back(oreg + i);
                        }
                    }
                    break;
                case COMPARE:
                    if (is_compatible(static_cast<compare*>(curr)))
                        weight += 2;
                    break;
                case CHECK:
                    if (is_compatible(static_cast<check*>(curr)))
                        weight += 2;
                    else if (m_use_filters && is_semi_compatible(static_cast<check*>(curr)))
                        weight += 1;
                    break;
                case CFILTER:
                    if (is_cfilter_compatible(static_cast<filter*>(curr)))
                        weight += 2;
                    break;
                case FILTER:
                    if (is_compatible(static_cast<filter*>(curr)))
                        weight += 2;
                    else if (is_semi_compatible(static_cast<filter*>(curr)))
                        weight += 1;
                    break;
                // TODO: Try to reuse IS_CGR instruction
                default:
                    break;
                }
                curr = curr->m_next;
            }
            if (num_instr > SIMPLE_SEQ_THRESHOLD || (curr != nullptr && curr->m_opcode == CHOOSE))
                simple = false;
            for (unsigned r : m_to_reset) 
                m_registers[r] = 0;
            return weight;
        }

        void insert(instruction * head, unsigned first_mp_idx) {
            for (;;) {
                m_compatible.reset();
                m_incompatible.reset();
                TRACE("mam_compiler_detail", tout << "processing head: " << *head << "\n";);
                instruction * curr = head->m_next;
                instruction * last = head;
                while (curr != nullptr && curr->m_opcode != CHOOSE && curr->m_opcode != NOOP) {
                    TRACE("mam_compiler_detail", tout << "processing instr: " << *curr << "\n";);
                    switch (curr->m_opcode) {
                    case BIND1: case BIND2: case BIND3: case BIND4: case BIND5: case BIND6: case BINDN: {
                        bind* bnd = static_cast<bind*>(curr);
                        if (is_compatible(bnd)) {
                            TRACE("mam_compiler_detail", tout << "compatible\n";);
                            unsigned ireg     = bnd->m_ireg;
                            SASSERT(m_todo.contains(ireg));
                            m_todo.erase(ireg);
                            set_check_mark(ireg, NOT_CHECKED);
                            m_compatible.push_back(curr);
                            app * app         = to_app(m_registers[ireg]);
                            unsigned oreg     = bnd->m_oreg;
                            unsigned num_args = bnd->m_num_args;
                            for (unsigned i = 0; i < num_args; i++) {
                                set_register(oreg + i, app->get_arg(i));
                                m_todo.push_back(oreg + i);
                            }
                        }
                        else {
                            TRACE("mam_compiler_detail", tout << "incompatible\n";);
                            m_incompatible.push_back(curr);
                        }
                        break;
                    }
                    case CHECK: {
                        check* chk = static_cast<check*>(curr);
                        if (is_compatible(chk)) {
                            TRACE("mam_compiler_detail", tout << "compatible\n";);
                            unsigned reg = chk->m_reg;
                            SASSERT(m_todo.contains(reg));
                            m_todo.erase(reg);
                            set_check_mark(reg, NOT_CHECKED);
                            m_compatible.push_back(curr);
                        }
                        else if (m_use_filters && is_semi_compatible(chk)) {
                            TRACE("mam_compiler_detail", tout << "semi compatible\n";);
                            unsigned reg = chk->m_reg;
                            enode *   n1 = chk->m_enode;
                            // n1->has_lbl_hash may be false, even
                            // when update_filters is invoked before
                            // executing this method.
                            //
                            // Reason: n1 is a ground subterm of a ground term T.
                            // I incorrectly assumed n1->has_lbl_hash() was true because
                            // update_filters executes set_lbl_hash for all maximal ground terms.
                            // And, I also incorrectly assumed that all arguments of check were
                            // maximal ground terms. This is not true. For example, assume
                            // the code_tree already has the pattern
                            // (f (g x) z)
                            // So, when the pattern (f (g b) x) is compiled a check instruction
                            // is created for a ground subterm b of the maximal ground term (g b).
                            if (!n1->has_lbl_hash())
                                m_egraph.set_lbl_hash(n1);
                            unsigned  h1 = n1->get_lbl_hash();
                            unsigned  h2 = get_pat_lbl_hash(reg);
                            approx_set s(h1);
                            s.insert(h2);
                            filter * new_instr = m_ct_manager.mk_cfilter(reg, s);
                            set_check_mark(reg, CHECK_SET);
                            m_compatible.push_back(new_instr);
                            m_incompatible.push_back(curr);
                        }
                        else {
                            TRACE("mam_compiler_detail", tout << "incompatible " << chk->m_reg << "\n";);
                            m_incompatible.push_back(curr);
                        }
                        break;
                    }
                    case COMPARE:
                        if (is_compatible(static_cast<compare*>(curr))) {
                            TRACE("mam_compiler_detail", tout << "compatible\n";);
                            unsigned reg1   = static_cast<compare*>(curr)->m_reg1;
                            unsigned reg2   = static_cast<compare*>(curr)->m_reg2;
                            SASSERT(m_todo.contains(reg2));
                            m_todo.erase(reg2);
                            set_check_mark(reg2, NOT_CHECKED);
                            if (is_var(m_registers[reg1])) {
                                m_todo.erase(reg1);
                                set_check_mark(reg1, NOT_CHECKED);
                                unsigned var_id = to_var(m_registers[reg1])->get_idx();
                                if (m_vars[var_id] == -1)
                                    m_vars[var_id] = reg1;
                            }
                            m_compatible.push_back(curr);
                        }
                        else {
                            TRACE("mam_compiler_detail", tout << "incompatible\n";);
                            m_incompatible.push_back(curr);
                        }
                        break;
                    case CFILTER:
                        SASSERT(m_use_filters);
                        if (is_cfilter_compatible(static_cast<filter*>(curr))) {
                            unsigned reg = static_cast<filter*>(curr)->m_reg;
                            SASSERT(static_cast<filter*>(curr)->m_lbl_set.size() == 1);
                            set_check_mark(reg, CHECK_SINGLETON);
                            m_compatible.push_back(curr);
                        }
                        else {
                            m_incompatible.push_back(curr);
                        }
                        break;
                    case FILTER: {
                        filter *flt = static_cast<filter*>(curr);
                        SASSERT(m_use_filters);
                        if (is_compatible(flt)) {
                            unsigned reg = flt->m_reg;
                            TRACE("mam_compiler_detail", tout << "compatible " << reg << "\n";);
                            CTRACE("mam_compiler_bug", !m_todo.contains(reg), {
                                    for (unsigned t : m_todo) { tout << t << " "; }
                                    tout << "\nregisters:\n";
                                    unsigned i = 0;
                                    for (expr* r : m_registers) { if (r) { tout << i++ << ":\n" << mk_pp(r, m) << "\n"; } }
                                    tout << "quantifier:\n" << mk_pp(m_qa, m) << "\n";
                                    tout << "pattern:\n" << mk_pp(m_mp, m) << "\n";
                                });
                            SASSERT(m_todo.contains(reg));
                            if (flt->m_lbl_set.size() == 1)
                                set_check_mark(reg, CHECK_SINGLETON);
                            else
                                set_check_mark(reg, CHECK_SET);
                            m_compatible.push_back(curr);
                        }
                        else if (is_semi_compatible(flt)) {
                            unsigned reg = flt->m_reg;
                            TRACE("mam_compiler_detail", tout << "semi compatible " << reg << "\n";);
                            CTRACE("mam_compiler_bug", !m_todo.contains(reg), {
                                    for (unsigned t : m_todo) { tout << t << " "; }
                                    tout << "\nregisters:\n";
                                    unsigned i = 0;
                                    for (expr* r : m_registers) { if (r) { tout << i++ << ":\n" << mk_pp(r, m) << "\n"; } }
                                    tout << "quantifier:\n" << mk_pp(m_qa, m) << "\n";
                                    tout << "pattern:\n" << mk_pp(m_mp, m) << "\n";
                                });
                            SASSERT(m_todo.contains(reg));
                            unsigned  h  = get_pat_lbl_hash(reg);
                            TRACE("mam_lbl_bug",
                                  tout << "curr_set: " << flt->m_lbl_set << "\n";
                                  tout << "new hash: " << h << "\n";);
                            set_check_mark(reg, CHECK_SET);
                            approx_set const & s = flt->m_lbl_set;
                            if (s.size() > 1) {
                                m_ct_manager.insert_new_lbl_hash(flt, h);
                                m_compatible.push_back(curr);
                            }
                            else {
                                SASSERT(s.size() == 1);
                                approx_set new_s(s);
                                new_s.insert(h);
                                filter * new_instr = m_ct_manager.mk_filter(reg, new_s);
                                m_compatible.push_back(new_instr);
                                m_incompatible.push_back(curr);
                            }
                        }
                        else {
                            TRACE("mam_compiler_detail", tout << "incompatible\n";);
                            m_incompatible.push_back(curr);
                        }
                        break;
                    }
                    default:
                        TRACE("mam_compiler_detail", tout << "incompatible\n";);
                        m_incompatible.push_back(curr);
                        break;
                    }
                    last = curr;
                    curr = curr->m_next;
                }

                TRACE("mam_compiler", tout << *head << " " << head << "\n";
                      tout << "m_compatible.size(): " << m_compatible.size() << "\n";
                      tout << "m_incompatible.size(): " << m_incompatible.size() << "\n";);

                if (m_incompatible.empty()) {
                    // sequence starting at head is fully compatible
                    SASSERT(curr != 0);
                    SASSERT(curr->m_opcode == CHOOSE);
                    choose * first_child = static_cast<choose *>(curr);
                    choose * best_child = find_best_child(first_child);
                    TRACE("mam", tout << "best child " << best_child << "\n";);
                    if (best_child == nullptr) {
                        // There is no compatible child
                        // Suppose the sequence is:
                        //   head -> c1 -> ... -> (cn == last) -> first_child;
                        // Then we should add
                        //   head -> c1 -> ... -> (cn == last) -> new_child
                        //   new_child: CHOOSE(first_child) -> linearise
                        choose * new_child = m_ct_manager.mk_choose(first_child);
                        m_num_choices++;
                        set_next(last, new_child);
                        linearise(new_child, first_mp_idx);
                        // DONE
                        return;
                    }
                    else {
                        head = best_child;
                        // CONTINUE from best_child
                    }
                }
                else {
                    SASSERT(head->is_init() || !m_compatible.empty());
                    SASSERT(!m_incompatible.empty());
                    // Suppose the sequence is:
                    // head -> c1 -> i1 -> c2 -> c3 -> i2 -> first_child_head
                    //    where c_j are the compatible instructions, and i_j are the incompatible ones
                    // Then the sequence starting at head should become
                    // head -> c1 -> c2 -> c3 -> new_child_head1
                    // new_child_head1:CHOOSE(new_child_head2) -> i1 -> i2 -> first_child_head
                    // new_child_head2:NOOP -> linearise()
                    instruction * first_child_head = curr;
                    choose * new_child_head2 = m_ct_manager.mk_noop();
                    SASSERT(new_child_head2->m_alt == 0);
                    choose * new_child_head1 = m_ct_manager.mk_choose(new_child_head2);
                    m_num_choices++;
                    // set: head -> c1 -> c2 -> c3 -> new_child_head1
                    curr = head;
                    for (instruction* instr : m_compatible) {
                        set_next(curr, instr);
                        curr = instr;
                    }
                    set_next(curr, new_child_head1);
                    // set: new_child_head1:CHOOSE(new_child_head2) -> i1 -> i2 -> first_child_head
                    curr = new_child_head1;
                    for (instruction* inc : m_incompatible) {
                        if (curr == new_child_head1)
                            curr->m_next = inc; // new_child_head1 is a new node, I don't need to save trail
                        else
                            set_next(curr, inc);
                        curr = inc;
                    }
                    set_next(curr, first_child_head);
                    // build new_child_head2:NOOP -> linearise()
                    linearise(new_child_head2, first_mp_idx);
                    // DONE
                    return;
                }
            }
        }


    public:
        compiler(egraph & ctx, code_tree_manager & ct_mg, label_hasher & h, bool use_filters = true):
            m_egraph(ctx),
            m(ctx.get_manager()),
            m_ct_manager(ct_mg),
            m_lbl_hasher(h),
            m_use_filters(use_filters) {
        }

        /**
           \brief Create a new code tree for the given quantifier.

           - mp: is a pattern of qa that will be used to create the code tree

           - first_idx: index of mp that will be the "head" (first to be processed) of the multi-pattern.
        */
        code_tree * mk_tree(quantifier * qa, app * mp, unsigned first_idx, bool filter_candidates) {
            SASSERT(m.is_pattern(mp));
            app * p = to_app(mp->get_arg(first_idx));
            unsigned num_args = p->get_num_args();
            code_tree * r     = m_ct_manager.mk_code_tree(p->get_decl(), num_args, filter_candidates);
            init(r, qa, mp, first_idx);
            linearise(r->m_root, first_idx);
            r->m_num_choices  = m_num_choices;
            TRACE("mam_compiler", tout << "new tree for:\n" << mk_pp(mp, m) << "\n" << *r;);
            return r;
        }

        /**
           \brief Insert a pattern into the code tree.

           - is_tmp_tree: trail for update operations is created if is_tmp_tree = false.
        */
        void insert(code_tree * tree, quantifier * qa, app * mp, unsigned first_idx, bool is_tmp_tree) {
            if (tree->expected_num_args() != to_app(mp->get_arg(first_idx))->get_num_args()) {
                // We have to check the number of arguments because of nary + and * operators.
                // The E-matching engine that was built when all + and * applications were binary.
                // We ignore the pattern if it does not have the expected number of arguments.
                // This is not the ideal solution, but it avoids possible crashes.
                return;
            }
            m_is_tmp_tree = is_tmp_tree;
            TRACE("mam_compiler", tout << "updating tree with:\n" << mk_pp(mp, m) << "\n";);
            TRACE("mam_bug", tout << "before insertion\n" << *tree << "\n";);
            if (!is_tmp_tree)
                m_ct_manager.save_num_regs(tree);
            init(tree, qa, mp, first_idx);
            m_num_choices = tree->m_num_choices;
            insert(tree->m_root, first_idx);
            TRACE("mam_bug",
                  tout << "m_num_choices: " << m_num_choices << "\n";);
            if (m_num_choices > tree->m_num_choices) {
                if (!is_tmp_tree)
                    m_ct_manager.save_num_choices(tree);
                tree->m_num_choices = m_num_choices;
            }
            TRACE("mam_bug",
                  tout << "m_num_choices: " << m_num_choices << "\n";
                  tout << "new tree:\n" << *tree;
                  tout << "todo ";
                  for (auto t : m_todo) tout << t << " ";
                  tout << "\n";);
        }
    };

#if 0
    bool check_lbls(enode * n) {
        approx_set  lbls;
        approx_set plbls;
        enode * first = n;
        do {
            lbls  |= n->get_lbls();
            plbls |= n->get_plbls();
            n = n->get_next();
        }
        while (first != n);
        SASSERT(n->get_root()->get_lbls()  == lbls);
        SASSERT(n->get_root()->get_plbls() == plbls);
        return true;
    }
#endif

    // ------------------------------------
    //
    // Code Tree Interpreter
    //
    // ------------------------------------

    struct backtrack_point {
        const instruction *  m_instr;
        unsigned             m_old_max_generation;
        union {
            enode *  m_curr;
            struct {
                enode_vector *  m_to_recycle;
                enode * const * m_it;
                enode * const * m_end;
            };
        };
    };

    typedef svector<backtrack_point> backtrack_stack;

    class interpreter {
        euf::solver&        ctx;
        ast_manager &       m;
        mam &               m_mam;
        bool                m_use_filters;
        enode_vector        m_registers;
        enode_vector        m_bindings;
        enode_vector        m_args;
        backtrack_stack     m_backtrack_stack;
        unsigned            m_top;
        const instruction * m_pc;

        // auxiliary temporary variables
        unsigned            m_max_generation;  // the maximum generation of an app enode processed.
        unsigned            m_curr_max_generation;  // temporary var used to store a copy of m_max_generation
        unsigned            m_num_args;
        unsigned            m_oreg;
        enode *             m_n1;
        enode *             m_n2;
        enode *             m_app;
        const bind *        m_b;

        // equalities used for pattern match. The first element of the tuple gives the argument (or null) of some term that was matched against some higher level
        // structure of the trigger, the second element gives the term that argument is replaced with in order to match the trigger. Used for logging purposes only.
        ptr_vector<enode>   m_pattern_instances; // collect the pattern instances... used for computing min_top_generation and max_top_generation
        unsigned_vector     m_min_top_generation, m_max_top_generation;

        pool<enode_vector>  m_pool;

        enode_vector * mk_enode_vector() {
            enode_vector * r = m_pool.mk();
            r->reset();
            return r;
        }

        void recycle_enode_vector(enode_vector * v) {
            if (v)
                m_pool.recycle(v);
        }

        void update_max_generation(enode * n, enode * prev) {
            m_max_generation = std::max(m_max_generation, n->generation());
        }

        // We have to provide the number of expected arguments because we have flat-assoc applications such as +.
        // Flat-assoc applications may have arbitrary number of arguments.
        enode * get_first_f_app(func_decl * lbl, unsigned num_expected_args, enode * first) {
            for (enode* curr : euf::enode_class(first)) {
                if (curr->get_decl() == lbl && curr->is_cgr() && curr->num_args() == num_expected_args) {
                    update_max_generation(curr, first);
                    return curr;
                }
            }
            return nullptr;
        }

        enode * get_next_f_app(func_decl * lbl, unsigned num_expected_args, enode * first, enode * curr) {
            curr = curr->get_next();
            while (curr != first) {
                if (curr->get_decl() == lbl && curr->is_cgr() && curr->num_args() == num_expected_args) {
                    update_max_generation(curr, first);
                    return curr;
                }
                curr = curr->get_next();
            }
            return nullptr;
        }

        /**
           \brief Execute the is_cgr instruction.
           Return true if succeeded, and false if backtracking is needed.
        */
        bool exec_is_cgr(is_cgr const * pc) {
            unsigned num_args = pc->m_num_args;
            enode * r         = m_registers[pc->m_ireg];
            func_decl * f     = pc->m_label;
            switch (num_args) {
            case 1:
                m_args[0] = m_registers[pc->m_iregs[0]]->get_root();
                for (enode* n : euf::enode_class(r)) {
                    if (n->get_decl() == f &&
                        n->get_arg(0)->get_root() == m_args[0]) {
                        update_max_generation(n, r);
                        return true;
                    }
                }
                return false;
            case 2:
                m_args[0] = m_registers[pc->m_iregs[0]]->get_root();
                m_args[1] = m_registers[pc->m_iregs[1]]->get_root();
                for (enode* n : euf::enode_class(r)) {
                    if (n->get_decl() == f &&
                        n->get_arg(0)->get_root() == m_args[0] &&
                        n->get_arg(1)->get_root() == m_args[1]) {
                        update_max_generation(n, r);
                        return true;
                    }
                }
                return false;
            default: {
                m_args.reserve(num_args+1, 0);
                for (unsigned i = 0; i < num_args; i++)
                    m_args[i] = m_registers[pc->m_iregs[i]]->get_root();
                for (enode* n : euf::enode_class(r)) {
                    if (n->get_decl() == f && num_args == n->num_args()) {
                        unsigned i = 0;
                        for (; i < num_args; i++) {
                            if (n->get_arg(i)->get_root() != m_args[i])
                                break;
                        }
                        if (i == num_args) {
                            update_max_generation(n, r);
                            return true;
                        }
                    }
                }
                return false;
            } }
        }

        enode_vector * mk_depth1_vector(enode * n, func_decl * f, unsigned i);

        enode_vector * mk_depth2_vector(joint2 * j2, func_decl * f, unsigned i);

        enode * init_continue(cont const * c, unsigned expected_num_args);

        void display_reg(std::ostream & out, unsigned reg);

        void display_instr_input_reg(std::ostream & out, instruction const * instr);

        void display_pc_info(std::ostream & out);

#define INIT_ARGS_SIZE 16

    public:
        interpreter(euf::solver& ctx, mam & ma, bool use_filters):
            ctx(ctx),
            m(ctx.get_manager()),
            m_mam(ma),
            m_use_filters(use_filters) {
            m_args.resize(INIT_ARGS_SIZE);
        }

        ~interpreter() {
        }

        void init(code_tree * t) {
            TRACE("mam_bug", tout << "preparing to match tree:\n" << *t << "\n";);
            m_registers.reserve(t->get_num_regs(), nullptr);
            m_bindings.reserve(t->get_num_regs(),  nullptr);
            if (m_backtrack_stack.size() < t->get_num_choices())
                m_backtrack_stack.resize(t->get_num_choices());
        }


        void execute(code_tree * t) {
            if (!t->has_candidates())
                return;
            TRACE("trigger_bug", tout << "execute for code tree:\n"; t->display(tout););
            init(t);
            t->save_qhead(ctx);
            enode* app;
            if (t->filter_candidates()) {                
                code_tree::scoped_unmark _unmark(t);
                while ((app = t->next_candidate()) && !ctx.resource_limits_exceeded()) {
                    TRACE("trigger_bug", tout << "candidate\n" << ctx.bpp(app) << "\n";);
                    if (!app->is_marked3() && app->is_cgr()) {
                        execute_core(t, app);                       
                        app->mark3();
                    }
                }
            }
            else {
                while ((app = t->next_candidate()) && !ctx.resource_limits_exceeded()) {
                    TRACE("trigger_bug", tout << "candidate\n" << ctx.bpp(app) << "\n";);
                    if (app->is_cgr()) 
                        execute_core(t, app);                                              
                }
            }
        }

        // init(t) must be invoked before execute_core
        bool execute_core(code_tree * t, enode * n);

        // Return the min, max generation of the enodes in m_pattern_instances.

        void get_min_max_top_generation(unsigned& min, unsigned& max) {
            SASSERT(!m_pattern_instances.empty());
            if (m_min_top_generation.empty()) {
                min = max = m_pattern_instances[0]->generation();
                m_min_top_generation.push_back(min);
                m_max_top_generation.push_back(max);
            }
            else {
                min = m_min_top_generation.back();
                max = m_max_top_generation.back();
            }
            for (unsigned i = m_min_top_generation.size(); i < m_pattern_instances.size(); ++i) {
                unsigned curr = m_pattern_instances[i]->generation();
                min = std::min(min, curr);
                m_min_top_generation.push_back(min);
                max = std::max(max, curr);
                m_max_top_generation.push_back(max);
            }
        }
    };

    /**
       \brief Return a vector with the relevant f-parents of n such that n is the i-th argument.
    */
    enode_vector * interpreter::mk_depth1_vector(enode * n, func_decl * f, unsigned i) {
        enode_vector * v = mk_enode_vector();
        n = n->get_root();
        for (enode* p : euf::enode_parents(n)) {
            if (p->get_decl() == f  && 
                i < p->num_args() && 
                ctx.is_relevant(p)  &&
                p->is_cgr() &&
                p->get_arg(i)->get_root() == n) 
                v->push_back(p);
        }
        return v;
    }

    /**
       \brief Return a vector with the relevant f-parents of each p in joint2 where n is the i-th argument.
       We say a p is in joint2 if p is the g-parent of m_registers[j2->m_reg] where g is j2->m_decl,
       and m_registers[j2->m_reg] is the argument j2->m_arg_pos.
    */
    enode_vector * interpreter::mk_depth2_vector(joint2 * j2, func_decl * f, unsigned i) {
        enode * n = m_registers[j2->m_reg]->get_root();
        if (n->num_parents() == 0)
            return nullptr;
        enode_vector * v  = mk_enode_vector();
        for (enode* p : euf::enode_parents(n)) {
            if (p->get_decl() == j2->m_decl &&
                ctx.is_relevant(p) &&
                p->num_args() > j2->m_arg_pos && 
                p->is_cgr() &&
                p->get_arg(j2->m_arg_pos)->get_root() == n) {
                // p is in joint2
                p = p->get_root();
                for (enode* p2 : euf::enode_parents(p)) {
                    if (p2->get_decl() == f &&
                        ctx.is_relevant(p2) &&
                        p2->is_cgr() &&
                        i < p2->num_args() && 
                        p2->get_arg(i)->get_root() == p) {
                        v->push_back(p2);
                    }
                }
            }
        }
        return v;
    }

    enode * interpreter::init_continue(cont const * c, unsigned expected_num_args) {
        func_decl * lbl         = c->m_label;
        unsigned min_sz         = ctx.get_egraph().enodes_of(lbl).size();
        unsigned short num_args = c->m_num_args;
        enode * r;
        // quick filter... check if any of the joint points have zero parents...
        for (unsigned i = 0; i < num_args; i++) {
            void * bare = c->m_joints[i];
            enode * n   = nullptr;
            switch (GET_TAG(bare)) {
            case NULL_TAG:
                goto non_depth1;
            case GROUND_TERM_TAG:
                n = UNTAG(enode *, bare);
                break;
            case VAR_TAG:
                n = m_registers[UNBOXINT(bare)];
                break;
            case NESTED_VAR_TAG:
                goto non_depth1;
            }
            r = n->get_root();
            if (m_use_filters && r->get_plbls().empty_intersection(c->m_lbl_set))
                return nullptr;
            if (r->num_parents() == 0)
                return nullptr;
        non_depth1:
            ;
        }
        // traverse each joint and select the best one.
        enode_vector * best_v   = nullptr;
        for (unsigned i = 0; i < num_args; i++) {
            enode * bare          = c->m_joints[i];
            enode_vector * curr_v = nullptr;
            switch (GET_TAG(bare)) {
            case NULL_TAG:
                curr_v = nullptr;
                break;
            case GROUND_TERM_TAG:
                curr_v = mk_depth1_vector(UNTAG(enode *, bare), lbl, i);
                break;
            case VAR_TAG:
                curr_v = mk_depth1_vector(m_registers[UNBOXINT(bare)], lbl, i);
                break;
            case NESTED_VAR_TAG:
                curr_v = mk_depth2_vector(UNTAG(joint2 *, bare), lbl, i);
                break;
            }
            if (curr_v != nullptr) {
                if (curr_v->size() < min_sz && (best_v == nullptr || curr_v->size() < best_v->size())) {
                    if (best_v)
                        recycle_enode_vector(best_v);
                    best_v  = curr_v;
                    if (best_v->empty()) {
                        recycle_enode_vector(best_v);
                        return nullptr;
                    }
                }
                else {
                    recycle_enode_vector(curr_v);
                }
            }
        }
        backtrack_point & bp = m_backtrack_stack[m_top];
        bp.m_instr                = c;
        bp.m_old_max_generation   = m_max_generation;
        if (best_v == nullptr) {
            TRACE("mam_bug", tout << "m_top: " << m_top << ", m_backtrack_stack.size(): " << m_backtrack_stack.size() << "\n";
                  tout << *c << "\n";);
            bp.m_to_recycle           = nullptr;
            bp.m_it                   = ctx.get_egraph().enodes_of(lbl).begin();
            bp.m_end                  = ctx.get_egraph().enodes_of(lbl).end();
        }
        else {
            SASSERT(!best_v->empty());
            bp.m_to_recycle           = best_v;
            bp.m_it                   = best_v->begin();
            bp.m_end                  = best_v->end();
        }
        // find application with the right number of arguments
        for (; bp.m_it != bp.m_end; ++bp.m_it) {
            enode * curr = *bp.m_it;
            if (curr->num_args() == expected_num_args && ctx.is_relevant(curr))
                break;
        }
        if (bp.m_it == bp.m_end) {
            recycle_enode_vector(bp.m_to_recycle);
            return nullptr;
        }
        m_top++;
        update_max_generation(*(bp.m_it), nullptr);
        return *(bp.m_it);
    }

    void interpreter::display_reg(std::ostream & out, unsigned reg) {
        out << "reg[" << reg << "]: ";
        enode * n = m_registers[reg];
        if (!n) {
            out << "nil\n";
        }
        else {
            out << "#" << n->get_expr_id() << ", root: " << n->get_root()->get_expr_id();
            if (m_use_filters)
                out << ", lbls: " << n->get_root()->get_lbls() << " ";
            out << "\n";
            out << mk_pp(n->get_expr(), m) << "\n";
        }
    }

    void interpreter::display_instr_input_reg(std::ostream & out, const instruction * instr) {
        switch (instr->m_opcode) {
        case INIT1: case INIT2: case INIT3: case INIT4: case INIT5: case INIT6: case INITN:
            display_reg(out, 0);
            break;
        case BIND1: case BIND2: case BIND3: case BIND4: case BIND5: case BIND6: case BINDN:
            display_reg(out, static_cast<const bind *>(instr)->m_ireg);
            break;
        case COMPARE:
            display_reg(out, static_cast<const compare *>(instr)->m_reg1);
            display_reg(out, static_cast<const compare *>(instr)->m_reg2);
            break;
        case CHECK:
            display_reg(out, static_cast<const check *>(instr)->m_reg);
            break;
        case FILTER:
            display_reg(out, static_cast<const filter *>(instr)->m_reg);
            break;
        case YIELD1: case YIELD2: case YIELD3: case YIELD4: case YIELD5: case YIELD6: case YIELDN:
            for (unsigned i = 0; i < static_cast<const yield *>(instr)->m_num_bindings; i++) {
                display_reg(out, static_cast<const yield *>(instr)->m_bindings[i]);
            }
            break;
        default:
            break;
        }
    }

    void interpreter::display_pc_info(std::ostream & out) {
        out << "executing: " << *m_pc << "\n";
        out << "m_pc: " << m_pc << ", next: " << m_pc->m_next;
        if (m_pc->m_opcode == CHOOSE)
            out << ", alt: " << static_cast<const choose *>(m_pc)->m_alt;
        out << "\n";
        display_instr_input_reg(out, m_pc);
    }

    bool interpreter::execute_core(code_tree * t, enode * n) {
        TRACE("trigger_bug", tout << "interpreter::execute_core\n"; t->display(tout); tout << "\nenode\n" << mk_ismt2_pp(n->get_expr(), m) << "\n";);
        unsigned since_last_check = 0;

#ifdef _PROFILE_MAM
#ifdef _PROFILE_MAM_EXPENSIVE
        if (t->get_watch().get_seconds() > _PROFILE_MAM_THRESHOLD && t->get_counter() % _PROFILE_MAM_EXPENSIVE_FREQ == 0) {
            std::cout << "EXPENSIVE\n";
            t->display(std::cout);
        }
#endif
        t->get_watch().start();
        t->inc_counter();
#endif
        // It doesn't make sense to process an irrelevant enode.
        TRACE("mam_execute_core", tout << "EXEC " << t->get_root_lbl()->get_name() << "\n";);
        if (!ctx.is_relevant(n))
            return false;
        SASSERT(ctx.is_relevant(n));
        m_pattern_instances.reset();
        m_min_top_generation.reset();
        m_max_top_generation.reset();
        m_pattern_instances.push_back(n);
        m_max_generation = n->generation();

        m_pc             = t->get_root();
        m_registers[0]   = n;
        m_top            = 0;


    main_loop:

        TRACE("mam_int", display_pc_info(tout););
#ifdef _PROFILE_MAM
        const_cast<instruction*>(m_pc)->m_counter++;
#endif
        switch (m_pc->m_opcode) {
        case INIT1:
            m_app          = m_registers[0];
            if (m_app->num_args() != 1)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INIT2:
            m_app          = m_registers[0];
            if (m_app->num_args() != 2)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_registers[2] = m_app->get_arg(1);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INIT3:
            m_app          = m_registers[0];
            if (m_app->num_args() != 3)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_registers[2] = m_app->get_arg(1);
            m_registers[3] = m_app->get_arg(2);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INIT4:
            m_app          = m_registers[0];
            if (m_app->num_args() != 4)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_registers[2] = m_app->get_arg(1);
            m_registers[3] = m_app->get_arg(2);
            m_registers[4] = m_app->get_arg(3);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INIT5:
            m_app          = m_registers[0];
            if (m_app->num_args() != 5)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_registers[2] = m_app->get_arg(1);
            m_registers[3] = m_app->get_arg(2);
            m_registers[4] = m_app->get_arg(3);
            m_registers[5] = m_app->get_arg(4);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INIT6:
            m_app          = m_registers[0];
            if (m_app->num_args() != 6)
                goto backtrack;
            m_registers[1] = m_app->get_arg(0);
            m_registers[2] = m_app->get_arg(1);
            m_registers[3] = m_app->get_arg(2);
            m_registers[4] = m_app->get_arg(3);
            m_registers[5] = m_app->get_arg(4);
            m_registers[6] = m_app->get_arg(5);
            m_pc = m_pc->m_next;
            goto main_loop;

        case INITN:
            m_app      = m_registers[0];
            m_num_args = m_app->num_args();
            if (m_num_args != static_cast<const initn *>(m_pc)->m_num_args)
                goto backtrack;
            for (unsigned i = 0; i < m_num_args; i++)
                m_registers[i+1] = m_app->get_arg(i);
            m_pc = m_pc->m_next;
            goto main_loop;

        case COMPARE:
            m_n1 = m_registers[static_cast<const compare *>(m_pc)->m_reg1];
            m_n2 = m_registers[static_cast<const compare *>(m_pc)->m_reg2];
            SASSERT(m_n1 != 0);
            SASSERT(m_n2 != 0);
            if (m_n1->get_root() != m_n2->get_root())
                goto backtrack;
            
            m_pc = m_pc->m_next;
            goto main_loop;

        case CHECK:
            m_n1 = m_registers[static_cast<const check *>(m_pc)->m_reg];
            m_n2 = static_cast<const check *>(m_pc)->m_enode;
            SASSERT(m_n1 != 0);
            SASSERT(m_n2 != 0);
            if (m_n1->get_root() != m_n2->get_root())
                goto backtrack;

            m_pc = m_pc->m_next;
            goto main_loop;

            /* CFILTER AND FILTER are handled differently by the compiler
               The compiler will never merge two CFILTERs with different m_lbl_set fields.
               Essentially, CFILTER is used to combine CHECK statements, and FILTER for BIND
            */
        case CFILTER:
        case FILTER:
            m_n1 = m_registers[static_cast<const filter *>(m_pc)->m_reg]->get_root();
            if (static_cast<const filter *>(m_pc)->m_lbl_set.empty_intersection(m_n1->get_lbls()))
                goto backtrack;
            m_pc = m_pc->m_next;
            goto main_loop;

        case PFILTER:
            m_n1 = m_registers[static_cast<const filter *>(m_pc)->m_reg]->get_root();
            if (static_cast<const filter *>(m_pc)->m_lbl_set.empty_intersection(m_n1->get_plbls()))
                goto backtrack;
            m_pc = m_pc->m_next;
            goto main_loop;

        case CHOOSE:
            m_backtrack_stack[m_top].m_instr                = m_pc;
            m_backtrack_stack[m_top].m_old_max_generation   = m_max_generation;
            m_top++;
            m_pc = m_pc->m_next;
            goto main_loop;
        case NOOP:
            SASSERT(static_cast<const choose *>(m_pc)->m_alt == 0);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND1:
#define BIND_COMMON()                                                                                                   \
                 m_n1   = m_registers[static_cast<const bind *>(m_pc)->m_ireg];                                         \
                 SASSERT(m_n1 != 0);                                                                                    \
                 m_oreg = static_cast<const bind *>(m_pc)->m_oreg;                                                      \
                 m_curr_max_generation = m_max_generation;                                                              \
                 m_app  = get_first_f_app(static_cast<const bind *>(m_pc)->m_label, static_cast<const bind *>(m_pc)->m_num_args, m_n1); \
                 if (!m_app)                                                                                            \
                     goto backtrack;                                                                                    \
                 TRACE("mam_int", tout << "bind candidate: " << mk_pp(m_app->get_expr(), m) << "\n";);     \
                 m_backtrack_stack[m_top].m_instr              = m_pc;                                                  \
                 m_backtrack_stack[m_top].m_old_max_generation = m_curr_max_generation;                                 \
                 m_backtrack_stack[m_top].m_curr               = m_app;                                                 \
                 m_top++;

            BIND_COMMON();
            m_registers[m_oreg] = m_app->get_arg(0);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND2:
            BIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND3:
            BIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND4:
            BIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND5:
            BIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_registers[m_oreg+4] = m_app->get_arg(4);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BIND6:
            BIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_registers[m_oreg+4] = m_app->get_arg(4);
            m_registers[m_oreg+5] = m_app->get_arg(5);
            m_pc = m_pc->m_next;
            goto main_loop;

        case BINDN:
            BIND_COMMON();
            m_num_args = static_cast<const bind *>(m_pc)->m_num_args;
            for (unsigned i = 0; i < m_num_args; i++)
                m_registers[m_oreg+i] = m_app->get_arg(i);
            m_pc = m_pc->m_next;
            goto main_loop;

        case YIELD1:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
#define ON_MATCH(NUM)                                                                                   \
            m_max_generation = std::max(m_max_generation, get_max_generation(NUM, m_bindings.begin())); \
            if (!m.inc())                                                                               \
                return false;                                                                           \
                                                                                                        \
            m_mam.on_match(static_cast<const yield *>(m_pc)->m_qa,                                      \
                           static_cast<const yield *>(m_pc)->m_pat,                                     \
                           NUM,                                                                         \
                           m_bindings.begin(),                                                          \
                           m_max_generation)

            SASSERT(static_cast<const yield *>(m_pc)->m_qa->get_decl_sort(0) == m_bindings[0]->get_expr()->get_sort());
            ON_MATCH(1);
            goto backtrack;

        case YIELD2:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[1]];
            m_bindings[1] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
            ON_MATCH(2);
            goto backtrack;

        case YIELD3:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[2]];
            m_bindings[1] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[1]];
            m_bindings[2] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
            ON_MATCH(3);
            goto backtrack;

        case YIELD4:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[3]];
            m_bindings[1] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[2]];
            m_bindings[2] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[1]];
            m_bindings[3] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
            ON_MATCH(4);
            goto backtrack;

        case YIELD5:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[4]];
            m_bindings[1] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[3]];
            m_bindings[2] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[2]];
            m_bindings[3] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[1]];
            m_bindings[4] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
            ON_MATCH(5);
            goto backtrack;

        case YIELD6:
            m_bindings[0] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[5]];
            m_bindings[1] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[4]];
            m_bindings[2] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[3]];
            m_bindings[3] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[2]];
            m_bindings[4] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[1]];
            m_bindings[5] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[0]];
            ON_MATCH(6);
            goto backtrack;

        case YIELDN:
            m_num_args = static_cast<const yield *>(m_pc)->m_num_bindings;
            for (unsigned i = 0; i < m_num_args; i++)
                m_bindings[i] = m_registers[static_cast<const yield *>(m_pc)->m_bindings[m_num_args - i - 1]];
            ON_MATCH(m_num_args);
            goto backtrack;

        case GET_ENODE:
            m_registers[static_cast<const get_enode_instr *>(m_pc)->m_oreg] = static_cast<const get_enode_instr *>(m_pc)->m_enode;
            m_pc = m_pc->m_next;
            goto main_loop;

        case GET_CGR1:

#define SET_VAR(IDX)                                                                                                                         \
            m_args[IDX] = m_registers[static_cast<const get_cgr *>(m_pc)->m_iregs[IDX]];                                                     \
            if (m_use_filters && static_cast<const get_cgr *>(m_pc)->m_lbl_set.empty_intersection(m_args[IDX]->get_root()->get_plbls())) {   \
                goto backtrack;                                                                                                              \
            }

            SET_VAR(0);
            goto cgr_common;

        case GET_CGR2:
            SET_VAR(0);
            SET_VAR(1);
            goto cgr_common;

        case GET_CGR3:
            SET_VAR(0);
            SET_VAR(1);
            SET_VAR(2);
            goto cgr_common;

        case GET_CGR4:
            SET_VAR(0);
            SET_VAR(1);
            SET_VAR(2);
            SET_VAR(3);
            goto cgr_common;

        case GET_CGR5:
            SET_VAR(0);
            SET_VAR(1);
            SET_VAR(2);
            SET_VAR(3);
            SET_VAR(4);
            goto cgr_common;

        case GET_CGR6:
            SET_VAR(0);
            SET_VAR(1);
            SET_VAR(2);
            SET_VAR(3);
            SET_VAR(4);
            SET_VAR(5);
            goto cgr_common;

        case GET_CGRN:
            m_num_args = static_cast<const get_cgr *>(m_pc)->m_num_args;
            m_args.reserve(m_num_args, 0);
            for (unsigned i = 0; i < m_num_args; i++)
                m_args[i] = m_registers[static_cast<const get_cgr *>(m_pc)->m_iregs[i]];
            goto cgr_common;

        case IS_CGR:
            if (!exec_is_cgr(static_cast<const is_cgr *>(m_pc)))
                goto backtrack;
            m_pc = m_pc->m_next;
            goto main_loop;

        case CONTINUE:
            m_num_args = static_cast<const cont *>(m_pc)->m_num_args;
            m_oreg     = static_cast<const cont *>(m_pc)->m_oreg;
            m_app = init_continue(static_cast<const cont *>(m_pc), m_num_args);
            if (m_app == nullptr)
                goto backtrack;
            m_pattern_instances.push_back(m_app);
            TRACE("mam_int", tout << "continue candidate:\n" << mk_ll_pp(m_app->get_expr(), m););
            for (unsigned i = 0; i < m_num_args; i++)
                m_registers[m_oreg+i] = m_app->get_arg(i);
            m_pc = m_pc->m_next;
            goto main_loop;
        }

        goto backtrack;

    cgr_common:
        m_n1 = ctx.get_egraph().get_enode_eq_to(static_cast<const get_cgr *>(m_pc)->m_label, static_cast<const get_cgr *>(m_pc)->m_num_args, m_args.data()); 
        if (!m_n1 || !ctx.is_relevant(m_n1))                                                                                                              
            goto backtrack;                                                                                                                                    
        update_max_generation(m_n1, nullptr);                                                                                                                  
        m_registers[static_cast<const get_cgr *>(m_pc)->m_oreg] = m_n1;                                                                                        
        m_pc = m_pc->m_next;                                                                                                                                   
        goto main_loop;

    backtrack:
        TRACE("mam_int", tout << "backtracking.\n";);
        if (m_top == 0) {
            TRACE("mam_int", tout << "no more alternatives.\n";);
#ifdef _PROFILE_MAM
            t->get_watch().stop();
#endif
            return true; // no more alternatives
        }
        backtrack_point & bp = m_backtrack_stack[m_top - 1];
        m_max_generation     = bp.m_old_max_generation;


        TRACE("mam_int", tout << "backtrack top: " << bp.m_instr << " " << *(bp.m_instr) << "\n";);
#ifdef _PROFILE_MAM
        if (bp.m_instr->m_opcode != CHOOSE) // CHOOSE has a different status. It is a control flow backtracking.
            const_cast<instruction*>(bp.m_instr)->m_counter++;
#endif

        if (since_last_check++ > 100) {
            since_last_check = 0;
            if (ctx.resource_limits_exceeded()) {
                // Soft timeout...
                // Cleanup before exiting
                while (m_top != 0) {
                    backtrack_point & bp = m_backtrack_stack[m_top - 1];
                    if (bp.m_instr->m_opcode == CONTINUE && bp.m_to_recycle)
                        recycle_enode_vector(bp.m_to_recycle);
                    m_top--;
                }
#ifdef _PROFILE_MAM
               t->get_watch().stop();
#endif
                return false;
            }
        }

        switch (bp.m_instr->m_opcode) {
        case CHOOSE:
            m_pc = static_cast<const choose*>(bp.m_instr)->m_alt;
            TRACE("mam_int", tout << "alt: " << m_pc << "\n";);
            SASSERT(m_pc != 0);
            m_top--;
            goto main_loop;
        case BIND1:
#define BBIND_COMMON() m_b   = static_cast<const bind*>(bp.m_instr);                                                            \
                       m_n1  = m_registers[m_b->m_ireg];                                                                        \
                       m_app = get_next_f_app(m_b->m_label, m_b->m_num_args, m_n1, bp.m_curr); \
                       if (m_app == 0) {                                                                                        \
                           m_top--;                                                                                             \
                           goto backtrack;                                                                                      \
                       }                                                                                                        \
                       bp.m_curr = m_app;                                                                                       \
                       TRACE("mam_int", tout << "bind next candidate:\n" << mk_ll_pp(m_app->get_expr(), m););      \
                       m_oreg    = m_b->m_oreg

            BBIND_COMMON();
            m_registers[m_oreg] = m_app->get_arg(0);
            m_pc = m_b->m_next;
            goto main_loop;

        case BIND2:
            BBIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_pc = m_b->m_next;
                goto main_loop;

        case BIND3:
            BBIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_pc = m_b->m_next;
            goto main_loop;

        case BIND4:
            BBIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_pc = m_b->m_next;
            goto main_loop;

        case BIND5:
            BBIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_registers[m_oreg+4] = m_app->get_arg(4);
            m_pc = m_b->m_next;
            goto main_loop;

        case BIND6:
            BBIND_COMMON();
            m_registers[m_oreg]   = m_app->get_arg(0);
            m_registers[m_oreg+1] = m_app->get_arg(1);
            m_registers[m_oreg+2] = m_app->get_arg(2);
            m_registers[m_oreg+3] = m_app->get_arg(3);
            m_registers[m_oreg+4] = m_app->get_arg(4);
            m_registers[m_oreg+5] = m_app->get_arg(5);
            m_pc = m_b->m_next;
            goto main_loop;

        case BINDN:
            BBIND_COMMON();
            m_num_args = m_b->m_num_args;
            for (unsigned i = 0; i < m_num_args; i++)
                m_registers[m_oreg+i] = m_app->get_arg(i);
            m_pc = m_b->m_next;
            goto main_loop;

        case CONTINUE:
            ++bp.m_it;
            for (; bp.m_it != bp.m_end; ++bp.m_it) {
                m_app = *bp.m_it;
                const cont * c = static_cast<const cont*>(bp.m_instr);
                // bp.m_it may reference an enode in [begin_enodes_of(lbl), end_enodes_of(lbl))
                // This enodes are not necessarily relevant.
                // So, we must check whether ctx.is_relevant(m_app) is true or not.
                if (m_app->num_args() == c->m_num_args && ctx.is_relevant(m_app)) {
                    // update the pattern instance
                    SASSERT(!m_pattern_instances.empty());
                    if (m_pattern_instances.size() == m_max_top_generation.size()) {
                        m_max_top_generation.pop_back();
                        m_min_top_generation.pop_back();
                    }
                    m_pattern_instances.pop_back();
                    m_pattern_instances.push_back(m_app);
                    // continue succeeded
                    update_max_generation(m_app, nullptr); // null indicates a top-level match
                    TRACE("mam_int", tout << "continue next candidate:\n" << mk_ll_pp(m_app->get_expr(), m););
                    m_num_args = c->m_num_args;
                    m_oreg     = c->m_oreg;
                    for (unsigned i = 0; i < m_num_args; i++)
                        m_registers[m_oreg+i] = m_app->get_arg(i);
                    m_pc = c->m_next;
                    goto main_loop;
                }
            }
            // continue failed
            if (bp.m_to_recycle)
                recycle_enode_vector(bp.m_to_recycle);
            m_top--;
            goto backtrack;

        default:
            UNREACHABLE();
        }
        return false;
    } // end of execute_core

#if 0
    void display_trees(std::ostream & out, const ptr_vector<code_tree> & trees) {
        unsigned lbl = 0;
        for (code_tree * tree : trees) {
            if (tree) {
                out << "tree for f" << lbl << "\n";
                out << *tree;
            }
            ++lbl;
        }
    }
#endif

    // ------------------------------------
    //
    // A mapping from func_label -> code tree.
    //
    // ------------------------------------
    class code_tree_map {
        ast_manager &               m;
        compiler &                  m_compiler;
        ptr_vector<code_tree>       m_trees;       // mapping: func_label -> tree
        euf::solver&                ctx;
#ifdef Z3DEBUG
        egraph *                   m_egraph;
#endif

        class mk_tree_trail : public trail {
            ptr_vector<code_tree> & m_trees;
            unsigned                m_lbl_id;
        public:
            mk_tree_trail(ptr_vector<code_tree> & t, unsigned id):m_trees(t), m_lbl_id(id) {}
            void undo() override {
                dealloc(m_trees[m_lbl_id]);
                m_trees[m_lbl_id] = nullptr;
            }
        };

    public:
        code_tree_map(ast_manager & m, compiler & c, euf::solver& ctx):
            m(m),
            m_compiler(c),
            ctx(ctx) {
        }

#ifdef Z3DEBUG
        void set_egraph(egraph* c) { m_egraph = c; }
    
#endif

        ~code_tree_map() {
            std::for_each(m_trees.begin(), m_trees.end(), delete_proc<code_tree>());
        }

        /**
           \brief Add a pattern to the code tree map.

           - mp: is used a pattern for qa.

           - first_idx: index to be used as head of the multi-pattern mp
        */
        void add_pattern(quantifier * qa, app * mp, unsigned first_idx) {
            (void)m;
            SASSERT(m.is_pattern(mp));
            SASSERT(first_idx < mp->get_num_args());
            app * p           = to_app(mp->get_arg(first_idx));
            func_decl * lbl   = p->get_decl();
            unsigned lbl_id   = lbl->get_small_id();
            m_trees.reserve(lbl_id+1, nullptr);
            if (m_trees[lbl_id] == nullptr) {
                m_trees[lbl_id] = m_compiler.mk_tree(qa, mp, first_idx, false);
                SASSERT(m_trees[lbl_id]->expected_num_args() == p->get_num_args());
                DEBUG_CODE(m_trees[lbl_id]->set_egraph(m_egraph););
                ctx.push(mk_tree_trail(m_trees, lbl_id));
            }
            else {
                code_tree * tree = m_trees[lbl_id];
                // We have to check the number of arguments because of nary + and * operators.
                // The E-matching engine that was built when all + and * applications were binary.
                // We ignore the pattern if it does not have the expected number of arguments.
                // This is not the ideal solution, but it avoids possible crashes.
                if (tree->expected_num_args() == p->get_num_args()) 
                    m_compiler.insert(tree, qa, mp, first_idx, false);
            }
            DEBUG_CODE(if (first_idx == 0) {
                m_trees[lbl_id]->get_patterns().push_back(std::make_pair(qa, mp));
                ctx.push(push_back_trail<std::pair<quantifier*, app*>, false>(m_trees[lbl_id]->get_patterns()));
            });
            TRACE("trigger_bug", tout << "after add_pattern, first_idx: " << first_idx << "\n"; m_trees[lbl_id]->display(tout););
        }

        void reset() {
            std::for_each(m_trees.begin(), m_trees.end(), delete_proc<code_tree>());
            m_trees.reset();
        }

        code_tree * get_code_tree_for(func_decl * lbl) const {
            unsigned lbl_id = lbl->get_small_id();
            if (lbl_id < m_trees.size())
                return m_trees[lbl_id];
            else
                return nullptr;
        }

        ptr_vector<code_tree>::iterator begin() { return m_trees.begin(); }
        ptr_vector<code_tree>::iterator end() { return m_trees.end(); }
    };

    // ------------------------------------
    //
    // Path trees AKA inverted path index
    //
    // ------------------------------------

    /**
       \brief Temporary object used to encode a path of the form:

       f.1 -> g.2 -> h.0

       These objects are used to update the inverse path index data structure.
       For example, in the path above, given an enode n, I want to follow the
       parents p_0 of n that are f-applications, and n is the second argument,
       then for each such p_0, I want to follow the parents p_1 of p_0 that
       are g-applications, and p_0 is the third argument. Finally, I want to
       follow the p_2 parents of p_1 that are h-applications and p_1 is the
       first argument of p_2.

       To improve the filtering power of the inverse path index, I'm also
       storing a ground argument (when possible) in the inverted path index.
       the idea is to have paths of the form

       f.1:t.2 -> g.2 -> h.0:s.1

       The extra pairs t.2 and s.1 are an extra filter on the parents.
       The idea is that I want only the f-parents s.t. the third argument is equal to t.
    */
    struct path {
        func_decl *    m_label;
        unsigned short m_arg_idx;
        unsigned short m_ground_arg_idx;
        enode *        m_ground_arg;
        unsigned       m_pattern_idx;
        path *         m_child;
        path (func_decl * lbl, unsigned short arg_idx, unsigned short ground_arg_idx, enode * ground_arg, unsigned pat_idx, path * child):
            m_label(lbl),
            m_arg_idx(arg_idx),
            m_ground_arg_idx(ground_arg_idx),
            m_ground_arg(ground_arg),
            m_pattern_idx(pat_idx),
            m_child(child) {
            SASSERT(ground_arg != nullptr || ground_arg_idx == 0);
        }
    };

    bool is_equal(path const * p1, path const * p2) {
        while (true) {

            if (p1->m_label        != p2->m_label ||
                p1->m_arg_idx      != p2->m_arg_idx ||
                p1->m_pattern_idx  != p2->m_pattern_idx ||
                (p1->m_child == nullptr) != (p2->m_child == nullptr)) {
                return false;
            }

            if (p1->m_child == nullptr && p2->m_child == nullptr)
                return true;

            p1 = p1->m_child;
            p2 = p2->m_child;
        }
    }

    typedef ptr_vector<path> paths;

    /**
       \brief Inverted path index data structure. See comments at struct path.
    */
    struct path_tree {
        func_decl *    m_label;
        unsigned short m_arg_idx;
        unsigned short m_ground_arg_idx;
        enode *        m_ground_arg;
        code_tree *    m_code;
        approx_set     m_filter;
        path_tree *    m_sibling;
        path_tree *    m_first_child;
        enode_vector * m_todo; // temporary field used to collect candidates
#ifdef _PROFILE_PATH_TREE
        stopwatch      m_watch;
        unsigned       m_counter;
        unsigned       m_num_eq_visited;
        unsigned       m_num_neq_visited;
        bool           m_already_displayed; //!< true if the path_tree was already displayed after reaching _PROFILE_PATH_TREE_THRESHOLD
#endif

        path_tree(path * p, label_hasher & h):
            m_label(p->m_label),
            m_arg_idx(p->m_arg_idx),
            m_ground_arg_idx(p->m_ground_arg_idx),
            m_ground_arg(p->m_ground_arg),
            m_code(nullptr),
            m_filter(h(p->m_label)),
            m_sibling(nullptr),
            m_first_child(nullptr),
            m_todo(nullptr) {
#ifdef _PROFILE_PATH_TREE
            m_counter = 0;
            m_num_eq_visited = 0;
            m_num_neq_visited = 0;
            m_already_displayed = false;
#endif
        }

        void display(std::ostream & out, unsigned indent) {
            path_tree * curr = this;
            while (curr != nullptr) {
                for (unsigned i = 0; i < indent; i++) out << "  ";
                out << curr->m_label->get_name() << ":" << curr->m_arg_idx;
                if (curr->m_ground_arg)
                    out << ":#" << curr->m_ground_arg->get_expr_id() << ":" << curr->m_ground_arg_idx;
                out << "  " << m_filter << " " << m_code;
#ifdef _PROFILE_PATH_TREE
                out << ", counter: " << m_counter << ", num_eq_visited: " << m_num_eq_visited << ", num_neq_visited: " << m_num_neq_visited
                    << ", avg. : " << static_cast<double>(m_num_neq_visited)/static_cast<double>(m_num_neq_visited+m_num_eq_visited);
#endif
                out << "\n";
                curr->m_first_child->display(out, indent+1);
                curr = curr->m_sibling;
            }
        }
    };

    typedef std::pair<path_tree *, path_tree *> path_tree_pair;

    // ------------------------------------
    //
    // Matching Abstract Machine Implementation
    //
    // ------------------------------------
    class mam_impl : public mam {
        euf::solver&                ctx;
        egraph &                    m_egraph;
        ematch &                    m_ematch;
        ast_manager &               m;
        bool                        m_use_filters;
        label_hasher                m_lbl_hasher;
        code_tree_manager           m_ct_manager;
        compiler                    m_compiler;
        interpreter                 m_interpreter;
        code_tree_map               m_trees;

        ptr_vector<code_tree>       m_tmp_trees;
        ptr_vector<func_decl>       m_tmp_trees_to_delete;
        ptr_vector<code_tree>       m_to_match;
        unsigned                    m_to_match_head = 0;
        typedef std::pair<quantifier *, app *> qp_pair;
        svector<qp_pair>            m_new_patterns; // recently added patterns

        // m_is_plbl[f] is true, then when f(c_1, ..., c_n) becomes relevant,
        //  for each c_i. c_i->get_root()->lbls().insert(lbl_hash(f))
        bool_vector               m_is_plbl;
        // m_is_clbl[f] is true, then when n=f(c_1, ..., c_n) becomes relevant,
        //  n->get_root()->lbls().insert(lbl_hash(f))
        bool_vector               m_is_clbl;    // children labels

        // auxiliary field used to update data-structures...
        typedef ptr_vector<func_decl> func_decls;
        vector<func_decls>          m_var_parent_labels;

        region &                    m_region;
        region                      m_tmp_region;
        path_tree_pair              m_pp[APPROX_SET_CAPACITY][APPROX_SET_CAPACITY];
        path_tree *                 m_pc[APPROX_SET_CAPACITY][APPROX_SET_CAPACITY];
        pool<enode_vector>          m_pool;

        // temporary field used to update path trees.
        vector<paths>               m_var_paths;
        // temporary field used to collect candidates
        ptr_vector<path_tree>       m_todo;

        enode *                     m_root = nullptr;  // temp field
        enode *                     m_other = nullptr; // temp field
        bool                        m_check_missing_instances = false;        

        enode_vector * mk_tmp_vector() {
            enode_vector * r = m_pool.mk();
            r->reset();
            return r;
        }

        void recycle(enode_vector * v) {
            m_pool.recycle(v);
        }

        void add_candidate(code_tree * t, enode * app) {
            if (!t)
                return;
            TRACE("q", tout << "candidate " << ctx.bpp(app) << "\n";);
            if (!t->has_candidates()) {
                ctx.push(push_back_trail<code_tree*, false>(m_to_match));
                m_to_match.push_back(t);
            }
            t->add_candidate(ctx, app);
        }

        void add_candidate(enode * app) {
            func_decl * lbl = app->get_decl();
            add_candidate(m_trees.get_code_tree_for(lbl), app);
        }

        bool is_plbl(func_decl * lbl) const {
            unsigned lbl_id = lbl->get_small_id();
            return lbl_id < m_is_plbl.size() && m_is_plbl[lbl_id];
        }
        bool is_clbl(func_decl * lbl) const {
            unsigned lbl_id = lbl->get_small_id();
            return lbl_id < m_is_clbl.size() && m_is_clbl[lbl_id];
        }

        void update_lbls(enode * n, unsigned elem) {
            approx_set & r_lbls = n->get_root()->get_lbls();
            if (!r_lbls.may_contain(elem)) {
                ctx.push(mam_value_trail<approx_set>(r_lbls));
                r_lbls.insert(elem);
            }
        }

        void update_clbls(func_decl * lbl) {
            unsigned lbl_id = lbl->get_small_id();
            m_is_clbl.reserve(lbl_id+1, false);
            TRACE("trigger_bug", tout << "update_clbls: " << lbl->get_name() << " is already clbl: " << m_is_clbl[lbl_id] << "\n";);
            TRACE("mam_bug", tout << "update_clbls: " << lbl->get_name() << " is already clbl: " << m_is_clbl[lbl_id] << "\n";);
            if (m_is_clbl[lbl_id])
                return;
            ctx.push(set_bitvector_trail(m_is_clbl, lbl_id));
            SASSERT(m_is_clbl[lbl_id]);
            unsigned h = m_lbl_hasher(lbl);
            for (enode* app : m_egraph.enodes_of(lbl)) {
                if (ctx.is_relevant(app)) {
                    update_lbls(app, h);
                    TRACE("mam_bug", tout << "updating labels of: #" << app->get_expr_id() << "\n";
                          tout << "new_elem: " << h << "\n";
                          tout << "lbls:     " << app->get_lbls() << "\n";
                          tout << "r.lbls:   " << app->get_root()->get_lbls() << "\n";);
                }
            }
        }

        void update_children_plbls(enode * app, unsigned char elem) {
            unsigned num_args = app->num_args();
            for (unsigned i = 0; i < num_args; i++) {
                enode * c            = app->get_arg(i);
                approx_set & r_plbls = c->get_root()->get_plbls();
                if (!r_plbls.may_contain(elem)) {
                    ctx.push(mam_value_trail<approx_set>(r_plbls));
                    r_plbls.insert(elem);
                    TRACE("trigger_bug", tout << "updating plabels of:\n" << mk_ismt2_pp(c->get_root()->get_expr(), m) << "\n";
                          tout << "new_elem: " << static_cast<unsigned>(elem) << "\n";
                          tout << "plbls:    " << c->get_root()->get_plbls() << "\n";);
                    TRACE("mam_bug", tout << "updating plabels of: #" << c->get_root()->get_expr_id() << "\n";
                          tout << "new_elem: " << static_cast<unsigned>(elem) << "\n";
                          tout << "plbls:    " << c->get_root()->get_plbls() << "\n";);

                }
            }
        }

        void update_plbls(func_decl * lbl) {
            unsigned lbl_id = lbl->get_small_id();
            m_is_plbl.reserve(lbl_id+1, false);
            TRACE("trigger_bug", tout << "update_plbls: " << lbl->get_name() << " is already plbl: " << m_is_plbl[lbl_id] << ", lbl_id: " << lbl_id << "\n";
                  tout << "mam: " << this << "\n";);
            TRACE("mam_bug", tout << "update_plbls: " << lbl->get_name() << " is already plbl: " << m_is_plbl[lbl_id] << "\n";);
            if (m_is_plbl[lbl_id])
                return;
            ctx.push(set_bitvector_trail(m_is_plbl, lbl_id));
            SASSERT(m_is_plbl[lbl_id]);
            SASSERT(is_plbl(lbl));
            unsigned h = m_lbl_hasher(lbl);
            for (enode * app : m_egraph.enodes_of(lbl)) {
                if (ctx.is_relevant(app))
                    update_children_plbls(app, h);
            }
        }

        void reset_pp_pc() {
            for (unsigned i = 0; i < APPROX_SET_CAPACITY; i++) {
                for (unsigned j = 0; j < APPROX_SET_CAPACITY; j++) {
                    m_pp[i][j].first  = 0;
                    m_pp[i][j].second = 0;
                    m_pc[i][j]        = nullptr;
                }
            }
        }

        code_tree * mk_code(quantifier * qa, app * mp, unsigned pat_idx) {
            SASSERT(m.is_pattern(mp));
            return m_compiler.mk_tree(qa, mp, pat_idx, true);
        }

        void insert_code(path_tree * t, quantifier * qa, app * mp, unsigned pat_idx) {
            SASSERT(m.is_pattern(mp));
            m_compiler.insert(t->m_code, qa, mp, pat_idx, false);
        }

        path_tree * mk_path_tree(path * p, quantifier * qa, app * mp) {
            SASSERT(m.is_pattern(mp));
            SASSERT(p != nullptr);
            unsigned pat_idx = p->m_pattern_idx;
            path_tree * head = nullptr;
            path_tree * curr = nullptr;
            path_tree * prev = nullptr;
            while (p != nullptr) {
                curr = new (m_region) path_tree(p, m_lbl_hasher);
                if (prev)
                    prev->m_first_child = curr;
                if (!head)
                    head = curr;
                prev = curr;
                p = p->m_child;
            }
            curr->m_code = mk_code(qa, mp, pat_idx);
            ctx.push(new_obj_trail<code_tree>(curr->m_code));
            return head;
        }

        void insert(path_tree * t, path * p, quantifier * qa, app * mp) {
            SASSERT(m.is_pattern(mp));
            path_tree * head = t;
            path_tree * prev_sibling = nullptr;
            bool found_label = false;
            while (t != nullptr) {
                if (t->m_label == p->m_label) {
                    found_label = true;
                    if (t->m_arg_idx == p->m_arg_idx &&
                        t->m_ground_arg == p->m_ground_arg &&
                        t->m_ground_arg_idx == p->m_ground_arg_idx
                        ) {
                        // found compatible node
                        if (t->m_first_child == nullptr) {
                            if (p->m_child == nullptr) {
                                SASSERT(t->m_code != 0);
                                insert_code(t, qa, mp, p->m_pattern_idx);
                            }
                            else {
                                ctx.push(set_ptr_trail<path_tree>(t->m_first_child));
                                t->m_first_child = mk_path_tree(p->m_child, qa, mp);
                            }
                        }
                        else {
                            if (p->m_child == nullptr) {
                                if (t->m_code) {
                                    insert_code(t, qa, mp, p->m_pattern_idx);
                                }
                                else {
                                    ctx.push(set_ptr_trail<code_tree>(t->m_code));
                                    t->m_code = mk_code(qa, mp, p->m_pattern_idx);
                                    ctx.push(new_obj_trail<code_tree>(t->m_code));
                                }
                            }
                            else {
                                insert(t->m_first_child, p->m_child, qa, mp);
                            }
                        }
                        return;
                    }
                }
                prev_sibling = t;
                t = t->m_sibling;
            }
            ctx.push(set_ptr_trail<path_tree>(prev_sibling->m_sibling));
            prev_sibling->m_sibling = mk_path_tree(p, qa, mp);
            if (!found_label) {
                ctx.push(value_trail<approx_set>(head->m_filter));
                head->m_filter.insert(m_lbl_hasher(p->m_label));
            }
        }

        void update_pc(unsigned char h1, unsigned char h2, path * p, quantifier * qa, app * mp) {
            if (m_pc[h1][h2]) {
                insert(m_pc[h1][h2], p, qa, mp);
            }
            else {
                ctx.push(set_ptr_trail<path_tree>(m_pc[h1][h2]));
                m_pc[h1][h2] = mk_path_tree(p, qa, mp);
            }
            TRACE("mam_path_tree_updt",
                  tout << "updated path tree:\n";
                  m_pc[h1][h2]->display(tout, 2););
        }

        void update_pp(unsigned char h1, unsigned char h2, path * p1, path * p2, quantifier * qa, app * mp) {
            if (h1 == h2) {
                SASSERT(m_pp[h1][h2].second == 0);
                if (m_pp[h1][h2].first) {
                    insert(m_pp[h1][h2].first, p1, qa, mp);
                    if (!is_equal(p1, p2))
                        insert(m_pp[h1][h2].first, p2, qa, mp);
                }
                else {
                    ctx.push(set_ptr_trail<path_tree>(m_pp[h1][h2].first));
                    m_pp[h1][h2].first = mk_path_tree(p1, qa, mp);
                    insert(m_pp[h1][h2].first, p2, qa, mp);
                }
            }
            else {
                if (h1 > h2) {
                    std::swap(h1, h2);
                    std::swap(p1, p2);
                }

                if (m_pp[h1][h2].first) {
                    SASSERT(m_pp[h1][h2].second);
                    insert(m_pp[h1][h2].first,  p1, qa, mp);
                    insert(m_pp[h1][h2].second, p2, qa, mp);
                }
                else {
                    SASSERT(m_pp[h1][h2].second == nullptr);
                    ctx.push(set_ptr_trail<path_tree>(m_pp[h1][h2].first));
                    ctx.push(set_ptr_trail<path_tree>(m_pp[h1][h2].second));
                    m_pp[h1][h2].first  = mk_path_tree(p1, qa, mp);
                    m_pp[h1][h2].second = mk_path_tree(p2, qa, mp);
                }
            }
            TRACE("mam_path_tree_updt",
                  tout << "updated path tree:\n";
                  SASSERT(h1 <= h2);
                  m_pp[h1][h2].first->display(tout, 2);
                  if (h1 != h2) {
                      m_pp[h1][h2].second->display(tout, 2);
                  });
        }

        void update_vars(unsigned short var_id, path * p, quantifier * qa, app * mp) {
            if (var_id >= qa->get_num_decls())
                return;
            paths & var_paths = m_var_paths[var_id];
            bool found = false;
            for (path* curr_path : var_paths) {
                if (is_equal(p, curr_path))
                    found = true;
                func_decl * lbl1 = curr_path->m_label;
                func_decl * lbl2 = p->m_label;
                update_plbls(lbl1);
                update_plbls(lbl2);
                update_pp(m_lbl_hasher(lbl1), m_lbl_hasher(lbl2), curr_path, p, qa, mp);
            }
            if (!found) 
                var_paths.push_back(p);            
        }

        enode * get_ground_arg(app * pat, quantifier * qa, unsigned & pos) {
            pos = 0;
            unsigned num_args = pat->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = pat->get_arg(i);
                if (is_ground(arg)) {
                    pos = i;
                    return m_egraph.find(arg);
                }
            }
            return nullptr;
        }

        /**
           \brief Update inverted path index with respect to pattern pat in the egraph of path p.
           pat is a sub-expression of mp->get_arg(pat_idx). mp is a multi-pattern of qa.
           If p == 0, then mp->get_arg(pat_idx) == pat.
        */
        void update_filters(app * pat, path * p, quantifier * qa, app * mp, unsigned pat_idx) {
            unsigned short num_args = pat->get_num_args();
            unsigned ground_arg_pos = 0;
            enode * ground_arg      = get_ground_arg(pat, qa, ground_arg_pos);
            func_decl * plbl        = pat->get_decl();
            for (unsigned short i = 0; i < num_args; i++) {
                expr * child = pat->get_arg(i);
                path * new_path = new (m_tmp_region) path(plbl, i, ground_arg_pos, ground_arg, pat_idx, p);

                if (is_var(child)) {
                    update_vars(to_var(child)->get_idx(), new_path, qa, mp);
                    continue;
                }

                SASSERT(is_app(child));

                if (to_app(child)->is_ground()) {
                    enode * n = m_egraph.find(child);
                    update_plbls(plbl);
                    if (!n->has_lbl_hash())
                        m_egraph.set_lbl_hash(n);
                    TRACE("mam_bug",
                          tout << "updating pc labels " << plbl->get_name() << " " <<
                          static_cast<unsigned>(n->get_lbl_hash()) << "\n";
                          tout << "#" << n->get_expr_id() << " " << n->get_root()->get_lbls() << "\n";
                          tout << "relevant: " << ctx.is_relevant(n) << "\n";);
                    update_pc(m_lbl_hasher(plbl), n->get_lbl_hash(), new_path, qa, mp);
                    continue;
                }

                func_decl * clbl = to_app(child)->get_decl();
                TRACE("mam_bug", tout << "updating pc labels " << plbl->get_name() << " " << clbl->get_name() << "\n";);
                update_plbls(plbl);
                update_clbls(clbl);
                update_pc(m_lbl_hasher(plbl), m_lbl_hasher(clbl), new_path, qa, mp);
                update_filters(to_app(child), new_path, qa, mp, pat_idx);
            }
        }

        /**
           \brief Update inverted path index.
        */
        void update_filters(quantifier * qa, app * mp) {
            TRACE("mam_bug", tout << "updating filters using:\n" << mk_pp(mp, m) << "\n";);
            unsigned num_vars = qa->get_num_decls();
            if (num_vars >= m_var_paths.size())
                m_var_paths.resize(num_vars+1);
            for (unsigned i = 0; i <= num_vars; i++)
                m_var_paths[i].reset();
            m_tmp_region.reset();
            // Given a multi-pattern (p_1, ..., p_n)
            // We need to update the filters using patterns:
            //  (p_1, p_2, ..., p_n)
            //  (p_2, p_1, ..., p_n)
            //  ...
            //  (p_n, p_2, ..., p_1)
            unsigned num_patterns = mp->get_num_args();
            for (unsigned i = 0; i < num_patterns; i++) {
                app * pat = to_app(mp->get_arg(i));
                update_filters(pat, nullptr, qa, mp, i);
            }
        }

        void display_filter_info(std::ostream & out) {
            for (unsigned i = 0; i < APPROX_SET_CAPACITY; i++) {
                for (unsigned j = 0; j < APPROX_SET_CAPACITY; j++) {
                    if (m_pp[i][j].first) {
                        out << "pp[" << i << "][" << j << "]:\n";
                        m_pp[i][j].first->display(out, 1);
                        if (i != j) {
                            m_pp[i][j].second->display(out, 1);
                        }
                    }
                    if (m_pc[i][j]) {
                        out << "pc[" << i << "][" << j << "]:\n";
                        m_pc[i][j]->display(out, 1);
                    }
                }
            }
        }

        /**
           \brief Check equality modulo the equality m_r1 = m_r2
        */
        bool is_eq(enode * n1, enode * n2) {
            return
                n1->get_root() == n2->get_root() ||
                (n1->get_root() == m_other && n2->get_root() == m_root) ||
                (n2->get_root() == m_other && n1->get_root() == m_root);
        }

        /**
           \brief Collect new E-matching candidates using the inverted path index t.
        */
        void collect_parents(enode * r, path_tree * t) {
            TRACE("mam", tout << ctx.bpp(r) << " " << t << "\n";);
            if (t == nullptr)
                return;
#ifdef _PROFILE_PATH_TREE
            t->m_watch.start();
#endif
            
            m_todo.reset();
            enode_vector * to_unmark  = mk_tmp_vector();
            enode_vector * to_unmark2 = mk_tmp_vector();
            SASSERT(to_unmark->empty());
            SASSERT(to_unmark2->empty());
            t->m_todo = mk_tmp_vector();
            t->m_todo->push_back(r);
            m_todo.push_back(t);
            unsigned head = 0;
            while (head < m_todo.size()) {
                path_tree    * t    = m_todo[head];
#ifdef _PROFILE_PATH_TREE
                t->m_counter++;
#endif
                TRACE("mam_path_tree",
                      tout << "processing:\n";
                      t->display(tout, 2););
                enode_vector * v    = t->m_todo;
                approx_set & filter = t->m_filter;
                head++;

#ifdef _PROFILE_PATH_TREE
                static unsigned counter  = 0;
                static unsigned total_sz = 0;
                static unsigned max_sz   = 0;
                counter++;
                total_sz += v->size();
                if (v->size() > max_sz)
                    max_sz = v->size();
                if (counter % 100000 == 0)
                    std::cout << "Avg. " << static_cast<double>(total_sz)/static_cast<double>(counter) << ", Max. " << max_sz << "\n";
#endif

                for (enode* n : *v) {
                    // Two different kinds of mark are used:
                    // - enode mark field:  it is used to mark the already processed parents.
                    // - enode mark2 field: it is used to mark the roots already added to be processed in the next level.
                    //
                    // In a previous version of Z3, the "enode mark field" was used to mark both cases. This is incorrect,
                    // and Z3 may fail to find potential new matches.
                    //
                    // The file regression\acu.sx exposed this problem.
                    enode * curr_child = n->get_root();

                    if (m_use_filters && curr_child->get_plbls().empty_intersection(filter))
                        continue;

#ifdef _PROFILE_PATH_TREE
                    static unsigned counter2  = 0;
                    static unsigned total_sz2 = 0;
                    static unsigned max_sz2   = 0;
                    counter2++;
                    total_sz2 += curr_child->get_num_parents();
                    if (curr_child->get_num_parents() > max_sz2)
                        max_sz2 = curr_child->get_num_parents();
                    if (counter2 % 100000 == 0)
                        std::cout << "Avg2. " << static_cast<double>(total_sz2)/static_cast<double>(counter2) << ", Max2. " << max_sz2 << "\n";
#endif

                    TRACE("mam_path_tree", tout << "processing: #" << curr_child->get_expr_id() << "\n";);
                    for (enode* curr_parent : euf::enode_parents(curr_child)) {
#ifdef _PROFILE_PATH_TREE
                        if (curr_parent->is_equality())
                            t->m_num_eq_visited++;
                        else
                            t->m_num_neq_visited++;
#endif
                        // Remark: equality is never in the inverted path index.
                        if (curr_parent->is_equality())
                            continue;
                        func_decl * lbl            = curr_parent->get_decl();
                        bool is_flat_assoc         = lbl->is_flat_associative();
                        enode * curr_parent_root   = curr_parent->get_root();
                        enode * curr_parent_cg     = curr_parent->get_cg();
                        TRACE("mam_path_tree", tout << "processing parent:\n" << mk_pp(curr_parent->get_expr(), m) << "\n";);
                        TRACE("mam_path_tree", tout << "parent is marked: " << curr_parent->is_marked1() << "\n";);
                        if (filter.may_contain(m_lbl_hasher(lbl)) &&
                            !curr_parent->is_marked1() &&
                            (curr_parent_cg == curr_parent || !is_eq(curr_parent_cg, curr_parent_root)) &&
                            ctx.is_relevant(curr_parent)
                            ) {
                            path_tree * curr_tree = t;
                            while (curr_tree) {
                                if (curr_tree->m_label == lbl &&
                                    // Starting at Z3 3.0, some associative operators (e.g., + and *) are represented using n-ary applications.
                                    // In this cases, we say the declarations is is_flat_assoc().
                                    // The MAM was implemented in Z3 2.0 when the following invariant was true:
                                    //    For every application f(x_1, ..., x_n) of a function symbol f, n = f->get_arity().
                                    // Starting at Z3 3.0, this is only true if !f->is_flat_associative().
                                    // Thus, we need the extra checks.
                                    curr_tree->m_arg_idx < curr_parent->num_args() && 
                                    (!is_flat_assoc || curr_tree->m_ground_arg_idx < curr_parent->num_args())) {
                                    enode * curr_parent_child = curr_parent->get_arg(curr_tree->m_arg_idx)->get_root();
                                    if (// Filter 1. the curr_child is equal to child of the current parent.
                                        curr_child == curr_parent_child &&
                                        // Filter 2. m_ground_arg_idx is a valid argument
                                        curr_tree->m_ground_arg_idx < curr_parent->num_args() && 
                                        // Filter 3.
                                        (
                                         // curr_tree has no support for the filter based on a ground argument.
                                         curr_tree->m_ground_arg == nullptr ||
                                         // checks whether the child of the parent is equal to the expected ground argument.
                                         is_eq(curr_tree->m_ground_arg, curr_parent->get_arg(curr_tree->m_ground_arg_idx))
                                         )) {
                                        if (curr_tree->m_code) {
                                            TRACE("mam_path_tree", tout << "found candidate " << expr_ref(curr_parent->get_expr(), m) << "\n";);
                                            add_candidate(curr_tree->m_code, curr_parent);
                                        }
                                        if (curr_tree->m_first_child) {
                                            path_tree * child = curr_tree->m_first_child;
                                            if (child->m_todo == nullptr) {
                                                child->m_todo = mk_tmp_vector();
                                                m_todo.push_back(child);
                                            }
                                            if (!curr_parent_root->is_marked2()) {
                                                child->m_todo->push_back(curr_parent_root);
                                            }
                                        }
                                    }
                                }
                                curr_tree = curr_tree->m_sibling;
                            }
                            curr_parent->mark1();
                            to_unmark->push_back(curr_parent);
                            if (!curr_parent_root->is_marked2()) {
                                curr_parent_root->mark2();
                                to_unmark2->push_back(curr_parent_root);
                            }
                        }
                    }
                }
                recycle(t->m_todo);
                t->m_todo = nullptr;
                // remove both marks.
                for (enode* n : *to_unmark) n->unmark1();
                for (enode* n : *to_unmark2) n->unmark2();
                to_unmark->reset();
                to_unmark2->reset();
            }
            recycle(to_unmark);
            recycle(to_unmark2);
#ifdef _PROFILE_PATH_TREE
            t->m_watch.stop();
            if (t->m_counter % _PROFILE_PATH_TREE_THRESHOLD == 0) {
                std::cout << "EXPENSIVE " << t->m_watch.get_seconds() << " secs, counter: " << t->m_counter << "\n";
                t->display(std::cout, 0);
                t->m_already_displayed = true;
            }
#endif
        }

        void process_pp(enode * r1, enode * r2) {
            approx_set & plbls1 = r1->get_plbls();
            approx_set & plbls2 = r2->get_plbls();
            TRACE("incremental_matcher", tout << "pp: plbls1: " << plbls1 << ", plbls2: " << plbls2 << "\n";);
            TRACE("mam_info", tout << "pp: " << plbls1.size() * plbls2.size() << "\n";);
            if (!plbls1.empty() && !plbls2.empty()) {
                for (unsigned plbl1 : plbls1) {
                    if (!m.inc()) {
                        break;
                    }
                    SASSERT(plbls1.may_contain(plbl1));
                    for (unsigned plbl2 : plbls2) {
                        SASSERT(plbls2.may_contain(plbl2));
                        unsigned n_plbl1 = plbl1;
                        unsigned n_plbl2 = plbl2;
                        enode *  n_r1    = r1;
                        enode *  n_r2    = r2;
                        if (n_plbl1 > n_plbl2) {
                            std::swap(n_plbl1, n_plbl2);
                            std::swap(n_r1,    n_r2);
                        }
                        if (n_plbl1 == n_plbl2) {
                            SASSERT(m_pp[n_plbl1][n_plbl2].second == 0);
                            if (n_r1->num_parents() <= n_r2->num_parents())
                                collect_parents(n_r1, m_pp[n_plbl1][n_plbl2].first);
                            else
                                collect_parents(n_r2, m_pp[n_plbl1][n_plbl2].first);
                        }
                        else {
                            SASSERT(n_plbl1 < n_plbl2);
                            if (n_r1->num_parents() <= n_r2->num_parents())
                                collect_parents(n_r1, m_pp[n_plbl1][n_plbl2].first);
                            else
                                collect_parents(n_r2, m_pp[n_plbl1][n_plbl2].second);
                        }
                    }
                }
            }
        }

        void process_pc(enode * r1, enode * r2) {
            approx_set & plbls = r1->get_plbls();
            approx_set & clbls = r2->get_lbls();
            if (!plbls.empty() && !clbls.empty()) {
                for (unsigned plbl1 : plbls) {
                    if (!m.inc()) {
                        break;
                    }
                    SASSERT(plbls.may_contain(plbl1));
                    for (unsigned lbl2 : clbls) {
                        SASSERT(clbls.may_contain(lbl2));
                        collect_parents(r1, m_pc[plbl1][lbl2]);
                    }
                }
            }
        }

        unsigned m_new_patterns_qhead = 0;

        void propagate_new_patterns() {
            if (m_new_patterns_qhead >= m_new_patterns.size())
                return;
            ctx.push(value_trail<unsigned>(m_new_patterns_qhead));

            TRACE("mam_new_pat", tout << "matching new patterns:\n";);
            m_tmp_trees_to_delete.reset();
            for (; m_new_patterns_qhead < m_new_patterns.size(); ++m_new_patterns_qhead) {
                if (!m.inc()) 
                    break;
                auto [qa, mp] = m_new_patterns[m_new_patterns_qhead];

                SASSERT(m.is_pattern(mp));
                app *        p     = to_app(mp->get_arg(0));
                func_decl *  lbl   = p->get_decl();
                if (!m_egraph.enodes_of(lbl).empty()) {
                    unsigned lbl_id = lbl->get_small_id();
                    m_tmp_trees.reserve(lbl_id+1, 0);
                    if (m_tmp_trees[lbl_id] == 0) {
                        m_tmp_trees[lbl_id] = m_compiler.mk_tree(qa, mp, 0, false);
                        m_tmp_trees_to_delete.push_back(lbl);
                    }
                    else {
                        m_compiler.insert(m_tmp_trees[lbl_id], qa, mp, 0, true);
                    }
                }
            }

            for (func_decl * lbl : m_tmp_trees_to_delete) {
                unsigned    lbl_id   = lbl->get_small_id();
                code_tree * tmp_tree = m_tmp_trees[lbl_id];
                SASSERT(tmp_tree != 0);
                SASSERT(!m_egraph.enodes_of(lbl).empty());
                m_interpreter.init(tmp_tree);
                auto& nodes = m_egraph.enodes_of(lbl);
                for (unsigned i = 0; i < nodes.size(); ++i) {
                    enode* app = nodes[i];
                    if (ctx.is_relevant(app))
                        m_interpreter.execute_core(tmp_tree, app);
                }
                m_tmp_trees[lbl_id] = nullptr;
                dealloc(tmp_tree);
            }
        }

    public:
        mam_impl(euf::solver & ctx, ematch& ematch, bool use_filters):
            ctx(ctx),
            m_egraph(ctx.get_egraph()),
            m_ematch(ematch),
            m(ctx.get_manager()),
            m_use_filters(use_filters),
            m_ct_manager(m_lbl_hasher, ctx),
            m_compiler(m_egraph, m_ct_manager, m_lbl_hasher, use_filters),
            m_interpreter(ctx, *this, use_filters),
            m_trees(m, m_compiler, ctx),
            m_region(ctx.get_region()) {
            DEBUG_CODE(m_trees.set_egraph(&m_egraph););
            DEBUG_CODE(m_check_missing_instances = false;);
            reset_pp_pc();
        }

        void add_pattern(quantifier * qa, app * mp) override {
            SASSERT(m.is_pattern(mp));
            TRACE("trigger_bug", tout << "adding pattern\n" << mk_ismt2_pp(qa, m) << "\n" << mk_ismt2_pp(mp, m) << "\n";);
            TRACE("mam_bug", tout << "adding pattern\n" << mk_pp(qa, m) << "\n" << mk_pp(mp, m) << "\n";);
            // Z3 checks if a pattern is ground or not before solving.
            // Ground patterns are discarded.
            // However, the simplifier may turn a non-ground pattern into a ground one.
            // So, we should check it again here.
            for (expr* arg : *mp)
                if (is_ground(arg) || has_quantifiers(arg))
                    return; // ignore multi-pattern containing ground pattern.
            update_filters(qa, mp);
            m_new_patterns.push_back(qp_pair(qa, mp));
            ctx.push(push_back_trail<qp_pair, false>(m_new_patterns));
            // The matching abstract machine implements incremental
            // e-matching. So, for a multi-pattern [ p_1, ..., p_n ],
            // we have to make n insertions. In the i-th insertion,
            // the pattern p_i is assumed to be the first one.
            for (unsigned i = 0; i < mp->get_num_args(); i++)
                m_trees.add_pattern(qa, mp, i);
        }

        void reset() override {
            m_trees.reset();
            m_is_plbl.reset();
            m_is_clbl.reset();
            reset_pp_pc();
            m_tmp_region.reset();
        }

        std::ostream& display(std::ostream& out) override {
            m_lbl_hasher.display(out << "mam:\n");
            for (auto* t : m_trees) 
                if (t)
                    t->display(out);            
            return out;
        }

        void propagate_to_match() {
            if (m_to_match_head >= m_to_match.size()) 
                return;
            ctx.push(value_trail<unsigned>(m_to_match_head));
            for (; m_to_match_head < m_to_match.size(); ++m_to_match_head) 
                m_interpreter.execute(m_to_match[m_to_match_head]);
        }

        void propagate() override {
            TRACE("trigger_bug", tout << "match\n"; display(tout););
            propagate_to_match();
            propagate_new_patterns();
        }

        void rematch(bool use_irrelevant) override {
            unsigned lbl = 0;
            for (auto * t : m_trees) {
                if (t) {
                    m_interpreter.init(t);
                    func_decl * lbl = t->get_root_lbl();
                    for (enode * curr : m_egraph.enodes_of(lbl)) {
                        if (use_irrelevant || ctx.is_relevant(curr))
                            m_interpreter.execute_core(t, curr);
                    }
                }
                ++lbl;
            }
        }

        bool check_missing_instances() override {
            TRACE("missing_instance", tout << "checking for missing instances...\n";);
            flet<bool> l(m_check_missing_instances, true);
            rematch(false);
            return true;
        }

        void on_match(quantifier * qa, app * pat, unsigned num_bindings, enode * const * bindings, unsigned max_generation) override {
            TRACE("trigger_bug", tout << "found match " << mk_pp(qa, m) << "\n";);
            unsigned min_gen = 0, max_gen = 0;
            m_interpreter.get_min_max_top_generation(min_gen, max_gen);
            m_ematch.on_binding(qa, pat, bindings, max_generation, min_gen, max_gen);
        }

        // This method is invoked when n becomes relevant.
        // If lazy == true, then n is not added to the list of 
        // candidate enodes for matching. That is, the method just updates the lbls.
        void add_node(enode * n, bool lazy) override {
            TRACE("trigger_bug", tout << "relevant_eh:\n" << mk_ismt2_pp(n->get_expr(), m) << "\n";
                  tout << "mam: " << this << "\n";);
            TRACE("mam", tout << "relevant_eh: #" << n->get_expr_id() << "\n";);
            if (n->has_lbl_hash())
                update_lbls(n, n->get_lbl_hash());

            if (n->num_args() > 0) {
                func_decl * lbl = n->get_decl();
                unsigned h      = m_lbl_hasher(lbl);
                TRACE("trigger_bug", tout << "lbl: " << lbl->get_name() << " is_clbl(lbl): " << is_clbl(lbl)
                      << ", is_plbl(lbl): " << is_plbl(lbl) << ", h: " << h << "\n";
                      tout << "lbl_id: " << lbl->get_small_id() << "\n";);
                if (is_clbl(lbl))
                    update_lbls(n, h);
                if (is_plbl(lbl))
                    update_children_plbls(n, h);
                TRACE("mam_bug", tout << "adding relevant candidate:\n" << mk_ll_pp(n->get_expr(), m) << "\n";);
                if (!lazy)
                    add_candidate(n);
            }
        }

        bool can_propagate() const override {
            return !m_to_match.empty() || !m_new_patterns.empty();
        }

        void on_merge(enode * root, enode * other) override {            
            flet<enode *> l1(m_other, other);
            flet<enode *> l2(m_root, root);

            TRACE("mam", tout << "on_merge: #" << other->get_expr_id() << " #" << root->get_expr_id() << "\n";);
            TRACE("mam_inc_bug_detail", m_egraph.display(tout););
            TRACE("mam_inc_bug",
                  tout << "before:\n#" << other->get_expr_id() << " #" << root->get_expr_id() << "\n";
                  tout << "other.lbls:  " << other->get_lbls() << "\n";
                  tout << "root.lbls:  " << root->get_lbls() << "\n";
                  tout << "other.plbls: " << other->get_plbls() << "\n";
                  tout << "root.plbls: " << root->get_plbls() << "\n";);

            process_pc(other, root);
            process_pc(root, other);
            process_pp(other, root);

            approx_set   other_plbls = other->get_plbls();
            approx_set & root_plbls = root->get_plbls();
            approx_set   other_lbls  = other->get_lbls();
            approx_set & root_lbls  = root->get_lbls();

            ctx.push(mam_value_trail<approx_set>(root_lbls));
            ctx.push(mam_value_trail<approx_set>(root_plbls));
            root_lbls  |= other_lbls;
            root_plbls |= other_plbls;
            TRACE("mam_inc_bug",
                  tout << "after:\n";
                  tout << "other.lbls:  " << other->get_lbls() << "\n";
                  tout << "root.lbls:  " << root->get_lbls() << "\n";
                  tout << "other.plbls: " << other->get_plbls() << "\n";
                  tout << "root.plbls: " << root->get_plbls() << "\n";);
            SASSERT(approx_subset(other->get_plbls(), root->get_plbls()));
            SASSERT(approx_subset(other->get_lbls(), root->get_lbls()));
        }
    };

    void mam::ground_subterms(expr* e, ptr_vector<app>& ground) {
        ground.reset();
        expr_fast_mark1 mark;
        ptr_buffer<app> todo;
        if (is_app(e))
            todo.push_back(to_app(e));
        while (!todo.empty()) {
            app * n = todo.back();
            todo.pop_back();
            if (mark.is_marked(n))
                continue;
            mark.mark(n);
            if (n->is_ground()) 
                ground.push_back(n);
            else {
                for (expr* arg : *n) 
                    if (is_app(arg))
                        todo.push_back(to_app(arg));
            }
        }
    }

    mam* mam::mk(euf::solver& ctx, ematch& em) {
        return alloc(mam_impl, ctx, em, true);
    }

}

