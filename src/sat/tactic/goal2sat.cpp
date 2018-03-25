/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal2sat.cpp

Abstract:

    "Compile" a goal into the SAT engine.
    Atoms are "abstracted" into boolean variables.
    The mapping between boolean variables and atoms
    can be used to convert back the state of the 
    SAT engine into a goal.

    The idea is to support scenarios such as:
    1) simplify, blast, convert into SAT, and solve
    2) convert into SAT, apply SAT for a while, learn new units, and translate back into a goal.
    3) convert into SAT, apply SAT preprocessor (failed literal propagation, resolution, etc) and translate back into a goal.
    4) Convert boolean structure into SAT, convert atoms into another engine, combine engines using lazy combination, solve.

Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#include "util/ref_util.h"
#include "util/cooperate.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "sat/tactic/goal2sat.h"
#include "sat/ba_solver.h"
#include "model/model_evaluator.h"
#include "model/model_v2_pp.h"
#include "tactic/tactic.h"
#include "tactic/generic_model_converter.h"
#include<sstream>

struct goal2sat::imp {
    struct frame {
        app *    m_t;
        unsigned m_root:1;
        unsigned m_sign:1;
        unsigned m_idx;
        frame(app * t, bool r, bool s, unsigned idx):
            m_t(t), m_root(r), m_sign(s), m_idx(idx) {}
    };
    ast_manager &               m;
    pb_util                     pb;
    sat::ba_solver*             m_ext;
    svector<frame>              m_frame_stack;
    svector<sat::literal>       m_result_stack;
    obj_map<app, sat::literal>  m_cache;
    obj_hashtable<expr>         m_interface_vars;
    sat::solver &               m_solver;
    atom2bool_var &             m_map;
    dep2asm_map &               m_dep2asm;
    sat::bool_var               m_true;
    bool                        m_ite_extra;
    unsigned long long          m_max_memory;
    expr_ref_vector             m_trail;
    expr_ref_vector             m_interpreted_atoms;
    bool                        m_default_external;
    bool                        m_xor_solver;
    bool                        m_is_lemma;
    
    imp(ast_manager & _m, params_ref const & p, sat::solver & s, atom2bool_var & map, dep2asm_map& dep2asm, bool default_external):
        m(_m),
        pb(m),
        m_ext(0),
        m_solver(s),
        m_map(map),
        m_dep2asm(dep2asm),
        m_trail(m),
        m_interpreted_atoms(m),
        m_default_external(default_external),
        m_is_lemma(false) {
        updt_params(p);
        m_true = sat::null_bool_var;
    }
        
    void updt_params(params_ref const & p) {
        m_ite_extra  = p.get_bool("ite_extra", true);
        m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_xor_solver = p.get_bool("xor_solver", false);
    }

    void throw_op_not_handled(std::string const& s) {
        std::string s0 = "operator " + s + " not supported, apply simplifier before invoking translator";
        throw tactic_exception(s0.c_str());
    }
    
    void mk_clause(sat::literal l) {
        TRACE("goal2sat", tout << "mk_clause: " << l << "\n";);
        m_solver.mk_clause(1, &l);
    }

    void set_lemma_mode(bool f) { m_is_lemma = f; }

    void mk_clause(sat::literal l1, sat::literal l2) {
        TRACE("goal2sat", tout << "mk_clause: " << l1 << " " << l2 << "\n";);
        m_solver.mk_clause(l1, l2, m_is_lemma);
    }

    void mk_clause(sat::literal l1, sat::literal l2, sat::literal l3) {
        TRACE("goal2sat", tout << "mk_clause: " << l1 << " " << l2 << " " << l3 << "\n";);
        m_solver.mk_clause(l1, l2, l3, m_is_lemma);
    }

    void mk_clause(unsigned num, sat::literal * lits) {
        TRACE("goal2sat", tout << "mk_clause: "; for (unsigned i = 0; i < num; i++) tout << lits[i] << " "; tout << "\n";);
        m_solver.mk_clause(num, lits, m_is_lemma);
    }

    sat::bool_var mk_true() {
        if (m_true == sat::null_bool_var) {
            // create fake variable to represent true;
            m_true = m_solver.mk_var(false);
            mk_clause(sat::literal(m_true, false)); // v is true
        }
        return m_true;
    }

   void convert_atom(expr * t, bool root, bool sign) {
        SASSERT(m.is_bool(t));
        sat::literal  l;
        sat::bool_var v = m_map.to_bool_var(t);
        if (v == sat::null_bool_var) {
            if (m.is_true(t)) {
                l = sat::literal(mk_true(), sign);
            }
            else if (m.is_false(t)) {
                l = sat::literal(mk_true(), !sign);
            }
            else {
                bool ext = m_default_external || !is_uninterp_const(t) || m_interface_vars.contains(t);
                sat::bool_var v = m_solver.mk_var(ext);
                m_map.insert(t, v);
                l = sat::literal(v, sign);
                TRACE("sat", tout << "new_var: " << v << ": " << mk_ismt2_pp(t, m) << "\n";);
                if (ext && !is_uninterp_const(t)) {
                    m_interpreted_atoms.push_back(t);
                }
            }
        }
        else {
            SASSERT(v != sat::null_bool_var);
            l = sat::literal(v, sign);
            m_solver.set_eliminated(v, false);
        }
        SASSERT(l != sat::null_literal);
        if (root)
            mk_clause(l);
        else
            m_result_stack.push_back(l);
    }

    bool convert_app(app* t, bool root, bool sign) {
        if (t->get_family_id() == pb.get_family_id()) {
            ensure_extension();
            m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
            return false;
        }
        else {
            convert_atom(t, root, sign);
            return true;
        }
    }

    bool process_cached(app * t, bool root, bool sign) {
        sat::literal l;
        if (m_cache.find(t, l)) {
            if (sign)
                l.neg();
            if (root)
                mk_clause(l);
            else
                m_result_stack.push_back(l);
            return true;
        }
        return false;
    }


    bool visit(expr * t, bool root, bool sign) {
        if (!is_app(t)) {
            convert_atom(t, root, sign);
            return true;
        }
        if (process_cached(to_app(t), root, sign))
            return true;
        if (to_app(t)->get_family_id() != m.get_basic_family_id()) {
            return convert_app(to_app(t), root, sign);
        }
        switch (to_app(t)->get_decl_kind()) {
        case OP_NOT:
        case OP_OR:
        case OP_AND:
        case OP_IFF:
            m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
            return false;
        case OP_ITE:
        case OP_EQ:
            if (m.is_bool(to_app(t)->get_arg(1))) {
                m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
                return false;
            }
            else {
                convert_atom(t, root, sign);
                return true;
            }
        case OP_XOR:
        case OP_IMPLIES:
        case OP_DISTINCT: {
            TRACE("goal2sat_not_handled", tout << mk_ismt2_pp(t, m) << "\n";);
            std::ostringstream strm;
            strm << mk_ismt2_pp(t, m);
            throw_op_not_handled(strm.str());
        }
        default:
            convert_atom(t, root, sign);
            return true;
        }
    }

    void convert_or(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_or:\n" << mk_ismt2_pp(t, m) << "\n";);
        unsigned num = t->get_num_args();
        if (root) {
            SASSERT(num == m_result_stack.size());
            if (sign) {
                // this case should not really happen.
                for (unsigned i = 0; i < num; i++) {
                    sat::literal l = m_result_stack[i];
                    l.neg();
                    mk_clause(l);
                }
            }
            else {
                mk_clause(m_result_stack.size(), m_result_stack.c_ptr());
            }
            m_result_stack.reset();
        }
        else {
            SASSERT(num <= m_result_stack.size());
            sat::bool_var k = m_solver.mk_var();
            sat::literal  l(k, false);
            m_cache.insert(t, l);
            sat::literal * lits = m_result_stack.end() - num;
            for (unsigned i = 0; i < num; i++) {
                mk_clause(~lits[i], l);
            }
            m_result_stack.push_back(~l);
            lits = m_result_stack.end() - num - 1;
            // remark: mk_clause may perform destructive updated to lits.
            // I have to execute it after the binary mk_clause above.
            mk_clause(num+1, lits);
            unsigned old_sz = m_result_stack.size() - num - 1;
            m_result_stack.shrink(old_sz);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_and(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_and:\n" << mk_ismt2_pp(t, m) << "\n";);
        unsigned num = t->get_num_args();
        if (root) {
            if (sign) {
                for (unsigned i = 0; i < num; ++i) {
                    m_result_stack[i].neg();
                }                
                mk_clause(m_result_stack.size(), m_result_stack.c_ptr());
            }
            else {
                for (unsigned i = 0; i < num; ++i) {
                    mk_clause(m_result_stack[i]);
                }
            }
            m_result_stack.reset();
        }
        else {
            SASSERT(num <= m_result_stack.size());
            sat::bool_var k = m_solver.mk_var();
            sat::literal  l(k, false);
            m_cache.insert(t, l);
            // l => /\ lits
            sat::literal * lits = m_result_stack.end() - num;
            for (unsigned i = 0; i < num; i++) {
                mk_clause(~l, lits[i]);
            }
            // /\ lits => l
            for (unsigned i = 0; i < num; ++i) {
                m_result_stack[m_result_stack.size() - num + i].neg();
            }
            m_result_stack.push_back(l);
            lits = m_result_stack.end() - num - 1;
            mk_clause(num+1, lits);
            unsigned old_sz = m_result_stack.size() - num - 1;
            m_result_stack.shrink(old_sz);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
            TRACE("goal2sat", tout << m_result_stack << "\n";);
        }
    }

    void convert_ite(app * n, bool root, bool sign) {
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 3);
        sat::literal  c = m_result_stack[sz-3];
        sat::literal  t = m_result_stack[sz-2];
        sat::literal  e = m_result_stack[sz-1];
        if (root) {
            SASSERT(sz == 3);
            if (sign) {
                mk_clause(~c, ~t);
                mk_clause(c,  ~e);
            }
            else {
                mk_clause(~c, t);
                mk_clause(c, e);
            }
            m_result_stack.reset();
        }
        else {
            sat::bool_var k = m_solver.mk_var();
            sat::literal  l(k, false);
            m_cache.insert(n, l);
            mk_clause(~l, ~c, t);
            mk_clause(~l,  c, e);
            mk_clause(l,  ~c, ~t);
            mk_clause(l,   c, ~e);
            if (m_ite_extra) {
                mk_clause(~t, ~e, l);
                mk_clause(t,  e, ~l);
            }
            m_result_stack.shrink(sz-3);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_iff2(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_iff " << root << " " << sign << "\n" << mk_ismt2_pp(t, m) << "\n";);
        unsigned sz = m_result_stack.size();
        SASSERT(sz >= 2);
        sat::literal  l1 = m_result_stack[sz-1];
        sat::literal  l2 = m_result_stack[sz-2];
        if (root) {
            SASSERT(sz == 2);
            if (sign) {
                mk_clause(l1, l2);
                mk_clause(~l1, ~l2);
            }
            else {
                mk_clause(l1, ~l2);
                mk_clause(~l1, l2);
            }
            m_result_stack.reset();
        }
        else {
            sat::bool_var k = m_solver.mk_var();
            sat::literal  l(k, false);
            m_cache.insert(t, l);
            mk_clause(~l, l1, ~l2);
            mk_clause(~l, ~l1, l2);
            mk_clause(l,  l1, l2);
            mk_clause(l, ~l1, ~l2);
            m_result_stack.shrink(sz-2);
            if (sign)
                l.neg();
            m_result_stack.push_back(l);
        }
    }

    void convert_iff(app * t, bool root, bool sign) {
        TRACE("goal2sat", tout << "convert_iff " << root << " " << sign << "\n" << mk_ismt2_pp(t, m) << "\n";);
        unsigned sz = m_result_stack.size();
        unsigned num = get_num_args(t);
        SASSERT(sz >= num && num >= 2);
        if (num == 2) {
            convert_iff2(t, root, sign);
            return;
        }
        sat::literal_vector lits;
        sat::bool_var v = m_solver.mk_var(true);
        lits.push_back(sat::literal(v, true));
        convert_pb_args(num, lits);
        // ensure that = is converted to xor
        for (unsigned i = 1; i + 1 < lits.size(); ++i) {
            lits[i].neg();
        }
        ensure_extension();
        m_ext->add_xr(lits);
        sat::literal lit(v, sign);
        if (root) {            
            m_result_stack.reset();
            mk_clause(lit);
        }
        else {
            m_result_stack.shrink(sz - num);
            m_result_stack.push_back(lit);
        }
    }

    void convert_pb_args(unsigned num_args, sat::literal_vector& lits) {
        unsigned sz = m_result_stack.size();
        for (unsigned i = 0; i < num_args; ++i) {
            sat::literal lit(m_result_stack[sz - num_args + i]);
            if (!m_solver.is_external(lit.var())) {
                m_solver.set_external(lit.var());
            }
            lits.push_back(lit);
        }
    }

    typedef std::pair<unsigned, sat::literal> wliteral;

    void check_unsigned(rational const& c) {
        if (!c.is_unsigned()) {
            throw default_exception("unsigned coefficient expected");
        }
    }

    void convert_to_wlits(app* t, sat::literal_vector const& lits, svector<wliteral>& wlits) {
        for (unsigned i = 0; i < lits.size(); ++i) {
            rational c = pb.get_coeff(t, i);
            check_unsigned(c);
            wlits.push_back(std::make_pair(c.get_unsigned(), lits[i]));
        }
    }

    void convert_pb_args(app* t, svector<wliteral>& wlits) {
        sat::literal_vector lits;
        convert_pb_args(t->get_num_args(), lits);
        convert_to_wlits(t, lits, wlits);        
    }

    void convert_pb_ge(app* t, bool root, bool sign) {
        rational k = pb.get_k(t);
        check_unsigned(k);                
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        unsigned sz = m_result_stack.size();
        if (root) {
            m_result_stack.reset();
            m_ext->add_pb_ge(sat::null_bool_var, wlits, k.get_unsigned());
        }
        else {
            sat::bool_var v = m_solver.mk_var(true);
            sat::literal lit(v, sign);
            m_ext->add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("goal2sat", tout << "root: " << root << " lit: " << lit << "\n";);
            m_result_stack.shrink(sz - t->get_num_args());
            m_result_stack.push_back(lit);
        }
    }

    void convert_pb_le(app* t, bool root, bool sign) {
        rational k = pb.get_k(t);
        k.neg();
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        unsigned sz = m_result_stack.size();
        if (root) {
            m_result_stack.reset();
            m_ext->add_pb_ge(sat::null_bool_var, wlits, k.get_unsigned());
        }
        else {
            sat::bool_var v = m_solver.mk_var(true);
            sat::literal lit(v, sign);
            m_ext->add_pb_ge(v, wlits, k.get_unsigned());
            TRACE("goal2sat", tout << "root: " << root << " lit: " << lit << "\n";);
            m_result_stack.shrink(sz - t->get_num_args());
            m_result_stack.push_back(lit);
        }
    }

    void convert_pb_eq(app* t, bool root, bool sign) {
        IF_VERBOSE(0, verbose_stream() << "pbeq: " << mk_pp(t, m) << "\n";);
        rational k = pb.get_k(t);
        SASSERT(k.is_unsigned());
        svector<wliteral> wlits;
        convert_pb_args(t, wlits);
        sat::bool_var v1 = (root && !sign) ? sat::null_bool_var : m_solver.mk_var(true);
        sat::bool_var v2 = (root && !sign) ? sat::null_bool_var : m_solver.mk_var(true);
        m_ext->add_pb_ge(v1, wlits, k.get_unsigned());        
        k.neg();
        for (wliteral& wl : wlits) {
            wl.second.neg();
            k += rational(wl.first);
        }
        check_unsigned(k);
        m_ext->add_pb_ge(v2, wlits, k.get_unsigned());
        if (root && !sign) {
            m_result_stack.reset();
        }
        else {
            sat::literal l1(v1, false), l2(v2, false);
            sat::bool_var v = m_solver.mk_var();
            sat::literal l(v, false);
            mk_clause(~l, l1);
            mk_clause(~l, l2);
            mk_clause(~l1, ~l2, l);
            m_cache.insert(t, l);
            m_result_stack.shrink(m_result_stack.size() - t->get_num_args());
            if (sign) l.neg();
            m_result_stack.push_back(l);
            if (root) {
                m_result_stack.reset();
                mk_clause(l);
            }
        }
    }

    void convert_at_least_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        sat::literal_vector lits;
        unsigned sz = m_result_stack.size();
        convert_pb_args(t->get_num_args(), lits);
        if (root) {
            m_result_stack.reset();
            m_ext->add_at_least(sat::null_bool_var, lits, k.get_unsigned());
        }
        else {
            sat::bool_var v = m_solver.mk_var(true);
            sat::literal lit(v, false);
            m_ext->add_at_least(v, lits, k.get_unsigned());
            m_cache.insert(t, lit);
            if (sign) lit.neg();
            TRACE("goal2sat", tout << "root: " << root << " lit: " << lit << "\n";);
            m_result_stack.shrink(sz - t->get_num_args());
            m_result_stack.push_back(lit);
        }
    }

    void convert_at_most_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        sat::literal_vector lits;
        unsigned sz = m_result_stack.size();
        convert_pb_args(t->get_num_args(), lits);
        for (sat::literal& l : lits) {
            l.neg();
        }
        if (root) {
            m_result_stack.reset();
            m_ext->add_at_least(sat::null_bool_var, lits, lits.size() - k.get_unsigned());
        }
        else {
            sat::bool_var v = m_solver.mk_var(true);
            sat::literal lit(v, false);
            m_ext->add_at_least(v, lits, lits.size() - k.get_unsigned());
            m_cache.insert(t, lit);
            m_result_stack.shrink(sz - t->get_num_args());
            if (sign) lit.neg();
            m_result_stack.push_back(lit);
        }        
    }

    void convert_eq_k(app* t, rational const& k, bool root, bool sign) {
        SASSERT(k.is_unsigned());
        sat::literal_vector lits;
        convert_pb_args(t->get_num_args(), lits);
        sat::bool_var v1 = (root && !sign) ? sat::null_bool_var : m_solver.mk_var(true);
        sat::bool_var v2 = (root && !sign) ? sat::null_bool_var : m_solver.mk_var(true);
        m_ext->add_at_least(v1, lits, k.get_unsigned());        
        for (sat::literal& l : lits) {
            l.neg();
        }
        m_ext->add_at_least(v2, lits, lits.size() - k.get_unsigned());


        if (root && !sign) {
            m_result_stack.reset();
        }
        else {
            sat::literal l1(v1, false), l2(v2, false);
            sat::bool_var v = m_solver.mk_var();
            sat::literal l(v, false);
            mk_clause(~l, l1);
            mk_clause(~l, l2);
            mk_clause(~l1, ~l2, l);
            m_cache.insert(t, l);
            m_result_stack.shrink(m_result_stack.size() - t->get_num_args());
            if (sign) l.neg();
            m_result_stack.push_back(l);
            if (root) {
                mk_clause(l);
                m_result_stack.reset();
            }
        }
    }

    void ensure_extension() {
        if (!m_ext) {
            sat::extension* ext = m_solver.get_extension();
            if (ext) {
                m_ext = dynamic_cast<sat::ba_solver*>(ext);
                SASSERT(m_ext);
            }
            if (!m_ext) {
                m_ext = alloc(sat::ba_solver);
                m_solver.set_extension(m_ext);
            }
        }
    }

    void convert(app * t, bool root, bool sign) {
        if (t->get_family_id() == m.get_basic_family_id()) {
            switch (to_app(t)->get_decl_kind()) {
            case OP_OR:
                convert_or(t, root, sign);
                break;
            case OP_AND:
                convert_and(t, root, sign);
                break;
            case OP_ITE:
                convert_ite(t, root, sign);
                break;
            case OP_IFF:
            case OP_EQ:
                convert_iff(t, root, sign);
                break;
            default:
                UNREACHABLE();
            }
        }
        else if (t->get_family_id() == pb.get_family_id()) {
            ensure_extension();
            rational k;
            switch (t->get_decl_kind()) {
            case OP_AT_MOST_K:
                k = pb.get_k(t);
                convert_at_most_k(t, k, root, sign);
                break;
            case OP_AT_LEAST_K:
                k = pb.get_k(t);
                convert_at_least_k(t, k, root, sign);
                break;
            case OP_PB_LE:
                if (pb.has_unit_coefficients(t)) {
                    k = pb.get_k(t);
                    convert_at_most_k(t, k, root, sign);
                }
                else {
                    convert_pb_le(t, root, sign);
                }
                break;
            case OP_PB_GE:
                if (pb.has_unit_coefficients(t)) {
                    k = pb.get_k(t);
                    convert_at_least_k(t, k, root, sign);
                }
                else {
                    convert_pb_ge(t, root, sign);
                }
                break;
            case OP_PB_EQ:
                if (pb.has_unit_coefficients(t)) {
                    k = pb.get_k(t);
                    convert_eq_k(t, k, root, sign);
                }
                else {
                    convert_pb_eq(t, root, sign);
                }
                break;
            default:
                UNREACHABLE();
            }
        }
        else {
            UNREACHABLE();
        }
    }


    unsigned get_num_args(app* t) {
        
        if (m.is_iff(t) && m_xor_solver) {
            unsigned n = 2;
            while (m.is_iff(t->get_arg(1))) {
                ++n;
                t = to_app(t->get_arg(1));
            }
            return n;
        }
        else {
            return t->get_num_args();
        }
    }

    expr* get_arg(app* t, unsigned idx) {
        if (m.is_iff(t) && m_xor_solver) {        
            while (idx >= 1) {
                SASSERT(m.is_iff(t));
                t = to_app(t->get_arg(1));
                --idx;
            }
            if (m.is_iff(t)) {
                return t->get_arg(idx);
            }
            else {
                return t;
            }
        }
        else {
            return t->get_arg(idx);
        }
    }
    
    void process(expr * n) {
        //SASSERT(m_result_stack.empty());
        TRACE("goal2sat", tout << "converting: " << mk_ismt2_pp(n, m) << "\n";);
        if (visit(n, true, false)) {
            SASSERT(m_result_stack.empty());
            return;
        }
        while (!m_frame_stack.empty()) {
        loop:
            cooperate("goal2sat");
            if (m.canceled())
                throw tactic_exception(m.limit().get_cancel_msg());
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            frame & fr = m_frame_stack.back();
            app * t    = fr.m_t;
            bool root  = fr.m_root;
            bool sign  = fr.m_sign;
            TRACE("goal2sat_bug", tout << "result stack\n";
                  tout << mk_ismt2_pp(t, m) << " root: " << root << " sign: " << sign << "\n";
                  tout << m_result_stack << "\n";);
            if (fr.m_idx == 0 && process_cached(t, root, sign)) {
                m_frame_stack.pop_back();
                continue;
            }
            if (m.is_not(t)) {
                m_frame_stack.pop_back();
                visit(t->get_arg(0), root, !sign);
                continue;
            }
            unsigned num = get_num_args(t);
            while (fr.m_idx < num) {
                expr * arg = get_arg(t, fr.m_idx);
                fr.m_idx++;
                if (!visit(arg, false, false))
                    goto loop;
            }
            TRACE("goal2sat_bug", tout << "converting\n";
                  tout << mk_ismt2_pp(t, m) << " root: " << root << " sign: " << sign << "\n";
                  tout << m_result_stack << "\n";);
            convert(t, root, sign);
            m_frame_stack.pop_back();
        }
        CTRACE("goal2sat", !m_result_stack.empty(), tout << m_result_stack << "\n";);
        SASSERT(m_result_stack.empty());
    }

    void insert_dep(expr* dep0, expr* dep, bool sign) {
        SASSERT(sign || dep0 == dep); // !sign || (not dep0) == dep.
        SASSERT(!sign || m.is_not(dep0));
        expr_ref new_dep(m), fml(m);
        if (is_uninterp_const(dep)) {
            new_dep = dep;
        }
        else {
            new_dep = m.mk_fresh_const("dep", m.mk_bool_sort());
            m_trail.push_back(new_dep);
            m_interface_vars.insert(new_dep);
            fml = m.mk_iff(new_dep, dep);
            process(fml);            
        }
        convert_atom(new_dep, false, false);
        sat::literal lit = m_result_stack.back();
        m_dep2asm.insert(dep0, sign?~lit:lit);
        m_result_stack.pop_back();
    }

    void operator()(goal const & g) {
        m_interface_vars.reset();
        collect_boolean_interface(g, m_interface_vars);
        unsigned size = g.size();
        expr_ref f(m), d_new(m);
        ptr_vector<expr> deps;
        expr_ref_vector  fmls(m);
        for (unsigned idx = 0; idx < size; idx++) {
            f = g.form(idx);
            // Add assumptions.
            if (g.dep(idx)) {
                deps.reset();
                fmls.reset();
                m.linearize(g.dep(idx), deps);
                fmls.push_back(f);
                for (expr * d : deps) {
                    expr * d1 = d;
                    SASSERT(m.is_bool(d));
                    bool sign = m.is_not(d, d1);

                    insert_dep(d, d1, sign);
                    if (d == f) {
                        goto skip_dep;
                    }
                    if (sign) {
                        d_new = d1;
                    }
                    else {
                        d_new = m.mk_not(d);
                    }
                    fmls.push_back(d_new);
                }                
                f = m.mk_or(fmls.size(), fmls.c_ptr());
            }
            TRACE("goal2sat", tout << f << "\n";);
            process(f);
        skip_dep:
            ;
        }
    }

    void operator()(unsigned sz, expr * const * fs) {
        m_interface_vars.reset();
        collect_boolean_interface(m, sz, fs, m_interface_vars);
        
        for (unsigned i = 0; i < sz; i++)
            process(fs[i]);
    }

};

struct unsupported_bool_proc {
    struct found {};
    ast_manager & m;
    unsupported_bool_proc(ast_manager & _m):m(_m) {}
    void operator()(var *) {}
    void operator()(quantifier *) {}
    void operator()(app * n) { 
        if (n->get_family_id() == m.get_basic_family_id()) {
            switch (n->get_decl_kind()) {
            case OP_XOR:
            case OP_IMPLIES:
            case OP_DISTINCT:
                throw found();
            default:
                break;
            }
        }
    }
};

/**
   \brief Return true if s contains an unsupported Boolean operator.
   goal_rewriter (with the following configuration) can be used to
   eliminate unsupported operators.
      :elim-and true
      :blast-distinct true
*/
bool goal2sat::has_unsupported_bool(goal const & g) {
    return test<unsupported_bool_proc>(g);
}

goal2sat::goal2sat():m_imp(nullptr), m_interpreted_atoms(nullptr) {
}

void goal2sat::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("ite_extra", CPK_BOOL, "(default: true) add redundant clauses (that improve unit propagation) when encoding if-then-else formulas");
}

struct goal2sat::scoped_set_imp {
    goal2sat * m_owner; 
    scoped_set_imp(goal2sat * o, goal2sat::imp * i):m_owner(o) {
        m_owner->m_imp = i;        
    }
    ~scoped_set_imp() {
        m_owner->m_imp = nullptr;
    }
};


void goal2sat::operator()(goal const & g, params_ref const & p, sat::solver & t, atom2bool_var & m, dep2asm_map& dep2asm, bool default_external, bool is_lemma) {
    imp proc(g.m(), p, t, m, dep2asm, default_external);
    scoped_set_imp set(this, &proc);
    proc.set_lemma_mode(is_lemma);
    proc(g);
    dealloc(m_interpreted_atoms);
    m_interpreted_atoms = alloc(expr_ref_vector, g.m());
    m_interpreted_atoms->append(proc.m_interpreted_atoms);
}

void goal2sat::get_interpreted_atoms(expr_ref_vector& atoms) {
    if (m_interpreted_atoms) {
        atoms.append(*m_interpreted_atoms);
    }
}


sat2goal::mc::mc(ast_manager& m): m(m), m_var2expr(m) {}

void sat2goal::mc::flush_smc(sat::solver& s, atom2bool_var const& map) {
    s.flush(m_smc);
    m_var2expr.resize(s.num_vars());
    map.mk_var_inv(m_var2expr);
}

void sat2goal::mc::flush_gmc() {
    sat::literal_vector updates;
    m_smc.expand(updates);    
    m_smc.reset();
    if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
    // now gmc owns the model converter
    sat::literal_vector clause;
    expr_ref_vector tail(m);
    expr_ref def(m);
    for (unsigned i = 0; i < updates.size(); ++i) {
        sat::literal l = updates[i];
        if (l == sat::null_literal) {
            sat::literal lit0 = clause[0];
            for (unsigned i = 1; i < clause.size(); ++i) {
                tail.push_back(lit2expr(~clause[i]));
            }
            def = m.mk_or(lit2expr(lit0), mk_and(tail));
            if (lit0.sign()) {
                lit0.neg();
                def = m.mk_not(def);
            }
            m_gmc->add(lit2expr(lit0), def);
            clause.reset();
            tail.reset();
        }
        // short circuit for equivalences:
        else if (clause.empty() && tail.empty() && 
                 i + 5 < updates.size() && 
                 updates[i] == ~updates[i + 3] &&
                 updates[i + 1] == ~updates[i + 4] && 
                 updates[i + 2] == sat::null_literal && 
                 updates[i + 5] == sat::null_literal) {
            sat::literal r = ~updates[i+1];
            if (l.sign()) { 
                l.neg(); 
                r.neg(); 
            }
            m_gmc->add(lit2expr(l), lit2expr(r));
            i += 5;
        }
        else {
            clause.push_back(l);
        }
    }
}
 
model_converter* sat2goal::mc::translate(ast_translation& translator) {
    mc* result = alloc(mc, translator.to());
    result->m_smc.copy(m_smc);
    result->m_gmc = m_gmc ? dynamic_cast<generic_model_converter*>(m_gmc->translate(translator)) : nullptr;
    for (app* e : m_var2expr) {
        result->m_var2expr.push_back(translator(e));
    }
    return result;
}

void sat2goal::mc::collect(ast_pp_util& visitor) {
    flush_gmc();
    if (m_gmc) m_gmc->collect(visitor);
}

void sat2goal::mc::display(std::ostream& out) {
    flush_gmc();
    if (m_gmc) m_gmc->display(out);
}

void sat2goal::mc::get_units(obj_map<expr, bool>& units) {
    flush_gmc();
    if (m_gmc) m_gmc->get_units(units);
}


void sat2goal::mc::operator()(model_ref & md) {
    model_evaluator ev(*md);
    ev.set_model_completion(false);
    
    // create a SAT model using md
    sat::model sat_md;
    expr_ref val(m);
    VERIFY(!m_var2expr.empty());
    for (expr * atom : m_var2expr) {
        if (!atom) {
            sat_md.push_back(l_undef);
            continue;
        }
        ev(atom, val);
        if (m.is_true(val)) 
            sat_md.push_back(l_true);
        else if (m.is_false(val))
            sat_md.push_back(l_false);
        else 
            sat_md.push_back(l_undef);
    }
    
    // apply SAT model converter
    m_smc(sat_md);
            
    // register value of non-auxiliary boolean variables back into md
    unsigned sz = m_var2expr.size();
    for (sat::bool_var v = 0; v < sz; v++) {
        app * atom = m_var2expr.get(v);
        if (atom && is_uninterp_const(atom)) {
            func_decl * d = atom->get_decl();
            lbool new_val = sat_md[v];
            if (new_val == l_true)
                md->register_decl(d, m.mk_true());
            else if (new_val == l_false)
                md->register_decl(d, m.mk_false());
        }
    }    
    // apply externalized model converter
    if (m_gmc) (*m_gmc)(md);
    TRACE("sat_mc", tout << "after sat_mc\n"; model_v2_pp(tout, *md););
}


void sat2goal::mc::operator()(expr_ref& fml) {
    flush_gmc();
    if (m_gmc) (*m_gmc)(fml);
}

void sat2goal::mc::insert(sat::bool_var v, app * atom, bool aux) {
    SASSERT(!m_var2expr.get(v, nullptr));
    m_var2expr.reserve(v + 1);
    m_var2expr.set(v, atom);
    if (aux) {
        SASSERT(is_uninterp_const(atom));
        SASSERT(m.is_bool(atom));
        if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
        m_gmc->hide(atom->get_decl());
    }
}

expr_ref sat2goal::mc::lit2expr(sat::literal l) {
    if (!m_var2expr.get(l.var())) {
        app* aux = m.mk_fresh_const(0, m.mk_bool_sort());
        m_var2expr.set(l.var(), aux);
        if (!m_gmc) m_gmc = alloc(generic_model_converter, m, "sat2goal");
        m_gmc->hide(aux->get_decl());
    }
    VERIFY(m_var2expr.get(l.var()));
    expr_ref result(m_var2expr.get(l.var()), m);
    if (l.sign()) {
        result = m.mk_not(result);
    }
    return result;
}


struct sat2goal::imp {

    typedef mc sat_model_converter;

    ast_manager &           m;
    expr_ref_vector         m_lit2expr;
    unsigned long long      m_max_memory;
    bool                    m_learned;
    
    imp(ast_manager & _m, params_ref const & p):m(_m), m_lit2expr(m) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        m_learned        = p.get_bool("learned", false);
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    }

    void checkpoint() {
        if (m.canceled())
            throw tactic_exception(m.limit().get_cancel_msg());
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
    }

    expr * lit2expr(ref<mc>& mc, sat::literal l) {
        if (!m_lit2expr.get(l.index())) {
            SASSERT(m_lit2expr.get((~l).index()) == 0);
            app* aux = mc ? mc->var2expr(l.var()) : nullptr;
            if (!aux) {
                aux = m.mk_fresh_const(0, m.mk_bool_sort());
                if (mc) {
                    mc->insert(l.var(), aux, true);
                }
            }
            sat::literal lit(l.var(), false);
            m_lit2expr.set(lit.index(), aux);
            m_lit2expr.set((~lit).index(), m.mk_not(aux));
        }        
        return m_lit2expr.get(l.index());
    }

    void assert_pb(ref<mc>& mc, goal& r, sat::ba_solver::pb const& p) {
        pb_util pb(m);
        ptr_buffer<expr> lits;
        vector<rational> coeffs;
        for (auto const& wl : p) {
            lits.push_back(lit2expr(mc, wl.second));
            coeffs.push_back(rational(wl.first));
        }
        rational k(p.k());
        expr_ref fml(pb.mk_ge(p.size(), coeffs.c_ptr(), lits.c_ptr(), k), m);
        
        if (p.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(mc, p.lit()), fml);            
        }
        r.assert_expr(fml);
    }

    void assert_card(ref<mc>& mc, goal& r, sat::ba_solver::card const& c) {
        pb_util pb(m);
        ptr_buffer<expr> lits;
        for (sat::literal l : c) {
            lits.push_back(lit2expr(mc, l));
        }
        expr_ref fml(pb.mk_at_least_k(c.size(), lits.c_ptr(), c.k()), m);
        
        if (c.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(mc, c.lit()), fml);            
        }
        r.assert_expr(fml);
    }

    void assert_xor(ref<mc>& mc, goal & r, sat::ba_solver::xr const& x) {
        ptr_buffer<expr> lits;
        for (sat::literal l : x) {
            lits.push_back(lit2expr(mc, l));
        }
        expr_ref fml(m.mk_xor(x.size(), lits.c_ptr()), m);
        
        if (x.lit() != sat::null_literal) {
            fml = m.mk_eq(lit2expr(mc, x.lit()), fml);            
        }
        r.assert_expr(fml);
    }

    void assert_clauses(ref<mc>& mc, sat::solver const & s, sat::clause_vector const& clauses, goal & r, bool asserted) {
        ptr_buffer<expr> lits;
        for (sat::clause* cp : clauses) {
            checkpoint();
            lits.reset();
            sat::clause const & c = *cp;
            if (asserted || m_learned || c.glue() <= s.get_config().m_gc_small_lbd) {
                for (sat::literal l : c) {
                    lits.push_back(lit2expr(mc, l));
                }
                r.assert_expr(m.mk_or(lits.size(), lits.c_ptr()));
            }
        }
    }

    sat::ba_solver* get_ba_solver(sat::solver const& s) {
        return dynamic_cast<sat::ba_solver*>(s.get_extension());
    }

    void operator()(sat::solver & s, atom2bool_var const & map, goal & r, ref<mc> & mc) {
        if (s.inconsistent()) {
            r.assert_expr(m.mk_false());
            return;
        }
        if (r.models_enabled() && !mc) {
            mc = alloc(sat_model_converter, m);
        }
        if (mc) mc->flush_smc(s, map);
        m_lit2expr.resize(s.num_vars() * 2);
        map.mk_inv(m_lit2expr);
        // collect units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            checkpoint();
            r.assert_expr(lit2expr(mc, s.trail_literal(i)));
        }

        // collect binary clauses
        svector<sat::solver::bin_clause> bin_clauses;
        s.collect_bin_clauses(bin_clauses, m_learned);
        for (sat::solver::bin_clause const& bc : bin_clauses) {
            checkpoint();
            r.assert_expr(m.mk_or(lit2expr(mc, bc.first), lit2expr(mc, bc.second)));
        }
        // collect clauses
        assert_clauses(mc, s, s.clauses(), r, true);

        sat::ba_solver* ext = get_ba_solver(s);
        if (ext) {
            for (auto* c : ext->constraints()) {
                switch (c->tag()) {
                case sat::ba_solver::card_t: 
                    assert_card(mc, r, c->to_card());
                    break;
                case sat::ba_solver::pb_t: 
                    assert_pb(mc, r, c->to_pb());
                    break;
                case sat::ba_solver::xr_t: 
                    assert_xor(mc, r, c->to_xr());
                    break;
                }
            }
        }
    }

    void add_clause(ref<mc>& mc, sat::literal_vector const& lits, expr_ref_vector& lemmas) {
        expr_ref_vector lemma(m);
        for (sat::literal l : lits) {
            expr* e = lit2expr(mc, l);
            if (!e) return;
            lemma.push_back(e);
        }
        lemmas.push_back(mk_or(lemma));
    }

    void add_clause(ref<mc>& mc, sat::clause const& c, expr_ref_vector& lemmas) {
        expr_ref_vector lemma(m);
        for (sat::literal l : c) {
            expr* e = lit2expr(mc, l);
            if (!e) return;
            lemma.push_back(e);
        }
        lemmas.push_back(mk_or(lemma));
    }

};

sat2goal::sat2goal():m_imp(nullptr) {
}

void sat2goal::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("learned", CPK_BOOL, "(default: false) collect also learned clauses.");
}

struct sat2goal::scoped_set_imp {
    sat2goal * m_owner; 
    scoped_set_imp(sat2goal * o, sat2goal::imp * i):m_owner(o) {
        m_owner->m_imp = i;        
    }
    ~scoped_set_imp() {
        m_owner->m_imp = nullptr;
    }
};

void sat2goal::operator()(sat::solver & t, atom2bool_var const & m, params_ref const & p, 
                          goal & g, ref<mc> & mc) {
    imp proc(g.m(), p);
    scoped_set_imp set(this, &proc);
    proc(t, m, g, mc);
}


