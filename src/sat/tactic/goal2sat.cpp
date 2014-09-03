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
#include"goal2sat.h"
#include"ast_smt2_pp.h"
#include"ref_util.h"
#include"cooperate.h"
#include"filter_model_converter.h"
#include"model_evaluator.h"
#include"for_each_expr.h"
#include"model_v2_pp.h"
#include"tactic.h"
#include"ast_pp.h"
#include<strstream>

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
    volatile bool               m_cancel;
    expr_ref_vector             m_trail;
    bool                        m_default_external;
    
    imp(ast_manager & _m, params_ref const & p, sat::solver & s, atom2bool_var & map, dep2asm_map& dep2asm, bool default_external):
        m(_m),
        m_solver(s),
        m_map(map),
        m_dep2asm(dep2asm),
        m_trail(m),
        m_default_external(default_external) {
        updt_params(p);
        m_cancel = false;
        m_true = sat::null_bool_var;
    }
        
    void updt_params(params_ref const & p) {
        m_ite_extra       = p.get_bool("ite_extra", true);
        m_max_memory      = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    }

    void throw_op_not_handled(std::string const& s) {
        std::string s0 = "operator " + s + " not supported, apply simplifier before invoking translator";
        throw tactic_exception(s0.c_str());
    }
    
    void mk_clause(sat::literal l) {
        TRACE("goal2sat", tout << "mk_clause: " << l << "\n";);
        m_solver.mk_clause(1, &l);
    }

    void mk_clause(sat::literal l1, sat::literal l2) {
        TRACE("goal2sat", tout << "mk_clause: " << l1 << " " << l2 << "\n";);
        m_solver.mk_clause(l1, l2);
    }

    void mk_clause(sat::literal l1, sat::literal l2, sat::literal l3) {
        TRACE("goal2sat", tout << "mk_clause: " << l1 << " " << l2 << " " << l3 << "\n";);
        m_solver.mk_clause(l1, l2, l3);
    }

    void mk_clause(unsigned num, sat::literal * lits) {
        TRACE("goal2sat", tout << "mk_clause: "; for (unsigned i = 0; i < num; i++) tout << lits[i] << " "; tout << "\n";);
        m_solver.mk_clause(num, lits);
    }

    sat::bool_var mk_true() {
        // create fake variable to represent true;
        if (m_true == sat::null_bool_var) {
            m_true = m_solver.mk_var();
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
                TRACE("goal2sat", tout << "new_var: " << v << "\n" << mk_ismt2_pp(t, m) << "\n";);
            }
        }
        else {
            SASSERT(v != sat::null_bool_var);
            l = sat::literal(v, sign);
        }
        SASSERT(l != sat::null_literal);
        if (root)
            mk_clause(l);
        else
            m_result_stack.push_back(l);
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
            convert_atom(t, root, sign);
            return true;
        }
        switch (to_app(t)->get_decl_kind()) {
        case OP_NOT:
        case OP_OR:
        case OP_IFF:
            m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
            return false;
        case OP_ITE:
        case OP_EQ:
            if (m.is_bool(to_app(t)->get_arg(1))) {
                m_frame_stack.push_back(frame(to_app(t), root, sign, 0));
                return false;
            }
            convert_atom(t, root, sign);
            return true;
        case OP_AND:
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
                m_result_stack.reset();
            }
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

    void convert_iff(app * t, bool root, bool sign) {
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

    void convert(app * t, bool root, bool sign) {
        SASSERT(t->get_family_id() == m.get_basic_family_id());
        switch (to_app(t)->get_decl_kind()) {
        case OP_OR:
            convert_or(t, root, sign);
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
    
    void process(expr * n) {
        TRACE("goal2sat", tout << "converting: " << mk_ismt2_pp(n, m) << "\n";);
        if (visit(n, true, false)) {
            SASSERT(m_result_stack.empty());
            return;
        }
        while (!m_frame_stack.empty()) {
        loop:
            cooperate("goal2sat");
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            frame & fr = m_frame_stack.back();
            app * t    = fr.m_t;
            bool root  = fr.m_root;
            bool sign  = fr.m_sign;
            TRACE("goal2sat_bug", tout << "result stack\n";
                  tout << mk_ismt2_pp(t, m) << " root: " << root << " sign: " << sign << "\n";
                  for (unsigned i = 0; i < m_result_stack.size(); i++) tout << m_result_stack[i] << " ";
                  tout << "\n";);
            if (fr.m_idx == 0 && process_cached(t, root, sign)) {
                m_frame_stack.pop_back();
                continue;
            }
            if (m.is_not(t)) {
                m_frame_stack.pop_back();
                visit(t->get_arg(0), root, !sign);
                continue;
            }
            unsigned num = t->get_num_args();
            while (fr.m_idx < num) {
                expr * arg = t->get_arg(fr.m_idx);
                fr.m_idx++;
                if (!visit(arg, false, false))
                    goto loop;
            }
            TRACE("goal2sat_bug", tout << "converting\n";
                  tout << mk_ismt2_pp(t, m) << " root: " << root << " sign: " << sign << "\n";
                  for (unsigned i = 0; i < m_result_stack.size(); i++) tout << m_result_stack[i] << " ";
                  tout << "\n";);
            convert(t, root, sign);
            m_frame_stack.pop_back();
        }
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
                for (unsigned i = 0; i < deps.size(); ++i) {
                    expr * d = deps[i];
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
            TRACE("sat", tout << mk_pp(f, m) << "\n";);
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

    void set_cancel(bool f) { m_cancel = f; }
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
            case OP_AND:
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

goal2sat::goal2sat():m_imp(0) {
}

void goal2sat::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("ite_extra", CPK_BOOL, "(default: true) add redundant clauses (that improve unit propagation) when encoding if-then-else formulas");
}

struct goal2sat::scoped_set_imp {
    goal2sat * m_owner; 
    scoped_set_imp(goal2sat * o, goal2sat::imp * i):m_owner(o) {
        #pragma omp critical (goal2sat)
        {
            m_owner->m_imp = i;
        }
    }
    ~scoped_set_imp() {
        #pragma omp critical (goal2sat)
        {
            m_owner->m_imp = 0;
        }
    }
};

void goal2sat::operator()(goal const & g, params_ref const & p, sat::solver & t, atom2bool_var & m, dep2asm_map& dep2asm, bool default_external) {
    imp proc(g.m(), p, t, m, dep2asm, default_external);
    scoped_set_imp set(this, &proc);
    proc(g);
}

void goal2sat::set_cancel(bool f) {
    #pragma omp critical (goal2sat)
    {
        if (m_imp)
            m_imp->set_cancel(f);
    }
}

struct sat2goal::imp {

    // Wrapper for sat::model_converter: converts it into an "AST level" model_converter.
    class sat_model_converter : public model_converter {
        sat::model_converter        m_mc;
        // TODO: the following mapping is storing a lot of useless information, and may be a performance bottleneck.
        // We need to save only the expressions associated with variables that occur in m_mc.
        // This information may be stored as a vector of pairs.
        // The mapping is only created during the model conversion.
        expr_ref_vector             m_var2expr;
        ref<filter_model_converter> m_fmc; // filter for eliminating fresh variables introduced in the assertion-set --> sat conversion
        
        sat_model_converter(ast_manager & m):
            m_var2expr(m) {
        }
        
    public:
        sat_model_converter(ast_manager & m, sat::solver const & s):m_var2expr(m) {
            m_mc.copy(s.get_model_converter());
            m_fmc = alloc(filter_model_converter, m);
        }
        
        ast_manager & m() { return m_var2expr.get_manager(); }
        
        void insert(expr * atom, bool aux) {
            m_var2expr.push_back(atom);
            if (aux) {
                SASSERT(is_uninterp_const(atom));
                SASSERT(m().is_bool(atom));
                m_fmc->insert(to_app(atom)->get_decl());
            }
        }
        
        virtual void operator()(model_ref & md, unsigned goal_idx) {
            SASSERT(goal_idx == 0);
            TRACE("sat_mc", tout << "before sat_mc\n"; model_v2_pp(tout, *md); display(tout););
            // REMARK: potential problem
            // model_evaluator can't evaluate quantifiers. Then,
            // an eliminated variable that depends on a quantified expression can't be recovered.
            // A similar problem also affects any model_converter that uses elim_var_model_converter.
            //
            // Possible solution:
            //   model_converters reject any variable elimination that depends on a quantified expression.
            
            model_evaluator ev(*md);
            ev.set_model_completion(false);
            
            // create a SAT model using md
            sat::model sat_md;
            unsigned sz = m_var2expr.size();
            expr_ref val(m());
            for (sat::bool_var v = 0; v < sz; v++) {
                expr * atom = m_var2expr.get(v);
                ev(atom, val);
                if (m().is_true(val)) 
                    sat_md.push_back(l_true);
                else if (m().is_false(val))
                    sat_md.push_back(l_false);
                else 
                    sat_md.push_back(l_undef);
            }
            
            // apply SAT model converter
            m_mc(sat_md);
            
            // register value of non-auxiliary boolean variables back into md
            sz = m_var2expr.size();
            for (sat::bool_var v = 0; v < sz; v++) {
                expr * atom = m_var2expr.get(v);
                if (is_uninterp_const(atom)) {
                    func_decl * d = to_app(atom)->get_decl();
                    lbool new_val = sat_md[v];
                    if (new_val == l_true)
                        md->register_decl(d, m().mk_true());
                    else if (new_val == l_false)
                        md->register_decl(d, m().mk_false());
                }
            }
            
            // apply filter model converter
            (*m_fmc)(md);
            TRACE("sat_mc", tout << "after sat_mc\n"; model_v2_pp(tout, *md););
        }
        
        virtual model_converter * translate(ast_translation & translator) {
            sat_model_converter * res = alloc(sat_model_converter, translator.to());
            res->m_fmc = static_cast<filter_model_converter*>(m_fmc->translate(translator));
            unsigned sz = m_var2expr.size();
            for (unsigned i = 0; i < sz; i++) 
                res->m_var2expr.push_back(translator(m_var2expr.get(i)));
            return res;
        }
        
        void display(std::ostream & out) {
            out << "(sat-model-converter\n";
            m_mc.display(out);
            sat::bool_var_set vars;
            m_mc.collect_vars(vars);
            out << "(atoms";
            unsigned sz = m_var2expr.size();
            for (unsigned i = 0; i < sz; i++) {
                if (vars.contains(i)) {
                    out << "\n (" << i << "\n  " << mk_ismt2_pp(m_var2expr.get(i), m(), 2) << ")";
                }
            }
            out << ")\n";
            m_fmc->display(out);
            out << ")\n";
        }
    };

    ast_manager &           m;
    expr_ref_vector         m_lit2expr;
    unsigned long long      m_max_memory;
    bool                    m_learned;
    volatile bool           m_cancel;
    
    imp(ast_manager & _m, params_ref const & p):m(_m), m_lit2expr(m), m_cancel(false) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        m_learned        = p.get_bool("learned", false);
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    }

    void checkpoint() {
        if (m_cancel)
            throw tactic_exception(TACTIC_CANCELED_MSG);
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
    }

    void init_lit2expr(sat::solver const & s, atom2bool_var const & map, model_converter_ref & mc, bool produce_models) {
        ref<sat_model_converter> _mc;
        if (produce_models)
            _mc = alloc(sat_model_converter, m, s);
        unsigned num_vars = s.num_vars();
        m_lit2expr.resize(num_vars * 2);
        map.mk_inv(m_lit2expr);
        sort * b = m.mk_bool_sort();
        for (sat::bool_var v = 0; v < num_vars; v++) {
            checkpoint();
            sat::literal l(v, false);
            if (m_lit2expr.get(l.index()) == 0) {
                SASSERT(m_lit2expr.get((~l).index()) == 0);
                app * aux = m.mk_fresh_const(0, b);
                if (_mc)
                    _mc->insert(aux, true);
                m_lit2expr.set(l.index(), aux);
                m_lit2expr.set((~l).index(), m.mk_not(aux));
            }
            else {
                if (_mc)
                    _mc->insert(m_lit2expr.get(l.index()), false);
                SASSERT(m_lit2expr.get((~l).index()) != 0);
            }
        }
        mc = _mc.get();
    }

    expr * lit2expr(sat::literal l) {
        return m_lit2expr.get(l.index());
    }

    void assert_clauses(sat::clause * const * begin, sat::clause * const * end, goal & r) {
        ptr_buffer<expr> lits;
        for (sat::clause * const * it = begin; it != end; it++) {
            checkpoint();
            lits.reset();
            sat::clause const & c = *(*it);
            unsigned sz = c.size();
            for (unsigned i = 0; i < sz; i++) {
                lits.push_back(lit2expr(c[i]));
            }
            r.assert_expr(m.mk_or(lits.size(), lits.c_ptr()));
        }
    }

    void operator()(sat::solver const & s, atom2bool_var const & map, goal & r, model_converter_ref & mc) {
        if (s.inconsistent()) {
            r.assert_expr(m.mk_false());
            return;
        }
        init_lit2expr(s, map, mc, r.models_enabled());
        // collect units
        unsigned num_vars = s.num_vars();
        for (sat::bool_var v = 0; v < num_vars; v++) {
            checkpoint();
            switch (s.value(v)) {
            case l_true:
                r.assert_expr(lit2expr(sat::literal(v, false)));
                break;
            case l_false:
                r.assert_expr(lit2expr(sat::literal(v, true)));
                break;
            case l_undef:
                break;
            }
        }
        // collect binary clauses
        svector<sat::solver::bin_clause> bin_clauses;
        s.collect_bin_clauses(bin_clauses, m_learned);
        svector<sat::solver::bin_clause>::iterator it  = bin_clauses.begin();
        svector<sat::solver::bin_clause>::iterator end = bin_clauses.end();
        for (; it != end; ++it) {
            checkpoint();
            r.assert_expr(m.mk_or(lit2expr(it->first), lit2expr(it->second)));
        }
        // collect clauses
        assert_clauses(s.begin_clauses(), s.end_clauses(), r);
        if (m_learned)
            assert_clauses(s.begin_learned(), s.end_learned(), r);
    }

    void set_cancel(bool f) { m_cancel = f; }
};

sat2goal::sat2goal():m_imp(0) {
}

void sat2goal::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    r.insert("learned", CPK_BOOL, "(default: false) collect also learned clauses.");
}

struct sat2goal::scoped_set_imp {
    sat2goal * m_owner; 
    scoped_set_imp(sat2goal * o, sat2goal::imp * i):m_owner(o) {
        #pragma omp critical (sat2goal)
        {
            m_owner->m_imp = i;
        }
    }
    ~scoped_set_imp() {
        #pragma omp critical (sat2goal)
        {
            m_owner->m_imp = 0;
        }
    }
};

void sat2goal::operator()(sat::solver const & t, atom2bool_var const & m, params_ref const & p, 
                          goal & g, model_converter_ref & mc) {
    imp proc(g.m(), p);
    scoped_set_imp set(this, &proc);
    proc(t, m, g, mc);
}

void sat2goal::set_cancel(bool f) {
    #pragma omp critical (sat2goal)
    {
        if (m_imp)
            m_imp->set_cancel(f);
    }
}
