/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_horn_ineq_def.h

Abstract:

    A*x <= b + D*x, coefficients to A and D are non-negative, 
    D is a diagonal matrix.
    Coefficients to b may have both signs.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-18

Revision History:

--*/

#ifndef _THEORY_HORN_INEQ_DEF_H_
#define _THEORY_HORN_INEQ_DEF_H_
#include "theory_horn_ineq.h"
#include "ast_pp.h"
#include "smt_context.h"

namespace smt {

    /**
       A clause represents an inequality of the form
       
       v1*c1 + v2*c2 + .. + v_n*c_n + w <= v*c 

       where 
       - m_vars: [v1,v2,...,v_n]
       - m_coeffs: [c1,c2,...,c_n]
       - m_var: v  
       - m_coeff: c 
       - m_weight: w

     */
    template<typename Ext>
    class theory_horn_ineq<Ext>::clause {
        vector<rational>    m_coeffs;  // coefficients of body.
        svector<th_var>     m_vars;    // variables of body.
        rational            m_coeff;   // coefficient of head.
        th_var              m_var;     // head variable.
        numeral             m_weight;  // constant to add
        literal             m_explanation;
        bool                m_enabled;
    public:
        clause(unsigned sz, rational const* coeffs, th_var const* vars, 
               rational const& coeff, th_var var, numeral const& w, 
               const literal& ex):
            m_coeffs(sz, coeffs),
            m_vars(sz, vars),
            m_coeff(coeff),
            m_var(var),
            m_weight(w),
            m_explanation(ex),
            m_enabled(false) {
            DEBUG_CODE(
                {
                    for (unsigned i = 0; i < size(); ++i) {
                        SASSERT(coeffs[i].is_pos());
                    }
                    SASSERT(coeff.is_pos());
                });
        }

        th_var vars(unsigned i) const { return m_vars[i]; }
        rational const& coeffs(unsigned i) const { return m_coeffs[i]; }
        th_var var() const { return m_var; }
        rational const& coeff() const { return m_coeff; }        
        const numeral & get_weight() const { return m_weight;  }        
        const literal & get_explanation() const { return m_explanation; }    
        bool is_enabled() const { return m_enabled; }
        unsigned size() const { return m_vars.size(); }

        void enable()  { m_enabled = true;  }        
        void disable() { m_enabled = false; }

        void display(std::ostream& out) const {
            out << (is_enabled()?"+ ":"- ");
            for (unsigned i = 0; i < size(); ++i) {
                if (i > 0 && coeffs(i).is_pos()) {
                    out << " + ";
                }
                display(out, coeffs(i), vars(i));
            }
            if (!get_weight().is_zero()) {
                out << " + " << get_weight();
            }
            display(out << " <= ", coeff(), var());
            out << "\n";
        }

    private:

        void display(std::ostream& out, rational const& c, th_var v) const {
            if (!c.is_one()) {
                out << c << "*";
            }
            out << "v" << v;                
        }
    };

    template<typename Ext>
    class theory_horn_ineq<Ext>::assignment_trail {
        th_var    m_var;
        numeral   m_old_value;
    public:
        assignment_trail(th_var v, const numeral & val):
            m_var(v),
            m_old_value(val) {}
        th_var get_var() const { return m_var; }
        const numeral & get_old_value() const {  return m_old_value; }        
    };

    template<typename Ext>
    class theory_horn_ineq<Ext>::parent_trail {
        th_var    m_var;
        clause_id m_old_value;
    public:
        parent_trail(th_var v, clause_id val):
            m_var(v),
            m_old_value(val) {}
        th_var get_var() const { return m_var; }
        clause_id get_old_value() const {  return m_old_value; }        
    };
    

    template<typename Ext>
    class theory_horn_ineq<Ext>::graph : private Ext {
        
        typedef vector<assignment_trail> assignment_stack;
        typedef vector<parent_trail>     parent_stack;        
        typedef unsigned_vector clause_id_vector;

        struct stats {
            unsigned m_propagation_cost;

            void reset() { 
                memset(this, 0, sizeof(*this));
            }
        };

        struct scope {
            unsigned m_clauses_lim;
            unsigned m_enabled_clauses_lim;
            unsigned m_assignment_lim;
            unsigned m_parent_lim;
            scope(unsigned e, unsigned enabled, unsigned alim, unsigned plim):
                m_clauses_lim(e),
                m_enabled_clauses_lim(enabled),
                m_assignment_lim(alim),
                m_parent_lim(plim) {
            }
        };

        stats                    m_stats;
        vector<clause>           m_clauses;
        vector<numeral>          m_assignment;       // per var
        clause_id_vector         m_parent;           // per var
        assignment_stack         m_assignment_stack; // stack for restoring the assignment
        parent_stack             m_parent_stack;     // stack for restoring parents
        clause_id_vector         m_enabled_clauses;
        vector<clause_id_vector> m_out_clauses; // use-list for clauses.
        vector<clause_id_vector> m_in_clauses;  // clauses that have variable in head.
        // forward reachability
        unsigned_vector          m_onstack;
        unsigned                 m_ts;
        unsigned_vector          m_todo;
        literal_vector           m_lits;
        vector<rational>         m_coeffs;
        th_var                   m_zero;
        clause_id                m_unsat_clause;
        svector<scope>           m_trail_stack;


    public:

        graph(): m_ts(0), m_zero(null_theory_var), m_unsat_clause(null_clause_id) {}
        
        void reset() {
            m_clauses           .reset();
            m_assignment        .reset();
            m_parent            .reset();
            m_assignment_stack  .reset();
            m_parent_stack      .reset();
            m_out_clauses       .reset();
            m_in_clauses        .reset();
            m_enabled_clauses   .reset();
            m_onstack           .reset();
            m_ts            = 0;
            m_lits              .reset();
            m_trail_stack       .reset();
            m_unsat_clause  = null_clause_id;
        }


        void traverse_neg_cycle1(bool /*stronger_lemmas*/) {
            TRACE("horn_ineq", display(tout););
            SASSERT(!m_enabled_clauses.empty());
            clause_id id = m_unsat_clause;
            SASSERT(id != null_clause_id);
            SASSERT(!is_feasible(m_clauses[id]));
            clause_id_vector todo;
            vector<rational> muls;
            todo.push_back(id);
            muls.push_back(rational(1));
            u_map<rational> lits;
            while (!todo.empty()) {
                id = todo.back();
                rational mul  = muls.back();
                todo.pop_back();
                muls.pop_back();
                clause const& cl = m_clauses[id];
                literal lit = cl.get_explanation();
                if (lit != null_literal) {
                    lits.insert_if_not_there2(id, rational(0))->get_data().m_value += mul;
                }
                for (unsigned i = 0; i < cl.size(); ++i) {
                    id = m_parent[cl.vars(i)];
                    if (id != null_clause_id) {
                        todo.push_back(id);
                        muls.push_back(mul*cl.coeffs(i));
                    }
                }
            }
            u_map<rational>::iterator it = lits.begin(), end = lits.end();
            m_lits.reset();
            m_coeffs.reset();
            for (; it != end; ++it) {
                m_lits.push_back(m_clauses[it->m_key].get_explanation());
                m_coeffs.push_back(it->m_value);
            }
            
            // TODO: use topological sort to tune traversal of parents to linear.
            // (current traversal can be exponential).
            // TODO: negative cycle traversal with inline resolution to find 
            // stronger conflict clauses.
            // follow heuristic used in theory_diff_logic_def.h:
        }

        unsigned get_num_clauses() const {
            return m_clauses.size();
        }

        literal_vector const& get_lits() const {
            return m_lits;
        }

        vector<rational> const& get_coeffs() const {
            return m_coeffs;
        }

        numeral get_assignment(th_var v) const {
            return m_assignment[v];
        }

        numeral eval_body(clause const& cl) const {
            numeral v(0);
            for (unsigned i = 0; i < cl.size(); ++i) {
                v += cl.coeffs(i)*m_assignment[cl.vars(i)];
            }
            v += cl.get_weight();
            return v;
        }

        numeral eval_body(clause_id id) const {
            return eval_body(m_clauses[id]);
        }

        numeral eval_head(clause_id id) const {
            return eval_head(m_clauses[id]);
        }

        numeral eval_head(clause const& cl) const {
            return cl.coeff()*m_assignment[cl.var()];
        }

        clause const& get_clause(clause_id id) const {
            return m_clauses[id];
        }

        void display_clause(std::ostream& out, clause_id id) const {
            if (id == null_clause_id) {
                out << "null\n";
            }
            else {
                m_clauses[id].display(out);
            }
        }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                display_clause(out, i);
            }
            for (unsigned i = 0; i < m_assignment.size(); ++i) {
                out << m_assignment[i] << "\n";
            }
        }

        void collect_statistics(::statistics& st) const {
            st.update("hi_propagation_cst", m_stats.m_propagation_cost);
        }

        void push() {
            m_trail_stack.push_back(scope(m_clauses.size(), m_enabled_clauses.size(), 
                                          m_assignment_stack.size(), m_parent_stack.size()));
        }

        void pop(unsigned num_scopes) {
            unsigned lvl           = m_trail_stack.size();
            SASSERT(num_scopes <= lvl);
            unsigned new_lvl       = lvl - num_scopes;
            scope & s              = m_trail_stack[new_lvl];
            // restore enabled clauses
            for (unsigned i = m_enabled_clauses.size(); i > s.m_enabled_clauses_lim; ) {
                --i;
                m_clauses[m_enabled_clauses[i]].disable();
            }
            m_enabled_clauses.shrink(s.m_enabled_clauses_lim);

            // restore assignment stack
            for (unsigned i = m_assignment_stack.size(); i > s.m_assignment_lim; ) {
                --i;
                m_assignment[m_assignment_stack[i].get_var()] = m_assignment_stack[i].get_old_value();
            }
            m_assignment_stack.shrink(s.m_assignment_lim);

            // restore parent stack
            for (unsigned i = m_parent_stack.size(); i > s.m_parent_lim; ) {
                --i;
                m_parent[m_parent_stack[i].get_var()] = m_parent_stack[i].get_old_value();
            }
            m_assignment_stack.shrink(s.m_assignment_lim);

            // restore clauses
            unsigned old_num_clauses = s.m_clauses_lim;
            unsigned num_clauses     = m_clauses.size();
            SASSERT(old_num_clauses <= num_clauses);
            unsigned to_delete     = num_clauses - old_num_clauses;
            for (unsigned i = 0; i < to_delete; i++) {
                const clause & cl = m_clauses.back();
                TRACE("horn_ineq", tout << "deleting clause:\n"; cl.display(tout););
                for (unsigned j = 0; j < cl.size(); ++j) {
                    m_out_clauses[cl.vars(j)].pop_back();
                }
                m_in_clauses[cl.var()].pop_back();
                m_clauses.pop_back();
            }
            m_trail_stack.shrink(new_lvl);
            SASSERT(check_invariant()); 
        }

        /**
           \brief Add clause z <= z and the assignment z := 0
           Then z cannot be incremented without causing a loop (and therefore a contradiction).
         */
        void set_to_zero(th_var z) {
            m_zero = z;
        }

        bool enable_clause(clause_id id) {
            if (id == null_clause_id) {
                return true;
            }
            clause& cl = m_clauses[id];
            bool r = true;
            if (!cl.is_enabled()) {
                cl.enable();
                if (!is_feasible(cl)) {
                    r = make_feasible(id);
                }
                m_enabled_clauses.push_back(id);
            }
            return r;
        }

        void init_var(th_var v) {
            unsigned sz = static_cast<unsigned>(v);
            while (m_assignment.size() <= sz) {
                m_assignment.push_back(Ext::m_minus_infty);
                m_out_clauses.push_back(clause_id_vector());
                m_in_clauses.push_back(clause_id_vector());
                m_parent.push_back(null_clause_id);
                m_onstack.push_back(0);
            }
            m_assignment[v] = Ext::m_minus_infty;
            SASSERT(m_out_clauses[v].empty());
            SASSERT(m_in_clauses[v].empty());
            SASSERT(check_invariant());
        }

        clause_id add_ineq(vector<std::pair<th_var, rational> > const& terms, numeral const& weight, literal l) {
            vector<rational> coeffs;
            svector<th_var>  vars;
            rational coeff(1);
            th_var var = null_theory_var;
            bool found_negative = false;
            for (unsigned i = 0; i < terms.size(); ++i) {
                rational const& r = terms[i].second;
                if (r.is_pos()) {
                    coeffs.push_back(terms[i].second);
                    vars.push_back(terms[i].first);
                }
                else if (found_negative) {
                    return null_clause_id;
                }
                else {
                    SASSERT(r.is_neg());
                    found_negative = true;
                    coeff = -r;
                    var = terms[i].first;
                }
            }
            if (!found_negative) {
                coeff = rational(1);
                var = m_zero;
            }
            if (!coeff.is_one()) {
                // so far just support unit coefficients on right.
                return null_clause_id;
            }
            clause_id id = m_clauses.size();
            m_clauses.push_back(clause(coeffs.size(), coeffs.c_ptr(), vars.c_ptr(), coeff, var, weight, l));
            for (unsigned i = 0; i < vars.size(); ++i) {
                m_out_clauses[vars[i]].push_back(id);
            }
            m_in_clauses[var].push_back(id);
            
            return id;
        }

        bool is_feasible() const {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                if (!is_feasible(m_clauses[i])) {
                    return false;
                }
            }            
            return true;
        }

    private:

        bool check_invariant() {
            return true;
        }

        /**
           assignments are fully retraced on backtracking. 
           This is not always necessary.
        */

        void acc_assignment(th_var v, const numeral & inc) {
            m_assignment_stack.push_back(assignment_trail(v, m_assignment[v]));
            m_assignment[v] += inc;
        }

        void acc_parent(th_var v, clause_id parent) {
            m_parent[v] = parent;
            m_parent_stack.push_back(parent_trail(v, parent));
        }
        
        numeral get_delta(const clause & cl) const {
            SASSERT(cl.coeff().is_one() && "Not yet support for non-units");
            return eval_body(cl) - eval_head(cl);
        }
        
        void set_onstack(th_var v) {
            SASSERT(m_ts != 0);
            m_onstack[v] = m_ts;
        }

        void reset_onstack(th_var v) {
            m_onstack[v] = 0;
        }

        bool is_onstack(th_var v) const { 
            return m_onstack[v] == m_ts;
        }

        void inc_ts() {
            m_ts++;
            if (m_ts == 0) {
                m_ts++;
                m_onstack.reset();
                m_onstack.resize(m_assignment.size(), 0);
            }
        }

        // Make the assignment feasible. An assignment is feasible if
        // Forall clause cl. eval_body(cl) <= eval_head(cl)
        // 
        // This method assumes that if the assignment is not feasible, 
        // then the only infeasible clause is the last added clause.
        //
        // Traversal is by naive DFS search.
        // 
        bool make_feasible(clause_id id) {
            SASSERT(is_almost_feasible(id));
            SASSERT(!m_clauses.empty());
            SASSERT(!is_feasible(m_clauses[id]));
            const clause & cl0 = m_clauses[id];
            inc_ts();
            for (unsigned i = 0; i < cl0.size(); ++i) {
                set_onstack(cl0.vars(i));
            }
            th_var source = cl0.var();
            numeral delta = get_delta(cl0);
            acc_parent(source, id);
            SASSERT(delta.is_pos());
            acc_assignment(source, delta);
            m_todo.reset();
            m_todo.push_back(source);
            
            TRACE("horn_ineq", cl0.display(tout););
            
            do {
                ++m_stats.m_propagation_cost;
                
                typename clause_id_vector::iterator it  = m_out_clauses[source].begin();
                typename clause_id_vector::iterator end = m_out_clauses[source].end();
                for (; it != end; ++it) {
                    clause & cl = m_clauses[*it];
                    if (!cl.is_enabled()) {
                        continue;
                    }
                    delta = get_delta(cl);
                    
                    if (delta.is_pos()) {
                        TRACE("horn_ineq", cl.display(tout););
                        th_var target   = cl.var();
                        if (is_onstack(target)) {
                            m_unsat_clause = *it;
                            return false;
                        }
                        else {
                            acc_assignment(target, delta);
                            acc_parent(target, *it);
                            m_todo.push_back(target);
                        }
                    }
                }    
                set_onstack(source);
                source = m_todo.back();
                // pop stack until there is a new variable to process.
                while (is_onstack(source)) {
                    m_todo.pop_back();
                    reset_onstack(source);
                    if (m_todo.empty()) {
                        break;
                    }
                    source = m_todo.back();
                }                
            }
            while (!m_todo.empty());
            return true;
        }

        bool is_almost_feasible(clause_id id) const {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                if (id != static_cast<clause_id>(i) && !is_feasible(m_clauses[i])) {
                    return false;
                }
            }
            return true;
        }

        bool is_feasible(const clause & cl) const {
            return !cl.is_enabled() || get_delta(cl).is_nonpos();
        }

    };

    template<typename Ext>
    theory_horn_ineq<Ext>::theory_horn_ineq(ast_manager& m):
            theory(m.mk_family_id("arith")),
            a(m),
            m_arith_eq_adapter(*this, m_params, a),
            m_zero_int(null_theory_var),
            m_zero_real(null_theory_var),
            m_graph(0),
            m_asserted_qhead(0),
            m_agility(0.5),
            m_lia(false),
            m_lra(false),
            m_non_horn_ineq_exprs(false),
            m_test(m),
            m_factory(0) {
        m_graph = alloc(graph);
    }            

    template<typename Ext>
    theory_horn_ineq<Ext>::~theory_horn_ineq() {
        reset_eh();
        dealloc(m_graph);
    }                

    template<typename Ext>
    std::ostream& theory_horn_ineq<Ext>::atom::display(theory_horn_ineq const& th, std::ostream& out) const { 
        context& ctx = th.get_context();
        lbool asgn = ctx.get_assignment(m_bvar);
        bool sign = (l_undef == asgn) || m_true;
        return out << literal(m_bvar, sign) << " " << mk_pp(ctx.bool_var2expr(m_bvar), th.get_manager()) << " ";         
        if (l_undef == asgn) {
            out << "unassigned\n";
        }
        else {
            th.m_graph->display_clause(out, get_asserted_edge());
        }
        return out;
    }

    template<typename Ext>
    theory_var theory_horn_ineq<Ext>::mk_var(enode* n) {
        th_var v = theory::mk_var(n);
        m_graph->init_var(v);
        get_context().attach_th_var(n, this, v);
        return v;
    }
    
    template<typename Ext>
    theory_var theory_horn_ineq<Ext>::mk_var(expr* n) {
        context & ctx = get_context();
        enode* e = 0;
        th_var v = null_theory_var;
        m_lia |= a.is_int(n);
        m_lra |= a.is_real(n);
        if (!is_app(n)) {
            return v;
        }
        if (ctx.e_internalized(n)) {
            e = ctx.get_enode(n);
            v = e->get_th_var(get_id());
        }
        else {
            ctx.internalize(n, false);
            e = ctx.get_enode(n);
        }
        if (v == null_theory_var) {
            v = mk_var(e);
        }      
        if (is_interpreted(to_app(n))) {
            found_non_horn_ineq_expr(n);
        }
        return v;
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::reset_eh() {
        m_graph            ->reset();
        m_zero_int          = null_theory_var;
        m_zero_real         = null_theory_var;
        m_atoms            .reset();
        m_asserted_atoms   .reset();
        m_stats            .reset();
        m_scopes           .reset();
        m_asserted_qhead        = 0;
        m_agility               = 0.5;
        m_lia = false;
        m_lra = false;
        m_non_horn_ineq_exprs   = false;
        theory::reset_eh();
    }

    

    template<typename Ext>
    void theory_horn_ineq<Ext>::new_eq_or_diseq(bool is_eq, th_var v1, th_var v2, justification& eq_just) {
        rational k;
        th_var s = expand(true,  v1, k);
        th_var t = expand(false, v2, k);
        context& ctx = get_context();
        ast_manager& m = get_manager();
        
        if (s == t) {
            if (is_eq != k.is_zero()) {
                // conflict 0 /= k;
                inc_conflicts();
                ctx.set_conflict(&eq_just);            
            }
        }
        else {
            //
            // Create equality ast, internalize_atom
            // assign the corresponding equality literal.
            //
                        
            app_ref eq(m), s2(m), t2(m);
            app* s1 = get_enode(s)->get_owner();
            app* t1 = get_enode(t)->get_owner();
            s2 = a.mk_sub(t1, s1);
            t2 = a.mk_numeral(k, m.get_sort(s2.get()));
            // t1 - s1 = k
            eq = m.mk_eq(s2.get(), t2.get());
            
            TRACE("horn_ineq", 
                  tout << v1 << " .. " << v2 << "\n";
                  tout << mk_pp(eq.get(), m) <<"\n";);
            
            if (!internalize_atom(eq.get(), false)) {
                UNREACHABLE();
            }
            
            literal l(ctx.get_literal(eq.get()));
            if (!is_eq) {
                l = ~l;
            }
            
            ctx.assign(l, b_justification(&eq_just), false);
        }
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::inc_conflicts() {
        m_stats.m_num_conflicts++;   
        if (m_params.m_arith_adaptive) {
            double g = m_params.m_arith_adaptive_propagation_threshold;
            m_agility = m_agility*g + 1 - g;
        }
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::set_neg_cycle_conflict() {
        m_graph->traverse_neg_cycle1(m_params.m_arith_stronger_lemmas);
        inc_conflicts();
        literal_vector const& lits = m_graph->get_lits();
        context & ctx = get_context();
        TRACE("horn_ineq", 
              tout << "conflict: ";
              for (unsigned i = 0; i < lits.size(); ++i) {
                  ctx.display_literal_info(tout, lits[i]);
              }
              tout << "\n";
              );
        
        if (m_params.m_arith_dump_lemmas) {
            char const * logic = m_lra ? (m_lia?"QF_LIRA":"QF_LRA") : "QF_LIA";
            ctx.display_lemma_as_smt_problem(lits.size(), lits.c_ptr(), false_literal, logic);
        }
        
        vector<parameter> params;
        if (get_manager().proofs_enabled()) {
            params.push_back(parameter(symbol("farkas")));
            vector<rational> const& coeffs = m_graph->get_coeffs();
            for (unsigned i = 0; i < coeffs.size(); ++i) {
                params.push_back(parameter(coeffs[i]));
            }
        } 
        
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(), 
                    lits.size(), lits.c_ptr(), 0, 0, params.size(), params.c_ptr())));        
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::found_non_horn_ineq_expr(expr* n) {
        if (!m_non_horn_ineq_exprs) {
            TRACE("horn_ineq", tout << "found non horn logic expression:\n" << mk_pp(n, get_manager()) << "\n";);
            get_context().push_trail(value_trail<context, bool>(m_non_horn_ineq_exprs));
            m_non_horn_ineq_exprs = true;
        }
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::init(context* ctx) {
        theory::init(ctx);
        m_zero_int  = mk_var(ctx->mk_enode(a.mk_numeral(rational(0), true), false, false, true));
        m_zero_real = mk_var(ctx->mk_enode(a.mk_numeral(rational(0), false), false, false, true));
        m_graph->set_to_zero(m_zero_int);
        m_graph->set_to_zero(m_zero_real);
    }

    /**
       \brief Create negated literal.
       
       The negation of: E <= 0

       -E + epsilon <= 0
       or
       -E + 1 <= 0
     */
    template<typename Ext>
    void theory_horn_ineq<Ext>::negate(coeffs& coeffs, rational& weight) {
        for (unsigned i = 0; i < coeffs.size(); ++i) {
            coeffs[i].second.neg();
        }
        weight.neg();
    }    

    template<typename Ext>
    typename theory_horn_ineq<Ext>::numeral theory_horn_ineq<Ext>::mk_weight(bool is_real, bool is_strict, rational const& w) const {
        if (is_strict) {
            return numeral(inf_numeral(w)) + (is_real?m_epsilon:numeral(1));
        }
        else {
            return numeral(inf_numeral(w));
        }
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::mk_coeffs(vector<std::pair<expr*,rational> > const& terms, coeffs& coeffs, rational& w) {
        coeffs.reset();
        w = m_test.get_weight();
        for (unsigned i = 0; i < terms.size(); ++i) {
            coeffs.push_back(std::make_pair(mk_var(terms[i].first), terms[i].second));
        }
    }

    template<typename Ext>
    bool theory_horn_ineq<Ext>::internalize_atom(app * n, bool) {
        context & ctx = get_context();
        if (!a.is_le(n) && !a.is_ge(n) && !a.is_lt(n) && !a.is_gt(n)) {
            found_non_horn_ineq_expr(n);
            return false;
        }
        SASSERT(!ctx.b_internalized(n));
        expr* e1 = n->get_arg(0), *e2 = n->get_arg(1);
        if (a.is_ge(n) || a.is_gt(n)) {
            std::swap(e1, e2);
        }
        bool is_strict = a.is_gt(n) || a.is_lt(n);

        horn_ineq_tester::classify_t cl = m_test.linearize(e1, e2);
        if (cl == horn_ineq_tester::non_horn) {
            found_non_horn_ineq_expr(n);
            return false;
        }

        rational w;
        coeffs coeffs;
        mk_coeffs(m_test.get_linearization(), coeffs, w);
        bool_var bv = ctx.mk_bool_var(n);
        ctx.set_var_theory(bv, get_id());
        literal l(bv);
        numeral w1 = mk_weight(a.is_real(e1), is_strict, w);
        clause_id pos = m_graph->add_ineq(coeffs, w1, l);        
        negate(coeffs, w);
        numeral w2 = mk_weight(a.is_real(e1), !is_strict, w);
        clause_id neg = m_graph->add_ineq(coeffs, w2, ~l);
        m_bool_var2atom.insert(bv, m_atoms.size());
        m_atoms.push_back(atom(bv, pos, neg));
        
        TRACE("horn_ineq", 
              tout << mk_pp(n, get_manager()) << "\n";
              m_graph->display_clause(tout << "pos: ", pos); 
              m_graph->display_clause(tout << "neg: ", neg); 
              );
        
        return true;
    }

    template<typename Ext>
    bool theory_horn_ineq<Ext>::internalize_term(app * term) {
        bool result = null_theory_var != mk_term(term);
        CTRACE("horn_ineq", !result, tout << "Did not internalize " << mk_pp(term, get_manager()) << "\n";);
        TRACE("horn_ineq", tout << "Terms may not be internalized " << mk_pp(term, get_manager()) << "\n";);
        found_non_horn_ineq_expr(term);
        return result;
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::internalize_eq_eh(app * atom, bool_var) {
        // noop
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::assign_eh(bool_var v, bool is_true) {
        m_stats.m_num_assertions++;
        unsigned idx = m_bool_var2atom.find(v);
        SASSERT(get_context().get_assignment(v) != l_undef);
        SASSERT((get_context().get_assignment(v) == l_true) == is_true);    
        m_atoms[idx].assign_eh(is_true);
        m_asserted_atoms.push_back(idx);   
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::push_scope_eh() {
        theory::push_scope_eh();
        m_graph->push();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_atoms_lim = m_atoms.size();
        s.m_asserted_atoms_lim = m_asserted_atoms.size();
        s.m_asserted_qhead_old = m_asserted_qhead;
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::pop_scope_eh(unsigned num_scopes) {
        unsigned lvl     = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl = lvl - num_scopes;
        scope & s        = m_scopes[new_lvl];
        del_atoms(s.m_atoms_lim);
        m_asserted_atoms.shrink(s.m_asserted_atoms_lim);
        m_asserted_qhead = s.m_asserted_qhead_old;
        m_scopes.shrink(new_lvl);
        m_graph->pop(num_scopes);
        theory::pop_scope_eh(num_scopes);
    }
    
    template<typename Ext>
    final_check_status theory_horn_ineq<Ext>::final_check_eh() {
        SASSERT(is_consistent());
        TRACE("horn_ineq", display(tout););
        if (can_propagate()) {
            propagate_core();
            return FC_CONTINUE;
        }        
        else if (m_non_horn_ineq_exprs) {
            return FC_GIVEUP;
        }
        else {
            return FC_DONE;
        }
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::propagate() {
        propagate_core();            
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::display(std::ostream& out) const {
        for (unsigned i = 0; i < m_atoms.size(); ++i) {
            m_atoms[i].display(*this, out);
        }
        out << "\n";
        m_graph->display(out);        
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::collect_statistics(::statistics& st) const {
        st.update("hi conflicts", m_stats.m_num_conflicts);
//        st.update("hi propagations", m_stats.m_num_th2core_prop);
//        st.update("hi asserts", m_stats.m_num_assertions);
//        st.update("core->hi eqs", m_stats.m_num_core2th_eqs);
        m_arith_eq_adapter.collect_statistics(st);
        m_graph->collect_statistics(st);
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::del_atoms(unsigned old_size) {
        typename atoms::iterator begin = m_atoms.begin() + old_size;
        typename atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            m_bool_var2atom.erase(it->get_bool_var());
        }    
        m_atoms.shrink(old_size);
    }

    template<typename Ext>
    void theory_horn_ineq<Ext>::propagate_core() {
        bool consistent = true;
        while (consistent && can_propagate()) {
            unsigned idx = m_asserted_atoms[m_asserted_qhead];
            m_asserted_qhead++;
            consistent = propagate_atom(m_atoms[idx]);
        }
    }

    template<typename Ext>
    bool theory_horn_ineq<Ext>::propagate_atom(atom const& a) {
        context& ctx = get_context();
        TRACE("horn_ineq", a.display(*this, tout); tout << "\n";);
        if (ctx.inconsistent()) {
            return false;
        }
        int clause_id = a.get_asserted_edge();
        if (!m_graph->enable_clause(clause_id)) {
            set_neg_cycle_conflict();
            return false;
        }
        return true;
    }
    
    template<typename Ext>
    theory_var theory_horn_ineq<Ext>::mk_term(app* n) {
        context& ctx = get_context();
        
        horn_ineq_tester::classify_t cl = m_test.linearize(n);
        if (cl == horn_ineq_tester::non_horn) {
            found_non_horn_ineq_expr(n);
            return null_theory_var;
        }

        coeffs coeffs;
        rational w;
        mk_coeffs(m_test.get_linearization(), coeffs, w);
        if (coeffs.empty()) {
            return mk_num(n, w);
        }
        if (coeffs.size() == 1 && coeffs[0].second.is_one()) {
            return coeffs[0].first;
        }
        th_var target = mk_var(ctx.mk_enode(n, false, false, true));        
        coeffs.push_back(std::make_pair(target, rational(-1)));

        VERIFY(m_graph->enable_clause(m_graph->add_ineq(coeffs, numeral(inf_numeral(w)), null_literal)));        
        negate(coeffs, w);
        VERIFY(m_graph->enable_clause(m_graph->add_ineq(coeffs, numeral(inf_numeral(w)), null_literal)));
        return target;
    }
    
    template<typename Ext>
    theory_var theory_horn_ineq<Ext>::mk_num(app* n, rational const& r) {
        theory_var v = null_theory_var;
        context& ctx = get_context();
        if (r.is_zero()) {            
            v = a.is_int(n)?m_zero_int:m_zero_real;
        }
        else if (ctx.e_internalized(n)) {
            enode* e = ctx.get_enode(n);
            v = e->get_th_var(get_id());
            SASSERT(v != null_theory_var);
        }
        else {
            v = mk_var(ctx.mk_enode(n, false, false, true));
            // v = k: v <= k k <= v
            coeffs coeffs;
            coeffs.push_back(std::make_pair(v, rational(1)));
            VERIFY(m_graph->enable_clause(m_graph->add_ineq(coeffs, numeral(inf_numeral(r)), null_literal)));
            coeffs.back().second.neg();
            VERIFY (m_graph->enable_clause(m_graph->add_ineq(coeffs, numeral(inf_numeral(-r)), null_literal)));
        }
        return v;
    }

    template<typename Ext>
    theory_var theory_horn_ineq<Ext>::expand(bool pos, th_var v, rational & k) {
        context& ctx = get_context();
        enode* e = get_enode(v);
        expr* x, *y;
        rational r;
        for (;;) {
            app* n = e->get_owner();
            if (a.is_add(n, x, y)) {
                if (a.is_numeral(x, r)) {
                    e = ctx.get_enode(y);                
                }
                else if (a.is_numeral(y, r)) {
                    e = ctx.get_enode(x);
                }
                v = e->get_th_var(get_id());
                SASSERT(v != null_theory_var);
                if (v == null_theory_var) {
                    break;
                }
                if (pos) {
                    k += r;
                }
                else {
                    k -= r;
                }
            }
            else {
                break;
            }
        }
        return v;
    }

    template<typename Ext>
    bool theory_horn_ineq<Ext>::is_consistent() const {
        return m_graph->is_feasible();
    }

    // models:
    template<typename Ext>
    void theory_horn_ineq<Ext>::init_model(model_generator & m) {    
        m_factory = alloc(arith_factory, get_manager());
        m.register_factory(m_factory);
        compute_delta();   
    }
    
    template<typename Ext>    
    model_value_proc * theory_horn_ineq<Ext>::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        numeral val = m_graph->get_assignment(v);
        rational num = val.get_infinity()*m_lambda + val.get_rational() + val.get_infinitesimal()*m_delta;
        TRACE("horn_ineq", tout << mk_pp(n->get_owner(), get_manager()) << " |-> " << num << "\n";);
        return alloc(expr_wrapper_proc, m_factory->mk_value(num, a.is_int(n->get_owner())));
    }

    /**
       \brief Compute numeral values for the infinitesimals to satisfy the inequalities.
     */

    template<typename Ext>
    void theory_horn_ineq<Ext>::compute_delta() {
        m_delta = rational(1);
        m_lambda = rational(0);
        unsigned sz = m_graph->get_num_clauses();

        for (unsigned i = 0; i < sz; ++i) {
            if (!m_graph->get_clause(i).is_enabled()) {
                continue;
            }
            numeral b = m_graph->eval_body(i);
            numeral h = m_graph->eval_head(i);

            if (b.get_infinity() < h.get_infinity()) {
                continue;
            }
            SASSERT(b.get_infinity() == h.get_infinity());

            // b <= h
            // suppose that h.eps < b.eps
            // then we have h.num > b.num
            // but also h.num + delta*h.eps >= b.num + delta*b.eps
            // <=>
            //      (h.num - b.num)/(b.eps - h.eps) >= delta
            rational num_r = h.get_rational() - b.get_rational();
            rational eps_r = b.get_infinitesimal() - h.get_infinitesimal();
            if (eps_r.is_pos()) {
                SASSERT(num_r.is_pos());
                rational new_delta = num_r/eps_r;
                if (new_delta < m_delta) {
                    m_delta = new_delta;
                }
            }
        }

        for (unsigned i = 0; i < sz; ++i) {
            if (!m_graph->get_clause(i).is_enabled()) {
                continue;
            }
            numeral b = m_graph->eval_body(i);
            numeral h = m_graph->eval_head(i);

            rational ir = h.get_infinity() - b.get_infinity();
            rational hr = b.get_rational() - h.get_rational();
            rational num_r = hr + m_delta*(b.get_infinitesimal() - h.get_infinitesimal());

            SASSERT(b.get_infinity() <= h.get_infinity());

            // b <= h
            // suppose that h.finite < b.finite
            // then we have h.infinite > b.infinite
            // but also 
            //      h.infinite*lambda + h.finite >= b.infinite*lambda + b.finite
            // <=>
            //      lambda >= (b.finite - h.finite) / (h.infinite - b.infinite) 
            if (num_r.is_pos()) {
                SASSERT(ir.is_pos());
                rational new_lambda = num_r/ir;
                if (new_lambda > m_lambda) {
                    m_lambda = new_lambda;
                }
            }
        }
    }



};

#endif
