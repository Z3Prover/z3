/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_preprocess_tactic.cpp

Abstract:

    Pre-process pseudo-Boolean inequalities using 
    generalized Davis Putnam (resolution) to eliminate variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-23

Notes:

    Resolution for PB constraints require the implicit 
    inequalities that each variable ranges over [0,1]
    so not all resolvents produce smaller sets of clauses.

    We here implement subsumption resolution.  

    x + y >= 1
    A~x + B~y + Cz >= k
    ---------------------
    Cz >= k - B    

    where A <= B, x, y do not occur elsewhere.    


--*/
#include "pb_preprocess_tactic.h"
#include "tactical.h"
#include "for_each_expr.h"
#include "pb_decl_plugin.h"
#include "th_rewriter.h"
#include "expr_substitution.h"
#include "ast_pp.h"

class pb_preproc_model_converter : public model_converter {
    ast_manager& m;
    pb_util      pb;
    expr_ref_vector                  m_refs;
    svector<std::pair<app*, expr*> > m_const;

public:
    pb_preproc_model_converter(ast_manager& m):m(m), pb(m), m_refs(m) {}

    virtual void operator()(model_ref & mdl, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        for (unsigned i = 0; i < m_const.size(); ++i) {
            mdl->register_decl(m_const[i].first->get_decl(), m_const[i].second);
        }
    }

    void set_value(expr* e, bool p) {
        while (m.is_not(e, e)) {
            p = !p;
        }
        SASSERT(is_app(e));
        set_value_p(to_app(e), p?m.mk_true():m.mk_false());        
    }

    virtual model_converter * translate(ast_translation & translator) {
        pb_preproc_model_converter* mc = alloc(pb_preproc_model_converter, translator.to());
        for (unsigned i = 0; i < m_const.size(); ++i) {
            mc->set_value_p(translator(m_const[i].first), translator(m_const[i].second));
        }
        return mc;
    }

private:
    void set_value_p(app* e, expr* v) {
        SASSERT(e->get_num_args() == 0);  
        SASSERT(is_uninterp_const(e));
        m_const.push_back(std::make_pair(e, v));
        m_refs.push_back(e);
        m_refs.push_back(v);
    }

};

class pb_preprocess_tactic : public tactic {
    struct rec { unsigned_vector pos, neg; rec() { } };
    typedef obj_map<app, rec> var_map;
    ast_manager&     m;
    pb_util          pb;
    var_map          m_vars;    
    unsigned_vector  m_ge;
    unsigned_vector  m_other;
    bool             m_progress;
    th_rewriter      m_r;
    

    struct declassifier {
        var_map& m_vars;        
        declassifier(var_map& v): m_vars(v) {}

        void operator()(app* e) {
            if (m_vars.contains(e)) {
                m_vars.remove(e);
            }
        }
        void operator()(var*) {}
        void operator()(quantifier*) {}
    };

    void display_annotation(std::ostream& out, goal_ref const& g) {
        for (unsigned i = 0; i < m_ge.size(); ++i) {
            out << "ge " << m_ge[i] << ": " << mk_pp(g->form(m_ge[i]), m) << "\n";
        }
        for (unsigned i = 0; i < m_other.size(); ++i) {
            out << "ot " << m_other[i] << ": " << mk_pp(g->form(m_other[i]), m) << "\n";
        }
                
        var_map::iterator it  = m_vars.begin();
        var_map::iterator end = m_vars.end();
        for (; it != end; ++it) {
            app* e = it->m_key;
            unsigned_vector const& pos = it->m_value.pos;
            unsigned_vector const& neg = it->m_value.neg;
            out << mk_pp(e, m) << ": ";
            for (unsigned i = 0; i < pos.size(); ++i) {
                out << "p: " << pos[i] << " ";
            }
            for (unsigned i = 0; i < neg.size(); ++i) {
                out << "n: " << neg[i] << " ";
            }
            out << "\n";
        }
    }

public:
    pb_preprocess_tactic(ast_manager& m, params_ref const& p = params_ref()): 
        m(m), pb(m), m_r(m) {}

    virtual ~pb_preprocess_tactic() {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(pb_preprocess_tactic, m);
    }
    
    virtual void operator()(
        goal_ref const & g, 
        goal_ref_buffer & result, 
        model_converter_ref & mc, 
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        pc = 0; core = 0;

        if (g->unsat_core_enabled()) {
            throw tactic_exception("pb-preprocess does not support cores");
        }
        if (g->proofs_enabled()) {
            throw tactic_exception("pb-preprocess does not support proofs");
        }

        pb_preproc_model_converter* pp = alloc(pb_preproc_model_converter, m);
        mc = pp;

        g->inc_depth();        
        result.push_back(g.get());       
        while (simplify(g, *pp));
        // decompose(g);
    }

    bool simplify(goal_ref const& g, pb_preproc_model_converter& mc) {
        reset();
        normalize(g);
        if (g->inconsistent()) {
            return false;
        }
        for (unsigned i = 0; i < g->size(); ++i) {
            process_vars(i, g);
        }
        
        if (m_ge.empty()) {
            return false;
        }
        
        for (unsigned i = 0; i < m_ge.size(); ++i) {
            classify_vars(i, to_app(g->form(m_ge[i])));
        }
        
        declassifier dcl(m_vars);
        expr_mark visited;        
        for (unsigned i = 0; !m_vars.empty() && i < m_other.size(); ++i) {
            for_each_expr(dcl, visited, g->form(m_other[i]));
        }
        
        if (m_vars.empty()) {
            return false;
        }
        
        // display_annotation(tout, g);
        m_progress = false;
        // first eliminate variables
        var_map::iterator it = next_resolvent(m_vars.begin()); 
        while (it != m_vars.end()) {            
            app * e = it->m_key;
            rec const& r = it->m_value;
            if (r.pos.empty()) {                
                replace(r.neg, e, m.mk_false(), g);
                mc.set_value(e, false);
            }
            else if (r.neg.empty()) {
                replace(r.pos, e, m.mk_true(), g);
                mc.set_value(e, true);
            }
            if (g->inconsistent()) return false;
            ++it;
            it = next_resolvent(it);
        }        
        // now resolve clauses.
        it = next_resolvent(m_vars.begin());
        while (it != m_vars.end()) {
            
            app * e = it->m_key;
            SASSERT(is_uninterp_const(e));
            rec const& r = it->m_value;
            if (r.pos.size() == 1 && !r.neg.empty()) {
                resolve(mc, r.pos[0], r.neg, e, true, g);
            }
            else if (r.neg.size() == 1 && !r.pos.empty()) {
                resolve(mc, r.neg[0], r.pos, e, false, g);                
            }
            if (g->inconsistent()) return false;
            ++it;
            it = next_resolvent(it);
        }

        // now check for subsumption.
        for (unsigned i = 0; i < m_ge.size(); ++i) {
            
            expr_ref_vector args1(m), args2(m);
            vector<rational> coeffs1, coeffs2;        
            rational k1, k2;
            expr* fml = g->form(m_ge[i]);
            if (!to_ge(fml, args1, coeffs1, k1)) continue;
            if (args1.empty()) continue;
            expr* arg = args1[0].get();
            bool neg = m.is_not(arg, arg);
            if (!is_uninterp_const(arg)) continue;
            if (!m_vars.contains(to_app(arg))) continue;
            rec const& r = m_vars.find(to_app(arg));
            unsigned_vector const& pos = neg?r.neg:r.pos;
            for (unsigned j = 0; j < pos.size(); ++j) {
                unsigned k = pos[j];
                if (k == i) continue;
                if (!to_ge(g->form(k), args2, coeffs2, k2)) continue;
                if (subsumes(args1, coeffs1, k1, args2, coeffs2, k2)) {
                    IF_VERBOSE(3, verbose_stream() << "replace " << mk_pp(g->form(k), m) << "\n";);
                    g->update(k, m.mk_true());                    
                    m_progress = true;
                }
            }
        }

        g->elim_true();

        return m_progress;
    }

    virtual void updt_params(params_ref const & p) {
    }

    virtual void cleanup() {
    }

private:

    void reset() {
        m_ge.reset();
        m_other.reset();
        m_vars.reset();
    }

    expr* negate(expr* e) {
        if (m.is_not(e, e)) return e;
        return m.mk_not(e);
    }

    void normalize(goal_ref const& g) {
        expr* r;
        expr_ref tmp(m);
        for (unsigned i = 0; !g->inconsistent() && i < g->size(); ++i) {
            expr* e = g->form(i);
            if (m.is_not(e, r) && pb.is_ge(r)) {
                rational k = pb.get_k(r);
                rational sum(0);
                expr_ref_vector args(m);
                vector<rational> coeffs;
                for (unsigned j = 0; j < to_app(r)->get_num_args(); ++j) {
                    sum += pb.get_coeff(r, j);
                    coeffs.push_back(pb.get_coeff(r, j));
                    args.push_back(negate(to_app(r)->get_arg(j)));
                }
                tmp = pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), sum - k + rational::one());
                g->update(i, tmp);
            }
        }
    }

    unsigned log2ceil(unsigned n) {
        unsigned p = 1;
        while (n > 0) {
            n /= 2;
            ++p;
        }
        return p;
    }

    /**
       \brief decompose large sums into smaller sums by intoducing
       auxilary variables.
    */
    void decompose(goal_ref const& g) {
        expr_ref fml1(m), fml2(m);
        for (unsigned i = 0; !g->inconsistent() && i < g->size(); ++i) {
            expr* e = g->form(i);
            unsigned_vector cuts;
            if (cut(e, cuts)) {
                app* a = to_app(e);
                expr_ref_vector  cut_args(m);
                vector<rational> cut_coeffs;
                if (cuts.size() < 2) continue;
                unsigned start = 0;
                for (unsigned j = 0; j < cuts.size(); ++j) {
                    unsigned end = cuts[j];
                    fml1 = decompose_cut(a, start, end, cut_args, cut_coeffs); 
                    g->assert_expr(fml1);
                    start = end;
                    TRACE("pb", tout << fml1 << "\n";);
                }
                fml2 = pb.mk_ge(cut_args.size(), cut_coeffs.c_ptr(), cut_args.c_ptr(), pb.get_k(e));
                g->update(i, fml2);
                TRACE("pb", tout << fml2 << "\n";);
            }
        }
    }
    bool cut(expr* e, unsigned_vector& cuts) {
        if (!pb.is_ge(e)) return false;
        if (to_app(e)->get_num_args() <= 20) return false;
        unsigned n = 0, cut = 0;
        unsigned sz = to_app(e)->get_num_args();
        for (unsigned i = 0; i < sz; ++i) {
            rational r = pb.get_coeff(e, i); 
            if (!r.is_unsigned()) {
                return false;
            }                
            n += r.get_unsigned();
            if (2*log2ceil(n) < cut) {
                cuts.push_back(i+1);
                n = 0; 
                cut = 0;
            }
            else {
                ++cut;
            }
        }
        if (!cuts.empty() && cuts.back() + 20 >= sz) {
            cuts.pop_back();
        }
        cuts.push_back(sz);
        return true;
    }

    expr_ref decompose_cut(app* e, unsigned start, unsigned end, 
                           expr_ref_vector& cut_args,
                           vector<rational>& cut_coeffs) {
        unsigned n = 0, j = 1;
        vector<rational> coeffs;
        expr_ref_vector args(m);
        app_ref z(m);
        expr_ref fml1(m), fml(m);

        for (unsigned i = start; i < end; ++i) {
            rational r = pb.get_coeff(e, i); 
            n += r.get_unsigned();
            args.push_back(e->get_arg(i));
            coeffs.push_back(r);
        }

        while (j <= n) {
            z = m.mk_fresh_const("z", m.mk_bool_sort());
            coeffs.push_back(-rational(j));
            args.push_back(z);
            cut_coeffs.push_back(rational(j));
            cut_args.push_back(z);            
            j <<= 1;
        }
        fml1 = pb.mk_ge(args.size(), coeffs.c_ptr(), args.c_ptr(), rational(0));
        m_r(fml1, fml);
        return fml;
    }
    

    void process_vars(unsigned i, goal_ref const& g) {
        expr* r, *e;
        e = g->form(i);

        if (is_uninterp_const(e)) {
            m_ge.push_back(i);
        }
        else if (pb.is_ge(e) && pure_args(to_app(e))) {
            m_ge.push_back(i);
        }
        else if (m.is_or(e) && pure_args(to_app(e))) {
            m_ge.push_back(i);
        }
        else if (m.is_not(e, r) && is_uninterp_const(r)) {
            m_ge.push_back(i);
        }
        else {
            m_other.push_back(i);
        }
    }

    void classify_vars(unsigned idx, app* e) {
        expr* r;
        if (m.is_not(e, r) && is_uninterp_const(r)) {
            insert(idx, to_app(r), false);
            return;
        }
        if (is_uninterp_const(e)) {
            insert(idx, e, true);
            return;
        }
        for (unsigned i = 0; i < e->get_num_args(); ++i) {
            expr* arg = e->get_arg(i);
            if (m.is_true(arg) || m.is_false(arg)) {
                // no-op
            }
            else if (m.is_not(arg, r)) {
                SASSERT(is_uninterp_const(r));
                insert(idx, to_app(r), false);
            }
            else {
                SASSERT(is_uninterp_const(arg));
                insert(idx, to_app(arg), true);
            }
        }
    }

    void insert(unsigned i, app* e, bool pos) {
        SASSERT(is_uninterp_const(e));
        if (!m_vars.contains(e)) {
            m_vars.insert(e, rec());
        }
        if (pos) {
            m_vars.find(e).pos.push_back(i);
        }
        else {
            m_vars.find(e).neg.push_back(i);
        }
    }

    bool pure_args(app* a) const {
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr* e = a->get_arg(i);
            m.is_not(e, e);
            if (!is_uninterp_const(e) && !m.is_true(e) && !m.is_false(e)) {
                return false;
            }
        }
        return true;
    }

    var_map::iterator next_resolvent(var_map::iterator it) {
        if (it == m_vars.end()) {
            return it;
        }
        while (it != m_vars.end() && it->m_value.pos.size() > 1 && it->m_value.neg.size() > 1) {
            ++it;
        }
        return it;        
    }

    rational get_coeff(unsigned num_args, expr* const* args, rational const* coeffs, expr* e) {
        for (unsigned i = 0; i < num_args; ++i) {
            if (args[i] == e) return coeffs[i];
        }
        return rational::zero();
    }

    //
    // one of the formulas are replaced by T after resolution
    // so if there is a pointer into that formula, we can no
    // longer assume variables have unique occurrences.
    //
    bool is_valid(unsigned_vector const& positions, goal_ref const& g) const {
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx = positions[i];
            if (m.is_true(g->form(idx))) return false;
        }
        return true;
    }

    bool is_reduction(unsigned_vector const& pos, app* fml, goal_ref const& g) {
        unsigned sz = fml->get_num_args();
        for (unsigned i = 0; i < pos.size(); ++i) {
            if (!is_app(g->form(pos[i]))) return false;
            if (to_app(g->form(pos[i]))->get_num_args() < sz) return false;
        }
        return true;
    }

    // Implement very special case of resolution.
    
    void resolve(pb_preproc_model_converter& mc, unsigned idx1, 
                 unsigned_vector const& positions, app* e, bool pos, goal_ref const& g) {
        if (positions.size() != 1) return;
        unsigned idx2 = positions[0];
        expr_ref tmp1(m), tmp2(m);
        expr* fml1 = g->form(idx1);
        expr* fml2 = g->form(idx2);
        TRACE("pb", tout << mk_pp(fml1, m) << " " << mk_pp(fml2, m) << "\n";);
        expr_ref_vector args1(m), args2(m);
        vector<rational> coeffs1, coeffs2;        
        rational k1, k2;
        if (!to_ge(fml1, args1, coeffs1, k1)) return;
        if (!k1.is_one()) return;
        if (!to_ge(g->form(idx2), args2, coeffs2, k2)) return;
        // check that each variable in idx1 occurs only in idx2
        unsigned min_index = 0;
        rational min_coeff(0);
        unsigned_vector indices;
        for (unsigned i = 0; i < args1.size(); ++i) {
            expr* x = args1[i].get();
            m.is_not(x, x);
            if (!is_app(x)) return;
            if (!m_vars.contains(to_app(x))) return;            
            TRACE("pb", tout << mk_pp(x, m) << "\n";);
            rec const& r = m_vars.find(to_app(x));
            if (r.pos.size() != 1 || r.neg.size() != 1) return;
            if (r.pos[0] != idx2 && r.neg[0] != idx2) return;
            for (unsigned j = 0; j < args2.size(); ++j) {
                if (is_complement(args1[i].get(), args2[j].get())) {
                    if (i == 0) {
                        min_coeff = coeffs2[j];
                    }
                    else if (min_coeff > coeffs2[j]) {
                        min_coeff = coeffs2[j];
                        min_index = j;
                    }
                    indices.push_back(j);
                }                
            }
        }
        for (unsigned i = 0; i < indices.size(); ++i) {
            unsigned j = indices[i];
            expr* arg = args2[j].get();
            if (j == min_index) {
                args2[j] = m.mk_false();
            }
            else {
                args2[j] = m.mk_true();
            }
            mc.set_value(arg, j != min_index);
        }
        
        tmp1 = pb.mk_ge(args2.size(), coeffs2.c_ptr(), args2.c_ptr(), k2);
        IF_VERBOSE(3, verbose_stream() << " " << tmp1 << "\n";
                   for (unsigned i = 0; i < args2.size(); ++i) {
                       verbose_stream() << mk_pp(args2[i].get(), m) << " ";
                   }
                   verbose_stream() << "\n";
                   );
        m_r(tmp1, tmp2);
        if (pb.is_ge(tmp2) && pb.get_k(to_app(tmp2)).is_one()) {
            tmp2 = m.mk_or(to_app(tmp2)->get_num_args(), to_app(tmp2)->get_args());
        }
        IF_VERBOSE(3, 
                   verbose_stream() << "resolve: " << mk_pp(fml1, m) << "\n" << mk_pp(fml2, m) << "\n" << tmp1 << "\n";
                   verbose_stream() << "to\n" << mk_pp(fml2, m) << " -> " << tmp2 << "\n";);

        g->update(idx1, m.mk_true()); // proof & dependencies
        g->update(idx2, tmp2);        // proof & dependencies
        m_progress = true;
        //IF_VERBOSE(0, if (!g->inconsistent()) display_annotation(verbose_stream(), g););
    }

    bool is_complement(expr* x, expr* y) const {
        if (m.is_not(x,x)) return x == y;
        if (m.is_not(y,y)) return x == y;
        return false;
    }

    bool to_ge(expr* e, expr_ref_vector& args, vector<rational>& coeffs, rational& k) {
        expr* r;
        if (is_uninterp_const(e)) {
            args.push_back(e);
            coeffs.push_back(rational::one());
            k = rational::one();
        }
        else if (m.is_not(e, r) && is_uninterp_const(r)) {
            args.push_back(e);
            coeffs.push_back(rational::one());
            k = rational::one();
        }
        else if (pb.is_ge(e)) {
            app* a = to_app(e);
            SASSERT(pure_args(a));
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                args.push_back(a->get_arg(i));
                coeffs.push_back(pb.get_coeff(a, i));
            }
            k = pb.get_k(e);
        }
        else if (m.is_or(e)) {
            app* a = to_app(e);
            SASSERT(pure_args(a));
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                args.push_back(a->get_arg(i));
                coeffs.push_back(rational::one());
            }
            k = rational::one();
        }
        else {
            return false;
        }
        return true;
    }

    void replace(unsigned_vector const& positions, expr* e, expr* v, goal_ref const& g) {
        if (!is_valid(positions, g)) return;
        expr_substitution sub(m);
        sub.insert(e, v);
        expr_ref tmp(m);
        m_r.set_substitution(&sub);        
        for (unsigned i = 0; i < positions.size(); ++i) {
            unsigned idx = positions[i];
            expr_ref f(m);
            f = g->form(idx);
            if (!m.is_true(f)) {
                m_r(f, tmp);
                if (tmp != f) {
                    TRACE("pb", tout << mk_pp(f, m) << " -> " << tmp 
                          << " by " << mk_pp(e, m) << " |-> " << mk_pp(v, m) << "\n";);
                    IF_VERBOSE(3, verbose_stream() << "replace " << mk_pp(f, m) << " -> " << tmp << "\n";);
                    g->update(idx, tmp); // proof & dependencies.
                    m_progress = true;
                }
            }
        }
        m_r.set_substitution(0);
    }

    bool subsumes(expr_ref_vector const& args1, 
                  vector<rational> const& coeffs1, rational const& k1, 
                  expr_ref_vector const& args2, 
                  vector<rational> const& coeffs2, rational const& k2) {
        if (k2 > k1) return false;
        for (unsigned i = 0; i < args1.size(); ++i) {
            bool found = false;
            for (unsigned j = 0; !found && j < args2.size(); ++j) {
                if (args1[i] == args2[j]) {
                    if (coeffs1[i] > coeffs2[j]) return false;
                    found = true;
                }
            }
            if (!found) return false;
        }
        return true;
    }
};


tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p) {
    return alloc(pb_preprocess_tactic, m);
}

