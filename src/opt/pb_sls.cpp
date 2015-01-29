/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    pb_sls.cpp

Abstract:
   
    SLS for PB optimization.

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-18

Notes:

--*/
#include "pb_sls.h"
#include "smt_literal.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "sat_sls.h"

namespace smt {
    struct pb_sls::imp {

        struct clause {
            literal_vector    m_lits;
            scoped_mpz_vector m_weights;
            scoped_mpz        m_k;
            scoped_mpz        m_value;
            bool              m_eq;
            clause(unsynch_mpz_manager& m):
                m_weights(m),
                m_k(m),
                m_value(m),
                m_eq(true)
            {}
            clause(clause const& cls):
                m_lits(cls.m_lits),
                m_weights(cls.m_weights.m()),
                m_k(cls.m_k),
                m_value(cls.m_value),
                m_eq(cls.m_eq) {
                for (unsigned i = 0; i < cls.m_weights.size(); ++i) {
                    m_weights.push_back(cls.m_weights[i]);
                }
            }
        };

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_flips;
            unsigned m_num_improvements;
        };
        
        ast_manager&     m;
        pb_util          pb;
        unsynch_mpz_manager mgr;
        th_rewriter      m_rewrite;
        volatile bool    m_cancel;
        vector<clause>   m_clauses;      // clauses to be satisfied        
        expr_ref_vector  m_orig_clauses; // for debugging
        model_ref        m_orig_model;   // for debugging
        vector<clause>   m_soft;         // soft constraints
        vector<rational> m_weights;      // weights of soft constraints
        rational         m_penalty;      // current penalty of soft constraints
        rational         m_best_penalty;
        vector<unsigned_vector>  m_hard_occ, m_soft_occ;  // variable occurrence
        svector<bool>    m_assignment;   // current assignment.
        svector<bool>    m_best_assignment;
        expr_ref_vector  m_trail;
        obj_map<expr, unsigned> m_decl2var; // map declarations to Boolean variables.
        ptr_vector<expr> m_var2decl;        // reverse map
        sat::index_set        m_hard_false;           // list of hard clauses that are false.
        sat::index_set        m_soft_false;           // list of soft clauses that are false.
        unsigned         m_max_flips;            // maximal number of flips
        unsigned         m_non_greedy_percent;   // percent of moves to do non-greedy style
        random_gen       m_rng;
        scoped_mpz       one;
        stats            m_stats;

        imp(ast_manager& m):
            m(m),
            pb(m),
            m_rewrite(m),
            m_cancel(false),
            m_orig_clauses(m),
            m_trail(m),
            one(mgr)
        {
            reset();
            one = mpz(1);
        }

        ~imp() {
        }

        void reset() {
            init_max_flips();
            m_non_greedy_percent = 30;
            m_decl2var.reset();
            m_var2decl.reset();
            m_assignment.reset();
            m_hard_occ.reset();
            m_soft_occ.reset();
            m_clauses.reset();
            m_orig_clauses.reset();
            m_soft.reset();
            m_weights.reset();
            m_trail.reset();
            m_decl2var.insert(m.mk_true(), 0);
            m_var2decl.push_back(m.mk_true());
            m_assignment.push_back(true);
            m_hard_occ.push_back(unsigned_vector());
            m_soft_occ.push_back(unsigned_vector());
        }

        void init_max_flips() {
            m_max_flips = 200;
        }

        void add(expr* f) {
            clause cls(mgr);
            if (compile_clause(f, cls)) {
                m_clauses.push_back(cls);
                m_orig_clauses.push_back(f);
            }
        }
        void add(expr* f, rational const& w) {
            clause cls(mgr);
            if (compile_clause(f, cls)) {
                m_soft.push_back(cls);
                m_weights.push_back(w);
            }
        }

        void set_model(model_ref & mdl) {
            m_orig_model = mdl;
            for (unsigned i = 0; i < m_var2decl.size(); ++i) {
                expr_ref tmp(m);
                VERIFY(mdl->eval(m_var2decl[i], tmp));
                m_assignment[i] = m.is_true(tmp);
            }
        }

        lbool operator()() {
            init();
            IF_VERBOSE(1, verbose_stream() << "(pb.sls initial penalty: " << m_best_penalty << ")\n";
                       verbose_stream() << "(pb.sls violated: " << m_hard_false.num_elems()
                       << " penalty: " << m_penalty << ")\n";);
            svector<bool> assignment(m_assignment);
            for (unsigned round = 0; round < 40; ++round) {
                init_max_flips();
                while (m_max_flips > 0) {
                    --m_max_flips;
                    literal lit = flip();
                    if (m_cancel) {
                        return l_undef;
                    }
                    IF_VERBOSE(3, verbose_stream() 
                               << "(pb.sls violated: " << m_hard_false.num_elems()
                               << " penalty: " << m_penalty << " " << lit << ")\n";);
                    if (m_hard_false.empty() && m_best_penalty.is_zero()) {
                        break;
                    }
                }
                if (m_hard_false.empty() && m_best_penalty.is_zero()) {
                    break;
                }
                IF_VERBOSE(1, verbose_stream() << "(pb.sls best penalty " << m_best_penalty << ")\n";);
                if (!m_best_assignment.empty()) {
                    assignment.reset();
                    assignment.append(m_best_assignment);
                    round = 0;
                }
                m_assignment.reset();
                m_assignment.append(assignment);
                m_best_assignment.reset();      
                m_soft_false.reset();
                m_hard_false.reset();
                m_penalty.reset();
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    if (!eval(m_soft[i])) {
                        m_soft_false.insert(i);
                        m_penalty += m_weights[i];
                    }
                }
                for (unsigned i = 0; i < m_clauses.size(); ++i) {
                    if (!eval(m_clauses[i])) {
                        m_hard_false.insert(i);
                    }
                }
            }
            m_assignment.reset();
            m_assignment.append(assignment);
            m_penalty = m_best_penalty;
            return l_true;
        }

        bool get_value(literal l) {
            return l.sign() ^ m_assignment[l.var()];
        }
        void set_cancel(bool f) {
            m_cancel = f;
        }
        void get_model(model_ref& mdl) {
            mdl = alloc(model, m);
            for (unsigned i = 1; i < m_var2decl.size(); ++i) {
                expr* d = m_var2decl[i];
                if (is_uninterp_const(d)) {
                    mdl->register_decl(to_app(d)->get_decl(), m_assignment[i] ? m.mk_true() : m.mk_false());
                }
            }
        }

        void collect_statistics(::statistics& st) const {
            st.update("sls.num_flips", m_stats.m_num_flips);
            st.update("sls.num_improvements", m_stats.m_num_improvements);
        }

        void updt_params(params_ref& p) {
        }

        bool soft_holds(unsigned index) {
            return eval(m_soft[index]);
        }

        void display(std::ostream& out, clause const& cls) {
            scoped_mpz w(mgr);
            for (unsigned i = 0; i < cls.m_lits.size(); ++i) {
                w = cls.m_weights[i];
                out << w << "*" << cls.m_lits[i] << " ";
                out << "(" << mk_pp(m_var2decl[cls.m_lits[i].var()], m) << ") ";
                if (i + 1 < cls.m_lits.size()) {
                    out << "+ ";
                }
            }
            out << "(" << cls.m_value << ") ";
            if (cls.m_eq) {
                out << "= ";
            }
            else {
                out << ">= ";
            }
            out << cls.m_k << "\n";
        }

        void display(std::ostream& out) {
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                display(out, m_clauses[i]);
            }
            out << "soft:\n";
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                display(out << m_weights[i] << ": ", m_soft[i]);
            }
            for (unsigned i = 0; i < m_assignment.size(); ++i) {
                out << literal(i) << ": " << mk_pp(m_var2decl[i], m) << " |-> " << (m_assignment[i]?"true":"false") << "\n";
            }
        }

        bool eval(clause& cls) {
            unsigned sz = cls.m_lits.size();
            cls.m_value.reset();
            for (unsigned i = 0; i < sz; ++i) {
                if (get_value(cls.m_lits[i])) {
                    cls.m_value += cls.m_weights[i];
                }
            }
            if (cls.m_eq) {
                return cls.m_value == cls.m_k;
            }
            else {
                return cls.m_value >= cls.m_k;
            }
        }

        void init_occ(vector<clause> const& clauses, vector<unsigned_vector> & occ) {
            for (unsigned i = 0; i < clauses.size(); ++i) {
                clause const& cls = clauses[i];
                for (unsigned j = 0; j < cls.m_lits.size(); ++j) {
                    literal lit = cls.m_lits[j];
                    if (occ.size() <= static_cast<unsigned>(lit.var())) occ.resize(lit.var() + 1);
                    occ[lit.var()].push_back(i);
                }
            }
        }
        
        void init() {
            m_best_assignment.reset();
            m_best_penalty.reset();
            m_hard_false.reset();
            m_hard_occ.reset();
            m_soft_false.reset();
            m_soft_occ.reset();
            m_penalty.reset();
            for (unsigned i = 0; i <= m_var2decl.size(); ++i) {
                m_soft_occ.push_back(unsigned_vector());
                m_hard_occ.push_back(unsigned_vector());
            }

            // initialize the occurs vectors.
            init_occ(m_clauses, m_hard_occ);
            init_occ(m_soft, m_soft_occ);

            // add clauses that are false.
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                if (!eval(m_clauses[i])) {
                    m_hard_false.insert(i);
                    expr_ref tmp(m);
                    VERIFY(m_orig_model->eval(m_orig_clauses[i].get(), tmp));                    
                    IF_VERBOSE(0,                               
                               verbose_stream() << "original evaluation: " << tmp << "\n";
                               verbose_stream() << mk_pp(m_orig_clauses[i].get(), m) << "\n";
                               display(verbose_stream(), m_clauses[i]););
                }
            }
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                if (!eval(m_soft[i])) {
                    m_soft_false.insert(i);
                    m_penalty += m_weights[i];
                }
            }
            m_best_penalty = m_penalty;
            TRACE("opt", display(tout););
        }
        
        literal flip() {
            m_stats.m_num_flips++;
            literal result;
            if (m_hard_false.empty()) {
                result = flip_soft();
            }
            else {
                result = flip_hard();
            }            
            if (m_hard_false.empty() && m_best_penalty > m_penalty) {
                IF_VERBOSE(1, verbose_stream() << "(pb.sls improved bound " << m_penalty << ")\n";);
                m_best_assignment.reset();
                m_best_assignment.append(m_assignment);
                m_best_penalty = m_penalty;
                m_stats.m_num_improvements++;
                init_max_flips();
            }
            if (!m_assignment[result.var()]) {
                result.neg();
            }
            return result;
        }
        
        literal flip_hard() {
            SASSERT(!m_hard_false.empty());
            literal lit;
            clause const& cls = pick_hard_clause();
            // IF_VERBOSE(1, display(verbose_stream(), cls);); 
            int break_count;
            int min_bc = INT_MAX;
            unsigned min_bc_index = 0;
            for (unsigned i = 0; i < cls.m_lits.size(); ++i) {
                lit = cls.m_lits[i];
                break_count = flip(lit);
                if (break_count < min_bc) {
                    min_bc = break_count;
                    min_bc_index = i;
                }
                else if (break_count == min_bc && m_rng(5) == 1) {
                    min_bc_index = i;
                }
                int new_break_count = flip(~lit);
                if (-break_count != new_break_count) {
                    verbose_stream() << lit << "\n";
                    IF_VERBOSE(0, display(verbose_stream(), cls););
                    display(verbose_stream());
                    exit(0);
                }
                // VERIFY(-break_count == flip(~lit));
            }            
            if (m_rng(100) <= m_non_greedy_percent) {
                lit = cls.m_lits[m_rng(cls.m_lits.size())];
            }
            else {
                lit = cls.m_lits[min_bc_index];
            }
            flip(lit);
            return lit;
        }
        
        literal flip_soft() {
            literal lit;
            clause const& cls = pick_soft_clause();
            int break_count;
            int min_bc = INT_MAX;
            unsigned min_bc_index = 0;
            rational penalty = m_penalty;
            rational min_penalty = penalty;
            for (unsigned i = 0; i < cls.m_lits.size(); ++i) {
                lit = cls.m_lits[i];
                break_count = flip(lit);
                SASSERT(break_count >= 0);
                if (break_count == 0 && penalty > m_penalty) {
                    return lit;
                }
                if ((break_count < min_bc) ||
                    (break_count == min_bc && m_penalty < min_penalty)) {
                    min_bc = break_count;
                    min_bc_index = i;
                    min_penalty = m_penalty;
                }
                VERIFY(-break_count == flip(~lit));
            }            
            if (m_rng(100) <= m_non_greedy_percent) {
                lit = cls.m_lits[m_rng(cls.m_lits.size())];
            }
            else {
                // just do a greedy move:
                lit = cls.m_lits[min_bc_index];
            }
            flip(lit);
            return lit;
        }

        //
        // TODO: alternate version: loop over soft clauses and see if there is a flip that 
        // reduces the penalty while preserving the hard constraints.
        // 

        // crude selection strategy.
        clause const& pick_hard_clause() {
            SASSERT(!m_hard_false.empty());
            return m_clauses[m_hard_false.choose(m_rng)];
        }

        clause const& pick_soft_clause() {
            SASSERT(!m_soft_false.empty());
            return m_soft[m_soft_false.choose(m_rng)];
        }

        int flip(literal l) {
            m_assignment[l.var()] = !m_assignment[l.var()];
            int break_count = 0;
            unsigned_vector const& occh = m_hard_occ[l.var()];
            scoped_mpz value(mgr);            
            for (unsigned i = 0; i < occh.size(); ++i) {
                unsigned j = occh[i];
                clause& cls = m_clauses[j];
                value = cls.m_value;
                if (eval(cls)) {
                    if (m_hard_false.contains(j)) {
                        break_count--;
                        m_hard_false.remove(j);
                    }
                }
                else {
                    if (!m_hard_false.contains(j)) {
                        break_count++;
                        m_hard_false.insert(j);
                    }
                    else if (value < m_clauses[j].m_value) {
                    }
                }
            }
            unsigned_vector const& occs = m_soft_occ[l.var()];
            for (unsigned i = 0; i < occs.size(); ++i) {
                unsigned j = occs[i];
                if (eval(m_soft[j])) {
                    if (m_soft_false.contains(j)) {
                        m_penalty -= m_weights[j];
                        m_soft_false.remove(j);
                    }
                }
                else {
                    if (!m_soft_false.contains(j)) {
                        m_penalty += m_weights[j];
                        m_soft_false.insert(j);
                    }
                }
            }                

            TRACE("opt", tout << "flip: " << l << " num false: " << m_hard_false.num_elems() 
                  << " penalty: " << m_penalty << " break count: " << break_count << "\n";);
            return break_count;
        }

        literal mk_aux_literal(expr* f) {           
            unsigned var;
            expr_ref tmp(m);
            if (!m_decl2var.find(f, var)) {
                var = m_hard_occ.size();
                SASSERT(m_var2decl.size() == var);
                SASSERT(m_soft_occ.size() == var);
                m_hard_occ.push_back(unsigned_vector());
                m_soft_occ.push_back(unsigned_vector());
                VERIFY(m_orig_model->eval(f, tmp));
                m_assignment.push_back(m.is_true(tmp));
                m_decl2var.insert(f, var);
                m_var2decl.push_back(f);
            }
            return literal(var);            
        }
        void pad(scoped_mpz_vector& vec, unsigned sz, mpz& val) {
            for (unsigned i = 0; i < sz; ++i) {
                vec.push_back(val);
            }
        }
        literal mk_literal(expr* f) {
            if (m.is_not(f, f)) {
                literal result = mk_literal(f);
                if (result != null_literal) {
                    result.neg();
                }
                return result;
            }
            if (is_uninterp_const(f)) 
                return mk_aux_literal(to_app(f));            
            if (m.is_true(f))
                return true_literal;
            if (m.is_false(f))
                return false_literal;
            if (m.is_and(f)) {
                literal_vector lits;
                app* g = to_app(f);
                for (unsigned i = 0; i < g->get_num_args(); ++i) {
                    lits.push_back(mk_literal(g->get_arg(i)));
                }
                literal result = mk_aux_literal(f);
                for (unsigned i = 0; i < lits.size(); ++i) {
                    clause cls(mgr);
                    cls.m_lits.push_back(~result);
                    cls.m_weights.push_back(one);
                    cls.m_lits.push_back(lits[i]);
                    cls.m_weights.push_back(one);
                    cls.m_k = one;
                    cls.m_eq = false;
                    m_clauses.push_back(cls);  
                    m_orig_clauses.push_back(f);
                    lits[i].neg();
                }
                lits.push_back(result);
                clause cls(mgr);
                cls.m_lits.append(lits);
                pad(cls.m_weights, lits.size(), one);
                cls.m_k = one;
                cls.m_eq = false;
                m_clauses.push_back(cls); 
                m_orig_clauses.push_back(f);
                return result;
            }
            if (m.is_or(f)) {
                literal_vector lits;
                app* g = to_app(f);
                for (unsigned i = 0; i < g->get_num_args(); ++i) {
                    lits.push_back(mk_literal(g->get_arg(i)));
                }
                literal result = mk_aux_literal(f);
                for (unsigned i = 0; i < lits.size(); ++i) {
                    clause cls(mgr);
                    cls.m_lits.push_back(result);
                    cls.m_weights.push_back(one);
                    cls.m_lits.push_back(~lits[i]);
                    cls.m_weights.push_back(one);
                    cls.m_k = one;
                    cls.m_eq = false;
                    m_clauses.push_back(cls);  
                    m_orig_clauses.push_back(f);
                }
                lits.push_back(~result);
                clause cls(mgr);
                cls.m_lits.append(lits);
                pad(cls.m_weights, lits.size(), one);
                cls.m_k = one;
                cls.m_eq = false;
                m_clauses.push_back(cls);       
                m_orig_clauses.push_back(f);
                return result;
            }
            expr* x, *y;
            if ((m.is_eq(f, x, y) && m.is_bool(x)) || m.is_iff(f, x, y)) {                
                literal a = mk_literal(x);
                literal b = mk_literal(y);
                literal result = mk_aux_literal(f);
                clause cls(mgr);
                cls.m_lits.push_back(~result);
                cls.m_lits.push_back(~a);
                cls.m_lits.push_back(b);
                pad(cls.m_weights, 3, one);
                cls.m_k = one;
                cls.m_eq = false;
                m_clauses.push_back(cls);
                m_orig_clauses.push_back(f); // actually, the clause that defines f
                cls.m_lits[0] = ~result;
                cls.m_lits[1] = a;
                cls.m_lits[2] = ~b;
                m_clauses.push_back(cls);
                m_orig_clauses.push_back(f);
                cls.m_lits[0] = result;
                cls.m_lits[1] = a;
                cls.m_lits[2] = b;
                m_clauses.push_back(cls);
                m_orig_clauses.push_back(f);
                cls.m_lits[0] = result;
                cls.m_lits[1] = ~a;
                cls.m_lits[2] = ~b;
                m_clauses.push_back(cls);
                m_orig_clauses.push_back(f);
                return result;
            }            
            if (pb.is_ge(f)) {
                
            }
            IF_VERBOSE(0, verbose_stream() << "not handled: " << mk_pp(f, m) << "\n";);
            return mk_aux_literal(f);
        }

        bool compile_clause(expr* _f, clause& cls) {
            expr_ref tmp(m);
            m_rewrite(_f, tmp);
            if (!is_app(tmp)) return false;            
            app* f = to_app(tmp);
            expr* f2;
            unsigned sz = f->get_num_args();
            expr* const* args = f->get_args();
            literal lit;
            rational coeff, k;
            if (m.is_not(f, f2) && pb.is_ge(f2)) {
                // ~(ax+by >= k) 
                // <=>
                // ax + by < k
                // <=>
                // -ax - by >= -k + 1
                // <=>
                // a(1-x) + b(1-y) >= -k + a + b + 1
                sz = to_app(f2)->get_num_args();
                args = to_app(f2)->get_args();
                k = pb.get_k(f2);
                SASSERT(k.is_int());
                k.neg();
                k += rational::one();
                expr_ref_vector args(m);
                vector<rational> coeffs;
                for (unsigned i = 0; i < sz; ++i) {
                    args.push_back(m.mk_not(to_app(f2)->get_arg(i)));
                    coeffs.push_back(pb.get_coeff(f2, i));
                    k += pb.get_coeff(f2, i);
                }
                tmp = pb.mk_ge(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), k);
                return compile_clause(tmp, cls);
            }
            else if (pb.is_ge(f) || pb.is_eq(f)) {
                k = pb.get_k(f);
                SASSERT(k.is_int());
                cls.m_k = k.to_mpq().numerator();
                for (unsigned i = 0; i < sz; ++i) {
                    coeff = pb.get_coeff(f, i);                    
                    SASSERT(coeff.is_int());
                    lit = mk_literal(args[i]);
                    if (lit == null_literal) return false;
                    if (lit == false_literal) continue;
                    if (lit == true_literal) {
                        cls.m_k -= coeff.to_mpq().numerator();
                        continue;
                    }
                    cls.m_lits.push_back(lit);
                    cls.m_weights.push_back(coeff.to_mpq().numerator());
                    if (get_value(lit)) {
                        cls.m_value += coeff.to_mpq().numerator();
                    }
                }
                cls.m_eq = pb.is_eq(f);
            }
            else if (m.is_or(f)) {
                for (unsigned i = 0; i < sz; ++i) {
                    lit = mk_literal(args[i]);
                    if (lit == null_literal) return false;
                    if (lit == false_literal) continue;
                    if (lit == true_literal) return false;
                    cls.m_lits.push_back(lit);
                    cls.m_weights.push_back(mpz(1));
                    if (get_value(lit)) {
                        cls.m_value += mpz(1);
                    }
                }
                cls.m_eq = false;
                cls.m_k = mpz(1);
            }
            else if (m.is_true(f)) {
                return false;
            }
            else {
                lit = mk_literal(f);
                if (lit == null_literal) return false;
                SASSERT(lit != false_literal && lit != true_literal);
                cls.m_lits.push_back(lit);
                cls.m_weights.push_back(mpz(1));
                cls.m_eq = true;
                cls.m_k = mpz(1);
            }
            return true;
        }
        
    };

    pb_sls::pb_sls(ast_manager& m) {
        m_imp = alloc(imp, m);
    }       
    pb_sls::~pb_sls() {
        dealloc(m_imp);
    }
    void pb_sls::add(expr* f) {
        m_imp->add(f);
    }
    void pb_sls::add(expr* f, rational const& w) {
        m_imp->add(f, w);
    }
    void pb_sls::set_model(model_ref& mdl) {
        m_imp->set_model(mdl);
    }
    lbool pb_sls::operator()() {
        return (*m_imp)();
    }
    void pb_sls::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }
    void pb_sls::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void pb_sls::get_model(model_ref& mdl) {
        m_imp->get_model(mdl);
    }
    void pb_sls::reset() {
        m_imp->reset();
    }
    bool pb_sls::soft_holds(unsigned index) {
        return m_imp->soft_holds(index);
    }
    void pb_sls::updt_params(params_ref& p) {
        m_imp->updt_params(p);
    }

}
