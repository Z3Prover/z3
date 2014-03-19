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
#include "uint_set.h"

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
        };
        
        ast_manager&     m;
        pb_util          pb;
        unsynch_mpz_manager mgr;
        volatile bool    m_cancel;
        vector<clause>   m_clauses;      // clauses to be satisfied        
        vector<clause>   m_soft;         // soft constraints
        vector<rational> m_weights;      // weights of soft constraints
        rational         m_penalty;      // current penalty of soft constraints
        vector<unsigned_vector>  m_hard_occ, m_soft_occ;  // variable occurrence
        svector<bool>    m_assignment;   // current assignment.
        obj_map<expr, unsigned> m_expr2var; // map expressions to Boolean variables.
        ptr_vector<expr> m_var2expr;        // reverse map
        uint_set         m_hard_false;      // list of hard clauses that are false.
        uint_set         m_soft_false;      // list of soft clauses that are false.
        unsigned         m_max_flips;
        imp(ast_manager& m):
            m(m),
            pb(m),
            m_cancel(false)
        {
            m_max_flips = 100;
        }

        ~imp() {
        }

        unsigned max_flips() {
            return m_max_flips;
        }

        void add(expr* f) {
            clause cls(mgr);
            if (compile_clause(f, cls)) {
                m_clauses.push_back(cls);
            }
        }
        void add(expr* f, rational const& w) {
            clause cls(mgr);
            if (compile_clause(f, cls)) {
                m_clauses.push_back(cls);
                m_weights.push_back(w);
            }
        }

        void init_value(expr* f, bool b) {
            literal lit = mk_literal(f);
            SASSERT(!lit.sign());
            m_assignment[lit.var()] = b;                
        }

        lbool operator()() {
            init();
            for (unsigned i = 0; i < max_flips(); ++i) {
                flip();
                if (m_cancel) {
                    return l_undef;
                }
            }
            return l_undef;
        }

        bool get_value(expr* f) {
            unsigned var;
            if (m_expr2var.find(f, var)) {
                return m_assignment[var];
            }
            UNREACHABLE();
            return true;
        }
        bool get_value(literal l) {
            return l.sign() ^ m_assignment[l.var()];
        }
        void set_cancel(bool f) {
            m_cancel = f;
        }
        void collect_statistics(statistics& st) const {
        }
        void get_model(model_ref& mdl) {
            NOT_IMPLEMENTED_YET();
        }
        void updt_params(params_ref& p) {
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
                    occ[lit.var()].push_back(i);
                }
            }
        }
        
        void init() {
            // initialize the occurs vectors.
            init_occ(m_clauses, m_hard_occ);
            init_occ(m_soft, m_soft_occ);
            // add clauses that are false.
            for (unsigned i = 0; i < m_clauses.size(); ++i) {
                if (!eval(m_clauses[i])) {
                    m_hard_false.insert(i);
                }
            }
            m_penalty.reset();
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                if (!eval(m_soft[i])) {
                    m_soft_false.insert(i);
                    m_penalty += m_weights[i];
                }
            }
        }
        
        void flip() {
            if (m_hard_false.empty()) {
                flip_soft();
            }
            else {
                flip_hard();
            }            
        }
        
        void flip_hard() {
            SASSERT(!m_hard_false.empty());
            clause const& cls = pick_hard_clause();
            int break_count;
            int min_bc = INT_MAX;
            unsigned min_bc_index = 0;
            for (unsigned i = 0; i < cls.m_lits.size(); ++i) {
                literal lit = cls.m_lits[i];
                break_count = flip(lit);
                if (break_count <= 0) {
                    return;
                }
                if (break_count < min_bc) {
                    min_bc = break_count;
                    min_bc_index = i;
                }
                VERIFY(-break_count == flip(~lit));
            }            
            // just do a greedy move:
            flip(cls.m_lits[min_bc_index]);
        }
        
        void flip_soft() {
            clause const& cls = pick_soft_clause();
            int break_count;
            int min_bc = INT_MAX;
            unsigned min_bc_index = 0;
            rational penalty = m_penalty;
            rational min_penalty = penalty;
            for (unsigned i = 0; i < cls.m_lits.size(); ++i) {
                literal lit = cls.m_lits[i];
                break_count = flip(lit);
                SASSERT(break_count >= 0);
                if (break_count == 0 && penalty > m_penalty) {
                    // TODO: save into best so far if this qualifies.
                    return;
                }
                if ((break_count < min_bc) ||
                    (break_count == min_bc && m_penalty < min_penalty)) {
                    min_bc = break_count;
                    min_bc_index = i;
                    min_penality = m_penalty;
                }
                VERIFY(-break_count == flip(~lit));
            }            
            // just do a greedy move:
            flip(cls.m_lits[min_bc_index]);
        }

        //
        // TODO: alternate version: loop over soft clauses and see if there is a flip that 
        // reduces the penalty while preserving the hard constraints.
        // 

        // crude selection strategy.
        clause const& pick_hard_clause() {
            SASSERT(!m_hard_false.empty());
            uint_set::iterator it = m_hard_false.begin();
            uint_set::iterator end = m_hard_false.end();
            SASSERT(it != end);
            return m_clauses[*it];
        }

        clause const& pick_soft_clause() {
            SASSERT(!m_soft_false.empty());
            uint_set::iterator it = m_soft_false.begin();
            uint_set::iterator end = m_soft_false.end();
            SASSERT(it != end);
            unsigned index = *it;
            rational penalty = m_weights[index];
            ++it;
            for (; it != end; ++it) {
                if (m_weights[*it] > penalty) {
                    index = *it;
                    penalty = m_weights[*it];
                }
            }
            return m_soft[index];
        }

        int flip(literal l) {
            SASSERT(get_value(l));
            m_assignment[l.var()] = !m_assignment[l.var()];
            int break_count = 0;
            {
                unsigned_vector const& occ = m_hard_occ[l.var()];
                for (unsigned i = 0; i < occ.size(); ++i) {
                    unsigned j = occ[i];
                    if (eval(m_clauses[j])) {
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
                    }
                }
            }
            {
                unsigned_vector const& occ = m_soft_occ[l.var()];
                for (unsigned i = 0; i < occ.size(); ++i) {
                    unsigned j = occ[i];
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
            }

            SASSERT(get_value(~l));
            return break_count;
        }

        literal mk_literal(expr* f) {
            literal result;
            bool sign = false;
            while (m.is_not(f, f)) {
                sign = !sign;
            }
            if (m.is_true(f)) {
                result = true_literal;
            }
            else if (m.is_false(f)) {
                result = false_literal;
            }
            else {
                unsigned var;
                if (!m_expr2var.find(f, var)) {
                    var = m_hard_occ.size();
                    SASSERT(m_expr2var.size() == var);
                    m_hard_occ.push_back(unsigned_vector());
                    m_soft_occ.push_back(unsigned_vector());
                    m_assignment.push_back(false);
                    m_expr2var.insert(f, var);
                    m_var2expr.push_back(f);
                }
                result = literal(var);
            }
            if (sign) {
                result.neg();
            }
            return result;
        }

        bool compile_clause(expr* _f, clause& cls) {
            if (!is_app(_f)) return false;
            app* f = to_app(_f);
            unsigned sz = f->get_num_args();
            expr* const* args = f->get_args();
            literal lit;
            rational coeff;
            if (pb.is_ge(f) || pb.is_eq(f)) {
                for (unsigned i = 0; i < sz; ++i) {
                    coeff = pb.get_coeff(f, i);
                    SASSERT(coeff.is_int());
                    lit = mk_literal(args[i]);
                    if (lit == null_literal) return false;
                    SASSERT(lit != false_literal && lit != true_literal);
                    cls.m_lits.push_back(lit);
                    cls.m_weights.push_back(coeff.to_mpq().numerator());
                    if (get_value(lit)) {
                        cls.m_value += coeff.to_mpq().numerator();
                    }
                }
                cls.m_eq = pb.is_eq(f);
                coeff = pb.get_k(f);
                SASSERT(coeff.is_int());
                cls.m_k = coeff.to_mpq().numerator();
            }
            else if (m.is_or(f)) {
                for (unsigned i = 0; i < sz; ++i) {
                    lit = mk_literal(args[i]);
                    if (lit == null_literal) return false;
                    SASSERT(lit != false_literal && lit != true_literal);
                    cls.m_lits.push_back(lit);
                    cls.m_weights.push_back(mpz(1));
                    if (get_value(lit)) {
                        cls.m_value += mpz(1);
                    }
                }
                cls.m_eq = false;
                cls.m_k = mpz(1);
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
    void pb_sls::init_value(expr* f, bool b) {
        m_imp->init_value(f, b);
    }
    lbool pb_sls::operator()() {
        return (*m_imp)();
    }
    bool pb_sls::get_value(expr* f) {
        return m_imp->get_value(f);
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
    void pb_sls::updt_params(params_ref& p) {
        m_imp->updt_params(p);
    }

}
