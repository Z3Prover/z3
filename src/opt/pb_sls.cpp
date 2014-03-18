#include "pb_sls.h"
#include "smt_literal.h"
#include "ast_pp.h"

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
        rational         m_value;        // current value of soft constraints
        vector<unsigned_vector>  m_pos, m_neg;   // positive and negative occurs.
        svector<bool>    m_assignment;   // current assignment.
        obj_map<expr, unsigned> m_expr2var; // map expressions to Boolean variables.
        ptr_vector<expr> m_var2expr;        // reverse map
        
        imp(ast_manager& m):
            m(m),
            pb(m),
            m_cancel(false)
        {}

        ~imp() {
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
            }
        }

        void init_value(expr* f, bool b) {
            literal lit = mk_literal(f);
            SASSERT(!lit.sign());
            //if (m_assignment[lit.var()] != b) {
            m_assignment[lit.var()] = b;                
            //}
        }

        lbool operator()() {
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
        }
        void updt_params(params_ref& p) {
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
                    var = m_pos.size();
                    SASSERT(m_expr2var.size() == var);
                    m_pos.push_back(unsigned_vector());
                    m_neg.push_back(unsigned_vector());
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
