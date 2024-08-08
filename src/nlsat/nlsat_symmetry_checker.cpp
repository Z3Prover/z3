#include "nlsat/nlsat_symmetry_checker.h"

struct Debug_Tracer {
    std::string tag_str;
    Debug_Tracer(std::string _tag_str) {
        tag_str = _tag_str;
        TRACE("linxi_symmetry_checker", 
            tout << "Debug_Tracer begin\n";
            tout << tag_str << "\n";
        );
    }
    ~Debug_Tracer() {
        TRACE("linxi_symmetry_checker", 
            tout << "Debug_Tracer end\n";
            tout << tag_str << "\n";
        );
    }
};

// #define _LINXI_DEBUG

#ifdef _LINXI_DEBUG
#define LINXI_DEBUG_CORE(x) std::stringstream DEBUG_ss_##x; DEBUG_ss_##x << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__; Debug_Tracer DEBUG_dt_##x(DEBUG_ss_##x.str());
#define LINXI_DEBUG_TRANS(x) LINXI_DEBUG_CORE(x);
#define LINXI_DEBUG LINXI_DEBUG_TRANS(__LINE__);
#define LINXI_HERE TRACE("linxi_symmetry_checker", tout << "here\n";);
#else
#define LINXI_DEBUG { }((void) 0 );
#define LINXI_HERE { }((void) 0 );
#endif



namespace nlsat {
    struct Symmetry_Checker::imp {
        // solver              &sol;
        pmanager            &pm;
        unsynch_mpq_manager &qm;
        const clause_vector &clauses;
        const atom_vector   &atoms;
        const bool_vector         &is_int;
        const unsigned      arith_var_num;
        // vector<unsigned long long> vars_hash;
        vector<vector<unsigned>> vars_occur;
        bool is_check;
        var tx, ty;
        struct Variable_Information {
            unsigned long long hash_value;
            unsigned deg;
            var x;
            bool is_int;
            bool operator< (const Variable_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Variable_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (deg != rhs.deg)
                    return false;
                if (x != rhs.x)
                    return false;
                if (is_int != rhs.is_int)
                    return false;
                return true;
            }
            bool operator!= (const Variable_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        unsigned long long VAR_BASE = 601;
        void collect_var_info(Variable_Information &var_info, var x, unsigned deg) {
            LINXI_DEBUG;
            if (is_check) {
                if (x == tx) {
                    x = ty;
                }
                else if (x == ty) {
                    x = tx;
                }
                else {
                    // do nothing
                }
            }
            else {
                vars_occur[x].push_back(deg);
            }
            var_info.deg = deg;
            var_info.x = x;
            var_info.is_int = is_int[x];
            var_info.hash_value = 0;
            for (unsigned i = 0; i < deg; ++i) {
                var_info.hash_value = var_info.hash_value*VAR_BASE + (unsigned long long)x;
            }
            var_info.hash_value = var_info.hash_value*VAR_BASE + (unsigned long long)var_info.is_int;
        }
        struct Monomial_Information {
            unsigned long long hash_value;
            unsigned long long coef;
            vector<Variable_Information> vars_info;
            bool operator< (const Monomial_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Monomial_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (coef != rhs.coef)
                    return false;
                if (vars_info.size() != rhs.vars_info.size())
                    return false;
                for (unsigned i = 0, sz = vars_info.size(); i < sz; ++i) {
                    if (vars_info[i] != rhs.vars_info[i])
                        return false;
                }
                return true;
            }
            bool operator!= (const Monomial_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        unsigned long long MONO_BASE = 99991;

        void collect_mono_info(Monomial_Information &mono_info, monomial *m, unsigned long long coef) {
            LINXI_DEBUG;
            unsigned sz = pm.size(m);
            mono_info.vars_info.resize(sz);
            for (unsigned i = 0; i < sz; ++i) {
                collect_var_info(mono_info.vars_info[i], pm.get_var(m, i), pm.degree(m, i));
            }
            mono_info.coef = coef;
            mono_info.hash_value = coef;
            std::sort(mono_info.vars_info.begin(), mono_info.vars_info.end());
            for (unsigned i = 0; i < sz; ++i) {
                mono_info.hash_value = mono_info.hash_value*MONO_BASE + mono_info.vars_info[i].hash_value;
            }
        }
        struct Polynomial_Information {
            unsigned long long hash_value;
            bool is_even;
            vector<Monomial_Information> monos_info;
            bool operator< (const Polynomial_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Polynomial_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (is_even != rhs.is_even)
                    return false;
                if (monos_info.size() != rhs.monos_info.size())
                    return false;
                for (unsigned i = 0, sz = monos_info.size(); i < sz; ++i) {
                    if (monos_info[i] != rhs.monos_info[i])
                        return false;
                }
                return true;
            }
            bool operator!= (const Polynomial_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        unsigned long long POLY_BASE = 99991;
        void collect_poly_info(Polynomial_Information &poly_info, poly *p, bool is_even) {
            LINXI_DEBUG;
            unsigned sz = pm.size(p);
            poly_info.monos_info.resize(sz);
            for (unsigned i = 0; i < sz; ++i) {
                collect_mono_info(poly_info.monos_info[i], pm.get_monomial(p, i), qm.get_uint64(pm.coeff(p, i)));
            }
            poly_info.hash_value = 0;
            std::sort(poly_info.monos_info.begin(), poly_info.monos_info.end());
            for (unsigned i = 0; i < sz; ++i) {
                poly_info.hash_value = poly_info.hash_value*POLY_BASE + poly_info.monos_info[i].hash_value;
            }
            poly_info.is_even = is_even;
            if (is_even) {
                poly_info.hash_value = poly_info.hash_value*poly_info.hash_value;
            }
        }
        struct Atom_Information {
            unsigned long long hash_value;
            atom::kind akd;
            vector<Polynomial_Information> polys_info;
            bool operator< (const Atom_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Atom_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (akd != rhs.akd)
                    return false;
                if (polys_info.size() != rhs.polys_info.size())
                    return false;
                for (unsigned i = 0, sz = polys_info.size(); i < sz; ++i) {
                    if (polys_info[i] != rhs.polys_info[i])
                        return false;
                }
                return true;
            }
            bool operator!= (const Atom_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        unsigned long long ATOM_BASE = 233;
        void collect_atom_info(Atom_Information &atom_info, ineq_atom *iat) {
            LINXI_DEBUG;
            unsigned sz = iat->size();
            atom_info.polys_info.resize(sz);
            for (unsigned i = 0; i < sz; ++i) {
                collect_poly_info(atom_info.polys_info[i], iat->p(i), iat->is_even(i));
            }
            atom_info.hash_value = 0;
            std::sort(atom_info.polys_info.begin(), atom_info.polys_info.end());
            for (unsigned i = 0; i < sz; ++i) {
                atom_info.hash_value = atom_info.hash_value*ATOM_BASE + atom_info.polys_info[i].hash_value;
            }
            atom_info.akd = iat->get_kind();
            atom_info.hash_value = atom_info.hash_value*ATOM_BASE + (unsigned long long)atom_info.akd;
        }
        struct Literal_Information {
            unsigned long long hash_value;
            vector<Atom_Information> atom_info; // not atoms
            bool operator< (const Literal_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Literal_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (atom_info.size() != rhs.atom_info.size())
                    return false;
                for (unsigned i = 0, sz = atom_info.size(); i < sz; ++i) {
                    if (atom_info[i] != rhs.atom_info[i])
                        return false;
                }
                return true;
            }
            bool operator!= (const Literal_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        void collect_lit_info(Literal_Information &lit_info, literal lit) {
            LINXI_DEBUG;
            atom *at = atoms[lit.var()];
            if (at == nullptr || !at->is_ineq_atom()) {
                lit_info.hash_value = lit.to_uint();
            }
            else {
                lit_info.atom_info.resize(1);
                collect_atom_info(lit_info.atom_info[0], to_ineq_atom(at));
                lit_info.hash_value = lit_info.atom_info[0].hash_value;
            }
        }
        struct Clause_Information {
            unsigned long long hash_value;
            vector<Literal_Information> lits_info;
            bool operator< (const Clause_Information &rhs) const {
                return hash_value < rhs.hash_value;
            }
            bool operator== (const Clause_Information &rhs) const {
                if (hash_value != rhs.hash_value)
                    return false;
                if (lits_info.size() != rhs.lits_info.size())
                    return false;
                for (unsigned i = 0, sz = lits_info.size(); i < sz; ++i) {
                    if (lits_info[i] != rhs.lits_info[i])
                        return false;
                }
                return true;
            }
            bool operator!= (const Clause_Information &rhs) const {
                return !(*this == rhs);
            }
        };
        unsigned long long CLA_BASE = 9973;
        void collect_cla_info(Clause_Information &cla_info, clause *cla) {
            LINXI_DEBUG;
            unsigned sz = cla->size();
            cla_info.lits_info.resize(sz);
            for (unsigned i = 0; i < sz; ++i) {
                literal lit = (*cla)[i];
                collect_lit_info(cla_info.lits_info[i], lit);
            }
            cla_info.hash_value = 0;
            std::sort(cla_info.lits_info.begin(), cla_info.lits_info.end());
            for (unsigned i = 0; i < sz; ++i) {
                cla_info.hash_value = cla_info.hash_value*CLA_BASE + cla_info.lits_info[i].hash_value;
            }
        }
        
        void collect_clas_info(vector<Clause_Information> &clas_info) {
            LINXI_DEBUG;
            unsigned sz = clauses.size();
            clas_info.resize(sz);
            for (unsigned i = 0; i < sz; ++i) {
                collect_cla_info(clas_info[i], clauses[i]);
            }
            std::sort(clas_info.begin(), clas_info.end());
            if (!is_check) {
                for (unsigned i = 0; i < arith_var_num; ++i) {
                    std::sort(vars_occur[i].begin(), vars_occur[i].begin());
                }
            }
        }
        vector<Clause_Information> ori_clas_info;
        imp(pmanager &_pm, unsynch_mpq_manager &_qm, const clause_vector &_clauses, const atom_vector &_atoms, const bool_vector &_is_int, const unsigned &_arith_var_num) : 
            // sol(_sol),
            pm(_pm),
            qm(_qm),
            clauses(_clauses),
            atoms(_atoms),
            is_int(_is_int),
            arith_var_num(_arith_var_num),
            is_check(false) {
            vars_occur.resize(arith_var_num);
            collect_clas_info(ori_clas_info);
            // vars_hash.resize(arith_var_num, 0);
        }
        vector<Clause_Information> check_clas_info;
        bool check_occur_same(var x, var y) {
            if (vars_occur[x].size() != vars_occur[y].size())
                return false;
            for (unsigned i = 0, sz = vars_occur[x].size(); i < sz; ++i) {
                if (vars_occur[x][i] != vars_occur[y][i])
                    return false;
            }
            return true;
        }
        bool check_symmetry(var x, var y) {
            if (!check_occur_same(x, y)) {
                return false;
            }
            is_check = true;
            tx = x, ty = y;
            collect_clas_info(check_clas_info);
            for (unsigned i = 0, sz = clauses.size(); i < sz; ++i) {
                if (ori_clas_info[i] != check_clas_info[i])
                    return false;
            }
            return true;
        }
    };
    Symmetry_Checker::Symmetry_Checker(pmanager &_pm, unsynch_mpq_manager &_qm, const clause_vector &_clauses, const atom_vector &_atoms, const bool_vector &_is_int, const unsigned &_arith_var_num) {
        LINXI_DEBUG;
        // m_imp = alloc(imp, _sol, _pm, _am, _clauses, _learned, _atoms, _arith_var_num);
        m_imp = alloc(imp, _pm, _qm, _clauses, _atoms, _is_int, _arith_var_num);
    }
    Symmetry_Checker::~Symmetry_Checker() {
        LINXI_DEBUG;
        dealloc(m_imp);
    }
    // bool Symmetry_Checker::operator()() {
    //     LINXI_DEBUG;
        
    // }
    bool Symmetry_Checker::check_symmetry(var x, var y) {
        return m_imp->check_symmetry(x, y);
    }
}