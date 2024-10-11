#include "nlsat/nlsat_variable_ordering_strategy.h"

namespace nlsat {
    struct vos_var_info_collector::imp {
        pmanager &          pm;
        atom_vector const & m_atoms;
        unsigned num_vars;
        Variable_Ordering_Strategy_Type m_vos_type;

        /** Maximum degree of this variable. */
        unsigned_vector m_max_degree;
        /** Sum of degrees of this variable within all polynomials. */
        unsigned_vector m_sum_poly_degree;
        /** Number of polynomials that contain this variable. */
        unsigned_vector m_num_polynomials;
        
        /** Maximum degree of the leading coefficient of this variable. */
        unsigned_vector m_max_lc_degree;
        /** Maximum of total degrees of terms that contain this variable. */
        unsigned_vector m_max_terms_tdegree;
        /** Sum of degrees of this variable within all terms. */
        unsigned_vector m_sum_term_degree;
        /** Number of terms that contain this variable. */
        unsigned_vector m_num_terms;

        
        unsigned_vector m_num_uni;
        numeral_vector m_coeffs;
        

        imp(pmanager & _pm, atom_vector const & atoms, unsigned _num_vars, unsigned _vos_type):
            pm(_pm),
            m_atoms(atoms),
            num_vars(_num_vars),
            m_vos_type(Variable_Ordering_Strategy_Type(_vos_type)) {
            
            m_max_degree.resize(num_vars, 0);
            m_sum_poly_degree.resize(num_vars, 0);
            m_num_polynomials.resize(num_vars, 0);

            if (m_vos_type != ONLYPOLY) {
                m_max_lc_degree.resize(num_vars, 0);
                m_max_terms_tdegree.resize(num_vars, 0);
                m_sum_term_degree.resize(num_vars, 0);
                m_num_terms.resize(num_vars, 0);

                
                m_num_uni.resize(num_vars, 0);
                m_coeffs.resize(num_vars, 0);
                
            }
        }

        void collect(monomial * m) {
            unsigned mdeg = 0;
            for (unsigned i = 0, sz = pm.size(m); i < sz; ++i) {
                var x = pm.get_var(m, i);
                mdeg += pm.degree_of(m, x);
                ++m_num_terms[x];
            }

            for (unsigned i = 0, sz = pm.size(m); i < sz; ++i) {
                var x = pm.get_var(m, i);
                m_sum_term_degree[x] += mdeg;
                if (mdeg > m_max_terms_tdegree[x])
                    m_max_terms_tdegree[x] = mdeg;
                unsigned lc_deg = mdeg - pm.degree_of(m, x);
                if (lc_deg > m_max_lc_degree[x])
                    m_max_lc_degree[x] = lc_deg;
            }
        }

        void collect(poly * p) {
            var_vector vec_vars;
            pm.vars(p, vec_vars);

            if (m_vos_type == UNIVARIATE) {
                if (vec_vars.size() == 1)
                    ++m_num_uni[vec_vars[0]];
            }
            
            for (unsigned i = 0, sz = vec_vars.size(); i < sz; ++i) {
                var x = vec_vars[i];
                unsigned k = pm.degree(p, x);
                ++m_num_polynomials[x];
                m_sum_poly_degree[x] += k;
                if (k > m_max_degree[x])
                    m_max_degree[x] = k;
                
                if (m_vos_type == FEATURE){
                    for (unsigned kl = 0; kl <= k; kl++) {
                        scoped_numeral curr(pm.m());
                        if (pm.const_coeff(p, x, kl, curr)) {
                            pm.m().abs(curr);
                            if (pm.m().gt(curr, m_coeffs[x])) {
                                pm.m().set(m_coeffs[x], curr);
                            }
                        }
                    }
                }
                
            }
            
            if (m_vos_type != ONLYPOLY && m_vos_type != UNIVARIATE){
                for (unsigned i = 0, sz = pm.size(p); i < sz; ++i) {
                    collect(pm.get_monomial(p, i));
                }
            }
        }

        void collect(literal l) {
            bool_var b = l.var();
            atom * a = m_atoms[b];
            if (a == nullptr)
                return;
            if (a->is_ineq_atom()) {
                unsigned sz = to_ineq_atom(a)->size();
                for (unsigned i = 0; i < sz; i++) {
                    collect(to_ineq_atom(a)->p(i));
                }
            }
            else {
                collect(to_root_atom(a)->p());
            }
        }
        
        void collect(clause const & c) {
            unsigned sz = c.size();
            for (unsigned i = 0; i < sz; i++) 
                collect(c[i]);
        }

        void collect(clause_vector const & cs) {
            unsigned sz = cs.size();
            for (unsigned i = 0; i < sz; i++) 
                collect(*(cs[i]));
        }

        
       struct univariate_reorder_lt {
            vos_var_info_collector::imp const *m_info;
            univariate_reorder_lt(vos_var_info_collector::imp const *info):m_info(info) {}
            bool operator()(var x, var y) const {
                if (m_info->m_num_uni[x] != m_info->m_num_uni[y])
                    return m_info->m_num_uni[x] > m_info->m_num_uni[y];
                return x < y;
            }
        };

        struct feature_reorder_lt {
            vos_var_info_collector::imp const *m_info;
            feature_reorder_lt(vos_var_info_collector::imp const * info): m_info(info){}
            bool operator()(var x, var y) const {
                if (m_info->m_max_degree[x] != m_info->m_max_degree[y])
                    return m_info->m_max_degree[x] > m_info->m_max_degree[y];
                if (m_info->m_max_terms_tdegree[x] != m_info->m_max_terms_tdegree[y])
                    return m_info->m_max_terms_tdegree[x] > m_info->m_max_terms_tdegree[y];
                if (!m_info->pm.m().eq(m_info->m_coeffs[x], m_info->m_coeffs[y])) {
                    return m_info->pm.m().lt(m_info->m_coeffs[x], m_info->m_coeffs[y]);
                }
                return x < y;
            }
        };
        struct brown_reorder_lt {
            vos_var_info_collector::imp const *m_info;
            brown_reorder_lt(vos_var_info_collector::imp const *info):m_info(info) {}
            bool operator()(var x, var y) const {
                // if (a.max_degree != b.max_degree)
                //     return a.max_degree > b.max_degree;
                // if (a.max_terms_tdegree != b.max_terms_tdegree)
                //     return a.max_terms_tdegree > b.max_terms_tdegree;
                // return a.num_terms > b.num_terms;
                if (m_info->m_max_degree[x] != m_info->m_max_degree[y])
                    return m_info->m_max_degree[x] > m_info->m_max_degree[y];
                if (m_info->m_max_terms_tdegree[x] != m_info->m_max_terms_tdegree[y])
                    return m_info->m_max_terms_tdegree[x] > m_info->m_max_terms_tdegree[y];
                if (m_info->m_num_terms[x] != m_info->m_num_terms[y])
                    return m_info->m_num_terms[x] > m_info->m_num_terms[y];
                return x < y;
            }
        };
        struct triangular_reorder_lt {
            const vos_var_info_collector::imp *m_info;
            triangular_reorder_lt(vos_var_info_collector::imp const *info):m_info(info) {}
            bool operator()(var x, var y) const {
                // if (a.max_degree != b.max_degree)
                //     return a.max_degree > b.max_degree;
                // if (a.max_lc_degree != b.max_lc_degree)
                //     return a.max_lc_degree > b.max_lc_degree;
                // return a.sum_poly_degree > b.sum_poly_degree;
                if (m_info->m_max_degree[x] != m_info->m_max_degree[y])
                    return m_info->m_max_degree[x] > m_info->m_max_degree[y];
                if (m_info->m_max_lc_degree[x] != m_info->m_max_lc_degree[y])
                    return m_info->m_max_lc_degree[x] > m_info->m_max_lc_degree[y];
                if (m_info->m_sum_poly_degree[x] != m_info->m_sum_poly_degree[y])
                    return m_info->m_sum_poly_degree[x] > m_info->m_sum_poly_degree[y];
                return x < y;
            }
        };
        struct onlypoly_reorder_lt {
            const vos_var_info_collector::imp *m_info;
            onlypoly_reorder_lt(vos_var_info_collector::imp const *info):m_info(info) {}
            bool operator()(var x, var y) const {
                // high degree first
                if (m_info->m_max_degree[x] != m_info->m_max_degree[y])
                    return m_info->m_max_degree[x] > m_info->m_max_degree[y];
                // 
                if (m_info->m_sum_poly_degree[x] != m_info->m_sum_poly_degree[y])
                    return m_info->m_sum_poly_degree[x] > m_info->m_sum_poly_degree[y];
                // more constrained first
                if (m_info->m_num_polynomials[x] != m_info->m_num_polynomials[y])
                    return m_info->m_num_polynomials[x] > m_info->m_num_polynomials[y];
                return x < y;
            }
        };
        bool check_invariant() const {return true;} // what is the invariant
        void operator()(var_vector &perm) {
            var_vector new_order;
            for (var x = 0; x < num_vars; x++) {
                new_order.push_back(x);
            }
            if (m_vos_type == BROWN) {
                std::sort(new_order.begin(), new_order.end(), brown_reorder_lt(this));
            }
            else if (m_vos_type == TRIANGULAR) {
                std::sort(new_order.begin(), new_order.end(), triangular_reorder_lt(this));
            }
            else if (m_vos_type == ONLYPOLY) {
                std::sort(new_order.begin(), new_order.end(), onlypoly_reorder_lt(this));
            }
            
            else if(m_vos_type == UNIVARIATE){
                std::sort(new_order.begin(), new_order.end(), univariate_reorder_lt(this));
            }
            else if(m_vos_type == FEATURE){
                std::sort(new_order.begin(), new_order.end(), feature_reorder_lt(this));
            }
            
            else {
                UNREACHABLE();
            }
            TRACE("reorder", 
                tout << "new order: ";
                for (unsigned i = 0; i < num_vars; i++) 
                    tout << new_order[i] << " ";
                tout << "\n";
            );
            perm.resize(num_vars, 0);
            for (var x = 0; x < num_vars; x++) {
                perm[new_order[x]] = x;
            }
            
            SASSERT(check_invariant());
        }
        // std::ostream& display(std::ostream & out, display_var_proc const & proc) {
        //     unsigned sz = m_num_occs.size();
        //     for (unsigned i = 0; i < sz; i++) {
        //         proc(out, i); out << " -> " << m_max_degree[i] << " : " << m_num_occs[i] << "\n";
        //     }
        //     return out;
        // }

        // std::ostream& display(std::ostream & out, display_var_proc const & proc) {
        //     for (unsigned i = 0; i < num_vars; ++i) {
        //         proc(out, i); out << " -> " << m_max_degree[i] << " : " << m_sum_poly_degree[i] << "\n";
        //     }
        //     return out;
        // }
    };
    vos_var_info_collector::vos_var_info_collector(pmanager & _pm, atom_vector const & _atoms, unsigned _num_vars, unsigned _vos_type) {
        m_imp = alloc(imp, _pm, _atoms, _num_vars, _vos_type);
    }
    vos_var_info_collector::~vos_var_info_collector() {
        dealloc(m_imp);
    }
    void vos_var_info_collector::collect(clause_vector const & cs) {
        m_imp->collect(cs);
    }
    void vos_var_info_collector::operator()(var_vector &perm) {
        m_imp->operator()(perm);
    }
}
