#include "nlsat/nlsat_simple_checker.h"

namespace nlsat {
    struct simple_checker::imp {
        // solver              &sol;
        pmanager            &pm;
        anum_manager        &am;
        const clause_vector &clauses;
        literal_vector      &learned_unit;
        const atom_vector   &atoms;
        const unsigned      arith_var_num;
        // unsigned            all_var_num;
        enum sign_kind { EQ = 0, LT, GT, NONE, LE, GE, NEQ};
        void display(std::ostream & out, const sign_kind &sk) {
            if (sk == EQ)
                out << "==";
            else if (sk == LT)
                out << "<";
            else if (sk == GT)
                out << ">";
            else if (sk == NONE)
                out << "<=>";
            else if (sk == LE)
                out << "<=";
            else if (sk == GE)
                out << ">=";
            else if (sk == NEQ)
                out << "!=";
            else
                UNREACHABLE();
        }
        struct Endpoint {
            anum_manager    &m_am;
            unsigned        m_open:1;
            unsigned        m_inf:1;
            unsigned        m_is_lower:1;
            scoped_anum     m_val;
            Endpoint(anum_manager &_am) : 
                m_am(_am),
                m_open(1),
                m_inf(1),
                m_is_lower(1),
                m_val(_am) {
            }
            Endpoint(anum_manager &_am, unsigned _open, unsigned _inf, unsigned _islower) : 
                m_am(_am),
                m_open(_open),
                m_inf(_inf),
                m_is_lower(_islower),
                m_val(_am) {
            }
            Endpoint(anum_manager &_am, unsigned _open, unsigned _inf, unsigned _islower, const scoped_anum &_val) : 
                m_am(_am),
                m_open(_open),
                m_inf(_inf),
                m_is_lower(_islower),
                m_val(_am) {
                m_am.set(m_val, _val);
            }
            bool operator== (const Endpoint &rhs) const {
                if (m_inf && rhs.m_inf && m_is_lower == rhs.m_is_lower)
                    return true;
                if (!m_inf && !rhs.m_inf && m_open == rhs.m_open && m_val == rhs.m_val) {
                    if (!m_open)
                        return true;
                    if (m_is_lower == rhs.m_is_lower)
                        return true;
                }
                return false;
            }
            bool operator< (const Endpoint &rhs) const {
                if (m_inf) {
                    if (m_is_lower) {
                        if (rhs.m_inf && rhs.m_is_lower)
                            return false;
                        else
                            return true;
                    }
                    else {
                        return false;
                    }
                }
                else {
                    if (rhs.m_inf) {
                        if (rhs.m_is_lower)
                            return false;
                        else
                            return true;
                    }
                    else {
                        if (m_val == rhs.m_val) {
                            if (!m_open && !rhs.m_open) { // {[, [}
                                // {[, [} {[, ]} {], [} {], ]}
                                return false;
                            }
                            else if (!m_open) { // {[, (}
                                // [ < (, [ > ), ] < (, ] > )
                                if (rhs.m_is_lower)
                                    return true;
                                else
                                    return false;
                            }
                            else if (!rhs.m_open) { // {(, [}
                                if (m_is_lower) // x + EPS
                                    return false;
                                else // x - EPS
                                    return true;
                            }
                            else { // {(, (}
                                // ( == (, ( > ), ) < (, ) == )
                                if (!m_is_lower && rhs.m_is_lower)
                                    return true;
                                else
                                    return false;
                            }
                        }
                        else {
                            return m_val < rhs.m_val;
                        }
                    }
                }
            }
            void copy(const Endpoint &ep) {
                m_inf = ep.m_inf;
                m_open = ep.m_open;
                m_is_lower = ep.m_is_lower;
                if (!m_inf)
                    m_am.set(m_val, ep.m_val);
            }
            void set_num(const scoped_anum &num, unsigned is_lower) {
                m_open = 0;
                m_inf = 0;
                m_is_lower = is_lower;
                m_am.set(m_val, num);
            }
            void set_num(int num, unsigned is_lower) {
                m_open = 0;
                m_inf = 0;
                m_is_lower = is_lower;
                m_am.set(m_val, num);
            }
            bool is_neg() const {
                if (m_inf) {
                    if (m_is_lower)
                        return true;
                    else
                        return false;
                }
                else {
                    if (m_am.is_zero(m_val)) {
                        if (m_open) {
                            if (m_is_lower)
                                return false;
                            else
                                return true;
                        }
                        else {
                            return false;
                        }
                    }
                    else {
                        return m_am.is_neg(m_val);
                    }
                }
            }
            bool is_zero(unsigned is_open = 0) const {
                return !m_inf && m_open == is_open && m_am.is_zero(m_val);
            }
        };
        struct Domain_Interval {
            anum_manager    &m_am;
            Endpoint        m_lower;
            Endpoint        m_upper;
            Domain_Interval(anum_manager &_am) :
                m_am(_am),
                m_lower(_am, 1, 1, 1),
                m_upper(_am, 1, 1, 0) {
                // (-oo, +oo)
            }
            Domain_Interval(anum_manager &_am, 
                            unsigned _lower_open, unsigned _lower_inf,
                            unsigned _upper_open, unsigned _upper_inf) :
                m_am(_am),
                m_lower(_am, _lower_open, _lower_inf, 1),
                m_upper(_am, _upper_open, _upper_inf, 0) {
            }
            void copy(const Domain_Interval &di) {
                m_lower.copy(di.m_lower);
                m_upper.copy(di.m_upper);
            }
            void set_num(const scoped_anum &num) {
                m_lower.set_num(num, 1);
                m_upper.set_num(num, 0);
            }
            void set_num(int num) {
                m_lower.set_num(num, 1);
                m_upper.set_num(num, 0);
            }
        };

        void display(std::ostream & out, anum_manager & am, Domain_Interval const & curr) {
            if (curr.m_lower.m_inf) {
                out << "(-oo, ";
            }
            else {
                if (curr.m_lower.m_open)
                    out << "(";
                else
                    out << "[";
                am.display_decimal(out, curr.m_lower.m_val);
                out << ", ";
            }
            if (curr.m_upper.m_inf) {
                out << "oo)";
            }
            else {
                am.display_decimal(out, curr.m_upper.m_val);
                if (curr.m_upper.m_open)
                    out << ")";
                else
                    out << "]";
            }
        }

        struct Var_Domain {
            Domain_Interval ori_val; // original, ext sign
            Domain_Interval mag_val; // magnitude
            Var_Domain(anum_manager &am) :
                ori_val(am),
                mag_val(am) {
                mag_val.m_lower.set_num(0, 1);
            }
            void copy(const Var_Domain &vd) {
                ori_val.copy(vd.ori_val);
                mag_val.copy(vd.mag_val);
            }
        };
        vector<Var_Domain> vars_domain;
        struct Clause_Visit_Tag {
            bool visited;
            bool_vector literal_visited;
            Clause_Visit_Tag() : visited(false) {}
        };
        vector<Clause_Visit_Tag> clauses_visited;
        bool improved;
        enum special_ineq_kind {UNK = 0, AXBC, AXBSC, NK}; // None Kind
        vector<vector<special_ineq_kind>> literal_special_kind;
        imp(pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, literal_vector &_learned_unit, const atom_vector &_atoms, const unsigned &_arith_var_num) : 
            // sol(_sol),
            pm(_pm),
            am(_am),
            clauses(_clauses),
            learned_unit(_learned_unit),
            atoms(_atoms),
            arith_var_num(_arith_var_num) {
            // all_var_num = atoms.size();
            for (unsigned i = 0; i < arith_var_num; ++i) {
                vars_domain.push_back(Var_Domain(am));
            }
            clauses_visited.resize(clauses.size());
            literal_special_kind.resize(clauses.size());
        }
        sign_kind to_sign_kind(atom::kind kd) {
            if (kd == atom::EQ)
                return EQ;
            if (kd == atom::LT)
                return LT;
            if (kd == atom::GT)
                return GT;
            UNREACHABLE();
            return EQ;
        }
        bool update_interval_intersection(Domain_Interval &ia, const Domain_Interval &ib) {
            TRACE("simple_checker",
                tout << "ia: "; 
                display(tout, am, ia);
                tout << "\nib: ";
                display(tout, am, ib);
                tout << "\n";
                tout << "ia.lower < ib.lower: " << (ia.m_lower < ib.m_lower) << '\n';
                tout << "ia.m_upper < ib.m_upper: " << (ia.m_upper < ib.m_upper) << '\n';
            );
            if (ia.m_lower < ib.m_lower) {
                ia.m_lower.copy(ib.m_lower);
                improved = true;
            }
                
            if (ib.m_upper < ia.m_upper) {
                ia.m_upper.copy(ib.m_upper);
                improved = true;
            }
            if (ia.m_upper < ia.m_lower)
                return false;
            
            
            
            TRACE("simple_checker",
                tout << "after update: "; 
                display(tout, am, ia);
                tout << "\n";
            );
            return true;
        }

        bool update_var_ori_domain_interval(Var_Domain &vd, const Domain_Interval &di) {
            return update_interval_intersection(vd.ori_val, di);
        }
        bool update_var_mag_domain_interval_by_ori(Var_Domain &vd, const Domain_Interval &di) {
            TRACE("simple_checker",
                tout << "vd mag val: "; 
                display(tout, am, vd.mag_val);
                tout << "\n";
                tout << "di: "; 
                display(tout, am, di);
                tout << "\n";
            );
            Domain_Interval mag_di(am, 0, 0, 1, 1);
       
            if (di.m_lower.m_inf) {
                mag_di.m_upper.m_inf = 1;
                mag_di.m_upper.m_open = 1;
                if (am.is_neg(di.m_upper.m_val)) {
                    // am.neg(di.m_upper);
                    am.set(mag_di.m_lower.m_val, di.m_upper.m_val*-1);
                    mag_di.m_lower.m_open = di.m_upper.m_open;
                }
                else if (am.is_zero(di.m_upper.m_val)) {
                    mag_di.m_lower.m_open = di.m_upper.m_open;
                }
                else {
                    return true;
                }
            }
            else if (di.m_upper.m_inf) {
                mag_di.m_upper.m_inf = 1;
                mag_di.m_upper.m_open = 1;
                if (am.is_neg(di.m_lower.m_val)) {
                    return true;
                }
                else if (am.is_zero(di.m_lower.m_val)) {
                    mag_di.m_lower.m_open = di.m_lower.m_open;
                }
                else {
                    am.set(mag_di.m_lower.m_val, di.m_lower.m_val);
                    mag_di.m_lower.m_open = di.m_lower.m_open;
                }
            }
            else {
                mag_di.m_lower.m_inf = 0;
                mag_di.m_upper.m_inf = 0;
                if (!am.is_neg(di.m_lower.m_val)) {
                    mag_di.m_lower.m_open = di.m_lower.m_open;
                    mag_di.m_upper.m_open = di.m_upper.m_open;
                    am.set(mag_di.m_lower.m_val, di.m_lower.m_val);
                    am.set(mag_di.m_upper.m_val, di.m_upper.m_val);
                }
                else if (!am.is_pos(di.m_upper.m_val)) {
                    mag_di.m_lower.m_open = di.m_upper.m_open;
                    mag_di.m_upper.m_open = di.m_lower.m_open;

                    am.set(mag_di.m_lower.m_val, di.m_upper.m_val*-1);
                    am.set(mag_di.m_upper.m_val, di.m_lower.m_val*-1);
                }
                else {
                    scoped_anum nl(am);
                    am.set(nl, di.m_lower.m_val);
                    am.neg(nl);
                    am.set(mag_di.m_lower.m_val, 0);
                    mag_di.m_lower.m_open = 0;
                    if (nl < di.m_upper.m_val) {
                        mag_di.m_upper.m_open = di.m_upper.m_open;
                        am.set(mag_di.m_upper.m_val, di.m_upper.m_val);
                    }
                    else if (nl == di.m_upper.m_val) {
                        mag_di.m_upper.m_open = (di.m_lower.m_open | di.m_upper.m_open);
                        am.set(mag_di.m_upper.m_val, di.m_upper.m_val);
                    }
                    else {
                        mag_di.m_upper.m_open = di.m_lower.m_open;
                        am.set(mag_di.m_upper.m_val, nl);
                    }
                }
            }
            TRACE("simple_checker",
                tout << "mag di: "; 
                display(tout, am, mag_di);
                tout << "\n";
            );
            return update_interval_intersection(vd.mag_val, mag_di);
        }
        void calc_formula(scoped_anum &num, const scoped_anum &a, unsigned b, const scoped_anum &c) {
            scoped_anum frac(am);
            am.div(c, a, frac);
            am.neg(frac);
            if (b > 1)
                am.root(frac, b, num);
            else
                am.set(num, frac);
        }
        bool process_odd_degree_formula(Var_Domain &vd, sign_kind nsk, const scoped_anum &a, unsigned b, const scoped_anum &c) {
            Domain_Interval now_di(am);
            scoped_anum num(am);
            calc_formula(num, a, b, c);
            TRACE("simple_checker",
                tout << "nsk: "; 
                display(tout, nsk);
                tout << '\n'; 
                tout << "num: " << num << '\n'; 
            );
            if (nsk == EQ) {
                now_di.set_num(num);
                // am.set(now_di.m_lower.m_val, num);
                // am.set(now_di.m_upper.m_val, num);
                // now_di.m_lower.m_inf = 0;
                // now_di.m_upper.m_inf = 0;
                // now_di.m_lower.m_open = 0;
                // now_di.m_upper.m_open = 0;
            }
            else if (nsk == LT) {
                am.set(now_di.m_upper.m_val, num);
                now_di.m_upper.m_inf = 0;
                now_di.m_upper.m_open = 1;
            }
            else if (nsk == GT) {
                am.set(now_di.m_lower.m_val, num);
                now_di.m_lower.m_inf = 0;
                now_di.m_lower.m_open = 1;
            }
            else if (nsk == LE) {
                am.set(now_di.m_upper.m_val, num);
                now_di.m_upper.m_inf = 0;
                now_di.m_upper.m_open = 0;
            }
            else if (nsk == GE) {
                am.set(now_di.m_lower.m_val, num);
                now_di.m_lower.m_inf = 0;
                now_di.m_lower.m_open = 0;
            }
            else {
                UNREACHABLE();
            }
            TRACE("simple_checker",
                tout << "now_di: "; 
                display(tout, am, now_di);
                tout << "\n";
            );
            if (!update_var_ori_domain_interval(vd, now_di))
                return false;
            if (!update_var_mag_domain_interval_by_ori(vd, vd.ori_val))
                return false;
            return true;
        }

       bool process_even_degree_formula(Var_Domain &vd, sign_kind nsk, const scoped_anum &a, unsigned b, const scoped_anum &c) {
            scoped_anum num(am), frac(am);
            am.div(c, a, frac);
            am.neg(frac);

            if (frac < 0) {
                if (nsk == EQ || nsk == LT || nsk == LE) {
                    return false;
                }
                else if (nsk == GT || nsk == GE) {
                    return true;
                }
                else {
                    UNREACHABLE();
                }
            }
            else if (frac == 0) {
                if (nsk == EQ || nsk == LE) {
                    Domain_Interval di(am);
                    di.set_num(0);
                    if (!update_interval_intersection(vd.ori_val, di))
                        return false;
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                }
                else if (nsk == LT) {
                    return false;
                }
                else if (nsk == GT) {
                    Domain_Interval di(am);
                    di.m_lower.set_num(0, 1);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                }
                else if (nsk == GE) {
                    return true;
                }
                else {
                    UNREACHABLE();
                }
            }
            else {
                scoped_anum num(am);
                am.root(frac, b, num);
                if (nsk == EQ) {
                    Domain_Interval di(am);
                    di.set_num(num);
                    // di.m_lower_open = 0;
                    // di.m_upper_open = 0;
                    // di.m_lower_inf = 0;
                    // di.m_upper_inf = 0;
                    // am.set(di.m_lower, num);
                    // am.set(di.m_upper, num);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                }
                else if (nsk == LT) {
                    Domain_Interval di(am, 0, 0, 1, 0);
                    // [0, num)
                    am.set(di.m_lower.m_val, 0);
                    am.set(di.m_upper.m_val, num);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                    
                    // (-num, num)
                    di.m_lower.m_open = 1;
                    // am.set(di.m_upper, num);
                    am.neg(num);
                    am.set(di.m_lower.m_val, num);
                    if (!update_interval_intersection(vd.ori_val, di))
                        return false;
                }
                else if (nsk == GT) {
                    // (num, inf)
                    Domain_Interval di(am, 1, 0, 1, 1);
                    // di.m_lower_open = 1;
                    // di.m_upper_open = 1;
                    // di.m_lower_inf = 0;
                    // di.m_upper_inf = 1;
                    am.set(di.m_lower.m_val, num);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                }
                else if (nsk == LE) {
                    Domain_Interval di(am, 0, 0, 0, 0);
                    // [0, num]
                    // di.m_lower_open = 0;
                    // di.m_upper_open = 0;
                    // di.m_lower_inf = 0;
                    // di.m_upper_inf = 0;
                    am.set(di.m_lower.m_val, 0);
                    am.set(di.m_upper.m_val, num);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                    // [-num, num]
                    // am.set(di.m_upper, num);
                    am.neg(num);
                    am.set(di.m_lower.m_val, num);
                    if (!update_interval_intersection(vd.ori_val, di))
                        return false;
                }
                else if (nsk == GE) {
                    // [num, inf)
                    Domain_Interval di(am, 0, 0, 1, 1);
                    // di.m_lower_open = 0;
                    // di.m_upper_open = 1;
                    // di.m_lower_inf = 0;
                    // di.m_upper_inf = 1;
                    am.set(di.m_lower.m_val, num);
                    if (!update_interval_intersection(vd.mag_val, di))
                        return false;
                }
                else {
                    UNREACHABLE();
                }
            }
            return true;
        }

        bool update_var_domain(sign_kind nsk, const scoped_anum &a, var x, unsigned b, const scoped_anum &c) {
            Var_Domain &vd = vars_domain[x];
            if (am.is_neg(a)) {
                if (nsk == LT)
                    nsk = GT;
                else if (nsk == GT)
                    nsk = LT;
                else if (nsk == LE)
                    nsk = GE;
                else if (nsk == GE)
                    nsk = LE;
            }
            if (nsk == NEQ) {
                if (am.is_zero(c)) {
                    Domain_Interval di(am, 1, 0, 1, 1);
                    am.set(di.m_lower.m_val, 0);
                    return update_interval_intersection(vd.mag_val, di);
                }
                else {
                    return true;
                }
            }
            if ((b & 1) == 1)
                return process_odd_degree_formula(vd, nsk, a, b, c);
            else
                return process_even_degree_formula(vd, nsk, a, b, c);
        }

        bool check_is_axbc(const poly *p, scoped_anum &a, var &x, unsigned &b, scoped_anum& c) {
            // is a*(x^b) + c*1 form
            if (pm.size(p) == 1 && pm.is_var(pm.get_monomial(p, 0), x)) {
                am.set(a, 1);
                b = 1;
                am.set(c, 0);
                return true;
            }
            if (pm.size(p) != 2)
                return false;
            if (!pm.is_unit(pm.get_monomial(p, 1)))
                return false;
            monomial *m = pm.get_monomial(p, 0);
            if (pm.size(m) != 1)
                return false;
            x = pm.get_var(m, 0);
            b = pm.degree(m, 0);
           
            am.set(a, pm.coeff(p, 0));
            am.set(c, pm.coeff(p, 1));
            return true;
        }

        bool collect_domain_axbc_form(unsigned cid, unsigned lid) {
            // is_var_num, a*(x^b) + c form
            literal lit = (*clauses[cid])[lid];
            bool s = lit.sign();
            ineq_atom *ia = to_ineq_atom(atoms[lit.var()]);
            if (ia->size() > 1) {
                // clauses_visited[cid].visited = true;
                return true;
            }
            poly *p = ia->p(0);
            if (literal_special_kind[cid][lid] != UNK &&
                literal_special_kind[cid][lid] != AXBC) 
                return true;
            var x;
            scoped_anum a(am), c(am);
            unsigned b;

            if (!check_is_axbc(p, a, x, b, c)) {
                // vec_id.push_back(cid);
                return true;
            }
            clauses_visited[cid].visited = true;
            literal_special_kind[cid][lid] = AXBC;
            sign_kind nsk = to_sign_kind(ia->get_kind());
            if (s) {
                if (nsk == EQ)
                    nsk = NEQ;
                else if (nsk == LT)
                    nsk = GE;
                else if (nsk == GT)
                    nsk = LE;
            }
            TRACE("simple_checker", 
                tout << a << "x[" << x << "]^" << b << " + " << c << " ";
                display(tout, nsk);
                tout << " 0 \n";
            );
            if (!update_var_domain(nsk, a, x, b, c))
                return false;
            TRACE("simple_checker",
                tout << "original: "; 
                display(tout, am, vars_domain[x].ori_val);
                tout << "\nmagnitude: ";
                display(tout, am, vars_domain[x].mag_val);
                tout << "\n";
            );
            return true;
        }
        bool check_is_axbsc(const poly *p, vector<scoped_anum> &as, vector<var> &xs, vector<unsigned> &bs, scoped_anum& c, unsigned &cnt) {
            // [a*(x^b)] + ... + [a*(x^b)] + c form
            unsigned psz = pm.size(p);
            am.set(c, 0);
            for (unsigned i = 0; i < psz; ++i) {
                monomial *m = pm.get_monomial(p, i);
                if (pm.size(m) > 1)
                    return false;
            }
            cnt = 0;
            for (unsigned i = 0; i < psz; ++i) {
                monomial *m = pm.get_monomial(p, i);
                if (pm.size(m) == 0) {
                    am.set(c, pm.coeff(p, i));
                }
                else {
                    // as.push_back(scoped_anum(am));
                    am.set(as[cnt++], pm.coeff(p, i));
                    xs.push_back(pm.get_var(m, 0));
                    bs.push_back(pm.degree(m, 0));
                }
            }
            return true;
        }

        sign_kind get_axb_sign(const scoped_anum &a, var x, unsigned b) {
            Var_Domain &vd = vars_domain[x];
            if (vd.ori_val.m_lower.is_zero() &&
                vd.ori_val.m_upper.is_zero())
                return EQ;
            if ((b & 1) == 0) {
                if (am.is_pos(a)) { // a > 0
                    if (vd.mag_val.m_lower.is_zero(0)) 
                        return GE;
                    else 
                        return GT;
                }
                else {
                    if (vd.mag_val.m_lower.is_zero(0))
                        return LE;
                    else 
                        return LT;
                }
            } else {
                sign_kind ret = NONE;
                if (!vd.ori_val.m_lower.m_inf && !vd.ori_val.m_upper.m_inf) {
                    if (am.is_zero(vd.ori_val.m_lower.m_val)) {
                        if (vd.ori_val.m_lower.m_open)
                            ret = GT;
                        else
                            ret = GE;
                    }
                    else if (am.is_pos(vd.ori_val.m_lower.m_val)) {
                        ret = GT;
                    }
                    if (am.is_zero(vd.ori_val.m_upper.m_val)) {
                        if (vd.ori_val.m_upper.m_open)
                            ret = LT;
                        else
                            ret = LE;
                    }
                    else if (am.is_neg(vd.ori_val.m_upper.m_val)) {
                        ret = LT;
                    }                    
                }
                else if (!vd.ori_val.m_lower.m_inf) {
                    if (am.is_pos(vd.ori_val.m_lower.m_val)) {
                        ret = GT;
                    }
                    else if (am.is_zero(vd.ori_val.m_lower.m_val)) {
                        if (vd.ori_val.m_lower.m_open)
                            ret = GT;
                        else
                            ret = GE;
                    }
                }
                else if (!vd.ori_val.m_upper.m_inf) {
                    if (am.is_neg(vd.ori_val.m_upper.m_val)) {
                        ret = LT;
                    }
                    else if (am.is_zero(vd.ori_val.m_upper.m_val)) {
                        if (vd.ori_val.m_upper.m_open)
                            ret = LT;
                        else
                            ret = LE;
                    }
                }
                if (a < 0) {
                    if (ret == LT)
                        ret = GT;
                    else if (ret == LE)
                        ret = GE;
                    else if (ret == GT)
                        ret = LT;
                    else if (ret == GE)
                        ret = LE;
                }
                return ret;
            }
        }

        bool check_is_sign_ineq_consistent(sign_kind &nsk, vector<scoped_anum> &as, vector<var> &xs, vector<unsigned> &bs, scoped_anum& c, bool &is_conflict) {
            sign_kind sta = get_axb_sign(as[0], xs[0], bs[0]);
            if (sta == NONE)
                return false;
            unsigned sz = as.size();
            for (unsigned i = 1; i < sz; ++i) {
                sign_kind now = get_axb_sign(as[i], xs[i], bs[i]);
                TRACE("simple_checker",
                    tout << "sta: ";
                    display(tout, sta);
                    tout << "\n";
                    tout << "now: ";
                    display(tout, now);
                    tout << "\n";
                );
                if (now == NONE)
                    return false;
                if (sta == EQ) {
                    sta = now;
                }
                else if (sta == LT || sta == LE) {
                    if (now != LT && now != LE) 
                        return false;
                    if (sta != now)
                        sta = LT;
                }
                else {
                    if (now != GT && now != GE) 
                        return false;
                    if (sta != now)
                        sta = GT;
                }
                TRACE("simple_checker",
                    tout << "after merge\n";
                    tout << "sta: ";
                    display(tout, sta);
                    tout << "\n";
                );
            }
            TRACE("simple_checker",
                tout << "sta: ";
                display(tout, sta);
                tout << "\n";
                tout << "nsk: ";
                display(tout, nsk);
                tout << "\n";
                tout << "c: ";
                am.display(tout, c);
                tout << "\n";
            );
/*
if (am.is_neg(c)) { // ( == 0) + (c < 0) -> < 0

}
else if (am.is_zero(c)) { // ( == 0) + (c == 0) -> == 0

}
else { // ( == 0) + (c > 0) -> > 0

}
*/
            if (sta == EQ) {
                if (am.is_neg(c)) { // ( == 0) + (c < 0) -> < 0
                    if (nsk == EQ || nsk == GE || nsk == GT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else if (am.is_zero(c)) { // ( == 0) + (c == 0) -> == 0
                    if (nsk == GT || nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else { // ( == 0) + (c > 0) -> > 0
                    if (nsk == EQ || nsk == LE || nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
            }
            else if (sta == LT) {
                if (am.is_neg(c)) { // ( < 0) + (c < 0) -> < 0
                    if (nsk == EQ || nsk == GE || nsk == GT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else if (am.is_zero(c)) { // ( < 0) + (c == 0) -> < 0
                    if (nsk == EQ || nsk == GE || nsk == GT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else { // [(t0 <= 0 + .. + tn <= 0) + (c > 0) >/>= 0] -> t > -c
                    if (nsk == LE || nsk == LT)
                        return false;
                    if (sz > 1 && nsk == EQ)
                        nsk = GE;
                    return true;
                }
            }
            else if (sta == LE) {
                if (am.is_neg(c)) { // ( <= 0) + (c < 0) -> < 0
                    if (nsk == EQ || nsk == GE || nsk == GT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else if (am.is_zero(c)) { // ( <= 0) + (c == 0) -> <= 0
                    if (nsk == GT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else { // [(t0 <= 0 + .. + tn <= 0) + (c > 0) >/>= 0] -> t > -c
                    if (nsk == LE || nsk == LT)
                        return false;
                    if (sz > 1 && nsk == EQ)
                        nsk = GE;
                    return true;
                }
            }
            else if (sta == GT) {
                if (am.is_neg(c)) { // [(t0 > 0 + .. + tn > 0) + (c < 0) </<= 0] -> t < -c
                    if (nsk == GE || nsk == GT)
                        return false;
                    if (sz > 1 && nsk == EQ)
                        nsk = LE;
                    return true;
                }
                else if (am.is_zero(c)) { // ( > 0) + (c == 0) -> > 0
                    if (nsk == EQ || nsk == LE || nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else { // (t > 0) + (c > 0) -> > 0
                    if (nsk == EQ || nsk == LE || nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
            }
            else if (sta == GE) {
                if (am.is_neg(c)) { // [(t0 >= 0 + .. + tn >= 0) + (c < 0) </<= 0] -> t < -c
                    if (nsk == GE || nsk == GT)
                        return false;
                    if (sz > 1 && nsk == EQ)
                        nsk = LE;
                    return true;
                }
                else if (am.is_zero(c)) { // ( >= 0) + (c == 0) -> >= 0
                    if (nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
                else { // (t >= 0) + (c > 0) -> > 0
                    if (nsk == EQ || nsk == LE || nsk == LT) {
                        is_conflict = true;
                        return true;
                    }
                    else {
                        return false;
                    }
                }
            }
            return false;
        }
        bool collect_domain_sign_ineq_consistent_form(sign_kind nsk, vector<scoped_anum> &as, vector<var> &xs, vector<unsigned> &bs, scoped_anum& c) {
            for (unsigned i = 0, sz = as.size(); i < sz; ++i) {
                if (!update_var_domain(nsk, as[i], xs[i], bs[i], c))
                    return false;
            }
            return true;
        }
        bool process_axbsc_form(sign_kind nsk, unsigned cid, vector<scoped_anum> &as, vector<var> &xs, vector<unsigned> &bs, scoped_anum& c) {
            bool is_conflict(false);
            TRACE("simple_checker",
                for (unsigned i = 0, sz = as.size(); i < sz; ++i) {
                    if (i > 0)
                        tout << "+ ";
                    tout << as[i] << "x[" << xs[i] << "]^" << bs[i] << " ";
                }
                tout << "+ " << c << " ";
                display(tout, nsk);
                tout << " 0\n";
            );
            if (!check_is_sign_ineq_consistent(nsk, as, xs, bs, c, is_conflict))
                return true;
            TRACE("simple_checker",
                tout << "is conflict: " << is_conflict << "\n"
            );
            if (is_conflict)
                return false;
            clauses_visited[cid].visited = true;
            if (!collect_domain_sign_ineq_consistent_form(nsk, as, xs, bs, c))
                return false;
            return true;
        }
        bool collect_domain_axbsc_form(unsigned cid, unsigned lid) {
            // [a*(x^k)] + ... + [a*(x^b)] + k form
            literal lit = (*clauses[cid])[lid];
            bool s = lit.sign();
            ineq_atom *iat = to_ineq_atom(atoms[lit.var()]);
            if (iat->size() > 1)
                return true;
            if (literal_special_kind[cid][lid] != UNK &&
                literal_special_kind[cid][lid] != AXBSC)
                return true;
            
            poly *p = iat->p(0);
            vector<scoped_anum> as;
            for (unsigned i = 0, sz = pm.size(p); i < sz; ++i) {
                as.push_back(scoped_anum(am));
            }
            vector<var> xs;
            vector<unsigned> bs;
            scoped_anum c(am);
            unsigned cnt;
            if (!check_is_axbsc(p, as, xs, bs, c, cnt)) {
                literal_special_kind[cid][lid] = NK;
                return true;
            }
            literal_special_kind[cid][lid] = AXBSC;
            TRACE("simple_checker",
                tout << "as size: " << as.size() << '\n';
            );
            while (as.size() > cnt)
                as.pop_back();

            sign_kind nsk = to_sign_kind(iat->get_kind());
            if (s) {
                if (nsk == EQ)
                    return true;
                else if (nsk == LT)
                    nsk = GE;
                else if (nsk == GT)
                    nsk = LE;
            }
            TRACE("simple_checker",
                tout << "ineq atom: " << '\n';
                for (unsigned i = 0, sz = iat->size(); i < sz; ++i) {
                    pm.display(tout, iat->p(i));
                    tout << " is even: " << iat->is_even(i) << "\n";
                }
                display(tout, nsk);
                tout << " 0\n";
                tout << "\n";
                tout << "as size: " << as.size() << '\n';
                for (unsigned i = 0, sz = as.size(); i < sz; ++i) {
                    if (i > 0)
                        tout << "+ ";
                    tout << as[i] << "x[" << xs[i] << "]^" << bs[i] << " ";
                }
                tout << "+ " << c << " ";
                display(tout, nsk);
                tout << " 0\n";
            );
            if (!process_axbsc_form(nsk, cid, as, xs, bs, c))
                return false;
            return true;
        }
   
        bool collect_var_domain() {
            // vector<unsigned> vec_id;
            for (unsigned i = 0, sz = clauses.size(); i < sz; ++i) {
                if (clauses_visited[i].visited)
                    continue;
                if (clauses[i]->size() > 1)
                    continue;
                literal lit = (*clauses[i])[0];
                atom *tmp_atom = atoms[lit.var()];
                if (tmp_atom == nullptr) {
                    clauses_visited[i].visited = true;
                    continue;
                }
                if (!tmp_atom->is_ineq_atom()) {
                    clauses_visited[i].visited = true;
                    continue;
                }
                ineq_atom *tmp_ineq_atom = to_ineq_atom(tmp_atom);
                if (tmp_ineq_atom->size() > 1)
                    continue;
                if (!collect_domain_axbc_form(i, 0))
                    return false;
            }
            TRACE("simple_checker",
                for (unsigned i = 0; i < arith_var_num; ++i) {
                    tout << "====== arith[" << i << "] ======\n";
                    tout << "original value: ";
                    display(tout, am, vars_domain[i].ori_val);
                    tout << "\nmagitude value: ";
                    display(tout, am, vars_domain[i].mag_val);
                    tout << "\n";
                    tout << "====== arith[" << i << "] ======\n";
                }
            );
            for (unsigned i = 0, sz = clauses.size(); i < sz; ++i) {
                // unsigned id = vec_id[i];
                if (!collect_domain_axbsc_form(i, 0))
                    return false;
            }
            return true;
        }
        void endpoint_multiply(const Endpoint &a, const Endpoint &b, Endpoint &c) {
            if (a.is_zero() || b.is_zero()) {
                c.set_num(0, 0);
                return ;
            }
            bool a_neg = a.is_neg(), b_neg = b.is_neg();
            if (a.m_inf || b.m_inf) {
                c.m_inf = 1;
                c.m_open = 1;
                if (a_neg == b_neg)
                    c.m_is_lower = 0;
                else
                    c.m_is_lower = 1;
            }
            else {
                c.m_inf = 0;
                c.m_open = (a.m_open | b.m_open);
                am.set(c.m_val, a.m_val*b.m_val);
            }
        }
        void get_max_min_endpoint(const ptr_vector<Endpoint> &pev, Endpoint *&pmi, Endpoint *&pmx) {
            pmi = pmx = pev[0];
            for (unsigned i = 1, sz = pev.size(); i < sz; ++i) {
                if (*pmx < *pev[i])
                    pmx = pev[i];
                if (*pev[i] < *pmi)
                    pmi = pev[i];
            }
        }
        void merge_mul_domain(Domain_Interval &pre, const Domain_Interval &now) {
            TRACE("simple_checker",
                tout << "dom: ";
                display(tout, am, pre);
                tout << "\n";
                tout << "di: ";
                display(tout, am, now);
                tout << "\n";
            );
            Endpoint plnl(am), plnu(am), punl(am), punu(am);
            endpoint_multiply(pre.m_lower, now.m_lower, plnl);
            endpoint_multiply(pre.m_lower, now.m_upper, plnu);
            endpoint_multiply(pre.m_upper, now.m_lower, punl);
            endpoint_multiply(pre.m_upper, now.m_upper, punu);
            ptr_vector<Endpoint> pev;
            pev.push_back(&plnl);
            pev.push_back(&plnu);
            pev.push_back(&punl);
            pev.push_back(&punu);
            Endpoint *pmi, *pmx;
            get_max_min_endpoint(pev, pmi, pmx);
            pre.m_lower.copy(*pmi);
            pre.m_lower.m_is_lower = 1;
            pre.m_upper.copy(*pmx);
            pre.m_upper.m_is_lower = 0;
        }

        void get_monomial_domain(monomial *m, const scoped_anum &a, Domain_Interval &dom) {
            TRACE("simple_checker",
                tout << "monomial: ";
                pm.display(tout, m);
                tout << '\n';
                tout << "coefficient: " << a << "\n";
                tout << "# ";
                for (unsigned i = 0, sz = pm.size(m); i < sz; ++i) {
                    var v = pm.get_var(m, i);
                    tout << " (" << i << ", " << pm.degree_of(m, v) << ")";
                }
                tout << "\n";
            );
            
            // [a, a]
            dom.set_num(a);
            for (unsigned i = 0, sz = pm.size(m); i < sz; ++i) {
                var v = pm.get_var(m, i);
                unsigned deg = pm.degree_of(m, v);
                const Domain_Interval &di = ((deg & 1) == 0 ? vars_domain[v].mag_val : vars_domain[v].ori_val);
                TRACE("simple_checker",
                    tout << "dom: ";
                    display(tout, am, dom);
                    tout << "\n";
                    tout << "var: " << v;
                    tout << ", di: ";
                    display(tout, am, di);
                    tout << "\n";
                );
                for (unsigned j = 0; j < deg; ++j) {
                    merge_mul_domain(dom, di);
                }
                TRACE("simple_checker",
                    tout << "after merge mul: ";
                    display(tout, am, dom);
                    tout << "\n";
                );
                // mul 0
                // if (dom.m_lower_inf && dom.m_upper_inf)
                //     return ;
            }
        }
        void endpoint_add(Endpoint &a, const Endpoint &b) {
            a.m_inf = (a.m_inf | b.m_inf);
            if (a.m_inf == 0) {
                am.set(a.m_val, a.m_val + b.m_val);
                a.m_open = (a.m_open | b.m_open);
            }
        }
        
        void merge_add_domain(Domain_Interval &pre, const Domain_Interval &now) {
            endpoint_add(pre.m_lower, now.m_lower);
            endpoint_add(pre.m_upper, now.m_upper);
        }
        
        sign_kind get_poly_sign(const poly *p) {
            scoped_anum a(am);
            am.set(a, pm.coeff(p, 0));
            Domain_Interval pre(am);
            get_monomial_domain(pm.get_monomial(p, 0), a, pre);
            TRACE("simple_checker",
                tout << "poly: ";
                pm.display(tout, p);
                tout << "\n";
            );
            TRACE("simple_checker",
                tout << "pre: ";
                display(tout, am, pre);
                tout << "\n";
            );
            for (unsigned i = 1, sz = pm.size(p); i < sz; ++i) {
                am.set(a, pm.coeff(p, i));
                Domain_Interval now(am);
                get_monomial_domain(pm.get_monomial(p, i), a, now);
                TRACE("simple_checker",
                    tout << "pre: ";
                    display(tout, am, pre);
                    tout << "\n";
                    tout << "now: ";
                    display(tout, am, now);
                    tout << "\n";
                );
                if (now.m_lower.m_inf && now.m_upper.m_inf)
                    return NONE;
                merge_add_domain(pre, now);
                TRACE("simple_checker",
                    tout << "after merge: ";
                    display(tout, am, pre);
                    tout << "\n";
                );
                if (pre.m_lower.m_inf && pre.m_upper.m_inf)
                    return NONE;
            }
            if (pre.m_lower.m_inf) {
                if (am.is_neg(pre.m_upper.m_val)) {
                    // (-inf, -}
                    return LT;
                }
                else if (am.is_zero(pre.m_upper.m_val)) {
                    // (-inf, 0}
                    if (pre.m_upper.m_open)
                        return LT;
                    else
                        return LE;
                }
                else {
                    // (-inf, +}
                    return NONE;
                }
            }
            else if (pre.m_upper.m_inf) {
                if (am.is_neg(pre.m_lower.m_val)) {
                    // {-, +inf)
                    return NONE;
                }
                else if (am.is_zero(pre.m_lower.m_val)) {
                    // {0, +inf)
                    if (pre.m_lower.m_open)
                        return GT;
                    else
                        return GE;
                }
                else {
                    // {+, +inf)
                    return GT;
                }
            }
            else {
                // [0, 0]
                if (am.is_zero(pre.m_lower.m_val) && am.is_zero(pre.m_upper.m_val))
                    return EQ;
                else if (am.is_zero(pre.m_lower.m_val)) {
                    // {0, +}
                    if (pre.m_lower.m_open)
                        return GT;
                    else
                        return GE;
                }
                else if (am.is_zero(pre.m_upper.m_val)) {
                    // {-, 0}
                    if (pre.m_upper.m_open)
                        return LT;
                    else
                        return LE;
                }
                else {
                    if (am.is_pos(pre.m_lower.m_val))
                        return GT;
                    else if (am.is_neg(pre.m_upper.m_val))
                        return LT;
                    else
                        return NONE;
                }
            }
            return NONE;
        }

        sign_kind get_poly_sign_degree(const poly *p, bool is_even) {
            sign_kind ret = get_poly_sign(p);
            if (is_even) {
                if (ret == GE || ret == LE || ret == NONE)
                    ret = GE;
                else if (ret != EQ)
                    ret = GT;
            }
            TRACE("simple_checker",
                tout << "ret sign: ";
                display(tout, ret);
                tout << "\n";
                tout << "is even: " << is_even << "\n";
            );
            return ret;
        }
        void merge_mul_sign(sign_kind &pre, sign_kind now) {
            if (pre == EQ)
                return ;
            if (now == EQ) {
                pre = EQ;
                return ;
            }
            if (pre == NONE)
                return ;
            
            if (now == NONE) {
                pre = NONE;
            }
            // else if (now == EQ) {
            //     pre = EQ;
            // }
            else if (now == LT) {
                if (pre == GE)
                    pre = LE;
                else if (pre == GT)
                    pre = LT;
                else if (pre == LE)
                    pre = GE;
                else if (pre == LT)
                    pre = GT;
            }
            else if (now == GT) {
                // if (pre == LE)
                //     pre = LE;
                // else if (pre == LT)
                //     pre = LT;
                // else if (pre == GT)
                //     pre = GT;
                // else if (pre == GE)
                //     pre = GE;
            }
            else if (now == LE) {
                if (pre == GE)
                    pre = LE;
                else if (pre == GT)
                    pre = LE;
                else if (pre == LE)
                    pre = GE;
                else if (pre == LT)
                    pre = GE;
            }
            else if (now == GE) {
                // if (pre == LE)
                //     pre = LE;
                if (pre == LT)
                    pre = LE;
                else if (pre == GT)
                    pre = GE;
                // else if (pre == GE)
                //     pre = GE;
            }
        }
        bool check_ineq_atom_satisfiable(const ineq_atom *iat, bool s) {
            TRACE("simple_checker",
                tout << "s: " << s << "\n";
                tout << "kd: " << iat->get_kind() << "\n";
            );
            sign_kind nsk = to_sign_kind(iat->get_kind());
            if (s) {
                if (nsk == EQ)
                    return true;
                else if (nsk == GT)
                    nsk = LE;
                else
                    nsk = GE;
            }
            TRACE("simple_checker",
                tout << "ineq atom: " << '\n';
                for (unsigned i = 0, sz = iat->size(); i < sz; ++i) {
                    pm.display(tout, iat->p(i));
                    tout << " is even: " << iat->is_even(i) << "\n";
                }
                display(tout, nsk);
                tout << " 0\n";
            );
            // return true;
            
            sign_kind pre = get_poly_sign_degree(iat->p(0), iat->is_even(0));
        
            for (unsigned i = 1, sz = iat->size(); i < sz; ++i) {
                sign_kind now = get_poly_sign_degree(iat->p(i), iat->is_even(i));
                merge_mul_sign(pre, now);
                if (pre == NONE)
                    return true;
                if ((nsk == EQ || nsk == GE || nsk == LE) &&
                    (pre == EQ || pre == GE || pre == LE))
                    return true;
            }
            TRACE("simple_checker",
                tout << "pre: ";
                display(tout, pre);
                tout << ", nsk: ";
                display(tout, nsk);
                tout << "\n";
            );
            if (pre == NONE)
                return true;
            if (pre == EQ && (nsk == LT || nsk == GT))
                return false;
            if (pre == GE && nsk == LT)
                return false;
            if (pre == GT && (nsk == LT || nsk == LE || nsk == EQ))
                return false;
            if (pre == LE && nsk == GT)
                return false;
            if (pre == LT && (nsk == GT || nsk == GE || nsk == EQ))
                return false;
            return true;
        }
        bool check_literal_satisfiable(unsigned cid, unsigned lit_id) {
            literal lit = (*clauses[cid])[lit_id];
            const var &v = lit.var();
            atom *at = atoms[v];
            if (at == nullptr) {
                clauses_visited[cid].visited = true;
                return true;
            }
            if (!at->is_ineq_atom()) {
                clauses_visited[cid].visited = true;
                return true;
            }
            // TRACE("sign",
            //     tout << "literal: " << lit << '\n';
            // );
            bool s = lit.sign();
            return check_ineq_atom_satisfiable(to_ineq_atom(at), s);
        }
        bool check_clause_satisfiable(unsigned cid) {
            const clause *cla = clauses[cid];
            TRACE("simple_checker",
                tout << "clause size: " << cla->size() << '\n';
            );
            unsigned sz = cla->size();
            if (clauses_visited[cid].literal_visited.size() == 0) {
                clauses_visited[cid].literal_visited.resize(sz, false);
                literal_special_kind[cid].resize(sz, UNK);
            }
            unsigned sat_lit_id = sz;
            for (unsigned i = 0; i < sz; ++i) {
                if (clauses_visited[cid].literal_visited[i])
                    continue;
                if (check_literal_satisfiable(cid, i)) {
                    if (clauses_visited[cid].visited)
                        return true;
                    if (sat_lit_id == sz) 
                        sat_lit_id = i;
                    else
                        return true;
                } else {
                    clauses_visited[cid].literal_visited[i] = true;
                    literal lit = (*clauses[cid])[i];
                    lit.neg();
                    learned_unit.push_back(lit);
                    TRACE("simple_checker_learned", 
                        tout << "making new clauses!\n";
                        tout << "sign: " << lit.sign() << '\n';
                        if (atoms[lit.var()] != nullptr && atoms[lit.var()]->is_ineq_atom()) {
                            ineq_atom *iat = to_ineq_atom(atoms[lit.var()]);
                            tout << "ineq atom: " << '\n';
                            sign_kind nsk = to_sign_kind(iat->get_kind());
                            for (unsigned i = 0, sz = iat->size(); i < sz; ++i) {
                                pm.display(tout, iat->p(i));
                                tout << " is even: " << iat->is_even(i) << "\n";
                            }
                            display(tout, nsk);
                            tout << " 0\n";
                        }
                    );
                }
            }
            if (sat_lit_id != sz) {
                if (!collect_domain_axbc_form(cid, sat_lit_id))
                    return false;
                if (!collect_domain_axbsc_form(cid, sat_lit_id))
                    return false;
                return true;
            }
            return false;
        }
        bool check() {
            for (unsigned i = 0, sz = clauses.size(); i < sz; ++i) {
                if (clauses_visited[i].visited)
                    continue;
                if (!check_clause_satisfiable(i)) {
                    return false;
                }
            }
            return true;
        }
        bool operator()() {
            
            improved = true;
            while (improved) {
                improved = false;
                if (!check())
                    return false;
                TRACE("simple_checker",
                for (unsigned i = 0; i < arith_var_num; ++i) {
                    tout << "====== arith[" << i << "] ======\n";
                    tout << "original value: ";
                    display(tout, am, vars_domain[i].ori_val);
                    tout << "\nmagitude value: ";
                    display(tout, am, vars_domain[i].mag_val);
                    tout << "\n";
                    tout << "====== arith[" << i << "] ======\n";
                }
            );
            }
            return true;
        }
    };
    simple_checker::simple_checker(pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, literal_vector &_learned_unit, const atom_vector &_atoms, const unsigned &_arith_var_num) {
        m_imp = alloc(imp, _pm, _am, _clauses, _learned_unit, _atoms, _arith_var_num);
    }
    simple_checker::~simple_checker() {
        dealloc(m_imp);
    }
    bool simple_checker::operator()() {
        return m_imp->operator()();
    }
}
