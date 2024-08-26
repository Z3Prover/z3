#include "nlsat/nlsat_simplify.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_scoped_literal_vector.h"
#include "util/dependency.h"
#include "util/map.h"

namespace nlsat {

    struct simplify::imp {

        solver& s;
        atom_vector&  m_atoms;
        clause_vector& m_clauses, m_learned;
        pmanager& m_pm;
        literal_vector m_lemma;
        vector<ptr_vector<clause>> m_var_occurs;


        imp(solver& s, atom_vector& atoms, clause_vector& clauses, clause_vector& learned, pmanager& pm):
            s(s), 
            m_atoms(atoms), 
            m_clauses(clauses), 
            m_learned(learned),
            m_pm(pm) {}

        void operator()() {

            // for now just remove all learned clauses.
            // TODO; check if main clauses are subsumed by learned, 
            // then promote learned to main.
            for (auto c : m_learned)
                s.del_clause(c);
            m_learned.reset();
            
            IF_VERBOSE(3, s.display(verbose_stream() << "before\n"));
            unsigned sz = m_clauses.size();
            while (true) {

                subsumption_simplify();

                while (elim_uncnstr())
                    ;

                simplify_literals();

                while (fm())
                    ;

                if (m_clauses.size() >= sz)
                    break;

                split_factors();

                sz = m_clauses.size();
            }

            IF_VERBOSE(3, s.display(verbose_stream() << "after\n"));
        }

        //
        // Apply gcd simplification to literals
        // 
        void simplify_literals() {
            u_map<literal> b2l;
            scoped_literal_vector lits(s);
            polynomial_ref p(m_pm);
            ptr_buffer<poly> ps;
            buffer<bool> is_even;
            unsigned num_atoms = m_atoms.size();
            for (unsigned j = 0; j < num_atoms; ++j) {
                atom* a1 = m_atoms[j];
                if (a1 && a1->is_ineq_atom()) {
                    ineq_atom const& a = *to_ineq_atom(a1);
                    ps.reset();
                    is_even.reset();
                    for (unsigned i = 0; i < a.size(); ++i) {                        
                        p = a.p(i);
                        ps.push_back(p);
                        is_even.push_back(a.is_even(i));
                    }
                    literal l = s.mk_ineq_literal(a.get_kind(), ps.size(), ps.data(), is_even.data(), true);
                    if (l == null_literal)
                        continue;
                    lits.push_back(l);
                    if (a.m_bool_var != l.var()) {
                        IF_VERBOSE(3, s.display(verbose_stream() << "simplify ", a) << " -> ";
                        s.display(verbose_stream(), l) << "\n");
                        b2l.insert(a.m_bool_var, l);
                    }
                }
            }
            update_clauses(b2l);
        }

        void update_clauses(u_map<literal> const& b2l) {
            literal_vector lits;
            unsigned n = m_clauses.size();

            for (unsigned i = 0; i < n; ++i) {
                clause* c = m_clauses[i];
                lits.reset();
                bool changed = false;
                bool is_tautology = false;
                for (literal l : *c) {
                    literal lit = null_literal;
                    if (b2l.find(l.var(), lit)) {
                        lit = l.sign() ? ~lit : lit;
                        if (lit == true_literal) 
                            is_tautology = true;                        
                        else if (lit != false_literal) 
                            lits.push_back(lit);                        
                        changed = true;
                    }
                    else 
                        lits.push_back(l);                    
                }
                if (changed) {
                    c->set_removed();
                    if (is_tautology) 
                        continue;                    
                    s.mk_clause(lits.size(), lits.data(), c->is_learned(), c->assumptions());                    
                }
            }
            cleanup_removed();
        }

        //
        // Replace unit literals p*q > 0 by clauses.
        // 
        void split_factors() {
            auto sz = m_clauses.size();
            for (unsigned i = 0; i < sz; ++i) {
                auto& c = *m_clauses[i];
                if (c.size() != 1)
                    continue;
                auto lit = c[0];
                auto a1 = m_atoms[lit.var()];
                if (!a1)
                    continue;
                auto& a = *to_ineq_atom(a1);
                if (a.size() != 2)
                    continue;
                if (a.is_root_atom())
                    continue;

                auto* p = a.p(0);
                auto* q = a.p(1);
                auto is_evenp = a.is_even(0);
                auto is_evenq = a.is_even(1);

                auto asum = c.assumptions();
                literal lits[2];
                clause* c1 = nullptr, * c2 = nullptr;

                c.set_removed();
                s.inc_simplify();
                switch (a.get_kind()) {
                case atom::EQ: {
                    auto l1 = s.mk_ineq_literal(atom::EQ, 1, &p, &is_evenp, false);
                    auto l2 = s.mk_ineq_literal(atom::EQ, 1, &q, &is_evenq, false);
                    if (lit.sign()) {
                        lits[0] = ~l1;
                        c1 = s.mk_clause(1, lits, false, asum);
                        lits[0] = ~l2;
                        c2 = s.mk_clause(1, lits, false, asum);
                    }
                    else {
                        lits[0] = l1;
                        lits[1] = l2;
                        c1 = s.mk_clause(2, lits, false, asum);
                    }
                    break;
                }
                case atom::LT: {
                    auto pgt = s.mk_ineq_literal(atom::GT, 1, &p, &is_evenp, false);
                    auto plt = s.mk_ineq_literal(atom::LT, 1, &p, &is_evenp, false);
                    auto qgt = s.mk_ineq_literal(atom::GT, 1, &q, &is_evenq, false);
                    auto qlt = s.mk_ineq_literal(atom::LT, 1, &q, &is_evenq, false);
                    if (lit.sign()) {
                        // p*q >= 0 <=> (p < 0 => q <= 0) & (q < 0 => p <= 0)
                        // (!(p < 0) or !(q > 0)) & (!(q < 0) or !(p > 0))

                        lits[0] = ~plt;
                        lits[1] = ~qgt;
                        c1 = s.mk_clause(2, lits, false, asum);
                        lits[0] = ~qlt;
                        lits[1] = ~pgt;
                        c2 = s.mk_clause(2, lits, false, asum);
                    }
                    else {
                        // p*q < 0
                        // (p > 0 & q < 0) or (q > 0 & p < 0)
                        // (p > 0 or q > 0) and (p < 0 or q < 0)

                        lits[0] = pgt;
                        lits[1] = qgt;
                        c1 = s.mk_clause(2, lits, false, asum);
                        lits[0] = plt;
                        lits[1] = qlt;
                        c2 = s.mk_clause(2, lits, false, asum);
                    }
                    break;
                }
                case atom::GT: {
                    auto pgt = s.mk_ineq_literal(atom::GT, 1, &p, &is_evenp, false);
                    auto plt = s.mk_ineq_literal(atom::LT, 1, &p, &is_evenp, false);
                    auto qgt = s.mk_ineq_literal(atom::GT, 1, &q, &is_evenq, false);
                    auto qlt = s.mk_ineq_literal(atom::LT, 1, &q, &is_evenq, false);
                    if (lit.sign()) {
                        // p*q <= 0
                        // (p > 0 => q <= 0) & (p < 0 => q >= 0)
                        // (!(p > 0) or !(q > 0)) & (!(p < 0) or !(q < 0))

                        lits[0] = ~pgt;
                        lits[1] = ~qgt;
                        c1 = s.mk_clause(2, lits, false, asum);
                        lits[0] = ~qlt;
                        lits[1] = ~plt;
                        c2 = s.mk_clause(2, lits, false, asum);
                    }
                    else {
                        // p*q > 0
                        // (p > 0 or q < 0) & (p < 0 or q > 0)
                        lits[0] = plt;
                        lits[1] = qgt;
                        c1 = s.mk_clause(2, lits, false, asum);
                        lits[0] = qlt;
                        lits[1] = pgt;
                        c2 = s.mk_clause(2, lits, false, asum);
                    }
                    break;
                }
                default:
                    SASSERT(a.is_root_atom());
                    UNREACHABLE();
                    break;
                }
                IF_VERBOSE(3, 
                s.display(verbose_stream(), c) << " ->\n";
                if (c1) s.display(verbose_stream(), *c1) << "\n";
                if (c2) s.display(verbose_stream(), *c2) << "\n");
            }
            cleanup_removed();
        }

        bool elim_uncnstr() {
            // compute variable occurrences
            if (any_of(m_clauses, [&](clause* c) { return s.has_root_atom(*c); }))
                return false;
            compute_occurs();
            // for each variable occurrence, figure out if it is unconstrained.
            bool has_removed = false;
            for (unsigned v = m_var_occurs.size(); v-- > 0; ) {
                auto& clauses = m_var_occurs[v];
                if (clauses.size() != 1)
                    continue;
                auto& c = *clauses[0];
                if (c.is_removed())
                    continue;
                if (!is_unconstrained(v, c))
                    continue;
                s.inc_simplify();
                c.set_removed();
                has_removed = true;
            }
            cleanup_removed();

            return has_removed;
        }

        bool is_unconstrained(var x, clause& c) {
            poly* p;
            polynomial_ref A(m_pm), B(m_pm);
            for (auto lit : c) {
                bool_var b = lit.var();
                if (!m_atoms[b])
                    continue;
                auto& a = *to_ineq_atom(m_atoms[b]);
                if (!is_single_poly(a, p))
                    continue;

                if (1 != m_pm.degree(p, x))
                    continue;

                A = m_pm.coeff(p, x, 1, B);

                if (a.is_eq() && !lit.sign()) {
                    // A*x + B = 0
                    if (s.is_int(x) && is_unit(A)) {
                        s.add_bound(bound_constraint(x, A, B, false, nullptr));
                        return true;
                    }

                    if (!s.is_int(x) && m_pm.is_const(A)) {
                        s.add_bound(bound_constraint(x, A, B, false, nullptr));
                        return true;
                    }
                }
                // TODO: add other cases for LT and GT atoms
            }
            return false;
        }

        void compute_occurs() {
            m_var_occurs.reset();
            for (auto c : m_clauses)
                compute_occurs(*c);
        }

        void compute_occurs(clause& c) {
            var_vector vars;
            m_pm.begin_vars_incremental();
            for (auto lit : c) {
                bool_var b = lit.var();
                atom* a = m_atoms[b];
                if (!a)
                    continue;
                if (a->is_ineq_atom()) {
                    auto sz = to_ineq_atom(a)->size();
                    for (unsigned i = 0; i < sz; ++i) {
                        auto* p = to_ineq_atom(a)->p(i);
                        m_pm.vars_incremental(p, vars);
                    }
                }
            }
            m_pm.end_vars_incremental(vars);
            unsigned h = 0;
            for (auto v : vars) {
                m_var_occurs.reserve(v + 1);
                m_var_occurs[v].push_back(&c);
                h |= (1ul << (v % 32ul));
            }
            c.set_var_hash(h);
        }

        bool cleanup_removed() {
            unsigned j = 0, sz = m_clauses.size();
            for (unsigned i = 0; i < sz; ++i) {
                auto c = m_clauses[i];
                if (c->is_removed())
                    s.del_clause(c);
                else
                    m_clauses[j++] = c;
            }
            m_clauses.shrink(j);
            return j < sz;
        }

        bool unit_subsumption_simplify(clause& src, clause& c) {
            if (src.size() != 1)
                return false;
            auto u = src[0];
            for (auto lit : c) {
                if (subsumes(u, ~lit)) {
                    
                    literal_vector lits;
                    for (auto lit2 : c)
                        if (lit2 != lit)
                            lits.push_back(lit2);
                    if (lits.empty())
                        return false;
                    auto a = s.join(c.assumptions(), src.assumptions());
                    auto cls = s.mk_clause(lits.size(), lits.data(), false, a);
                    if (cls)
                        compute_occurs(*cls);
                    return true;
                }
            }
            return false;
        }

        //
        // Subsumption simplification
        // 
        // Remove D if C subsumes D
        //                
        // Unit subsumption resolution
        // u is a unit literal (lit or C) is a clause
        // u => ~lit, then simplify (lit or C) to C
        // 
        void subsumption_simplify() {
            compute_occurs();
            for (unsigned v = m_var_occurs.size(); v-- > 0; ) {
                auto& clauses = m_var_occurs[v];
                unsigned sz = clauses.size();
                for (unsigned i = 0; i < sz; ++i) {
                    auto c = clauses[i];
                    if (c->is_marked() || c->is_removed())
                        continue;
                    c->mark();
                    for (unsigned j = 0; j < sz; ++j) {
                        auto c2 = clauses[j];
                        if (c == c2 || c2->is_removed())
                            continue;
                        if (subsumes(*c, *c2) || unit_subsumption_simplify(*c, *c2)) {
                            IF_VERBOSE(3, s.display(verbose_stream() << "subsumes ", *c);
                            s.display(verbose_stream() << " ", *c2) << "\n");
                            s.inc_simplify();
                            c2->set_removed();
                        }
                    }
                }
            }
            for (auto c : m_clauses)
                c->unmark();

            cleanup_removed();
        }

        // does c1 subsume c2?
        bool subsumes(clause const& c1, clause const& c2) {
            if (c1.size() > c2.size())
                return false;
            if ((c1.var_hash() & c2.var_hash()) != c1.var_hash())
                return false;
            for (auto lit1 : c1) {
                if (!any_of(c2, [&](auto lit2) { return subsumes(lit1, lit2); }))
                    return false;
            }
            return true;
        }

        bool subsumes(literal lit1, literal lit2) {
            if (lit1 == lit2)
                return true;

            atom* a1 = m_atoms[lit1.var()];
            atom* a2 = m_atoms[lit2.var()];
            if (!a1 || !a2)
                return false;

            // use m_pm.ge(p1, p2) 
            // whenever lit1 = p1 < 0,    lit2 = p2 < 0
            // or       lit1 = p1 < 0,    lit2 = !(p2 > 0)
            // or       lit1 = !(p1 > 0), lit2 = !(p2 > 0)
            // use m_pm.ge(p2, p1)
            // whenever lit1 = p1 > 0,    lit2 = p2 > 0
            // or       lit1 = !(p1 < 0), lit2 = !(p2 < 0)
            // or       lit1 = p1 > 0,    lit2 = !(p2 < 0)
            // or       lit1 = !(p1 > 0), lit2 = p2 < 0
            //
            if (a1->is_ineq_atom() && a2->is_ineq_atom()) {
                auto& i1 = *to_ineq_atom(a1);
                auto& i2 = *to_ineq_atom(a2);
                auto is_lt1 = !lit1.sign() && a1->get_kind() == atom::kind::LT;
                auto is_le1 = lit1.sign() && a1->get_kind() == atom::kind::GT;
                auto is_gt1 = !lit1.sign() && a1->get_kind() == atom::kind::GT;
                auto is_ge1 = lit1.sign() && a1->get_kind() == atom::kind::LT;

                auto is_lt2 = !lit2.sign() && a2->get_kind() == atom::kind::LT;
                auto is_le2 = lit2.sign() && a2->get_kind() == atom::kind::GT;
                auto is_gt2 = !lit2.sign() && a2->get_kind() == atom::kind::GT;
                auto is_ge2 = lit2.sign() && a2->get_kind() == atom::kind::LT;

                auto check_ge = (is_lt1 && (is_lt2 || is_le2)) || (is_le1 && is_le2);
                auto check_le = (is_gt1 && (is_gt2 || is_ge2)) || (is_ge1 && is_ge2);

                if (i1.size() != i2.size())
                    ;
                else if (check_ge) {
                    for (unsigned i = 0; i < i1.size(); ++i)
                        if (!m_pm.ge(i1.p(i), i2.p(i)))
                            return false;
                    return true;
                }
                else if (check_le) {
                    for (unsigned i = 0; i < i1.size(); ++i)
                        if (!m_pm.ge(i2.p(i), i1.p(i)))
                            return false;
                    return true;
                }
            }
            return false;
        }

        //
// Fourier Motzkin elimination
//

        bool fm() {
            if (any_of(m_clauses, [&](clause* c) { return s.has_root_atom(*c); }))
                return false;
            compute_occurs();

            for (unsigned v = m_var_occurs.size(); v-- > 0; )
                apply_fm(v, m_var_occurs[v]);

            return cleanup_removed();
        }

        // progression of possible features:
        // . Current: unit literals
        // . Either lower or upper bound is unit coefficient
        // . single occurrence of x in C
        // . (x <= t or x <= s or C) == (x <= max(s, t) or C)
        //

        bool is_invertible(var x, polynomial_ref& A) {
            if (!m_pm.is_const(A))
                return false;
            if (s.is_int(x) && !is_unit(A))
                return false;
            return true;
        }

        bool apply_fm(var x, ptr_vector<clause>& clauses) {
            polynomial_ref A(m_pm), B(m_pm);
            vector<bound_constraint> lo, hi;
            poly* p = nullptr;
            bool all_solved = true;
            for (auto c : clauses) {
                if (c->is_removed())
                    continue;
                if (c->size() != 1) {
                    all_solved = false;
                    continue;
                }
                literal lit = (*c)[0];
                bool sign = lit.sign();
                ineq_atom const& a = *to_ineq_atom(m_atoms[lit.var()]);
                if (sign && a.is_eq()) {
                    all_solved = false;
                    continue;
                }
                if (!is_single_poly(a, p)) {
                    all_solved = false;
                    continue;
                }
                if (1 != m_pm.degree(p, x)) {
                    all_solved = false;
                    continue;
                }
                A = m_pm.coeff(p, x, 1, B);
                if (!is_invertible(x, A)) {
                    all_solved = false;
                    continue;
                }
                auto const& A_value = m_pm.coeff(A, 0);
                bool is_pos = m_pm.m().is_pos(A_value);
                bool is_strict = false;
                switch (a.get_kind()) {
                case atom::LT:
                    //  !(Ax + B < 0) == Ax + B >= 0
                    if (sign)
                        is_strict = false;
                    else {
                        // Ax + B < 0 == -Ax - B > 0
                        A = -A;
                        B = -B;
                        is_pos = !is_pos;
                        if (s.is_int(x)) {
                            // Ax + B > 0 == Ax + B - |A| >= 0
                            if (is_pos)
                                B = m_pm.sub(B, A);
                            else
                                B = m_pm.add(B, A);
                            is_strict = false;
                        }
                        else
                            is_strict = true;
                    }
                    break;
                case atom::GT:
                    //  !(Ax + B > 0) == -Ax + -B >= 0
                    if (sign) {
                        A = -A;
                        B = -B;
                        is_pos = !is_pos;
                        is_strict = false;
                    }
                    else {
                        // Ax + B > 0
                        if (s.is_int(x)) {
                            // Ax + B - |A| >= 0
                            if (is_pos)
                                B = m_pm.sub(B, A);
                            else
                                B = m_pm.add(B, A);
                            is_strict = false;
                        }
                        else
                            is_strict = true;
                    }
                    break;
                case atom::EQ: {
                    all_solved = false;
                    if (sign)
                        continue;
                    bound_constraint l(x, A, B, false, c);
                    A = -A;
                    B = -B;
                    bound_constraint h(x, A, B, false, c);
                    apply_fm_equality(x, clauses, l, h);
                    return true;
                }
                default:
                    UNREACHABLE();
                    break;
                }
                auto& set = is_pos ? hi : lo;
                bool found = false;
                for (auto const& bound : set) {
                    if (is_strict == bound.is_strict && m_pm.eq(A, bound.A) && m_pm.eq(B, bound.B))
                        found = true;
                }
                if (found)
                    continue;

                set.push_back(bound_constraint(x, A, B, is_strict, c));

            }

            if (lo.empty() && hi.empty())
                return false;

            if (apply_fm_equality(x, clauses, lo, hi))
                return true;


            if (!all_solved)
                return false;

            IF_VERBOSE(3,
                verbose_stream() << "x" << x << " lo " << lo.size() << " hi " << hi.size() << "\n";
            for (auto c : clauses)
                if (!c->is_removed())
                    s.display(verbose_stream(), *c) << "\n";
            );

            auto num_lo = lo.size(), num_hi = hi.size();
            if (num_lo >= 2 && num_hi >= 2 && (num_lo > 2 || num_hi > 2))
                return false;

            apply_fm_inequality(x, clauses, lo, hi);

            return true;
        }

        void apply_fm_inequality(
            var x, ptr_vector<clause>& clauses,
            vector<bound_constraint>& lo, vector<bound_constraint>& hi) {

            polynomial_ref C(m_pm), D(m_pm);
            for (auto c : clauses)
                c->set_removed();

            for (auto const& l : lo) {
                // l.A * x + l.B, l.is_strict;, l.A < 0
                for (auto const& h : hi) {
                    // h.A * x + h.B, h.is_strict; h.A > 0
                    // (l.A x + l.B)*h.A + (h.A x + h.B)*|l.A| >= 0
                    C = m_pm.mul(l.B, h.A);
                    D = m_pm.mul(h.B, l.A);
                    C = m_pm.sub(C, D);
                    poly* p = C.get();
                    bool is_even = false;
                    m_lemma.reset();
                    if (l.is_strict || h.is_strict)
                        m_lemma.push_back(s.mk_ineq_literal(atom::GT, 1, &p, &is_even, true));
                    else
                        m_lemma.push_back(~s.mk_ineq_literal(atom::LT, 1, &p, &is_even, true));
                    if (m_lemma[0] == true_literal)
                        continue;
                    auto a = s.join(l.c->assumptions(), h.c->assumptions());
                    auto cls = s.mk_clause(m_lemma.size(), m_lemma.data(), false, a);
                    if (cls)
                        compute_occurs(*cls);
                    IF_VERBOSE(3, s.display(verbose_stream() << "add resolvent ", *cls) << "\n");
                }
            }

            // track updates for model reconstruction
            for (auto const& l : lo)
                s.add_bound(l);
            for (auto const& h : hi)
                s.add_bound(h);
        }

        literal substitute_var(var x, poly* p, poly* q, literal lit) {
            auto b = lit.var();
            auto a = m_atoms[b];
            if (!a)
                return lit;
            SASSERT(a->is_ineq_atom());
            auto& a1 = *to_ineq_atom(a);
            auto r = substitute_var(x, p, q, a1);
            if (r == null_literal)
                r = lit;
            else if (lit.sign())
                r.neg();
            return r;
        }

        literal substitute_var(var x, poly* p, poly* q, ineq_atom const& a) {
            unsigned sz = a.size();
            bool_vector even;
            polynomial_ref pr(m_pm), qq(q, m_pm);
            qq = -qq;
            polynomial_ref_vector ps(m_pm);
            bool change = false;
            auto k = a.get_kind();
            for (unsigned i = 0; i < sz; ++i) {
                poly* po = a.p(i);
                m_pm.substitute(po, x, qq, p, pr);
                change |= pr != po;
                TRACE("nlsat", tout << pr << "\n";);
                if (m_pm.is_zero(pr)) {
                    ps.reset();
                    even.reset();
                    ps.push_back(pr);
                    even.push_back(false);
                    break;
                }
                if (m_pm.is_const(pr)) {
                    if (!a.is_even(i) && m_pm.m().is_neg(m_pm.coeff(pr, 0)))
                        k = atom::flip(k);
                    continue;
                }
                ps.push_back(pr);
                even.push_back(a.is_even(i));
            }
            if (!change)
                return null_literal;
            return s.mk_ineq_literal(k, ps.size(), ps.data(), even.data(), true);
        }

        bool apply_fm_equality(
            var x, ptr_vector<clause>& clauses,
            vector<bound_constraint>& lo, vector<bound_constraint>& hi) {
            for (auto& l : lo) {
                if (l.is_strict)
                    continue;
                l.A = -l.A;
                l.B = -l.B;
                for (auto& h : hi) {
                    if (h.is_strict)
                        continue;
                    if (!m_pm.eq(l.B, h.B))
                        continue;
                    if (!m_pm.eq(l.A, h.A))
                        continue;
                    l.A = -l.A;
                    l.B = -l.B;
                    apply_fm_equality(x, clauses, l, h);
                    s.inc_simplify();
                    return true;
                }
                l.A = -l.A;
                l.B = -l.B;
            }
            return false;
        }

        void apply_fm_equality(
            var x, ptr_vector<clause>& clauses,
            bound_constraint& l, bound_constraint& h) {
            auto a1 = s.join(l.c->assumptions(), h.c->assumptions());
            s.inc_ref(a1);

            polynomial_ref A(l.A), B(l.B);

            if (m_pm.is_neg(l.A)) {
                A = -A;
                B = -B;
            }

            for (auto c : clauses) {
                if (c->is_removed())
                    continue;
                c->set_removed();
                if (c == l.c || c == h.c)
                    continue;
                m_lemma.reset();
                bool is_tautology = false;
                for (literal lit : *c) {
                    lit = substitute_var(x, A, B, lit);
                    m_lemma.push_back(lit);
                    if (lit == true_literal)
                        is_tautology = true;
                }
                if (is_tautology)
                    continue;
                auto a = s.join(c->assumptions(), a1);
                auto cls = s.mk_clause(m_lemma.size(), m_lemma.data(), false, a);

                IF_VERBOSE(3,
                    if (cls) {
                        s.display_proc()(verbose_stream(), x) << " * " << l.A << " = " << l.B << "\n";
                        s.display(verbose_stream(), *c) << " -> ";
                        s.display(verbose_stream(), *cls) << " - ";
                        s.display(verbose_stream(), *l.c) << " ";
                        s.display(verbose_stream(), *h.c) << "\n";
                    });
                if (cls)
                    compute_occurs(*cls);
            }
            s.dec_ref(a1);
            // track updates for model reconstruction
            s.add_bound(l);
            s.add_bound(h);
            s.inc_simplify();
        }

        bool is_single_poly(ineq_atom const& a, poly*& p) {
            unsigned sz = a.size();
            return sz == 1 && a.is_odd(0) && (p = a.p(0), true);
        }

        bool is_unit(polynomial_ref const& p) {
            if (!m_pm.is_const(p))
                return false;
            auto const& c = m_pm.coeff(p, 0);
            return m_pm.m().is_one(c) || m_pm.m().is_minus_one(c);
        }
    };

    simplify::simplify(solver& s, atom_vector& atoms, clause_vector& clauses, clause_vector& learned, pmanager& pm) {
        m_imp = alloc(imp, s, atoms, clauses, learned, pm);
    }

    simplify::~simplify() {
        dealloc(m_imp);
    }

    void simplify::operator()() {
        (*m_imp)();
    }

};
