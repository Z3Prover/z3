/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_evaluator.cpp

Abstract:

    Helper class for computing the infeasible intervals of an
    arithmetic literal.

Author:

    Leonardo de Moura (leonardo) 2012-01-12.

Revision History:

--*/
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_solver.h"

namespace nlsat {

    struct evaluator::imp {
        solver&                  m_solver;
        assignment const &       m_assignment;
        pmanager &               m_pm;
        small_object_allocator & m_allocator;
        anum_manager &           m_am;
        interval_set_manager     m_ism;
        scoped_anum_vector       m_tmp_values;
        scoped_anum_vector       m_add_roots_tmp;
        scoped_anum_vector       m_inf_tmp;
        
        // sign tables: light version
        struct sign_table {
            anum_manager &     m_am;
            struct section {
                anum     m_root;
                unsigned m_pos;
            };
            svector<section>   m_sections;
            unsigned_vector    m_sorted_sections; // refs to m_sections
            unsigned_vector    m_poly_sections;   // refs to m_sections
            svector<int>       m_poly_signs;
            struct poly_info {
                unsigned       m_num_roots;
                unsigned       m_first_section;   // idx in m_poly_sections;
                unsigned       m_first_sign;      // idx in m_poly_signs;
                poly_info(unsigned num, unsigned first_section, unsigned first_sign):
                    m_num_roots(num),
                    m_first_section(first_section),
                    m_first_sign(first_sign) {
                }
            };
            svector<poly_info> m_info;
            
            sign_table(anum_manager & am):m_am(am) {}

            ~sign_table() {
                reset();
            }

            void reset() {
                unsigned sz = m_sections.size();
                for (unsigned i = 0; i < sz; i++)
                    m_am.del(m_sections[i].m_root);
                m_sections.reset();
                m_sorted_sections.reset();
                m_poly_sections.reset();
                m_poly_signs.reset();
                m_info.reset();
            }

            unsigned mk_section(anum & v, unsigned pos) {
                unsigned new_id = m_sections.size();
                m_sections.push_back(section());
                section & new_s = m_sections.back();
                m_am.set(new_s.m_root, v);
                new_s.m_pos = pos;
                return new_id;
            }

            // Merge the new roots of a polynomial p into m_sections & m_sorted_sections.
            // Store the section ids for the new roots in p_section_ids
            unsigned_vector new_sorted_sections;
            void merge(anum_vector & roots, unsigned_vector & p_section_ids) {
                new_sorted_sections.reset();  // new m_sorted_sections
                unsigned i1  = 0;
                unsigned sz1 = m_sorted_sections.size();
                unsigned i2  = 0;
                unsigned sz2 = roots.size();
                unsigned j   = 0;
                while (i1 < sz1 && i2 < sz2) {
                    unsigned s1_id = m_sorted_sections[i1];
                    section & s1   = m_sections[s1_id];
                    anum &    r2   = roots[i2];
                    int c = m_am.compare(s1.m_root, r2);
                    if (c == 0) {
                        new_sorted_sections.push_back(s1_id);
                        p_section_ids.push_back(s1_id);
                        s1.m_pos = j;
                        i1++;
                        i2++;
                    }
                    else if (c < 0) {
                        new_sorted_sections.push_back(s1_id);
                        s1.m_pos = j;
                        i1++;
                    }
                    else {
                        // create new section
                        unsigned new_id = mk_section(r2, j);

                        //
                        new_sorted_sections.push_back(new_id);
                        p_section_ids.push_back(new_id);
                        i2++;
                    }
                    j++;
                }
                SASSERT(i1 == sz1 || i2 == sz2);
                while (i1 < sz1) {
                    unsigned s1_id = m_sorted_sections[i1];
                    section & s1   = m_sections[s1_id];
                    
                    new_sorted_sections.push_back(s1_id);
                    s1.m_pos = j;
                    
                    i1++;
                    j++;
                }
                while (i2 < sz2) {
                    anum &    r2   = roots[i2];
                    // create new section
                    unsigned new_id = mk_section(r2, j);
                    
                    //
                    new_sorted_sections.push_back(new_id);
                    p_section_ids.push_back(new_id);
                    i2++;
                    j++;
                }
                m_sorted_sections.swap(new_sorted_sections);
            }

            /**
               \brief Add polynomial with the given roots and signs.
            */
            unsigned_vector p_section_ids;
            void add(anum_vector & roots, svector<int> & signs) {
                p_section_ids.reset();
                if (!roots.empty())
                    merge(roots, p_section_ids);
                unsigned first_sign    = m_poly_signs.size();
                unsigned first_section = m_poly_sections.size();
                unsigned num_signs = signs.size();
                // Must normalize signs since we use arithmetic operations such as *
                // during evaluation.
                // Without normalization, overflows may happen, and wrong results may be produced.
                for (unsigned i = 0; i < num_signs; i++)
                    m_poly_signs.push_back(normalize_sign(signs[i]));
                m_poly_sections.append(p_section_ids);
                m_info.push_back(poly_info(roots.size(), first_section, first_sign));
                SASSERT(check_invariant());
            }

            /**
               \brief Add constant polynomial 
            */
            void add_const(int sign) {
                unsigned first_sign    = m_poly_signs.size();
                unsigned first_section = m_poly_sections.size();
                m_poly_signs.push_back(normalize_sign(sign));
                m_info.push_back(poly_info(0, first_section, first_sign));
            }

            unsigned num_cells() const {
                return m_sections.size() * 2 + 1;
            }
            
            /**
               \brief Return true if the given cell is a section (i.e., root)
            */
            bool is_section(unsigned c) const {
                SASSERT(c < num_cells());
                return c % 2 == 1;
            }

            /**
               \brief Return true if the given cell is a sector (i.e., an interval between roots, or (-oo, min-root), or (max-root, +oo)).
            */
            bool is_sector(unsigned c) const {
                SASSERT(c < num_cells());
                return c % 2 == 0;
            }

            /**
               \brief Return the root id associated with the given section.
               
               \pre is_section(c)
            */
            unsigned get_root_id(unsigned c) const {
                SASSERT(is_section(c));
                return m_sorted_sections[c/2];
            }
            
            // Return value of root idx.
            // If idx == UINT_MAX, it return zero (this is a hack to simplify the infeasible_intervals method
            anum const & get_root(unsigned idx) const {
                static anum zero;
                if (idx == UINT_MAX)
                    return zero;
                SASSERT(idx < m_sections.size());
                return m_sections[idx].m_root;
            }

            static unsigned section_id_to_cell_id(unsigned section_id) {
                return section_id*2 + 1;
            }
            
            // Return the cell_id of the root i of pinfo
            unsigned cell_id(poly_info const & pinfo, unsigned i) const {
                return section_id_to_cell_id(m_sections[m_poly_sections[pinfo.m_first_section + i]].m_pos);
            }
            
            // Return the sign idx of pinfo
            int sign(poly_info const & pinfo, unsigned i) const {
                return m_poly_signs[pinfo.m_first_sign + i];
            }
            
#define LINEAR_SEARCH_THRESHOLD 8
            int sign_at(unsigned info_id, unsigned c) const {
                poly_info const & pinfo  = m_info[info_id];
                unsigned num_roots = pinfo.m_num_roots;
                if (num_roots < LINEAR_SEARCH_THRESHOLD) {
                    unsigned i = 0;
                    for (; i < num_roots; i++) {
                        unsigned section_cell_id = cell_id(pinfo, i);
                        if (section_cell_id == c)
                            return 0;
                        else if (section_cell_id > c)
                            break;
                    }
                    return sign(pinfo, i);
                }
                else {
                    if (num_roots == 0)
                        return sign(pinfo, 0);
                    unsigned root_1_cell_id = cell_id(pinfo, 0);
                    unsigned root_n_cell_id = cell_id(pinfo, num_roots - 1);
                    if (c < root_1_cell_id)
                        return sign(pinfo, 0);
                    else if (c == root_1_cell_id || c == root_n_cell_id)
                        return 0;
                    else if (c > root_n_cell_id)
                        return sign(pinfo, num_roots);
                    int low  = 0;
                    int high = num_roots-1;
                    while (true) {
                        SASSERT(0 <= low && high < static_cast<int>(num_roots));
                        SASSERT(cell_id(pinfo, low) < c);
                        SASSERT(c < cell_id(pinfo, high));
                        if (high == low + 1) {
                            SASSERT(cell_id(pinfo, low) < c);
                            SASSERT(c < cell_id(pinfo, low+1));
                            return sign(pinfo, low+1);
                        }
                        SASSERT(high > low + 1);
                        int mid   = low + ((high - low)/2);
                        SASSERT(low < mid && mid < high);
                        unsigned mid_cell_id = cell_id(pinfo, mid);
                        if (mid_cell_id == c) {
                            return 0;
                        }
                        if (c < mid_cell_id) {
                            high = mid;
                        }
                        else {
                            SASSERT(mid_cell_id < c);
                            low  = mid;
                        }
                    }
                }
            }
            
            bool check_invariant() const {
                SASSERT(m_sections.size() == m_sorted_sections.size());
                for (unsigned i = 0; i < m_sorted_sections.size(); i++) {
                    SASSERT(m_sorted_sections[i] < m_sections.size());
                    SASSERT(m_sections[m_sorted_sections[i]].m_pos == i);
                }
                unsigned total_num_sections = 0;
                unsigned total_num_signs = 0;
                for (unsigned i = 0; i < m_info.size(); i++) {
                    SASSERT(m_info[i].m_first_section <= m_poly_sections.size());
                    SASSERT(m_info[i].m_num_roots == 0 || m_info[i].m_first_section < m_poly_sections.size());
                    SASSERT(m_info[i].m_first_sign < m_poly_signs.size());
                    total_num_sections += m_info[i].m_num_roots;
                    total_num_signs += m_info[i].m_num_roots + 1;
                }
                SASSERT(total_num_sections == m_poly_sections.size());
                SASSERT(total_num_signs == m_poly_signs.size());
                return true;
            }

            // Display sign table for the given variable
            void display(std::ostream & out) const {
                out << "sections:\n  ";
                for (unsigned i = 0; i < m_sections.size(); i++) {
                    if (i > 0) out << " < ";
                    m_am.display_decimal(out, m_sections[m_sorted_sections[i]].m_root);
                }
                out << "\n";
                out << "sign variations:\n";
                for (unsigned i = 0; i < m_info.size(); i++) {
                    out << "  ";
                    for (unsigned j = 0; j < num_cells(); j++) {
                        if (j > 0)
                            out << " ";
                        int s = sign_at(i, j);
                        if (s < 0) out << "-";
                        else if (s == 0) out << "0";
                        else out << "+";
                    }
                    out << "\n";
                }
            }

            // Display sign table for the given variable
            void display_raw(std::ostream & out) const {
                out << "sections:\n  ";
                for (unsigned i = 0; i < m_sections.size(); i++) {
                    if (i > 0) out << " < ";
                    m_am.display_decimal(out, m_sections[m_sorted_sections[i]].m_root);
                }
                out << "\n";
                out << "poly_info:\n";
                for (unsigned i = 0; i < m_info.size(); i++) {
                    out << "  roots:";
                    poly_info const & info = m_info[i];
                    for (unsigned j = 0; j < info.m_num_roots; j++) {
                        out << " ";
                        out << m_poly_sections[info.m_first_section+j];
                    }
                    out << ", signs:";
                    for (unsigned j = 0; j < info.m_num_roots+1; j++) {
                        out << " ";
                        int s = m_poly_signs[info.m_first_sign+j];
                        if (s < 0) out << "-";
                        else if (s == 0) out << "0";
                        else out << "+";
                    }
                    out << "\n";
                }
            }
        };

        sign_table m_sign_table_tmp;

        imp(solver& s, assignment const & x2v, pmanager & pm, small_object_allocator & allocator):
            m_solver(s),
            m_assignment(x2v),
            m_pm(pm),
            m_allocator(allocator),
            m_am(m_assignment.am()),
            m_ism(m_am, allocator),
            m_tmp_values(m_am),
            m_add_roots_tmp(m_am),
            m_inf_tmp(m_am),
            m_sign_table_tmp(m_am) {
        }

        var max_var(poly const * p) const {
            return m_pm.max_var(p);
        }

        /**
           \brief Return the sign of the polynomial in the current interpretation.
           
           \pre All variables of p are assigned in the current interpretation.
        */
        int eval_sign(poly * p) {
            // TODO: check if it is useful to cache results
            SASSERT(m_assignment.is_assigned(max_var(p)));
            int r = m_am.eval_sign_at(polynomial_ref(p, m_pm), m_assignment);
            return r > 0 ? +1 : (r < 0 ? -1 : 0);
        }
        
        bool satisfied(int sign, atom::kind k) {
            return 
                (sign == 0 && (k == atom::EQ || k == atom::ROOT_EQ || k == atom::ROOT_LE || k == atom::ROOT_GE)) ||
                (sign <  0 && (k == atom::LT || k == atom::ROOT_LT || k == atom::ROOT_LE)) ||
                (sign >  0 && (k == atom::GT || k == atom::ROOT_GT || k == atom::ROOT_GE));
        }

        bool satisfied(int sign, atom::kind k, bool neg) {
            bool r = satisfied(sign, k);
            return neg ? !r : r;
        }

        bool eval_ineq(ineq_atom * a, bool neg) {
            SASSERT(m_assignment.is_assigned(a->max_var()));
            // all variables of a were already assigned... 
            atom::kind k = a->get_kind();
            unsigned sz  = a->size();
            int sign = 1;
            for (unsigned i = 0; i < sz; i++) {
                int curr_sign = eval_sign(a->p(i));
                if (a->is_even(i) && curr_sign < 0)
                    curr_sign = 1;
                sign = sign * curr_sign;
                if (sign == 0)
                    break;
            }
            return satisfied(sign, k, neg);
        }

        bool eval_root(root_atom * a, bool neg) {
            SASSERT(m_assignment.is_assigned(a->max_var()));
            // all variables of a were already assigned... 
            atom::kind k = a->get_kind();
            scoped_anum_vector & roots = m_tmp_values;
            roots.reset();
            m_am.isolate_roots(polynomial_ref(a->p(), m_pm), undef_var_assignment(m_assignment, a->x()), roots);
            TRACE("nlsat",
                  m_solver.display(tout << (neg?"!":""), *a); tout << "\n";
                  if (roots.empty()) {
                      tout << "No roots\n";
                  }
                  else {
                      tout << "Roots for ";
                      for (unsigned i = 0; i < roots.size(); ++i) {
                          m_am.display_interval(tout, roots[i]); tout << " "; 
                      }
                      tout << "\n";
                  }
                  m_assignment.display(tout);
                  );
            SASSERT(a->i() > 0);
            if (a->i() > roots.size()) {
                return neg;
            }
            int sign = m_am.compare(m_assignment.value(a->x()), roots[a->i() - 1]);            
            return satisfied(sign, k, neg);
        }
        
        bool eval(atom * a, bool neg) {
            return a->is_ineq_atom() ? eval_ineq(to_ineq_atom(a), neg) : eval_root(to_root_atom(a), neg);
        }

        svector<int> m_add_signs_tmp;
        void add(poly * p, var x, sign_table & t) {
            SASSERT(m_pm.max_var(p) <= x);
            if (m_pm.max_var(p) < x) {
                t.add_const(eval_sign(p));
            }
            else {
                // isolate roots of p
                scoped_anum_vector & roots = m_add_roots_tmp;
                svector<int>       & signs = m_add_signs_tmp;
                roots.reset();
                signs.reset();
                TRACE("nlsat_evaluator", tout << "x: " << x << " max_var(p): " << m_pm.max_var(p) << "\n";);
                // Note: I added undef_var_assignment in the following statement, to allow us to obtain the infeasible interval sets
                // even when the maximal variable is assigned. I need this feature to minimize conflict cores.
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(m_assignment, x), roots, signs);
                t.add(roots, signs);
            }
        }

        // Evaluate the sign of p1^e1*...*pn^en (of atom a) in cell c of table t.
        int sign_at(ineq_atom * a, sign_table const & t, unsigned c) const {
            int sign = 1;
            unsigned num_ps = a->size();
            for (unsigned i = 0; i < num_ps; i++) {
                int curr_sign = t.sign_at(i, c);
                TRACE("nlsat_evaluator_bug", tout << "sign of i: " << i << " at cell " << c << "\n"; 
                      m_pm.display(tout, a->p(i)); 
                      tout << "\nsign: " << curr_sign << "\n";);
                if (a->is_even(i) && curr_sign < 0)
                    curr_sign = 1;
                sign = sign * curr_sign;
                if (sign == 0)
                    break;
            }
            return sign;
        }
        
        interval_set_ref infeasible_intervals(ineq_atom * a, bool neg) {
            sign_table & table = m_sign_table_tmp;
            table.reset();
            unsigned num_ps = a->size();
            var x = a->max_var();
            for (unsigned i = 0; i < num_ps; i++) {
                add(a->p(i), x, table);
                TRACE("nlsat_evaluator_bug", tout << "table after:\n"; m_pm.display(tout, a->p(i)); tout << "\n"; table.display_raw(tout);); 
                
            }
            TRACE("nlsat_evaluator", 
                  tout << "sign table for:\n"; 
                  for (unsigned i = 0; i < num_ps; i++) { m_pm.display(tout, a->p(i)); tout << "\n"; }
                  table.display(tout););

            interval_set_ref result(m_ism);
            interval_set_ref set(m_ism);
            literal jst(a->bvar(), neg);
            atom::kind k = a->get_kind();
            
            anum dummy;
            bool prev_sat         = true;
            bool prev_inf         = true;
            bool prev_open        = true;
            unsigned prev_root_id = UINT_MAX;
            
            unsigned num_cells = table.num_cells();
            for (unsigned c = 0; c < num_cells; c++) {
                TRACE("nlsat_evaluator",
                      tout << "cell: " << c << "\n";
                      tout << "prev_sat: " << prev_sat << "\n";
                      tout << "prev_inf: " << prev_inf << "\n";
                      tout << "prev_open: " << prev_open << "\n";
                      tout << "prev_root_id: " << prev_root_id << "\n";
                      tout << "processing cell: " << c << "\n";
                      tout << "interval_set so far:\n" << result << "\n";);
                int sign = sign_at(a, table, c);
                TRACE("nlsat_evaluator", tout << "sign: " << sign << "\n";);
                if (satisfied(sign, k, neg)) {
                    // current cell is satisfied
                    if (!prev_sat) {
                        SASSERT(c > 0);
                        // add interval
                        bool curr_open;
                        unsigned curr_root_id;
                        if (table.is_section(c)) {
                            curr_open    = true;
                            curr_root_id = table.get_root_id(c);
                        }
                        else {
                            SASSERT(table.is_section(c-1));
                            curr_open    = false;
                            curr_root_id = table.get_root_id(c-1);
                        }
                        set = m_ism.mk(prev_open, prev_inf, table.get_root(prev_root_id),
                                       curr_open, false,    table.get_root(curr_root_id), jst);
                        result = m_ism.mk_union(result, set);   
                        prev_sat = true;
                    }
                }
                else {
                    // current cell is not satisfied
                    if (prev_sat) {
                        if (c == 0) {
                            if (num_cells == 1) {
                                // (-oo, oo)
                                result = m_ism.mk(true, true, dummy, true, true, dummy, jst); 
                            }
                            else {
                                // save -oo as beginning of infeasible interval
                                prev_open    = true;
                                prev_inf     = true;
                                prev_root_id = UINT_MAX;
                            }
                        }
                        else { 
                            SASSERT(c > 0);
                            prev_inf     = false;
                            if (table.is_section(c)) {
                                prev_open    = false;
                                prev_root_id = table.get_root_id(c); 
                                TRACE("nlsat_evaluator", tout << "updated prev_root_id: " << prev_root_id << " using cell: " << c << "\n";);
                            }
                            else {
                                SASSERT(table.is_section(c-1));
                                prev_open    = true;
                                prev_root_id = table.get_root_id(c-1);
                                TRACE("nlsat_evaluator", tout << "updated prev_root_id: " << prev_root_id << " using cell: " << (c - 1) << "\n";);
                            }
                        }
                        prev_sat = false;
                    }
                    if (c == num_cells - 1) {
                        // last cell add interval with  (prev, oo)
                        set = m_ism.mk(prev_open, prev_inf, table.get_root(prev_root_id),
                                       true, true, dummy, jst);
                        result = m_ism.mk_union(result, set);
                    } 
                }
            }
            TRACE("nlsat_evaluator", tout << "interval_set: " << result << "\n";);
            return result;
        }

        interval_set_ref infeasible_intervals(root_atom * a, bool neg) {
            atom::kind k = a->get_kind();
            unsigned i = a->i();
            SASSERT(i > 0);
            literal jst(a->bvar(), neg);
            anum dummy;
            scoped_anum_vector & roots = m_tmp_values;
            roots.reset();
            var x = a->max_var();
            // Note: I added undef_var_assignment in the following statement, to allow us to obtain the infeasible interval sets
            // even when the maximal variable is assigned. I need this feature to minimize conflict cores.
            m_am.isolate_roots(polynomial_ref(a->p(), m_pm), undef_var_assignment(m_assignment, x), roots);
            interval_set_ref result(m_ism);

            if (i > roots.size()) {
                // p does have sufficient roots
                // atom is false by definition
                if (neg) {
                    result = m_ism.mk_empty(); 
                }
                else {
                    result = m_ism.mk(true, true, dummy, true, true, dummy, jst); // (-oo, oo)
                }
            }
            else {
                anum const & r_i = roots[i-1];
                switch (k) {
                case atom::ROOT_EQ:
                    if (neg) {
                        result = m_ism.mk(false, false, r_i, false, false, r_i, jst); // [r_i, r_i]
                    }
                    else {
                        interval_set_ref s1(m_ism), s2(m_ism);
                        s1 = m_ism.mk(true, true, dummy, true, false, r_i, jst); // (-oo, r_i)
                        s2 = m_ism.mk(true, false, r_i, true, true, dummy, jst); // (r_i, oo)
                        result = m_ism.mk_union(s1, s2);
                    }
                    break;
                case atom::ROOT_LT:
                    if (neg)
                        result = m_ism.mk(true, true, dummy, true, false, r_i, jst); // (-oo, r_i)
                    else
                        result = m_ism.mk(false, false, r_i, true, true, dummy, jst); // [r_i, oo)
                    break;
                case atom::ROOT_GT:
                    if (neg) 
                        result = m_ism.mk(true, false, r_i, true, true, dummy, jst); // (r_i, oo)
                    else
                        result = m_ism.mk(true, true, dummy, false, false, r_i, jst); // (-oo, r_i]
                    break;
                case atom::ROOT_LE:
                    if (neg)
                        result = m_ism.mk(true, true, dummy, false, false, r_i, jst); // (-oo, r_i]
                    else
                        result = m_ism.mk(true, false, r_i, true, true, dummy, jst); // (r_i, oo)
                    break;
                case atom::ROOT_GE:
                    if (neg) 
                        result = m_ism.mk(false, false, r_i, true, true, dummy, jst); // [r_i, oo)
                    else
                        result = m_ism.mk(true, true, dummy, true, false, r_i, jst); // (-oo, r_i)
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            TRACE("nlsat_evaluator", tout << "interval_set: " << result << "\n";);
            return result;
        }
        
        interval_set_ref infeasible_intervals(atom * a, bool neg) {
            return a->is_ineq_atom() ? infeasible_intervals(to_ineq_atom(a), neg) : infeasible_intervals(to_root_atom(a), neg); 
        }
    };
    
    evaluator::evaluator(solver& s, assignment const & x2v, pmanager & pm, small_object_allocator & allocator) {
        m_imp = alloc(imp, s, x2v, pm, allocator);
    }

    evaluator::~evaluator() {
        dealloc(m_imp);
    }

    interval_set_manager & evaluator::ism() const {
        return m_imp->m_ism;
    }

    bool evaluator::eval(atom * a, bool neg) {
        return m_imp->eval(a, neg);
    }
        
    interval_set_ref evaluator::infeasible_intervals(atom * a, bool neg) {
        return m_imp->infeasible_intervals(a, neg);
    }

    void evaluator::push() {
        // do nothing
    }

    void evaluator::pop(unsigned num_scopes) {
        // do nothing
    }
};
