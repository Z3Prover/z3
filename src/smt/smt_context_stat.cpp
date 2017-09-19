/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context_stat.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-06.

Revision History:

--*/
#include "smt/smt_context.h"
#include "ast/ast_pp.h"

namespace smt {

    unsigned context::get_lemma_avg_activity() const {
        if (m_lemmas.empty())
            return 0;
        unsigned long long acc            = 0;
        clause_vector::const_iterator it  = m_lemmas.begin();
        clause_vector::const_iterator end = m_lemmas.end();
        for (; it != end; ++it)
            acc += (*it)->get_activity();
        return static_cast<unsigned>(acc / m_lemmas.size());
    }

    static void acc_num_occs(clause * cls, unsigned_vector & lit2num_occs) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal l = cls->get_literal(i);
            lit2num_occs[l.index()]++;
        }
    }

    static void acc_num_occs(clause_vector const & v, unsigned_vector & lit2num_occs) {
        clause_vector::const_iterator it  = v.begin();
        clause_vector::const_iterator end = v.end();
        for (; it != end; ++it)
            acc_num_occs(*it, lit2num_occs);
    }

    void context::display_literal_num_occs(std::ostream & out) const {
        unsigned num_lits = m_assignment.size();
        unsigned_vector lit2num_occs;
        lit2num_occs.resize(num_lits, 0);
        acc_num_occs(m_aux_clauses, lit2num_occs);
        acc_num_occs(m_lemmas, lit2num_occs);
        for (unsigned lidx = 0; lidx < num_lits; lidx++) {
            literal l = to_literal(lidx);
            if (lit2num_occs[lidx] > 0) {
                out << lit2num_occs[lidx] << " ";
                // display_literal(out, l);
                out << l.sign() << " " << mk_pp(bool_var2expr(l.var()), m_manager);
                out << "\n";
            }
        }
    }

    void context::display_num_assigned_literals_per_lvl(std::ostream & out) const {
        unsigned n = 0;
        svector<scope>::const_iterator it  = m_scopes.begin();
        svector<scope>::const_iterator end = m_scopes.end();
        out << "[";
        for (; it != end; ++it) {
            scope const & s = *it;
            SASSERT(n <= s.m_assigned_literals_lim);
            out << (s.m_assigned_literals_lim - n) << " ";
            n = s.m_assigned_literals_lim;
        }
        SASSERT(n <= m_assigned_literals.size());
        out << (m_assigned_literals.size() - n) << "]";
    }

    static void acc_var_num_occs(clause * cls, unsigned_vector & var2num_occs) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal l = cls->get_literal(i);
            var2num_occs[l.var()]++;
        }
    }

    static void acc_var_num_occs(clause_vector const & v, unsigned_vector & var2num_occs) {
        clause_vector::const_iterator it  = v.begin();
        clause_vector::const_iterator end = v.end();
        for (; it != end; ++it)
            acc_var_num_occs(*it, var2num_occs);
    }

    void context::display_var_occs_histogram(std::ostream & out) const {
        unsigned num_vars = get_num_bool_vars();
        unsigned_vector var2num_occs;
        var2num_occs.resize(num_vars, 0);
        acc_var_num_occs(m_aux_clauses, var2num_occs);
        acc_var_num_occs(m_lemmas, var2num_occs);
        unsigned_vector histogram;
        for (unsigned v = 0; v < num_vars; v++) {
            unsigned num_occs = var2num_occs[v];
            histogram.reserve(num_occs+1, 0);
            histogram[num_occs]++;
        }
        out << "number of atoms having k occs:\n"; 
        unsigned sz = histogram.size();
        for (unsigned i = 1; i < sz; i++)
            if (histogram[i] > 0)
                out << i << ":" << histogram[i] << " ";
        out << "\n";
    }

    static void acc_var_num_min_occs(clause * cls, unsigned_vector & var2num_min_occs) {
        unsigned num_lits = cls->get_num_literals();
        bool_var min_var  = cls->get_literal(0).var();
        for (unsigned i = 1; i < num_lits; i++) {
            bool_var v = cls->get_literal(i).var();
            if (v < min_var)
                min_var = v;
        }
        var2num_min_occs[min_var]++;
    }

    static void acc_var_num_min_occs(clause_vector const & v, unsigned_vector & var2num_min_occs) {
        clause_vector::const_iterator it  = v.begin();
        clause_vector::const_iterator end = v.end();
        for (; it != end; ++it)
            acc_var_num_min_occs(*it, var2num_min_occs);
    }

    void context::display_num_min_occs(std::ostream & out) const {
        unsigned num_vars = get_num_bool_vars();
        unsigned_vector var2num_min_occs;
        var2num_min_occs.resize(num_vars, 0);
        acc_var_num_min_occs(m_aux_clauses, var2num_min_occs);
        acc_var_num_min_occs(m_lemmas, var2num_min_occs);
        out << "number of min occs:\n";
        for (unsigned v = 0; v < num_vars; v++) {
            if (var2num_min_occs[v] > 0)
                out << v << ":" << var2num_min_occs[v] << " ";
        }
        out << "\n";
    }

    void context::display_profile_res_sub(std::ostream & out) const {
        display_var_occs_histogram(std::cerr);
        display_num_min_occs(std::cerr);
        std::cerr << "\n";
    }

    void context::display_profile(std::ostream & out) const {
        if (m_fparams.m_profile_res_sub)
            display_profile_res_sub(out);
    }
};
