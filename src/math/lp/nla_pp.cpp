/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

   nla_core.cpp

Author:
   Lev Nachmanson (levnach)
   Nikolaj Bjorner (nbjorner)

--*/

#include "math/lp/nla_core.h"
using namespace nla;

template <typename T>
std::ostream& core::print_product(const T& m, std::ostream& out) const {
    bool first = true;
    for (lpvar v : m) {
        if (!first)
            out << " * ";
        else
            first = false;
        if (lp_settings().print_external_var_name())
            out << lra.get_variable_name(v);
        else
            out << "j" << v;
    }
    return out;
}

template <typename T>
std::string core::product_indices_str(const T& m) const {
    std::stringstream out;
    bool first = true;
    for (lpvar v : m) {
        if (!first)
            out << "*";
        else
            first = false;
        out << "j" << v;
        ;
    }
    return out.str();
}

std::ostream& core::print_factor(const factor& f, std::ostream& out) const {
    if (f.sign())
        out << "- ";
    if (f.is_var()) {
        out << "VAR,  " << pp(f.var());
    } else {
        out << "MON, v" << m_emons[f.var()] << " = ";
        print_product(m_emons[f.var()].rvars(), out);
    }
    out << "\n";
    return out;
}

std::ostream& core::print_factor_with_vars(const factor& f, std::ostream& out) const {
    if (f.is_var()) {
        out << pp(f.var());
    } else {
        out << " MON = " << pp_mon_with_vars(*this, m_emons[f.var()]);
    }
    return out;
}

std::ostream& core::print_monic(const monic& m, std::ostream& out) const {
    if (lp_settings().print_external_var_name())
        out << "[" << m.var() << "] := " << lra.get_variable_name(m.var()) << " := ";
    else
        out << "j" << m.var() << " := ";
    print_product(m.vars(), out) << "\n";
    return out;
}
 
std::ostream& core::print_bfc(const factorization& m, std::ostream& out) const {
    SASSERT(m.size() == 2);
    out << "( x = " << pp(m[0]) << "* y = " << pp(m[1]) << ")";
    return out;
}

std::ostream& core::print_monic_with_vars(lpvar v, std::ostream& out) const {
    return print_monic_with_vars(m_emons[v], out);
}

template <typename T>
std::ostream& core::print_product_with_vars(const T& m, std::ostream& out) const {
    print_product(m, out) << "\n";
    for (unsigned k = 0; k < m.size(); ++k) {
        print_var(m[k], out);
    }
    return out;
}

std::ostream& core::print_monic_with_vars(const monic& m, std::ostream& out) const {
    out << "[" << pp(m.var()) << "]\n";
    out << "vars:";
    print_product_with_vars(m.vars(), out) << "\n";
    if (m.vars() == m.rvars())
        out << "same rvars, and m.rsign = " << m.rsign() << " of course\n";
    else {
        out << "rvars:";
        print_product_with_vars(m.rvars(), out) << "\n";
        out << "rsign:" << m.rsign() << "\n";
    }
    return out;
}

std::ostream& core::print_explanation(const lp::explanation& exp, std::ostream& out) const {
    out << "expl: ";
    unsigned i = 0;
    for (auto p : exp) {
        out << "(" << p.ci() << ")";
        lra.constraints().display(out, [this](lpvar j) { return var_str(j); }, p.ci());
        if (++i < exp.size())
            out << "      ";
    }
    return out;
}
   
std::ostream& core::print_ineq(const ineq& in, std::ostream& out) const {
    lra.print_term_as_indices(in.term(), out);
    return out << " " << lconstraint_kind_string(in.cmp()) << " " << in.rs();
}

std::ostream& core::print_var(lpvar j, std::ostream& out) const {
    if (is_monic_var(j))
        print_monic(m_emons[j], out);

    lra.print_column_info(j, out);
    signed_var jr = m_evars.find(j);
    out << "root=";
    if (jr.sign()) {
        out << "-";
    }

    out << lra.get_variable_name(jr.var()) << "\n";
    return out;
}

std::ostream& core::print_monics(std::ostream& out) const {
    for (auto& m : m_emons) 
        print_monic_with_vars(m, out);    
    return out;
}

std::ostream& core::print_ineqs(const lemma& l, std::ostream& out) const {
    std::unordered_set<lpvar> vars;
    out << "ineqs: ";
    if (l.ineqs().size() == 0) {
        out << "conflict\n";
    } else {
        for (unsigned i = 0; i < l.ineqs().size(); ++i) {
            auto& in = l.ineqs()[i];
            print_ineq(in, out);
            if (i + 1 < l.ineqs().size()) out << " or ";
            for (lp::lar_term::ival p : in.term())
                vars.insert(p.j());
        }
        out << std::endl;
        for (lpvar j : vars) {
            print_var(j, out);
        }
        out << "\n";
    }
    return out;
}

std::ostream& core::print_factorization(const factorization& f, std::ostream& out) const {
    if (f.is_mon()) {
        out << "is_mon " << pp_mon(*this, f.mon());
    } else {
        for (unsigned k = 0; k < f.size(); ++k) {
            out << "(" << pp(f[k]) << ")";
            if (k < f.size() - 1)
                out << "*";
        }
    }
    return out;
}

void core::trace_print_monic_and_factorization(const monic& rm, const factorization& f, std::ostream& out) const {
    out << "rooted vars: ";
    print_product(rm.rvars(), out) << "\n";
    out << "mon:   " << pp_mon(*this, rm.var()) << "\n";
    out << "value: " << var_val(rm) << "\n";
    print_factorization(f, out << "fact: ") << "\n";
}

template <typename T>
void core::trace_print_rms(const T& p, std::ostream& out) {
    out << "p = {\n";
    for (auto j : p) {
        out << "j = " << j << ", rm = " << m_emons[j] << "\n";
    }
    out << "}";
}

void core::print_monic_stats(const monic& m, std::ostream& out) {
    if (m.size() == 2) return;
    monic_coeff mc = canonize_monic(m);
    for (unsigned i = 0; i < mc.vars().size(); ++i) {
        if (abs(val(mc.vars()[i])) == rational(1)) {
            auto vv = mc.vars();
            vv.erase(vv.begin() + i);
            monic const* sv = m_emons.find_canonical(vv);
            if (!sv) {
                out << "nf length" << vv.size() << "\n";
                ;
            }
        }
    }
}

void core::print_stats(std::ostream& out) {
}


std::ostream& core::print_terms(std::ostream& out) const {
    for (const auto* t : lra.terms()) {
        out << "term:";
        print_term(*t, out) << std::endl;
        print_var(t->j(), out);
    }
    return out;
}

std::ostream& core::print_term(const lp::lar_term& t, std::ostream& out) const {
    return lp::print_linear_combination_customized(
        t.coeffs_as_vector(),
        [this](lpvar j) { return var_str(j); },
        out);
}

std::string core::var_str(lpvar j) const {
    std::string result;
    if (is_monic_var(j))
        result += product_indices_str(m_emons[j].vars()) + (check_monic(m_emons[j]) ? "" : "_");
    else
        result += std::string("j") + lp::T_to_string(j);
    //    result += ":w" + lp::T_to_string(get_var_weight(j));
    return result;
}

std::ostream& core::display_row(std::ostream& out, lp::row_strip<lp::mpq> const& row) const {
    auto display_coeff = [&](bool first, lp::mpq const& p) {
        if (first && p == 1)
            return;
        if (first && p > 0)
            out << p;
        else if (p == 1)
            out << " + ";
        else if (p > 0)
            out << " + " << p << " * ";
        else if (p == -1)
            out << " - ";
        else if (first)
            out << p << " * ";
        else
            out << " - " << -p << " * ";
    };
    auto display_var = [&](bool first, lp::mpq p, lp::lpvar v) {
        if (is_monic_var(v)) {
            for (auto w : m_emons[v].vars())
                p *= m_evars.find(w).rsign();           
        } 
        else 
            p *= m_evars.find(v).rsign();
        
        display_coeff(first, p);
        if (is_monic_var(v)) {
            bool first = true;
            for (auto w : m_emons[v].vars())
                out << (first ? (first = false, "") : " * ") << "j" << m_evars.find(w).var();
        } 
        else
            out << "j" << m_evars.find(v).var();  
    };

    bool first = true;
    for (auto const& ri : row) {
        auto v = ri.var();
        if (lra.column_is_fixed(v)) {
            auto q = lra.get_column_value(v).x;
            if (q == 0)
                continue;
            q = q * ri.coeff();
            if (first)
                out << q;
            else if (q > 0)
                out << " + " << q;
            else if (q < 0)
                out << " - " << -q;
        }
        else if (lra.column_has_term(v)) {
            auto const& t = lra.get_term(v);
            for (lp::lar_term::ival p : t) {
                display_var(first, p.coeff() * ri.coeff(), p.j());
                first = false;
            }
        } 
        else {
            display_var(first, ri.coeff(), ri.var());
        }
        first = false;
    }
    out << " = 0\n";
    return out;
}

std::ostream& core::display(std::ostream& out) {
    for (auto& m : m_emons)
        print_monic(m, out);
    return out;
}

std::ostream& core::display_smt(std::ostream& out) {
    out << "(set-option :unsat_core true)\n";
    display_declarations_smt(out);
    unsigned id = 0;
    for (auto& c : lra.constraints().active())
        display_constraint_smt(out, id++, c);
    out << "(check-sat)\n";
    out << "(get-unsat-core)\n";
    out << "(reset)\n";
    return out;
}


std::ostream& core::display_declarations_smt(std::ostream& out) const {
    for (unsigned v = 0; v < lra.column_count(); ++v) {
        if (is_monic_var(v)) {
            out << "(define-const x" << v << " ";
            out << (lra.var_is_int(v) ? "Int" : "Real");
            auto const& m = m_emons[v];
            out << " (*";
            for (auto w : m.vars())
                out << " x" << w;
            out << ")";
            out << "); " << val(v) << " = ";
            rational p(1);
            for (auto w : m.vars())
                p *= val(w);
            out << p;
            out << "\n";
        } 
        else {
            out << "(declare-const x" << v << " ";
            out << (lra.var_is_int(v) ? "Int" : "Real");
            out << "); " << val(v) << "\n";
        }
    }
    return out;
}

std::ostream& core::display_constraint_smt(std::ostream& out, unsigned id, lp::lar_base_constraint const& c) const {
    auto k = c.kind();
    auto rhs = c.rhs();
    auto lhs = c.coeffs();
    rational den = denominator(rhs);
    for (auto [coeff, v] : lhs) 
        den = lcm(den, denominator(coeff));
    rhs *= den;  

    auto value_of = [&](lp::lpvar v) {
        if (is_monic_var(v)) {
            auto& m = m_emons[v];
            rational p(1);
            for (auto w : m.vars())
                p *= val(w);
            return p;
        }
        return val(v);
    };

    switch (k) {
    case lp::lconstraint_kind::LE:
        out << "(assert (! (<= ";
        break;
    case lp::lconstraint_kind::GE:
        out << "(assert (! (>= ";
        break;
    case lp::lconstraint_kind::LT:
        out << "(assert (! (< ";
        break;
    case lp::lconstraint_kind::GT:
        out << "(assert (! (> ";
        break;
    case lp::lconstraint_kind::EQ:
        out << "(assert (! (= ";
        break;
    default:
        UNREACHABLE();  // unreachable
    }
    rational lhs_val(0);
    if (lhs.size() > 1)
        out << "(+";
    for (auto [coeff, v] : lhs) {
        auto c = coeff * den;
        if (c == 1)
            out << " x" << v;
        else
            out << " (* " << c << " x" << v << ")";
        lhs_val += value_of(v) * c;
    }
    if (lhs.size() > 1)
        out << ")";
    out << " " << rhs << ") :named a" << id << ")); ";
    bool evaluation = true;
    switch (k) {
        case lp::lconstraint_kind::LE:
            evaluation = lhs_val <= rhs;
            break;
        case lp::lconstraint_kind::GE:
            evaluation = lhs_val >= rhs;
            break;
        case lp::lconstraint_kind::LT:
            evaluation = lhs_val < rhs;
            break;
        case lp::lconstraint_kind::GT:
            evaluation = lhs_val > rhs;
            break;
        case lp::lconstraint_kind::EQ:
            evaluation = lhs_val == rhs;
            break;            
        default:
            UNREACHABLE();  // unreachable
    }
    out << (evaluation ? "true" : "false");
    out << "\n";
    return out;
}