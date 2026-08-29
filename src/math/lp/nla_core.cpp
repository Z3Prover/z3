 /*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    nla_core.cpp

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#include "util/uint_set.h"
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
#include "math/lp/nex.h"
#include "math/grobner/pdd_solver.h"
#include "math/dd/pdd_interval.h"
#include "math/dd/pdd_eval.h"

using namespace nla;

typedef lp::lar_term term;

core::core(lp::lar_solver& s, params_ref const& p, reslimit & lim) :
    m_evars(),
    lra(s),
    m_reslim(lim),
    m_params(p),
    m_tangents(this),
    m_basics(this),
    m_order(this),
    m_monotone(this),
    m_powers(*this),
    m_divisions(*this),
    m_intervals(this, lim),
    m_monomial_bounds(this),
    m_patcher(this),
    m_explanations(this),
    m_horner(this),
    m_grobner(this),
    m_emons(m_evars),
    m_use_nra_model(false),
    m_nra(s, m_nra_lim, *this, p),
    m_throttle(lra.trail(), 
	lra.settings().stats()) {
     m_nlsat_backoff.set_delay_bound(lp_settings().nlsat_delay());
     lra.m_find_monics_with_changed_bounds_func = [&](const indexed_uint_set& columns_with_changed_bounds) {
        for (lpvar j : columns_with_changed_bounds) {
            if (is_monic_var(j))
                m_monics_with_changed_bounds.insert(j);
            for (const auto & m: m_emons.get_use_list(j)) 
                m_monics_with_changed_bounds.insert(m.var());
        }
    };
}

void core::updt_params(params_ref const& p) {
    m_grobner.updt_params(p);
}
    
bool core::compare_holds(const rational& ls, llc cmp, const rational& rs) const {
    switch(cmp) {
    case llc::LE: return ls <= rs;
    case llc::LT: return ls < rs;
    case llc::GE: return ls >= rs;
    case llc::GT: return ls > rs;
    case llc::EQ: return ls == rs;
    case llc::NE: return ls != rs;
    };
        
    return false;
}

rational core::value(const lp::lar_term& r) const {
    rational ret(0);
    for (lp::lar_term::ival t : r) 
        ret += t.coeff() * val(t.j());
    return ret;
}

bool core::ineq_holds(const ineq& n) const {
    return compare_holds(value(n.term()), n.cmp(), n.rs());
}

bool core::lemma_holds(const lemma& l) const {
    for (const ineq &i : l.ineqs()) 
        if (ineq_holds(i))
            return true;
    return false;
}

lpvar core::map_to_root(lpvar j) const {
    return m_evars.find(j).var();
}
    
svector<lpvar> core::sorted_rvars(const factor& f) const {
    if (f.is_var()) {
        svector<lpvar> r; r.push_back(map_to_root(f.var()));
        return r;
    }
    return m_emons[f.var()].rvars();
}

// the value of the factor is equal to the value of the variable multiplied
// by the canonize_sign
bool core::canonize_sign(const factor& f) const {
    return f.sign() ^ (f.is_var()? canonize_sign(f.var()) : canonize_sign(m_emons[f.var()]));
}

bool core::canonize_sign(lpvar j) const {
    return m_evars.find(j).sign();        
}

bool core::canonize_sign_is_correct(const monic& m) const {
    bool r = false;
    for (lpvar j : m.vars()) {
        r ^= canonize_sign(j);
    }
    return r == m.rsign();
}

bool core::canonize_sign(const monic& m) const {
    SASSERT(canonize_sign_is_correct(m));
    return m.rsign();
}

bool core::canonize_sign(const factorization& f) const {
    bool r = false;
    for (const factor & a : f) 
        r ^= canonize_sign(a);
    return r;
}

void core::add_monic(lpvar v, unsigned sz, lpvar const* vs) {
    m_add_buffer.resize(sz);
    for (unsigned i = 0; i < sz; ++i) {
        m_add_buffer[i] = vs[i];
    }
    m_emons.add(v, m_add_buffer);
    m_monics_with_changed_bounds.insert(v);
}
    
void core::push() {
    TRACE(nla_solver_verbose, tout << "\n";);
    m_emons.push();
}

     
void core::pop(unsigned n) {
    TRACE(nla_solver_verbose, tout << "n = " << n << "\n";);
    m_emons.pop(n);
    SASSERT(elists_are_consistent(false));
}

rational core::product_value(const monic& m) const {
    rational r(1);
    for (auto j : m.vars()) {
        r *= lra.get_column_value(j).x;
    }
    return r;
}
    
// return true iff the monic value is equal to the product of the values of the factors
//                 or if the variable associated with the monomial is not relevant.
bool core::check_monic(const monic& m) const {    
#if 0
    // TODO test this
    if (!is_relevant(m.var()))
        return true;
#endif
    if (lra.column_is_int(m.var()) && !lra.get_column_value(m.var()).is_int())
        return true;
    
    bool ret = product_value(m) == lra.get_column_value(m.var()).x; 
    CTRACE(nla_solver_check_monic, !ret, print_monic(m, tout) << '\n';);
    return ret;
}
    

// the monics should be equal by modulo sign but this is not so in the model
void core::fill_explanation_and_lemma_sign(lemma_builder& lemma, const monic& a, const monic & b, rational const& sign) {
    SASSERT(sign == 1 || sign == -1);
    lemma &= a;
    lemma &= b;
    TRACE(nla_solver, tout << "used constraints: " << lemma;);
    SASSERT(lemma.num_ineqs() == 0);
    lemma |= ineq(term(rational(1), a.var(), -sign, b.var()), llc::EQ, 0);
}

// Replaces each variable index by the root in the tree and flips the sign if the var comes with a minus.
// Also sorts the result.
// 
svector<lpvar> core::reduce_monic_to_rooted(const svector<lpvar> & vars, rational & sign) const {
    svector<lpvar> ret;
    bool s = false;
    for (lpvar v : vars) {
        auto root = m_evars.find(v);
        s ^= root.sign();
        TRACE(nla_solver_eq,
              tout << pp(v) << " mapped to " << pp(root.var()) << "\n";);
        ret.push_back(root.var());
    }
    sign = rational(s? -1: 1);
    std::sort(ret.begin(), ret.end());
    return ret;
}


// Replaces definition m_v = v1* .. * vn by
// m_v = coeff * w1 * ... * wn, where w1, .., wn are canonical
// representatives, which are the roots of the equivalence tree, under current equations.
// 
monic_coeff core::canonize_monic(monic const& m) const {
    rational sign = rational(1);
    svector<lpvar> vars = reduce_monic_to_rooted(m.vars(), sign);
    return monic_coeff(vars, sign);
}

int core::vars_sign(const svector<lpvar>& v) {
    int sign = 1;
    for (lpvar j : v) {
        sign *= nla::rat_sign(val(j));
        if (sign == 0) 
            return 0;
    }
    return sign;
}
   
bool core::has_upper_bound(lpvar j) const {
    return lra.column_has_upper_bound(j);
} 

bool core::has_lower_bound(lpvar j) const {
    return lra.column_has_lower_bound(j);
} 
const rational& core::get_upper_bound(unsigned j) const {
    return lra.get_upper_bound(j).x;
}

const rational& core::get_lower_bound(unsigned j) const {
    return lra.get_lower_bound(j).x;
}    
    
bool core::zero_is_an_inner_point_of_bounds(lpvar j) const {
    if (has_upper_bound(j) && get_upper_bound(j) <= rational(0))            
        return false;
    if (has_lower_bound(j) && get_lower_bound(j) >= rational(0))            
        return false;
    return true;
}
    
int core::rat_sign(const monic& m) const {
    int sign = 1;
    for (lpvar j : m.vars()) {
        auto v = val(j);
        if (v.is_neg()) {
            sign = - sign;
            continue;
        }
        if (v.is_pos()) {
            continue;
        }
        sign = 0;
        break;
    }
    return sign;
}

// Returns true if the monic sign is incorrect
bool core::sign_contradiction(const monic& m) const {
    return  nla::rat_sign(var_val(m)) != rat_sign(m);
}

/*
  unsigned_vector eq_vars(lpvar j) const {
  TRACE(nla_solver_eq, tout << "j = " << pp(j) << "eqs = ";
  for(auto jj : m_evars.eq_vars(j)) tout << pp(jj) << " ";
  });
  return m_evars.eq_vars(j);
  }
*/

bool core::var_is_fixed_to_zero(lpvar j) const {
    return 
        lra.column_is_fixed(j) &&
        lra.get_lower_bound(j) == lp::zero_of_type<lp::impq>();
}
bool core::var_is_fixed_to_val(lpvar j, const rational& v) const {
    return 
        lra.column_is_fixed(j) &&
        lra.get_lower_bound(j) == lp::impq(v);
}

bool core::var_is_fixed(lpvar j) const {
    return lra.column_is_fixed(j);
}

bool core::var_is_free(lpvar j) const {
    return lra.column_is_free(j);
}
    
bool core::find_canonical_monic_of_vars(const svector<lpvar>& vars, lpvar & i) const {
    monic const* sv = m_emons.find_canonical(vars);
    return sv && (i = sv->var(), true);
}

bool core::is_canonical_monic(lpvar j) const {
    return m_emons.is_canonical_monic(j);
}

bool core::var_has_positive_lower_bound(lpvar j) const {
    return lra.column_has_lower_bound(j) && lra.get_lower_bound(j) > lp::zero_of_type<lp::impq>();
}

bool core::var_has_negative_upper_bound(lpvar j) const {
    return lra.column_has_upper_bound(j) && lra.get_upper_bound(j) < lp::zero_of_type<lp::impq>();
}
    
bool core::var_is_separated_from_zero(lpvar j) const {
    return
        var_has_negative_upper_bound(j) ||
        var_has_positive_lower_bound(j);
}
    

bool core::vars_are_equiv(lpvar a, lpvar b) const {
    SASSERT(abs(val(a)) == abs(val(b)));
    return m_evars.vars_are_equiv(a, b);
}
    
bool core::has_zero_factor(const factorization& factorization) const {
    for (factor f : factorization) {
        if (val(f).is_zero())
            return true;
    }
    return false;
}


template <typename T>
bool core::mon_has_zero(const T& product) const {
    for (lpvar j: product) {
        if (val(j).is_zero())
            return true;
    }
    return false;
}

template bool core::mon_has_zero<unsigned_vector>(const unsigned_vector& product) const;


lp::lp_settings& core::lp_settings() {
    return lra.settings();
}
const lp::lp_settings& core::lp_settings() const {
    return lra.settings();
}
    
unsigned core::random() { return lp_settings().random_next(); }
    

void core::clear() {
    m_lemmas.clear();
    m_literals.clear();
    m_fixed_equalities.clear();
    m_equalities.clear();
    m_conflicts = 0;
    m_check_feasible = false;
}
    
void core::init_search() {
    TRACE(nla_solver_mons, tout << "init\n";);
    SASSERT(m_emons.invariant());
    clear();
    m_explanations.init_vars_equivalence();
    SASSERT(m_emons.invariant());
    SASSERT(elists_are_consistent(false));
}

void core::insert_to_refine(lpvar j) {
    TRACE(lar_solver, tout << "j=" << j << '\n';);
    m_to_refine.insert(j);
}

void core::erase_from_to_refine(lpvar j) {
    TRACE(lar_solver, tout << "j=" << j << '\n';);
    if (m_to_refine.contains(j))
        m_to_refine.remove(j);
}


void core::init_to_refine() {
    TRACE(nla_solver_details, tout << "emons:" << pp_emons(*this, m_emons););
    // check_monic() compares only the rational parts of the column values, so
    // m_to_refine has to be calibrated against a model without infinitesimal
    // (delta) components. Otherwise a monomial whose factors still carry
    // non-zero delta parts looks consistent here, while the model handed to the
    // theory solver - where delta is instantiated by a positive rational -
    // violates it. optimize_nl_bounds() re-solves the LP and re-introduces
    // delta components, so they are dropped here rather than only on entry to
    // check().
    if (lra.is_feasible())
        lra.get_rid_of_inf_eps();
    m_to_refine.reset();
    unsigned r = random(), sz = m_emons.number_of_monics();
    for (unsigned k = 0; k < sz; ++k) {
        auto const & m = *(m_emons.begin() + (k + r)% sz);
        if (!check_monic(m)) 
            insert_to_refine(m.var());
    }
    
    TRACE(nla_solver, 
          tout << m_to_refine.size() << " mons to refine:\n";
          for (lpvar v : m_to_refine) tout << pp_mon(*this, m_emons[v]) << ":error = " <<
                                          (val(v) - mul_val(m_emons[v])).get_double() << "\n";);
}
        
std::unordered_set<lpvar> core::collect_vars(const lemma& l) const {
    std::unordered_set<lpvar> vars;
    auto insert_j = [&](lpvar j) { 
        vars.insert(j);
        if (is_monic_var(j)) {
            for (lpvar k : m_emons[j].vars())
                vars.insert(k);
        }
    };
    
    for (const auto& i : l.ineqs()) {
        for (lp::lar_term::ival p : i.term()) {                
            insert_j(p.j());
        }
    }
    for (auto p : l.expl()) {
        const auto& c = lra.constraints()[p.ci()];
        for (const auto& r : c.coeffs()) {
            insert_j(r.second);
        }
    }
    return vars;
}

// divides bc by c, so bc = b*c
bool core::divide(const monic& bc, const factor& c, factor & b) const {
    svector<lpvar> c_rvars = sorted_rvars(c);
    TRACE(nla_solver_div, tout << "c_rvars = "; print_product(c_rvars, tout); tout << "\nbc_rvars = "; print_product(bc.rvars(), tout););
    if (!lp::is_proper_factor(c_rvars, bc.rvars()))
        return false;
            
    auto b_rvars = lp::vector_div(bc.rvars(), c_rvars);
    TRACE(nla_solver_div, tout << "b_rvars = "; print_product(b_rvars, tout););
    SASSERT(b_rvars.size() > 0);
    if (b_rvars.size() == 1) {
        b = factor(b_rvars[0], factor_type::VAR);
    } else {
        monic const* sv = m_emons.find_canonical(b_rvars);
        if (sv == nullptr) {
            TRACE(nla_solver_div, tout << "not in rooted";);
            return false;
        }
        b = factor(sv->var(), factor_type::MON);
    }
    SASSERT(!b.sign());
    // We have bc = canonize_sign(bc)*bc.rvars() = canonize_sign(b)*b.rvars()*canonize_sign(c)*c.rvars().
    // Dividing by bc.rvars() we get canonize_sign(bc) = canonize_sign(b)*canonize_sign(c)
    // Currently, canonize_sign(b) is 1, we might need to adjust it
    b.sign() = canonize_sign(b) ^ canonize_sign(c) ^ canonize_sign(bc); 
    TRACE(nla_solver, tout << "success div:" << pp(b) << "\n";);
    return true;
}


void core::negate_factor_equality(lemma_builder& lemma, const factor& c,
                                  const factor& d) {
    if (c == d)
        return;
    lpvar i = var(c);
    lpvar j = var(d);
    auto iv = val(i), jv = val(j);
    SASSERT(abs(iv) == abs(jv));
    lemma |= ineq(term(i, rational(iv == jv ? -1 : 1), j), llc::NE, 0);    
}
    
void core::negate_factor_relation(lemma_builder& lemma, const rational& a_sign, const factor& a, const rational& b_sign, const factor& b) {
    rational a_fs = sign_to_rat(canonize_sign(a));
    rational b_fs = sign_to_rat(canonize_sign(b));
    llc cmp = a_sign*val(a) < b_sign*val(b)? llc::GE : llc::LE;
    lemma |= ineq(term(a_fs*a_sign, var(a), - b_fs*b_sign, var(b)), cmp, 0);
}

std::ostream& core::print_lemma(const lemma& l, std::ostream& out) const {
    static int n = 0;
    out << "lemma:" << ++n << " ";    
    print_ineqs(l, out);
    print_explanation(l.expl(), out);        
    for (lpvar j : collect_vars(l)) {
        print_var(j, out);
    }
    return out;
}
    

void core::trace_print_ol(const monic& ac,
                          const factor& a,
                          const factor& c,
                          const monic& bc,
                          const factor& b,
                          std::ostream& out) {
    out << "ac = " << pp_mon(*this, ac) << "\n";
    out << "bc = " << pp_mon(*this, bc) << "\n";
    out << "a = ";
    print_factor_with_vars(a, out);
    out << ", \nb = ";
    print_factor_with_vars(b, out);
    out << "\nc = ";
    print_factor_with_vars(c, out);
}
    
void core::maybe_add_a_factor(lpvar i,
                              const factor& c,
                              std::unordered_set<lpvar>& found_vars,
                              std::unordered_set<unsigned>& found_rm,
                              vector<factor> & r) const {
    SASSERT(abs(val(i)) == abs(val(c)));
    if (!is_monic_var(i)) {
        i = m_evars.find(i).var();
        if (try_insert(i, found_vars)) {
            r.push_back(factor(i, factor_type::VAR));
        }
    } else {
        if (try_insert(i, found_rm)) {
            r.push_back(factor(i, factor_type::MON));
            TRACE(nla_solver, tout << "inserting factor = "; print_factor_with_vars(factor(i, factor_type::MON), tout); );
        }
    }
}
    

// Returns rooted monics by arity
std::unordered_map<unsigned, unsigned_vector> core::get_rm_by_arity() {
    std::unordered_map<unsigned, unsigned_vector> m;
    for (auto const& mon : m_emons) {
        unsigned arity = mon.vars().size();
        auto it = m.find(arity);
        if (it == m.end()) {
            it = m.insert(it, std::make_pair(arity, unsigned_vector()));
        }
        it->second.push_back(mon.var());
    }
    return m;
}

bool core::rm_check(const monic& rm) const {
    return check_monic(m_emons[rm.var()]);
}

bool core::has_relevant_monomial() const {
    return any_of(emons(), [&](auto const& m) { return is_relevant(m.var()); });
}
    
bool core::find_bfc_to_refine_on_monic(const monic& m, factorization & bf) {
    for (auto f : factorization_factory_imp(m, *this)) {
        if (f.size() == 2) {
            auto a = f[0];
            auto b = f[1];
            if (var_val(m) != val(a) * val(b)) {
                bf = f;
                TRACE(nla_solver, tout << "found bf";
                      tout << ":m:" << pp_mon_with_vars(*this, m) << "\n";
                      tout << "bf:"; print_bfc(bf, tout););
                      
                return true;
            }
        }
    }
    return false;
}

// finds a monic to refine with its binary factorization
bool core::find_bfc_to_refine(const monic* & m, factorization & bf){
    m = nullptr;
    unsigned r = random(), sz = m_to_refine.size();
    for (unsigned k = 0; k < sz; ++k) {
        lpvar i = m_to_refine[(k + r) % sz];
        m = &m_emons[i];
        SASSERT (!check_monic(*m));
        if (has_real(m))
            continue;
        if (m->size() == 2) {
            bf.set_mon(m);
            bf.push_back(factor(m->vars()[0], factor_type::VAR));
            bf.push_back(factor(m->vars()[1], factor_type::VAR));
            return true;
        }
                
        if (find_bfc_to_refine_on_monic(*m, bf)) {
            TRACE(nla_solver,
                  tout << "bf = "; print_factorization(bf, tout);
                  tout << "\nval(*m) = " << var_val(*m) << ", should be = (val(bf[0])=" << val(bf[0]) << ")*(val(bf[1]) = " << val(bf[1]) << ") = " << val(bf[0])*val(bf[1]) << "\n";);
            return true;
        } 
    }
    return false;
}

rational core::val(const factorization& f) const {
    rational r(1);
    for (const factor &p : f) {
        r *= val(p);
    }
    return r;
}

lemma_builder::lemma_builder(core& c, const char* name):name(name), c(c) {
    c.m_lemmas.push_back(lemma());
}

lemma_builder& lemma_builder::operator|=(ineq const& ineq) {
    if (!c.m_explanations.explain_ineq(*this, ineq.term(), ineq.cmp(), ineq.rs())) {
        CTRACE(nla_solver, c.ineq_holds(ineq), c.print_ineq(ineq, tout) << "\n";);
        SASSERT(c.m_use_nra_model || !c.ineq_holds(ineq));
        current().push_back(ineq);
    }
    return *this;
}
    

lemma_builder::~lemma_builder() {
    static int i = 0;
    (void)i;
    (void)name;
    // code for checking lemma can be added here
    if (current().is_conflict()) {
        c.m_conflicts++;
    }
    IF_VERBOSE(4, verbose_stream() << name << " " << c.lra.get_scope_level() << "\n");
    IF_VERBOSE(4, verbose_stream() << *this << "\n");
    TRACE(nla_solver, tout << name << " " << (++i) << "\n" << *this; );
}

lemma& lemma_builder::current() {
    return c.m_lemmas.back();
}
const lemma& lemma_builder::current() const {
    return c.m_lemmas.back();
}
lemma_builder& lemma_builder::operator&=(lp::explanation const& e) {
    expl().add_expl(e);
    return *this;
}

lemma_builder& lemma_builder::operator&=(const monic& m) {
    for (lpvar j : m.vars())
        *this &= j;
    return *this;
}

lemma_builder& lemma_builder::operator&=(const factor& f) {
    if (f.type() == factor_type::VAR) 
        *this &= f.var();
    else 
        *this &= c.m_emons[f.var()];
    return *this;
}

lemma_builder& lemma_builder::operator&=(const factorization& f) {
    if (f.is_mon())
        return *this;
    for (const auto& fc : f) {
        *this &= fc;
    }
    return *this;
}

lemma_builder& lemma_builder::operator&=(lpvar j) {
    c.m_evars.explain(j, expl());
    return *this;
}

lemma_builder& lemma_builder::explain_fixed(lpvar j) {
    SASSERT(c.var_is_fixed(j));
    explain_existing_lower_bound(j);
    explain_existing_upper_bound(j);
    return *this;
}

lemma_builder& lemma_builder::explain_equiv(lpvar a, lpvar b) {
    SASSERT(abs(c.val(a)) == abs(c.val(b)));
    if (c.vars_are_equiv(a, b)) {
        *this &= a;
        *this &= b;
    } else {
        explain_fixed(a);
        explain_fixed(b);
    }
    return *this;
}

lemma_builder& lemma_builder::explain_var_separated_from_zero(lpvar j) {
    SASSERT(c.var_is_separated_from_zero(j));
    if (c.lra.column_has_upper_bound(j) && 
        (c.lra.get_upper_bound(j)< lp::zero_of_type<lp::impq>())) 
        explain_existing_upper_bound(j);
    else 
        explain_existing_lower_bound(j);
    return *this;
}

lemma_builder& lemma_builder::explain_existing_lower_bound(lpvar j) {
    SASSERT(c.has_lower_bound(j));
    lp::explanation ex;
    c.lra.push_explanation(c.lra.get_column_lower_bound_witness(j), ex);
    *this &= ex;
    TRACE(nla_solver, tout << j << ": " << *this << "\n";);
    return *this;
}

lemma_builder& lemma_builder::explain_existing_upper_bound(lpvar j) {
    SASSERT(c.has_upper_bound(j));
    lp::explanation ex;
    c.lra.push_explanation(c.lra.get_column_upper_bound_witness(j), ex);
    *this &= ex;
    return *this;
}
    
std::ostream& lemma_builder::display(std::ostream & out) const {
    auto const& lemma = current();

    for (auto p : lemma.expl()) {
        out << "(" << p.ci() << ") ";
        c.lra.constraints().display(out, [this](lpvar j) { return c.var_str(j);}, p.ci());
    }
    out << " ==> ";
    if (lemma.ineqs().empty()) {
        out << "false";
    }
    else {
        bool first = true;
        for (auto & in : lemma.ineqs()) {
            if (first) first = false; else out << " or ";
            c.print_ineq(in, out);
        }
    }
    out << "\n";
    for (lpvar j : c.collect_vars(lemma)) {
        c.print_var(j, out);
    }
    return out;
}
    
void core::negate_relation(lemma_builder& lemma, unsigned j, const rational& a) {
    SASSERT(val(j) != a);
    lemma |= ineq(j, val(j) < a ? llc::GE : llc::LE, a);   
}

bool core::conflict_found() const {
    return any_of(m_lemmas, [&](const auto& l) { return l.is_conflict(); });
}

bool core::done() const {
    return m_lemmas.size() >= 10 || 
        conflict_found() || 
        lp_settings().get_cancel_flag();
}

bool core::elist_is_consistent(const std::unordered_set<lpvar> & list) const {
    bool first = true;
    bool p;
    for (lpvar j : list) {
        if (first) {
            p = check_monic(m_emons[j]);
            first = false;
        } else 
            if (check_monic(m_emons[j]) != p)
                return false;
    }
    return true;
}

bool core::elists_are_consistent(bool check_in_model) const {
    std::unordered_map<unsigned_vector, std::unordered_set<lpvar>, hash_svector> lists;
    if (!m_emons.elists_are_consistent(lists))
        return false;

    if (!check_in_model)
        return true;
    for (const auto & p : lists) {
        if (! elist_is_consistent(p.second))
            return false;
    }
    return true;
}

bool core::var_is_big(lpvar j) const {
    return !var_is_int(j) && val(j).is_big();
}

bool core::has_big_num(const monic& m) const {
    if (var_is_big(var(m)))
        return true;
    for (lpvar j : m.vars())
        if (var_is_big(j))
            return true;
    return false;
}

bool core::has_real(const factorization& f) const {
    for (const factor& fc: f) {
        lpvar j = var(fc);
        if (!var_is_int(j))
            return true;
    }
    return false;
}

bool core::has_real(const monic& m) const {
    for (lpvar j : m.vars())
        if (!var_is_int(j))
            return true;
    return false;
}

/**
 * Cycle through different end-game solvers weighted by probability.
 */
void core::check_weighted(unsigned sz, std::pair<unsigned, std::function<void(void)>>* checks) {
    unsigned bound = 0;
    for (unsigned i = 0; i < sz; ++i) 
        bound += checks[i].first;
    uint_set seen;
    while (bound > 0 && !done() && m_lemmas.empty()) {
        unsigned n = random() % bound;
        for (unsigned i = 0; i < sz; ++i) {
            if (seen.contains(i))
                continue;
            if (n < checks[i].first) {
                seen.insert(i);
                checks[i].second();
                bound -= checks[i].first;
                break;
            }
            n -= checks[i].first;
        }
    }
}

lbool core::check_power(lpvar r, lpvar x, lpvar y) {
    clear();
    // powers::check and lemma validation read only the rational parts of the
    // column values; drop infinitesimals first, as init_to_refine does for check().
    if (lra.is_feasible())
        lra.get_rid_of_inf_eps();
    return m_powers.check(r, x, y, m_lemmas);
}

void core::check_bounded_divisions() {
    clear();
    m_divisions.check_bounded_divisions();
}
// looking for a free variable inside of a monic to split
void core::add_bounds() {
    unsigned r = random(), sz = m_to_refine.size();
    for (unsigned k = 0; k < sz; ++k) {
        lpvar i = m_to_refine[(k + r) % sz];
        auto const& m = m_emons[i];
        for (lpvar j : m.vars()) {
            if (!var_is_free(j))
                continue;
	    if (m.is_bound_propagated())
                continue;
	    m_emons.set_bound_propagated(m);
            // split the free variable (j <= 0, or j > 0), and return
            m_literals.push_back(ineq(j, lp::lconstraint_kind::EQ, rational::zero()));
            TRACE(nla_solver, print_ineq(m_literals.back(), tout) << "\n");                  
            ++lp_settings().stats().m_nla_add_bounds;
            return;
        }
    }    
}

lbool core::check(unsigned level) {
    lp_settings().stats().m_nla_calls++;
    TRACE(nla_solver, tout << "calls = " << lp_settings().stats().m_nla_calls << "\n";);
    lra.get_rid_of_inf_eps();
    if (!(lra.get_status() == lp::lp_status::OPTIMAL || 
          lra.get_status() == lp::lp_status::FEASIBLE)) {
        TRACE(nla_solver, tout << "unknown because of the lra.m_status = " << lra.get_status() << "\n";);
        return l_undef;
    }

    init_to_refine();
    m_patcher.patch_monomials();
    set_use_nra_model(false);
    if (m_to_refine.empty()) {
        m_squeeze_schedule.on_nothing_to_refine();
        return l_true;
    }
    init_search();
    m_nla_satisfied = false;

    lbool ret = l_undef;
    bool run_grobner = need_run_grobner();
    bool run_horner = need_run_horner();
    bool run_bounds = params().arith_nl_branching();

    auto no_effect = [&]() { return ret == l_undef && !done() && !m_nla_satisfied && m_lemmas.empty() && m_literals.empty() && !m_check_feasible; };
    
    if (no_effect())
        m_monomial_bounds.generate_lemmas();

    if (no_effect() && refine_pseudo_linear())
        return l_false;

    // Squeeze monomial bounds eagerly while it helps, otherwise on the horner
    // cadence; disable after too many fruitless calls.
    bool squeeze_cadence = lp_settings().stats().m_nla_calls % params().arith_nl_horner_frequency() == 0;
    if (no_effect() && m_squeeze_schedule.enabled() && (run_horner || run_grobner) && (m_squeeze_schedule.eager() || squeeze_cadence)) {
        m_squeeze_schedule.on_squeeze(m_monomial_bounds.optimize_nl_bounds());
        if (m_to_refine.empty()) {
            m_squeeze_schedule.on_nothing_to_refine();
            return l_true;
        }
    }

    {
        std::function<void(void)> check1 = [&]() { if (no_effect() && run_horner) m_horner.horner_lemmas(); };
        std::function<void(void)> check2 = [&]() { if (no_effect() && run_grobner) m_grobner(); };
        std::function<void(void)> check3 = [&]() { if (no_effect() && run_bounds) add_bounds(); };

        std::pair<unsigned, std::function<void(void)>> checks[] =
            { {1, check1},
              {1, check2},
              {1, check3} };
        check_weighted(3, checks);

        if (lp_settings().get_cancel_flag())
            return l_undef;
        if (!m_lemmas.empty() || !m_literals.empty() || m_check_feasible)
            return l_false;
        // bound optimization proved all monomials consistent: goal satisfied.
        if (m_nla_satisfied)
            return l_true;
    }

    if (no_effect() && params().arith_nl_nra_check_assignment() && m_check_assignment_fail_cnt < params().arith_nl_nra_check_assignment_max_fail()) {
        scoped_limits sl(m_reslim);
        sl.push_child(&m_nra_lim);
        ret = m_nra.check_assignment();
        if (ret != l_true)
            ++m_check_assignment_fail_cnt;
    }

    if (no_effect() && should_run_bounded_nlsat())
        ret = bounded_nlsat();
                
    if (no_effect()) 
        m_basics.basic_lemma(true); 

    if (no_effect()) 
        m_basics.basic_lemma(false);

    if (no_effect()) 
        m_divisions.check();


    if (no_effect()) {
        std::function<void(void)> check1 = [&]() { m_order.order_lemma();
        };
        std::function<void(void)> check2 = [&]() { m_monotone.monotonicity_lemma();
        };
        std::function<void(void)> check3 = [&]() { m_tangents.tangent_lemma();
        };
        
        std::pair<unsigned, std::function<void(void)>> checks[] = 
            { { 6, check1 }, 
              { 2, check2 }, 
              { 1, check3 }};
        check_weighted(3, checks);

        unsigned num_calls = lp_settings().stats().m_nla_calls;
        if (!conflict_found() && params().arith_nl_nra() && num_calls % 50 == 0 && num_calls > 500)
            ret = bounded_nlsat();
    }

    if (no_effect() && params().arith_nl_nra() && level >= 2) {
        scoped_limits sl(m_reslim);
        sl.push_child(&m_nra_lim);
        params_ref p;
        p.set_uint("max_conflicts", lp_settings().m_max_conflicts);
        m_nra.updt_params(p);
        ret = m_nra.check();
        lp_settings().stats().m_nra_calls++;
    }
    
    if (ret == l_undef && !no_effect() && m_reslim.inc()) 
        ret = l_false;

    lp_settings().stats().m_nla_lemmas += m_lemmas.size();
    
    TRACE(nla_solver, tout << "ret = " << ret << ", lemmas count = " << m_lemmas.size() << "\n";);
    IF_VERBOSE(5, if(ret == l_undef) {verbose_stream() << "Monomials\n"; print_monics(verbose_stream());});
    CTRACE(nla_solver, ret == l_undef, tout << "Monomials\n"; print_monics(tout););
    CTRACE(nla_solver, ret == l_undef, display_smt(tout););
    // if (ret == l_undef) IF_VERBOSE(0, display_smt(verbose_stream()));
    return ret;
}

bool core::should_run_bounded_nlsat() {
    return params().arith_nl_nra() && m_nlsat_backoff.should_run();
}

// One budget-limited run of the nlsat solver on the full set of nonlinear
// constraints. nlsat is complete for nonlinear real arithmetic but can be
// arbitrarily expensive, so the run is capped by a conflict and an rlimit
// budget. l_true: nlsat found a model, the state is satisfiable; l_false:
// nlsat proved infeasibility and produced a lemma; l_undef: nlsat exhausted
// its budget without an answer.
lbool core::bounded_nlsat() {
    const unsigned max_conflicts_budget = 100;
    const unsigned rlimit_budget = 100000;
    params_ref p;
    lbool ret;
    p.set_uint("max_conflicts", max_conflicts_budget);
    m_nra.updt_params(p);
    uint64_t rlimit_consumed = 0;
    {
        scoped_limits sl(m_reslim);
        sl.push_child(&m_nra_lim); // zeroes m_nra_lim's counter
        scoped_rlimit sr(m_nra_lim, rlimit_budget);
        ret = m_nra.check();
        // must be read here: pop_child transfers the child's count to the
        // parent and zeroes it, so outside this block the counter is 0 again
        rlimit_consumed = m_nra_lim.count();
    }
    p.set_uint("max_conflicts", lp_settings().m_max_conflicts);
    m_nra.updt_params(p);
    lp_settings().stats().m_nra_calls++;

    // A conflict, or a run that consumed almost none of its budget,
    // re-engages the backoff scheduler; only an expensive run that gave up
    // backs off. A search that needs a cheap satisfiability certificate
    // every round to advance (e.g. between quantifier instantiation rounds)
    // must not be starved of them.
    bool cheap = rlimit_consumed < rlimit_budget / 10;
    bool re_engage = ret == l_false || cheap;
    m_nlsat_backoff.update(re_engage);

    IF_VERBOSE(3, verbose_stream() << "(nla-bounded-nlsat :result " << ret
               << " :rlimit-consumed " << rlimit_consumed
               << " :re-engage " << (re_engage ? "true" : "false") << ")\n");

    if (ret == l_true)
        clear();
    return ret;
}

bool core::no_lemmas_hold() const {
    for (auto & l : m_lemmas) {
        if (lemma_holds(l)) {
            TRACE(nla_solver, print_lemma(l, tout););
            return false;
        }
    }
    return true;
}
    
lbool core::test_check() {
    lra.set_status(lp::lp_status::OPTIMAL);
    return check(2);
}

std::unordered_set<lpvar> core::get_vars_of_expr_with_opening_terms(const nex *e ) {
    auto ret = get_vars_of_expr(e);
    auto & ls = lra;
    svector<lpvar> added;
    for (auto j : ret) {
        added.push_back(j);
    }
    for (unsigned i = 0; i < added.size(); ++i) {
        lpvar j = added[i];
        if (ls.column_has_term(j)) {
            const auto& t = lra.get_term(j);
            for (auto p : t) {
                if (ret.find(p.j()) == ret.end()) {
                    added.push_back(p.j());
                    ret.insert(p.j());
                }
            }
        }
    }
    return ret;
}

bool core::is_nl_var(lpvar j) const {
    return is_monic_var(j) || m_emons.is_used_in_monic(j);
}

unsigned core::get_var_weight(lpvar j) const {
    unsigned k = 0;
    switch (lra.get_column_type(j)) {

    case lp::column_type::fixed:
        k = 0;
        break;
    case lp::column_type::boxed:
        k = 3;
        break;
    case lp::column_type::lower_bound:
    case lp::column_type::upper_bound:
        k = 6;
        break;
    case lp::column_type::free_column:
        k = 9;
        break;
    }
    if (is_monic_var(j)) {
        k++;
        if (m_to_refine.contains(j))
            k++;
    }
    return k;
}


void core::set_active_vars_weights(nex_creator& nc) {
    nc.set_number_of_vars(lra.column_count());
    for (lpvar j : active_var_set()) 
        nc.set_var_weight(j, get_var_weight(j));
}

bool core::influences_nl_var(lpvar j) const {
    if (is_nl_var(j))
        return true;
    for (const auto & c : lra.A_r().m_columns[j]) {
        lpvar basic_in_row = lra.r_basis()[c.var()];
        if (is_nl_var(basic_in_row))
            return true;        
    }
    return false;
}

void core::set_use_nra_model(bool m) {
    if (m != m_use_nra_model) {
        trail().push(value_trail(m_use_nra_model));
        m_use_nra_model = m;        
    }
}

    
bool core::propagate() {
    clear();
	bool propagated = false;
    if (m_monomial_bounds.tighten_lp_bounds())
		propagated = true;
    if (m_monomial_bounds.propagate_changed_bounds())
        propagated = true;
    if (m_monomial_bounds.propagate_violated_linear_monomials())
        propagated = true;
    m_monics_with_changed_bounds.reset();
    if (propagated)
        m_check_feasible = true;
    return propagated;
}

bool core::incremental_propagate() {
    bool propagated = false;
    clear();
    if (m_monomial_bounds.propagate_changed_bounds())
        propagated = true;
    m_monics_with_changed_bounds.reset();
    if (propagated)
        m_check_feasible = true;
    return propagated;    
}

void core::simplify() {
    // in-processing simplifiation can go here, such as bounds improvements.
}

bool core::is_pseudo_linear(monic const& m) const {
    bool has_unbounded = false;
    for (auto v : m.vars()) {
        if (lra.column_is_bounded(v) && lra.var_is_int(v)) {
            auto lb = lra.get_lower_bound(v);
            auto ub = lra.get_upper_bound(v);
            if (ub - lb <= rational(4))
                continue;
        }
        if (has_unbounded)
            return false;
        has_unbounded = true;
    }
    return true;
}

bool core::refine_pseudo_linear() {
    if (!params().arith_nl_reduce_pseudo_linear())
        return false;
    for (lpvar j : m_to_refine) {
        if (is_pseudo_linear(m_emons[j])) {
            refine_pseudo_linear(m_emons[j]);
            return true;
        }
    }
    return false;
}

void core::refine_pseudo_linear(monic const& m) {
    lemma_builder lemma(*this, "nla-pseudo-linear");
    lpvar nlvar = null_lpvar;
    rational prod(1);
    for (unsigned i = 0; i < m.vars().size(); ++i) {
        auto v = m.vars()[i];
        if (i == m.vars().size() - 1 && nlvar == null_lpvar) {
            nlvar = v;
            break;
        }
        if (lra.column_is_bounded(v) && lra.var_is_int(v)) {
            auto lb = lra.get_lower_bound(v);
            auto ub = lra.get_upper_bound(v);
            if (ub - lb <= rational(4)) {
                lemma |= ineq(v, llc::NE, val(v));
                prod *= val(v);
                continue;
            }
        }
        SASSERT(nlvar == null_lpvar);
        nlvar = v;
    }
    SASSERT(nlvar != null_lpvar);
    lemma |= ineq(lp::lar_term(m.var(), rational(-prod), nlvar), llc::EQ, rational(0));
}
