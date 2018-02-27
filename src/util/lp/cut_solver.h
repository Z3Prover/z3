/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#pragma once
#include "util/vector.h"
#include "util/trace.h"
#include "util/lp/lp_settings.h"
#include "util/lp/column_namer.h"
#include "util/lp/integer_domain.h"
#include "util/lp/lp_utils.h"
#include <functional>
#include "util/lp/int_set.h"
#include "util/lp/linear_combination_iterator_on_std_vector.h"
#include "util/lp/stacked_vector.h"

namespace lp {
enum class lbool { l_false, l_true, l_undef };
inline std::string lbool_to_string(lbool l) {
    switch(l) {
    case lbool::l_true: return std::string("true");
    case lbool::l_false: return std::string("false");
    case lbool::l_undef: return std::string("undef");
    default:
        return std::string("what is it?");
    }
}

class cut_solver;

struct monomial {
    mpq           m_coeff; // the coefficient of the monomial
    var_index     m_var; // the variable index
public:
    monomial(const mpq& coeff, var_index var) : m_coeff(coeff), m_var(var) {}
    // copy constructor
    monomial(const monomial& m) : monomial(m.coeff(), m.var()) {}
    monomial(var_index var) : monomial(one_of_type<mpq>(), var) {}
    const mpq & coeff() const { return m_coeff; }
    mpq & coeff() { return m_coeff; }
    var_index var() const { return m_var; }
    std::pair<mpq, var_index> to_pair() const { return std::make_pair(coeff(), var());}
};

struct polynomial {
    static mpq m_local_zero;
    // the polynomial evaluates to m_coeffs + m_a
    vector<monomial>        m_coeffs;
    mpq                     m_a; // the free coefficient
    polynomial(const vector<monomial>& p, const mpq & a) : m_coeffs(p), m_a(a) {}
    polynomial(const vector<monomial>& p) : polynomial(p, zero_of_type<mpq>()) {}
    polynomial(): m_a(zero_of_type<mpq>()) {}
    polynomial(const polynomial & p) : m_coeffs(p.m_coeffs), m_a(p.m_a) {} 
            
    const mpq & coeff(var_index j) const {
        for (const auto & t : m_coeffs) {
            if (j == t.var()) {
                return t.coeff();
            }
        }
        return m_local_zero;
    }

    polynomial &  operator+=(const polynomial & p) {
        m_a += p.m_a;
        for (const auto & t: p.m_coeffs)
            *this += monomial(t.coeff(), t.var());
        return *this;
    }

    void add(const mpq & c, const polynomial &p) {
        m_a += p.m_a * c;
            
        for (const auto & t: p.m_coeffs)
            *this += monomial(c * t.coeff(), t.var());
    }
        
    void clear() {
        m_coeffs.clear();
        m_a = zero_of_type<mpq>();
    }
        
    bool is_empty() const { return m_coeffs.size() == 0 && numeric_traits<mpq>::is_zero(m_a); }

    unsigned number_of_monomials() const { return m_coeffs.size();}

    void add(const monomial &m ){
        if (is_zero(m.coeff())) return;
        for (unsigned k = 0; k < m_coeffs.size(); k++) {
            auto & l = m_coeffs[k];
            if (m.var() == l.var()) {
                l.coeff() += m.coeff();
                if (l.coeff() == 0)
                    m_coeffs.erase(m_coeffs.begin() + k);
                return;
            }
        }
        m_coeffs.push_back(m);
        lp_assert(is_correct());
    }
        
    polynomial & operator+=(const monomial &m ){
        add(m);
        return *this;
    }

    polynomial & operator+=(const mpq &c ){
        m_a += c;
        return *this;
    }

        
    bool is_correct() const {
        std::unordered_set<var_index> s;
        for (auto & l : m_coeffs) {
            if (l.coeff() == 0)
                return false;
            s.insert(l.var());
        }
        return m_coeffs.size() == s.size();
    }

    bool var_coeff_is_unit(unsigned j) const {
        const mpq & a = coeff(j);
        return a == 1 || a == -1;
    }
    const vector<monomial> & coeffs() const { return m_coeffs; }
};

class constraint; // forward definition
struct constraint_hash {
    size_t operator() (const constraint* c) const;
};

struct constraint_equal {
    bool operator() (const constraint * a, const constraint * b) const;
};

class constraint { // we only have less or equal for the inequality sign, which is enough for integral variables
    int                                              m_id;  
    bool                                             m_is_ineq;
    polynomial                                       m_poly;
    mpq                                              m_d; // the divider for the case of a divisibility constraint
    const svector<constraint_index>                  m_assert_origins; // these indices come from the client
    bool                                             m_active;
    std::unordered_set<const constraint*>            m_predecessors;  // used in tight_constraints and lemmas
public :
    void set_active_flag() {m_active = true;}
    void remove_active_flag() { m_active = false; }
    bool is_active() const { return m_active; }
    unsigned id() const { return m_id; }
    const polynomial & poly() const { return m_poly; }
    polynomial & poly() { return m_poly; }
    const svector<constraint_index> & assert_origins() const { return m_assert_origins;}
    bool is_lemma() const { return !is_assert(); }
    bool is_assert() const { return m_predecessors.size() == 0; }
    bool is_ineq() const { return m_is_ineq; }
    const mpq & divider() const { return m_d; }
public :
    static constraint * make_ineq_assert(
        int id,
        const vector<monomial>& term,
        const mpq& a,
        const svector<constraint_index> & origins) {
        return new constraint(id, origins, polynomial(term, a), true);
    }

    static constraint * make_ineq_constraint(
        int id,
        const polynomial & p,
        std::unordered_set<const constraint*>  predecessors_set) {
        auto c = new constraint(id, p, true);
        c->predecessors() = predecessors_set;
        return c;
    }
    
    static constraint * make_ineq_lemma(unsigned id, const polynomial &p) {
        return new constraint(id, p, true);
    }

    // static constraint make_div_lemma(unsigned id, const polynomial &p, const mpq & div) {
    //     lp_assert(false); // not implemented
    //     // constraint * c = new constraint(id, p, true);
    //     // c->m_d = div;
    //     return nullptr;
    // }
private:
    constraint(
        unsigned id,
        const svector<constraint_index> & assert_origins,
        const polynomial & p,
        bool is_ineq):
        m_id(id),
        m_is_ineq(is_ineq),
        m_poly(p),
        m_assert_origins(assert_origins),
        m_active(false) { // creates an assert
    }


    
    constraint(
        unsigned id,
        const polynomial & p,
        bool is_ineq):
        m_id(id),
        m_is_ineq(is_ineq),
        m_poly(p),
        m_active(false) { // creates a lemma
    }
        
public:
    constraint() {}

    const mpq & coeff(var_index j) const {
        return m_poly.coeff(j);
    }
    const vector<monomial>& coeffs() const { return m_poly.m_coeffs;}

    bool is_tight(unsigned j) const {
        const mpq & a = m_poly.coeff(j);
        return a == 1 || a == -1;
    }
    const std::unordered_set<const constraint*>& predecessors() const { return m_predecessors; }
    std::unordered_set<const constraint*>& predecessors() { return m_predecessors; }
    void add_predecessor(const constraint* p) {
        lp_assert(p != nullptr);
        m_predecessors.insert(p); }
};


struct pp_poly {
    cut_solver const& s;
    polynomial const& p;
    pp_poly(cut_solver const& s, polynomial const& p): s(s), p(p) {}
};

struct pp_constraint {
    cut_solver const& s;
    constraint const& c;
    pp_constraint(cut_solver const& s, constraint const& c): s(s), c(c) {}
};

std::ostream& operator<<(std::ostream& out, pp_poly const& p);
std::ostream& operator<<(std::ostream& out, pp_constraint const& p);
    
class cut_solver : public column_namer {
public: // for debugging

    typedef lp::polynomial polynomial;
    typedef lp::monomial monomial;

    vector<std::pair<mpq, var_index>> to_pairs(const vector<monomial>& ms) const {
        vector<std::pair<mpq, var_index>> ret;
        for (const auto p : ms)
            ret.push_back(p.to_pair());
        return ret;
    }    


    typedef const constraint const_constr;
    
    class literal {
        int                      m_decision_context_index; // points to the trail element if a decision has been made
        unsigned                 m_var;        
        bool                     m_is_lower;
        mpq                      m_bound;
        constraint*              m_constraint; // nullptr if it is a decided literal
        constraint*              m_tight_constr; // nullptr if it is not calculated
        unsigned                 m_prev_var_level;
    public:
    private:
        literal(  // creates an implied bound
            unsigned var_index,
            bool is_lower,
            const mpq & bound,
            constraint * constr,
            unsigned prev_var_level) :
            m_decision_context_index(-1),
            m_var(var_index),
            m_is_lower(is_lower),
            m_bound(bound),
            m_constraint(constr),
            m_tight_constr(nullptr),
            m_prev_var_level(prev_var_level) {
        }
        literal(  // creates a decided bound
            int trail_index,
            unsigned var_index,
            bool is_lower,
            const mpq & bound,
            unsigned prev_var_level):
            m_decision_context_index(trail_index),
            m_var(var_index),
            m_is_lower(is_lower),
            m_bound(bound),
            m_constraint(nullptr),
            m_tight_constr(nullptr),
            m_prev_var_level(prev_var_level) {
        }
    public:
        const constraint * tight_constr() const { return m_tight_constr; }
        constraint*& tight_constr () { return m_tight_constr; }
        const mpq & bound() const { return m_bound; }
        bool is_lower() const { return m_is_lower; }
        bool is_upper() const { return !m_is_lower; }
        int decision_context_index() const { return m_decision_context_index; }
        const_constr * cnstr() const { return m_constraint; }
        constraint * cnstr() { return m_constraint; }
        literal() {}

        bool tight_constraint_is_calculated() const {
            return m_tight_constr != nullptr;
        }

        bool is_decided() const { return m_decision_context_index != -1; }

        bool is_implied() const { return !is_decided();}

        // TBD: would be nice with a designated type for variables?

        unsigned var() const { return m_var; }

        static literal make_implied_literal(unsigned var_index, bool is_lower, const mpq & bound, constraint * c, unsigned var_level) {
            return literal(var_index, is_lower, bound, c, var_level);
        }
        static literal make_decided_literal(unsigned var_index, bool is_lower,
                                            const mpq & bound, int decision_context_index, unsigned var_level) {
            return literal(decision_context_index, var_index, is_lower, bound, var_level);
        }

        unsigned prev_var_level() const { return m_prev_var_level; }
    };    

    enum class bound_type {
        LOWER, UPPER, UNDEF
            };

    struct bound_result {
        mpq m_bound;
        bound_type m_type;
        
        bound_result(const mpq & b, bound_type bt): m_bound(b), m_type(bt) {}
        bound_result() : m_type(bound_type::UNDEF) {
        }
        void print( std::ostream & out) const {
            if (m_type == bound_type::LOWER) {
                out << "lower bound = ";
            }
            else if (m_type == bound_type::UPPER) {
                out << "upper bound = ";
            }
            else {
                out << "undef";
                return;
            }
            out << m_bound;
        }
        const mpq & bound() const { return m_bound; }
    };

    class var_info {
        unsigned                                                                       m_internal_j; // it is just the index into m_var_infos of this var_info, if the var_info is not active then this value is set to (unsigned)-1
        integer_domain<mpq>                                                            m_domain;
        // the map of constraints using the var: bound_type = UNDEF stands for a div constraint
        std::unordered_map<constraint*, bound_type, constraint_hash, constraint_equal> m_dependent_constraints;
        unsigned                                                                       m_external_stack_level;
        unsigned                                                                       m_number_of_bound_propagations;
        unsigned                                                                       m_number_of_asserts;
        
    public:
        unsigned number_of_asserts() const { return m_number_of_asserts; }

        var_info(unsigned user_var_index) :
            m_internal_j(user_var_index),
            m_external_stack_level(static_cast<unsigned>(-1)),
            m_number_of_bound_propagations(0),
            m_number_of_asserts(0)
        {}
        var_info() : m_internal_j(static_cast<unsigned>(-1)),
                     m_external_stack_level(static_cast<unsigned>(-1)),
                     m_number_of_bound_propagations(0),
                     m_number_of_asserts(0) {}

        bool is_active() const { return m_internal_j != static_cast<unsigned>(-1); }
        
        const integer_domain<mpq> & domain() const { return m_domain; }
        unsigned internal_j() const {
            return m_internal_j;
        }
        void activate(unsigned internal_j) {
            m_internal_j = internal_j;
        }
        void add_dependent_constraint(constraint* i, bound_type bt) {
            lp_assert(m_dependent_constraints.find(i) == m_dependent_constraints.end());
            if (i->is_assert())
                m_number_of_asserts++;
            m_dependent_constraints[i] = bt;
        }
        void remove_depended_constraint(constraint* i) {
            lp_assert(m_dependent_constraints.find(i) != m_dependent_constraints.end());
            if (i->is_assert())
                m_number_of_asserts--;
            m_dependent_constraints.erase(i);
        }

        void conditional_push(unsigned external_level) {
            if (external_level != m_external_stack_level) {
                m_domain.push();
                m_external_stack_level = external_level;
            }
        }
        
        bool intersect_with_lower_bound(const mpq & b, unsigned explanation, unsigned stack_level) {
            conditional_push(stack_level);
            return m_domain.intersect_with_bound(b, true, explanation);
        }
        
        bool intersect_with_upper_bound(const mpq & b, unsigned explanation, unsigned external_level) {
            conditional_push(external_level);
            return m_domain.intersect_with_bound(b, false, explanation);
        }
        
        bool is_fixed() const { return m_domain.is_fixed();}
        bool get_upper_bound(mpq & b) const { return m_domain.get_upper_bound(b); }
        bool get_lower_bound(mpq & b) const { return m_domain.get_lower_bound(b); }
        bool get_upper_bound_with_expl(mpq & b, unsigned& expl) const { return m_domain.get_upper_bound_with_expl(b, expl); }
        bool get_lower_bound_with_expl(mpq & b, unsigned& expl) const { return m_domain.get_lower_bound_with_expl(b, expl); }
        void print_var_domain(std::ostream &out) const { m_domain.print(out); }
        std::unordered_map<constraint*, bound_type, constraint_hash, constraint_equal> & dependent_constraints() { return m_dependent_constraints; }
        const std::unordered_map<constraint*, bound_type, constraint_hash, constraint_equal> & dependent_constraints() const { return m_dependent_constraints; }
        int get_lower_bound_expl() const { return m_domain.get_lower_bound_expl();}
        int get_upper_bound_expl() const { return m_domain.get_upper_bound_expl();}
    public:
        void pop(unsigned k, unsigned external_level) {            
            m_domain.pop(k);
            m_external_stack_level = external_level;
        }
        unsigned external_stack_level() const { return m_external_stack_level; }
        unsigned &external_stack_level() { return m_external_stack_level; }

        unsigned number_of_bound_propagations() const { return m_number_of_bound_propagations; }
        unsigned & number_of_bound_propagations() { return m_number_of_bound_propagations; }
        
    }; // end of var_info

    bool lhs_is_int(const vector<monomial> & lhs) const {
        for (auto & p : lhs) {
            if (numeric_traits<mpq>::is_int(p.coeff()) == false) return false;
        }
        return true;
    }

public:

    bool all_fixed_except_j(const polynomial & p, var_index j) const {
        for (auto &m : p.coeffs())
            if (m.var() != j && m_var_infos[m.var()].is_fixed() == false)
                return false;
        return true;
    }

    bool lower_bound_exists(const var_info & v) const {
        return v.get_lower_bound_expl() != -1;
    }

    bool upper_bound_exists(const var_info & v) const {
        return v.get_upper_bound_expl() != -1;
    }

    bool lower_bound_exists(const integer_domain<mpq> & v) const {
        return v.get_lower_bound_expl() != -1;
    }

    bool upper_bound_exists(const integer_domain<mpq> & v) const {
        return v.get_upper_bound_expl() != -1;
    }

    
    bool is_cc(var_index j, const constraint*&lower, const constraint*&upper) const {
        const var_info & vj = m_var_infos[j];
        if (lower_bound_exists(vj) && upper_bound_exists(vj))
            return false;
        if (vj.domain().is_empty())
            return false;

        unsigned upper_bounds = 0;
        unsigned lower_bounds = 0;
        for (auto p : vj.dependent_constraints()) {
            constraint* c = p.first;
            const mpq& coeff = c->poly().coeff(j);
            if (coeff == one_of_type<mpq>() || coeff == - one_of_type<mpq>())
                continue;
            if (!all_fixed_except_j(c->poly(), j)) continue;
            if (p.second == bound_type::UPPER) {
                upper_bounds++;
                upper = c;
                if (lower_bounds) return true;
            } else if (p.second == bound_type::LOWER) {
                lower_bounds++;
                lower = c;
                if (upper_bounds)
                    return true;
            }
        }
        return false;
    }

    std::string get_column_name(unsigned j) const {
        return m_var_name_function(m_var_infos[j].internal_j());
    }


    ~cut_solver() {
        for (constraint * c : m_asserts)
            delete c;
        for (constraint * c : m_lemmas)
            delete c;
    }

    class active_set {
        std::unordered_set<constraint*, constraint_hash, constraint_equal> m_cs;
    public:

        std::unordered_set<constraint*, constraint_hash, constraint_equal> cs() const { return m_cs;}
        
        bool is_empty() const { return m_cs.size() == 0; }

        void add_constraint(constraint* c) {
            if (c->is_active()) return;
            m_cs.insert(c);
            c->set_active_flag();
        }

        void clear() {
            for (constraint * c: m_cs) {
                c->remove_active_flag();
            }
            m_cs.clear();
        }
        
        
        constraint* remove_random_constraint(unsigned rand) {
            if (m_cs.size() == 0)
                return nullptr;
            unsigned j = rand % m_cs.size();
            auto it = std::next(m_cs.begin(), j);
            constraint * c = *it;
            c->remove_active_flag();
            m_cs.erase(it);
            return c;
        }
        
        unsigned size() const {
            return static_cast<unsigned>(m_cs.size());
        }

        void remove_constraint(constraint * c) {
            m_cs.erase(c);
            c->remove_active_flag();
        }
    };

    struct scope {
        unsigned m_asserts_size;
        unsigned m_lemmas_size;
        unsigned m_trail_size;
        scope() {}
        scope(unsigned asserts_size,
              unsigned lemmas_size,
              unsigned trail_size) : m_asserts_size(asserts_size),
                                     m_lemmas_size(lemmas_size),
                                     m_trail_size(trail_size)
        {}

    };
    
    // fields
    vector<var_info> m_var_infos;
    svector<constraint*>                           m_asserts;
    svector<constraint*>                           m_lemmas;
    vector<mpq>                                    m_v; // the values of the variables
    std::function<std::string (unsigned)>          m_var_name_function;
    std::function<void (unsigned, std::ostream &)> m_print_constraint_function;
    std::function<unsigned ()>                     m_number_of_variables_function;         
    std::function<const impq & (unsigned)>         m_var_value_function;         
    active_set                                     m_active_set;
    vector<literal>                                m_trail;
    lp_settings &                                  m_settings;
    unsigned                                       m_max_constraint_id;
    std::set<unsigned>                             m_U; // the set of conflicting cores
    unsigned                                       m_bounded_search_calls;
    unsigned                                       m_number_of_conflicts;
    vector<scope>                                  m_scopes;
    std::unordered_map<unsigned, unsigned>         m_user_vars_to_cut_solver_vars;
    std::unordered_set<constraint_index>           m_explanation; // if this collection is not empty we have a conflict 
    // the number of decisions in the current trail
    unsigned                                       m_decision_level;
    bool                                           m_stuck_state;
    bool                                           m_cancelled;
    // debug fields
    unsigned                                       m_number_of_constraints_tried_for_propagaton;
    unsigned                                       m_pushes_to_trail;

    bool is_lower_bound(literal & l) const {
        return l.is_lower();
    }
    
    // bool lower_for_var(unsigned j, mpq & lower) const {
    //     bool ret = false;
    //     for (unsigned i : m_var_infos[j].m_literals)
    //         if (is_lower_bound(m_trail[i])) {
    //             if (ret == false) {
    //                 ret = true;
    //                 lower = get_bound(m_trail[i]);
    //             } else {
    //                 lower = std::max(lower, get_bound(m_trail[i]));
    //             }
    //         }
    //     return ret;
    // }

    bool is_upper_bound(literal & l) const {
        return !l.is_lower();
    }
    
    bool  at_base_lvl() const { return m_decision_level == 0; }

    void simplify_problem() {
        // no-op
    }

    void gc() {
        // no-op
    }

    void restart() {
        // no-op for now
    }

    bool check_inconsistent() {
        if (at_base_lvl()) {
            // the last added lemmas can give the contradiction
            for (unsigned j = m_lemmas.size(); j--; ) {
                if (lower_is_pos(m_lemmas[j])) { 
                    TRACE("check_inconsistent_int", tout << pp_poly(*this, m_lemmas[j]->poly()) << "\n";); 
                    lp_assert(false);  // not implemented
                    return true;
                }
            }
            for (unsigned j = m_asserts.size(); j--; ) {
                if (lower_is_pos(m_asserts[j])) {
                    TRACE("check_inconsistent_int", tout << pp_poly(*this, m_asserts[j]->poly()) << "\n";); 
                    lp_assert(false);  // not implemented
                    return true;
                }
            }
        }
        return false;
    }

    void cleanup() {  }

    bool all_constraints_hold() const {
        for (auto c : m_asserts) {
            if (is_pos(value(c->poly()))) {
                TRACE("all_constraints_hold_int", tout << "constraint does not hold\n";
                      tout << pp_constraint(*this, *c) << "value = " << value(c->poly()) << std::endl;);
                
                return false;
            }
        }
        for (auto c : m_lemmas) {
            if (is_pos(value(c->poly()))) {
                TRACE("all_constraints_hold_int", tout << "constraint does not hold\n";
                      print_constraint(tout, *c););
                return false;
            }
        }
        return true;
    }
    
    lbool final_check() {
        if (!all_vars_are_fixed()) {
            TRACE("final_check_int", tout << "return undef" << std::endl;);
            m_stuck_state = true;
            return lbool::l_undef; // we are stuck
        }
        lp_assert(all_constraints_hold());
        lp_assert(at_base_lvl());
        // there are no more case splits, and all clauses are satisfied.
        // prepare the model for external consumption.
        return lbool::l_true;
    }
    
    void find_new_conflicting_cores_under_constraint(var_index j, const_constr* c) {
        // lp_assert(false);
    }

    void find_new_conflicting_cores(var_index j) {
        for (auto p: m_var_infos[j].dependent_constraints())
            find_new_conflicting_cores_under_constraint(j, p.first);
    }

    void set_value_for_fixed_var_and_check_for_conf_cores(unsigned j) {
        TRACE("set_value_for_fixed_var_and_check_for_conf_cores", tout << "j = " << j << std::endl;); 
        if (m_v.size() <= j)
            m_v.resize(j + 1);
        lp_assert(m_var_infos[j].is_fixed());
        lp_assert(m_var_infos[j].is_active());
        m_var_infos[j].domain().get_upper_bound(m_v[j]); // sets the value of the variable
        find_new_conflicting_cores(j);
    }
    
    void restrict_var_domain_with_bound_result(var_index j, const bound_result & br, unsigned trail_index) {
        TRACE("restrict_var_domain_with_bound_result", tout << "j = " << j << std::endl;
              br.print(tout););
        auto & vi = m_var_infos[j];
        lp_assert(!vi.is_fixed());
        lp_assert(m_trail.back().var() == j);
        if (br.m_type == bound_type::UPPER) {
            vi.intersect_with_upper_bound(br.m_bound,  trail_index, m_scopes.size());
        } else {
            vi.intersect_with_lower_bound(br.m_bound,  trail_index, m_scopes.size());
        }
        if (vi.is_fixed()) {
            TRACE("d.is_fixed", tout << "j = " << j << std::endl;);
            set_value_for_fixed_var_and_check_for_conf_cores(j);
        }
    }

    // 'j' is a variable that changed
    void add_changed_var(unsigned j) {
        TRACE("add_changed_var_int", tout <<  "j = " << j << "\n";);
        for (auto & p: m_var_infos[j].dependent_constraints()) {
            TRACE("add_changed_var_int", tout << pp_constraint(*this, *p.first) << "\n";);
            m_active_set.add_constraint(p.first);
        }
    }

    unsigned number_of_vars() const { return static_cast<unsigned>( m_var_infos.size()); }
    
    const mpq & var_value(unsigned j) const {
        return m_v[j];
    }

    bool var_is_active(unsigned j) const {
        return m_var_infos[j].is_active();
    }
    
    struct test_bound_struct {
        mpq m_lower_bound;
        mpq m_upper_bound;
        int m_expl_lower;
        int m_expl_upper;
        test_bound_struct() :m_expl_lower(-1), m_expl_upper(-1) {}
    };

    
    bool var_infos_are_correct() const {
        vector<test_bound_struct> bounds = get_bounds_from_trail();
        for (unsigned j = 0; j < m_var_infos.size(); j++)
            if (!var_info_is_correct(j, bounds[j])) {
                TRACE("var_infos_are_correct", print_var_info(tout, j); tout << " var_info is incorrect j = " << j;);
                return false;
            }
        return true;
    }

    bound_result bound_test_on_poly(const polynomial &p, const mpq& a, unsigned j, vector<test_bound_struct>& bs) const {
        lp_assert(!is_zero(a));
        if (numeric_traits<mpq>::is_pos(a)) {
            TRACE("bound_test_on_poly", tout << var_name(j) << " a is pos, p = "; print_polynomial(tout, p););
            bound_result r = lower_without_test(p, j, bs);
            if (r.m_type == bound_type::UNDEF)
                return r;
            lp_assert(is_int(r.m_bound));
            r.m_bound = - ceil_ratio(r.m_bound , a);
            r.m_type = bound_type::UPPER;
            return r;
        }
        else {
            TRACE("bound_test_on_poly", tout << var_name(j) << " a is neg, p = "; print_polynomial(tout, p););
            bound_result r = lower_without_test(p, j, bs);
            if (r.m_type == bound_type::UNDEF)
                return r;
            r.m_bound = -floor_ratio(r.m_bound, a);
            r.m_type = bound_type::LOWER;
            return r;
        }
  
    }

    bound_result bound_test(unsigned j, const polynomial &p, vector<test_bound_struct>& bs) const {
        const mpq &a = p.coeff(j);
        bound_result br = bound_test_on_poly(p, a, j, bs);
        TRACE("bound_test", tout << var_name(j) << ", p = ";  print_polynomial(tout, p);
              tout << ", br = "; br.print(tout); );
        return br;
    }
    
    void bound_test_literal(const literal & l, vector<test_bound_struct> & bs) const {
        bound_result br = l.cnstr() != nullptr?
            bound_test(l.var(), l.cnstr()->poly(), bs) :
            bound_result(l.bound(), l.is_lower() ? bound_type::LOWER: bound_type::UPPER);
        lp_assert(br.m_type != bound_type::UNDEF);
        if (l.is_lower()) {
            lp_assert(br.m_type == bound_type::LOWER);
            lp_assert(br.m_bound >= l.bound());
        } else {
            lp_assert(br.m_type == bound_type::UPPER);
            lp_assert(br.m_bound <= l.bound());
        }

        if (l.tight_constr() != nullptr) {
            br = bound_test(l.var(), l.tight_constr()->poly(), bs);
            lp_assert(br.m_type != bound_type::UNDEF);
            if (l.is_lower()) {
                lp_assert(br.m_type == bound_type::LOWER);
                lp_assert(br.m_bound >= l.bound());
            } else {
                lp_assert(br.m_type == bound_type::UPPER);
                lp_assert(br.m_bound <= l.bound());
            }
        }
            
    }
    
    void get_bounds_from_trail_elem(unsigned j, vector<test_bound_struct>& bs) const {
        const literal & l = m_trail[j];
        auto & t = bs[l.var()];
        TRACE("get_bounds_from_trail_elem", tout << "j = " << j << ", literal = "; print_literal(tout, l););
        bound_test_literal(l, bs);
        if (l.is_lower()) {
            if (t.m_expl_lower == -1) {
                t.m_expl_lower = j;
                t.m_lower_bound = l.bound();
                TRACE("get_bounds_from_trail_elem", tout << var_name(l.var()) << " m_lower_bound = " << t.m_lower_bound << std::endl;);
            } else {
                lp_assert(t.m_lower_bound < l.bound());
                t.m_lower_bound = l.bound();
                TRACE("get_bounds_from_trail_elem", tout << var_name(l.var()) << " m_lower_bound = " << t.m_lower_bound << std::endl;);
                t.m_expl_lower = j;
            }
        } else {
            if (t.m_expl_upper == -1) {
                t.m_expl_upper = j;
                t.m_upper_bound = l.bound();
                TRACE("get_bounds_from_trail_elem", tout << var_name(l.var()) << " m_u = " << t.m_upper_bound << std::endl;);
            } else {
                lp_assert(t.m_upper_bound > l.bound());
                t.m_upper_bound = l.bound();
                t.m_expl_upper = j;
                TRACE("get_bounds_from_trail_elem", tout << var_name(l.var()) << " m_u = " << t.m_upper_bound << std::endl;);
            }
        }
    }

    vector<test_bound_struct> get_bounds_from_trail() const {
        vector<test_bound_struct> ret(m_var_infos.size());
        for (unsigned j = 0; j < m_trail.size(); j++) {
            get_bounds_from_trail_elem(j, ret);
        }
        return ret;
    }
    
    bool var_info_is_correct(unsigned j, const test_bound_struct& t) const {
        const var_info & v = m_var_infos[j];
        if (v.external_stack_level() != static_cast<unsigned>(-1) && v.external_stack_level() > m_scopes.size()) {
            
            TRACE("var_info_is_correct", tout << "incorrect: the level is too high:";
                  print_var_info(tout, j);
                  tout << "external_level = " << v.external_stack_level();
                  tout << "\nm_scopes.size() = " << m_scopes.size(); );
            return false;
        }
        std::unordered_set<constraint*, constraint_hash, constraint_equal> deps;
        for (const auto c: m_asserts) {
            if (!is_zero(c->coeff(j)))
                deps.insert(c);
        }
        for (const auto c: m_lemmas) {
            if (!is_zero(c->coeff(j)))
                deps.insert(c);
        }

        for (auto p : v.dependent_constraints()) {
            if (deps.find(p.first) == deps.end()) {
                TRACE("var_info_is_correct", tout << "deps.find(p.first) == deps.end()";);
                return false;
            }
        }
        if (v.is_fixed() && m_v.size() <= j) {
            TRACE("var_info_is_correct", tout << "m_v is too short, j="<< j <<std::endl;);
            return false;
        }

        for (auto p: deps) {
            if (v.dependent_constraints().find(p) == v.dependent_constraints().end()) {
                TRACE("var_info_is_correct", tout << "v.dependent_constraints().find(p) == v.dependent_constraints().end()";);
                return false;
            }
        }

        return var_bounds_are_correctly_explained_by_trail(j, t);
    }


    bool var_bounds_are_correctly_explained_by_trail(unsigned j, const test_bound_struct& t) const {
        return var_upper_bound_is_correct_by_trail(j, t) && var_lower_bound_is_correct_by_trail(j, t);
    }

    bool var_upper_bound_is_correct_by_trail(unsigned j, const test_bound_struct& t) const {
        const var_info & v = m_var_infos[ j];
        mpq b; unsigned expl; 
        if (v.get_upper_bound_with_expl(b, expl)) {
            if (expl >= m_trail.size()) {
                TRACE("var_bound_is_correct_by_trail", tout<< "expl =" << expl << " of " << var_name(j) << ", j = "<< j << " points out of the trail, trail.size() =  " << m_trail.size(); tout << "return false";);
                return false;
            }
            const literal & l = m_trail[expl];

            if (! (b == l.bound() && !l.is_lower() && j == l.var())) {
                TRACE("var_bound_is_correct_by_trail", tout<< "expl=" << expl << std::endl; print_var_info(tout, j); tout << "b=" << b<<", expl = " << expl << std::endl; print_literal(tout, l); tout << "return false";);
                return false;
            }
            return (t.m_expl_upper == static_cast<int>(expl) && t.m_upper_bound == b);
        }
        CTRACE("var_bound_is_correct_by_trail", t.m_expl_upper != -1 , 
               tout << "literal index = " << t.m_expl_upper << "\n";
               print_literal(tout, m_trail[t.m_expl_upper]);
               tout << "will return false";
               );
        
        return t.m_expl_upper == -1;
    }

    // bool run_over_trail_with_upper_bound(unsigned j, const mpq & b) const {
    //     bool limited = false;
    //     mpq found_b;
    //     run_over_trail_with_upper_bound_on_literal(j, b, 
    // }
    
    bool var_lower_bound_is_correct_by_trail(unsigned j, const test_bound_struct& t) const {
        const var_info & v = m_var_infos[j];
        mpq b;
        unsigned expl;
        if (v.get_lower_bound_with_expl(b, expl)) {
            if (expl >= m_trail.size()) {
                TRACE("var_bound_is_correct_by_trail", tout<< "expl =" << expl << " of " << var_name(j) << ", j = "<< j << " points out of the trail, trail.size() =  " << m_trail.size();
                      tout << ", "; print_var_info(tout, j););
                return false;
            }
            const literal & l = m_trail[expl];
            

            if (! (t.m_expl_lower == static_cast<int>(expl) && t.m_lower_bound == b)) {
                TRACE("var_bound_is_correct_by_trail", print_var_info(tout, j); tout << "b=" << b<<", expl = " << expl << std::endl; print_literal(tout, l); tout << "return " << (b == l.bound() && l.is_lower()););
                return false;
            }
            return b == l.bound() && l.is_lower();
        }

        CTRACE("var_bound_is_correct_by_trail", !(t.m_expl_lower == -1), tout << "return " << (t.m_expl_lower == -1) << " t.m_expl_lower = " << t.m_expl_lower << ", "; print_var_info(tout, v); print_trail(tout););
        return t.m_expl_lower == -1;
    }
    
    void push_literal_to_trail(literal & l) {
        m_pushes_to_trail ++;
        m_trail.push_back(l);
        add_changed_var(l.var());
    }

    unsigned find_large_enough_j(unsigned i) {
        unsigned r = 0;
        for (const auto & p : m_asserts[i]->poly().m_coeffs) {
            r = std::max(r, p.var() + 1);
        }
        return r;
    }

    std::string var_name(unsigned j) const {
        return get_column_name(j);
    }
    
    void trace_print_domain_change(std::ostream& out, unsigned j, const mpq& v, const monomial & p, const_constr* c) const {
        out << "trail.size() = " << m_trail.size() << "\n";
        out << "change in domain of " << var_name(j) << ", v = " << v << ", domain becomes ";
        print_var_domain(out, j);
        mpq lb;
        bool r = lower(c, lb);
        if (r)
            out << "lower_of_constraint = " << lb << "\n";
        else
            out << "no lower bound for constraint\n";
    }

    
    
    bool new_lower_bound_is_relevant(unsigned j, const mpq & v) const {
        mpq lb;
        const var_info & vi = m_var_infos[j];
        auto & d = vi.domain();
        bool has_bound = d.get_lower_bound(lb);
        if (!has_bound)
            return true;
        if (v <= lb)
            return false;
        if (upper_bound_exists(d))
            return true;

        if (too_many_propagations_for_var(vi))
            return false;
        
        //        int delta = 2;
        return v >= lb + 2 * abs(lb);
        
    }

    bool too_many_propagations_for_var(const var_info& vi) const {
        return vi.number_of_bound_propagations() > m_settings.m_cut_solver_cycle_on_var * vi.number_of_asserts();
    }

    bool new_upper_bound_is_relevant(unsigned j, const mpq & v) const {
        auto & vi = m_var_infos[j];
        auto & d = vi.domain();
        mpq b;
        bool has_bound = d.get_upper_bound(b);
        if (!has_bound)
            return true;
        if (v >= b)
            return false;
        if (lower_bound_exists(d))
            return true;

        if (too_many_propagations_for_var(vi))
            return false;
        
        //        delta = 2
        return v <= b - 2 * abs(b); // returns false if the improvement is small
    }

    void intersect_var_info_with_upper_bound(unsigned j, const mpq & v) {
        lp_assert(m_trail.back().var() == j && m_trail.back().is_upper());
        m_var_infos[j].intersect_with_upper_bound(v, m_trail.size() - 1, m_scopes.size());   // m_trail.size() - 1 is the explanation 
        if (m_var_infos[j].is_fixed()) 
            set_value_for_fixed_var_and_check_for_conf_cores(j);
    }

    void intersect_var_info_with_lower_bound(unsigned j, const mpq& v) {
        lp_assert(m_trail.back().var() == j && m_trail.back().is_lower());
        m_var_infos[j].intersect_with_lower_bound(v, m_trail.size() - 1, m_scopes.size()); // m_trail.size() - 1 is the explanation
        if (m_var_infos[j].is_fixed()) 
            set_value_for_fixed_var_and_check_for_conf_cores(j);
    }

    void propagate_monomial_on_lower(const monomial & p,
                                     const mpq& lower_val,
                                     constraint* c) {
        unsigned j = p.var();

        if (is_pos(p.coeff())) {
            mpq m;
            get_var_lower_bound(p.var(), m);
            mpq v = floor(- lower_val / p.coeff()) + m;
            if (new_upper_bound_is_relevant(j, v)) {
                add_bound(v, j, false, c);
                intersect_var_info_with_upper_bound(j, v);
            }
        } else {
            mpq m;
            get_var_upper_bound(p.var(), m);
            mpq v = ceil( - lower_val / p.coeff()) + m;
            if (new_lower_bound_is_relevant(j, v)) {
                add_bound(v, j, true, c);
                intersect_var_info_with_lower_bound(j, v);
            }
        }
    }

    void  propagate_monomial_on_right_side(const monomial & p,
                                           const mpq& rs,
                                           constraint *c) {
        unsigned j = p.var();

        if (is_pos(p.coeff())) {
            mpq v = floor(rs / p.coeff());
            if (new_upper_bound_is_relevant(j, v)) {
                add_bound(v, j, false, c);
                intersect_var_info_with_upper_bound(j, v);
                TRACE("ba_int_change", trace_print_domain_change(tout, j, v, p, c););
            }
        } else {
            mpq v = ceil(rs / p.coeff());
            if (new_lower_bound_is_relevant(j, v)) {
                TRACE("ba_int_change", print_var_info(tout, j););
                add_bound(v, j, true , c);
                intersect_var_info_with_lower_bound(j, v);
                TRACE("ba_int_change", trace_print_domain_change(tout, j, v, p, c););
            }
        }
    }

    void print_var_info(std::ostream & out, const var_info & vi) const {
        out << m_var_name_function(vi.internal_j()) << " ";
        if (vi.internal_j() < m_v.size()) {
            out << "m_v[" << vi.internal_j() << "] = " << m_v[vi.internal_j()] << std::endl;
        }
        if (vi.is_active()) out << ", active var ";
        print_var_domain(out, vi);
        out << ", propagaions = " <<  vi.number_of_bound_propagations() << ", deps = " << vi.dependent_constraints().size();
        out << ", asserts = " << vi.number_of_asserts() << std::endl;
        // out << "external levels: ";
        // for (auto j : vi.external_stack_level())
        //     out << j << " ";
    }

    void print_var_info(std::ostream & out, unsigned j) const {
        print_var_info(out, m_var_infos[j]);
    }
    
    void print_var_domain(std::ostream & out, unsigned j) const {
        m_var_infos[j].print_var_domain(out);
    }

    void print_var_domain(std::ostream & out, const var_info & vi) const {
        vi.print_var_domain(out);
    }

    // b is the value of lower
    void propagate_constraint_on_lower(constraint* c, const mpq & b) {
        for (const auto & p: c->coeffs())
            propagate_monomial_on_lower(p, b, c);
    }


    void explain_literal(unsigned trail_index,
                         std::unordered_set<unsigned> & visited_literals,
                         std::unordered_set<const_constr*> & visited_constraints) {
        if (visited_literals.find(trail_index) != visited_literals.end())
            return;
        visited_literals.insert(trail_index);
        const literal & l = m_trail[trail_index];
        const_constr* c = l.tight_constr();
        if (c == nullptr)
            c = l.cnstr();
        lp_assert(c != nullptr);
        add_premises(c, visited_constraints);
        explain_bound(c, trail_index, visited_literals, visited_constraints);
    }
    
    void explain_bound(const_constr * c,
                       unsigned trail_lim,
                       std::unordered_set<unsigned> & visited_literals,
                       std::unordered_set<const_constr*> visited_constraints) {
        add_premises(c, visited_constraints);
        TRACE("fill_conflict_explanation", tout << "visited_constraints\n";
              for (auto cc: visited_constraints)
                  trace_print_constraint(tout, *cc););
        for (const monomial & m : c->poly().coeffs()) {
            int trail_index = find_literal_index_after(m.var(), is_pos(m.coeff()), trail_lim);
            if (trail_index == -1)
                continue;
            explain_literal(trail_index, visited_literals, visited_constraints);
        }
        
    }

    void dumb_exlplanations() {
        m_explanation.clear();
        for (auto c: m_asserts)
            for (auto j : c->assert_origins())
                m_explanation.insert(j);
    }

    void add_premises(const_constr *c, std::unordered_set<const_constr*> & visited_constraints) {
        if (visited_constraints.find(c) != visited_constraints.end())
            return;
        
        visited_constraints.insert(c);
        
        for (auto j : c->assert_origins())
            m_explanation.insert(j);

        for (const_constr* p : c->predecessors())
            add_premises(p, visited_constraints);
    }
    
    void fill_conflict_explanation(const constraint *confl) {
        //dumb_exlplanations();
        TRACE("fill_conflict_explanation",
              trace_print_constraint(tout, *confl);
              print_trail(tout);
              );
        m_explanation.clear();
        std::unordered_set<unsigned> visited_literals;
        std::unordered_set<const_constr*> visited_constraints;
        explain_bound(confl, m_trail.size(), visited_literals, visited_constraints);
        TRACE("fill_conflict_explanation", tout << "m_explanation = ";
              for (unsigned j : m_explanation) {
                  tout <<  j << " ";
              });
    }

    void trace_print_constraint(std::ostream& out, const_constr& i) const {
        trace_print_constraint(out, &i);
    }   

    void trace_print_constraint(std::ostream& out, const_constr* i) const {
        print_constraint(out, *i);
        out << "id = " << i->id() << ", ";
        unsigned j;
        auto pairs = to_pairs(i->poly().m_coeffs);
        auto it = linear_combination_iterator_on_vector<mpq>(pairs);
        while (it.next(j)) {
            out << "domain of " << var_name(j) << " = ";
            print_var_domain(out, j);
        }
        if (i->assert_origins().size()) {
            out << (i->assert_origins().size() > 1?"origins: ":"origin: ") ;
            for (auto o : i->assert_origins())
                out << o << ", ";
            out << "\n";
        }
    }

   
    void propagate_constraint_only_one_unlim(constraint* i, unsigned the_only_unlim) {
        mpq rs = - i->poly().m_a;
        for (unsigned j = 0; j < i->poly().m_coeffs.size(); j++) {
            if (j == the_only_unlim) continue;
            mpq m;
            lower_monomial(i->poly().m_coeffs[j], m);
            rs -= m;
        }

        // we cannot get a conflict here because the monomial i.poly().m_coeffs[the_only_unlim]
        // is unlimited from below and we are adding an upper bound for it
        propagate_monomial_on_right_side(i->poly().m_coeffs[the_only_unlim], rs, i);
    }

    bool conflict() const { return m_explanation.size() > 0; }

    bool get_var_lower_bound(var_index i, mpq & bound) const {
        return m_var_infos[i].get_lower_bound(bound);
    }

    bool get_var_lower_bound_test(var_index i, mpq & bound, const vector<test_bound_struct>& bs) const {
        const auto & t = bs[i];
        if (t.m_expl_lower == -1)
            return false;
        bound = t.m_lower_bound;
        return true;
    }
    bool get_var_upper_bound_test(var_index i, mpq & bound, const vector<test_bound_struct>& bs) const {
        const auto & t = bs[i];
        if (t.m_expl_upper == -1)
            return false;
        bound = t.m_upper_bound;
        return true;
    }

    
    
    bool get_var_upper_bound(var_index i, mpq & bound) const {
        const var_info & v = m_var_infos[i];
        return v.get_upper_bound(bound);
    }

    // returns the reason for the lower bound, which is the index of the literal,
    // or -1 if the bound does not exist
    int get_lower_for_monomial_expl(const monomial & p) const {
        lp_assert(p.coeff() != 0);

        const auto & v = m_var_infos[p.var()];
        return p.coeff() > 0? v.get_lower_bound_expl():v.get_upper_bound_expl();
    }

    bool lower_for_monomial_exists(const monomial &p ) const {
        return get_lower_for_monomial_expl(p) != -1;
    }

    bool lower_for_monomial_exists_test(const monomial &p, const vector<test_bound_struct>& bs ) const {
        return is_pos(p.coeff())? bs[p.var()].m_expl_lower != -1: bs[p.var()].m_expl_upper != -1;
    }

    bool upper_for_monomial_exists(const monomial &p ) const {
        return get_upper_for_monomial_expl(p) != -1;
    }
    bool upper_for_monomial_exists_test(const monomial &p, const vector<test_bound_struct> & bs ) const {
        const auto &t = bs[p.var()];
        TRACE("upper_for_monomial_exists_test", tout << p.coeff() << ", " << var_name(p.var());
              tout << "t.m_expl_lower = " << t.m_expl_lower << ", t.m_expl_upper = " << t.m_expl_upper;);
        return is_neg(p.coeff())? t.m_expl_lower != -1: t.m_expl_upper != -1;
    }
    
    int get_upper_for_monomial_expl(const monomial & p) const {
        lp_assert(p.coeff() != 0);
        const auto &v = m_var_infos[p.var()];
        return p.coeff() > 0? v.get_upper_bound_expl() : v.get_lower_bound_expl();
    }

    bool lower_monomial_test(const monomial & p, mpq & lb, vector<test_bound_struct>& bs) const {
        lp_assert(p.coeff() != 0);
        mpq var_bound;
        if (p.coeff() > 0) {
            if (!get_var_lower_bound_test(p.var(), var_bound, bs))
                return false;
            lb = p.coeff() * var_bound;
        }
        else {
            if (!get_var_upper_bound_test(p.var(), var_bound, bs))
                return false;
            lb = p.coeff() * var_bound;
        }
        return true;
    }
    // finds the lower bound of the monomial,
    // otherwise returns false
    bool lower_monomial(const monomial & p, mpq & lb) const {
        lp_assert(p.coeff() != 0);
        mpq var_bound;
        if (p.coeff() > 0) {
            if (!get_var_lower_bound(p.var(), var_bound))
                return false;
            lb = p.coeff() * var_bound;
        }
        else {
            if (!get_var_upper_bound(p.var(), var_bound))
                return false;
            lb = p.coeff() * var_bound;
        }
        return true;
    }

    bool upper_monomial(const monomial & p, mpq & lb) const {
        lp_assert(p.coeff() != 0);
        mpq var_bound;
        if (p.coeff() > 0) {
            if (!get_var_upper_bound(p.var(), var_bound))
                return false;
        }
        else {
            if (!get_var_lower_bound(p.var(), var_bound))
                return false;
        }
        lb = p.coeff() * var_bound;
        return true;
    }

    bool upper_monomial_test(const monomial & p, mpq & lb, const vector<test_bound_struct> & bs) const {
        lp_assert(p.coeff() != 0);
        mpq var_bound;
        if (p.coeff() > 0) {
            if (!get_var_upper_bound_test(p.var(), var_bound, bs))
                return false;
        }
        else {
            if (!get_var_lower_bound_test(p.var(), var_bound, bs))
                return false;
        }
        lb = p.coeff() * var_bound;
        return true;
    }

    
    
    // returns false if not limited from below
    // otherwise the answer is put into lb
    bool lower(const_constr* c, mpq & lb) const {
        return lower(c->poly(), lb);
    }

    // returns false if not limited from below
    // otherwise the answer is put into lb
    mpq lower_val(const_constr * c) const {
        return lower_val(*c);
    }
    
    mpq lower_val(const_constr & i) const {
        mpq lb;
#if Z3DEBUG
        bool r =
#endif
            lower(i.poly(), lb);
        lp_assert(r);
        return lb;
    }

        
    // returns false if not limited from below
    // otherwise the answer is put into lb
    bool lower(const polynomial & f, mpq & lb) const {
        lb = f.m_a;
        mpq lm;
        for (const auto & p : f.m_coeffs) {
            if (lower_monomial(p, lm)) {
                lb += lm;
            } else {
                return false;
            }
        }
        return true;
    }


    // returns the number of lower unlimited monomials - 0, 1, >=2
    // if there is only one lower unlimited then the index is put into the_only_unlimited
    int lower_analize(const_constr * f, unsigned & the_only_unlimited) const {
        int ret = 0;
        for (unsigned j = 0; j < f->poly().m_coeffs.size(); j++) {
            int k;
            if ((k = get_lower_for_monomial_expl(f->poly().m_coeffs[j])) == -1) {
                if (ret == 1)
                    return 2;
                ret ++;
                the_only_unlimited = j;
            }
        }
        return ret;
    }


 
    bound_result lower_without(const polynomial & p, var_index j) const {
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;
            if (!lower_for_monomial_exists(t)) {
                return bound_result();
            }
        }
        // if we are here then there is a lower bound for p
        mpq bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;

            mpq l;
            lower_monomial(t, l);
            bound += l;
        }
        return bound_result(bound,bound_type::LOWER);
    }

    bound_result lower_without_test(const polynomial & p, var_index j, vector<test_bound_struct>& bs ) const {
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;
            if (!lower_for_monomial_exists_test(t, bs)) {
                return bound_result();
            }
        }
        // if we are here then there is a lower bound for p
        mpq bound = p.m_a;
        for (const auto & t:  p.m_coeffs) {
            if (t.var() == j)
                continue;

            mpq l;
            lower_monomial_test(t, l, bs);
            bound += l;
        }
        return bound_result(bound,bound_type::LOWER);
    }

    // a is the coefficient before j
    bound_result bound_on_polynomial(const polynomial & p, const mpq& a, var_index j) const {
        lp_assert(!is_zero(a));
        bound_result r = lower_without(p, j);
        if (r.m_type == bound_type::UNDEF)
            return r;
        if (numeric_traits<mpq>::is_pos(a)) {
            r.m_bound = - ceil_ratio(r.m_bound , a);
            r.m_type = bound_type::UPPER;
            return r;
        }
        else {
            r.m_bound = -floor_ratio(r.m_bound, a);
            r.m_type = bound_type::LOWER;
            return r;
        }
    }
    

    
    bound_result bound(const_constr * q, var_index j) const {
        const mpq& a = q->poly().coeff(j);
        return bound_on_polynomial(q->poly(), a, j);
    }

    bound_result bound(const polynomial& q, var_index j) const {
        const mpq& a = q.coeff(j);
        return bound_on_polynomial(q, a, j);
    }

    
    bound_result bound(unsigned constraint_index, var_index j) const {
        return bound(m_asserts[constraint_index], j);
    }

    
    void print_constraint(std::ostream & out, const_constr & i ) const {
        out << (i.is_lemma()? "lemma ": "assert ");
        out << "id = " << i.id() << ", ";
        if (!i.is_ineq()) {
            out << i.divider() << " | ";
        }
        out << pp_poly(*this, i.poly());
        if (i.is_ineq()) {
            out << " <= 0";
        }
        out << " active = " << i.is_active() << " ";
        mpq b;
        if (lower(&i, b)) {
            out << ", lower = " << b;
            if (is_pos(b))
                out << " INF";
        } else {
            out << ", no lower";
        }

        bool all_vars_are_fixed = true;
        for (const auto & p : i.poly().coeffs()) {
            if (!m_var_infos[p.var()].is_fixed()) {
                all_vars_are_fixed = false;
                break;
            }
        }

        if (all_vars_are_fixed) {
            auto v = value(i.poly());
            out << ", value = " << v;
            if (is_pos(v))
                out << " INF";
        }
        out << std::endl;
    }

    void print_literal(std::ostream & out, const literal & t) const {
        out << (t.is_decided()? "decided ": "implied ");
        out << var_name(t.var()) << " ";
        if (t.is_lower())
            out << ">= ";
        else
            out << "<= ";
        out << t.bound();

        if (t.is_decided() == false) {
            out << " by constraint " << pp_constraint(*this, *(t.cnstr()));
        } else {
            out << " decided on trail element " << t.decision_context_index();
            if (m_trail[t.decision_context_index()].tight_constr() != nullptr) {
                out << " with tight ineq " << pp_constraint(*this, *m_trail[t.decision_context_index()].tight_constr());
            }
            out << "\n";
        }
        if (t.tight_constr() != nullptr) {
            out << "tight_constr() = " << pp_constraint(*this, *t.tight_constr()) << "\n";
        }
    }
       
    void print_polynomial(std::ostream & out, const polynomial & p) const {
        vector<std::pair<mpq, unsigned>> pairs = to_pairs(p.m_coeffs);
        this->print_linear_combination_of_column_indices_std(pairs, out);
        if (!is_zero(p.m_a)) {
            if (p.m_a < 0) {
                out << " - " << -p.m_a;
            } else {
                out << " + " << p.m_a;
            }
        }
    }

    void trace_print_polynomial(std::ostream & out, const polynomial & p) const {
        vector<std::pair<mpq, unsigned>> pairs = to_pairs(p.m_coeffs);
        this->print_linear_combination_of_column_indices_std(pairs, out);
        if (!is_zero(p.m_a)) {
            if (p.m_a < 0) {
                out << " - " << -p.m_a;
            } else {
                out << " + " << p.m_a;
            }
        }
        out << "\n";
        for (auto m : p.coeffs()) {
            unsigned j = m.var();
            out << "domain of " << var_name(j) << " = ";
            print_var_domain(out, j);
        }
        mpq b;
        if (lower(p, b)) {
            out << ", lower = " << b;
            if (is_pos(b))
                out << " INF";
        } else {
            out << ", no lower";
        }

        bool all_vars_are_fixed = true;
        for (const auto & pp : p.coeffs()) {
            if (!m_var_infos[pp.var()].is_fixed()) {
                all_vars_are_fixed = false;
                break;
            }
        }

        if (all_vars_are_fixed) {
            auto v = value(p);
            out << ", value = " << v;
            if (is_pos(v))
                out << " INF";
        }
    }

    // trying to improve constraint "ie" by eliminating var j by using the tight inequality 
    // for j. the left side of the inequality is passed as a parameter.
    bool resolve(polynomial & ie, unsigned j, bool sign_j_in_ti_is_pos, const polynomial & ti) const {
        TRACE("resolve_int", tout << "ie = " << pp_poly(*this, ie);
              tout << ", j = " << j << "(" << var_name(j) << ")" << ", sign_j_in_ti_is_pos = " << sign_j_in_ti_is_pos << ", ti = " << pp_poly(*this, ti) << "\n";);
        lp_assert(ti.var_coeff_is_unit(j));
        lp_assert(is_pos(ti.coeff(j)) == sign_j_in_ti_is_pos);
        auto &coeffs = ie.m_coeffs;
        // todo: implement a more efficient version
        bool found = false;
        mpq a;
        for (const auto & c : coeffs) {
            if (c.var() == j) {
                a = c.coeff();
                found = true;
                break;
            }
        }

        if (!found) {
            TRACE("resolve_int", tout << " no change\n";);
            return false;
        }

        if (is_neg(a)) {
            if (!sign_j_in_ti_is_pos)
                return false;
            a = -a;
        } else {
            if (sign_j_in_ti_is_pos)
                return false;
        }

        for (auto & c : ti.m_coeffs) {
            ie += monomial(a * c.coeff(), c.var());
        }

        ie.m_a += a * ti.m_a;
        TRACE("resolve_int", tout << "ie = " << pp_poly(*this, ie) << "\n";);
        return true;
    }

    // returns true iff p imposes a better bound on j
    bool improves(var_index j, const_constr * p) const {
        auto a = p->coeff(j);
        if (is_zero(a))
            return false;
        const auto& dom = m_var_infos[j].domain();
        if (dom.is_empty())
            return false;
        if (is_pos(a)) {
            bound_result new_upper = bound(p, j);
            if (new_upper.m_type == bound_type::UNDEF)
                return false;
            return dom.improves_with_upper_bound(new_upper.bound());
        }

        lp_assert(is_neg(a));
        bound_result new_lower = bound(p, j);
        if (new_lower.m_type == bound_type::UNDEF)
            return false;
        return dom.improves_with_lower_bound(new_lower.bound());
    }


    // returns true iff br imposes a better bound on j
    bool improves(var_index j, const bound_result & br) const {
        if (br.m_type == bound_type::UNDEF)
            return false;
        const auto& dom = m_var_infos[j].domain();
        if (dom.is_empty())
            return false;
        if (br.m_type == bound_type::UPPER) {
            mpq b;
            bool j_has_upper_bound = get_var_upper_bound(j, b);
            return (!j_has_upper_bound || br.bound() < b) &&
                !dom.intersection_with_upper_bound_is_empty(br.bound());
        }

        if (br.m_type == bound_type::UNDEF)
            return false;
        mpq b;
        bool lower_bound_exists = get_var_lower_bound(j, b);
        return (!lower_bound_exists || br.bound() > b) &&
            !dom.intersection_with_lower_bound_is_empty(br.bound());
    }


    void add_bound(mpq v, unsigned j, bool is_lower, constraint * c) {
        literal l = literal::make_implied_literal(j, is_lower, v, c, m_var_infos[j].external_stack_level());
        push_literal_to_trail(l);
        m_var_infos[j].number_of_bound_propagations()++;
    }
    
    mpq value(const polynomial & p) const {
        mpq ret= p.m_a;
        for (const auto & t:p.m_coeffs)
            ret += t.coeff() * m_v[t.var()];
        return ret;
    }

    bool flip_coin() {
        return m_settings.random_next() % 2 == 0;
    }

    void pop_to_external_level() {
        while (m_decision_level > 0) {
            pop();
        }
    }

    void print_state_stats(std::ostream & out) const {
        static bool one_time_print = true;
        if (m_bounded_search_calls % 10 )
            return;
        out << "search_calls = " << m_bounded_search_calls << ", ";
        out << "vars = " << m_var_infos.size() << ",";
        out << "asserts = "<< m_asserts.size() << ", ";
        out << "lemmas = "  << m_lemmas.size() << ", ";
        out << "trail = " << m_trail.size() << ", props = " << m_number_of_constraints_tried_for_propagaton << ", ";
        out << "cnfls = " << m_number_of_conflicts << ", ";
        if (one_time_print && m_lemmas.size() >= 500) {
            print_state(out);
            one_time_print = false;
        }
    }

    
    lbool check() {
        init_search();
        TRACE("check_int", tout << "starting check" << "\n";);
        while (!m_stuck_state && !cancel()) {
            TRACE("cs_ch", tout << "inside loop\n";);
            lbool r = bounded_search();
            if (cancel()) {
                break;
            }
            if (r != lbool::l_undef) {
                TRACE("check_int", tout << "return " << (r == lbool::l_true ? "true" : "false") << "\n"; );
                pop_to_external_level();
                return r;
            }
            restart();
            simplify_problem();
            if (check_inconsistent()) {
                TRACE("check_int", tout << "return " << (r == lbool::l_true ? "true" : "false") << "\n"; );
                pop_to_external_level();
                return lbool::l_false;
            }
            gc();
            TRACE("check_int", tout << "continue\n"; print_state_stats(tout); );

        }
        TRACE("check_int", tout << "return undef\n";);
        pop_to_external_level();
        return lbool::l_undef;
    }

    unsigned find_unused_index() const {
        for (unsigned j = m_var_infos.size(); ; j++)
            if (m_user_vars_to_cut_solver_vars.find(j) == m_user_vars_to_cut_solver_vars.end())
                return j;
        
    }

    
    void init_search() {
        lp_assert(m_explanation.size() == 0);
        m_number_of_conflicts = 0;
        m_bounded_search_calls = 0;
        m_stuck_state = false;
        m_cancelled = false;
        for (constraint * c : m_asserts)
            m_active_set.add_constraint(c);
        for (auto & vi : m_var_infos)
            vi.number_of_bound_propagations() = 0;
        m_number_of_constraints_tried_for_propagaton = 0;
        m_pushes_to_trail = 0;
    }

    constraint* propagate_constraint(constraint* c) {
        m_number_of_constraints_tried_for_propagaton ++;
        lp_assert(c->is_ineq());
        TRACE("ba_int", trace_print_constraint(tout, c););
        // consider a special case for a constraint with just two variables
        unsigned the_only_unlim;
        int r = lower_analize(c, the_only_unlim);
        if (r == 0) {
            mpq b;
            lower(c->poly(), b);
            if (is_pos(b)) {
                TRACE("cs_inconsistent", tout << "incostistent constraint ";
                      trace_print_constraint(tout, c);
                      tout << "\nlevel = " << m_decision_level << std::endl;);
                return c;
            } 
            propagate_constraint_on_lower(c, b); 
        } else if (r == 1) {
            lp_assert(!lower_is_pos(c->poly()));
            propagate_constraint_only_one_unlim(c, the_only_unlim);
        }
        lp_assert(!lower_is_pos(c->poly()));
        return nullptr;
    }

    void print_trail(std::ostream & out) const { print_trail(out, m_trail.size()); }
    
    void print_trail(std::ostream & out, unsigned last_index) const {
        out << "trail\n";
        for (unsigned j = 0; j <= last_index && j < m_trail.size(); j++ ) {
            out << "offset = " << j << ", ";
            print_literal(out, m_trail[j]); 
        }
        out << "end of trail\n";
    }
    void print_state(std::ostream & out) const {
        out << "asserts total " << m_asserts.size() << "\n";
        for (const auto  i: m_asserts) {
            print_constraint(out, *i);
        }
        out << "end of constraints\n";
        out << "lemmas total " << m_lemmas.size() << "\n";
        for (const auto  i: m_lemmas) {
            print_constraint(out, *i);
        }
        out << "end of constraints\n";
        print_trail(out);
        out << "var_infos\n";
        for (const auto & v: m_var_infos) {
            if (v.is_active())
                print_var_info(out, v);
        }
        out << "end of var_infos\n";
        out << "level = " << m_decision_level << "\n";
        out << "end of state dump, bounded_search_calls = "  <<  m_bounded_search_calls << ", number_of_conflicts = " << m_number_of_conflicts << std::endl;
    }
    lbool bounded_search() {
        m_bounded_search_calls++;
        lbool is_sat = propagate_and_backjump_step();
        if (is_sat != lbool::l_undef) {
            TRACE("decide_int", tout << "returning " << (int)is_sat << "\n";);
            return is_sat;
        }
        gc();
        if (cancel())
            return lbool::l_undef;
        if (!decide()) {
            TRACE("decide_int", tout << "going to final_check()\n";);
            lbool is_sat = final_check();
            if (is_sat != lbool::l_undef) {
                return is_sat;
            }
        }
        TRACE("decide_int", tout << "returning undef\n";);
        return lbool::l_undef;
    }

    bool pick_bound_kind(unsigned j) {
        var_info & vi = m_var_infos[j];
        if (lower_bound_exists(vi) && upper_bound_exists(vi))
            return flip_coin();
        if (lower_bound_exists(vi))
            return true;
        lp_assert(upper_bound_exists(vi));
        return false;
    }
    
    bool decide() {
        int j = find_var_for_deciding();
        if (j < 0)
            return false;
        TRACE("decide_int", tout << "going to decide " << var_name(j) << " var index = " << j << "\n";
              tout << "domain = "; print_var_domain(tout, j); tout << ", m_decision_level="<<m_decision_level<< "\n";);
        decide_var_on_bound(j, pick_bound_kind(j));
        return true;
    }

    bool cancel() {
        if (m_cancelled)
            return true;
        if (m_settings.get_cancel_flag()) {
            m_cancelled = true;
            return true;
        }
        unsigned bound = m_asserts.size() * 200 /  (1 + m_settings.m_int_branch_cut_solver);
        if (m_trail.size()  > bound || m_number_of_conflicts > bound) {
            m_cancelled = true;
            return true;
        }
        return false;
    }

    bool cancel_when_propagation_speed_is_too_slow() {
        if (m_number_of_constraints_tried_for_propagaton >= 10000) {
            m_cancelled = m_pushes_to_trail <= 50;
            m_pushes_to_trail = 0;
            m_number_of_constraints_tried_for_propagaton = 0;
            return m_cancelled;
        }
        return false;
    }

    
    lbool propagate_and_backjump_step() {
        do {
            if (cancel_when_propagation_speed_is_too_slow())
                return lbool::l_undef;
            constraint* c = propagate();
            if (cancel())
                return lbool::l_undef;
            TRACE("cs_dec", tout << "trail = \n"; print_trail(tout); tout << "end of trail\n";);

            if (c != nullptr) {
                m_number_of_conflicts++;
                TRACE("propagate_and_backjump_step_int", tout << "incostistent_constraint "; trace_print_constraint(tout, c); tout << "m_number_of_conflicts = " << m_number_of_conflicts << std::endl; tout << "cut_solver_calls " << m_settings.st().m_cut_solver_calls << std::endl;);
                if (at_base_lvl()) {
                    fill_conflict_explanation(c);
                    return lbool::l_false;
                }
                handle_conflicting_cores(); // testing only
                resolve_conflict(c);
            }
        }
        while (!m_active_set.is_empty());

        return !all_vars_are_fixed()? lbool::l_undef :lbool::l_true;
    }

    bool decision_is_redundant_for_constraint(const polynomial& i, literal & l) const {
        const mpq & coeff = i.coeff(l.var());
        if (is_zero(coeff))
            return true;
        return is_pos(coeff)? ! l.is_lower(): l.is_lower();
    }

    bool is_divizible(const mpq & a, const mpq & b) const {
        lp_assert(!is_zero(b));
        return is_zero(a % b);
    }
    
    void create_div_ndiv_parts_for_tightening(const polynomial & p, const mpq & coeff, polynomial & div_part, polynomial & ndiv_part) {
        for (const auto &m : p.m_coeffs) {
            if (is_divizible(m.coeff(), coeff)){
                div_part.m_coeffs.push_back(m);
            } else {
                ndiv_part.m_coeffs.push_back(m);
            }
        }

        TRACE("tight",
              tout << "div_part = " << pp_poly(*this, div_part) << "\n";
              tout << "ndiv_part = " << pp_poly(*this, ndiv_part) << "\n";);
    }


    void add_tight_constr_of_literal(polynomial &ndiv_part,
                                     const mpq & c,
                                     literal &l) {
        lp_assert(is_pos(c));
        ndiv_part.add(c, m_trail[l.decision_context_index()].tight_constr()->poly());
        lp_assert(is_zero(ndiv_part.coeff(l.var())));
        TRACE("tight", tout << "ndiv_part = " << pp_poly(*this, ndiv_part) << "\n";);
    }

    void decided_lower(const mpq & a,
                       const mpq & c,
                       polynomial &div_part,
                       polynomial &ndiv_part,
                       literal &l) {
        mpq k = is_pos(a)?ceil( c / a): floor(c / a);
        ndiv_part += monomial(-c, l.var()); // it will be moved to div_part
        mpq a_k = a * k;
        mpq m = a_k - c;
        TRACE("tight", tout << "c = " << c << ", a = " << a <<
              ", c / a = " << c/a << ", k = " <<
              k << ", a * k = " << a * k << ", m = " << m << "\n"; );  
        lp_assert(!is_neg(m));
        create_tight_constr_under_literal(l.decision_context_index());
        const literal & lex = m_trail[l.decision_context_index()];
        lp_assert(lex.var() == l.var());
        for (const monomial & n : lex.tight_constr()->poly().coeffs()) {
            if (n.var() == l.var()) {
                lp_assert(n.coeff() == one_of_type<mpq>());
                div_part += monomial(a_k, l.var());
            } else {
                ndiv_part += monomial(m * n.coeff(), n.var());
            }
        }
        ndiv_part += m * lex.tight_constr()->poly().m_a;
        TRACE("tight", tout << "Decided-Lower ";
              tout << "div_part = " << pp_poly(*this, div_part) << "\n";
              tout << "ndiv_part = " << pp_poly(*this, ndiv_part) << "\n";);
    }

    void decided_upper(const mpq & a,
                       const mpq & c,
                       polynomial &div_part,
                       polynomial &r,
                       literal &l) {
        // we would like to have c - ak > 0, or ak < c
        mpq k = is_pos(a)? floor( c / a): ceil(c / a);
        r += monomial(-c, l.var()); // it will be moved to div_part
        
        mpq a_k = a * k;
        mpq m = c - a_k;
        TRACE("tight", tout << "c = " << c << ", a = " << a <<
              ", c / a = " << c/a << ", k = " <<
              k << ", a * k = " << a * k << ", m = " << m << "\n"; );  
        lp_assert(!is_neg(m));
        create_tight_constr_under_literal(l.decision_context_index());
        const literal & lex = m_trail[l.decision_context_index()];
        lp_assert(lex.var() == l.var());
        for (const monomial & n : lex.tight_constr()->poly().coeffs()) {
            if (n.var() == l.var()) {
                lp_assert(n.coeff() == -one_of_type<mpq>());
                div_part += monomial(a_k, l.var());
            } else {
                r += monomial(m * n.coeff(), n.var());
            }
        }
        r += m * lex.tight_constr()->poly().m_a;
        TRACE("tight", tout << "Decided-Lower ";
              tout << "div_part = " << pp_poly(*this, div_part) << "\n";
              tout << "r = " << pp_poly(*this, r) << "\n";);
    }

    // returns true iff there was a change
    bool tighten_on_literal(const mpq & a,
                            polynomial & div_part,
                            polynomial & ndiv_part,
                            int index_of_literal) {
        bool change = false;
        literal & l = m_trail[index_of_literal];
        if (l.tight_constr() == nullptr) {
            create_tight_constr_under_literal(index_of_literal);
        }
        TRACE("tight",
              tout << "index_of_literal = " << index_of_literal << ", ";
              print_literal(tout, m_trail[index_of_literal]););
        if (l.is_implied()) { // Resolve-Implied
            change = resolve(ndiv_part, l.var(), !l.is_lower(), l.tight_constr()->poly());
            TRACE("tight", tout << "after resolve ndiv_part = " << pp_poly(*this, ndiv_part) << "\n";);
        } else { 
            create_tight_constr_under_literal(l.decision_context_index());
            TRACE("tight", 
                  tout << "index_of_literal = " << index_of_literal << ", ";
                  print_literal(tout, m_trail[index_of_literal]); tout << "\n";
                  tout << "div_part = " << pp_poly(*this, div_part) << "\n";
                  tout << "ndiv_part = " << pp_poly(*this, ndiv_part) << "\n";
                  tout << "a = " << a << "\n";
                  );
            mpq c = ndiv_part.coeff(l.var());
            if (is_zero(c))
                return false;
            if (l.is_lower()) {
                if (is_neg(c))
                    add_tight_constr_of_literal(ndiv_part, -c, l);
                else 
                    decided_lower(a, c, div_part, ndiv_part, l);
            } else {
                if (is_pos(c)) // Decided-Upper-Pos
                    add_tight_constr_of_literal(ndiv_part, c, l);
                else
                    decided_upper(a, c, div_part, ndiv_part, l);
            }
            change = true;
        }
        return change;
    }

    void eliminate_ndiv_part_monomials(const mpq& a, polynomial & div_part, polynomial& ndiv_part, unsigned index_of_literal) {
        if (ndiv_part.number_of_monomials() == 0)
            return;
        int k = index_of_literal - 1;
        lp_assert(k >= 0);
        literal& l = m_trail[index_of_literal];
        while (ndiv_part.number_of_monomials() > 0) {
            if (tighten_on_literal(a, div_part, ndiv_part, k)) {
                literal & lk = m_trail[k];
                l.tight_constr()->add_predecessor(
                    lk.is_implied()?
                    lk.tight_constr() :
                    m_trail[lk.decision_context_index()].tight_constr()
                                                  );
            }
            k--;
        }
    }
    
    // see page 88 of Cutting to Chase
    void tighten(constraint * c,
                 unsigned j_of_var,
                 const mpq& a,
                 unsigned index_of_literal) {
        polynomial div_part, ndiv_part;
        ndiv_part.m_a = c->poly().m_a;
        create_div_ndiv_parts_for_tightening(c->poly(), a, div_part, ndiv_part);
        eliminate_ndiv_part_monomials(a, div_part, ndiv_part, index_of_literal);
        mpq abs_a = abs(a);
        polynomial & p = c->poly();
        p.clear();
        for (const auto & m : div_part.m_coeffs) {
            p.m_coeffs.push_back(monomial(m.coeff() / abs_a, m.var()));
        }
        p.m_a = ceil(ndiv_part.m_a / abs_a);
        lp_assert(p.m_a >= ndiv_part.m_a / abs_a);
        TRACE("tight", tout << "index_of_literal = " << index_of_literal << ", got tight p = " << pp_poly(*this, p) << "\n";);
    }

    void create_tight_constr_under_literal(unsigned index_of_literal) {
        literal & l = m_trail[index_of_literal];
        if (l.tight_constr() != nullptr)
            return;
        if (l.is_decided()) {
            create_tight_constr_under_literal(l.decision_context_index());
            return;
        }
        TRACE("tight", tout << "index_of_literal = " << index_of_literal << "\n";);
        const_constr*  c = l.cnstr();
        lp_assert(c->is_ineq());
        unsigned j = l.var();
        const mpq& a = c->poly().coeff(j);
        lp_assert(!is_zero(a));
        if (a == one_of_type<mpq>() || a == - one_of_type<mpq>()) {
            l.tight_constr() = l.cnstr();
            return;
        }
        l.tight_constr() = constraint::make_ineq_constraint( m_max_constraint_id++,
                                                             c->poly(),
                                                             c->predecessors());
        l.tight_constr()->add_predecessor(c);
        tighten(l.tight_constr(), j, a, index_of_literal);
        add_lemma_as_not_active(l.tight_constr());
    }

    void backjump(unsigned index_of_literal,
                  bool lemma_has_been_modified,
                  constraint* lemma,
                  constraint * orig_conflict) {
        polynomial &p = lemma->poly();
        lp_assert(m_trail[index_of_literal].is_decided());
        unsigned j = m_trail[index_of_literal].var();
        while(m_trail.size() > index_of_literal) {  pop(); }
        lp_assert(m_trail.size() == index_of_literal);
        bound_result br = bound_on_polynomial(p, p.coeff(j), j);

        TRACE("int_backjump", br.print(tout);
              print_var_info(tout, j);
              tout << "p = " << pp_poly(*this, p) << "\n";);
        if (!improves(j, br)) {
            CTRACE("int_backjump", lp_settings::ddd, br.print(tout); tout << "\nimproves is false\n";
                   tout << "var info after pop = ";  print_var_info(tout, j););
            if (lemma_has_been_modified)
                add_lemma(lemma);
            else {
                m_active_set.add_constraint(orig_conflict);
            }
        } else {
            constraint *c;
            if (lemma_has_been_modified) {
                c = lemma;
                add_lemma_as_not_active(lemma);
            } else {
                c = orig_conflict;
            }
            add_bound(br.bound(), j, br.m_type == bound_type::LOWER, c);
            restrict_var_domain_with_bound_result(j, br, m_trail.size() - 1);
            lp_assert(!m_var_infos[j].domain().is_empty());
            TRACE("int_backjump", tout << "done resolving:\nvar info after restricton = ";
                  print_var_info(tout, j);
                  tout << "new literal = "; print_literal(tout, m_trail.back()););
            lp_assert(!lower_is_pos(c->poly()));
        }
    }

    void print_resolvent(std::ostream& out, const polynomial& p, literal &l) const {
        out << "p = "; trace_print_polynomial(out, p);
        mpq rr;
        bool bb = lower(p, rr);
        if (!bb) {
            out << "\nlower(p) is not defined\n";
        } else {
            out << "\nlower(p) = " << rr << "\n";
        }
        
        out << "tight_constr = " << pp_constraint(*this, *l.tight_constr()) << "\n";
        out << "constraint = " << pp_constraint(*this, *l.cnstr()) << "\n";
        out << "var domains" << "\n";
        for (auto & m : l.tight_constr()->poly().coeffs()) {
            out <<  "var = " << m.var() << " " << var_name(m.var()) << " ";
            print_var_domain(out, m.var());
            out << " ";
        }
        out << "\n";
    }

    void trace_resolve_print(std::ostream& out, const polynomial & p, literal & l, unsigned index_of_literal) {
        out << "index_of_literal = " << index_of_literal <<", p = " << pp_poly(*this, p) << "\n";
        out << "l = ";  print_literal(out, l);
        out << "lower(p) = " << lower_no_check(p) << "\n";
        for (auto & m : p.coeffs()) {
            out <<  var_name(m.var()) << " ";
            print_var_domain(out, m.var());
            out << " ";
        }
        out << "\nm_decision_level = " << m_decision_level << "\n";
    }


    bool resolve_decided_literal(unsigned index_of_literal, literal& l, bool lemma_has_been_modified, constraint* lemma, constraint *orig_conflict) {
        if (decision_is_redundant_for_constraint(lemma->poly(), l)) {
            do { pop();} while(m_trail.size() > index_of_literal);
            lp_assert(m_trail.size() == index_of_literal);
            TRACE("resolve_decided_literal", tout << "n "; print_literal(tout, l);  if (m_decision_level == 0) tout << ", done resolving";);
            lp_assert(lower_is_pos(lemma->poly()));
            return m_decision_level == 0;
        }
        handle_conflicting_cores();
        backjump(index_of_literal, lemma_has_been_modified, lemma, orig_conflict);
        return true; // done
    }

    // applying Resolve rule
    void resolve_implied_literal(literal & l,
                                 bool &lemma_has_been_modified,
                                 constraint* lemma) {
        polynomial & p = lemma->poly();
        lp_assert(lower_is_pos(p));
        if (!resolve(p, l.var(), !l.is_lower(), l.tight_constr()->poly()))
            return;
        lemma_has_been_modified = true;
        lemma->add_predecessor(l.tight_constr());
        TRACE("resolve_implied_literal", tout << "resolved p: "; print_resolvent(tout, p, l););
        lp_assert(lower_is_pos(p));
    }
    
    // returns true iff resolved
    bool resolve_conflict_for_inequality_on_trail_element(unsigned index_of_literal, bool & lemma_has_been_modified, constraint* lemma, constraint * orig_conflict) {
        lp_assert(lower_is_pos(lemma->poly()));
        literal & l = m_trail[index_of_literal];
        TRACE("resolve_conflict_for_inequality_on_trail_element",
              tout << "index_of_literal = " << index_of_literal <<", p = " << pp_poly(*this, lemma->poly()) << "\n";
              tout << "\nm_decision_level = " << m_decision_level << "\n";
              print_literal(tout, l););
        if (l.is_decided()) {
            return resolve_decided_literal(index_of_literal, l, lemma_has_been_modified, lemma, orig_conflict);
        } else {
            create_tight_constr_under_literal(index_of_literal);
            resolve_implied_literal(l, lemma_has_been_modified, lemma);
            return false;
        }
    }

    bool lower_is_pos(const_constr* c) const { return lower_is_pos(c->poly()); }
    
    bool lower_is_pos(const polynomial & p) const {
        mpq b;
        bool r = lower(p, b);
        return r && is_pos(b);
    }

    mpq lower_no_check(const polynomial & p) const {
        mpq b;
#if Z3DEBUG
        bool r =
#endif
            lower(p, b);
#if Z3DEBUG
        lp_assert(r);
#endif
        return b;
    }

    
    void resolve_conflict_for_inequality(constraint * c) {
        // Create a new constraint, almost copy of "c", that becomes a lemma and could be modified later
        constraint *lemma = constraint::make_ineq_lemma(m_max_constraint_id++, c->poly());
        lemma->predecessors() = c->predecessors(); // copy predecessors
        lemma->add_predecessor(c); // and add c

        TRACE("resolve_conflict_for_inequality", print_constraint(tout, *lemma););
        lp_assert(lower_is_pos(lemma->poly()));
        bool done = false;
        unsigned j = m_trail.size() - 1;
        bool lemma_has_been_modified = false;
        unsigned number_of_lemmas = m_lemmas.size();
        while (!done) {
            if (cancel()) {
                return;
            }
            done = resolve_conflict_for_inequality_on_trail_element(j--, lemma_has_been_modified, lemma, c);
            if (j >= m_trail.size()) {
                TRACE("resolve_conflict_for_inequality", tout << "adjust j";);
                lp_assert(m_trail.size());
                j = m_trail.size() - 1;
            }
        }
        
        if (number_of_lemmas == m_lemmas.size()) {
            if (lemma_has_been_modified)
                add_lemma_as_not_active(lemma);
            else {
                delete lemma;
            }
        }
    }

    void resolve_conflict(constraint * i) {
        lp_assert(!at_base_lvl());
        TRACE("int_resolve_confl", tout << "inconstistent_constraint = ";
              print_constraint(tout, *i); print_state(tout););
        if (i->is_ineq()) {
            resolve_conflict_for_inequality(i);
        } else {
            lp_assert(false); // not implemented
        }
    }


    void print_scope(std::ostream& out) const {
        for (const scope & s : m_scopes) {
            out <<  "asserts_size = " << s.m_asserts_size;
            out << ", lemmas_size = " << s.m_lemmas_size << "\n";
            out << ", trail_size = " << s.m_trail_size << "\n";
        }
    }

    void remove_active_flag_from_constraints_in_active_set() {
        for (auto c : m_active_set.cs()) {
            c->remove_active_flag();
        }
    }

    void set_active_flag_for_constraints_in_active_set() {
        for (auto c : m_active_set.cs()) {
            c->set_active_flag();
        }
    }

public:
    void push() {
        m_scopes.push_back(scope(m_asserts.size(), m_lemmas.size(), m_trail.size()));
        TRACE("pp_cs", tout << "level =  " << m_scopes.size() << ", trail size = " << m_trail.size(););
    }


    void pop_constraints(unsigned n_asserts, unsigned n_lemmas) {
        if (n_asserts >= m_asserts.size())
            return; // only shrink the lemmas if asserts are shrunk
        while (m_asserts.size() > n_asserts) {
            constraint * i = m_asserts.back();;
            for (auto & p: i->poly().m_coeffs) {
                m_var_infos[p.var()].remove_depended_constraint(i);
            }
            m_active_set.remove_constraint(i);
            delete i;
            m_asserts.pop_back();
        }

        while (m_lemmas.size() > n_lemmas) {
            constraint * i = m_lemmas.back();;
            for (auto & p: i->poly().m_coeffs) {
                m_var_infos[p.var()].remove_depended_constraint(i);
            }
            m_active_set.remove_constraint(i);
            delete i;
            m_lemmas.pop_back();
        }
    }

public:
    void pop(unsigned k) {
        unsigned new_scope_size = m_scopes.size() - k;
        scope s = m_scopes[new_scope_size];
        m_scopes.shrink(new_scope_size);
        for (unsigned j = m_trail.size(); j-- > s.m_trail_size; ) {
            literal& lit = m_trail[j];
            if (lit.is_decided())
                m_decision_level--;
            var_info & vi = m_var_infos[lit.var()];
            if (vi.external_stack_level() != lit.prev_var_level())
                vi.pop(1, lit.prev_var_level());
            m_trail.pop_back();
        }
        pop_constraints(s.m_asserts_size, s.m_lemmas_size);
        lp_assert(var_infos_are_correct());
    }
public:    
    void pop() { pop(1); }
    
    cut_solver(std::function<std::string (unsigned)> var_name_function,
               std::function<void (unsigned, std::ostream &)> print_constraint_function,
               std::function<unsigned ()>                     number_of_variables_function,         
               std::function<const impq &(unsigned)>         var_value_function,         
               lp_settings & settings
               ) : m_var_name_function(var_name_function),
                   m_print_constraint_function(print_constraint_function),
                   m_number_of_variables_function(number_of_variables_function),
                   m_var_value_function(var_value_function),
                   m_settings(settings),
                   m_max_constraint_id(0),
                   m_decision_level(0)
    {}


    int find_conflicting_core(const constraint* &lower, const constraint* & upper) const {
        for (unsigned j = 0; j < m_var_infos.size(); j++) {
            if (is_cc(j, lower, upper))
                return j;
        }
        return -1;
    }

    void list_confl_cores() {
        const constraint* lower; const constraint* upper;
        for (unsigned j = 0; j < m_var_infos.size(); j++) {
            if (is_cc(j, lower, upper)) {
                std::cout << "confl core = "; print_var_info(std::cout, j);
                std::cout << "lower = "; print_constraint(std::cout, *lower);
                std::cout << "upper = "; print_constraint(std::cout, *upper);
            }
        }
    }
    
    void handle_conflicting_cores() {
        return;
        const constraint* lower;
        const constraint* upper;
        int j = find_conflicting_core(lower, upper);
       
        if (j >=0) {
            std::cout << "confl core = "; print_var_info(std::cout, j);
            std::cout << "lower = "; print_constraint(std::cout, *lower);
            std::cout << "upper = "; print_constraint(std::cout, *upper);
            lp_assert(false); // not implemented
        }
    }

    constraint* find_constraint_to_propagate(unsigned rand) {
        handle_conflicting_cores();
        return m_active_set.remove_random_constraint(rand);
    }
    
    // returns nullptr if there is no conflict, or a conflict constraint otherwise
    constraint* propagate_constraints_on_active_set() {
        constraint *c;
        while ((c = find_constraint_to_propagate(m_settings.random_next())) != nullptr) {
            c = propagate_constraint(c);
            if (cancel()) {
                return nullptr;
            }
            if (c != nullptr) {
                return c;
            }
        }
        return nullptr;
    }


    // returns -1 if there is no conflict and the index of the conflict constraint otherwise
    constraint * propagate() {
        constraint* cnf = propagate_constraints_on_active_set();;
        if (cnf != nullptr){
            lp_assert(lower_is_pos(cnf));
            return cnf;
        }
        handle_conflicting_cores();
        return nullptr;
    }


    // walk the trail backward and find the last implied bound on j (of the right kind)
    int find_literal_index_after(unsigned j, bool is_lower, unsigned trail_lim) const {
        for (unsigned k = trail_lim; k-- > 0;) {
            const auto & l = m_trail[k];
            lp_assert(!l.is_decided());
            if (l.var() == j && l.is_lower() == is_lower)
                return k;
        }
        TRACE("find_literal", tout << "cannot find a literal for " << var_name(j)<<  " j = " << j << " is_lower = " << is_lower << ", trail_lim = " << trail_lim;);
        return -1;
    }
    
    void decide_var_on_bound(unsigned j, bool decide_on_lower) {
        mpq b;
        vector<monomial> lhs;
        unsigned decision_context_index;
        var_info & vi = m_var_infos[j];
        unsigned var_level = vi.external_stack_level();
        push();    
        if (decide_on_lower) {
            vi.domain().get_lower_bound_with_expl(b, decision_context_index);
            vi.intersect_with_upper_bound(b, m_trail.size(), m_scopes.size());
        }
        else {
            vi.domain().get_upper_bound_with_expl(b, decision_context_index);
            vi.intersect_with_lower_bound(b, m_trail.size(), m_scopes.size());
        }
        if (j >= m_v.size())
            m_v.resize(j + 1);
        m_v[j] = b;
        TRACE("decide_var_on_bound", tout<< "j="<< j<<" ";print_var_info(tout, j););
        add_changed_var(j);
        m_decision_level++;
        literal nl = literal::make_decided_literal(j, !decide_on_lower, b, decision_context_index, var_level);
        push_literal_to_trail(nl);
    }

    bool consistent(const_constr * i) const {
        // an option could be to check that upper(i.poly()) <= 0
        bool ret = value(i->poly()) <= zero_of_type<mpq>();
        CTRACE("cut_solver_state_inconsistent", !ret,
               tout << "inconsistent constraint " << pp_constraint(*this, *i) << "\n";
               tout << "value = " << value(i->poly()) << '\n';);
        return ret;
    }

    int find_var_for_deciding() const {
        unsigned j = m_settings.random_next() % m_var_infos.size();
        
        for (unsigned k = 0; k < m_var_infos.size(); k++, j++) {
            if (j == m_var_infos.size())
                j = 0;
            const auto & d = m_var_infos[j].domain();
            lp_assert(!d.is_empty());
            if (!d.is_fixed() && (lower_bound_exists(d) || upper_bound_exists(d)))
                return j;
        }

        // start using the rational solution for bounds and branches
        
        return -1;
    }

    bool there_is_var_with_empty_domain() const {
        for (unsigned j = 0; j < m_var_infos.size(); j++) {
            const auto & d = m_var_infos[j].domain();
            if (d.is_empty())
                return true;
        }
        return false;
    }
    
    bool all_vars_are_fixed() const {
        for (unsigned j = 0; j < m_var_infos.size(); j++) {
            if (m_var_infos[j].is_active() && ! m_var_infos[j].is_fixed())
                return false;
        }
        return true;
    }

    bool consistent() const {
        if (!all_vars_are_fixed()) {
            // this check could be removed if we use upper bound to check if an constraint holds
            return false; // ignore the variables values and only return true if every variable is fixed
        }
    
        for (const_constr* i : m_asserts) {
            if (!consistent(i))
                return false;
        }
        return true;
    }


    void simplify_ineq(polynomial & p) const {
        TRACE("simplify_ineq_int", tout << "p = " << pp_poly(*this, p) << "\n";);
        auto & ms = p.m_coeffs;
        lp_assert(ms.size());
        mpq g;
        if (ms.size() == 1) {
            g = abs(ms[0].coeff());
        } else {
            g = gcd(ms[0].coeff(), ms[1].coeff());
            for (unsigned j = 2; j < ms.size(); j++) {
                g = gcd(g, ms[j].coeff());
            }
            lp_assert(is_pos(g));
        }
        if (g != one_of_type<mpq>()) {
            for (auto & m : ms)
                m.coeff() /= g;
            p.m_a = ceil(p.m_a /g);
        }
        TRACE("simplify_ineq_int", tout << "p = " << pp_poly(*this, p) << "\n";);
    }

    void add_lemma_common(constraint* lemma) {
        m_lemmas.push_back(lemma);
        polynomial & p = lemma->poly();
        simplify_ineq(p);
        for (const auto & m : p.coeffs()) {
            m_var_infos[m.var()].add_dependent_constraint(lemma, is_pos(m.coeff())? bound_type::UPPER: bound_type::LOWER);
        }
    }

    void add_lemma_as_not_active(constraint * lemma) {
        add_lemma_common(lemma);
        TRACE("add_lemma_int",  trace_print_constraint(tout, lemma););
    }
    
    void add_lemma(constraint * lemma) {
        add_lemma_common(lemma);
        m_active_set.add_constraint(lemma);
        TRACE("add_lemma_int",  trace_print_constraint(tout, lemma););
    }

    
    unsigned add_ineq(const vector<monomial> & lhs,
                      const mpq& free_coeff,
                      svector<constraint_index> origins) {
        lp_assert(lhs_is_int(lhs));
        lp_assert(is_int(free_coeff));
        for (auto & p : lhs) {
            if (p.var() >= m_var_infos.size()) {
                m_var_infos.resize(m_number_of_variables_function());
            }

            var_info & vi = m_var_infos[p.var()];

            if (!vi.is_active()) {
                vi.activate(p.var());
            }
        }
        
        constraint * c = constraint::make_ineq_assert(m_max_constraint_id++, lhs, free_coeff,origins);
        m_asserts.push_back(c);
        add_constraint_to_dependend_for_its_vars(c);
        m_active_set.add_constraint(c);

        TRACE("add_ineq_int",
              tout << "explanation :";
              for (auto i: origins) {
                  m_print_constraint_function(i, tout);
                  tout << "\n";
              });

        TRACE("add_ineq_int", tout << "m_asserts[" << m_asserts.size() - 1 << "] =  ";
              print_constraint(tout, *m_asserts.back()); tout << "\n";);
        
        return m_asserts.size() - 1;
    }
    

    void add_constraint_to_dependend_for_its_vars(constraint * c) {
        for (auto & p : c->poly().coeffs()) {
            m_var_infos[p.var()].add_dependent_constraint(c, is_pos(p.coeff())? bound_type::UPPER : bound_type::LOWER);
        }
    }

    bool var_has_no_bounds(const var_info& vi) const {
        return !lower_bound_exists(vi) && !upper_bound_exists(vi);
    }
};

inline polynomial operator*(const mpq & a, polynomial & p) {
    polynomial ret;
    ret.m_a = p.m_a * a;
    
    for (const auto & t: p.m_coeffs)
        ret.m_coeffs.push_back(monomial(a * t.coeff(), t.var()));
    
    return ret;
}
}
