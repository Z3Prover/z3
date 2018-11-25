/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    euclidean_solver.cpp

Abstract:

    Euclidean Solver with support for explanations.

Author:

    Leonardo de Moura (leonardo) 2011-07-08.

Revision History:

--*/
#include "math/euclid/euclidean_solver.h"
#include "util/numeral_buffer.h"
#include "util/heap.h"

struct euclidean_solver::imp {
    typedef unsigned                             var; 
    typedef unsigned                             justification;
    typedef unsynch_mpq_manager                  numeral_manager;
    typedef numeral_buffer<mpz, numeral_manager> mpz_buffer;
    typedef numeral_buffer<mpq, numeral_manager> mpq_buffer;
    typedef svector<justification>               justification_vector;
    static const justification                   null_justification = UINT_MAX;
#define null_var    UINT_MAX
#define null_eq_idx UINT_MAX
    typedef svector<var>                         var_vector;
    typedef svector<mpz>                         mpz_vector;
    typedef svector<mpq>                         mpq_vector;

    struct elim_order_lt {
        unsigned_vector & m_solved;
        elim_order_lt(unsigned_vector & s):m_solved(s) {}
        bool operator()(var x1, var x2) const { return m_solved[x1] < m_solved[x2]; }
    };

    typedef heap<elim_order_lt>                  var_queue; // queue used for scheduling variables for applying substitution.

    static unsigned pos(unsigned_vector const & xs, unsigned x_i) {
        if (xs.empty())
            return UINT_MAX;
        int low  = 0;
        int high = xs.size() - 1;
        while (true) {
            int mid   = low + ((high - low) / 2);
            var x_mid = xs[mid];
            if (x_i > x_mid) {
                low = mid + 1;
                if (low > high)
                    return UINT_MAX;
            }
            else if (x_i < x_mid) {
                high = mid - 1;
                if (low > high)
                    return UINT_MAX;
            }
            else {
                return mid;
            }
        }
    }
    
    /**
       Equation as[0]*xs[0] + ... + as[n-1]*xs[n-1] + c = 0 with justification bs[0]*js[0] + ... + bs[m-1]*js[m-1]
    */
    struct equation {
        mpz_vector            m_as;
        var_vector            m_xs;
        mpz                   m_c;
        // justification
        mpq_vector            m_bs;
        justification_vector  m_js;

        unsigned size() const { return m_xs.size(); }
        unsigned js_size() const { return m_js.size(); }
        var x(unsigned i) const { return m_xs[i]; }
        var & x(unsigned i) { return m_xs[i]; }
        mpz const & a(unsigned i) const { return m_as[i]; }
        mpz & a(unsigned i) { return m_as[i]; }
        mpz const & c() const { return m_c; }
        mpz & c() { return m_c; }
        var j(unsigned i) const { return m_js[i]; }
        var & j(unsigned i) { return m_js[i]; }
        mpq const & b(unsigned i) const { return m_bs[i]; }
        mpq & b(unsigned i) { return m_bs[i]; }

        unsigned pos_x(unsigned x_i) const { return pos(m_xs, x_i); }
    };
    
    typedef ptr_vector<equation>   equations;
    typedef svector<unsigned>      occs;

    numeral_manager *  m_manager;
    bool               m_owns_m;

    equations          m_equations;
    equations          m_solution;
    
    svector<bool>      m_parameter;
    unsigned_vector    m_solved; // null_eq_idx if var is not solved, otherwise the position in m_solution
    vector<occs>       m_occs; // occurrences of the variable in m_equations.
    
    unsigned           m_inconsistent; // null_eq_idx if not inconsistent, otherwise it is the index of an unsatisfiable equality in m_equations.
    unsigned           m_next_justification;
    mpz_buffer         m_decompose_buffer;
    mpz_buffer         m_as_buffer;
    mpq_buffer         m_bs_buffer;

    var_vector         m_tmp_xs;
    mpz_buffer         m_tmp_as;
    mpq_buffer         m_tmp_bs;
    
    var_vector         m_norm_xs_vector;
    mpz_vector         m_norm_as_vector;
    mpq_vector         m_norm_bs_vector;

    var_queue          m_var_queue;

    // next candidate
    unsigned           m_next_eq;
    var                m_next_x;
    mpz                m_next_a;
    bool               m_next_pos_a;

    numeral_manager & m() const { return *m_manager; }

    bool solved(var x) const { return m_solved[x] != null_eq_idx; }

    template<typename Numeral>
    void sort_core(svector<Numeral> & as, unsigned_vector & xs, numeral_buffer<Numeral, numeral_manager> & buffer) {
        std::sort(xs.begin(), xs.end());
        unsigned num = as.size();
        for (unsigned i = 0; i < num; i++) {
            m().swap(as[i], buffer[xs[i]]);
        }
    }
    
    template<typename Numeral>
    void sort(svector<Numeral> & as, unsigned_vector & xs, numeral_buffer<Numeral, numeral_manager> & buffer) {
        unsigned num = as.size();
        for (unsigned i = 0; i < num; i++) {
            m().set(buffer[xs[i]], as[i]);
        }
        sort_core(as, xs, buffer);
    }

    equation * mk_eq(unsigned num, mpz const * as, var const * xs, mpz const & c, unsigned num_js, mpq const * bs, justification const * js,
                     bool sort = true) {
        equation * new_eq = alloc(equation);
        for (unsigned i = 0; i < num; i++) {
            m().set(m_as_buffer[xs[i]], as[i]);
            new_eq->m_as.push_back(mpz());
            new_eq->m_xs.push_back(xs[i]);
        }
        sort_core(new_eq->m_as, new_eq->m_xs, m_as_buffer);
        m().set(new_eq->m_c, c);
        for (unsigned i = 0; i < num_js; i++) {
            m().set(m_bs_buffer[js[i]], bs[i]);
            new_eq->m_bs.push_back(mpq());
            new_eq->m_js.push_back(js[i]);
        }
        if (sort)
            sort_core(new_eq->m_bs, new_eq->m_js, m_bs_buffer);
        return new_eq;
    }

    template<typename Numeral>
    void div(svector<Numeral> & as, mpz const & g) {
        unsigned n = as.size();
        for (unsigned i = 0; i < n; i++)
            m().div(as[i], g, as[i]);
    }

    void normalize_eq(unsigned eq_idx) {
        if (inconsistent())
            return;
        equation & eq = *(m_equations[eq_idx]);
        TRACE("euclidean_solver", tout << "normalizing:\n"; display(tout, eq); tout << "\n";);
        unsigned num = eq.size();
        if (num == 0) {
            // c == 0 inconsistency
            if (!m().is_zero(eq.c())) {
                TRACE("euclidean_solver", tout << "c = 0 inconsistency detected\n";);
                m_inconsistent = eq_idx;
            }
            else {
                del_eq(&eq);
                m_equations[eq_idx] = 0;
            }
            return;
        }
        
        mpz g;
        mpz a;
        m().set(g, eq.a(0));
        m().abs(g);
        for (unsigned i = 1; i < num; i++) {
            if (m().is_one(g))
                break;
            m().set(a, eq.a(i));
            m().abs(a);
            m().gcd(g, a, g);
        }
        if (m().is_one(g))
            return;
        if (!m().divides(g, eq.c())) {
            // g does not divide c
            TRACE("euclidean_solver", tout << "gcd inconsistency detected\n";);
            m_inconsistent = eq_idx;
            return;
        }
        div(eq.m_as, g);
        div(eq.m_bs, g);
        m().del(g);
        m().del(a);
        TRACE("euclidean_solver", tout << "after normalization:\n"; display(tout, eq); tout << "\n";);
    }

    bool is_better(mpz const & a, var x, unsigned eq_sz) {
        SASSERT(m().is_pos(a));
        if (m_next_x == null_var)
            return true;
        if (m().lt(a, m_next_a))
            return true;
        if (m().lt(m_next_a, a))
            return false;
        if (m_occs[x].size() < m_occs[m_next_x].size())
            return true;
        if (m_occs[x].size() > m_occs[m_next_x].size())
            return false;
        return eq_sz < m_equations[m_next_eq]->size();
    }

    void updt_next_candidate(unsigned eq_idx) {
        if (!m_equations[eq_idx])
            return;
        mpz abs_a;
        equation const & eq = *(m_equations[eq_idx]);
        unsigned num = eq.size();
        for (unsigned i = 0; i < num; i++) {
            mpz const & a = eq.a(i);
            m().set(abs_a, a);
            m().abs(abs_a);
            if (is_better(abs_a, eq.x(i), num)) {
                m().set(m_next_a, abs_a);
                m_next_x  = eq.x(i);
                m_next_eq = eq_idx;
                m_next_pos_a = m().is_pos(a);
            } 
        }
        m().del(abs_a);
    }
    
    /**
       \brief Select next variable to be eliminated.
       Return false if there is not variable to eliminate.
       
       The result is in
       m_next_x   variable to be eliminated
       m_next_eq  id of the equation containing x
       m_next_a   absolute value of the coefficient of x in eq.
       m_next_pos_a  true if the coefficient of x is positive in eq.
    */
    bool select_next_var() {
        while (!m_equations.empty() && m_equations.back() == 0)
            m_equations.pop_back();
        if (m_equations.empty())
            return false;
        SASSERT(!m_equations.empty() && m_equations.back() != 0);
        m_next_x = null_var;
        unsigned eq_idx = m_equations.size();
        while (eq_idx > 0) {
            --eq_idx;
            updt_next_candidate(eq_idx);
            // stop as soon as possible
            // TODO: use heuristics
            if (m_next_x != null_var && m().is_one(m_next_a))
                return true; 
        }
        CTRACE("euclidean_solver_bug", m_next_x == null_var, display(tout););
        SASSERT(m_next_x != null_var);
        return true;
    }

    template<typename Numeral>
    void del_nums(svector<Numeral> & as) {
        unsigned sz = as.size();
        for (unsigned i = 0; i < sz; i++)
            m().del(as[i]);
        as.reset();
    }
    
    void del_eq(equation * eq) {
        m().del(eq->c());
        del_nums(eq->m_as);
        del_nums(eq->m_bs);
        dealloc(eq);
    }

    void del_equations(equations & eqs) {
        unsigned sz = eqs.size();
        for (unsigned i = 0; i < sz; i++) {
            if (eqs[i]) 
                del_eq(eqs[i]);
        }
    }

    /**
       \brief Store the "solved" variables in xs into m_var_queue.
    */
    void schedule_var_subst(unsigned num, var const * xs) {
        for (unsigned i = 0; i < num; i++) {
            if (solved(xs[i]))
                m_var_queue.insert(xs[i]);
        }
    }

    void schedule_var_subst(var_vector const & xs) {
        schedule_var_subst(xs.size(), xs.c_ptr());
    }
    
    /**
       \brief Store as1*xs1 + k*as2*xs2 into new_as*new_xs

       If UpdateOcc == true,
       Then, 
       1) for each variable x occurring in xs2 but not in xs1:
             - eq_idx is added to m_occs[x]  
       2) for each variable that occurs in xs1 and xs2 and the resultant coefficient is zero,
             - eq_idx is removed from m_occs[x]  IF x != except_var
       
       If UpdateQueue == true
       Then,
       1) for each variable x occurring in xs2 but not in xs1:
             - if x is solved, then x is inserted into m_var_queue
       2) for each variable that occurs in xs1 and xs2 and the resultant coefficient is zero,
             - if x is solved, then x is removed from m_var_queue

    */
    template<typename Numeral, bool UpdateOcc, bool UpdateQueue>
    void addmul(svector<Numeral> const & as1, var_vector const & xs1,
                mpz const & k, svector<Numeral> const & as2, var_vector const & xs2,
                numeral_buffer<Numeral, numeral_manager> & new_as, var_vector & new_xs,
                unsigned eq_idx = null_eq_idx, var except_var = null_var) {
        Numeral new_a;
        SASSERT(as1.size() == xs1.size());
        SASSERT(as2.size() == xs2.size());
        new_as.reset();
        new_xs.reset();
        unsigned sz1 = xs1.size();
        unsigned sz2 = xs2.size();
        unsigned i1  = 0;
        unsigned i2  = 0;
        while (true) {
            if (i1 == sz1) {
                // copy remaining entries from as2*xs2
                while (i2 < sz2) {
                    var x2 = xs2[i2];
                    if (UpdateOcc)
                        m_occs[x2].push_back(eq_idx);
                    if (UpdateQueue && solved(x2))
                        m_var_queue.insert(x2);
                    new_as.push_back(Numeral());
                    m().mul(k, as2[i2], new_as.back());
                    new_xs.push_back(x2);
                    i2++;
                }
                break;
            }
            if (i2 == sz2) {
                // copy remaining entries from as1*xs1
                while (i1 < sz1) {
                    new_as.push_back(as1[i1]);
                    new_xs.push_back(xs1[i1]);
                    i1++;
                }
                break;
            }
            var x1 = xs1[i1];
            var x2 = xs2[i2];
            if (x1 < x2) {
                new_as.push_back(as1[i1]);
                new_xs.push_back(xs1[i1]);
                i1++;
            }
            else if (x1 > x2) {
                if (UpdateOcc) 
                    m_occs[x2].push_back(eq_idx);
                if (UpdateQueue && solved(x2))
                    m_var_queue.insert(x2);
                new_as.push_back(Numeral());
                m().mul(k, as2[i2], new_as.back());
                new_xs.push_back(x2);
                i2++;
            }
            else {
                m().addmul(as1[i1], k, as2[i2], new_a);
                TRACE("euclidean_solver_add_mul", tout << "i1: " << i1 << ", i2: " << i2 << " new_a: " << m().to_string(new_a) << "\n";
                      tout << "as1: " << m().to_string(as1[i1]) << ", k: " << m().to_string(k) << ", as2: " << m().to_string(as2[i2]) << "\n";);
                if (m().is_zero(new_a)) {
                    // variable was canceled
                    if (UpdateOcc && x1 != except_var)
                        m_occs[x1].erase(eq_idx);
                    if (UpdateQueue && solved(x1) && m_var_queue.contains(x1))
                        m_var_queue.erase(x1);
                }
                else {
                    new_as.push_back(new_a);
                    new_xs.push_back(x1);
                }
                i1++;
                i2++;
            }
        }
        m().del(new_a);
    }
    
    template<bool UpdateOcc, bool UpdateQueue>
    void apply_solution(var x, mpz_vector & as, var_vector & xs, mpz & c, mpq_vector & bs, justification_vector & js, 
                        unsigned eq_idx = null_eq_idx, var except_var = null_var) {
        SASSERT(solved(x));
        unsigned idx = pos(xs, x);
        if (idx == UINT_MAX)
            return;
        mpz const & a1 = as[idx];
        SASSERT(!m().is_zero(a1));
        equation const & eq2 = *(m_solution[m_solved[x]]);
        SASSERT(eq2.pos_x(x) != UINT_MAX);
        SASSERT(m().is_minus_one(eq2.a(eq2.pos_x(x))));
        TRACE("euclidean_solver_apply", 
              tout << "applying: " << m().to_string(a1) << " * "; display(tout, eq2); tout << "\n";
              for (unsigned i = 0; i < xs.size(); i++) tout << m().to_string(as[i]) << "*x" << xs[i] << " "; tout << "\n";);
        addmul<mpz, UpdateOcc, UpdateQueue>(as, xs, a1, eq2.m_as, eq2.m_xs, m_tmp_as, m_tmp_xs, eq_idx, except_var);
        m().addmul(c, a1, eq2.m_c, c);
        m_tmp_as.swap(as);
        m_tmp_xs.swap(xs);
        SASSERT(as.size() == xs.size());
        TRACE("euclidean_solver_apply", for (unsigned i = 0; i < xs.size(); i++) tout << m().to_string(as[i]) << "*x" << xs[i] << " "; tout << "\n";);
        addmul<mpq, false, false>(bs, js, a1, eq2.m_bs, eq2.m_js, m_tmp_bs, m_tmp_xs);
        m_tmp_bs.swap(bs);
        m_tmp_xs.swap(js);
        SASSERT(pos(xs, x) == UINT_MAX);
    }

    void apply_solution(mpz_vector & as, var_vector & xs, mpz & c, mpq_vector & bs, justification_vector & js) {
        m_var_queue.reset();
        schedule_var_subst(xs);
        while (!m_var_queue.empty()) {
            var x = m_var_queue.erase_min();
            apply_solution<false, true>(x, as, xs, c, bs, js);
        }
    }

    void apply_solution(equation & eq) {
        apply_solution(eq.m_as, eq.m_xs, eq.m_c, eq.m_bs, eq.m_js);
    }

    void display(std::ostream & out, equation const & eq) const {
        unsigned num = eq.js_size();
        for (unsigned i = 0; i < num; i ++) {
            if (i > 0) out << " ";
            out << m().to_string(eq.b(i)) << "*j" << eq.j(i);
        }
        if (num > 0) out << " ";
        out << "|= ";
        num = eq.size();
        for (unsigned i = 0; i < num; i++) {
            out << m().to_string(eq.a(i)) << "*x" << eq.x(i) << " + ";
        }
        out << m().to_string(eq.c()) << " = 0"; 
    }

    void display(std::ostream & out, equations const & eqs) const {
        unsigned num = eqs.size();
        for (unsigned i = 0; i < num; i++) {
            if (eqs[i]) {
                display(out, *(eqs[i]));
                out << "\n";
            }
        }
    }

    void display(std::ostream & out) const {
        if (inconsistent()) {
            out << "inconsistent: ";
            display(out, *(m_equations[m_inconsistent]));
            out << "\n";
        }
        out << "solution set:\n";
        display(out, m_solution);
        out << "todo:\n";
        display(out, m_equations);
    }

    void add_occs(unsigned eq_idx) {
        equation const & eq = *(m_equations[eq_idx]);
        unsigned sz = eq.size();
        for (unsigned i = 0; i < sz; i++)
            m_occs[eq.x(i)].push_back(eq_idx);
    }

    imp(numeral_manager * m):
        m_manager(m == nullptr ? alloc(numeral_manager) : m),
        m_owns_m(m == nullptr),
        m_decompose_buffer(*m_manager),
        m_as_buffer(*m_manager),
        m_bs_buffer(*m_manager), 
        m_tmp_as(*m_manager),
        m_tmp_bs(*m_manager),
        m_var_queue(16, elim_order_lt(m_solved)) {
        m_inconsistent       = null_eq_idx;
        m_next_justification = 0; 
        m_next_x             = null_var;
        m_next_eq            = null_eq_idx;
    }

    ~imp() {
        m().del(m_next_a);
        del_equations(m_equations);
        del_equations(m_solution);
        if (m_owns_m)
            dealloc(m_manager);
    }

    var mk_var(bool parameter) {
        var x = m_solved.size();
        m_parameter.push_back(parameter);
        m_solved.push_back(null_eq_idx);
        m_occs.push_back(occs());
        m_as_buffer.push_back(mpz());
        m_var_queue.reserve(x+1);
        return x;
    }

    justification mk_justification() {
        justification r = m_next_justification;
        m_bs_buffer.push_back(mpq());
        m_next_justification++;
        return r;
    }

    void assert_eq(unsigned num, mpz const * as, var const * xs, mpz const & c, justification j) {
        if (inconsistent())
            return;
        equation * eq;
        if (j == null_justification) {
            eq = mk_eq(num, as, xs, c, 0, nullptr, nullptr);
        }
        else {
            mpq one(1);
            eq = mk_eq(num, as, xs, c, 1, &one, &j);
        }
        TRACE("euclidean_solver", tout << "new-eq:\n"; display(tout, *eq); tout << "\n";);
        unsigned eq_idx = m_equations.size();
        m_equations.push_back(eq);
        apply_solution(*eq);
        normalize_eq(eq_idx);
        add_occs(eq_idx);
        TRACE("euclidean_solver", tout << "asserted:\n"; display(tout, *eq); tout << "\n";);
    }

    justification_vector const & get_justification() const {
        SASSERT(inconsistent());
        return m_equations[m_inconsistent]->m_js;
    }

    template<typename Numeral>
    void neg_coeffs(svector<Numeral> & as) {
        unsigned sz = as.size();
        for (unsigned i = 0; i < sz; i++) {
            m().neg(as[i]);
        }
    }

    void substitute_most_recent_solution(var x) {
        SASSERT(!m_solution.empty());
        TRACE("euclidean_solver", tout << "applying solution for x" << x << "\n"; 
              display(tout, *(m_solution.back())); tout << "\n";);
        occs & use_list = m_occs[x];
        occs::iterator it  = use_list.begin();
        occs::iterator end = use_list.end();
        for (; it != end; ++it) {
            unsigned eq_idx = *it;
            // remark we don't want to update the use_list of x while we are traversing it.
            equation & eq2 = *(m_equations[eq_idx]);
            TRACE("euclidean_solver", tout << "eq before substituting x" << x << "\n"; display(tout, eq2); tout << "\n";);
            apply_solution<true, false>(x, eq2.m_as, eq2.m_xs, eq2.m_c, eq2.m_bs, eq2.m_js, eq_idx, x);
            TRACE("euclidean_solver", tout << "eq after substituting x" << x << "\n"; display(tout, eq2); tout << "\n";);
            normalize_eq(eq_idx);
            if (inconsistent())
                break;
        }
        use_list.reset();
    }

    void elim_unit() {
        SASSERT(m().is_one(m_next_a));
        equation & eq = *(m_equations[m_next_eq]);
        TRACE("euclidean_solver", tout << "eliminating equation with unit coefficient:\n"; display(tout, eq); tout << "\n";);
        if (m_next_pos_a) {
            // neg coeffs... to make sure that m_next_x is -1
            neg_coeffs(eq.m_as);
            neg_coeffs(eq.m_bs);
            m().neg(eq.m_c);
        }
        unsigned sz = eq.size();
        for (unsigned i = 0; i < sz; i++) {
            m_occs[eq.x(i)].erase(m_next_eq);
        }
        m_solved[m_next_x] = m_solution.size();
        m_solution.push_back(&eq);
        m_equations[m_next_eq] = 0;
        substitute_most_recent_solution(m_next_x);
    }

    void decompose(bool pos_a, mpz const & abs_a, mpz const & a_i, mpz & new_a_i, mpz & r_i) {
        mpz abs_a_i;
        bool pos_a_i = m().is_pos(a_i);
        m().set(abs_a_i, a_i);
        if (!pos_a_i)
            m().neg(abs_a_i);
        bool new_pos_a_i = pos_a_i;
        if (pos_a) 
            new_pos_a_i  = !new_pos_a_i;
        m().div(abs_a_i, abs_a, new_a_i);
        if (m().divides(abs_a, a_i)) {
            m().reset(r_i);
        }
        else {
            if (pos_a_i)
                m().submul(a_i, abs_a, new_a_i, r_i);
            else 
                m().addmul(a_i, abs_a, new_a_i, r_i);
        }
        if (!new_pos_a_i)
            m().neg(new_a_i);
        m().del(abs_a_i);
    }

    void decompose_and_elim() {
        m_tmp_xs.reset();
        mpz_buffer & buffer = m_decompose_buffer;
        buffer.reset();
        var p = mk_var(true);
        mpz new_a_i;
        equation & eq = *(m_equations[m_next_eq]);
        TRACE("euclidean_solver", tout << "decompositing equation for x" << m_next_x << "\n"; display(tout, eq); tout << "\n";);
        unsigned sz = eq.size();
        unsigned j  = 0;
        for (unsigned i = 0; i < sz; i++) {
            var x_i = eq.x(i);
            if (x_i == m_next_x) {
                m().set(new_a_i, -1);
                buffer.push_back(new_a_i);
                m_tmp_xs.push_back(m_next_x);
                m_occs[x_i].erase(m_next_eq);
            }
            else {
                decompose(m_next_pos_a, m_next_a, eq.a(i), new_a_i, eq.m_as[j]);
                buffer.push_back(new_a_i);
                m_tmp_xs.push_back(x_i);
                if (m().is_zero(eq.m_as[j])) {
                    m_occs[x_i].erase(m_next_eq);
                }
                else {
                    eq.m_xs[j] = x_i;
                    j++;
                }
            }
        }
        SASSERT(j < sz);
        // add parameter: p to new equality, and m_next_pos_a * m_next_a * p to current eq
        m().set(new_a_i, 1);
        buffer.push_back(new_a_i);
        m_tmp_xs.push_back(p);
        m().set(eq.m_as[j], m_next_a);
        if (!m_next_pos_a)
            m().neg(eq.m_as[j]);
        eq.m_xs[j] = p;
        j++;
        unsigned new_sz = j;
        // shrink current eq
        for (; j < sz; j++)
            m().del(eq.m_as[j]);
        eq.m_as.shrink(new_sz);
        eq.m_xs.shrink(new_sz);
        // adjust c
        mpz new_c;
        decompose(m_next_pos_a, m_next_a, eq.m_c, new_c, eq.m_c);
        // create auxiliary equation
        equation * new_eq = mk_eq(m_tmp_xs.size(), buffer.c_ptr(), m_tmp_xs.c_ptr(), new_c, 0, nullptr, nullptr, false);
        // new_eq doesn't need to normalized, since it has unit coefficients
        TRACE("euclidean_solver", tout << "decomposition: new parameter x" << p << " aux eq:\n";
              display(tout, *new_eq); tout << "\n";
              display(tout, eq); tout << "\n";);
        m_solved[m_next_x] = m_solution.size();
        m_solution.push_back(new_eq);
        substitute_most_recent_solution(m_next_x);
        m().del(new_a_i);
        m().del(new_c);
    }
    
    bool solve() {
        if (inconsistent()) return false;
        TRACE("euclidean_solver", tout << "solving...\n"; display(tout););
        while (select_next_var()) {
            CTRACE("euclidean_solver_bug", m_next_x == null_var, display(tout););
            TRACE("euclidean_solver", tout << "eliminating x" << m_next_x << "\n";);
            if (m().is_one(m_next_a) || m().is_minus_one(m_next_a))
                elim_unit();
            else
                decompose_and_elim();
            TRACE("euclidean_solver", display(tout);); 
            if (inconsistent()) return false;
        }
        return true;
    }

    bool inconsistent() const {
        return m_inconsistent != null_eq_idx;
    }

    bool is_parameter(var x) const {
        return m_parameter[x];
    }
    
    void normalize(unsigned num, mpz const * as, var const * xs, mpz const & c, mpz & a_prime, mpz & c_prime, justification_vector & js) {
        TRACE("euclidean_solver", tout << "before applying solution set\n";
              for (unsigned i = 0; i < num; i++) {
                  tout << m().to_string(as[i]) << "*x" << xs[i] << " ";
              }
              tout << "\n";);
        m_norm_xs_vector.reset();
        m_norm_as_vector.reset();
        for (unsigned i = 0; i < num; i++) {
            m_norm_xs_vector.push_back(xs[i]);
            m_norm_as_vector.push_back(mpz());
            m().set(m_norm_as_vector.back(), as[i]);
        }
        sort(m_norm_as_vector, m_norm_xs_vector, m_as_buffer);
        m_norm_bs_vector.reset();
        js.reset();
        m().set(c_prime, c);
        apply_solution(m_norm_as_vector, m_norm_xs_vector, c_prime, m_norm_bs_vector, js);
        TRACE("euclidean_solver", tout << "after applying solution set\n";
              for (unsigned i = 0; i < m_norm_as_vector.size(); i++) {
                  tout << m().to_string(m_norm_as_vector[i]) << "*x" << m_norm_xs_vector[i] << " ";
              }
              tout << "\n";);
        // compute gcd of the result m_norm_as_vector
        if (m_norm_as_vector.empty()) {
            m().set(a_prime, 0);
        }
        else {
            mpz a;
            m().set(a_prime, m_norm_as_vector[0]);
            m().abs(a_prime);
            unsigned sz = m_norm_as_vector.size();
            for (unsigned i = 1; i < sz; i++) {
                if (m().is_one(a_prime))
                    break;
                m().set(a, m_norm_as_vector[i]);
                m().abs(a);
                m().gcd(a_prime, a, a_prime);
            }
            m().del(a);
        }
        // REMARK: m_norm_bs_vector contains the linear combination of the justifications. It may be useful if we 
        // decided (one day) to generate detailed proofs for this step.
        del_nums(m_norm_as_vector);
        del_nums(m_norm_bs_vector);
    }


};

euclidean_solver::euclidean_solver(numeral_manager * m):
    m_imp(alloc(imp, m)) {
}
    
euclidean_solver::~euclidean_solver() {
    dealloc(m_imp);
}

euclidean_solver::numeral_manager & euclidean_solver::m() const {
    return m_imp->m();
}

void euclidean_solver::reset() {
    numeral_manager * m = m_imp->m_manager;
    bool owns_m         = m_imp->m_owns_m;
    m_imp->m_owns_m     = false;
    dealloc(m_imp);
    m_imp = alloc(imp, m);
    m_imp->m_owns_m = owns_m;    
}

euclidean_solver::var euclidean_solver::mk_var() {
    return m_imp->mk_var(false);
}

euclidean_solver::justification euclidean_solver::mk_justification() {
    return m_imp->mk_justification();
}

void euclidean_solver::assert_eq(unsigned num, mpz const * as, var const * xs, mpz const & c, justification j) {
    m_imp->assert_eq(num, as, xs, c, j);
}

bool euclidean_solver::solve() {
    return m_imp->solve();
}

euclidean_solver::justification_vector const & euclidean_solver::get_justification() const {
    return m_imp->get_justification();
}

bool euclidean_solver::inconsistent() const {
    return m_imp->inconsistent();
}

bool euclidean_solver::is_parameter(var x) const {
    return m_imp->is_parameter(x);
}
    
void euclidean_solver::normalize(unsigned num, mpz const * as, var const * xs, mpz const & c, mpz & a_prime, mpz & c_prime, 
                                 justification_vector & js) {
    return m_imp->normalize(num, as, xs, c, a_prime, c_prime, js);
}


void euclidean_solver::display(std::ostream & out) const {
    m_imp->display(out);
}


