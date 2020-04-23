/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_t_def.h

Abstract:

    Subpaving template for non-linear arithmetic.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#include "math/subpaving/subpaving_t.h"
#include "math/interval/interval_def.h"
#include "util/buffer.h"
#include "util/z3_exception.h"
#include "util/common_msgs.h"

namespace subpaving {

/**
   \brief Node selector for breadth-first search.
*/
template<typename C>
class breadth_first_node_selector : public context_t<C>::node_selector {
    typedef typename context_t<C>::node            node;
public:
    breadth_first_node_selector(context_t<C> * ctx):
        context_t<C>::node_selector(ctx) {
    }

    node * operator()(node * front, node * back) override {
        return back;
    }
};

/**
   \brief Node selector for depth-first search.
*/
template<typename C>
class depth_first_node_selector : public context_t<C>::node_selector {
    typedef typename context_t<C>::node            node;
public:
    depth_first_node_selector(context_t<C> * ctx):
        context_t<C>::node_selector(ctx) {
    }

    virtual node * operator()(node * front, node * back) {
        return front;
    }
};

/**
   Round robing variable selector.
   If only_non_def is true, then variable definitions (aka auxiliary variables) are ignored.
*/
template<typename C>
class round_robing_var_selector : public context_t<C>::var_selector {
    typedef typename context_t<C>::bound           bound;

    bool m_only_non_def;

    void next(var & x) const {
        x++;
        if (x >= this->ctx()->num_vars())
            x = 0;
    }

public:
    round_robing_var_selector(context_t<C> * ctx, bool only_non_def = true):
        context_t<C>::var_selector(ctx),
        m_only_non_def(only_non_def) {
    }

    // Return the next variable to branch.
    var operator()(typename context_t<C>::node * n) override {
        typename context_t<C>::numeral_manager & nm = this->ctx()->nm();
        if (this->ctx()->num_vars() == 0)
            return null_var;
        var x = this->ctx()->splitting_var(n);
        if (x == null_var)
            x = 0;
        else
            next(x);
        var start = x;
        do {
            if (!m_only_non_def || !this->ctx()->is_definition(x)) {
                bound * lower = n->lower(x);
                bound * upper = n->upper(x);
                if (lower == nullptr || upper == nullptr || !nm.eq(lower->value(), upper->value())) {
                    return x;
                }
            }
            next(x);
        }
        while (x != start);
        return null_var;
    }
};

/**
   Selector that uses the following strategy:

   - If only_non_def is true, then variable definitions (aka auxiliary variables) are ignored.

   - All variables x s.t. lower(x) == upper(x) are ignored.

   - If node contains an unbounded variable (-oo, oo), then return the smallest unbounded variable.

   - Otherwise, select the smallest variable x with the largest width, where
     width is defined as:
         If x has lower and upper bound, then width = upper(x) - lower(x).
         If x has only lower,  width = penalty/max(|lower(x)|, 1)
         If x has only upper,  width = penalty/max(|upper(x)|, 1)
     penaly is a parameter of this class.

     This strategy guarantees fairness.
*/
template<typename C>
class largest_interval_var_selector : public context_t<C>::var_selector {
    unsigned m_penalty;
    bool     m_only_non_def;

public:
    largest_interval_var_selector(context_t<C> * ctx, unsigned unbounded_penalty = 10, bool only_non_def = true):
        context_t<C>::var_selector(ctx),
        m_penalty(unbounded_penalty),
        m_only_non_def(only_non_def) {
    }

    // Return the next variable to branch.
    virtual var operator()(typename context_t<C>::node * n) {
        var y = null_var;
        typename context_t<C>::numeral_manager & nm = this->ctx()->nm();
        _scoped_numeral<typename context_t<C>::numeral_manager> largest(nm), width(nm), penalty(nm), one(nm);
        nm.set(penalty, m_penalty);
        nm.set(one, 1);
        unsigned num   = this->ctx()->num_vars();
        for (var x = 0; x < num; x++) {
            if (m_only_non_def && this->ctx()->is_definition(x))
                continue;
            typename context_t<C>::bound * l = n->lower(x);
            typename context_t<C>::bound * u = n->upper(x);
            // variables without lower and upper bounds are selected immediately.
            if (l == 0 && u == 0)
                return x;
            if (l != 0 && u != 0) {
                // ignore variables s.t. lower(x) == upper(x)
                if (nm.eq(l->value(), u->value()))
                    continue;
                // if x has lower and upper bounds, set width to upper(x) - lower(x)
                C::round_to_plus_inf(nm);
                nm.sub(u->value(), l->value(), width);
            }
            else {
                // if x does not have lower or upper, then
                // set width to  penalty/|value|  where value is the existing bound.
                if (l != 0)
                    nm.set(width, l->value());
                else
                    nm.set(width, u->value());
                C::round_to_plus_inf(nm);
                if (nm.is_neg(width))
                    nm.neg(width);
                if (nm.lt(width, one))
                    nm.set(width, one);
                nm.mul(penalty, width, width);
            }
            if (y == null_var || nm.gt(width, largest)) {
                y = x;
                nm.set(largest, width);
            }
        }
        return y;
    }
};

template<typename C>
class midpoint_node_splitter : public context_t<C>::node_splitter {
    typedef typename context_t<C>::numeral_manager numeral_manager;
    typedef typename numeral_manager::numeral      numeral;
    typedef typename context_t<C>::node            node;
    typedef typename context_t<C>::bound           bound;
    bool     m_left_open;
    unsigned m_delta;
public:
    midpoint_node_splitter(context_t<C> * ctx, bool left_open = true, unsigned delta = 1):
        context_t<C>::node_splitter(ctx),
        m_left_open(left_open),
        m_delta(delta) {
        SASSERT(m_delta < INT_MAX);
    }

    void operator()(node * n, var x) override {
        SASSERT(!n->inconsistent());
        numeral_manager & nm = this->ctx()->nm();
        node * left   = this->mk_node(n);
        node * right  = this->mk_node(n);
        bound * lower = n->lower(x);
        bound * upper = n->upper(x);
        _scoped_numeral<numeral_manager> mid(nm);
        if (lower == nullptr && upper == nullptr) {
            nm.set(mid, 0);
            // mid == 0
        }
        else if (lower == nullptr) {
            _scoped_numeral<numeral_manager> delta(nm);
            SASSERT(upper != 0);
            nm.set(delta, static_cast<int>(m_delta));
            nm.set(mid, upper->value());
            C::round_to_minus_inf(nm);
            nm.sub(mid, delta, mid);
            // mid == upper - delta
        }
        else if (upper == nullptr) {
            _scoped_numeral<numeral_manager> delta(nm);
            SASSERT(lower != 0);
            nm.set(delta, static_cast<int>(m_delta));
            nm.set(mid, lower->value());
            C::round_to_plus_inf(nm);
            nm.add(mid, delta, mid);
            // mid == lower + delta
        }
        else {
            _scoped_numeral<numeral_manager> two(nm);
            SASSERT(!nm.eq(lower->value(), upper->value()));
            nm.set(two, 2);
            nm.add(lower->value(), upper->value(), mid);
            nm.div(mid, two, mid);
            if (!(nm.lt(lower->value(), mid) && nm.lt(mid, upper->value())))
                throw subpaving::exception();
            // mid == (lower + upper)/2
        }

        this->mk_decided_bound(x, mid, false, m_left_open, left);
        this->mk_decided_bound(x, mid, true, !m_left_open, right);
        TRACE("subpaving_int_split",
              tout << "LEFT:\n"; this->ctx()->display_bounds(tout, left);
              tout << "\nRIGHT:\n"; this->ctx()->display_bounds(tout, right););
    }
};


/**
   \brief Auxiliary static method used to display a bound specified by (x, k, lower, open).
*/
template<typename C>
void context_t<C>::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc, var x, numeral & k, bool lower, bool open) {
    if (lower) {
        out << nm.to_rational_string(k) << " <";
        if (!open)
            out << "=";
        out << " ";
        proc(out, x);
    }
    else {
        proc(out, x);
        out << " <";
        if (!open)
            out << "=";
        out << " " << nm.to_rational_string(k);
    }
}

template<typename C>
void context_t<C>::ineq::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    context_t<C>::display(out, nm, proc, m_x, m_val, is_lower(), is_open());
}

template<typename C>
void context_t<C>::bound::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    context_t<C>::display(out, nm, proc, m_x, m_val, is_lower(), is_open());
}

template<typename C>
void context_t<C>::clause::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    for (unsigned i = 0; i < size(); i++) {
        if (i > 0)
            out << " or ";
        m_atoms[i]->display(out, nm, proc);
    }
}

template<typename C>
context_t<C>::node::node(context_t & s, unsigned id):
    m_bm(s.bm()) {
    m_id              = id;
    m_depth           = 0;
    unsigned num_vars = s.num_vars();
    m_conflict        = null_var;
    m_trail           = nullptr;
    m_parent          = nullptr;
    m_first_child     = nullptr;
    m_next_sibling    = nullptr;
    m_prev            = nullptr;
    m_next            = nullptr;
    bm().mk(m_lowers);
    bm().mk(m_uppers);
    for (unsigned i = 0; i < num_vars; i++) {
        bm().push_back(m_lowers, nullptr);
        bm().push_back(m_uppers, nullptr);
    }
}

template<typename C>
context_t<C>::node::node(node * parent, unsigned id):
    m_bm(parent->m_bm) {
    m_id             = id;
    m_depth          = parent->depth() + 1;
    bm().copy(parent->m_lowers, m_lowers);
    bm().copy(parent->m_uppers, m_uppers);
    m_conflict       = parent->m_conflict;
    m_trail          = parent->m_trail;
    m_parent         = parent;
    m_first_child    = nullptr;
    m_next_sibling   = parent->m_first_child;
    m_prev           = nullptr;
    m_next           = nullptr;
    parent->m_first_child = this;
}

/**
   \brief Add a new bound b at this node.
*/
template<typename C>
void context_t<C>::node::push(bound * b) {
    SASSERT(b->prev() == m_trail);
    m_trail = b;
    if (b->is_lower()) {
        bm().set(m_lowers, b->x(), b);
        SASSERT(lower(b->x()) == b);
    }
    else {
        bm().set(m_uppers, b->x(), b);
        SASSERT(upper(b->x()) == b);
    }
}

/**
    \brief Return the most recent variable that was used for splitting on node n.
*/
template<typename C>
var context_t<C>::splitting_var(node * n) const {
    if (n == m_root)
        return null_var;
    bound * b = n->trail_stack();
    while (b != nullptr) {
        if (b->jst().is_axiom())
            return b->x();
        b = b->prev();
    }
    UNREACHABLE();
    return null_var;
}

template<typename C>
context_t<C>::monomial::monomial(unsigned sz, power const * pws):
    definition(constraint::MONOMIAL),
    m_size(sz) {
    memcpy(m_powers, pws, sz*sizeof(power));
    std::sort(m_powers, m_powers+sz, typename power::lt_proc());
    DEBUG_CODE({
            for (unsigned i = 0; i < sz; i ++) {
                SASSERT(i == 0 || x(i) > x(i-1));
                SASSERT(degree(i) > 0);
            }});
}

template<typename C>
void context_t<C>::monomial::display(std::ostream & out, display_var_proc const & proc, bool use_star) const {
    SASSERT(m_size > 0);
    for (unsigned i = 0; i < m_size; i++) {
        if (i > 0) {
            if (use_star)
                out << "*";
            else
                out << " ";
        }
        proc(out, x(i));
        if (degree(i) > 1)
            out << "^" << degree(i);
    }
}

template<typename C>
void context_t<C>::polynomial::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc, bool use_star) const {
    bool first = true;
    if (!nm.is_zero(m_c)) {
        out << nm.to_rational_string(m_c);
        first = false;
    }

    for (unsigned i = 0; i < m_size; i++) {
        if (first)
            first = false;
        else
            out << " + ";
        if (!nm.is_one(a(i))) {
            out << nm.to_rational_string(a(i));
            if (use_star)
                out << "*";
            else
                out << " ";
        }
        proc(out, x(i));
    }
}

template<typename C>
context_t<C>::context_t(reslimit& lim, C const & c, params_ref const & p, small_object_allocator * a):
    m_limit(lim),
    m_c(c),
    m_own_allocator(a == nullptr),
    m_allocator(a == nullptr ? alloc(small_object_allocator, "subpaving") : a),
    m_bm(*this, *m_allocator),
    m_im(lim, interval_config(m_c.m())),
    m_num_buffer(nm()) {
    m_arith_failed  = false;
    m_timestamp     = 0;
    m_root          = nullptr;
    m_leaf_head     = nullptr;
    m_leaf_tail     = nullptr;
    m_conflict      = null_var;
    m_qhead         = 0;
    m_display_proc  = &m_default_display_proc;
    m_node_selector = alloc(breadth_first_node_selector<C>, this);
    m_var_selector  = alloc(round_robing_var_selector<C>, this);
    m_node_splitter = alloc(midpoint_node_splitter<C>, this);
    m_num_nodes     = 0;
    updt_params(p);
    reset_statistics();
}

template<typename C>
context_t<C>::~context_t() {
    nm().del(m_epsilon);
    nm().del(m_max_bound);
    nm().del(m_minus_max_bound);
    nm().del(m_nth_root_prec);
    nm().del(m_tmp1);
    nm().del(m_tmp2);
    nm().del(m_tmp3);
    del(m_i_tmp1);
    del(m_i_tmp2);
    del(m_i_tmp3);
    del_nodes();
    del_unit_clauses();
    del_clauses();
    del_definitions();
    if (m_own_allocator)
        dealloc(m_allocator);
}

template<typename C>
void context_t<C>::checkpoint() {
    if (!m_limit.inc())
        throw default_exception(Z3_CANCELED_MSG);
    if (memory::get_allocation_size() > m_max_memory)
        throw default_exception(Z3_MAX_MEMORY_MSG);
}

template<typename C>
void context_t<C>::del(interval & a) {
    nm().del(a.m_l_val);
    nm().del(a.m_u_val);
}

template<typename C>
void context_t<C>::updt_params(params_ref const & p) {
    unsigned epsilon = p.get_uint("epsilon", 20);
    if (epsilon != 0) {
        nm().set(m_epsilon, static_cast<int>(epsilon));
        nm().inv(m_epsilon);
        m_zero_epsilon = false;
    }
    else {
        nm().reset(m_epsilon);
        m_zero_epsilon = true;
    }

    unsigned max_power = p.get_uint("max_bound", 10);
    nm().set(m_max_bound, 10);
    nm().power(m_max_bound, max_power, m_max_bound);
    nm().set(m_minus_max_bound, m_max_bound);
    nm().neg(m_minus_max_bound);

    m_max_depth = p.get_uint("max_depth", 128);
    m_max_nodes = p.get_uint("max_nodes", 8192);

    m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));

    unsigned prec = p.get_uint("nth_root_precision", 8192);
    if (prec == 0)
        prec = 1;
    nm().set(m_nth_root_prec, static_cast<int>(prec));
    nm().inv(m_nth_root_prec);
}

template<typename C>
void context_t<C>::collect_param_descrs(param_descrs & d) {
    d.insert("max_nodes", CPK_UINT, "(default: 8192) maximum number of nodes in the subpaving tree.");
    d.insert("max_depth", CPK_UINT, "(default: 128) maximum depth of the subpaving tree.");
    d.insert("epsilon", CPK_UINT, "(default: 20) value k s.t. a new lower (upper) bound for x is propagated only new-lower(x) > lower(k) + 1/k * max(min(upper(x) - lower(x), |lower|), 1) (new-upper(x) < upper(x) - 1/k * max(min(upper(x) - lower(x), |lower|), 1)). If k = 0, then this restriction is ignored.");
    d.insert("max_bound", CPK_UINT, "(default 10) value k s.t. a new upper (lower) bound for x is propagated only if upper(x) > -10^k or lower(x) = -oo (lower(x) < 10^k or upper(x) = oo)");
    d.insert("nth_root_precision", CPK_UINT, "(default 8192) value k s.t. 1/k is the precision for computing the nth root in the subpaving module.");
}

template<typename C>
void context_t<C>::display_params(std::ostream & out) const {
    out << "max_nodes  " << m_max_nodes << "\n";
    out << "max_depth  " << m_max_depth << "\n";
    out << "epsilon    " << nm().to_rational_string(m_epsilon) << "\n";
    out << "max_bound  " << nm().to_rational_string(m_max_bound) << "\n";
    out << "max_memory " << m_max_memory << "\n";
}

template<typename C>
typename context_t<C>::bound * context_t<C>::mk_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst) {
    SASSERT(!inconsistent(n));
    m_num_mk_bounds++;
    void * mem = allocator().allocate(sizeof(bound));
    bound * r  = new (mem) bound();
    r->m_x         = x;
    if (is_int(x)) {
        // adjust integer bound
        if (!nm().is_int(val))
            open = false; // performing ceil/floor
        if (lower) {
            nm().ceil(val, r->m_val);
        }
        else {
            nm().floor(val, r->m_val);
        }
        if (open) {
            open = false;
            if (lower)  {
                C::round_to_minus_inf(nm());
                nm().inc(r->m_val);
            }
            else {
                C::round_to_plus_inf(nm());
                nm().dec(r->m_val);
            }
        }
    }
    else {
        nm().set(r->m_val, val);
    }
    r->m_lower     = lower;
    r->m_open      = open;
    r->m_mark      = false;
    r->m_timestamp = m_timestamp;
    r->m_prev      = n->trail_stack();
    r->m_jst       = jst;
    n->push(r);
    TRACE("subpaving_mk_bound", tout << "mk_bound: "; display(tout, r); tout << "\ntimestamp: " << r->m_timestamp << "\n";);
    if (conflicting_bounds(x, n)) {
        TRACE("subpaving_mk_bound", tout << "conflict\n"; display_bounds(tout, n););
        set_conflict(x, n);
    }
    m_timestamp++;
    if (m_timestamp == UINT64_MAX)
        throw subpaving::exception(); // subpaving failed.
    return r;
}

template<typename C>
void context_t<C>::propagate_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst) {
    bound * b = mk_bound(x, val, lower, open, n, jst);
    m_queue.push_back(b);
    SASSERT(!lower || n->lower(x) == b);
    SASSERT(lower  || n->upper(x) == b);
    SASSERT(is_int(x) || !lower || nm().eq(n->lower(x)->value(), val));
    SASSERT(is_int(x) || lower  || nm().eq(n->upper(x)->value(), val));
    SASSERT(open || !nm().is_int(val) || !lower || nm().eq(n->lower(x)->value(), val));
    SASSERT(open || !nm().is_int(val) || lower  || nm().eq(n->upper(x)->value(), val));
    SASSERT(!lower || nm().ge(n->lower(x)->value(), val));
    SASSERT(lower  || nm().le(n->upper(x)->value(), val));
}

template<typename C>
void context_t<C>::del_bound(bound * b) {
    nm().del(b->m_val);
    b->~bound();
    allocator().deallocate(sizeof(bound), b);
}

template<typename C>
void context_t<C>::display(std::ostream & out, var x) const {
    if (x == null_var)
        out << "[null]";
    else
        (*m_display_proc)(out, x);
}

template<typename C>
void context_t<C>::display(std::ostream & out, bound * b) const {
    b->display(out, nm(), *m_display_proc);
}

template<typename C>
void context_t<C>::display(std::ostream & out, ineq * a) const {
    a->display(out, nm(), *m_display_proc);
}

template<typename C>
void context_t<C>::display_definition(std::ostream & out, definition const * d, bool use_star) const {
    switch (d->get_kind()) {
    case constraint::MONOMIAL:
        static_cast<monomial const *>(d)->display(out, *m_display_proc, use_star);
        break;
    case constraint::POLYNOMIAL:
        static_cast<polynomial const *>(d)->display(out, nm(), *m_display_proc, use_star);
        break;
    default:
        UNREACHABLE();
    };
}

template<typename C>
void context_t<C>::display(std::ostream & out, constraint * c, bool use_star) const {
    if (c->get_kind() == constraint::CLAUSE)
        static_cast<clause*>(c)->display(out, nm(), *m_display_proc);
    else
        display_definition(out, static_cast<definition*>(c), use_star);
}

template<typename C>
void context_t<C>::display_bounds(std::ostream & out, node * n) const {
    unsigned num = num_vars();
    for (unsigned x = 0; x < num; x++) {
        bound * l = n->lower(x);
        bound * u = n->upper(x);
        if (l != nullptr) {
            display(out, l);
            out << " ";
        }
        if (u != nullptr) {
            display(out, u);
        }
        if (l != nullptr || u != nullptr)
            out << "\n";
    }
}

/**
   \brief Return true if all variables in m are integer.
*/
template<typename C>
bool context_t<C>::is_int(monomial const * m) const {
    for (unsigned i = 0; i < m->size(); i++) {
        if (is_int(m->x(i)))
            return true;
    }
    return false;
}

/**
   \brief Return true if all variables in p are integer, and all coefficients in p are integer.
*/
template<typename C>
bool context_t<C>::is_int(polynomial const * p) const {
    for (unsigned i = 0; i < p->size(); i++) {
        if (!is_int(p->x(i)) || !nm().is_int(p->a(i))) {
            TRACE("subpaving_is_int", tout << "polynomial is not integer due to monomial at i: " << i << "\n"; tout.flush();
                  display(tout, p->x(i)); tout << " "; nm().display(tout, p->a(i)); tout << "\n";);
            return false;
        }
    }
    return nm().is_int(p->c());
}

template<typename C>
var context_t<C>::mk_var(bool is_int) {
    var r = static_cast<var>(m_is_int.size());
    m_is_int.push_back(is_int);
    m_defs.push_back(0);
    m_wlist.push_back(watch_list());
    m_var_selector->new_var_eh(r);
    return r;
}

template<typename C>
void context_t<C>::del_monomial(monomial * m) {
    unsigned mem_sz = monomial::get_obj_size(m->size());
    m->~monomial();
    allocator().deallocate(mem_sz, m);
}

template<typename C>
var context_t<C>::mk_monomial(unsigned sz, power const * pws) {
    SASSERT(sz > 0);
    m_pws.reset();
    m_pws.append(sz, pws);
    std::sort(m_pws.begin(), m_pws.end(), power::lt_proc());
    unsigned j = 0;
    for (unsigned i = 1; i < sz; i++) {
        if (m_pws[j].x() == m_pws[i].x()) {
            m_pws[j].degree() += m_pws[i].degree();
        }
        else {
            j++;
            SASSERT(j <= i);
            m_pws[j] = m_pws[i];
        }
    }
    sz = j + 1;
    pws = m_pws.c_ptr();
    unsigned mem_sz  = monomial::get_obj_size(sz);
    void * mem       = allocator().allocate(mem_sz);
    monomial * r     = new (mem) monomial(sz, pws);
    var new_var      = mk_var(is_int(r));
    m_defs[new_var]  = r;
    for (unsigned i = 0; i < sz; i++) {
        var x = pws[i].x();
        m_wlist[x].push_back(watched(new_var));
    }
    return new_var;
}

template<typename C>
void context_t<C>::del_sum(polynomial * p) {
    unsigned sz = p->size();
    unsigned mem_sz = polynomial::get_obj_size(sz);
    for (unsigned i = 0; i < sz; i++) {
        nm().del(p->m_as[i]);
    }
    nm().del(p->m_c);
    p->~polynomial();
    allocator().deallocate(mem_sz, p);
}

template<typename C>
var context_t<C>::mk_sum(numeral const & c, unsigned sz, numeral const * as, var const * xs) {
    m_num_buffer.reserve(num_vars());
    for (unsigned i = 0; i < sz; i++) {
        SASSERT(xs[i] < num_vars());
        nm().set(m_num_buffer[xs[i]], as[i]);
    }
    unsigned mem_sz  = polynomial::get_obj_size(sz);
    void * mem       = allocator().allocate(mem_sz);
    polynomial * p   = new (mem) polynomial();
    p->m_size        = sz;
    nm().set(p->m_c, c);
    p->m_as          = reinterpret_cast<numeral*>(static_cast<char*>(mem) + sizeof(polynomial));
    p->m_xs          = reinterpret_cast<var*>(reinterpret_cast<char*>(p->m_as) + sizeof(numeral)*sz);
    memcpy(p->m_xs, xs, sizeof(var)*sz);
    std::sort(p->m_xs, p->m_xs+sz);
    for (unsigned i = 0; i < sz; i++) {
        numeral * curr = p->m_as + i;
        new (curr) numeral();
        var x = p->m_xs[i];
        nm().swap(m_num_buffer[x], *curr);
    }
    TRACE("subpaving_mk_sum", tout << "new variable is integer: " << is_int(p) << "\n";);
    var new_var      = mk_var(is_int(p));
    for (unsigned i = 0; i < sz; i++) {
        var x = p->m_xs[i];
        m_wlist[x].push_back(watched(new_var));
    }
    m_defs[new_var]  = p;
    return new_var;
}

template<typename C>
typename context_t<C>::ineq * context_t<C>::mk_ineq(var x, numeral const & k, bool lower, bool open) {
    void * mem = allocator().allocate(sizeof(ineq));
    ineq * r   = new (mem) ineq();
    r->m_ref_count = 0;
    r->m_x         = x;
    nm().set(r->m_val, k);
    r->m_lower     = lower;
    r->m_open      = open;
    return r;
}

template<typename C>
void context_t<C>::inc_ref(ineq * a) {
    TRACE("subpaving_ref_count", tout << "inc-ref: " << a << " " << a->m_ref_count << "\n";);
    if (a)
        a->m_ref_count++;
}

template<typename C>
void context_t<C>::dec_ref(ineq * a) {
    if (a) {
        TRACE("subpaving_ref_count",
              tout << "dec-ref: " << a << " " << a->m_ref_count << "\n";
              a->display(tout, nm());
              tout << "\n";);
        SASSERT(a->m_ref_count > 0);
        a->m_ref_count--;
        if (a->m_ref_count == 0) {
            nm().del(a->m_val);
            a->~ineq();
            allocator().deallocate(sizeof(ineq), a);
        }
    }
}

template<typename C>
void context_t<C>::add_clause_core(unsigned sz, ineq * const * atoms, bool lemma, bool watch) {
    SASSERT(lemma || watch);
    SASSERT(sz > 0);
    if (sz == 1) {
        add_unit_clause(atoms[0], true);
        return;
    }

    void * mem = allocator().allocate(clause::get_obj_size(sz));
    clause * c = new (mem) clause();
    c->m_size  = sz;
    for (unsigned i = 0; i < sz; i++) {
        inc_ref(atoms[i]);
        c->m_atoms[i] = atoms[i];
    }
    std::stable_sort(c->m_atoms, c->m_atoms + sz, typename ineq::lt_var_proc());
    if (watch) {
        for (unsigned i = 0; i < sz; i++) {
            var x = c->m_atoms[i]->x();
            if (x != null_var && (i == 0 || x != c->m_atoms[i-1]->x()))
                m_wlist[x].push_back(watched(c));
        }
    }
    c->m_lemma   = lemma;
    c->m_num_jst = 0;
    c->m_watched = watch;
    if (!lemma) {
        m_clauses.push_back(c);
    }
    else if (watch) {
        m_lemmas.push_back(c);
    }
    TRACE("subpaving_clause", tout << "new clause:\n"; display(tout, c); tout << "\n";);
}

template<typename C>
void context_t<C>::del_clause(clause * c) {
    SASSERT(c->m_num_jst == 0); // We cannot delete a clause that is being used to justify some bound
    bool watch  = c->watched();
    var prev_x  = null_var;
    unsigned sz = c->size();
    for (unsigned i = 0; i < sz; i++) {
        var x = c->m_atoms[i]->x();
        if (watch) {
            if (x != prev_x)
                m_wlist[x].erase(watched(c));
            prev_x = x;
        }
        dec_ref((*c)[i]);
    }
    unsigned mem_sz = clause::get_obj_size(sz);
    c->~clause();
    allocator().deallocate(mem_sz, c);
}

template<typename C>
void context_t<C>::add_unit_clause(ineq * a, bool axiom) {
    TRACE("subpaving", a->display(tout, nm(), *m_display_proc); tout << "\n";);
    inc_ref(a);
    m_unit_clauses.push_back(TAG(ineq*, a, axiom));
}

template<typename C>
void context_t<C>::add_ineq(var x, numeral const & k, bool lower, bool open, bool axiom) {
    ineq * unit = mk_ineq(x, k, lower, open);
    add_unit_clause(unit, axiom);
}

template<typename C>
typename context_t<C>::node * context_t<C>::mk_node(node * parent) {
    void * mem = allocator().allocate(sizeof(node));
    node * r;
    if (parent == nullptr)
        r = new (mem) node(*this, m_node_id_gen.mk());
    else
        r = new (mem) node(parent, m_node_id_gen.mk());
    m_var_selector->new_node_eh(r);

    // Add node in the leaf dlist
    push_front(r);

    m_num_nodes++;
    return r;
}

template<typename C>
void context_t<C>::del_node(node * n) {
    SASSERT(n->first_child() == 0);

    SASSERT(m_num_nodes > 0);
    m_num_nodes--;

    m_var_selector->del_node_eh(n);

    // recycle id
    m_node_id_gen.recycle(n->id());

    // disconnect n from list of leaves.
    remove_from_leaf_dlist(n);

    // disconnect n from parent
    node * p = n->parent();
    bound * b = n->trail_stack();
    bound * b_old;
    if (p != nullptr) {
        node * c = p->first_child();
        if (c == n) {
            // n is the first child
            p->set_first_child(n->next_sibling());
        }
        else {
            SASSERT(c->next_sibling() != 0);
            while (c->next_sibling() != n) {
                c = c->next_sibling();
                SASSERT(c->next_sibling() != 0);
            }
            SASSERT(c->next_sibling() == n);
            c->set_next_sibling(n->next_sibling());
        }
        b_old = p->trail_stack();
    }
    else {
        b_old = nullptr;
    }
    while (b != b_old) {
        bound * old = b;
        b = b->prev();
        del_bound(old);
    }
    bm().del(n->uppers());
    bm().del(n->lowers());
    n->~node();
    allocator().deallocate(sizeof(node), n);
}

template<typename C>
void context_t<C>::del_nodes() {
    ptr_buffer<node> todo;
    if (m_root == nullptr)
        return;
    todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        node * c = n->first_child();
        if (c == nullptr) {
            del_node(n);
            todo.pop_back();
        }
        else {
            while (c != nullptr) {
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::push_front(node * n) {
    SASSERT(n->first_child() == 0);
    SASSERT(n->next() == 0);
    SASSERT(n->prev() == 0);
    n->set_next(m_leaf_head);
    if (m_leaf_head != nullptr) {
        SASSERT(m_leaf_head->prev() == 0);
        m_leaf_head->set_prev(n);
    }
    else {
        SASSERT(m_leaf_head == 0);
        m_leaf_tail = n;
    }
    m_leaf_head = n;
}

template<typename C>
void context_t<C>::push_back(node * n) {
    SASSERT(n->first_child() == 0);
    SASSERT(n->next() == 0);
    SASSERT(n->prev() == 0);
    n->set_prev(m_leaf_tail);
    if (m_leaf_tail != nullptr) {
        SASSERT(m_leaf_tail->next() == 0);
        m_leaf_tail->set_next(n);
    }
    else {
        SASSERT(m_leaf_tail == 0);
        m_leaf_head = n;
    }
    m_leaf_tail = n;
}

template<typename C>
void context_t<C>::reset_leaf_dlist() {
    // Remove all nodes from the lead doubly linked list
    node * n = m_leaf_head;
    while (n != nullptr) {
        node * next = n->next();
        n->set_next(nullptr);
        n->set_prev(nullptr);
        n = next;
    }
    m_leaf_head = nullptr;
    m_leaf_tail = nullptr;
}

template<typename C>
void context_t<C>::rebuild_leaf_dlist(node * n) {
    reset_leaf_dlist();
    // Reinsert all leaves in the leaf dlist.
    ptr_buffer<node, 1024> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        if (c == nullptr) {
            if (!n->inconsistent())
                push_front(n);
        }
        else  {
            while (c != nullptr) {
                SASSERT(c->parent() == n);
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::remove_from_leaf_dlist(node * n) {
    node * prev = n->prev();
    node * next = n->next();
    SASSERT(prev == 0 || prev != next);
    SASSERT(next == 0 || prev != next);
    SASSERT(prev != n); SASSERT(next != n);
    if (prev != nullptr) {
        SASSERT(m_leaf_head != n);
        prev->set_next(next);
        n->set_prev(nullptr);
    }
    else if (m_leaf_head == n) {
        m_leaf_head = next;
    }

    if (next != nullptr) {
        SASSERT(m_leaf_tail != n);
        next->set_prev(prev);
        n->set_next(nullptr);
    }
    else if (m_leaf_tail == n) {
        m_leaf_tail = prev;
    }
    SASSERT(n->prev() == 0 && n->next() == 0);
}

template<typename C>
void context_t<C>::collect_leaves(ptr_vector<node> & leaves) const {
    // Copy all leaves to the given vector.
    ptr_buffer<node, 1024> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        if (c == nullptr) {
            if (!n->inconsistent())
                leaves.push_back(n);
        }
        else  {
            while (c != nullptr) {
                SASSERT(c->parent() == n);
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::del_unit_clauses() {
    unsigned sz = m_unit_clauses.size();
    for (unsigned i = 0; i < sz; i++)
        dec_ref(UNTAG(ineq*, m_unit_clauses[i]));
    m_unit_clauses.reset();
}

template<typename C>
void context_t<C>::del_clauses(ptr_vector<clause> & cs) {
    unsigned sz = cs.size();
    for (unsigned i = 0; i < sz; i++) {
        del_clause(cs[i]);
    }
    cs.reset();
}

template<typename C>
void context_t<C>::del_clauses() {
    del_clauses(m_clauses);
    del_clauses(m_lemmas);
}

template<typename C>
void context_t<C>::del_definitions() {
    unsigned sz = num_vars();
    for (unsigned i = 0; i < sz; i++) {
        definition * d = m_defs[i];
        if (d == nullptr)
            continue;
        switch (d->get_kind()) {
        case constraint::MONOMIAL:
            del_monomial(static_cast<monomial*>(d));
            break;
        case constraint::POLYNOMIAL:
            del_sum(static_cast<polynomial*>(d));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
}

template<typename C>
void context_t<C>::display_constraints(std::ostream & out, bool use_star) const {
    // display definitions
    for (unsigned i = 0; i < num_vars(); i++) {
        if (is_definition(i)) {
            (*m_display_proc)(out, i);
            out << " = ";
            display_definition(out, m_defs[i], use_star);
            out << "\n";
        }
    }
    // display units
    for (unsigned i = 0; i < m_unit_clauses.size(); i++) {
        ineq * a = UNTAG(ineq*, m_unit_clauses[i]);
        a->display(out, nm(), *m_display_proc); out << "\n";
    }
    // display clauses
    for (unsigned i = 0; i < m_clauses.size(); i++) {
        m_clauses[i]->display(out, nm(), *m_display_proc); out << "\n";
    }
}

// -----------------------------------
//
// Propagation
//
// -----------------------------------

template<typename C>
void context_t<C>::set_conflict(var x, node * n) {
    m_num_conflicts++;
    n->set_conflict(x);
    remove_from_leaf_dlist(n);
}

template<typename C>
bool context_t<C>::may_propagate(bound * b, constraint * c, node * n) {
    SASSERT(b != 0 && c != 0);
    TRACE("may_propagate_bug", display(tout, b); tout << " | "; display(tout, c); tout << "\nresult: " << (b->timestamp() > c->timestamp()) << ", " << b->timestamp() << ", " << c->timestamp() << "\n";);
    return b->timestamp() >= c->timestamp();
}

// Normalization for integer bounds
template<typename C>
void context_t<C>::normalize_bound(var x, numeral & val, bool lower, bool & open) {
    if (is_int(x)) {
        // adjust integer bound
        if (!nm().is_int(val))
            open = false; // performing ceil/floor
        if (lower) {
            nm().ceil(val, val);
        }
        else {
            nm().floor(val, val);
        }
        if (open) {
            open = false;
            if (lower) {
                C::round_to_minus_inf(nm());
                nm().inc(val);
            }
            else {
                C::round_to_plus_inf(nm());
                nm().dec(val);
            }
        }
    }
}

template<typename C>
bool context_t<C>::relevant_new_bound(var x, numeral const & k, bool lower, bool open, node * n) {
    try {
        bound * curr_lower = n->lower(x);
        bound * curr_upper = n->upper(x);
        SASSERT(curr_lower == 0 || curr_lower->x() == x);
        SASSERT(curr_upper == 0 || curr_upper->x() == x);
        TRACE("subpaving_relevant_bound",
              display(tout, x); tout << " " << (lower ? ">" : "<") << (open ? "" : "=") << " "; nm().display(tout, k); tout << "\n";
              tout << "existing bounds:\n";
              if (curr_lower) { display(tout, curr_lower); tout << "\n"; }
              if (curr_upper) { display(tout, curr_upper); tout << "\n"; });
        if (lower) {
            // If new bound triggers a conflict, then it is relevant.
            if (curr_upper && (nm().gt(k, curr_upper->value()) || ((open || curr_upper->is_open()) && nm().eq(k, curr_upper->value())))) {
                TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
                return true;
            }
            // If m_epsilon is zero, then bound is relevant only if it improves existing bound.
            if (m_zero_epsilon && curr_lower != nullptr && (nm().lt(k, curr_lower->value()) || ((curr_lower->is_open() || !open) && nm().eq(k, curr_lower->value())))) {
                // new lower bound does not improve existing bound
                TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
                return false;
            }
            if (curr_upper == nullptr && nm().lt(m_max_bound, k)) {
                // new lower bound exceeds the :max-bound threshold
                TRACE("subpaving_relevant_bound", tout << "irrelevant because exceeds :max-bound threshold.\n";);
                return false;
            }
            if (!m_zero_epsilon && curr_lower != nullptr) {
                // check if:
                // new-lower > lower + m_epsilon * max(min(upper - lower, |lower|), 1)
                numeral & min       = m_tmp1;
                numeral & abs_lower = m_tmp2;
                nm().set(abs_lower, curr_lower->value());
                nm().abs(abs_lower);
                if (curr_upper != nullptr) {
                    nm().sub(curr_upper->value(), curr_lower->value(), min);
                    if (nm().lt(abs_lower, min))
                        nm().set(min, abs_lower);
                }
                else {
                    nm().set(min, abs_lower);
                }
                numeral & delta    = m_tmp3;
                nm().set(delta, 1);
                if (nm().gt(min, delta))
                    nm().set(delta, min);
                nm().mul(delta, m_epsilon, delta);
                nm().add(curr_lower->value(), delta, delta);
                TRACE("subpaving_relevant_bound_bug",
                      tout << "k: "; nm().display(tout, k);
                      tout << ", delta: "; nm().display(tout, delta); tout << "\n";
                      tout << "curr_lower: "; nm().display(tout, curr_lower->value());
                      tout << ", min: "; nm().display(tout, min); tout << "\n";);
                if (nm().le(k, delta)) {
                    TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound to at least ";
                          nm().display(tout, delta); tout << "\n";);
                    return false;
                }
            }
        }
        else {
            // If new bound triggers a conflict, then it is relevant.
            if (curr_lower && (nm().gt(curr_lower->value(), k) || ((open || curr_lower->is_open()) && nm().eq(k, curr_lower->value())))) {
                TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
                return true;
            }
            // If m_epsilon is zero, then bound is relevant only if it improves existing bound.
            if (m_zero_epsilon && curr_upper != nullptr && (nm().lt(curr_upper->value(), k) || ((curr_upper->is_open() || !open) && nm().eq(k, curr_upper->value())))) {
                // new upper bound does not improve existing bound
                TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
                return false;
            }
            if (curr_lower == nullptr && nm().lt(k, m_minus_max_bound)) {
                // new upper bound exceeds the -:max-bound threshold
                TRACE("subpaving_relevant_bound", tout << "irrelevant because exceeds -:max-bound threshold.\n";);
                return false;
            }
            if (!m_zero_epsilon && curr_upper != nullptr) {
                // check if:
                // new-upper < upper - m_epsilon * max(min(upper - lower, |upper|), 1)
                numeral & min       = m_tmp1;
                numeral & abs_upper = m_tmp2;
                nm().set(abs_upper, curr_upper->value());
                nm().abs(abs_upper);
                if (curr_lower != nullptr) {
                    nm().sub(curr_upper->value(), curr_lower->value(), min);
                    if (nm().lt(abs_upper, min))
                        nm().set(min, abs_upper);
                }
                else {
                    nm().set(min, abs_upper);
                }
                numeral & delta    = m_tmp3;
                nm().set(delta, 1);
                if (nm().gt(min, delta))
                    nm().set(delta, min);
                nm().mul(delta, m_epsilon, delta);
                nm().sub(curr_upper->value(), delta, delta);
                if (nm().ge(k, delta)) {
                    TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound to at least ";
                          nm().display(tout, delta); tout << "\n";);
                    return false;
                }
            }
        }
        TRACE("subpaving_relevant_bound", tout << "new bound is relevant\n";);
        return true;
    }
    catch (const typename C::exception &) {
        // arithmetic module failed.
        set_arith_failed();
        return false;
    }
}


template<typename C>
bool context_t<C>::is_zero(var x, node * n) const {
    // Return true if lower(x) == upper(x) == 0 at n
    bound * l = n->lower(x);
    bound * u = n->upper(x);
    return l != nullptr && u != nullptr && nm().is_zero(l->value()) && nm().is_zero(u->value()) && !l->is_open() && !u->is_open();
}

template<typename C>
bool context_t<C>::is_upper_zero(var x, node * n) const {
    // Return true if upper(x) is zero at node n
    bound * u = n->upper(x);
    return u != nullptr && nm().is_zero(u->value()) && !u->is_open();
}

template<typename C>
bool context_t<C>::conflicting_bounds(var x, node * n) const {
    // Return true if upper(x) < lower(x) at node n
    bound * l = n->lower(x);
    bound * u = n->upper(x);
    return l != nullptr && u != nullptr && (nm().lt(u->value(), l->value()) || ((l->is_open() || u->is_open()) && nm().eq(u->value(), l->value())));
}

/**
   \brief Return the truth value of the inequality t in node n.

   The result may be l_true (True), l_false (False), or l_undef(Unknown).
*/
template<typename C>
lbool context_t<C>::value(ineq * t, node * n) {
    var x = t->x();
    bound * u = n->upper(x);
    bound * l = n->lower(x);
    if (u == nullptr && l == nullptr)
        return l_undef;
    else if (t->is_lower()) {
        if (u != nullptr && (nm().lt(u->value(), t->value()) || ((u->is_open() || t->is_open()) && nm().eq(u->value(), t->value()))))
            return l_false;
        else if (l != nullptr && (nm().gt(l->value(), t->value()) || ((l->is_open() || !t->is_open()) && nm().eq(l->value(), t->value()))))
            return l_true;
        else
            return l_undef;
    }
    else {
        if (l != nullptr && (nm().gt(l->value(), t->value()) || ((l->is_open() || t->is_open()) && nm().eq(l->value(), t->value()))))
            return l_false;
        else if (u != nullptr && (nm().lt(u->value(), t->value()) || ((u->is_open() || !t->is_open()) && nm().eq(u->value(), t->value()))))
            return l_true;
        else
            return l_undef;
    }
}

template<typename C>
void context_t<C>::propagate_clause(clause * c, node * n) {
    TRACE("propagate_clause", tout << "propagate using:\n"; display(tout, c); tout << "\n";);
    m_num_visited++;
    c->set_visited(m_timestamp);
    unsigned sz = c->size();
    unsigned j  = UINT_MAX;
    for (unsigned i = 0; i < sz; i++) {
        ineq * atom = (*c)[i];
        switch (value(atom, n)) {
        case l_true:
            return; // clause was already satisfied at n
        case l_false:
            break;
        case l_undef:
            if (j != UINT_MAX)
                return; // clause has more than one unassigned literal
            j = i;
            break;
        }
    }
    if (j == UINT_MAX) {
        // Clause is in conflict, use first atom to trigger inconsistency
        j = 0;
    }
    ineq * a = (*c)[j];
    TRACE("propagate_clause", tout << "propagating inequality: "; display(tout, a); tout << "\n";);
    propagate_bound(a->x(), a->value(), a->is_lower(), a->is_open(), n, justification(c));
    // A clause can propagate only once.
    // So, we can safely set its timestamp again to avoid another useless visit.
    c->set_visited(m_timestamp);
}

template<typename C>
void context_t<C>::propagate_polynomial(var x, node * n, var y) {
    SASSERT(y != null_var);
    SASSERT(is_polynomial(x));
    polynomial * p = get_polynomial(x);
    unsigned sz    = p->size();
    interval & r   = m_i_tmp1; r.set_mutable();
    interval & v   = m_i_tmp2;
    interval & av  = m_i_tmp3; av.set_mutable();
    if (x == y) {
        for (unsigned i = 0; i < sz; i++) {
            var z = p->x(i);
            v.set_constant(n, z);
            im().mul(p->a(i), v, av);
            if (i == 0)
                im().set(r, av);
            else
                im().add(r, av, r);
        }
        // r contains the deduced bounds for x == y
    }
    else {
        v.set_constant(n, x);
        numeral & a = m_tmp1;
        im().set(r, v);
        for (unsigned i = 0; i < sz; i++) {
            var z = p->x(i);
            if (z != y) {
                v.set_constant(n, z);
                im().mul(p->a(i), v, av);
                im().sub(r, av, r);
            }
            else {
                nm().set(a, p->a(i));
                TRACE("propagate_polynomial_bug", tout << "a: "; nm().display(tout, a); tout << "\n";);
            }
        }
        TRACE("propagate_polynomial_bug", tout << "r before mul 1/a: "; im().display(tout, r); tout << "\n";);
        im().div(r, a, r);
        TRACE("propagate_polynomial_bug", tout << "r after mul 1/a:  "; im().display(tout, r); tout << "\n";);
        // r contains the deduced bounds for y.
    }
    // r contains the deduced bounds for y.
    if (!r.m_l_inf) {
        normalize_bound(y, r.m_l_val, true, r.m_l_open);
        if (relevant_new_bound(y, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(y, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
    }
    if (!r.m_u_inf) {
        normalize_bound(y, r.m_u_val, false, r.m_u_open);
        if (relevant_new_bound(y, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(y, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
void context_t<C>::propagate_polynomial(var x, node * n) {
    TRACE("propagate_polynomial", tout << "propagate_polynomial: "; display(tout, x); tout << "\n";);
    TRACE("propagate_polynomial_detail", display_bounds(tout, n););
    SASSERT(is_polynomial(x));
    polynomial * p = get_polynomial(x);
    p->set_visited(m_timestamp);
    var unbounded_var = null_var;
    if (is_unbounded(x, n))
        unbounded_var = x;
    unsigned sz = p->size();
    for (unsigned i = 0; i < sz; i++) {
        var y = p->x(i);
        if (is_unbounded(y, n)) {
            if (unbounded_var != null_var)
                return; // no propagation is possible.
            unbounded_var = y;
        }
    }
    TRACE("propagate_polynomial", tout << "unbounded_var: "; display(tout, unbounded_var); tout << "\n";);

    if (unbounded_var != null_var) {
        propagate_polynomial(x, n, unbounded_var);
    }
    else {
        propagate_polynomial(x, n, x);
        for (unsigned i = 0; i < sz; i++) {
            if (inconsistent(n))
                return;
            propagate_polynomial(x, n, p->x(i));
        }
    }
}

template<typename C>
void context_t<C>::propagate_monomial(var x, node * n) {
    TRACE("propagate_monomial", tout << "propagate_monomial: "; display(tout, x); tout << "\n";);
    SASSERT(is_monomial(x));
    SASSERT(!inconsistent(n));
    monomial * m = get_monomial(x);
    m->set_visited(m_timestamp);
    bool found_unbounded = false;
    bool found_zero      = false;
    bool x_is_unbounded  = false;
    unsigned sz = m->size();
    for (unsigned i = 0; i < sz; i++) {
        var y = m->x(i);
        if (is_zero(y, n)) {
            found_zero = true;
        }
        if (m->degree(i) % 2 == 0) {
            if (is_upper_zero(y, n)) {
                found_zero = true;
            }
            continue; // elements with even power always produce a lower bound
        }
        if (is_unbounded(y, n)) {
            found_unbounded = true;
        }
    }
    TRACE("propagate_monomial", tout << "found_zero: " << found_zero << ", found_unbounded: " << found_unbounded << "\n";);
    if (found_zero) {
        if (!is_zero(x, n)) {
            // x must be zero
            numeral & zero = m_tmp1;
            nm().set(zero, 0);
            propagate_bound(x, zero, true,  false, n, justification(x));
            if (inconsistent(n))
                return;
            propagate_bound(x, zero, false, false, n, justification(x));
        }
        // no need to downward propagation
        return;
    }
    x_is_unbounded = n->is_unbounded(x);
    if (!found_unbounded)
        propagate_monomial_upward(x, n);
    if (inconsistent(n))
        return;
    if (!x_is_unbounded) {
        unsigned bad_pos = UINT_MAX;
        interval & aux   = m_i_tmp1;
        for (unsigned i = 0; i < sz; i++) {
            aux.set_constant(n, m->x(i));
            if (im().contains_zero(aux)) {
                if (bad_pos != UINT_MAX)
                    return; // there is more than one position that contains zero, so downward propagation is not possible.
                bad_pos = i;
            }
        }
        if (bad_pos == UINT_MAX) {
            // we can use all variables for downward propagation.
            for (unsigned i = 0; i < sz; i++) {
                if (inconsistent(n))
                    return;
                propagate_monomial_downward(x, n, i);
            }
        }
        else {
            propagate_monomial_downward(x, n, bad_pos);
        }
    }
}

template<typename C>
void context_t<C>::propagate_monomial_upward(var x, node * n) {
    SASSERT(is_monomial(x));
    monomial * m = get_monomial(x);
    unsigned sz  = m->size();
    interval & r  = m_i_tmp1; r.set_mutable();
    interval & y  = m_i_tmp2;
    interval & yk = m_i_tmp3; yk.set_mutable();
    for (unsigned i = 0; i < sz; i++) {
        y.set_constant(n, m->x(i));
        im().power(y, m->degree(i), yk);
        if (i == 0)
            im().set(r, yk);
        else
            im().mul(r, yk, r);
    }
    // r contains the new bounds for x
    if (!r.m_l_inf) {
        normalize_bound(x, r.m_l_val, true, r.m_l_open);
        if (relevant_new_bound(x, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(x, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
    }
    if (!r.m_u_inf) {
        normalize_bound(x, r.m_u_val, false, r.m_u_open);
        if (relevant_new_bound(x, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(x, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
void context_t<C>::propagate_monomial_downward(var x, node * n, unsigned j) {
    TRACE("propagate_monomial", tout << "propagate_monomial_downward: "; display(tout, x); tout << ", j: " << j << "\n";
          display(tout, get_monomial(x)); tout << "\n";);
    SASSERT(is_monomial(x));
    monomial * m = get_monomial(x);
    SASSERT(j < m->size());
    unsigned sz = m->size();

    interval & r = m_i_tmp3;
    if (sz > 1) {
        interval & d  = m_i_tmp1; d.set_mutable();
        interval & y  = m_i_tmp2;
        interval & yk = m_i_tmp3; yk.set_mutable();
        bool first = true;
        for (unsigned i = 0; i < sz; i++) {
            if (i == j)
                continue;
            y.set_constant(n, m->x(i));
            im().power(y, m->degree(i), yk);
            if (first)
                im().set(d, yk);
            else {
                im().mul(d, yk, r);
                im().set(d, r);
                first = false;
            }
        }       
        if (im().contains_zero(d)) {
            im().reset_lower(r);
            im().reset_upper(r);
        }
        else {
            interval& aux = m_i_tmp2;
            aux.set_constant(n, x);
            im().div(aux, d, r);
        }
    }
    else {
        SASSERT(sz == 1);
        SASSERT(j == 0);
        interval & aux  = m_i_tmp2;
        aux.set_constant(n, x);
        im().set(r, aux);
    }
    unsigned deg = m->degree(j);
    if (deg > 1) {
        if (deg % 2 == 0 && im().lower_is_neg(r))
            return; // If d is even, we can't take the nth-root when lower(r) is negative.
        im().xn_eq_y(r, deg, m_nth_root_prec, r);
    }
    var y = m->x(j);
    // r contains the new bounds for y
    if (!r.m_l_inf) {
        normalize_bound(y, r.m_l_val, true, r.m_l_open);
        if (relevant_new_bound(y, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(y, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
    }
    if (!r.m_u_inf) {
        normalize_bound(y, r.m_u_val, false, r.m_u_open);
        if (relevant_new_bound(y, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(y, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
bool context_t<C>::most_recent(bound * b, node * n) const {
    var x = b->x();
    if (b->is_lower())
        return n->lower(x) == b;
    else
        return n->upper(x) == b;
}

template<typename C>
void context_t<C>::add_recent_bounds(node * n) {
    SASSERT(m_queue.empty());
    bound * old_b = n->parent_trail_stack();
    bound * b     = n->trail_stack();
    while (b != old_b) {
        if (most_recent(b, n)) {
            b->set_timestamp(m_timestamp);
            m_queue.push_back(b);
        }
        b = b->prev();
    }
}

template<typename C>
void context_t<C>::propagate_def(var x, node * n) {
    SASSERT(is_definition(x));
    m_num_visited++;
    definition * d = m_defs[x];
    switch (d->get_kind()) {
    case constraint::MONOMIAL:
        propagate_monomial(x, n);
        break;
    case constraint::POLYNOMIAL:
        propagate_polynomial(x, n);
        break;
    default:
        break;
    }
}

template<typename C>
void context_t<C>::propagate(node * n, bound * b) {
    var x = b->x();
    TRACE("subpaving_propagate", tout << "propagate: "; display(tout, b); tout << ", timestamp: " << b->timestamp() << "\n";);
    typename watch_list::const_iterator it  = m_wlist[x].begin();
    typename watch_list::const_iterator end = m_wlist[x].end();
    for (; it != end; ++it) {
        if (inconsistent(n))
            return;
        watched const & w = *it;
        try {
            if (w.is_clause()) {
                clause * c = w.get_clause();
                if (may_propagate(b, c, n)) {
                    propagate_clause(c, n);
                }
            }
            else {
                var y = w.get_var();
                definition * d = m_defs[y];
                if (may_propagate(b, d, n)) {
                    propagate_def(y, n);
                }
            }
        }
        catch (const typename C::exception &) {
            // arithmetic module failed, ignore constraint
            set_arith_failed();
        }
    }
    if (inconsistent(n))
        return;
    if (is_definition(x)) {
        definition * d = m_defs[x];
        if (may_propagate(b, d, n)) {
            propagate_def(x, n);
        }
    }
}

template<typename C>
void context_t<C>::propagate(node * n) {
    unsigned num_nodes = num_vars();
    while (!inconsistent(n) && m_qhead < m_queue.size() && 2*m_qhead < num_nodes) {
        checkpoint();
        bound * b = m_queue[m_qhead];
        SASSERT(is_bound_of(b, n));
        m_qhead++;
        propagate(n, b);
    }
    m_queue.reset();
    m_qhead = 0;
}

template<typename C>
void context_t<C>::propagate_all_definitions(node * n) {
    unsigned num = num_vars();
    for (unsigned x = 0; x < num; x++) {
        if (inconsistent(n))
            break;
        if (is_definition(x))
            propagate_def(x, n);
    }
}

// -----------------------------------
//
// Main
//
// -----------------------------------

template<typename C>
void context_t<C>::assert_units(node * n) {
    typename ptr_vector<ineq>::const_iterator it  = m_unit_clauses.begin();
    typename ptr_vector<ineq>::const_iterator end = m_unit_clauses.end();
    for (; it != end; ++it) {
        checkpoint();
        ineq * a = UNTAG(ineq*, *it);
        bool axiom = GET_TAG(*it) != 0;
        TRACE("subpaving_init", tout << "asserting: "; display(tout, a); tout << ", axiom: " << axiom << "\n";);
        if (a->x() == null_var)
            continue;
        propagate_bound(a->x(), a->value(), a->is_lower(), a->is_open(), n, justification(axiom));
        if (inconsistent(n))
            break;
    }
    TRACE("subpaving_init", tout << "bounds after init\n"; display_bounds(tout, n););
}

template<typename C>
void context_t<C>::init() {
    SASSERT(m_root       == 0);
    SASSERT(m_leaf_head  == 0);
    SASSERT(m_leaf_tail  == 0);
    m_timestamp = 0;
    m_root      = mk_node();
    SASSERT(m_leaf_head == m_root);
    SASSERT(m_leaf_tail == m_root);
    TRACE("subpaving_init", display_constraints(tout););
    assert_units(m_root);
    propagate_all_definitions(m_root);
    propagate(m_root);
    TRACE("subpaving_init", tout << "root bounds after propagation\n"; display_bounds(tout, m_root););
    SASSERT(check_invariant());
}

template<typename C>
void context_t<C>::operator()() {
    if (m_root == nullptr)
        init();
    TRACE("subpaving_stats", statistics st; collect_statistics(st); tout << "statistics:\n"; st.display_smt2(tout););
    TRACE("subpaving_main", display_params(tout););
    while (m_leaf_head != nullptr) {
        checkpoint();
        SASSERT(m_queue.empty());
        if (m_num_nodes > m_max_nodes)
            break;
        node * n = (*m_node_selector)(m_leaf_head, m_leaf_tail);
        if (n == nullptr)
            break;
        TRACE("subpaving_main", tout << "selected node: #" << n->id() << ", depth: " << n->depth() << "\n";);
        remove_from_leaf_dlist(n);
        if (n != m_root) {
            add_recent_bounds(n);
            propagate(n);
        }
        TRACE("subpaving_main", tout << "node #" << n->id() << " after propagation\n";
              display_bounds(tout, n););
        if (n->inconsistent()) {
            TRACE("subpaving_main", tout << "node #" << n->id() << " is inconsistent.\n";);
            // TODO: conflict resolution
            continue;
        }
        if (n->depth() >= m_max_depth) {
            TRACE("subpaving_main", tout << "maximum depth reached, skipping node #" << n->id() << "\n";);
            continue;
        }
        var x = (*m_var_selector)(n);
        TRACE("subpaving_main", tout << "splitting variable: "; display(tout, x); tout << "\n";);
        if (x != null_var) {
            (*m_node_splitter)(n, x);
            m_num_splits++;
            // remove inconsistent children
        }
    }
    TRACE("subpaving_stats", statistics st; collect_statistics(st); tout << "statistics:\n"; st.display_smt2(tout););
}

template<typename C>
void context_t<C>::display_bounds(std::ostream & out) const {
    ptr_vector<node> leaves;
    collect_leaves(leaves);
    typename ptr_vector<node>::const_iterator it  = leaves.begin();
    typename ptr_vector<node>::const_iterator end = leaves.end();
    for (bool first = true; it != end; ++it) {
        node * n = *it;
        if (first)
            first = false;
        else
            out << "=========\n";
        display_bounds(out, n);
    }
}

// -----------------------------------
//
// Statistics
//
// -----------------------------------

template<typename C>
void context_t<C>::reset_statistics() {
    m_num_conflicts = 0;
    m_num_mk_bounds = 0;
    m_num_splits    = 0;
    m_num_visited   = 0;
}

template<typename C>
void context_t<C>::collect_statistics(statistics & st) const {
    st.update("conflicts",  m_num_conflicts);
    st.update("new bounds", m_num_mk_bounds);
    st.update("splits",     m_num_splits);
    st.update("nodes",      m_num_nodes);
    st.update("visited",    m_num_visited);
}

// -----------------------------------
//
// Debugging support
//
// -----------------------------------

template<typename C>
bool context_t<C>::is_bound_of(bound * b, node * n) const {
    bound * c = n->trail_stack();
    while (c != nullptr) {
        if (c == b)
            return true;
        if (c->timestamp() <= b->timestamp())
            return false;
        c = c->prev();
    }
    return false;
}

template<typename C>
bool context_t<C>::check_leaf_dlist() const {
    node * n = m_leaf_head;
    while (n != nullptr) {
        node * next = n->next();
        SASSERT(next != 0 || m_leaf_tail  == n);
        SASSERT(next == 0 || next->prev() == n);
        n = next;
    }
    return true;
}

template<typename C>
bool context_t<C>::check_tree() const {
    ptr_buffer<node> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        while (c != nullptr) {
            SASSERT(c->parent() == n);
            todo.push_back(c);
            c = c->next_sibling();
        }
    }
    return true;
}

template<typename C>
bool context_t<C>::check_invariant() const {
    SASSERT(check_tree());
    SASSERT(check_leaf_dlist());
    return true;
}


};
