/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aig.cpp

Abstract:

    And-inverted graphs

Author:

    Leonardo (leonardo) 2011-05-13

Notes:

--*/
#include "tactic/aig/aig.h"
#include "tactic/goal.h"
#include "ast/ast_smt2_pp.h"
#include "util/cooperate.h"

#define USE_TWO_LEVEL_RULES
#define FIRST_NODE_ID (UINT_MAX/2)

struct aig;

class aig_lit {
    friend class aig_ref;
    aig * m_ref;
public:
    aig_lit(aig * n = nullptr):m_ref(n) {}
    aig_lit(aig_ref const & r):m_ref(static_cast<aig*>(r.m_ref)) {}
    bool is_inverted() const { return (reinterpret_cast<size_t>(m_ref) & static_cast<size_t>(1)) == static_cast<size_t>(1); }
    void invert() { m_ref = reinterpret_cast<aig*>(reinterpret_cast<size_t>(m_ref) ^ static_cast<size_t>(1)); }
    aig * ptr() const { return reinterpret_cast<aig*>(reinterpret_cast<size_t>(m_ref) & ~static_cast<size_t>(1)); }
    aig * ptr_non_inverted() const { SASSERT(!is_inverted()); return m_ref; }
    bool is_null() const { return m_ref == nullptr; }
    friend bool operator==(aig_lit const & r1, aig_lit const & r2) { return r1.m_ref == r2.m_ref; }
    friend bool operator!=(aig_lit const & r1, aig_lit const & r2) { return r1.m_ref != r2.m_ref; }
    aig_lit & operator=(aig_lit const & r) { m_ref = r.m_ref; return *this; }
    static aig_lit null;
};

aig_lit aig_lit::null;

struct aig {
    unsigned m_id;
    unsigned m_ref_count;
    aig_lit  m_children[2];
    unsigned m_mark:1;
    aig() {}
};

#if Z3DEBUG
inline bool is_true(aig_lit const & r) { return !r.is_inverted() && r.ptr_non_inverted()->m_id == 0; }
#endif
// inline bool is_false(aig_lit const & r) { return r.is_inverted() && r.ptr()->m_id == 0; }
inline bool is_var(aig * n) { return n->m_children[0].is_null(); }
inline bool is_var(aig_lit const & n) { return is_var(n.ptr()); }
inline unsigned id(aig_lit const & n) { return n.ptr()->m_id; }
inline unsigned ref_count(aig_lit const & n) { return n.ptr()->m_ref_count; }
inline aig_lit left(aig * n) { return n->m_children[0]; }
inline aig_lit right(aig * n) { return n->m_children[1]; }
inline aig_lit left(aig_lit const & n) { return left(n.ptr()); }
inline aig_lit right(aig_lit const & n) { return right(n.ptr()); }

inline unsigned to_idx(aig * p) { SASSERT(!is_var(p)); return p->m_id - FIRST_NODE_ID; }


static void unmark(unsigned sz, aig * const * ns) {
    for (unsigned i = 0; i < sz; i++) {
        ns[i]->m_mark = false;
    }
}

struct aig_hash {
    unsigned operator()(aig * n) const {
        SASSERT(!is_var(n));
        return hash_u_u(id(n->m_children[0]), id(n->m_children[1]));
    }
};

struct aig_eq {
    bool operator()(aig * n1, aig * n2) const {
        SASSERT(!is_var(n1));
        SASSERT(!is_var(n2));
        return 
            n1->m_children[0] == n2->m_children[0] &&
            n1->m_children[1] == n2->m_children[1];
    }
};

class aig_table : public chashtable<aig*, aig_hash, aig_eq> {
public:
};

struct aig_lit_lt {
    bool operator()(aig_lit const & l1, aig_lit const & l2) const { 
        if (id(l1) < id(l2)) return true;
        if (id(l1) == id(l2)) return l1.is_inverted() && !l2.is_inverted();
        return false;
    }
};

struct aig_manager::imp {
    id_gen                   m_var_id_gen;
    id_gen                   m_node_id_gen;
    aig_table                m_table;
    unsigned                 m_num_aigs;
    expr_ref_vector          m_var2exprs;
    small_object_allocator   m_allocator;
    ptr_vector<aig>          m_to_delete;
    aig_lit                  m_true;
    aig_lit                  m_false;
    bool                     m_default_gate_encoding;
    unsigned long long       m_max_memory;

    void dec_ref_core(aig * n) {
        SASSERT(n->m_ref_count > 0);
        n->m_ref_count--;
        if (n->m_ref_count == 0)
            m_to_delete.push_back(n);
    }

    void checkpoint() {
        if (memory::get_allocation_size() > m_max_memory)
            throw aig_exception(TACTIC_MAX_MEMORY_MSG);
        if (m().canceled())
            throw aig_exception(m().limit().get_cancel_msg());
        cooperate("aig");
    }

    void dec_ref_core(aig_lit const & r) { dec_ref_core(r.ptr()); }

    void dec_ref_result(aig * n) { SASSERT(n->m_ref_count > 0); n->m_ref_count--; }
    void dec_ref_result(aig_lit const & r) { dec_ref_result(r.ptr()); }
    
    void process_to_delete() {
        while (!m_to_delete.empty()) {
            aig * n = m_to_delete.back();
            m_to_delete.pop_back();
            delete_node(n);
        }
    }

    void delete_node(aig * n) {
        TRACE("aig_lit_count", tout << "deleting: "; display_ref(tout, n); tout << "\n";);
        SASSERT(m_num_aigs > 0);
        m_num_aigs--;
        if (is_var(n)) {
            m_var_id_gen.recycle(n->m_id);
            m_var2exprs.set(n->m_id, nullptr);
        }
        else {
            m_table.erase(n);
            m_node_id_gen.recycle(n->m_id);
            dec_ref_core(n->m_children[0]);
            dec_ref_core(n->m_children[1]);
        }
        m_allocator.deallocate(sizeof(aig), n);
    }

    aig * allocate_node() {
        return static_cast<aig*>(m_allocator.allocate(sizeof(aig)));
    }

    aig * mk_var(expr * t) {
        m_num_aigs++;
        aig * r          = allocate_node();
        r->m_id          = m_var_id_gen.mk();
        r->m_ref_count   = 0;
        r->m_mark        = false;
        r->m_children[0] = aig_lit();
        SASSERT(r->m_id <= m_var2exprs.size());
        if (r->m_id == m_var2exprs.size())
            m_var2exprs.push_back(t);
        else
            m_var2exprs.set(r->m_id, t);
        return r;
    }

    aig_lit mk_node_core(aig_lit const & l, aig_lit const & r) {
        aig * new_node = allocate_node();
        new_node->m_children[0] = l;
        new_node->m_children[1] = r;
        aig * old_node = m_table.insert_if_not_there(new_node);
        if (old_node != new_node) {
            m_allocator.deallocate(sizeof(aig), new_node);
            return aig_lit(old_node);
        }
        m_num_aigs++;
        new_node->m_id        = m_node_id_gen.mk();
        new_node->m_ref_count = 0;
        new_node->m_mark      = false;
        SASSERT(new_node->m_ref_count == 0);
        inc_ref(l);
        inc_ref(r);
        return aig_lit(new_node);
    }

    bool is_not_eq(aig_lit const & l, aig_lit const & r) const {
        return l.ptr() == r.ptr() && l.is_inverted() != r.is_inverted();
    }

    /**
       \brief Create an AIG representing (l and r)
       Apply two-level minimization rules that guarantee that
       locally the size is decreasing, and globally is not increasing.
    */
    aig_lit mk_node(aig_lit l, aig_lit r) {
    start:
        bool sign1 = l.is_inverted();
        aig * n1   = l.ptr();
        bool sign2 = r.is_inverted();
        aig * n2   = r.ptr();
        
        if (n1->m_id == 0) {
            if (sign1)
                return m_false; // false and r 
            else
                return r; // true and r
        }
        
        if (n2->m_id == 0) {
            if (sign2)
                return m_false; // l and false;
            else
                return l; // l and true;
        }

        if (n1 == n2) {
            if (sign1 == sign2)
                return l;  // l and l;
            else
                return m_false; // l and not l
        }

#ifdef USE_TWO_LEVEL_RULES
        if (!is_var(n1)) {
            aig_lit a = n1->m_children[0];
            aig_lit b = n1->m_children[1];

            if (is_not_eq(a, r) || is_not_eq(b, r)) {
                if (sign1) {
                    // substitution
                    return r;  // (not (a and b)) and r  --> r   IF  a = (not r) or b = (not r)
                }
                else {
                    // contradiction
                    return m_false;  // (a and b) and r  --> false  IF a = (not r) or b = (not r)
                }
            }
            if (a == r) {
                if (sign1) {
                    // substitution
                    // not (a and b) and r  --> (not b) and r   IF  a == r
                    l = b;
                    l.invert();
                    goto start;
                }
                else {
                    // substitution
                    return l; // (a and b) and r --> (a and b)  IF  a = r 
                }
            }
            if  (b == r) {
                if (sign1) {
                    // substitution
                    // not (a and b) and r --> (not a) and r   IF b == r
                    l = a;
                    l.invert();
                    goto start;
                }
                else {
                    // substitution
                    return l; // (a and b) and r --> (a and b)  IF b = r;
                }
            }
        
            if (!is_var(n2)) {
                aig_lit c = n2->m_children[0];
                aig_lit d = n2->m_children[1];

                if (!sign1 && !sign2) {
                    // contradiction
                    if (is_not_eq(a, c) || is_not_eq(a, d) || is_not_eq(b, c) || is_not_eq(b, d))
                        return m_false; // (a and b) and (c and d)  --> false  IF  a = not(c) OR a = not(d) or b = not(c) or b = not(d)
                    // idempotence
                    if (a == c || b == c) {
                        r = d;          // (a and b) and (c and d) --> (a and b) and d   IF a == c or b == c
                        goto start; 
                    }
                    // idempotence
                    if (b == c || b == d) {
                        l = a;          //  (a and b) and (c and d) --> a and (c and d)  IF b == c or b == d
                        goto start; 
                    }
                    // idempotence
                    if (a == d || b == d) {
                        r = c;
                        goto start;    //  (a and b) and (c and d) --> (a and b) and c   IF a == d or b == d
                    }
                    // idempotence
                    if (a == c || a == d) {
                        l = b;         //  (a and b) and (c and d) --> b and (c and d)  IF a == c or a == d
                        goto start;
                    }
                }

                if (sign1 && !sign2) {
                    // subsumption
                    if (is_not_eq(a, c) || is_not_eq(a, d) || is_not_eq(b, c) || is_not_eq(b, d))
                        return r;      // not (a and b) and (c and d) --> (c and d)

                    // substitution
                    if (b == c || b == d) {
                        // not (a and b) and (c and d) --> (not a) and (c and d)
                        a.invert();
                        l = a;
                        goto start;
                    }

                    // substitution
                    if (a == c || a == d) {
                        // not (a and b) and (c and d) --> (not b) and (c and d)
                        b.invert();
                        l = b;
                        goto start;
                    }
                }

                if (!sign1 && sign2) {
                    // subsumption
                    if (is_not_eq(a, c) || is_not_eq(a, d) || is_not_eq(b, c) || is_not_eq(b, d))
                        return l;      // (a and b) and not (c and d) --> (a and b)

                    // substitution
                    if (c == a || c == b) {
                        // (a and b) and not (c and d) --> (a and b) and (not d);
                        d.invert();
                        r = d;
                        goto start;
                    }

                    // substitution
                    if (d == a || d == b) {
                        // (a and b) and not (c and d) --> (a and b) and (not c);
                        c.invert();
                        r = c;
                        goto start;
                    }
                }
                
                if (sign1 && sign2) {
                    // resolution
                    if (a == c && is_not_eq(b, d)) {
                        a.invert();    // (not (a and b)) and (not (a and (not b))) --> not a     
                        return a;
                    }
                    SASSERT(!(a == d && is_not_eq(b, c))); // cannot happen because we sort args
                    // resolution
                    if (is_not_eq(a, c) && b == d) {
                        b.invert();   // (not (a and b)) and (not (a and (not b))) --> not b
                        return b;
                    }
                    SASSERT(!(is_not_eq(a, d) && b == c)); // cannot happen because we sort args
                }
            }
        }

        if (!is_var(n2)) {
            aig_lit a = n2->m_children[0];
            aig_lit b = n2->m_children[1];
            if (is_not_eq(l, a) || is_not_eq(l, b)) {
                if (sign2) {
                    // substitution
                    return l;        // l and (not (a and b)) --> l   IF  a = (not l) or b = (not l)
                }
                else {
                    // contradiction
                    return m_false;  // l and (a and b) --> false  IF a = (not l) or b = (not l)
                }
            }
            if (a == l) {
                if (sign2) {
                    // substitution
                    // l and not (a and b) and r --> l and (not b)   IF  a == l
                    r = b;
                    r.invert();
                    goto start;
                }
                else {
                    // substitution
                    return r; // l and (a and b) --> (a and b)  IF  a = l;
                }
            }
            if  (b == l) {
                if (sign2) {
                    // substitution
                    // l and not (a and b) --> l and (not a)   IF b == l
                    r = a;
                    r.invert();
                    goto start;
                }
                else {
                    // substitution
                    return r; // l and (a and b) --> (a and b)  IF  b = l;
                }
            }
        }
#endif

        if (n1->m_id > n2->m_id)
            return mk_node_core(r, l);
        else 
            return mk_node_core(l, r);
    }

    struct expr2aig {
        struct frame {
            app *     m_t;
            unsigned  m_idx;
            unsigned  m_spos;
            frame(app * t, unsigned spos):m_t(t), m_idx(0), m_spos(spos) {}
        };
        imp &                  m;
        svector<frame>         m_frame_stack;
        svector<aig_lit>       m_result_stack;
        obj_map<expr, aig_lit> m_cache;
        
        expr2aig(imp & _m):m(_m) {}
        
        ~expr2aig() {
            obj_map<expr, aig_lit>::iterator it  = m_cache.begin();
            obj_map<expr, aig_lit>::iterator end = m_cache.end();
            for (; it != end; ++it) {
                TRACE("expr2aig", tout << "dec-ref: "; m.display_ref(tout, it->m_value); 
                      tout << " ref-count: " << ref_count(it->m_value) << "\n";);
                m.dec_ref(it->m_value);
            }
            restore_result_stack(0);
        }
        
        void save_result(aig_lit & r) {
            m.inc_ref(r);
            m_result_stack.push_back(r);
        }

        void cache_result(expr * t, aig_lit const & r) {
            TRACE("expr2aig", tout << "caching:\n" << mk_ismt2_pp(t, m.m()) << "\n---> "; m.display_ref(tout, r); tout << "\n";); 
            SASSERT(!m_cache.contains(t));
            m.inc_ref(r);
            m_cache.insert(t, r);
        }
        
        bool is_cached(expr * t) {
            aig_lit r;
            if (m_cache.find(t, r)) {
                save_result(r);
                return true;
            }
            return false;
        }

        void process_var(expr * t) {
            if (is_cached(t))
                return;
            aig_lit r(m.mk_var(t));
            SASSERT(ref_count(r) == 0);
            cache_result(t, r);
            save_result(r);
        }

        void mk_frame(app * t) {
            m_frame_stack.push_back(frame(t, m_result_stack.size()));
        }
        
        bool visit(expr * t) {
            if (is_app(t)) {
                app * tapp = to_app(t);
                if (tapp->get_family_id() == m.m().get_basic_family_id()) {
                    switch (tapp->get_decl_kind()) {
                    case OP_TRUE:    save_result(m.m_true); return true;
                    case OP_FALSE:   save_result(m.m_false); return true; 
                    case OP_EQ:
                        if (!m.m().is_bool(tapp->get_arg(0)))
                            break;
                    case OP_NOT:
                    case OP_OR:      
                    case OP_AND:
                    case OP_XOR:
                    case OP_IMPLIES:
                    case OP_ITE:
                        if (tapp->get_ref_count() > 1 && is_cached(tapp))
                            return true;
                        mk_frame(tapp);
                        return false;
                    default:
                        break;
                    }
                }
                process_var(t);
                return true;
            }
            else {
                // quantifiers and free variables are handled as aig variables                
                process_var(t);
                return true;
            }
        }
        
        void restore_result_stack(unsigned old_sz) {
            unsigned sz = m_result_stack.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++)
                m.dec_ref(m_result_stack[i]);
            m_result_stack.shrink(old_sz);
        }

        void save_node_result(unsigned spos, aig_lit r) {
            m.inc_ref(r);
            restore_result_stack(spos);
            save_result(r);
            SASSERT(ref_count(r) >= 2);
            m.dec_ref(r);
        }
                
        void mk_or(unsigned spos) {
            SASSERT(spos <= m_result_stack.size());
            unsigned num = m_result_stack.size() - spos;
            aig_lit r = m.mk_or(num, m_result_stack.begin() + spos);
            save_node_result(spos, r);
        }

        void mk_and(unsigned spos) {
            SASSERT(spos <= m_result_stack.size());
            unsigned num = m_result_stack.size() - spos;
            aig_lit r = m.mk_and(num, m_result_stack.begin() + spos);
            save_node_result(spos, r);
        }

        void mk_ite(unsigned spos) {
            SASSERT(spos + 3 == m_result_stack.size());
            aig_lit r = m.mk_ite(m_result_stack[spos], m_result_stack[spos+1], m_result_stack[spos+2]);
            save_node_result(spos, r);
        }

        void mk_iff(unsigned spos) {
            SASSERT(spos + 2 == m_result_stack.size());
            aig_lit r = m.mk_iff(m_result_stack[spos], m_result_stack[spos+1]);
            save_node_result(spos, r);
        }
        
        void mk_xor(unsigned spos) {
            SASSERT(spos + 2 == m_result_stack.size());
            aig_lit r = m.mk_xor(m_result_stack[spos], m_result_stack[spos+1]);
            save_node_result(spos, r);
        }

        void mk_implies(unsigned spos) {
            SASSERT(spos + 2 == m_result_stack.size());
            aig_lit r = m.mk_implies(m_result_stack[spos], m_result_stack[spos+1]);
            save_node_result(spos, r);
        }

        void mk_aig(frame & fr) {
            SASSERT(fr.m_t->get_family_id() == m.m().get_basic_family_id());
            switch (fr.m_t->get_decl_kind()) {
            case OP_NOT:
                m_result_stack[fr.m_spos].invert();
                break;
            case OP_OR: 
                mk_or(fr.m_spos);
                break;
            case OP_AND:
                mk_and(fr.m_spos);
                break;
            case OP_EQ:
                SASSERT(m.m().is_bool(fr.m_t->get_arg(0)));
                mk_iff(fr.m_spos);
                break;
            case OP_XOR:
                mk_xor(fr.m_spos);
                break;
            case OP_IMPLIES:
                mk_implies(fr.m_spos);
                break;
            case OP_ITE:
                mk_ite(fr.m_spos);
                break;
            default:
                UNREACHABLE();
            }
            if (fr.m_t->get_ref_count() > 1) {
                cache_result(fr.m_t, m_result_stack.back());
            }
        }
        
        aig_lit operator()(expr * n) {
            SASSERT(check_cache());
            if (!visit(n)) {
                while (!m_frame_stack.empty()) {
                loop:
                    m.checkpoint();
                    frame & fr = m_frame_stack.back();
                    if (fr.m_idx == 0 && fr.m_t->get_ref_count() > 1) {
                        if (is_cached(fr.m_t)) {
                            m_frame_stack.pop_back();
                            continue;
                        }
                    }
                    unsigned num_args = fr.m_t->get_num_args();
                    while (fr.m_idx < num_args) {
                        expr * arg = fr.m_t->get_arg(fr.m_idx);
                        fr.m_idx++;
                        if (!visit(arg))
                            goto loop;
                    }
                    mk_aig(fr);
                    m_frame_stack.pop_back();
                }
            }
            SASSERT(m_result_stack.size() == 1);
            aig_lit r = m_result_stack.back();
            m_result_stack.pop_back();
            m.dec_ref_result(r);
            SASSERT(check_cache());
            return r;
        }

        bool check_cache() const {
            for (auto const& kv : m_cache) {
                VERIFY(ref_count(kv.m_value) > 0);
            }
            return true;
        }
    };

    /**
       \brief Return true if the AIG represents an if-then-else
    */
    template<bool Collect>
    bool is_ite_core(aig * n, aig_lit & c, aig_lit & t, aig_lit & e) const {
        if (is_var(n))
            return false;
        aig_lit l = left(n);
        aig_lit r = right(n);
        if (l.is_inverted() && r.is_inverted()) {
            aig * l_ptr = l.ptr();
            aig * r_ptr = r.ptr();
            if (is_var(l_ptr) || is_var(r_ptr))
                return false;
            aig_lit l1 = left(l_ptr);
            aig_lit l2 = right(l_ptr);
            aig_lit r1 = left(r_ptr); 
            aig_lit r2 = right(r_ptr);
            if (is_not_eq(l1, r1)) {
                if (Collect) {
                    l1.invert(); l2.invert(); r1.invert(); r2.invert();
                    if (l1.is_inverted()) {
                        c = r1; t = l2; e = r2;
                    }
                    else {
                        c = l1; t = r2; e = l2;
                    }
                }
                return true;
            }
            else if (is_not_eq(l1, r2)) {
                if (Collect) {
                    l1.invert(); l2.invert(); r1.invert(); r2.invert();                
                    if (l1.is_inverted()) {
                        c = r2; t = l2; e = r1;
                    }
                    else {
                        c = l1; t = r1; e = l2;
                    }
                }
                return true;
            }
            else if (is_not_eq(l2, r1)) {
                if (Collect) {
                    l1.invert(); l2.invert(); r1.invert(); r2.invert();                
                    if (l2.is_inverted()) {
                        c = r1; t = l1; e = r2;
                    }
                    else {
                        c = l2; t = r2; e = l1;
                    }
                }
                return true;
            }
            else if (is_not_eq(l2, r2)) {
                if (Collect) {
                    l1.invert(); l2.invert(); r1.invert(); r2.invert();                
                    if (l2.is_inverted()) {
                        c = r2; t = l1; e = r1;
                    }
                    else {
                        c = l2; t = r1; e = l1;
                    }
                }
                return true;
            }
        }
        return false;
    }

    bool is_ite(aig * n, aig_lit & c, aig_lit & t, aig_lit & e) const {
        return is_ite_core<true>(n, c, t, e);
    }

    bool is_ite(aig * n) const {
        static aig_lit c, t, e;
        return is_ite_core<false>(n, c, t, e);
    }

    /**
       \brief Return true if the AIG represents an iff
    */
    bool is_iff(aig * n) const {
        if (is_var(n))
            return false;
        aig_lit l = left(n);
        aig_lit r = right(n);
        if (l.is_inverted() && r.is_inverted()) {
            if (is_var(l) || is_var(r))
                return false;
            return is_not_eq(left(l), left(r)) && is_not_eq(right(l), right(r));
        }
        return false;
    }

    expr * var2expr(aig * n) const {
        SASSERT(is_var(n));
        return m_var2exprs[n->m_id];
    }

    struct aig2expr {
        imp &           m;
        ast_manager &   ast_mng;
        enum kind { AIG_AND,       
                    AIG_AUX_AND,  // does not have an associated expr
                    AIG_ITE 
        };
        struct frame {
            aig *       m_node;
            unsigned    m_kind:2;
            unsigned    m_first:1;
            frame(aig * n, kind k):m_node(n), m_kind(k), m_first(true) {}
        };
        expr_ref_vector m_cache;
        svector<frame>  m_frame_stack;

        aig2expr(imp & _m):m(_m), ast_mng(m.m()), m_cache(ast_mng) {}
        
        expr * get_cached(aig * n) {
            if (is_var(n)) {
                return n->m_id == 0 ? ast_mng.mk_true() : m.var2expr(n);
            }
            else {
                CTRACE("aig2expr", !is_cached(n), tout << "invalid get_cached for "; m.display_ref(tout, n); tout << "\n";);
                SASSERT(is_cached(n));
                return m_cache.get(to_idx(n));
            }
        }

        expr * invert(expr * n) {
            if (ast_mng.is_not(n))
                return to_app(n)->get_arg(0);
            if (ast_mng.is_true(n))
                return ast_mng.mk_false();
            SASSERT(!ast_mng.is_false(n));
            return ast_mng.mk_not(n);
        }

        expr * get_cached(aig_lit const & n) {
            if (n.is_inverted())
                return invert(get_cached(n.ptr()));
            else
                return get_cached(n.ptr());
        }

        bool is_cached(aig * n) {
            if (is_var(n))
                return true;
            unsigned idx = to_idx(n);
            if (idx >= m_cache.size()) {
                m_cache.resize(idx+1);
                return false;
            }
            return m_cache.get(idx) != nullptr;
        }

        void cache_result(aig * n, expr * t) {
            unsigned idx = to_idx(n);
            SASSERT(idx < m_cache.size());
            SASSERT(m_cache.get(idx) == 0);
            m_cache.set(idx, t);
        }

        void visit_and_child(aig_lit c, bool & visited) {
            aig * n = c.ptr();
            if (is_cached(n))
                return;
            if (m.is_ite(n))
                m_frame_stack.push_back(frame(n, AIG_ITE));
            else if (!c.is_inverted() && n->m_ref_count == 1)
                m_frame_stack.push_back(frame(n, AIG_AUX_AND));
            else
                m_frame_stack.push_back(frame(n, AIG_AND));
            visited = false;
        }

        void visit_ite_child(aig_lit c, bool & visited) {
            aig * n = c.ptr();
            if (is_cached(n))
                return;
            m_frame_stack.push_back(frame(n, m.is_ite(n) ? AIG_ITE : AIG_AND));
            visited = false;
        }

        ptr_vector<expr> m_and_children;
        ptr_vector<aig>  m_and_todo;

        void add_child(aig_lit c) {
            aig * n = c.ptr();
            if (c.is_inverted()) {
                // adding (not c) since I build an OR node
                m_and_children.push_back(get_cached(n));
                return;
            }
            if (is_cached(n)) {
                m_and_children.push_back(invert(get_cached(n)));
                return;
            }
            SASSERT(n->m_ref_count == 1);
            m_and_todo.push_back(n);
        }

        void mk_and(aig * n) {
            m_and_children.reset();
            m_and_todo.reset();
            add_child(left(n));
            add_child(right(n));
            while (!m_and_todo.empty()) {
                aig * t = m_and_todo.back();
                SASSERT(!is_var(t));
                m_and_todo.pop_back();
                add_child(left(t));
                add_child(right(t));
            }
            expr * r = ast_mng.mk_not(ast_mng.mk_or(m_and_children.size(), m_and_children.c_ptr()));
            cache_result(n, r);
            TRACE("aig2expr", tout << "caching AND "; m.display_ref(tout, n); tout << "\n";);
        }

        void mk_ite(aig * n) {
            aig_lit c, t, e;
            VERIFY(m.is_ite(n, c, t, e));
            if (c.is_inverted()) {
                c.invert();
                std::swap(t, e);
            }
            expr * r;
            if (m.is_not_eq(t, e)) {
                r = ast_mng.mk_iff(get_cached(c), get_cached(t));
            }
            else { 
                r = ast_mng.mk_ite(get_cached(c), get_cached(t), get_cached(e));
            }
            cache_result(n, r);
            TRACE("aig2expr", tout << "caching ITE/IFF "; m.display_ref(tout, n); tout << "\n";);
        }

        /**
           \brief Return an expression representing the negation of p.
        */
        expr * process_root(aig * r) {
            if (is_cached(r))
                return get_cached(r);
            m_frame_stack.push_back(frame(r, m.is_ite(r) ? AIG_ITE : AIG_AND));
            while (!m_frame_stack.empty()) {
                m.checkpoint();
                frame & fr = m_frame_stack.back();
                aig * n    = fr.m_node;
                if (is_cached(n)) {
                    m_frame_stack.pop_back();
                    continue;
                }
                if (fr.m_first) {
                    fr.m_first   = false;
                    bool visited = true;
                    switch (fr.m_kind) {
                    case AIG_AND:
                    case AIG_AUX_AND:
                        visit_and_child(left(n), visited);
                        visit_and_child(right(n), visited);
                        break;
                    case AIG_ITE: {
                        aig_lit a = left(left(n));
                        aig_lit b = right(left(n));
                        aig_lit c = left(right(n));
                        aig_lit d = right(right(n));
                        visit_ite_child(a, visited);
                        visit_ite_child(b, visited);
                        if (c.ptr() != a.ptr() && c.ptr() != b.ptr())
                            visit_ite_child(c, visited);
                        if (d.ptr() != a.ptr() && d.ptr() != b.ptr())
                            visit_ite_child(d, visited);
                        break;
                    }
                    default:
                        UNREACHABLE();
                        break;
                    }
                    if (!visited)
                        continue;
                }
                switch (fr.m_kind){
                case AIG_AUX_AND:
                    // do nothing
                    TRACE("aig2expr", tout << "skipping aux AND "; m.display_ref(tout, n); tout << "\n";);
                    break;
                case AIG_AND:
                    mk_and(n);
                    break;
                case AIG_ITE:
                    mk_ite(n);
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
                m_frame_stack.pop_back();
            }
            return get_cached(r);
        }

        /**
           \brief (Debugging) Naive AIG -> EXPR 
        */
        void naive(aig_lit const & l, expr_ref & r) {
            expr_ref_vector cache(ast_mng);
            ptr_vector<aig> todo;
            todo.push_back(l.ptr());
            while (!todo.empty()) {
                aig * t = todo.back();
                if (is_var(t)) {
                    todo.pop_back();
                    continue;
                }
                unsigned idx = to_idx(t);
                cache.reserve(idx+1);
                if (cache.get(idx) != nullptr) {
                    todo.pop_back();
                    continue;
                }
                bool ok = true;
                for (unsigned i = 0; i < 2; i++) {
                    aig * c = t->m_children[i].ptr();
                    if (!is_var(c) && cache.get(to_idx(c), nullptr) == nullptr) {
                        todo.push_back(c);
                        ok = false;
                    }
                }
                if (!ok) 
                    continue;
                expr * args[2];
                for (unsigned i = 0; i < 2; i++) {
                    aig_lit l = t->m_children[i];
                    aig *   c = l.ptr();
                    if (is_var(c))
                        args[i] = m.m_var2exprs.get(c->m_id);
                    else
                        args[i] = cache.get(to_idx(c), nullptr);
                    if (!l.is_inverted())
                        args[i] = invert(args[i]);
                }
                cache.set(idx, ast_mng.mk_not(ast_mng.mk_or(args[0], args[1])));
                todo.pop_back();
            }
            aig * c = l.ptr();
            if (is_var(c))
                r = m.m_var2exprs.get(c->m_id);
            else
                r = cache.get(to_idx(c));
            if (l.is_inverted())
                r = invert(r);
        }

        void operator()(aig_lit const & l, expr_ref & r) {
            naive(l, r);
        }

        void operator()(aig_lit const & l, goal & g) {
            g.reset();
            sbuffer<aig_lit> roots;
            roots.push_back(l);
            while (!roots.empty()) {
                aig_lit n = roots.back();
                roots.pop_back();
                if (n.is_inverted()) {
                    g.assert_expr(invert(process_root(n.ptr())), nullptr, nullptr);
                    continue;
                }
                aig * p = n.ptr();
                if (m.is_ite(p)) {
                    g.assert_expr(process_root(p), nullptr, nullptr);
                    continue;
                }
                if (is_var(p)) {
                    g.assert_expr(m.var2expr(p), nullptr, nullptr);
                    continue;
                }
                roots.push_back(left(p));
                roots.push_back(right(p));
            }
        }

    };

    struct max_sharing_proc {
        struct frame {
            aig *          m_node;
            unsigned short m_idx;
            frame(aig * n):m_node(n), m_idx(0) {}
        };
        imp &             m;
        svector<frame>    m_frame_stack;
        svector<aig_lit>  m_result_stack;
        svector<aig_lit>  m_cache;
        ptr_vector<aig>   m_saved;

        max_sharing_proc(imp & _m):m(_m) {}

        ~max_sharing_proc() {
            reset_saved();
        }

        void reset_saved() {
            m.dec_array_ref(m_saved.size(), m_saved.c_ptr());
            m_saved.finalize();
        }

        void reset_cache() {
            m_cache.finalize();
            reset_saved();
        }

        void push_result(aig_lit n) {
            m_result_stack.push_back(n);
            if (!n.is_null())
                m.inc_ref(n);
        }

        bool is_cached(aig * p) {
            SASSERT(!is_var(p));
            if (p->m_ref_count <= 1)
                return false;
            unsigned idx = to_idx(p);
            if (idx >= m_cache.size()) {
                m_cache.resize(idx+1, aig_lit::null);
                return false;
            }
            aig_lit c = m_cache[idx];
            if (!c.is_null()) {
                push_result(c);
                return true;
            }
            return false;
        }

        bool visit(aig * p) {
            if (is_var(p)) {
                push_result(nullptr);
                return true;
            }
            if (is_cached(p))
                return true;
            m_frame_stack.push_back(frame(p));
            return false;
        }

        bool visit(aig_lit l) { return visit(l.ptr()); }

        void save_result(aig * o, aig_lit n) {
            SASSERT(!is_var(o));
            if (o->m_ref_count > 1) {
                unsigned idx = to_idx(o);
                if (idx >= m_cache.size())
                    m_cache.resize(idx+1, aig_lit::null);
                m_cache[idx] = n;
                m_saved.push_back(o);
                m_saved.push_back(n.ptr());
                m.inc_ref(o);
                m.inc_ref(n);
            }
            if (o != n.ptr()) {
                push_result(n);
            }
            else {
                SASSERT(!n.is_inverted());
                push_result(aig_lit::null);
            }
        }

        void pop2_result() {
            aig_lit r1 = m_result_stack.back();
            m_result_stack.pop_back();
            aig_lit r2 = m_result_stack.back();
            m_result_stack.pop_back();
            if (!r1.is_null()) m.dec_ref(r1);
            if (!r2.is_null()) m.dec_ref(r2);
        }

        bool improve_sharing_left(aig * o, aig_lit n) {
            SASSERT(!left(n).is_inverted());
            SASSERT(!is_var(left(n)));
            aig_lit a = left(left(n));
            aig_lit b = right(left(n));
            aig_lit c = right(n);
            TRACE("max_sharing", 
                  tout << "trying (and "; m.display_ref(tout, a); 
                  tout << " (and ";       m.display_ref(tout, b); 
                  tout << " ";            m.display_ref(tout, c);
                  tout << "))\n";);
            aig_lit bc = m.mk_and(b, c);
            m.inc_ref(bc);
            if (ref_count(bc) > 1) {
                aig_lit r = m.mk_and(a, bc);
                if (n.is_inverted())
                    r.invert();
                save_result(o, r);
                m.dec_ref(bc);
                TRACE("max_sharing", tout << "improved:\n"; m.display(tout, o); tout << "---->\n"; m.display(tout, r););
                return true;
            }
            m.dec_ref(bc);
            
            TRACE("max_sharing", 
                  tout << "trying (and "; m.display_ref(tout, a); 
                  tout << " (and ";       m.display_ref(tout, c); 
                  tout << " ";            m.display_ref(tout, b);
                  tout << "))\n";);
            aig_lit ac = m.mk_and(a, c);
            m.inc_ref(ac);
            if (ref_count(ac) > 1) {
                aig_lit r = m.mk_and(b, ac);
                if (n.is_inverted())
                    r.invert();
                save_result(o, r);
                m.dec_ref(ac);
                TRACE("max_sharing", tout << "improved:\n"; m.display(tout, o); tout << "---->\n"; m.display(tout, r););
                return true;
            }
            m.dec_ref(ac);

            return false;
        }

        bool improve_sharing_right(aig * o, aig_lit n) {
            SASSERT(!right(n).is_inverted());
            SASSERT(!is_var(right(n)));
            aig_lit a = left(n);
            aig_lit b = left(right(n));
            aig_lit c = right(right(n));
            TRACE("max_sharing", 
                  tout << "trying (and (and "; m.display_ref(tout, a); 
                  tout << " ";                 m.display_ref(tout, b); 
                  tout << ") ";                m.display_ref(tout, c);
                  tout << ")\n";);
            aig_lit ab = m.mk_and(a, b);
            m.inc_ref(ab);
            if (ref_count(ab) > 1) {
                aig_lit r = m.mk_and(ab, c);
                if (n.is_inverted())
                    r.invert();
                save_result(o, r);
                m.dec_ref(ab);
                TRACE("max_sharing", tout << "improved:\n"; m.display(tout, o); tout << "---->\n"; m.display(tout, r););
                return true;
            }
            m.dec_ref(ab);
            
            aig_lit ac = m.mk_and(a, c);
            TRACE("max_sharing", 
                  tout << "trying (and (and "; m.display_ref(tout, a); 
                  tout << " ";                 m.display_ref(tout, c); 
                  tout << ") ";                m.display_ref(tout, b);
                  tout << ")\n";);
            m.inc_ref(ac);
            if (ref_count(ac) > 1) {
                aig_lit r = m.mk_and(ac, b);
                if (n.is_inverted())
                    r.invert();
                save_result(o, r);
                m.dec_ref(ac);
                TRACE("max_sharing", tout << "improved:\n"; m.display(tout, o); tout << "---->\n"; m.display(tout, r););
                return true;
            }
            m.dec_ref(ac);
            return false;
        }

        void improve_sharing_core(aig * o, aig_lit n) {
            if (!is_var(n)) {
                aig_lit l = left(n);
                if (!l.is_inverted() && ref_count(l) == 1 && !is_var(l) && improve_sharing_left(o, n))
                    return;
                aig_lit r = right(n);
                if (!r.is_inverted() && ref_count(r) == 1 && !is_var(r) && improve_sharing_right(o, n))
                    return;
            }
            save_result(o, n);
        }

        void improve_sharing(aig * p) {
            unsigned sz   = m_result_stack.size();
            aig_lit new_l = m_result_stack[sz-2];
            aig_lit new_r = m_result_stack[sz-1];
            if (new_l.is_null() && new_r.is_null()) {
                pop2_result();
                improve_sharing_core(p, aig_lit(p));
                return;
            }
            aig_lit l = left(p);
            aig_lit r = right(p);
            if (!new_l.is_null()) {
                if (l.is_inverted())
                    new_l.invert();
                l = new_l;
            }
            if (!new_r.is_null()) {
                if (r.is_inverted())
                    new_r.invert();
                r = new_r;
            }
            aig_lit n = m.mk_and(l, r);
            m.inc_ref(n);
            pop2_result();
            improve_sharing_core(p, n);
            m.dec_ref(n);
        }

        void process(aig * p) {
            if (visit(p))
                return;
            while (!m_frame_stack.empty()) {
            start:
                frame & fr = m_frame_stack.back();
                aig * n    = fr.m_node;
                TRACE("max_sharing", tout << "processing "; m.display_ref(tout, n); tout << " idx: " << fr.m_idx << "\n";);
                switch (fr.m_idx) {
                case 0: 
                    fr.m_idx++;
                    if (!visit(left(n)))
                        goto start;
                case 1:
                    fr.m_idx++;
                    if (!visit(right(n)))
                        goto start;
                default:
                    if (!is_cached(n))
                        improve_sharing(n);
                    m_frame_stack.pop_back();
                    break;
                }
            }
        }

        aig_lit operator()(aig_lit p) {
            process(p.ptr());
            SASSERT(m_result_stack.size() == 1);
            aig_lit r = m_result_stack.back();
            TRACE("max_sharing", tout << "r.is_null(): " << r.is_null() << "\n";);
            SASSERT(r.is_null() || ref_count(r) >= 1);
            reset_cache();
            if (r.is_null()) {
                r = p;
                m.inc_ref(r);
            }
            else if (p.is_inverted()) {
                r.invert();
            }
            m_result_stack.pop_back();
            TRACE("max_sharing", tout << "result:\n"; m.display(tout, r););
            m.dec_ref_result(r);
            return r;
        }
    };

public:
    imp(ast_manager & m, unsigned long long max_memory, bool default_gate_encoding):
        m_var_id_gen(0),
        m_node_id_gen(FIRST_NODE_ID),
        m_num_aigs(0),
        m_var2exprs(m),
        m_allocator("aig"),
        m_true(mk_var(m.mk_true())) {
        SASSERT(is_true(m_true));
        m_false = m_true;
        m_false.invert();
        inc_ref(m_true);
        inc_ref(m_false);
        m_max_memory = max_memory;
        m_default_gate_encoding = default_gate_encoding;
    }
    
    ~imp() {
        dec_ref(m_true);
        dec_ref(m_false);
        SASSERT(m_num_aigs == 0);
    }

    ast_manager & m() const { return m_var2exprs.get_manager(); }


    void inc_ref(aig * n) { n->m_ref_count++; }
    void inc_ref(aig_lit const & r) { inc_ref(r.ptr()); }
    void dec_ref(aig * n) { 
        dec_ref_core(n);
        process_to_delete();
    }
    void dec_ref(aig_lit const & r) { dec_ref(r.ptr()); }

    void dec_array_ref(unsigned sz, aig * const * ns) {
        for (unsigned i = 0; i < sz; i++)
            if (ns[i]) 
                dec_ref(ns[i]);
    }

    aig_lit mk_and(aig_lit r1, aig_lit r2) {
        aig_lit r = mk_node(r1, r2);
        TRACE("mk_and_bug", 
              display(tout, r1);
              tout << "AND\n";
              display(tout, r2);
              tout << "-->\n"; 
              display(tout, r);
              tout << "\n";);
        return r;
    }

    aig_lit mk_and(unsigned num, aig_lit * args) {
        switch (num) {
        case 0:
            return m_true;
        case 1:
            return args[0];
        case 2:
            return mk_and(args[0], args[1]);
        default:
            // No need to use stable_sort, aig_lit_lt is a total order on AIG nodes
            std::sort(args, args+num, aig_lit_lt());
            aig_lit r = mk_and(args[0], args[1]);
            inc_ref(r);
            for (unsigned i = 2; i < num; i++) {
                aig_lit new_r = mk_and(r, args[i]);
                inc_ref(new_r);
                dec_ref(r);
                r = new_r;
            }
            dec_ref_result(r);
            return r;
        }
    }

    aig_lit mk_or(aig_lit r1, aig_lit r2) {
        r1.invert();
        r2.invert();
        aig_lit r = mk_and(r1, r2);
        r.invert();
        return r;
    }

    aig_lit mk_or(unsigned num, aig_lit * args) {
        switch (num) {
        case 0:
            return m_false;
        case 1:
            return args[0];
        case 2:
            return mk_or(args[0], args[1]);
        default:
            std::sort(args, args+num, aig_lit_lt());
            aig_lit r = mk_or(args[0], args[1]);
            inc_ref(r);
            for (unsigned i = 2; i < num; i++) {
                aig_lit new_r = mk_or(r, args[i]);
                inc_ref(new_r);
                dec_ref(r);
                r = new_r;
            }
            dec_ref_result(r);
            return r;
        }
    }

    aig_lit mk_ite(aig_lit c, aig_lit t, aig_lit e) {
        if (m_default_gate_encoding) {
            t.invert();
            aig_lit n1 = mk_and(c, t); // c and (not t)
            c.invert();
            e.invert();
            aig_lit n2 = mk_and(c, e); // (not c) and (not e)
            inc_ref(n1);
            inc_ref(n2);
            n1.invert();
            n2.invert();
            aig_lit r  = mk_and(n1, n2);
            inc_ref(r);
            dec_ref(n1);
            dec_ref(n2);
            dec_ref_result(r);
            return r;
        }
        else {
            aig_lit n1 = mk_and(c, t);
            inc_ref(n1);
            c.invert();
            aig_lit n2 = mk_and(c, e);
            inc_ref(n2);
            n1.invert();
            n2.invert();
            aig_lit r = mk_and(n1, n2);
            r.invert();
            inc_ref(r);
            dec_ref(n1);
            dec_ref(n2);
            dec_ref_result(r);
            return r;
        }
    }

    aig_lit mk_iff(aig_lit lhs, aig_lit rhs) {
        if (m_default_gate_encoding) {
            rhs.invert();
            aig_lit n1 = mk_and(lhs, rhs); // lhs and (not rhs)
            lhs.invert();
            rhs.invert();
            aig_lit n2 = mk_and(lhs, rhs); // (not lhs) and rhs
            inc_ref(n1);
            inc_ref(n2);
            n1.invert();
            n2.invert();
            aig_lit r  = mk_and(n1, n2);
            inc_ref(r);
            dec_ref(n1);
            dec_ref(n2);
            dec_ref_result(r);
            return r;
        }
        else {
            aig_lit n1 = mk_and(lhs, rhs); // lhs and rhs
            inc_ref(n1);
            lhs.invert();
            rhs.invert();
            aig_lit n2 = mk_and(lhs, rhs); // not lhs and not rhs
            inc_ref(n2);
            n1.invert();
            n2.invert();
            aig_lit r = mk_and(n1, n2);
            r.invert();
            inc_ref(r);
            dec_ref(n1);
            dec_ref(n2);
            dec_ref_result(r);
            return r;
        }
    }

    aig_lit mk_xor(aig_lit lhs, aig_lit rhs) {
        lhs.invert();
        return mk_iff(lhs, rhs);
    }

    aig_lit mk_implies(aig_lit lhs, aig_lit rhs) {
        lhs.invert();
        return mk_or(lhs, rhs);
    }

    aig_lit mk_aig(expr * t) {
        aig_lit r;
        { 
            expr2aig proc(*this);
            r = proc(t);
            inc_ref(r);
        }
        dec_ref_result(r);
        return r;
    }

    template<typename S>
    aig_lit mk_aig(S const & s) { 
        aig_lit r;
        r   = m_true;
        inc_ref(r);
        try {
        expr2aig proc(*this);
            unsigned sz = s.size();
            for (unsigned i = 0; i < sz; i++) {
                SASSERT(ref_count(r) >= 1);
                expr * t = s.form(i);
                aig_lit n = proc(t);
                inc_ref(n);
                aig_lit new_r = mk_and(r, n);
                SASSERT(proc.check_cache());
                inc_ref(new_r);
                dec_ref(r);
                dec_ref(n);
                SASSERT(proc.check_cache());
                r = new_r;
            }
            SASSERT(ref_count(r) >= 1);
        }
    catch (const aig_exception & ex) {
        dec_ref(r);
        throw ex;
    }
        dec_ref_result(r);
        return r;
    }

    void to_formula(aig_lit const & r, goal & g) {
        aig2expr proc(*this);
        proc(r, g);
    }
    
    void to_formula(aig_lit const & r, expr_ref & result) {
        aig2expr proc(*this);
        proc(r, result);
    }

    aig_lit max_sharing(aig_lit l) {
        max_sharing_proc p(*this);
        return p(l);
    }

    void display_ref(std::ostream & out, aig * r) const {
        if (is_var(r)) 
            out << "#" << r->m_id;
        else
            out << "@" << (r->m_id - FIRST_NODE_ID);
    }

    void display_ref(std::ostream & out, aig_lit const & r) const {
        if (r.is_inverted())
            out << "-";
        display_ref(out, r.ptr());
    }

    void display(std::ostream & out, aig_lit const & r) const {
        display_ref(out, r); 
        out << "\n";
        ptr_vector<aig> queue;
        unsigned        qhead = 0;
        queue.push_back(r.ptr());
        while (qhead < queue.size()) {
            aig * n = queue[qhead];
            qhead++;
            display_ref(out, n); out << ": ";
            if (is_var(n)) {
                out << mk_ismt2_pp(m_var2exprs[n->m_id], m()) << "\n";
            }
            else {
                display_ref(out, n->m_children[0]);
                out << " ";
                display_ref(out, n->m_children[1]);
                out << "\n";
                aig * c1 = n->m_children[0].ptr();
                aig * c2 = n->m_children[1].ptr();
                if (!c1->m_mark) {
                    c1->m_mark = true;
                    queue.push_back(c1);
                }
                if (!c2->m_mark) {
                    c2->m_mark = true;
                    queue.push_back(c2);
                }
            }
        }
        unmark(queue.size(), queue.c_ptr());
    }

    void display_smt2_ref(std::ostream & out, aig_lit const & r) const {
        if (r.is_inverted())
            out << "(not ";
        if (is_var(r)) {
            out << mk_ismt2_pp(var2expr(r.ptr()), m());
        }
        else {
            out << "aig" << to_idx(r.ptr());
        }
        if (r.is_inverted())
            out << ")";
    }

    void display_smt2(std::ostream & out, aig_lit const & r) const {
        ptr_vector<aig> to_unmark;
        ptr_vector<aig> todo;
        todo.push_back(r.ptr());
        while (!todo.empty()) {
            aig * t = todo.back();
            if (t->m_mark) {
                todo.pop_back();
                continue;
            }
            if (is_var(t)) {
                to_unmark.push_back(t);
                t->m_mark = true;
                todo.pop_back();
                continue;
            }
            bool visited = true;
            for (unsigned i = 0; i < 2; i++) {
                aig_lit c = t->m_children[i];
                aig * c_ptr = c.ptr();
                if (!c_ptr->m_mark) {
                    todo.push_back(c_ptr);
                    visited = false;
                }
            }
            if (!visited)
                continue;
            to_unmark.push_back(t);
            t->m_mark = true;
            out << "(define-fun aig" << to_idx(t) << " () Bool (and";
            for (unsigned i = 0; i < 2; i++) {
                out << " ";
                display_smt2_ref(out, t->m_children[i]);
            }
            out << "))\n";
            todo.pop_back();
        }
        out << "(assert ";
        display_smt2_ref(out, r);
        out << ")\n";
        unmark(to_unmark.size(), to_unmark.c_ptr());
    }

    unsigned get_num_aigs() const {
        return m_num_aigs;
    }
};


aig_ref::aig_ref():
    m_manager(nullptr),
    m_ref(nullptr) {
}

aig_ref::aig_ref(aig_manager & m, aig_lit const & l):
    m_manager(&m),
    m_ref(l.m_ref) {
    m.m_imp->inc_ref(l);
}

aig_ref::~aig_ref() {
    if (m_ref != nullptr) {
        m_manager->m_imp->dec_ref(aig_lit(*this));
    }
}

aig_ref & aig_ref::operator=(aig_ref const & r) {
    if (r.m_ref != nullptr)
        r.m_manager->m_imp->inc_ref(aig_lit(r));
    if (m_ref != nullptr)
        m_manager->m_imp->dec_ref(aig_lit(*this));
    m_ref     = r.m_ref;
    m_manager = r.m_manager;
    return *this;
}

aig_manager::aig_manager(ast_manager & m, unsigned long long max, bool default_gate_encoding) {
    m_imp = alloc(imp, m, max, default_gate_encoding);
}

aig_manager::~aig_manager() {
    dealloc(m_imp);
}

void aig_manager::set_max_memory(unsigned long long max) {
    m_imp->m_max_memory = max;
}

aig_ref aig_manager::mk_aig(expr * n) {
    return aig_ref(*this, m_imp->mk_aig(n));
}

aig_ref aig_manager::mk_aig(goal const & s) {
    return aig_ref(*this, m_imp->mk_aig(s));
}

aig_ref aig_manager::mk_not(aig_ref const & r) {
    aig_lit l(r);
    l.invert();
    return aig_ref(*this, l);
}

aig_ref aig_manager::mk_and(aig_ref const & r1, aig_ref const & r2) {
    return aig_ref(*this, m_imp->mk_and(aig_lit(r1), aig_lit(r2)));
}

aig_ref aig_manager::mk_or(aig_ref const & r1, aig_ref const & r2) {
    return aig_ref(*this, m_imp->mk_or(aig_lit(r1), aig_lit(r2)));
}

aig_ref aig_manager::mk_iff(aig_ref const & r1, aig_ref const & r2) {
    return aig_ref(*this, m_imp->mk_iff(aig_lit(r1), aig_lit(r2)));
}

aig_ref aig_manager::mk_ite(aig_ref const & r1, aig_ref const & r2, aig_ref const & r3) {
    return aig_ref(*this, m_imp->mk_ite(aig_lit(r1), aig_lit(r2), aig_lit(r3)));
}

void aig_manager::max_sharing(aig_ref & r) {
    r = aig_ref(*this, m_imp->max_sharing(aig_lit(r)));
}

void aig_manager::to_formula(aig_ref const & r, goal & g) {
    SASSERT(!g.proofs_enabled());
    SASSERT(!g.unsat_core_enabled());
    return m_imp->to_formula(aig_lit(r), g);
}

void aig_manager::to_formula(aig_ref const & r, expr_ref & res) {
    return m_imp->to_formula(aig_lit(r), res);
}
 
void aig_manager::display(std::ostream & out, aig_ref const & r) const {
    m_imp->display(out, aig_lit(r));
}

void aig_manager::display_smt2(std::ostream & out, aig_ref const & r) const {
    m_imp->display_smt2(out, aig_lit(r));
}

unsigned aig_manager::get_num_aigs() const {
    return m_imp->get_num_aigs();
}



