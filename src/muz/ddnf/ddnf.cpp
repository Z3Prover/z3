/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    ddnf.cpp

Abstract:

    DDNF based engine.

Author:

    Nikolaj Bjorner (nbjorner) 2014-08-21

Revision History:

   - inherits from Nuno Lopes Hassel utilities 
     and Garvit Juniwal's DDNF engine.

--*/

#include "ddnf.h"
#include "dl_rule_set.h"
#include "dl_context.h"
#include "scoped_proof.h"


namespace datalog {

#define BIT_0 ((0<<1)|1)
#define BIT_1 ((1<<1)|0)
#define BIT_x ((1<<1)|1)
#define BIT_z 0

    class tbv : private bit_vector {
    public:
        tbv(): bit_vector() {}
        tbv(unsigned n): bit_vector(2*n) {}
        tbv(tbv const& other): bit_vector(other) {}
        tbv(unsigned n, unsigned val): bit_vector() {
            SASSERT(val <= 3);
            resize(n, val);
        }
        tbv(uint64 val, unsigned n) : bit_vector(2*n) {
            for (unsigned bit = n; bit > 0;) {
                --bit;
                if (val & (1ULL << bit)) {                        
                    set(bit, BIT_1);
                } else {
                    set(bit, BIT_0);
                }
            }
        }

        tbv(rational const& v, unsigned n) : bit_vector(2*n) {
            if (v.is_uint64() && n <= 64) {
                tbv tmp(v.get_uint64(), n);
                *this = tmp;
                return;
            }

            for (unsigned bit = n; bit > 0; ) {
                --bit;
                if (bitwise_and(v, rational::power_of_two(bit)).is_zero()) {
                    set(bit, BIT_0);
                } else {
                    set(bit, BIT_1);
                }
            }            
        }

        tbv& operator=(tbv const& other) { 
            bit_vector::operator=(other);
            return *this;
        }

        bool operator!=(tbv const& other) const { 
            return bit_vector::operator!=(other);
        }

        bool operator==(tbv const& other) const { 
            return bit_vector::operator==(other);
        }

        unsigned get_hash() const {
            return bit_vector::get_hash();
        }

        void resize(unsigned n, unsigned val) {
            while (size() < n) {
                bit_vector::push_back((val & 2) != 0);
                bit_vector::push_back((val & 1) != 0);
            }
        }

        bool is_subset(tbv const& other) const {
            SASSERT(size() == other.size());
            return other.contains(*this);
        }

        bool is_superset(tbv const& other) const {
            SASSERT(size() == other.size());
            return contains(other);
        }

        unsigned size() const { return bit_vector::size()/2; }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < size(); ++i) {
                switch (get(i)) {
                case BIT_0:
                    out << '0';
                    break;
                case BIT_1:
                    out << '1';
                    break;
                case BIT_x:
                    out << 'x';
                    break;
                case BIT_z:
                    out << 'z';
                    break;
                default:
                    UNREACHABLE();
                }
            }
        }
        
        friend bool intersect(tbv const& a, tbv const& b, tbv& result);

    private:
        void set(unsigned index, unsigned value) {
            SASSERT(value <= 3);
            bit_vector::set(2*index,   (value & 2) != 0);
            bit_vector::set(2*index+1, (value & 1) != 0);
        }

        unsigned get(unsigned index) const {
            index *= 2;
            return (bit_vector::get(index) << 1) | (unsigned)bit_vector::get(index+1);
        }
    };

    bool intersect(tbv const& a, tbv const& b, tbv& result) {
        result = a;
        result &= b;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (result.get(i) == BIT_z) return false;
        }
        return true;
    }

    class dot {
        tbv         m_pos;
        vector<tbv> m_negs;
    public:
        dot() {}
        dot(tbv const& pos, vector<tbv> const& negs):
            m_pos(pos), m_negs(negs) {
            DEBUG_CODE(
                for (unsigned i = 0; i < negs.size(); ++i) {
                    SASSERT(pos.size() == negs[i].size());
                }
                );
        }

        tbv const& pos() const { return m_pos; }
        tbv neg(unsigned i) const { return m_negs[i]; }
        unsigned size() const { return m_negs.size(); }
        unsigned num_bits() const { return m_pos.size(); }

        bool operator==(dot const& other) const {
            if (m_pos != other.m_pos) return false;
            if (m_negs.size() != other.m_negs.size()) return false;
            for (unsigned i = 0; i < m_negs.size(); ++i) {
                if (m_negs[i] != other.m_negs[i]) return false;
            }
            return true;
        }

        void display(std::ostream& out) {
            out << "<";
            m_pos.display(out);
            out << "\\";
            for (unsigned i = 0; i < m_negs.size(); ++i) {
                m_negs[i].display(out);
                if (i + 1 < m_negs.size()) out << " u ";
            }
            out << ">";
        }

        struct eq {
            bool operator()(dot const& d1, dot const& d2) const {
                return d1 == d2;
            }
        };

        struct hash {
            unsigned operator()(dot const& d) const {
                unsigned h = d.pos().get_hash();
                for (unsigned i = 0; i < d.size(); ++i) {
                    h ^= d.neg(i).get_hash();
                }
                return h;
            }
        };

    };

    class ddnf_mgr;
    class ddnf_node;
    typedef ref_vector<ddnf_node, ddnf_mgr> ddnf_node_vector;

    class ddnf_node {
        tbv                   m_tbv;
        ddnf_node_vector      m_children;
        vector<dot>           m_pos;
        vector<dot>           m_neg;
        unsigned              m_refs;
        unsigned              m_id;
        
        friend class ddnf_mgr;

    public:
        ddnf_node(ddnf_mgr& m, tbv const& tbv, unsigned id):
            m_tbv(tbv),
            m_children(m),
            m_refs(0),
            m_id(id) {                        
        }

        ~ddnf_node() {}

        unsigned inc_ref() {
            return ++m_refs;
        }

        void dec_ref() {
            SASSERT(m_refs > 0);
            --m_refs;
            if (m_refs == 0) {
                dealloc(this);
            }
        }

        struct eq {
            bool operator()(ddnf_node* n1, ddnf_node* n2) const {
                return n1->get_tbv() == n2->get_tbv();
            }
        };

        struct hash {
            unsigned operator()(ddnf_node* n) const {
                return n->get_tbv().get_hash();
            }
        };

        unsigned get_id() const { return m_id; }
        
        unsigned num_children() const { return m_children.size(); }

        ddnf_node* operator[](unsigned index) { return m_children[index].get(); }

        tbv const& get_tbv() const { return m_tbv; }
        vector<dot> const& pos() const { return m_pos; }
        vector<dot> const& neg() const { return m_neg; }

        void add_child(ddnf_node* n);
        
        void remove_child(ddnf_node* n);
        
        bool contains_child(ddnf_node* n) const;

        ddnf_node* add_pos(dot const& d) { m_pos.push_back(d); return this; }

        ddnf_node* add_neg(dot const& d) { m_neg.push_back(d); return this; }

        void display(std::ostream& out) const {
            out << "node[";
            m_tbv.display(out);
            for (unsigned i = 0; i < m_children.size(); ++i) {
                out << " " << m_children[i]->get_id();
            }
            out << "]";
        }
    };

    typedef ptr_hashtable<ddnf_node, ddnf_node::hash, ddnf_node::eq> ddnf_nodes;
    typedef map<dot, ddnf_nodes*, dot::hash, dot::eq> dot2nodes;

    class ddnf_mgr {        
        unsigned               m_num_bits;
        ddnf_node*             m_root;
        ddnf_node_vector       m_noderefs;
        ddnf_nodes             m_nodes;
        ptr_vector<ddnf_nodes> m_tables;
        dot2nodes              m_dots;
        bool                   m_internalized;
    public:
        ddnf_mgr(unsigned n): m_num_bits(n), m_noderefs(*this), m_internalized(false) {
            m_root = alloc(ddnf_node, *this, tbv(n, BIT_x), m_nodes.size());
            m_noderefs.push_back(m_root);
            m_nodes.insert(m_root);
        }

        ~ddnf_mgr() {
            m_noderefs.reset();
            std::for_each(m_tables.begin(), m_tables.end(), delete_proc<ddnf_nodes>());
        }

        void inc_ref(ddnf_node* n) {
            n->inc_ref();
        }

        void dec_ref(ddnf_node* n) {
            n->dec_ref();
        }

        void insert(dot const& d) {
            SASSERT(d.size() == m_num_bits);
            SASSERT(!m_internalized);
            if (m_dots.contains(d)) return;
            ddnf_nodes* ns = alloc(ddnf_nodes);
            m_tables.push_back(ns);
            m_dots.insert(d, ns);
            insert(d.pos())->add_pos(d);
            for (unsigned i = 0; i < d.size(); ++i) {
                insert(d.neg(i))->add_neg(d);
            }
        }

        ddnf_nodes const& lookup(dot const& d)  {
            internalize();
            return *m_dots.find(d);
        }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_noderefs.size(); ++i) {
                m_noderefs[i]->display(out);
                out << "\n";
            }
        }

    private:

        ddnf_node* insert(tbv const& t) {
            vector<tbv> new_tbvs;
            new_tbvs.push_back(t);
            for (unsigned i = 0; i < new_tbvs.size(); ++i) {
                tbv const& nt = new_tbvs[i];
                if (contains(nt))  continue;
                ddnf_node* n = alloc(ddnf_node, *this, nt, m_noderefs.size());
                m_noderefs.push_back(n);
                m_nodes.insert(n);
                insert(*m_root, n, new_tbvs);
            }
            return find(t);
        }

        ddnf_node* find(tbv const& t) {
            ddnf_node dummy(*this, t, 0);
            return *(m_nodes.find(&dummy));
        }
    
        bool contains(tbv const& t) {
            ddnf_node dummy(*this, t, 0);
            return m_nodes.contains(&dummy);
        }    

        void insert(ddnf_node& root, ddnf_node* new_n, vector<tbv>& new_intersections) {
            tbv const& new_tbv = new_n->get_tbv();
            
            SASSERT(new_tbv.is_subset(root.get_tbv()));
            if (&root == new_n) return;
            bool inserted = false;
            for (unsigned i = 0; i < root.num_children(); ++i) {
                ddnf_node& child = *(root[i]);
                if (child.get_tbv().is_superset(new_tbv)) {
                    inserted = true;
                    insert(child, new_n, new_intersections);
                }
            }
            if (inserted) {
                return;
            }
            ddnf_node_vector subset_children(*this);
            tbv intr;
            for (unsigned i = 0; i < root.num_children(); ++i) {
                ddnf_node& child = *(root[i]);
                // cannot be superset
                SASSERT(!child.get_tbv().is_superset(new_tbv));
                // checking for subset
                if (child.get_tbv().is_subset(new_tbv)) {
                    subset_children.push_back(&child);
                }
                // this means there is a non-full intersection
                else {
                    if (intersect(child.get_tbv(), new_tbv, intr)) {
                        new_intersections.push_back(intr);
                    }
                }
            }
            for (unsigned i = 0; i < subset_children.size(); ++i) {
                root.remove_child(subset_children[i].get());
                new_n->add_child(subset_children[i].get());
            }
            root.add_child(new_n);           
        }


        void internalize() {
            // create map: dot |-> ddnf_node set
            if (!m_internalized) {                
                vector<dot> dots1, dots2;
                add_pos(*m_root, dots1);
                del_neg(*m_root, dots2);    
                m_internalized = true;
            }
        }
        
        void add_pos(ddnf_node& n, vector<dot>& active) {
            for (unsigned i = 0; i < n.pos().size(); ++i) {                
                active.push_back(n.pos()[i]);
                // TBD: Garvit; prove (or disprove): there are no repetitions.
                // the argument may be that the sub-expressions are
                // traversed in DFS order, and that repeated dots
                // cannot occur below each-other.
            }
            for (unsigned i = 0; i < active.size(); ++i) {
                m_dots.find(active[i])->insert(&n);
            }
            for (unsigned i = 0; i < n.num_children(); ++i) {
                vector<dot> active1(active);
                add_pos(*n[i], active1);
            }            
        }

        void del_neg(ddnf_node& n, vector<dot>& active) {
            for (unsigned i = 0; i < n.neg().size(); ++i) {                
                active.push_back(n.neg()[i]);
            }
            for (unsigned i = 0; i < active.size(); ++i) {
                m_dots.find(active[i])->remove(&n);
            }
            for (unsigned i = 0; i < n.num_children(); ++i) {
                vector<dot> active1(active);
                del_neg(*n[i], active1);
            }          
        } 
        
    };

    void ddnf_node::add_child(ddnf_node* n) {
        SASSERT(!m_tbv.is_subset(n->m_tbv));
        m_children.push_back(n);
    }
    
    void ddnf_node::remove_child(ddnf_node* n) {
        m_children.erase(n);
    }
    
    bool ddnf_node::contains_child(ddnf_node* n) const {
        return m_children.contains(n);
    }        


    class ddnfs {
        u_map<ddnf_mgr*> m_mgrs;
    public:
        ddnfs() {}

        ~ddnfs() {
            u_map<ddnf_mgr*>::iterator it = m_mgrs.begin(), end = m_mgrs.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
        }
        
        void insert(dot const& d) {
            unsigned n = d.num_bits();
            ddnf_mgr* m = 0;
            if (!m_mgrs.find(n, m)) {
                m = alloc(ddnf_mgr, n);
                m_mgrs.insert(n, m);
            }
            m->insert(d);
        }
        
        ddnf_nodes const& lookup(dot const& d) const {
            return m_mgrs.find(d.num_bits())->lookup(d);
        }

        void display(std::ostream& out) const {
            u_map<ddnf_mgr*>::iterator it = m_mgrs.begin(), end = m_mgrs.end();
            for (; it != end; ++it) {
                it->m_value->display(out);
            }
        }

    };


    class ddnf::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        context&               m_ctx;
        ast_manager&           m;
        rule_manager&          rm;
        volatile bool          m_cancel;
        ptr_vector<expr>       m_todo;
        ast_mark               m_visited1, m_visited2;
        ddnfs                  m_ddnfs;
        stats                  m_stats;

    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_cancel(false)
        {
        }

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            if (!can_handle_rules()) {
                return l_undef;
            }
            IF_VERBOSE(0, verbose_stream() << "rules are OK\n";);
            return run();
        }
    
        void cancel() {
            m_cancel = true;
        }
        
        void cleanup() {
            m_cancel = false;
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
        }

        void display_certificate(std::ostream& out) const {
            expr_ref ans = get_answer();
            out << mk_pp(ans, m) << "\n";
        }

        expr_ref get_answer() const {
            UNREACHABLE();
            return expr_ref(m.mk_true(), m);
        }

    private:
    
        proof_ref get_proof() const {
            scoped_proof sp(m);
            proof_ref pr(m);
            return pr;
        }
   
        lbool run() {
            return l_undef;
        }

        bool can_handle_rules()  {
            m_visited1.reset();
            m_todo.reset();
            rule_set const& rules = m_ctx.get_rules();
            datalog::rule_set::iterator it  = rules.begin();
            datalog::rule_set::iterator end = rules.end();
            for (; it != end; ++it) {
                if (!can_handle_rule(**it)) {
                    return false;
                }
            }
            return true;
        }

        bool can_handle_rule(rule const& r) {
            // all predicates are monadic.
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned sz = r.get_tail_size();
            for (unsigned i = utsz; i < sz; ++i) {
                m_todo.push_back(r.get_tail(i));
            }
            if (check_monadic()) {
                return true;
            }
            else {
                r.display(m_ctx, std::cout);
                return false;
            }
        }

        bool check_monadic() {
            expr* e1, *e2;
            while (!m_todo.empty()) {
                expr* e = m_todo.back();
                m_todo.pop_back();
                if (m_visited1.is_marked(e)) {
                    continue;
                }
                m_visited1.mark(e, true);
                if (is_var(e)) {
                    continue;
                }
                if (is_quantifier(e)) {
                    return false;
                }
                if (m.is_and(e) ||
                    m.is_or(e) ||
                    m.is_iff(e) ||
                    m.is_not(e) ||
                    m.is_implies(e)) {
                    m_todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
                    continue;
                }
                if (m.is_eq(e, e1, e2)) {
                    if (is_var(e1) && is_ground(e2)) {
                        continue;
                    }
                    if (is_var(e2) && is_ground(e1)) {
                        continue;
                    }
                    if (is_var(e1) && is_var(e2)) {
                        continue;
                    }
                }
                if (is_ground(e)) {
                    continue;
                }
                if (is_unary(e)) {
                    continue;
                }
                IF_VERBOSE(0, verbose_stream() << "Could not handle: " << mk_pp(e, m) << "\n";);
                return false;
            }
            return true;
        }

        bool is_unary(expr* e) {
            var* v = 0;
            m_visited2.reset();
            unsigned sz = m_todo.size();
            m_todo.push_back(e);
            while (m_todo.size() > sz) {
                expr* e = m_todo.back();
                m_todo.pop_back();
                if (m_visited2.is_marked(e)) {
                    continue;
                }
                m_visited2.mark(e, true);
                if (is_var(e)) {
                    if (v && v != e) {
                        return false;
                    }
                    v = to_var(e);                    
                }
                else if (is_app(e)) {
                    m_todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
                }
                else {
                    return false;
                }
            }
            return true;
        }

        void compile(expr* e) {
            // TBD: 
            // compiles monadic predicates into dots.
            // saves the mapping from expr |-> dot
            // such that atomic sub-formula can be expressed 
            // as a set of ddnf_nodes
        }

    };

    ddnf::ddnf(context& ctx):
        datalog::engine_base(ctx.get_manager(),"tabulation"),
        m_imp(alloc(imp, ctx)) {        
    }
    ddnf::~ddnf() {
        dealloc(m_imp);
    }    
    lbool ddnf::query(expr* query) {
        return m_imp->query(query);
    }
    void ddnf::cancel() {
        m_imp->cancel();
    }
    void ddnf::cleanup() {
        m_imp->cleanup();
    }
    void ddnf::reset_statistics() {
        m_imp->reset_statistics();
    }
    void ddnf::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void ddnf::display_certificate(std::ostream& out) const {
        m_imp->display_certificate(out);
    }
    expr_ref ddnf::get_answer() {
        return m_imp->get_answer();
    }

};
