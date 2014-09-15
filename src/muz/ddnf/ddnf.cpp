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
#include "bv_decl_plugin.h"

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
            resize(n, BIT_x);
            for (unsigned bit = n; bit > 0;) {
                --bit;
                if (val & (1ULL << bit)) {                        
                    set(bit, BIT_1);
                } else {
                    set(bit, BIT_0);
                }
            }
        }

        tbv(uint64 v, unsigned sz, unsigned hi, unsigned lo) : bit_vector(2*sz) {
            resize(sz, BIT_x);
            SASSERT(64 >= sz && sz > hi && hi >= lo);
            for (unsigned i = 0; i < hi - lo + 1; ++i) {
                set(lo + i, (v & (1ULL << i))?BIT_1:BIT_0);
            }
        }

        tbv(rational const& v, unsigned n) : bit_vector(2*n) {
            if (v.is_uint64() && n <= 64) {
                tbv tmp(v.get_uint64(), n);
                *this = tmp;
                return;
            }

            resize(n, BIT_x);
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

        struct eq {
            bool operator()(tbv const& d1, tbv const& d2) const {
                return d1 == d2;
            }
        };

        struct hash {
            unsigned operator()(tbv const& d) const {
                return d.get_hash();
            }
        };

        
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

    std::ostream& operator<<(std::ostream& out, tbv const& t) {
        t.display(out);
        return out;
    }

    bool intersect(tbv const& a, tbv const& b, tbv& result) {
        result = a;
        result &= b;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (result.get(i) == BIT_z) return false;
        }
        return true;
    }

    class ddnf_mgr;
    class ddnf_node;
    typedef ref_vector<ddnf_node, ddnf_mgr> ddnf_node_vector;

    class ddnf_node {
    public:

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

        typedef ptr_hashtable<ddnf_node, ddnf_node::hash, ddnf_node::eq> ddnf_nodes;
    private:
        tbv                   m_tbv;
        ddnf_node_vector      m_children;
        unsigned              m_refs;
        unsigned              m_id;
        ddnf_nodes            m_descendants;

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

        ddnf_nodes& descendants() { return m_descendants; }

        unsigned get_id() const { return m_id; }
        
        unsigned num_children() const { return m_children.size(); }

        ddnf_node* operator[](unsigned index) { return m_children[index].get(); }

        tbv const& get_tbv() const { return m_tbv; }

        void add_child(ddnf_node* n);
        
        void remove_child(ddnf_node* n);
        
        bool contains_child(ddnf_node* n) const;

        void display(std::ostream& out) const {
            out << "node[" << get_id() << ": ";
            m_tbv.display(out);
            for (unsigned i = 0; i < m_children.size(); ++i) {
                out << " " << m_children[i]->get_id();
            }
            out << "]";
        }
    };

    typedef ddnf_node::ddnf_nodes ddnf_nodes;


    class ddnf_mgr {        
        unsigned               m_num_bits;
        ddnf_node*             m_root;
        ddnf_node_vector       m_noderefs;
        ddnf_nodes             m_nodes;
        bool                   m_internalized;
    public:
        ddnf_mgr(unsigned n): m_num_bits(n), m_noderefs(*this), m_internalized(false) {
            m_root = alloc(ddnf_node, *this, tbv(n, BIT_x), m_nodes.size());
            m_noderefs.push_back(m_root);
            m_nodes.insert(m_root);
        }

        ~ddnf_mgr() {
            m_noderefs.reset();
        }

        void inc_ref(ddnf_node* n) {
            n->inc_ref();
        }

        void dec_ref(ddnf_node* n) {
            n->dec_ref();
        }

        ddnf_node* insert(tbv const& t) {
            SASSERT(t.size() == m_num_bits);
            SASSERT(!m_internalized);
            vector<tbv> new_tbvs;
            new_tbvs.push_back(t);
            for (unsigned i = 0; i < new_tbvs.size(); ++i) {
                tbv const& nt = new_tbvs[i];
                if (contains(nt)) continue;
                ddnf_node* n = alloc(ddnf_node, *this, nt, m_noderefs.size());
                m_noderefs.push_back(n);
                m_nodes.insert(n);
                insert(*m_root, n, new_tbvs);
            }
            return find(t);
        }

        unsigned size() const { 
            return m_noderefs.size(); 
        }

        ddnf_nodes const& lookup(tbv const& t)  {
            internalize();
            return find(t)->descendants();
        }

        void display(std::ostream& out) const {
            for (unsigned i = 0; i < m_noderefs.size(); ++i) {
                m_noderefs[i]->display(out);
                out << "\n";
            }
        }

    private:

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
                else if (intersect(child.get_tbv(), new_tbv, intr)) {
                    // this means there is a non-full intersection
                    new_intersections.push_back(intr);
                }
            }
            for (unsigned i = 0; i < subset_children.size(); ++i) {
                root.remove_child(subset_children[i].get());
                new_n->add_child(subset_children[i].get());
            }
            root.add_child(new_n);           
        }


        void internalize() {
            // populate maps (should be bit-sets) of decendants.
            if (m_internalized) {                
                return;
            }
            ptr_vector<ddnf_node> todo;
            todo.push_back(m_root);
            svector<bool> done(m_noderefs.size(), false);
            while (!todo.empty()) {
                ddnf_node& n = *todo.back();
                if (done[n.get_id()]) {
                    todo.pop_back();
                    continue;
                }
                unsigned sz = n.num_children();
                bool all_done = true;
                for (unsigned i = 0; i < sz; ++i) {
                    ddnf_node* child = n[i];
                    if (!done[child->get_id()]) {
                        all_done = false;
                        todo.push_back(child);
                    }
                }
                if (all_done) {
                    n.descendants().insert(&n);
                    for (unsigned i = 0; i < sz; ++i) {
                        ddnf_node* child = n[i];
                        add_table(n.descendants(), child->descendants());
                    }
                    done[n.get_id()] = true;
                    todo.pop_back();
                }                
            }
            m_internalized = true;            
        }

        void add_table(ddnf_nodes& dst, ddnf_nodes const& src) {
            ddnf_nodes::iterator it = src.begin(), end = src.end();
            for (; it != end; ++it) {
                dst.insert(*it);
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
        
        void insert(tbv const& t) {
            get(t.size()).insert(t);
        }
        
        ddnf_mgr& get(unsigned sz) {
            ddnf_mgr* result = 0;
            if (!m_mgrs.find(sz, result)) {
                result = insert(sz);
                m_mgrs.insert(sz, result);
            }
            return *result;
        }

        ddnf_nodes const& lookup(tbv const& t) const {
            return m_mgrs.find(t.size())->lookup(t);
        }

        void display(std::ostream& out) const {
            u_map<ddnf_mgr*>::iterator it = m_mgrs.begin(), end = m_mgrs.end();
            for (; it != end; ++it) {
                it->m_value->display(out);
            }
        }

    private:

        ddnf_mgr* insert(unsigned n) {
            ddnf_mgr* m = 0;
            if (!m_mgrs.find(n, m)) {
                m = alloc(ddnf_mgr, n);
                m_mgrs.insert(n, m);
            }
            return m;
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
        bv_util                bv;
        volatile bool          m_cancel;
        ptr_vector<expr>       m_todo;
        ast_mark               m_visited1, m_visited2;
        ddnfs                  m_ddnfs;
        stats                  m_stats;
        obj_map<expr, tbv>     m_expr2tbv;
        obj_map<expr, expr*>   m_cache;
        expr_ref_vector        m_trail;
        context                m_inner_ctx;

    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            bv(m),
            m_cancel(false),
            m_trail(m),
            m_inner_ctx(m, m_ctx.get_register_engine(), m_ctx.get_fparams())
        {
            params_ref params;
            params.set_sym("engine", symbol("datalog"));
            m_inner_ctx.updt_params(params);
        }

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            rule_set& old_rules = m_ctx.get_rules();
            rm.mk_query(query, old_rules);
            rule_set new_rules(m_ctx);
            IF_VERBOSE(10, verbose_stream() << "(ddnf.preprocess)\n";);
            if (!pre_process_rules(old_rules)) {
                return l_undef;
            }
            IF_VERBOSE(10, verbose_stream() << "(ddnf.compile)\n";);
            if (!compile_rules1(old_rules, new_rules)) {
                return l_undef;
            }
            IF_VERBOSE(15, m_ddnfs.display(verbose_stream()););

            dump_rules(new_rules);
            return l_undef;

            // return execute_rules(new_rules);
        }
    
        void cancel() {
            m_cancel = true;
            m_inner_ctx.cancel();
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
   
        bool pre_process_rules(rule_set const& rules)  {
            m_visited1.reset();
            m_todo.reset();
            m_cache.reset();
            m_expr2tbv.reset();
            datalog::rule_set::iterator it  = rules.begin();
            datalog::rule_set::iterator end = rules.end();
            for (; it != end; ++it) {
                if (!pre_process_rule(**it)) {
                    return false;
                }
            }
            return true;
        }

        bool pre_process_rule(rule const& r) {
            // all predicates are monadic.
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned sz = r.get_tail_size();
            for (unsigned i = utsz; i < sz; ++i) {
                m_todo.push_back(r.get_tail(i));
            }
            if (process_todo()) {
                return true;
            }
            else {
                r.display(m_ctx, std::cout);
                return false;
            }
        }

        bool process_todo() {
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
                if (is_ground(e)) {
                    continue;
                }
                if (process_atomic(e)) {
                    continue;
                }
                IF_VERBOSE(0, verbose_stream() << "Could not handle: " << mk_pp(e, m) << "\n";);
                return false;
            }
            return true;
        }        

        bool process_atomic(expr* e) {
            expr* e1, *e2, *e3;
            unsigned lo, hi;            
            
            if (m.is_eq(e, e1, e2) && bv.is_bv(e1)) {
                if (is_var(e1) && is_ground(e2)) {
                    return process_eq(e, to_var(e1), bv.get_bv_size(e1)-1, 0, e2); 
                }
                if (is_var(e2) && is_ground(e1)) {
                    return process_eq(e, to_var(e2), bv.get_bv_size(e2)-1, 0, e1); 
                }
                if (bv.is_extract(e1, lo, hi, e3) && is_var(e3) && is_ground(e2)) {
                    return process_eq(e, to_var(e3), hi, lo, e2);
                }
                if (bv.is_extract(e2, lo, hi, e3) && is_var(e3) && is_ground(e1)) {
                    return process_eq(e, to_var(e3), hi, lo, e1);
                }
                if (is_var(e1) && is_var(e2)) {
                    return true;
                }                
            }
            return false;
        }

        bool process_eq(expr* e, var* v, unsigned hi, unsigned lo, expr* c) {
            rational val;
            unsigned sz_c;
            unsigned sz_v = bv.get_bv_size(v);
            if (!bv.is_numeral(c, val, sz_c)) {
                return false;
            }
            if (!val.is_uint64()) {
                return false;
            }
            // v[hi:lo] = val
            tbv tbv(val.get_uint64(), sz_v, hi, lo);            
            m_ddnfs.insert(tbv);
            m_expr2tbv.insert(e, tbv);
            // std::cout << mk_pp(v, m) << " " << lo << " " << hi << " " << v << " " << tbv << "\n";
            return true;
        }

        void init_ctx(rule_set& rules) {
            m_inner_ctx.reset();
            func_decl_set const& predicates = m_ctx.get_predicates();
            for (func_decl_set::iterator fit = predicates.begin(); fit != predicates.end(); ++fit) {
                m_inner_ctx.register_predicate(*fit, false);
            }
            m_inner_ctx.ensure_opened();
            m_inner_ctx.replace_rules(rules);
            m_inner_ctx.close();
        }

        void dump_rules(rule_set& rules) {
            init_ctx(rules);
            m_inner_ctx.display_smt2(0, 0, std::cout);
        }

        lbool execute_rules(rule_set& rules) {
            init_ctx(rules);

            ptr_vector<func_decl> heads;
            rule_set::decl2rules::iterator dit  = rules.begin_grouped_rules();
            rule_set::decl2rules::iterator dend = rules.end_grouped_rules();
            for (; dit != dend; ++dit) {
                heads.push_back(dit->m_key);
            }
            return m_inner_ctx.rel_query(heads.size(), heads.c_ptr());
        }

        bool compile_rules1(rule_set const& rules, rule_set& new_rules) {
            datalog::rule_set::iterator it  = rules.begin();
            datalog::rule_set::iterator end = rules.end();
            unsigned idx = 0;
            for (; it != end; ++idx, ++it) {
                if (!compile_rule1(**it, rules, new_rules)) {
                    return false;
                }
            }
            return true;            
        }

        bool compile_rule1(rule& r, rule_set const& old_rules, rule_set& new_rules) {
            app_ref head(m), pred(m);
            app_ref_vector body(m);
            expr_ref tmp(m);
            compile_predicate(r.get_head(), head);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned sz = r.get_tail_size();
            for (unsigned i = 0; i < utsz; ++i) {
                compile_predicate(r.get_tail(i), pred);
                body.push_back(pred);
            }
            for (unsigned i = utsz; i < sz; ++i) {
                compile_expr(r.get_tail(i), tmp);
                body.push_back(to_app(tmp));
            }
            rule* r_new = rm.mk(head, body.size(), body.c_ptr(), 0, r.name(), false);
            new_rules.add_rule(r_new);
            IF_VERBOSE(20, r_new->display(m_ctx, verbose_stream()););
            if (old_rules.is_output_predicate(r.get_decl())) {
                new_rules.set_output_predicate(r_new->get_decl());
            }
            return true;
        }

        void compile_predicate(app* p, app_ref& result) {
            sort_ref_vector domain(m);
            func_decl* d = p->get_decl();
            SASSERT(d->get_family_id() == null_family_id);
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                domain.push_back(compile_sort(m.get_sort(p->get_arg(i))));
            }
            func_decl_ref fn(m);
            fn = m.mk_func_decl(d->get_name(), domain.size(), domain.c_ptr(), m.mk_bool_sort());
            m_ctx.register_predicate(fn, false);
            expr_ref_vector args(m);
            expr_ref tmp(m);
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                compile_expr(p->get_arg(i), tmp);
                args.push_back(tmp);
            }
            result = m.mk_app(fn, args.size(), args.c_ptr());
        }

        void insert_cache(expr* e, expr* r) {
            m_trail.push_back(r);
            m_cache.insert(e, r);
        }

        void compile_var(var* v, var_ref& result) {
            expr* r;
            if (m_cache.find(v, r)) {
                result = to_var(r);
            }
            else {
                unsigned idx = v->get_idx();
                result = m.mk_var(idx, compile_sort(v->get_sort()));
                insert_cache(v, result);
            }
        }

        sort* compile_sort(sort* s) {
            if (m.is_bool(s)) {
                return s;
            }
            if (bv.is_bv_sort(s)) {
                unsigned sz = bv.get_bv_size(s);
                ddnf_mgr const& mgr = m_ddnfs.get(sz);
                unsigned num_elems = mgr.size();
                unsigned nb = 1;
                while ((1UL << nb) <= num_elems) {
                    ++nb;                    
                }
                return bv.mk_sort(nb);
            }
            UNREACHABLE();
            return 0;
        }

        void compile_expr(expr* e, expr_ref& result) {
            expr* r = 0;
            if (m_cache.find(e, r)) {
                result = r;
                return;
            }

            if (is_ground(e)) {
                result = e;
                m_cache.insert(e, result);
                return;
            }

            if (is_var(e)) {
                var_ref w(m);
                compile_var(to_var(e), w);
                result = w;
                return;
            }
            
            if (m.is_and(e) ||
                m.is_or(e)  ||
                m.is_iff(e) ||
                m.is_not(e) ||
                m.is_implies(e)) {
                app* a = to_app(e);
                expr_ref tmp(m);
                expr_ref_vector args(m);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    compile_expr(a->get_arg(i), tmp);
                    args.push_back(tmp);
                } 
                result = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
                insert_cache(e, result);
                return;
            }
            
            expr* e1, *e2, *e3;
            unsigned lo, hi; 
            if (m.is_eq(e, e1, e2) && bv.is_bv(e1)) {
                if (is_var(e1) && is_ground(e2)) {
                    compile_eq(e, result, to_var(e1), bv.get_bv_size(e1)-1, 0, e2); 
                }
                else if (is_var(e2) && is_ground(e1)) {
                    compile_eq(e, result, to_var(e2), bv.get_bv_size(e2)-1, 0, e1); 
                }
                else if (bv.is_extract(e1, lo, hi, e3) && is_var(e3) && is_ground(e2)) {
                    compile_eq(e, result, to_var(e3), hi, lo, e2);
                }
                else if (bv.is_extract(e2, lo, hi, e3) && is_var(e3) && is_ground(e1)) {
                    compile_eq(e, result, to_var(e3), hi, lo, e1);
                }
                else if (is_var(e1) && is_var(e2)) {
                    var_ref v1(m), v2(m);
                    compile_var(to_var(e1), v1);
                    compile_var(to_var(e2), v2);
                    result = m.mk_eq(v1, v2);
                }                
                else {
                    UNREACHABLE();
                }
                insert_cache(e, result);
                return;
            }         
            std::cout << mk_pp(e, m) << "\n";
            UNREACHABLE();
        }

        void compile_eq(expr* e, expr_ref& result, var* v, unsigned hi, unsigned lo, expr* c) {
            tbv t;
            VERIFY(m_expr2tbv.find(e, t));            
            var_ref w(m);
            compile_var(v, w);
            ddnf_nodes const& ns = m_ddnfs.lookup(t);
            ddnf_nodes::iterator it = ns.begin(), end = ns.end();
            expr_ref_vector eqs(m);
            sort* s = m.get_sort(w);
            for (; it != end; ++it) {
                eqs.push_back(m.mk_eq(w, bv.mk_numeral(rational((*it)->get_id()), s)));
            }
            switch (eqs.size()) {
            case 0:
                UNREACHABLE();
                result = m.mk_false();
                break;
            case 1:
                result = eqs[0].get();
                break;
            default:
                result = m.mk_or(eqs.size(), eqs.c_ptr());
                break;
            }
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
