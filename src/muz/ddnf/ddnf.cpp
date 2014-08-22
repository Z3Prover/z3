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
#include "trail.h"
#include "dl_rule_set.h"
#include "dl_context.h"
#include "dl_mk_rule_inliner.h"
#include "smt_kernel.h"
#include "qe_lite.h"
#include "bool_rewriter.h"
#include "th_rewriter.h"
#include "datatype_decl_plugin.h"
#include "for_each_expr.h"
#include "matcher.h"
#include "scoped_proof.h"
#include "fixedpoint_params.hpp"


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

        void resize(unsigned n, unsigned val) {
            while (size() < n) {
                bit_vector::push_back((val & 2) != 0);
                bit_vector::push_back((val & 1) != 0);
            }
        }

        bool empty() const { return false; } // TBD

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

    class dot {
        tbv         m_pos;
        vector<tbv> m_negs;
    public:
        dot(tbv const& pos, vector<tbv> const& negs):
            m_pos(pos), m_negs(negs) {}

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
        
    public:
        ddnf_node(ddnf_mgr& m, tbv const& tbv):
            m_tbv(tbv),
            m_children(m),
            m_refs(0) {                        
        }

        unsigned inc_ref() {
            return ++m_refs;
        }

        unsigned dec_ref() {
            SASSERT(m_refs > 0);
            return --m_refs;
        }
        
        unsigned num_children() const { return m_children.size(); }

        ddnf_node* operator[](unsigned index) { return m_children[index].get(); }

        tbv const& get_tbv() const { return m_tbv; }

        void add_child(ddnf_node* n);
        
        void remove_child(ddnf_node* n);
        
        bool contains_child(ddnf_node* n) const;

    };

    class ddnf_mgr {
        unsigned              m_num_bits;
        ddnf_node*            m_root;
        ddnf_node_vector      m_nodes;
        vector<dot>           m_dots;
    public:
        ddnf_mgr(unsigned n): m_num_bits(n), m_nodes(*this) {
            m_root = alloc(ddnf_node, *this, tbv(n, BIT_x));
            m_nodes.push_back(m_root);
        }

        void inc_ref(ddnf_node* n) {
            n->inc_ref();
        }

        void dec_ref(ddnf_node* n) {
            unsigned count = n->dec_ref();
            NOT_IMPLEMENTED_YET();
        }

    private:
        void insert_new(ddnf_node& root, ddnf_node* new_n, 
                        ptr_vector<tbv>& new_intersections) {
            SASSERT(root.get_tbv().is_superset(new_n->get_tbv()));
//            if (root == *new_n) return;
            bool inserted = false;
            for (unsigned i = 0; i < root.num_children(); ++i) {
                ddnf_node& child = *(root[i]);
                if (child.get_tbv().is_superset(new_n->get_tbv())) {
                    inserted = true;
                    insert_new(child, new_n, new_intersections);
                }
            }
            if (inserted) return;
            ddnf_node_vector subset_children(*this);
            for (unsigned i = 0; i < root.num_children(); ++i) {
                ddnf_node& child = *(root[i]);
                // cannot be superset
                // checking for subset
                if (child.get_tbv().is_subset(new_n->get_tbv())) {
                    subset_children.push_back(&child);
                }
                // this means there is a non-full intersection
                else {
                    tbv intr;
                    // TBD intersect(child.get_tbv(), new_n->get_tbv(), intr);
                    if (!intr.empty()) {
                        // TBD new_intersections.push_back(intr);
                    }
                }
            }
            for (unsigned i = 0; i < subset_children.size(); ++i) {
                root.remove_child(subset_children[i].get());
                new_n->add_child(subset_children[i].get());
            }
            root.add_child(new_n);           
        }


#if 0

        DDNFNode InsertTBV(TernaryBitVector aTbv)
        {
            foreach (DDNFNode node in allNodes)
            {
                if (node.tbv.IsEqualset(aTbv))
                {
                    return node;
                }
            }
            DDNFNode newNode = new DDNFNode(aTbv);
            this.allNodes.Add(newNode);
            List<TernaryBitVector> newIntersections = new List<TernaryBitVector>();
            InsertNewNode(this.root, newNode, newIntersections);

            // add the TBVs corresponding to new intersections
            foreach (TernaryBitVector newIntr in newIntersections)
            {
                // this assert guarantees termination since you can only
                // insert smaller tbvs recursively
                Debug.Assert(!newIntr.IsSupset(aTbv));

                InsertTBV(newIntr);
            }

            return newNode;
        }

        public void InsertDot(DOT aDot)
        {
            this.allDots.Add(aDot);
            DDNFNode posNode = InsertTBV(aDot.pos);
            List<DDNFNode> negNodes = new List<DDNFNode>();
            foreach (TernaryBitVector neg in aDot.negs)
            {
                negNodes.Add(InsertTBV(neg));
            }

            posNode.posDots.Add(aDot);
            foreach (DDNFNode negNode in negNodes)
            {
                negNode.negDots.Add(aDot);
            }
        }

        // remove all negNodes for each dot in dot2Nodes
        void RemoveNegNodesForAllDots(DDNFNode aNode, HashSet<DOT> activeDots,
            ref Dictionary<DOT, HashSet<DDNFNode>> dot2Nodes)
        {
            foreach (DOT negDot in aNode.negDots)
            {
                activeDots.Add(negDot);
            }

            foreach (DOT activeDot in activeDots)
            {
                dot2Nodes[activeDot].Remove(aNode);
            }

            foreach (DDNFNode child in aNode.children)

            {
                RemoveNegNodesForAllDots(child, new HashSet<DOT>(activeDots), ref dot2Nodes);
            }
        }

        // add all posNodes for each dot in dot2Nodes
        void AddPosNodesForAllDots(DDNFNode aNode, HashSet<DOT> activeDots,
            ref Dictionary<DOT, HashSet<DDNFNode>> dot2Nodes)
        {
            foreach (DOT posDot in aNode.posDots)
            {
                activeDots.Add(posDot);
            }

            foreach (DOT activeDot in activeDots)
            {
                dot2Nodes[activeDot].Add(aNode);
            }

            foreach (DDNFNode child in aNode.children)
            {
                AddPosNodesForAllDots(child, new HashSet<DOT>(activeDots), ref dot2Nodes);
            }
        }

        public Dictionary<DOT, HashSet<DDNFNode>> NodesForAllDots()
        {
            Dictionary<DOT, HashSet<DDNFNode>> dot2Nodes = 
                new Dictionary<DOT, HashSet<DDNFNode>>();

            foreach (DOT dot in allDots)
            {
                dot2Nodes[dot] = new HashSet<DDNFNode>();
            }
            AddPosNodesForAllDots(this.root, new HashSet<DOT>(), ref dot2Nodes);
            RemoveNegNodesForAllDots(this.root, new HashSet<DOT>(), ref dot2Nodes);

            return dot2Nodes;

        }
        public string PrintNodes()
        {
            StringBuilder retVal = new StringBuilder();
            retVal.Append("<DDNF: ");
            foreach (DDNFNode node in allNodes)
            {
                retVal.Append("\n").Append(node.ToString());
            }
            return retVal.Append(">").ToString();
        }
    }


}

#endif
        
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
