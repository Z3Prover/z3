#ifdef _WINDOWS
#include "vector.h"
#include "region.h"
#include "trail.h"
#include "nat_set.h"
#include "stream_buffer.h"
#include "obj_hashtable.h"
#include "reg_decl_plugins.h"

class partition {
public:
    class id { 
        friend class partition;
        unsigned m_id; 
        id(unsigned idx): m_id(idx) {} 
        unsigned get_id() const { return m_id; }
    public:
        id() : m_id(0) {}
        bool operator==(id const& other) const { return m_id == other.m_id; }
        bool operator!=(id const& other) const { return m_id != other.m_id; }     
        std::ostream& display(std::ostream& out) const {
            return out << "p" << m_id; 
        }
    };
private:
    static const unsigned invalid_length = 0xFFFFFFFF;

    unsigned_vector      m_vertices; // permutation of vertices
    svector<id>          m_roots;    // pointers to class roots, the position in m_vertices that contains the root.
    unsigned_vector      m_lengths;  // length of equivalence class, valid at root position.
    unsigned_vector      m_length_trail;
    unsigned_vector      m_offset_trail;
    unsigned_vector      m_length_lim;

    bool invariant() const {
        if (m_roots.size() != m_vertices.size()) {
            return false;
        }
        if (m_roots.size() != m_lengths.size()) {
            return false;
        }
        for (unsigned i = 0; i < m_roots.size(); ++i) {
            if (!is_root(m_vertices[m_roots[m_vertices[i]].get_id()])) {
                return false;
            }
        }
        return true;
    }

    bool is_root(id class_id) const {
        return 
            class_id.m_id < m_vertices.size() &&
            m_roots[m_vertices[class_id.m_id]] == class_id;
    }

public:

    class mark {
        partition& m_partition;
        nat_set    m_mark;

    public:
        mark(partition& p): m_partition(p) {
            m_mark.assure_domain(p.m_roots.size());
        }
        
        void reset() {
            m_mark.reset();
        }
        
        bool test_and_set(id class_id0) {
            if (m_mark.contains(class_id0.m_id)) {
                return false;
            }
            m_mark.insert(class_id0.m_id);             
            return true;
        }
    };

    partition(unsigned size) {
        for (unsigned i = 0; i < size; ++i) {
            m_vertices.push_back(i);
            m_roots.push_back(id(0));
            m_lengths.push_back(invalid_length);
        }        
        m_lengths[0] = size;        
    }

    void push_scope() {
        SASSERT(invariant());
        m_length_lim.push_back(m_length_trail.size());
    }

    void pop_scope(unsigned num_scopes) {
        if (num_scopes == 0) {
            return;
        }
        unsigned lvl      = m_length_lim.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl  = lvl - num_scopes;
        unsigned old_size = m_length_lim[new_lvl];
        //
        // NB. backtracking could be expensive in the case where
        // we partition the same class multiple times during
        // one level. Alternative is to maintain level indication
        // together with length to avoid pushing redundant length
        // constraints on the stack.
        //
        for (unsigned i = m_length_trail.size(); i > old_size; ) {
            --i;
            unsigned offset = m_offset_trail[i];
            unsigned length = m_length_trail[i];
            id class_id(offset);
            if (length != invalid_length) {
                for (unsigned j = 0; j < length; ++j) {
                    m_roots[m_vertices[offset + j]] = class_id;
                }
            }
            m_lengths[offset] = length;
        }
        m_length_trail.shrink(old_size);
        m_offset_trail.shrink(old_size);
        m_length_lim.shrink(new_lvl);
        SASSERT(invariant());
    }

    unsigned get_size(id class_id) const {
        SASSERT(is_root(class_id));
        return m_lengths[class_id.m_id];
    }

    unsigned * get_elems(id class_id) {
        SASSERT(is_root(class_id));
        return m_vertices.begin() + class_id.m_id;
    }

    unsigned const * get_elems(id class_id) const {
        return m_vertices.begin() + class_id.m_id;
    }

    void mk_partition(unsigned length, unsigned const* vertices) {
        SASSERT(m_vertices.begin() <= vertices);
        SASSERT(vertices < m_vertices.begin() + m_vertices.size());
        unsigned offset = static_cast<unsigned>(vertices - m_vertices.begin());
        m_length_trail.push_back(m_lengths[offset]);
        m_offset_trail.push_back(offset);
        m_lengths[offset] = length;
        id class_id(offset);
        for (unsigned i = 0; i < length; ++i) {
            m_roots[vertices[i]] = class_id;
        }
    }       

    id operator[](unsigned v) const {
        return m_roots[v];
    }

    void display(std::ostream& out) {
        for (unsigned i = 0; i < m_vertices.size(); ++i) {
            out << m_vertices[i] << " |-> " << m_roots[m_vertices[i]].m_id << "\n";
        }
    }

    void copy_vertices(unsigned_vector& vertices) {
        vertices = m_vertices;
    }

    void split(id id, unsigned v, unsigned pos) {
        // split class id into two parts. 
        // put var v at position pos in a singleton class.
        // 
        // TBD: can swap into last place to save updates to ids.
        // TBD: nothing ensures vertices are invariant under backtracking.
        // TBD: the new partitions should be added to m_todo in 
        //      the refiner.
        //
        unsigned offset = id.get_id();
        if (pos > offset) {
            unsigned length = m_lengths[offset];
            std::swap(m_vertices.begin()[pos],m_vertices.begin()[offset]);
            SASSERT(length > 1);
            mk_partition(1, m_vertices.begin()+offset);
            mk_partition(length-1,m_vertices.begin()+offset+1);
        }
    }

    bool next_split(id& class_id) {
        //
        // TBD: find first non-singleton partition that is not already
        // split on.
        //
        return false;
    }

};

class graph {
    // vertex adjacency graph:
    vector<vector<unsigned,false> > m_in;
    vector<vector<unsigned,false> > m_out;
    unsigned m_max_degree;


public:
    graph() : m_max_degree(0) {}

    void add_vertex(unsigned v) {
        if (get_num_vertices() <= v) {
            m_out.resize(v+1,vector<unsigned,false>());
            m_in.resize(v+1,vector<unsigned,false>());
        }
        SASSERT(get_num_vertices() == m_in.size());
        SASSERT(get_num_vertices() == m_out.size());
        SASSERT(v < get_num_vertices());
    }


    void add_edge(unsigned src, unsigned dst) {        
        SASSERT(src < get_num_vertices());
        SASSERT(dst < get_num_vertices());
        m_out[src].push_back(dst);
        m_in[dst].push_back(src);
        if (m_out[src].size() > m_max_degree) {
            m_max_degree = m_out[src].size();
        }
    }

    unsigned get_num_in(unsigned dst) const { 
        return m_in[dst].size();
    }

    unsigned get_src(unsigned dst, unsigned idx) const {
        return m_in[dst][idx];
    }
    
    unsigned get_dst(unsigned src, unsigned idx) const {
        return m_out[src][idx];
    }

    unsigned get_num_out(unsigned src) const {
        return m_out[src].size();
    }

    unsigned get_num_vertices() const {
        return m_in.size();
    }

    unsigned get_max_degree() const {
        return m_max_degree;
    }
};

class partition_refiner {

    partition&     m_partition;
    graph&         m_graph;
    partition::mark m_mark;

    
    // 
    // Temporary variables.
    // 
    svector<partition::id> m_todo;
    svector<partition::id> m_inverse;

    //
    // For bucketizing bisimilar nodes.
    //
    vector<unsigned,false> m_non_empty_buckets;
    vector<unsigned_vector> m_buckets;


public:
    partition_refiner(partition& p, graph& g): m_partition(p), m_graph(g), m_mark(p) {
        m_buckets.resize(m_graph.get_max_degree()+1);
    }

    void add_refine_class(partition::id id) {
        m_todo.push_back(id);
    }

    //
    // 
    // compute equivalence classes for vertices
    // based on partition refinement.
    // 
    // m_todo contains node classes to partition refine.
    // 
    void partition_refinement() {
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            partition_refinement(m_todo[i]);
        }
        m_todo.reset();
    }        


private:

    // 
    // refine classes with vertices entering id_dst
    // TBD: if we already refined id_dst, then avoid redundant re-refining?
    // 
    void partition_refinement(partition::id id_dst) {
        m_mark.reset();
        unsigned class_sz = m_partition.get_size(id_dst);
        unsigned const* elems = m_partition.get_elems(id_dst);
        for (unsigned j = 0; j < class_sz; ++j) {
            unsigned dst = elems[j];
            unsigned in_degree = m_graph.get_num_in(dst);
            for (unsigned k = 0; k < in_degree; ++k) {
                unsigned src = m_graph.get_src(dst,k);
                partition::id id_src = m_partition[src];
                if (m_mark.test_and_set(id_src)) {
                    partition_refinement(id_src, id_dst);
                }
            }
        }
    }

    //
    // refined partition algorithm based on
    // counting number of edges to id_dst.
    //
    void partition_refinement(partition::id id_src, partition::id id_dst) {

        unsigned src_sz = m_partition.get_size(id_src);
        unsigned* src_elems = m_partition.get_elems(id_src);
        // 
        // First pass: count number of connections to id_dst.
        // Move vertices with 0 count into prefix.
        // Count max-count
        // 
        unsigned max_count = 0;
        unsigned num_max_count = 0;
        unsigned num_zeros = 0;
        for (unsigned j = 0; j < src_sz; ++j) {
            unsigned src = src_elems[j];
            unsigned count = 0;
            unsigned out_degree = m_graph.get_num_out(src);
            for (unsigned k = 0; k < out_degree; ++k) {
                unsigned dst = m_graph.get_dst(src,k);
                if (m_partition[dst] == id_src) {
                    ++count;
                }
            }
            if (count > max_count) {
                max_count = count;
                num_max_count = 1;
            }
            else if (count == max_count) {
                ++num_max_count;
            }
            if (count == 0) {
                SASSERT(num_zeros <= j);
                if (num_zeros < j) {
                    std::swap(src_elems[j],src_elems[num_zeros]);
                }
                ++num_zeros;
            }
            else {
                m_buckets[count].push_back(src);
                if (m_buckets[count].size() == 1) {
                    m_non_empty_buckets.push_back(count);
                }
            }
        }
        // 
        // All vertices have the same degree.
        // 
        if (num_max_count == src_sz) {
            reset_buckets();
            return;
        }

        //
        // at least two vertices have different counts
        // reaching id_src.
        //

        //
        // Second pass: refine [src_elems+num_zeros..src_elems+src_size-1] based on count-sort.
        //
        
        SASSERT(m_non_empty_buckets.size() >= 1);

        unsigned largest_bucket_pos = 0;
        unsigned largest_bucket_sz = num_zeros;
        unsigned pos = num_zeros;
        if (num_zeros > 0) {
            m_partition.mk_partition(num_zeros, src_elems);
        }
        for (unsigned i = 0; i < m_non_empty_buckets.size(); ++i) {
            unsigned bucket_id = m_non_empty_buckets[i];
            unsigned_vector const& bucket = m_buckets[bucket_id];
            unsigned bucket_sz = bucket.size();
            SASSERT(bucket_sz > 0);
            for (unsigned j = 0; j < bucket_sz; ++j) {
                src_elems[pos+j] = bucket[j];                
            }
            if (largest_bucket_sz < bucket_sz) {
                largest_bucket_sz = bucket_sz;
                largest_bucket_pos = pos;
            }
            m_partition.mk_partition(bucket_sz, src_elems+pos);
            pos += bucket_sz;
        }

        //
        // Insert all partitions except for largest_bucket_pos.
        //
        pos = 0;
        if (num_zeros > 0 && largest_bucket_pos != 0) {
            m_todo.push_back(m_partition[src_elems[0]]);
        }
        pos += num_zeros;
        for (unsigned i = 0; i < m_non_empty_buckets.size(); ++i) {
            unsigned sz = m_buckets[m_non_empty_buckets[i]].size();
            if (pos != largest_bucket_pos) {
                m_todo.push_back(m_partition[src_elems[pos]]);
            }
            pos += sz;
        }

        // reset buckets that were used.
        reset_buckets();
    }

    void reset_buckets() {
        for (unsigned i = 0; i < m_non_empty_buckets.size(); ++i) {
            m_buckets[m_non_empty_buckets[i]].reset();
        }
        m_non_empty_buckets.reset();
    }
};

class automorphism_search {
    struct stats {
        unsigned m_nodes;
        unsigned m_max_level;
        stats() : m_nodes(0), m_max_level(0) {}
    };
    bool              m_first;
    unsigned_vector   m_first_permutation;
    partition_refiner m_refiner;
    stats             m_stats;
    partition&        m_partition;
    graph&            m_graph;
    unsigned_vector   m_num_elems;
    ptr_vector<unsigned> m_elems;

public:

    automorphism_search(partition& p, graph& g): 
        m_first(true), 
        m_refiner(p,g),
        m_partition(p),
        m_graph(g)
    {}

    void search_main() {
        search();
    }
private:

    bool propagate(partition::id& id) {
        m_refiner.partition_refinement();
        
        if (m_partition.next_split(id)) {
            return true;
        }
            
        if (m_first) {
            m_first = false;
            m_partition.copy_vertices(m_first_permutation);
            pop_scope(1);
        }
        else {
            // not the first node.
            // process this.
            // TBD
            
        }
        return false;
    }

    //
    // enumerate elements from partition id:
    //
    
    void search() {
        partition::id id;
        unsigned num_elems;
        unsigned * elems;

        while (true) {
            if (propagate(id)) {
                push_scope();
                num_elems = m_partition.get_size(id);
                elems = m_partition.get_elems(id);
                SASSERT(num_elems > 0);                
                m_num_elems.push_back(num_elems);
                m_elems.push_back(elems);            
            }
            else if (get_level() == 0) {
                return;
            }
            else {
                num_elems = m_num_elems.back();
                elems = m_elems.back();
            }

            // TBD orbits.

            if (num_elems == 0) {
                pop_scope(1);
            }
            else {
                m_partition.split(id, elems[0], 0); // TBD
                --m_num_elems.back();
                ++m_elems.back();
            }
        }
    }

    // TBD:
    void push_scope() {}
    
    void pop_scope(unsigned num_scopes) {}
    
    unsigned get_level() { return 0; }

};

void tst_symmetry0() {
    graph g;
    partition p(6);
    for (unsigned i = 0; i < 6; ++i) {
        g.add_vertex(i);
    }
    for (unsigned i = 0; i < 3; ++i) {
        g.add_edge(i,i+3);
    }
    g.add_edge(0,1);
    g.add_edge(1,2);
    g.add_edge(2,0);
    partition_refiner r(p,g);
    r.add_refine_class(p[0]);
    r.partition_refinement();
    p.display(std::cout);
}

#include "ast.h"
#include "smtparser.h"
#include "array_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "basic_simplifier_plugin.h"
#include "front_end_params.h"
#include "smt_context.h"

class expr_symmetry_graph {
    template<class T>
    class labeling :  public obj_map<T const, unsigned> {
        unsigned m_count;
        u_map<T*> m_inverse;
    public:
        labeling() : m_count(0) {}
        
        unsigned get_count() const { return m_count; }
        
        unsigned get_label(T* e) {
            unsigned lbl = 0;
            if (!find(e, lbl)) {
                insert(e, ++m_count);
                lbl = m_count;
                m_inverse.insert(lbl, e);
            }
            return lbl;
        }

        unsigned get_existing_label(T* e) {
            unsigned lbl = 0;
            if (!find(e, lbl)) {
                UNREACHABLE();
            }
            return lbl;
        }

        T* get_inverse(unsigned n) {
            T* a = 0;
            if (!m_inverse.find(n, a)) {
                return 0;
            }
            return a;
        }
    };

    ast_manager     m_mgr;
    labeling<expr>  m_node_id;
    expr_ref_vector m_formulas;
    expr_ref_vector m_symmetry_breakers;
    expr_ref_vector m_aux_preds;
    
    typedef obj_map<func_decl const, unsigned> func_decl_map;
    

    bool is_labeled_function(func_decl* d) {
        if (d->is_commutative() || d->get_arity() <= 1) {
            return false;
        }
        if (m_mgr.is_distinct(d)) {
            return false;
        }
        
        return true;
    }
    
    // TBD: we are not really interested in symmetries on unit literals.
    
    void print_graph(std::ostream& out, unsigned num_exprs, expr *const* exprs) {
        ptr_vector<expr> todo;
        ast_mark mark;
        unsigned num_vertices = 0, num_edges = 0;
        unsigned num_arity_colors = 0;
        labeling<ast> node_color;
        func_decl_map arity_color_map;
        
        todo.append(num_exprs, exprs);
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (m_node_id.contains(e)) {
                continue;
            }
            m_node_id.get_label(e);
            
            ++num_vertices;
            if (is_app(e)) {
                app* a = to_app(e);
                func_decl* d = a->get_decl();
                node_color.get_label(d);
                unsigned arity = a->get_num_args();
                todo.append(arity, a->get_args());
                if (!is_labeled_function(d)) {
                    num_edges += arity;
                }
                else {
                    num_edges += 2*arity;
                    if (!arity_color_map.contains(d)) {
                        arity_color_map.insert(d,num_arity_colors);
                        num_arity_colors += arity;
                    }
                }
            }
        }
        num_vertices = m_node_id.get_count() + num_arity_colors;
        
        out << "p edge " << num_vertices << " " << num_edges << "\n";

        // print graph

        // print nodes used for arities:
        func_decl_map::iterator it  = arity_color_map.begin();
        func_decl_map::iterator end = arity_color_map.end();
        for (; it != end; ++it) {
            func_decl const* d = (*it).m_key;
            unsigned offset = (*it).m_value;
            for (unsigned i = 0; i < d->get_arity(); ++i) {
                out << "n " << offset + m_node_id.get_count() + i << " " << i + 1 << "\n";
            }
        }
        
        todo.append(num_exprs, exprs);
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e)) {
                continue;
            }
            mark.mark(e,true);
            unsigned id = m_node_id.get_existing_label(e);
            
            if (is_app(e)) {
                app* a = to_app(e);
                func_decl* d = a->get_decl();
                unsigned arity = a->get_num_args();
                unsigned offset;

                todo.append(arity, a->get_args());
                out << "c " << d->get_name() << "\n";
                if(m_mgr.is_value(a) || arity > 0) {                    
                    out << "n " << id << " " << node_color.get_label(d) << "\n";                    
                }
                else {
                    out << "n " << id << " 0\n";
                }

                if (is_labeled_function(d) && !arity_color_map.find(d,offset)) {
                    UNREACHABLE();
                }
                for (unsigned i = 0; i < arity; ++i) {
                    unsigned id2 = m_node_id.get_existing_label(a->get_arg(i));
                    if (!is_labeled_function(d)) {
                        out << "e " << id << " " << id2 << "\n";
                    }
                    else {
                        unsigned color = offset + m_node_id.get_count() + i;
                        out << "e " << id    << " " << color << "\n";
                        out << "e " << color << " " << id2 << "\n";
                    }
                }
            }
        }       
    }

public:
    expr_symmetry_graph() : 
        m_formulas(m_mgr), 
        m_symmetry_breakers(m_mgr),
        m_aux_preds(m_mgr) {
    }

    void parse_file(char const* file_path, char const* file_tmp) {
        
        smtlib::parser* parser = smtlib::parser::create(m_mgr);
        reg_decl_plugins(m_mgr);
        parser->initialize_smtlib();
        
        if (!parser->parse_file(file_path)) {
            std::cout << "Could not parse file : " << file_path << std::endl;
            dealloc(parser);
            return;
        }
        
        smtlib::benchmark* b = parser->get_benchmark();
        
        smtlib::theory::expr_iterator it  = b->begin_formulas();
        smtlib::theory::expr_iterator end = b->end_formulas();
        for (; it != end; ++it) {
            m_formulas.push_back(*it);
        }
        it  = b->begin_axioms();
        end = b->end_axioms();
        for (; it != end; ++it) {
            m_formulas.push_back(*it);
        }

        std::ofstream out(file_tmp);

        if (out.bad() || out.fail()) {
            std::cerr << "Error: failed to open file \"" << file_tmp << "\" for writing.\n";
            exit(ERR_OPEN_FILE);
        }
        print_graph(out, m_formulas.size(), m_formulas.c_ptr());    
        out.close();
        
        dealloc(parser);
    }

private:
    static void skip_blank(stream_buffer& inp) {
        while (*inp == ' ' || *inp == '\t' || *inp == '\r') {
            ++inp;
        }
    }


    static bool read_line(stream_buffer& inp) {
        while (*inp != EOF && *inp != '\n') {
            ++inp;
        }
        if (*inp == EOF) {
            return false;
        }
        ++inp;
        return true;
    }
    
    
    enum token_type {
        t_undef,
        t_eof,
        t_alpha,
        t_digit,
        t_special
    };

    static token_type get_token_type(int c) {
        if ('0' <= c && c <= '9') {
            return t_digit;
        }
        if ('a' <= c && c <= 'z') {
            return t_alpha;
        }
        if ('A' <= c && c <= 'Z') {
            return t_alpha;
        }
        return t_special;
    }

    static bool read_token(stream_buffer& in, std::string& token, token_type& ty1) {
        skip_blank(in);
        ty1 = t_undef;
        if (*in == EOF) {
            ty1 = t_eof;
            return false;
        }
        token.clear();
        while (*in != '\n' && 
               *in != ' '  && 
               *in != '\r' && 
               *in != '\t' && 
               *in != EOF) {
            token_type ty2 = get_token_type(*in);
            if (ty1 == t_undef) {
                ty1 = ty2;
                token.push_back(*in);
                ++in;
            }
            else if (ty2 != t_special && ty1 == ty2) {
                token.push_back(*in);
                ++in;
            }
            else {
                break;
            }
        }
        return true;
    }

    static bool read_token(stream_buffer& in, char const* token) {
        token_type ty;
        std::string s;
        return 
            read_token(in, s, ty) && 
            0 == strcmp(s.c_str(), token);
    }

    static bool read_unsigned(char const* token, unsigned& u) {
        u = 0;
        while (*token) {
            if ('0' <= *token && *token <= '9') {
                u = 10*u + (*token - '0');
                ++token;
            }
            else {
                return false;
            }
        }
        return true;
    }

    static bool read_unsigned(stream_buffer& in, unsigned& u) {
        std::string token;
        token_type ty = t_undef;
        if (!(read_token(in, token, ty) && ty == t_digit)) {
            return false;
        }
        return read_unsigned(token.c_str(), u);
    }

    void print_cycle(unsigned_vector const& permutation) {
        for (unsigned i = 0; i < permutation.size(); ++i) {
            ast* a = m_node_id.get_inverse(permutation[i]);
            if (a) {
                std::cout << mk_pp(a, m_mgr) << " ";
            }
        }
        std::cout << "\n";
    }
    

    void mk_symmetry_breaker(vector<unsigned_vector> const& permutation) {
        expr_ref p(m_mgr);
        p = m_mgr.mk_true();
        expr_ref_vector preds(m_mgr);
        basic_simplifier_plugin util(m_mgr);
        for (unsigned i = 0; i < permutation.size(); ++i) {
            unsigned_vector const& cycle = permutation[i];
            if (cycle.size() <= 1) {
                continue;
            }
            unsigned n = cycle[0];
            expr* first = m_node_id.get_inverse(n);
            if (!first) {
                continue;
            }
            
            if (m_mgr.is_or(first) || m_mgr.is_not(first) || m_mgr.is_implies(first) || m_mgr.is_and(first)) {
                continue;
            }
            if (!m_mgr.is_bool(first)) {
                continue;
            }
            // cycle has at least 2 elements, all elements are predicates
            // that are not Boolean connectives.
            for (unsigned j = 0; j + 1 < cycle.size(); ++j) {
                expr_ref q(m_mgr), a(m_mgr), b(m_mgr), ab(m_mgr), ba(m_mgr), e(m_mgr), abq(m_mgr);
                if (j + 2 < cycle.size() || i + 1 < permutation.size()) {
                    q = m_mgr.mk_fresh_const("p",m_mgr.mk_bool_sort());
                    m_aux_preds.push_back(q.get());
                }
                else {
                    q = m_mgr.mk_true();
                }
                a = m_node_id.get_inverse(cycle[j]);
                b = m_node_id.get_inverse(cycle[j+1]);
                util.mk_implies(a,b,ab);
                util.mk_implies(b,a,ba);
                util.mk_and(ab, q, abq);
                util.mk_implies(p,abq,e);
                m_symmetry_breakers.push_back(e.get());
                
                util.mk_and(ba.get(),q.get(),p);
            }
        }
    }
    
    
    
    bool read_cycle(stream_buffer& in, vector<unsigned_vector>& permutation) {
        unsigned_vector cycle;
        unsigned n;
        token_type ty;
        std::string token;
        if (!(read_token(in, token, ty) && ty == t_special && strcmp(token.c_str(),"(") == 0)) {
            std::cout << "read (\n";
            return false;
        }
        if (!read_unsigned(in, n)) {
            std::cout << "read unsigned\n";
            return false;
        }
        cycle.push_back(n);
        while (true) {
            if (!read_token(in, token, ty)) {
                std::cout << "read next token\n";
                return false;
            }
            if (0 == strcmp(token.c_str(),")")) {
                break;
            }
            if (0 != strcmp(token.c_str(),",")) {
                std::cout << "read ,\n";
                return false;
            }
            if (!read_token(in, token, ty)) {
                std::cout << "read next token\n";
                return false;
            }
            if (!read_unsigned(token.c_str(), n)) {
                std::cout << "read number\n";
                return false;
            }
            cycle.push_back(n);
        }
        // print_cycle(cycle);
        permutation.push_back(cycle);
        return true;
    }

    bool read_permutation(stream_buffer& in) {
        vector<unsigned_vector> permutation;
        while (*in != '\n') {
            if (!read_cycle(in, permutation)) {
                return false;
            }
        }
        ++in;
        mk_symmetry_breaker(permutation);
        return true;
    }

public:
    void parse_generators(char const* symmetry_file) {
        std::fstream in(symmetry_file);
        if (in.bad() || in.fail()) {
            std::cerr << "Error: failed to open file \"" << symmetry_file << "\" for reading.\n";
            exit(ERR_OPEN_FILE);
        }
        {
            stream_buffer in_buf(in);
        
            while (true) {
                if (!read_token(in_buf, "Generator")) {
                    if (read_line(in_buf)) {
                        continue;
                    }
                    break;
                }
                if (!read_token(in_buf, ":")) {
                    break;
                }
                if (!read_permutation(in_buf)) {
                    std::cout << "Could not read generator\n";
                    char buffer[2] = { *in_buf, 0 };
                    std::cout << buffer << "\n";
                    break;
                }
                std::cout << "Read generator\n";
                // convert back to symmetry breaking.
            }
        }
        
        in.close();
        
    }

public:
    static void run_bliss(char const* file_in, char const* file_out) {
        char const* bliss_exe = "C:\\users\\nbjorner\\Documents\\Downloads\\bliss-0.50\\bliss-0.50\\bliss.exe";
        char buffer[4024];
#if _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "%s -directed %s > %s", bliss_exe, file_in, file_out);
#else
        sprintf(buffer, "%s -directed %s > %s", bliss_exe, file_in, file_out);
#endif
      system(buffer);  
    }

    void print_symmetry_breakers(const char* out_file) {
        std::ofstream out(out_file);
        if (out.bad() || out.fail()) {
            std::cerr << "Error: failed to open file \"" << out_file << "\" for writing.\n";
            exit(ERR_OPEN_FILE);
        }
        out << ":extrapreds (";
        for (unsigned i = 0; i < m_aux_preds.size(); ++i) {
            out << "(" << mk_pp(m_aux_preds[i].get(), m_mgr) << ") "; 
        }
        out << ")\n";
        for (unsigned i = 0; i < m_symmetry_breakers.size(); ++i) {
            out << ":assumption " << mk_pp(m_symmetry_breakers[i].get(), m_mgr) << "\n";
        }
        out.close();
    }


    void prove_with_symmetry_breakers() {
        front_end_params params;
        smt::context ctx(m_mgr, params);
        for (unsigned i = 0; i < m_formulas.size(); ++i) {
            ctx.assert_expr(m_formulas[i].get());
        }
        for (unsigned i = 0; i < m_symmetry_breakers.size(); ++i) {
            ctx.assert_expr(m_symmetry_breakers[i].get());
        }
        lbool result = ctx.setup_and_check();
        std::cout << result << "\n";
        ctx.display_statistics(std::cout);
    }

};
  
void tst_symmetry_parse(char** argv, int argc, int& i) {
    if (i+2 < argc) {
        char const* file_in   = argv[i+1];
        char const* file_tmp1 = "C:\\tmp\\bliss_in.txt";
        char const* file_tmp2 = "C:\\tmp\\bliss_out.txt";
        char const* file_out  = argv[i+2];
        expr_symmetry_graph graph;
        graph.parse_file(file_in, file_tmp1);
        graph.run_bliss(file_tmp1, file_tmp2);
        graph.parse_generators(file_tmp2);
        graph.print_symmetry_breakers(file_out);
        i += 2;
    }   
    else {
        std::cout << "usage <file_in>.smt <bliss_graph(out)> <bliss_result(out)> <file_out>.smt \n";
    }
}

void tst_symmetry_prove(char** argv, int argc, int& i) {
    if (i+1 < argc) {
        char const* file_in   = argv[i+1];
        char const* file_tmp1 = "C:\\tmp\\bliss_in.txt";
        char const* file_tmp2 = "C:\\tmp\\bliss_out.txt";
        expr_symmetry_graph graph;
        graph.parse_file(file_in, file_tmp1);
        graph.run_bliss(file_tmp1, file_tmp2);
        graph.parse_generators(file_tmp2);
        graph.prove_with_symmetry_breakers();
        i += 1;
    }   
    else {
        std::cout << "usage <file_in>.smt\n";
    }
}

void tst_symmetry() {
    char const* arg = "C:\\tvm\\src\\benchmarks\\zap\\smt-lib\\QF_IDL\\queens_bench\\toroidal_bench\\toroidal_queen2-1.smt";
    expr_symmetry_graph graph;
    graph.parse_file(arg, 0);
}
#else
void tst_symmetry_parse(char** argv, int argc, int& i) {
}

void tst_symmetry_prove(char** argv, int argc, int& i) {
}

void tst_symmetry() {
}
#endif
