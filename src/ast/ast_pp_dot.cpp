/*++

Abstract: Pretty-printer for proofs in Graphviz format

--*/

#include "util/util.h"
#include "util/map.h"
#include "ast/ast_pp_dot.h"

// string escaping for DOT
std::string escape_dot(const std::string &s)
{
    std::string res;
    res.reserve(s.size()); // preallocate
    for (auto c : s) {
        if (c == '\n')
            res.append("\\l");
        else
            res.push_back(c);
    }
    return res;
}

// map from proofs to unique IDs
typedef obj_map<const expr, unsigned> expr2id;

// temporary structure for traversing the proof and printing it
struct ast_pp_dot_st {
    ast_manager &           m_manager;
    std::ostream &          m_out;
    const ast_pp_dot *      m_pp;
    unsigned                m_next_id;
    expr2id                 m_id_map;
    obj_hashtable<const expr>     m_printed;
    svector<const expr *>   m_to_print;
    bool                    m_first;

    ast_pp_dot_st(const ast_pp_dot * pp, std::ostream & out) :
        m_manager(pp->get_manager()),
        m_out(out),
        m_pp(pp),
        m_next_id(0),
        m_id_map(),
        m_printed(),
        m_to_print(),
        m_first(true) {}

    ~ast_pp_dot_st() {};
    
    void push_term(const expr * a) { m_to_print.push_back(a); }        

    void pp_loop() {
        // DFS traversal
        while (!m_to_print.empty()) {
            const expr * a = m_to_print.back();
            m_to_print.pop_back();
            if (!m_printed.contains(a)) {
                m_printed.insert(a);
                if (m().is_proof(a))
                    pp_step(to_app(a));
                else
                    pp_atomic_step(a);
            }
        }
    }

private:

    inline ast_manager & m() const { return m_manager; }

    // label for an expression
    std::string label_of_expr(const expr * e) const {
        expr_ref er((expr*)e, m());
        std::ostringstream out;
        out << er << std::flush;
        return escape_dot(out.str());
    }

    void pp_atomic_step(const expr * e) {
        unsigned id = get_id(e);
        m_out << "node_" << id << " [shape=box,color=\"yellow\",style=\"filled\",label=\"" << label_of_expr(e) << "\"] ;" << std::endl;
    }
    
    void pp_step(const proof * p) {
        TRACE("pp_ast_dot_step", tout << " :kind " << p->get_kind() << " :num-args " << p->get_num_args() << "\n";);
        if (m().has_fact(p)) {
            // print result
            expr* p_res = m().get_fact(p); // result of proof step
            unsigned id = get_id(p);
            unsigned num_parents = m().get_num_parents(p);
            const char* color =
                m_first ? (m_first=false,"color=\"red\"") : num_parents==0 ? "color=\"yellow\"": "";
            m_out << "node_" << id <<
                " [shape=box,style=\"filled\",label=\"" << label_of_expr(p_res) << "\""
                << color << "]" << std::endl;
            // now print edges to parents (except last one, which is the result)
            std::string label = p->get_decl()->get_name().str();
            for (unsigned i = 0 ; i < num_parents; ++i) {
                expr* parent = m().get_parent(p, i);
                // explore parent, also print a link to it
                push_term(to_app(parent));
                m_out << "node_" << id << " -> " << "node_" << get_id((expr*)parent)
                    << "[label=\"" << label << "\"];" << std::endl;;
            }
        } else {
            pp_atomic_step(p);
        }
    }

    // find a unique ID for this proof
    unsigned get_id(const expr * e) {
        unsigned id = 0;
        if (!m_id_map.find(e, id)) {
             id = m_next_id++;
             m_id_map.insert(e, id);
        }
        return id;
    }

};

// main printer
std::ostream & ast_pp_dot::pp(std::ostream & out) const {
    out << "digraph proof { " << std::endl;
    ast_pp_dot_st pp_st(this, out);
    pp_st.push_term(m_pr);
    pp_st.pp_loop();
    out << std::endl << " } " << std::endl << std::flush;
    return out;
}

std::ostream &operator<<(std::ostream &out, const ast_pp_dot & p) { return p.pp(out); }

