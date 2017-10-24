/*++

Abstract: Pretty-printer for proofs in Graphviz format

--*/

#include "util/util.h"
#include "util/map.h"
#include "ast_pp_dot.h"

// string escaping for DOT
std::string escape_dot(std::string const & s) {
    std::string res;
    for (auto c : s) {
        if (c == '\n')
            res.append("\\l");
        else
            res.push_back(c);
    }
    return res;
}

// map from proofs to unique IDs
typedef map<const expr*, unsigned, obj_ptr_hash<const expr>, default_eq<const expr*> > expr2id;
typedef map<const expr*, bool, obj_ptr_hash<const expr>, default_eq<const expr*> > set_expr;

// temporary structure for traversing the proof and printing it
struct ast_pp_dot_st {
    const ast_pp_dot *      m_pp;
    set_expr                m_printed;
    expr2id                 m_id_map;
    svector<const expr *>   m_to_print;
    std::ostream &          m_out;
    unsigned                m_next_id;

    ast_pp_dot_st(const ast_pp_dot * pp, std::ostream & out) :
        m_pp(pp),
        m_out(out),
        m_next_id(0),
        m_id_map(),
        m_to_print(),
        m_printed() {}
    
    void push_term(const expr * a) { m_to_print.push_back(a); }        

    void pp_loop() {
        // DFS traversal
        auto& m = get_manager();
        while (!m_to_print.empty()) {
            const expr * a = m_to_print.back();
            m_to_print.pop_back();
            if (!m_printed.contains(a)) {
                m_printed.insert(a, true);
                if (m.is_proof(a))
                    pp_step(to_app(a));
                else
                    pp_atomic_step(a);
            }
        }
    }

private:

    ast_manager & get_manager() const { return m_pp->get_manager(); }

    // label for an expression
    std::string label_of_expr(const expr * e) const {
        expr_ref er((expr*)e, get_manager());
        std::ostringstream out;
        out << er << std::flush;
        return escape_dot(out.str());
    }

    void pp_atomic_step(const expr * e) {
        unsigned id = get_id(e);
        m_out << "node_" << id << " [shape=box,label=\"" << label_of_expr(e) << "\"] ;" << std::endl;
    }
    
    void pp_step(const proof * p) {
        auto m = get_manager();
        unsigned num_args = p->get_num_args();
        TRACE("pp_ast_dot_step", tout << " :kind " << p->get_kind() << " :num-args " << num_args);
        if (num_args > 0) {
            // print result
            expr* p_res = p->get_args()[num_args-1]; // result
            unsigned id = get_id(p);
            m_out << "node_" << id << " [shape=box,label=\"" << label_of_expr(p_res) << "\"]" << std::endl;
            // now print edges to parents (except last one, which is the result)
            std::string label = p->get_decl()->get_name().str();
            for (unsigned i = 0 ; i+1 < num_args; ++i) {
                expr* parent = p->get_args()[i];
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
        if (m_id_map.contains(e)) {
            return m_id_map[e];
        } else {
            auto id = m_next_id ++;
            m_id_map.insert(e, id);
            return id;
        }
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

