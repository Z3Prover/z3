#ifndef IUC_PROOF_H_
#define IUC_PROOF_H_

#include "ast/ast.h"

namespace spacer {
    typedef obj_hashtable<expr> expr_set;
    typedef obj_hashtable<func_decl> func_decl_set;

    /*
     * an iuc_proof is a proof together with information of the coloring of the axioms.
     */
    class iuc_proof
    {
    public:
        
        iuc_proof(ast_manager& m, proof* pr, expr_set& b_conjuncts);
        
        proof* get();

        /*
         * returns whether symbol contains only symbols which occur in B.
         */
        bool only_contains_symbols_b(expr* expr) const;

        bool is_a_marked(proof* p);
        bool is_b_marked(proof* p);
        bool is_h_marked(proof* p);

        bool is_b_pure (proof *p)
        {return !is_h_marked (p) && only_contains_symbols_b (m.get_fact (p));}

        /*
         * print dot-representation to file proof.dot
         * use Graphviz's dot with option -Tpdf to convert dot-representation into pdf
         */
        void pp_dot();
        
        void print_farkas_stats();
    private:
        ast_manager& m;
        proof_ref m_pr;
        
        ast_mark m_a_mark;
        ast_mark m_b_mark;
        ast_mark m_h_mark;
        
        func_decl_set m_symbols_b; // symbols, which occur in any b-asserted formula

        // collect symbols occuring in B
        void collect_symbols_b(expr_set& b_conjuncts);

        // compute for each formula of the proof whether it derives from A and whether it derives from B
        void compute_marks(expr_set& b_conjuncts);
        
        void pp_dot_to_stream(std::ofstream& dotstream);
        std::string escape_dot(const std::string &s);
        
        void post_process_dot(std::string dot_filepath, std::ofstream& dotstream);
    };
    
    
}

#endif /* IUC_PROOF_H_ */
