/**

output     :: derivation model

derivation :: "(" "derivation" step* ")"

step       :: "(" "step" step-name fact rule-name subst labels premises ")"

step-name  :: identifier

rule-name  :: identifier

fact       :: "(" predicate theory-term* ")"

subst      :: "(" "subst" assignment* ")"

assignment :: "(" "=" variable theory-term ")"

labels     :: "(" "labels" label* ")"

premises   :: "(" "ref" step-name* ")"

model      :: "(" "model" smtlib2-model ")"

In each step the "fact" is derivable by hyper-resolution from the named 
premises and the named rule, under the given substitution for the 
universally quantified variables in the rule. The premises of each 
step must have occurred previously in the step sequence. The last fact 
is a nullary placeholder predicate representing satisfaction of the query 
(its name is arbitrary).

The labels list consists of all the positively labeled sub-formulas whose 
truth is used in the proof, and all the negatively labeled formulas whose 
negation is used. A theory-term is a ground term using only interpreted 
constants of the background theories.

The smtlib2-model gives an interpretation of the uninterpreted constants 
in the background theory under which the derivation is valid. Currently 
it is a quoted string in the old z3 model format, for compatibility with 
Boogie, however, this should be changed to the new model format (using 
define-fun) when Boogie supports this.

*/

#include "ast.h"
#include "model.h"

namespace datalog {
    class boogie_proof {
        typedef vector<std::pair<symbol,expr*> > subst;
        typedef svector<symbol> labels;
        typedef unsigned_vector  refs;
        struct step {
            symbol m_rule_name;
            expr*  m_fact;
            subst  m_subst;
            labels m_labels;
            refs   m_refs;
        };

        ast_manager& m;
        proof_ref    m_proof;
        model_ref    m_model;

        void pp_proof(std::ostream& out);
        void pp_steps(std::ostream& out, vector<step>& steps);
        void pp_step(std::ostream& out, unsigned i, step& s);
        void pp_fact(std::ostream& out, expr* fact);
        void pp_subst(std::ostream& out, subst& s);
        void pp_assignment(std::ostream& out, symbol const& v, expr* t);
        void pp_labels(std::ostream& out, labels& lbls);
        void pp_premises(std::ostream& out, refs& refs);

        void get_subst(proof* p, subst& sub);
        void get_rule_name(proof* p, symbol&);
        void get_labels(proof* p, labels&);

    public:
        boogie_proof(ast_manager& m): m(m), m_proof(m), m_model(0) {}
        
        void set_proof(proof* p);
        
        void set_model(model* m);

        void pp(std::ostream& out);
    };
}
