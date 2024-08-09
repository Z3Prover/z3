#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_clause.h"


namespace nlsat {
    class Simple_Checker {
        struct imp;
        imp *  m_imp;
    public:
        // Simple_Checker(solver &_sol, pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, clause_vector &_learned, const atom_vector &_atoms, const unsigned &_arith_var_num);
        Simple_Checker(pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, literal_vector &_learned_unit, const atom_vector &_atoms, const unsigned &_arith_var_num);
        ~Simple_Checker();
        bool operator()();
    };
}