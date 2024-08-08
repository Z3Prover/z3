#include "nlsat/nlsat_clause.h"

namespace nlsat {
    class Symmetry_Checker {
        struct imp;
        imp *  m_imp;
    public:
        // Simple_Checker(solver &_sol, pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, clause_vector &_learned, const atom_vector &_atoms, const unsigned &_arith_var_num);
        Symmetry_Checker(pmanager &_pm, unsynch_mpq_manager &_qm, const clause_vector &_clauses, const atom_vector &_atoms, const bool_vector &_is_int, const unsigned &_arith_var_num);
        ~Symmetry_Checker();
        bool check_symmetry(var x, var y);
    };
}