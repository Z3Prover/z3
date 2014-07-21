
namespace opt {
    class mus {
        struct imp;
        imp * m_imp;
    public:
        mus(solver& s, ast_manager& m);
        ~mus();
        /**
           Add soft constraint.

           Assume that the solver context enforces that 
           cls is equivalent to a disjunction of args.
           Assume also that cls is a literal.           
        */
        unsigned add_soft(expr* cls, unsigned sz, expr* const* args);
        
        lbool get_mus(unsigned_vector& mus);
    };

};
