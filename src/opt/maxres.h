
namespace opt {
    class maxres : public maxsmt_solver {
        struct imp;
        imp* m_imp;
    public:
        maxres(ast_manager& m, solver& s, expr_ref_vector& soft_constraints);
        ~maxres();
        virtual lbool operator()();
        virtual rational get_lower() const;
        virtual rational get_upper() const;
        virtual bool get_assignment(unsigned index) const;
        virtual void set_cancel(bool f);
        virtual void collect_statistics(statistics& st) const;
        virtual void get_model(model_ref& mdl);
        virtual void updt_params(params_ref& p);
    };
};
