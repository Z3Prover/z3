/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    datatype_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2017-9-1 

Revision History:

--*/

#include "util/warning.h"
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_translation.h"


namespace datatype {

    void accessor::fix_range(sort_ref_vector const& dts) {
        if (!m_range) {
            m_range = dts[m_index];
        }
    }

    func_decl_ref accessor::instantiate(sort_ref_vector const& ps) const {
        ast_manager& m = ps.get_manager();
        unsigned n = ps.size();
        SASSERT(m_range);
        SASSERT(n == get_def().params().size());
        sort_ref range(m.substitute(m_range, n, get_def().params().c_ptr(), ps.c_ptr()), m);
        sort_ref src(get_def().instantiate(ps));
        sort* srcs[1] = { src.get() };
        parameter pas[2] = { parameter(name()), parameter(get_constructor().name()) };
        return func_decl_ref(m.mk_func_decl(u().get_family_id(), OP_DT_ACCESSOR, 2, pas, 1, srcs, range), m);
    }

    func_decl_ref accessor::instantiate(sort* dt) const {
        sort_ref_vector sorts = get_def().u().datatype_params(dt);
        return instantiate(sorts);
    }

    def const& accessor::get_def() const { return m_constructor->get_def(); }
    util& accessor::u() const { return m_constructor->u(); }
    accessor* accessor::translate(ast_translation& tr) {
        return alloc(accessor, tr.to(), name(), to_sort(tr(m_range.get())));
    }

    constructor::~constructor() {
        for (accessor* a : m_accessors) dealloc(a);
        m_accessors.reset();
    }
    util& constructor::u() const { return m_def->u(); }

    func_decl_ref constructor::instantiate(sort_ref_vector const& ps) const {
        ast_manager& m = ps.get_manager();
        sort_ref_vector domain(m);
        for (accessor const* a : accessors()) {
            domain.push_back(a->instantiate(ps)->get_range());
        }
        sort_ref range = get_def().instantiate(ps);
        parameter pas[1] = { parameter(name()) };
        return func_decl_ref(m.mk_func_decl(u().get_family_id(), OP_DT_CONSTRUCTOR, 1, pas, domain.size(), domain.c_ptr(), range), m);        
    }

    func_decl_ref constructor::instantiate(sort* dt) const {
        sort_ref_vector sorts = get_def().u().datatype_params(dt);
        return instantiate(sorts);
    }

    constructor* constructor::translate(ast_translation& tr) {
        constructor* result = alloc(constructor, m_name, m_recognizer);
        for (accessor* a : *this) {
            result->add(a->translate(tr));
        }
        return result;
    }


    sort_ref def::instantiate(sort_ref_vector const& sorts) const {
        sort_ref s(m);
        TRACE("datatype", tout << "instantiate " << m_name << "\n";);
        if (!m_sort) {
            vector<parameter> ps;
            ps.push_back(parameter(m_name));
            for (sort * s : m_params) ps.push_back(parameter(s));
            m_sort = m.mk_sort(u().get_family_id(), DATATYPE_SORT, ps.size(), ps.c_ptr());
        }
        if (sorts.empty()) {
            return m_sort;
        }
        return sort_ref(m.substitute(m_sort, sorts.size(), m_params.c_ptr(), sorts.c_ptr()), m);
    }

    def* def::translate(ast_translation& tr, util& u) {
        SASSERT(&u.get_manager() == &tr.to());
        sort_ref_vector ps(tr.to());
        for (sort* p : m_params) {
            ps.push_back(to_sort(tr(p)));
        }
        def* result = alloc(def, tr.to(), u, m_name, m_class_id, ps.size(), ps.c_ptr());
        for (constructor* c : *this) {
            result->add(c->translate(tr));
        }
        if (m_sort) result->m_sort = to_sort(tr(m_sort.get()));
        return result;               
    }

    enum status {
        GRAY,
        BLACK
    };

    namespace param_size {
        void  size::dec_ref() { --m_ref; if (m_ref == 0) dealloc(this); }
        size* size::mk_offset(sort_size const& s) { return alloc(offset, s); }
        size* size::mk_param(sort_ref& p) { return alloc(sparam, p); }
        size* size::mk_plus(size* a1, size* a2) { return alloc(plus, a1, a2); }
        size* size::mk_times(size* a1, size* a2) { return alloc(times, a1, a2); }
        size* size::mk_times(ptr_vector<size>& szs) {
            if (szs.empty()) return mk_offset(sort_size(1));
            if (szs.size() == 1) return szs[0];
            size* r = szs[0];
            for (unsigned i = 1; i < szs.size(); ++i) {
                r = mk_times(r, szs[i]);
            }
            return r;
        }
        size* size::mk_plus(ptr_vector<size>& szs) {
            if (szs.empty()) return mk_offset(sort_size(0));
            if (szs.size() == 1) return szs[0];
            size* r = szs[0];
            for (unsigned i = 1; i < szs.size(); ++i) {
                r = mk_plus(r, szs[i]);
            }
            return r;
        }

        size* size::mk_power(size* a1, size* a2) { 
            return alloc(power, a1, a2); 
        }

        
        sort_size plus::eval(obj_map<sort, sort_size> const& S) {
            rational r(0);
            ptr_vector<size> todo;
            todo.push_back(m_arg1);
            todo.push_back(m_arg2);
            while (!todo.empty()) {
                size* s = todo.back();
                todo.pop_back();
                plus* p = dynamic_cast<plus*>(s);
                if (p) {
                    todo.push_back(p->m_arg1);
                    todo.push_back(p->m_arg2);
                }
                else {
                    sort_size sz = s->eval(S);                        
                    if (sz.is_infinite()) return sz;
                    if (sz.is_very_big()) return sz;
                    r += rational(sz.size(), rational::ui64());
                }
            }
            return sort_size(r);
        }

        size* plus::subst(obj_map<sort,size*>& S) { 
            return mk_plus(m_arg1->subst(S), m_arg2->subst(S)); 
        }

        sort_size times::eval(obj_map<sort, sort_size> const& S) {
            sort_size s1 = m_arg1->eval(S);
            sort_size s2 = m_arg2->eval(S);
            if (s1.is_infinite()) return s1;
            if (s2.is_infinite()) return s2;
            if (s1.is_very_big()) return s1;
            if (s2.is_very_big()) return s2;
            rational r = rational(s1.size(), rational::ui64()) * rational(s2.size(), rational::ui64());
            return sort_size(r);
        }

        size* times::subst(obj_map<sort,size*>& S) { 
            return mk_times(m_arg1->subst(S), m_arg2->subst(S)); 
        }

        sort_size power::eval(obj_map<sort, sort_size> const& S) {
            sort_size s1 = m_arg1->eval(S);
            sort_size s2 = m_arg2->eval(S);
            // s1^s2
            if (s1.is_infinite()) return s1;
            if (s2.is_infinite()) return s2;
            if (s1.is_very_big()) return s1;
            if (s2.is_very_big()) return s2;
            if (s1.size() == 1) return s1;
            if (s2.size() == 1) return s1;
            if (s1.size() > (2 << 20) || s2.size() > 10) return sort_size::mk_very_big();
            rational r = ::power(rational(s1.size(), rational::ui64()), static_cast<unsigned>(s2.size()));
            return sort_size(r);
        }

        size* power::subst(obj_map<sort,size*>& S) { 
            return mk_power(m_arg1->subst(S), m_arg2->subst(S)); 
        }

        size* sparam::subst(obj_map<sort, size*>& S) { 
            return S[m_param]; 
        }

    }

    namespace decl {

        plugin::~plugin() {
            finalize();
        }

        void plugin::finalize() {
            for (auto& kv : m_defs) {
                dealloc(kv.m_value);
            }
            m_defs.reset();
            m_util = nullptr; // force deletion
        }

        util & plugin::u() const {
            SASSERT(m_manager);
            SASSERT(m_family_id != null_family_id);
            if (m_util.get() == nullptr) {
                m_util = alloc(util, *m_manager);
            }
            return *(m_util.get());
        }

        void plugin::inherit(decl_plugin* other_p, ast_translation& tr) {
            plugin* p = dynamic_cast<plugin*>(other_p);
            svector<symbol> names;
            ptr_vector<def> new_defs;            
            SASSERT(p);
            for (auto& kv : p->m_defs) {
                def* d = kv.m_value;
                if (!m_defs.contains(kv.m_key)) {
                    names.push_back(kv.m_key);
                    new_defs.push_back(d->translate(tr, u()));
                }
            }
            for (def* d : new_defs) 
                m_defs.insert(d->name(), d);
            m_class_id = m_defs.size();
            u().compute_datatype_size_functions(names);
        }


        struct invalid_datatype {};

        sort * plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
            try {
                if (k != DATATYPE_SORT) {
                    TRACE("datatype", tout << "invalid kind parameter to datatype\n";);
                    throw invalid_datatype();
                }
                if (num_parameters < 1) {
                    TRACE("datatype", tout << "at least one parameter expected to datatype declaration\n";);
                    throw invalid_datatype();                    
                }
                parameter const & name = parameters[0];
                if (!name.is_symbol()) {
                    TRACE("datatype", tout << "expected symol parameter at position " << 0 << " got: " << name << "\n";);
                    throw invalid_datatype();
                }
                for (unsigned i = 1; i < num_parameters; ++i) {
                    parameter const& s = parameters[i];
                    if (!s.is_ast() || !is_sort(s.get_ast())) {
                        TRACE("datatype", tout << "expected sort parameter at position " << i << " got: " << s << "\n";);
                        throw invalid_datatype();
                    }
                }
                                
                sort* s = m_manager->mk_sort(name.get_symbol(),
                                             sort_info(m_family_id, k, num_parameters, parameters, true));
                def* d = nullptr;
                if (m_defs.find(s->get_name(), d) && d->sort_size()) {
                    obj_map<sort, sort_size> S;
                    for (unsigned i = 0; i + 1 < num_parameters; ++i) {
                        sort* r = to_sort(parameters[i + 1].get_ast());
                        TRACE("datatype", tout << "inserting " << mk_ismt2_pp(r, *m_manager) << " " << r->get_num_elements() << "\n";);
                        S.insert(d->params()[i], r->get_num_elements()); 
                    }
                    sort_size ts = d->sort_size()->eval(S);
                    TRACE("datatype", tout << name << " has size " << ts << "\n";);
                    s->set_num_elements(ts);
                }
                else {
                    TRACE("datatype", tout << "not setting size for " << name << "\n";);
                }
                return s;
            }
            catch (const invalid_datatype &) {
                m_manager->raise_exception("invalid datatype");
                return nullptr;
            }
        }

        func_decl * plugin::mk_update_field(
            unsigned num_parameters, parameter const * parameters, 
            unsigned arity, sort * const * domain, sort * range) {
            decl_kind k = OP_DT_UPDATE_FIELD;
            ast_manager& m = *m_manager;
            
            if (num_parameters != 1 || !parameters[0].is_ast()) {
                m.raise_exception("invalid parameters for datatype field update");
                return nullptr;
            }
            if (arity != 2) {
                m.raise_exception("invalid number of arguments for datatype field update");
                return nullptr;
            }
            func_decl* acc = nullptr;
            if (is_func_decl(parameters[0].get_ast())) {
                acc = to_func_decl(parameters[0].get_ast());
            }
            if (acc && !u().is_accessor(acc)) {
                acc = nullptr;
            }
            if (!acc) {
                m.raise_exception("datatype field update requires a datatype accessor as the second argument");
                return nullptr;
            }
            sort* dom = acc->get_domain(0);
            sort* rng = acc->get_range();
            if (dom != domain[0]) {
                m.raise_exception("first argument to field update should be a data-type");
                return nullptr;
            }
            if (rng != domain[1]) {
                std::ostringstream buffer;
                buffer << "second argument to field update should be " << mk_ismt2_pp(rng, m) 
                       << " instead of " << mk_ismt2_pp(domain[1], m);
                m.raise_exception(buffer.str());
                return nullptr;
            }
            range = domain[0];
            func_decl_info info(m_family_id, k, num_parameters, parameters);
            return m.mk_func_decl(symbol("update-field"), arity, domain, range, info);
        }

#define VALIDATE_PARAM(_pred_) if (!(_pred_)) m_manager->raise_exception("invalid parameter to datatype function "  #_pred_);
        
        func_decl * decl::plugin::mk_constructor(unsigned num_parameters, parameter const * parameters, 
                                                 unsigned arity, sort * const * domain, sort * range) {
            ast_manager& m = *m_manager;
            VALIDATE_PARAM(num_parameters == 1 && parameters[0].is_symbol() && range && u().is_datatype(range));
            // we blindly trust other conditions are met, including domain types.
            symbol name = parameters[0].get_symbol();
            func_decl_info info(m_family_id, OP_DT_CONSTRUCTOR, num_parameters, parameters);
            info.m_private_parameters = true;
            return m.mk_func_decl(name, arity, domain, range, info);
        }

        func_decl * decl::plugin::mk_recognizer(unsigned num_parameters, parameter const * parameters, 
                                                unsigned arity, sort * const * domain, sort *) {
            ast_manager& m = *m_manager;
            VALIDATE_PARAM(arity == 1 && num_parameters == 2 && parameters[1].is_symbol() && parameters[0].is_ast() && is_func_decl(parameters[0].get_ast()));
            VALIDATE_PARAM(u().is_datatype(domain[0]));
            // blindly trust that parameter is a constructor
            sort* range = m_manager->mk_bool_sort();
            func_decl_info info(m_family_id, OP_DT_RECOGNISER, num_parameters, parameters);
            info.m_private_parameters = true;
            return m.mk_func_decl(symbol(parameters[1].get_symbol()), arity, domain, range, info);
        }

        func_decl * decl::plugin::mk_is(unsigned num_parameters, parameter const * parameters, 
                                                unsigned arity, sort * const * domain, sort *) {
            ast_manager& m = *m_manager;
            VALIDATE_PARAM(arity == 1 && num_parameters == 1 && parameters[0].is_ast() && is_func_decl(parameters[0].get_ast()));
            VALIDATE_PARAM(u().is_datatype(domain[0]));
            // blindly trust that parameter is a constructor
            sort* range = m_manager->mk_bool_sort();
            func_decl_info info(m_family_id, OP_DT_IS, num_parameters, parameters);
            info.m_private_parameters = true;
            return m.mk_func_decl(symbol("is"), arity, domain, range, info);
        }

        func_decl * decl::plugin::mk_accessor(unsigned num_parameters, parameter const * parameters, 
                                              unsigned arity, sort * const * domain, sort * range) 
        {            
            ast_manager& m = *m_manager;
            VALIDATE_PARAM(arity == 1 && num_parameters == 2 && parameters[0].is_symbol() && parameters[1].is_symbol());
            VALIDATE_PARAM(u().is_datatype(domain[0]));
            SASSERT(range);
            func_decl_info info(m_family_id, OP_DT_ACCESSOR, num_parameters, parameters);
            info.m_private_parameters = true;
            symbol name = parameters[0].get_symbol();
            return m.mk_func_decl(name, arity, domain, range, info);           
        }

        func_decl * decl::plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                               unsigned arity, sort * const * domain, sort * range) {                        
            switch (k) {
            case OP_DT_CONSTRUCTOR:
                return mk_constructor(num_parameters, parameters, arity, domain, range);
            case OP_DT_RECOGNISER:
                return mk_recognizer(num_parameters, parameters, arity, domain, range);                
            case OP_DT_IS:
                return mk_is(num_parameters, parameters, arity, domain, range);                
            case OP_DT_ACCESSOR:
                return mk_accessor(num_parameters, parameters, arity, domain, range);                
            case OP_DT_UPDATE_FIELD: 
                return mk_update_field(num_parameters, parameters, arity, domain, range);
            default:
                m_manager->raise_exception("invalid datatype operator kind");
                return nullptr;
            }
        }

        def* plugin::mk(symbol const& name, unsigned n, sort * const * params) {
            ast_manager& m = *m_manager;
            return alloc(def, m, u(), name, m_class_id, n, params);
        }


        void plugin::end_def_block() {
            ast_manager& m = *m_manager;

            sort_ref_vector sorts(m);
            for (symbol const& s : m_def_block) {
                def const& d = *m_defs[s];
                sort_ref_vector ps(m);
                sorts.push_back(d.instantiate(ps));
            }
            for (symbol const& s : m_def_block) {
                def& d = *m_defs[s];
                for (constructor* c : d) {
                    for (accessor* a : *c) {
                        a->fix_range(sorts);
                    }
                }
            }
            if (!u().is_well_founded(sorts.size(), sorts.c_ptr())) {
                m_manager->raise_exception("datatype is not well-founded");
            }
            if (!u().is_covariant(sorts.size(), sorts.c_ptr())) {
                m_manager->raise_exception("datatype is not co-variant");
            }

            array_util autil(m);
            for (sort* s : sorts) {
                for (constructor const* c : get_def(s)) {
                    for (accessor const* a : *c) {
                        if (autil.is_array(a->range())) {
                            if (sorts.contains(get_array_range(a->range()))) {
                                m_has_nested_arrays = true;
                            }
                        }                    
                    }
                }
            }
            
            u().compute_datatype_size_functions(m_def_block);
            for (symbol const& s : m_def_block) {
                sort_ref_vector ps(m);
                m_defs[s]->instantiate(ps);
            }
        }

        void plugin::log_axiom_definitions(symbol const& s, sort * new_sort) {
            std::ostream& out = m_manager->trace_stream();
            symbol const& family_name = m_manager->get_family_name(get_family_id());
            for (constructor const* c : *m_defs[s]) {
                func_decl_ref f = c->instantiate(new_sort);
                const unsigned num_args = f->get_arity();
                if (num_args == 0) continue;

                // log constructor with quantified variables as arguments
                for (unsigned i = 0; i < num_args; ++i) {
                    out << "[mk-var] " << family_name << "#" << m_id_counter << " " << i << "\n";
                    ++m_id_counter;
                }
                const unsigned constructor_id = m_id_counter;
                out << "[mk-app] " << family_name << "#" << constructor_id << " " << f->get_name();
                for (unsigned i = 0; i < num_args; ++i) {
                    out << " " << family_name << "#" << constructor_id - num_args + i;
                }
                out << "\n";
                ++m_id_counter;

                // axioms for all accessors are generated when a constructor is applied => use constructor as pattern
                out << "[mk-app] " << family_name << "#" << m_id_counter << " pattern " << family_name << "#" << constructor_id << "\n";
                ++m_id_counter;
                m_axiom_bases.insert(f->get_name(), constructor_id + 4);
                std::ostringstream var_sorts;
                for (accessor const* a : *c) {
                    var_sorts << " (;" << a->range()->get_name() << ")";
                }
                std::string var_description = var_sorts.str();

                // create axioms: the ith accessor returns the ith argument of the constructor
                unsigned i = 0;
                for (accessor const* a : *c) {
                    func_decl_ref acc = a->instantiate(new_sort);
                    out << "[mk-app] " << family_name << "#" << m_id_counter << " " << acc->get_name() << " " << family_name << "#" << constructor_id << "\n";
                    ++m_id_counter;
                    out << "[mk-app] " << family_name << "#" << m_id_counter << " = " << family_name << "#" << constructor_id - num_args + i 
                        << " " << family_name << "#" << m_id_counter - 1 << "\n";
                    ++m_id_counter;
                    out << "[mk-quant] " << family_name << "#" << m_id_counter << " constructor_accessor_axiom " << num_args << " " << family_name
                        << "#" << constructor_id + 1 << " " << family_name << "#" << m_id_counter - 1 << "\n";
                    out << "[attach-var-names] " << family_name << "#" << m_id_counter << var_description << "\n";
                    ++m_id_counter;
                    ++i;
                }
            }
        }

        bool plugin::mk_datatypes(unsigned num_datatypes, def * const * datatypes, unsigned num_params, sort* const* sort_params, sort_ref_vector & new_sorts) {
            begin_def_block();
            for (unsigned i = 0; i < num_datatypes; ++i) {
                def* d = nullptr;
                TRACE("datatype", tout << "declaring " << datatypes[i]->name() << "\n";);
                if (m_defs.find(datatypes[i]->name(), d)) {
                    TRACE("datatype", tout << "delete previous version for " << datatypes[i]->name() << "\n";);
                    u().reset();
                    dealloc(d);
                }
                m_defs.insert(datatypes[i]->name(), datatypes[i]);
                m_def_block.push_back(datatypes[i]->name());
            }
            end_def_block();            
            sort_ref_vector ps(*m_manager);
            for (symbol const& s : m_def_block) {                
                new_sorts.push_back(m_defs[s]->instantiate(ps));
                if (m_manager->has_trace_stream()) {
                    log_axiom_definitions(s, new_sorts.back());
                }
            }
            return true;
        }

        void plugin::remove(symbol const& s) {
            def* d = nullptr;
            if (m_defs.find(s, d)) {
                dealloc(d);
            }
            m_defs.remove(s);
        }

        bool plugin::is_value_visit(expr * arg, ptr_buffer<app> & todo) const {
            if (!is_app(arg))
                return false;
            family_id fid = to_app(arg)->get_family_id();
            if (fid == m_family_id) {
                if (!u().is_constructor(to_app(arg)))
                    return false;
                if (to_app(arg)->get_num_args() == 0)
                    return true;
                todo.push_back(to_app(arg));
                return true;
            }
            else {
                return m_manager->is_value(arg);
            }
        }
        
        bool plugin::is_value(app * e) const {
            TRACE("dt_is_value", tout << "checking\n" << mk_ismt2_pp(e, *m_manager) << "\n";);
            if (!u().is_constructor(e))
                return false;
            if (e->get_num_args() == 0)
                return true;
            // REMARK: if the following check is too expensive, we should
            // cache the values in the decl::plugin.
            ptr_buffer<app> todo;
            // potentially expensive check for common sub-expressions.
            for (expr* arg : *e) {
                if (!is_value_visit(arg, todo)) {
                    TRACE("dt_is_value", tout << "not-value:\n" << mk_ismt2_pp(arg, *m_manager) << "\n";);
                    return false;
                }
            }
            while (!todo.empty()) {
                app * curr = todo.back();
                SASSERT(u().is_constructor(curr));
                todo.pop_back();
                for (expr* arg : *curr) {
                    if (!is_value_visit(arg, todo)) {
                        TRACE("dt_is_value", tout << "not-value:\n" << mk_ismt2_pp(arg, *m_manager) << "\n";);
                        return false;
                    }
                }
            }
            return true;
        }
        
        void plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
            op_names.push_back(builtin_name("is", OP_DT_IS));
            if (logic == symbol::null || logic == symbol("ALL")) {
                op_names.push_back(builtin_name("update-field", OP_DT_UPDATE_FIELD));
            }
        }

        expr * plugin::get_some_value(sort * s) {
            SASSERT(u().is_datatype(s));
            func_decl * c = u().get_non_rec_constructor(s);
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < c->get_arity(); i++) {
                args.push_back(m_manager->get_some_value(c->get_domain(i)));
            }
            return m_manager->mk_app(c, args.size(), args.c_ptr());
        }

        bool plugin::is_fully_interp(sort * s) const {
            return u().is_fully_interp(s);
        }
    }

    sort_ref_vector util::datatype_params(sort * s) const {
        SASSERT(is_datatype(s));
        sort_ref_vector result(m);
        for (unsigned i = 1; i < s->get_num_parameters(); ++i) {
            result.push_back(to_sort(s->get_parameter(i).get_ast()));
        }
        return result;
    }


    bool util::is_fully_interp(sort * s) const {
        SASSERT(is_datatype(s));
        bool fi = true;
        return fi;
        if (m_is_fully_interp.find(s, fi)) {
            return fi;
        }
        unsigned sz = m_fully_interp_trail.size();
        m_is_fully_interp.insert(s, true);
        def const& d = get_def(s);
        bool is_interp = true;
        m_fully_interp_trail.push_back(s);
        for (constructor const* c : d) {
            for (accessor const* a : *c) {
                func_decl_ref ac = a->instantiate(s);
                sort* r = ac->get_range();
                if (!m.is_fully_interp(r)) {
                    is_interp = false;
                    break;
                }
            }
            if (!is_interp) break;
        }
        for (unsigned i = sz; i < m_fully_interp_trail.size(); ++i) {
            m_is_fully_interp.remove(m_fully_interp_trail[i]);
        }
        m_fully_interp_trail.shrink(sz);
        m_is_fully_interp.insert(s, is_interp);
        m_asts.push_back(s);
        return true;
    }

    /**
       \brief Return true if the inductive datatype is recursive.
    */
    bool util::is_recursive_core(sort* s) const {
        obj_map<sort, status> already_found;
        ptr_vector<sort> todo, subsorts;
        todo.push_back(s);
        status st;
        while (!todo.empty()) {
            s = todo.back();
            if (already_found.find(s, st) && st == BLACK) {
                todo.pop_back();
                continue;
            }
            already_found.insert(s, GRAY);
            def const& d = get_def(s);
            bool can_process       = true;
            for (constructor const* c : d) {
                for (accessor const* a : *c) {
                    sort* d = a->range();
                    // check if d is a datatype sort
                    subsorts.reset();
                    get_subsorts(d, subsorts);
                    for (sort * s2 : subsorts) {
                        if (is_datatype(s2)) {
                            if (already_found.find(s2, st)) {
                                // type is recursive
                                if (st == GRAY) return true;
                            }
                            else {
                                todo.push_back(s2);
                                can_process = false;
                            }
                        }
                    }
                }
            }
            if (can_process) {
                already_found.insert(s, BLACK);
                todo.pop_back();
            }
        }
        return false;
    }

    unsigned util::get_datatype_num_parameter_sorts(sort * ty) {
        SASSERT(ty->get_num_parameters() >= 1);
        return ty->get_num_parameters() - 1;
    }

    sort* util::get_datatype_parameter_sort(sort * ty, unsigned idx) {
        SASSERT(idx < get_datatype_num_parameter_sorts(ty));
        return to_sort(ty->get_parameter(idx+1).get_ast());
    }

    param_size::size* util::get_sort_size(sort_ref_vector const& params, sort* s) {
        if (params.empty() && !is_datatype(s)) {
            return param_size::size::mk_offset(s->get_num_elements());
        }
        if (is_datatype(s)) {
            param_size::size* sz;
            obj_map<sort, param_size::size*> S;
            unsigned n = get_datatype_num_parameter_sorts(s);
            def & d = get_def(s->get_name());
            SASSERT(n == d.params().size());
            for (unsigned i = 0; i < n; ++i) {
                sort* ps = get_datatype_parameter_sort(s, i);
                sz = get_sort_size(params, ps);
                m_refs.push_back(sz);
                S.insert(d.params().get(i), sz); 
            }            
            auto ss = d.sort_size();
            if (!ss) {
                d.set_sort_size(param_size::size::mk_offset(sort_size::mk_infinite()));
                ss = d.sort_size();
            }
            return ss->subst(S);
        }
        array_util autil(m);
        if (autil.is_array(s)) {
            unsigned n = get_array_arity(s);
            ptr_vector<param_size::size> szs;
            for (unsigned i = 0; i < n; ++i) {
                szs.push_back(get_sort_size(params, get_array_domain(s, i)));
            }
            param_size::size* sz1 = param_size::size::mk_times(szs);
            param_size::size* sz2 = get_sort_size(params, get_array_range(s));
            return param_size::size::mk_power(sz2, sz1);
        }
        for (sort* p : params) {           
            if (s == p) {
                sort_ref sr(s, m);
                return param_size::size::mk_param(sr);
            }
        }
        return param_size::size::mk_offset(s->get_num_elements());        
    }

    bool util::is_declared(sort* s) const {
        return m_plugin->is_declared(s);
    }
    
    void util::compute_datatype_size_functions(svector<symbol> const& names) {
        map<symbol, status, symbol_hash_proc, symbol_eq_proc> already_found;
        map<symbol, param_size::size*, symbol_hash_proc, symbol_eq_proc> szs;

        TRACE("datatype", for (auto const& s : names) tout << s << " "; tout << "\n";);
        svector<symbol> todo(names);
        status st;
        while (!todo.empty()) {
            symbol s = todo.back();
            TRACE("datatype", tout << "Sort size for " << s << "\n";);

            if (already_found.find(s, st) && st == BLACK) {
                todo.pop_back();
                continue;
            }
            already_found.insert(s, GRAY);
            bool is_infinite = false;
            bool can_process = true;
            def& d = get_def(s);
            for (constructor const* c : d) {
                for (accessor const* a : *c) {
                    sort* r = a->range();
                    if (is_datatype(r)) {
                        symbol s2 = r->get_name();
                        if (already_found.find(s2, st)) {
                            // type is infinite
                            if (st == GRAY) {
                                is_infinite = true;
                            }
                        }
                        else if (names.contains(s2)) {
                            todo.push_back(s2);
                            can_process = false;
                        }
                    }
                }
            }
            if (!can_process) {
                continue;
            }
            todo.pop_back();
            already_found.insert(s, BLACK);
            if (is_infinite) {
                TRACE("datatype", tout << "infinite " << s << "\n";);
                d.set_sort_size(param_size::size::mk_offset(sort_size::mk_infinite()));
                continue;
            }

            ptr_vector<param_size::size> s_add;      
            for (constructor const* c : d) {
                ptr_vector<param_size::size> s_mul;
                for (accessor const* a : *c) {
                    s_mul.push_back(get_sort_size(d.params(), a->range()));
                }
                s_add.push_back(param_size::size::mk_times(s_mul));
            }
            TRACE("datatype", tout << "set sort size " << s << "\n";);
            d.set_sort_size(param_size::size::mk_plus(s_add));
            m_refs.reset();
        }
    }
    

    /**
       \brief Return true if the inductive datatype is well-founded.
       Pre-condition: The given argument constrains the parameters of an inductive datatype.
    */
    bool util::is_well_founded(unsigned num_types, sort* const* sorts) {
        buffer<bool> well_founded(num_types, false);
        obj_map<sort, unsigned> sort2id;
        for (unsigned i = 0; i < num_types; ++i) {
            sort2id.insert(sorts[i], i);
        }
        unsigned num_well_founded = 0, id = 0;
        bool changed;
        ptr_vector<sort> subsorts;
        do {
            changed = false;
            for (unsigned tid = 0; tid < num_types; tid++) {
                if (well_founded[tid]) {
                    continue;
                }
                sort* s = sorts[tid];
                def const& d = get_def(s);
                for (constructor const* c : d) {
                    for (accessor const* a : *c) {
                        subsorts.reset();
                        get_subsorts(a->range(), subsorts);
                        for (sort* srt : subsorts) {
                            if (sort2id.find(srt, id) && !well_founded[id]) {
                                goto next_constructor;
                            }
                        }
                    }
                    changed = true;
                    well_founded[tid] = true;
                    num_well_founded++;
                    break;
                next_constructor:
                    ;
                }
            }
        } 
        while (changed && num_well_founded < num_types);
        return num_well_founded == num_types;
    }

    /**
       \brief Return true if the inductive datatype is co-variant.
       Pre-condition: The given argument constrains the parameters of an inductive datatype.
    */
    bool util::is_covariant(unsigned num_types, sort* const* sorts) const {
        ast_mark mark;
        ptr_vector<sort> subsorts;

        for (unsigned tid = 0; tid < num_types; tid++) {
            mark.mark(sorts[tid], true);
        }
        
        for (unsigned tid = 0; tid < num_types; tid++) {
            sort* s = sorts[tid];
            def const& d = get_def(s);
            for (constructor const* c : d) {
                for (accessor const* a : *c) {
                    if (!is_covariant(mark, subsorts, a->range())) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    bool util::is_covariant(ast_mark& mark, ptr_vector<sort>& subsorts, sort* s) const {
        array_util autil(m);
        if (!autil.is_array(s)) {
            return true;
        }
        unsigned n = get_array_arity(s);
        subsorts.reset();
        for (unsigned i = 0; i < n; ++i) {
            get_subsorts(get_array_domain(s, i), subsorts);
        }
        if (!is_datatype(get_array_range(s))) {
            get_subsorts(get_array_range(s), subsorts);
        }
        for (sort* r : subsorts) {
            if (mark.is_marked(r)) return false;
        }
        return true;
    }

    def const& util::get_def(sort* s) const {
        return m_plugin->get_def(s);
    }

    void util::get_subsorts(sort* s, ptr_vector<sort>& sorts) const {
        sorts.push_back(s);
        for (parameter const& p : s->parameters()) {
            if (p.is_ast() && is_sort(p.get_ast())) {
                get_subsorts(to_sort(p.get_ast()), sorts);
            }
        }
    }


    util::util(ast_manager & m):
        m(m),
        m_family_id(m.mk_family_id("datatype")),
        m_asts(m),
        m_start(0) {
        m_plugin = dynamic_cast<decl::plugin*>(m.get_plugin(m_family_id));
        SASSERT(m_plugin);
    }

    util::~util() {
        std::for_each(m_vectors.begin(), m_vectors.end(), delete_proc<ptr_vector<func_decl> >());
    }

    ptr_vector<func_decl> const * util::get_datatype_constructors(sort * ty) {
        SASSERT(is_datatype(ty));
        ptr_vector<func_decl> * r = nullptr;
        if (m_datatype2constructors.find(ty, r))
            return r;
        r = alloc(ptr_vector<func_decl>);
        m_asts.push_back(ty);
        m_vectors.push_back(r);
        m_datatype2constructors.insert(ty, r);
        def const& d = get_def(ty);
        for (constructor const* c : d) {
            func_decl_ref f = c->instantiate(ty);
            m_asts.push_back(f);
            r->push_back(f);
        }
        return r;
    }

    ptr_vector<func_decl> const * util::get_constructor_accessors(func_decl * con) {
        SASSERT(is_constructor(con));
        ptr_vector<func_decl> * res = nullptr;
        if (m_constructor2accessors.find(con, res)) {
            return res;
        }
        res = alloc(ptr_vector<func_decl>);
        m_asts.push_back(con);
        m_vectors.push_back(res);
        m_constructor2accessors.insert(con, res);
        sort * datatype = con->get_range();
        def const& d = get_def(datatype);
        for (constructor const* c : d) {
            if (c->name() == con->get_name()) {
                for (accessor const* a : *c) {
                    func_decl_ref fn = a->instantiate(datatype);
                    res->push_back(fn);
                    m_asts.push_back(fn);
                }
                break;
            }
        }
        return res;
    }


    func_decl * util::get_constructor_is(func_decl * con) {
        SASSERT(is_constructor(con));
        sort * datatype = con->get_range();
        parameter ps[1] = { parameter(con)};
        return m.mk_func_decl(m_family_id, OP_DT_IS, 1, ps, 1, &datatype);
    }

    func_decl * util::get_constructor_recognizer(func_decl * con) {
        SASSERT(is_constructor(con));
        func_decl * d = nullptr;
        if (m_constructor2recognizer.find(con, d))
            return d;
        sort * datatype = con->get_range();
        def const& dd = get_def(datatype);
        symbol r;
        for (constructor const* c : dd) {
            if (c->name() == con->get_name()) {
                r = c->recognizer();
            }
        }
        parameter ps[2] = { parameter(con), parameter(r) };
        d  = m.mk_func_decl(m_family_id, OP_DT_RECOGNISER, 2, ps, 1, &datatype);
        SASSERT(d);
        m_asts.push_back(con);
        m_asts.push_back(d);
        m_constructor2recognizer.insert(con, d);
        return d;
    }

    app* util::mk_is(func_decl * c, expr *f) {
        return m.mk_app(get_constructor_is(c), 1, &f);
    }

    func_decl * util::get_recognizer_constructor(func_decl * recognizer) const {
        SASSERT(is_recognizer(recognizer));
        return to_func_decl(recognizer->get_parameter(0).get_ast());
    }

    func_decl * util::get_update_accessor(func_decl * updt) const {
        SASSERT(is_update_field(updt));
        return to_func_decl(updt->get_parameter(0).get_ast());
    }

    bool util::is_recursive(sort * ty) {
        SASSERT(is_datatype(ty));
        bool r = false;
        if (!m_is_recursive.find(ty, r)) {
            r = is_recursive_core(ty);
            m_is_recursive.insert(ty, r);
            m_asts.push_back(ty);
        }
        return r;
    }

    bool util::is_enum_sort(sort* s) {
        if (!is_datatype(s)) {
            return false;
        }
        bool r = false;
        if (m_is_enum.find(s, r))
            return r;
        ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
        r = true;
        for (unsigned i = 0; r && i < cnstrs.size(); ++i) {
            r = cnstrs[i]->get_arity() == 0;
        }
        m_is_enum.insert(s, r);
        m_asts.push_back(s);
        return r;
    }

    func_decl * util::get_accessor_constructor(func_decl * accessor) { 
        SASSERT(is_accessor(accessor));
        func_decl * r = nullptr;
        if (m_accessor2constructor.find(accessor, r))
            return r;
        sort * datatype = accessor->get_domain(0);
        symbol c_id   = accessor->get_parameter(1).get_symbol();
        def const& d = get_def(datatype);
        func_decl_ref fn(m);
        for (constructor const* c : d) {
            if (c->name() == c_id) {
                fn = c->instantiate(datatype);
                break;
            }
        }
        r = fn;
        m_accessor2constructor.insert(accessor, r);
        m_asts.push_back(accessor);
        m_asts.push_back(r);
        return r;
    }


    void util::reset() {
        m_datatype2constructors.reset();
        m_datatype2nonrec_constructor.reset();
        m_constructor2accessors.reset();
        m_constructor2recognizer.reset();
        m_recognizer2constructor.reset();
        m_accessor2constructor.reset();
        m_is_recursive.reset();
        m_is_enum.reset();
        std::for_each(m_vectors.begin(), m_vectors.end(), delete_proc<ptr_vector<func_decl> >());
        m_vectors.reset();
        m_asts.reset();
        ++m_start;
    }


    /**
       \brief Return a constructor mk(T_1, ... T_n)
       where each T_i is not a datatype or it is a datatype that contains 
       a constructor that will not contain directly or indirectly an element of the given sort.
    */
    func_decl * util::get_non_rec_constructor(sort * ty) {
        SASSERT(is_datatype(ty));
        func_decl * r = nullptr;
        if (m_datatype2nonrec_constructor.find(ty, r))
            return r;
        r = nullptr;
        ptr_vector<sort> forbidden_set;
        forbidden_set.push_back(ty);
        TRACE("util_bug", tout << "invoke get-non-rec: " << sort_ref(ty, m) << "\n";);
        r = get_non_rec_constructor_core(ty, forbidden_set);
        SASSERT(forbidden_set.back() == ty);
        SASSERT(r);
        m_asts.push_back(ty);
        m_asts.push_back(r);
        m_datatype2nonrec_constructor.insert(ty, r);
        return r;
    }

    /**
       \brief Return a constructor mk(T_1, ..., T_n) where
       each T_i is not a datatype or it is a datatype t not in forbidden_set,
       and get_non_rec_constructor_core(T_i, forbidden_set union { T_i })
    */
    func_decl * util::get_non_rec_constructor_core(sort * ty, ptr_vector<sort> & forbidden_set) {
        // We must select a constructor c(T_1, ..., T_n):T such that
        //   1) T_i's are not recursive
        // If there is no such constructor, then we select one that 
        //   2) each type T_i is not recursive or contains a constructor that does not depend on T

        ptr_vector<func_decl> const& constructors = *get_datatype_constructors(ty);
        unsigned sz = constructors.size();
        array_util autil(m);
        TRACE("util_bug", tout << "get-non-rec constructor: " << sort_ref(ty, m) << "\n";
              tout << "forbidden: ";
              for (sort* s : forbidden_set) tout << sort_ref(s, m) << " ";
              tout << "\n";
              tout << "constructors: " << sz << "\n";
              for (func_decl* f : constructors) tout << func_decl_ref(f, m) << "\n";
              );
        // step 1)
        unsigned start = ++m_start;
        for (unsigned j = 0; j < sz; ++j) {        
            func_decl * c = constructors[(j + start) % sz];
            TRACE("util_bug", tout << "checking " << sort_ref(ty, m) << ": " << func_decl_ref(c, m) << "\n";);
            unsigned num_args = c->get_arity();
            unsigned i = 0;
            for (; i < num_args && !is_datatype(autil.get_array_range_rec(c->get_domain(i))); i++);
            if (i == num_args) {
                TRACE("util_bug", tout << "found non-rec " << func_decl_ref(c, m) << "\n";);
                return c;
            }
        }
        // step 2)
        for (unsigned j = 0; j < sz; ++j) {        
            func_decl * c = constructors[(j + start) % sz];
            TRACE("util_bug", tout << "non_rec_constructor c: " << j << " " << func_decl_ref(c, m) << "\n";);
            unsigned num_args = c->get_arity();
            unsigned i = 0;
            for (; i < num_args; i++) {
                sort * T_i = autil.get_array_range_rec(c->get_domain(i));
                TRACE("util_bug", tout << "c: " << i << " " << sort_ref(T_i, m) << "\n";);
                if (!is_datatype(T_i)) {
                    TRACE("util_bug", tout << sort_ref(T_i, m) << " is not a datatype\n";);
                    continue;
                }
                if (std::find(forbidden_set.begin(), forbidden_set.end(), T_i) != forbidden_set.end()) {
                    TRACE("util_bug", tout << sort_ref(T_i, m) << " is in forbidden_set\n";);
                    break;
                }
                forbidden_set.push_back(T_i);
                func_decl * nested_c = get_non_rec_constructor_core(T_i, forbidden_set);
                SASSERT(forbidden_set.back() == T_i);
                forbidden_set.pop_back();
                if (nested_c == nullptr)
                    break;
                TRACE("util_bug", tout << "nested_c: " << nested_c->get_name() << "\n";);
            }
            if (i == num_args)
                return c;
        }
        return nullptr;
    }

    unsigned util::get_constructor_idx(func_decl * f) const {
        unsigned idx = 0;
        def const& d = get_def(f->get_range());
        for (constructor* c : d) {
            if (c->name() == f->get_name()) {
                return idx;
            }
            ++idx;
        }
        UNREACHABLE();
        return 0;
    }

    unsigned util::get_recognizer_constructor_idx(func_decl * f) const {
        return get_constructor_idx(get_recognizer_constructor(f));
    }

    /**
       \brief Two datatype sorts s1 and s2 are siblings if they were
       defined together in the same mutually recursive definition.
    */
    bool util::are_siblings(sort * s1, sort * s2) {
        if (!is_datatype(s1) || !is_datatype(s2)) {
            return s1 == s2;
        }
        else {
            return get_def(s1).id() == get_def(s2).id();
        }
    }

    unsigned util::get_datatype_num_constructors(sort * ty) {
        def const& d = get_def(ty->get_name());
        return d.constructors().size();
    }

    void util::get_defs(sort* s0, ptr_vector<def>& defs) {
        svector<symbol> mark;
        ptr_buffer<sort> todo;
        todo.push_back(s0);
        mark.push_back(s0->get_name());
        while (!todo.empty()) {
            sort* s = todo.back();
            todo.pop_back();
            defs.push_back(&m_plugin->get_def(s->get_name()));
            def const& d = get_def(s);
            for (constructor* c : d) {
                for (accessor* a : *c) {
                    sort* s = a->range();
                    if (are_siblings(s0, s) && !mark.contains(s->get_name())) {
                        mark.push_back(s->get_name());
                        todo.push_back(s);
                    }
                }
            }
        }
    }

    void util::display_datatype(sort *s0, std::ostream& out) {
        ast_mark mark;
        ptr_buffer<sort> todo;
        SASSERT(is_datatype(s0));
        out << s0->get_name() << " where\n";
        todo.push_back(s0);
        mark.mark(s0, true);
        while (!todo.empty()) {
            sort* s = todo.back();
            todo.pop_back();
            out << s->get_name() << " =\n";
            ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
            for (func_decl * cns : cnstrs) {
                out << "  " << cns->get_name() << " :: ";
                ptr_vector<func_decl> const & accs = *get_constructor_accessors(cns);
                for (func_decl* acc : accs) {
                    sort* s1 = acc->get_range();
                    out << "(" << acc->get_name() << ": " << s1->get_name() << ") "; 
                    if (is_datatype(s1) && are_siblings(s1, s0) && !mark.is_marked(s1)) {
                        mark.mark(s1, true);
                        todo.push_back(s1);
                    }          
                }
                out << "\n";
            }
        }
    }

    sort_ref util::mk_list_datatype(sort* elem, symbol const& name, 
                                    func_decl_ref& cons, func_decl_ref& is_cons, 
                                    func_decl_ref& hd, func_decl_ref& tl, 
                                    func_decl_ref& nil, func_decl_ref& is_nil) {

        accessor_decl* head_tail[2] = {
            mk_accessor_decl(m, symbol("head"), type_ref(elem)),
            mk_accessor_decl(m, symbol("tail"), type_ref(0))
        };
        constructor_decl* constrs[2] = {
            mk_constructor_decl(symbol("nil"), symbol("is_nil"), 0, nullptr),
            mk_constructor_decl(symbol("cons"), symbol("is_cons"), 2, head_tail)
        };
        decl::plugin& p = *get_plugin();

        sort_ref_vector sorts(m);
        datatype_decl * decl = mk_datatype_decl(*this, name, 0, nullptr, 2, constrs);
        bool is_ok = p.mk_datatypes(1, &decl, 0, nullptr, sorts);
        del_datatype_decl(decl);
        
        if (!is_ok) {
            return sort_ref(m);
        }
        sort* s = sorts.get(0);
        ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
        SASSERT(cnstrs.size() == 2);
        nil = cnstrs[0];
        is_nil = get_constructor_is(cnstrs[0]);
        cons = cnstrs[1];
        is_cons = get_constructor_is(cnstrs[1]);
        ptr_vector<func_decl> const& acc = *get_constructor_accessors(cnstrs[1]);
        SASSERT(acc.size() == 2);
        hd = acc[0];
        tl = acc[1];
        return sort_ref(s, m);
    }

    sort_ref util::mk_pair_datatype(sort* a, sort* b, func_decl_ref& fst, func_decl_ref& snd, func_decl_ref& pair) {
        type_ref t1(a), t2(b);
        accessor_decl* fstd = mk_accessor_decl(m, symbol("fst"), t1);
        accessor_decl* sndd = mk_accessor_decl(m, symbol("snd"), t2);
        accessor_decl* accd[2] = { fstd, sndd };
        auto * p = mk_constructor_decl(symbol("pair"), symbol("is-pair"), 2, accd);
        auto* dt = mk_datatype_decl(*this, symbol("pair"), 0, nullptr, 1, &p);
        sort_ref_vector sorts(m);
        VERIFY(get_plugin()->mk_datatypes(1, &dt, 0, nullptr, sorts));
        del_datatype_decl(dt);
        sort* s = sorts.get(0);
        ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
        SASSERT(cnstrs.size() == 1);
        ptr_vector<func_decl> const& acc = *get_constructor_accessors(cnstrs[0]);
        SASSERT(acc.size() == 2);
        fst = acc[0];
        snd = acc[1];
        pair = cnstrs[0];
        return sort_ref(s, m);
    }

    sort_ref util::mk_tuple_datatype(svector<std::pair<symbol, sort*>> const& elems, symbol const& name, symbol const& test, func_decl_ref& tup, func_decl_ref_vector& accs) {
        ptr_vector<accessor_decl> accd;
        for (auto const& e : elems) {
            type_ref t(e.second);
            accd.push_back(mk_accessor_decl(m, e.first, t));
        }
        auto* tuple = mk_constructor_decl(name, test, accd.size(), accd.c_ptr());
        auto* dt = mk_datatype_decl(*this, name, 0, nullptr, 1, &tuple);
        sort_ref_vector sorts(m);
        VERIFY(get_plugin()->mk_datatypes(1, &dt, 0, nullptr, sorts));
        del_datatype_decl(dt);
        sort* s = sorts.get(0);
        ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
        SASSERT(cnstrs.size() == 1);
        ptr_vector<func_decl> const& acc = *get_constructor_accessors(cnstrs[0]);
        for (auto* f : acc) accs.push_back(f);
        tup = cnstrs[0];
        return sort_ref(s, m);
    }

}

datatype_decl * mk_datatype_decl(datatype_util& u, symbol const & n, unsigned num_params, sort*const* params, unsigned num_constructors, constructor_decl * const * cs) {
    datatype::decl::plugin* p = u.get_plugin();
    datatype::def* d = p->mk(n, num_params, params);
    for (unsigned i = 0; i < num_constructors; ++i) {
        d->add(cs[i]);
    }
    return d;
}
