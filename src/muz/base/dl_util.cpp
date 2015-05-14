/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_util.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-20.

Revision History:

--*/

#include <sstream>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef _WINDOWS
#include <windows.h>
#endif
#include"ast_pp.h"
#include"bool_rewriter.h"
#include"for_each_expr.h"
#include"scoped_proof.h"
#include"dl_context.h"
#include"dl_rule.h"
#include"dl_util.h"
#include"stopwatch.h"

namespace datalog {

    verbose_action::verbose_action(char const* msg, unsigned lvl): m_lvl(lvl), m_sw(0) {
        IF_VERBOSE(m_lvl, 
                   (verbose_stream() << msg << "...").flush(); 
                   m_sw = alloc(stopwatch); 
                   m_sw->start(););
    }

    verbose_action::~verbose_action() {
        double sec = 0.0;
        if (m_sw) m_sw->stop();
        sec = m_sw?m_sw->get_seconds():0.0;
        if (sec < 0.001) sec = 0.0;
        IF_VERBOSE(m_lvl, 
                   (verbose_stream() << sec << "s\n").flush();
                   );
        dealloc(m_sw);
    }




    bool contains_var(expr * trm, unsigned var_idx) {
        expr_free_vars fv;
        fv(trm);
        return fv.contains(var_idx);
    }
    
    unsigned count_variable_arguments(app * pred)
    {
        SASSERT(is_uninterp(pred));
        unsigned res = 0;
        unsigned n = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = pred->get_arg(i);
            if (is_var(arg)) {
                res++;
            }
        }
        return res;
    }

    void mk_new_rule_tail(ast_manager & m, app * pred, var_idx_set const & non_local_vars, unsigned & next_idx, varidx2var_map & varidx2var, 
                          sort_ref_buffer & new_rule_domain, expr_ref_buffer & new_rule_args, app_ref & new_pred) {
        expr_ref_buffer new_args(m);
        unsigned n  = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = pred->get_arg(i);
            if (m.is_value(arg)) {
                new_args.push_back(arg);
            }
            else {
                SASSERT(is_var(arg));
                int vidx      = to_var(arg)->get_idx();
                var * new_var = 0;
                if (!varidx2var.find(vidx, new_var)) {
                    new_var = m.mk_var(next_idx, to_var(arg)->get_sort());
                    next_idx++;
                    varidx2var.insert(vidx, new_var);
                    if (non_local_vars.contains(vidx)) {
                        // other predicates used this variable... so it should be in the domain of the filter
                        new_rule_domain.push_back(to_var(arg)->get_sort());
                        new_rule_args.push_back(new_var);
                    }
                }
                SASSERT(new_var != 0);
                new_args.push_back(new_var);
            }
        }
        new_pred = m.mk_app(pred->get_decl(), new_args.size(), new_args.c_ptr());
    }

    void apply_subst(expr_ref_vector& tgt, expr_ref_vector const& sub) {
        ast_manager& m = tgt.get_manager();
        var_subst vs(m, false);
        expr_ref tmp(m);
        for (unsigned i = 0; i < tgt.size(); ++i) {
            if (tgt[i].get()) {
                vs(tgt[i].get(), sub.size(), sub.c_ptr(), tmp);
                tgt[i] = tmp;
            }
            else {
                tgt[i] = sub[i];
            }
        }
        for (unsigned i = tgt.size(); i < sub.size(); ++i) {
            tgt.push_back(sub[i]);
        }
    }


    void output_predicate(context & ctx, app * f, std::ostream & out)
    {
        func_decl * pred_decl = f->get_decl();
        unsigned arity = f->get_num_args();

        out << pred_decl->get_name() << '(';

        for (unsigned i = 0; i < arity; i++) {
            expr * arg = f->get_arg(i);
            if (i != 0) {
                out << ',';
            }
            if (is_var(arg)) {
                out << "#" << to_var(arg)->get_idx();
            }
            else {
                out << mk_pp(arg, ctx.get_manager());
            }
        }
        out << ")";
    }

    void display_predicate(context & ctx, app * f, std::ostream & out)
    {
        output_predicate(ctx, f, out);
        out << "\n";
    }

    void display_fact(context & ctx, app * f, std::ostream & out)
    {
        func_decl * pred_decl = f->get_decl();
        unsigned arity = f->get_num_args();

        out << "\t(";

        for(unsigned i = 0; i < arity; i++) {
            if (i != 0) {
                out << ',';
            }

            expr * arg = f->get_arg(i);
            uint64 sym_num;
            SASSERT(is_app(arg));
            VERIFY( ctx.get_decl_util().is_numeral_ext(to_app(arg), sym_num) );
            relation_sort sort = pred_decl->get_domain(i);            
            out << ctx.get_argument_name(pred_decl, i) << '=';
            ctx.print_constant_name(sort, sym_num, out);
            out << '(' << sym_num << ')';
        }
        out << ")\n";
    }

    void idx_set_union(idx_set & tgt, const idx_set & src) {
        idx_set::iterator vit = src.begin();
        idx_set::iterator vend = src.end();
        for(;vit!=vend;++vit) {
            tgt.insert(*vit);
        }
    }


    bool variable_intersection::values_match(const expr * v1, const expr * v2)
    {
        //return !m_manager.are_distinct(v1, v2);
        return v1==v2;
    }

    bool variable_intersection::args_match(const app * f1, const app * f2)
    {
        unsigned n=size();
        for (unsigned i = 0; i < n; i++) {
            unsigned f1_index, f2_index;
            get(i, f1_index, f2_index);
            if (!values_match(f1->get_arg(f1_index),f2->get_arg(f2_index))) {
                return false;
            }
        }
        return true;
    }

    bool variable_intersection::args_self_match(const app * f)
    {
        if(!args_match(f,f)) {
            return false;
        }

        unsigned n = m_const_indexes.size();
        for(unsigned i=0; i<n; i++) {
            unsigned f_index = m_const_indexes[i];
            if(!values_match(f->get_arg(f_index), m_consts[i].get())) {
                return false;
            }
        }
        return true;
    }

    void variable_intersection::populate_self(const app * a)
    {
        SASSERT(is_uninterp(a));

        //TODO: optimize quadratic complexity
        //TODO: optimize number of checks when variable occurs multiple times
        unsigned arity = a->get_num_args();
        for(unsigned i1=0; i1<arity; i1++) {
            expr * e1=a->get_arg(i1);
            if(is_var(e1)) {
                var* v1=to_var(e1);
                for(unsigned i2=i1+1; i2<arity; i2++) {
                    expr * e2=a->get_arg(i2);
                    if(!is_var(e2)) {
                        continue;
                    }
                    var* v2=to_var(e2);
                    if(v1->get_idx()==v2->get_idx()) {
                        add_pair(i1, i2);
                    }
                }
            }
            else {
                SASSERT(is_app(e1));
                app * c1 = to_app(e1);
                SASSERT(c1->get_num_args()==0); //c1 must be a constant

                m_const_indexes.push_back(i1);
                m_consts.push_back(c1);

                SASSERT(m_const_indexes.size()==m_consts.size());
            }
        }
    }

    
    void rule_counter::count_rule_vars(ast_manager & m, const rule * r, int coef) {
        reset();
        count_vars(m, r->get_head(), 1);
        unsigned n = r->get_tail_size();
        for (unsigned i = 0; i < n; i++) {
            count_vars(m, r->get_tail(i), coef);
        }
    }

    unsigned rule_counter::get_max_rule_var(const rule & r) {
        m_todo.push_back(r.get_head());
        m_scopes.push_back(0);
        unsigned n = r.get_tail_size();
        bool has_var = false;
        for (unsigned i = 0; i < n; i++) {
            m_todo.push_back(r.get_tail(i));
            m_scopes.push_back(0);
        }
        return get_max_var(has_var);
    }

    void del_rule(horn_subsume_model_converter* mc, rule& r) {
        if (mc) {
            ast_manager& m = mc->get_manager();
            expr_ref_vector body(m);
            for (unsigned i = 0; i < r.get_tail_size(); ++i) {
                if (r.is_neg_tail(i)) {
                    body.push_back(m.mk_not(r.get_tail(i)));
                }
                else {
                    body.push_back(r.get_tail(i));
                }
            }
            TRACE("dl_dr", 
                  tout << mk_pp(r.get_head(), m) << " :- \n";
                  for (unsigned i = 0; i < body.size(); ++i) {
                      tout << mk_pp(body[i].get(), m) << "\n";
                  });
                      
            mc->insert(r.get_head(), body.size(), body.c_ptr());
        }
    }


    void resolve_rule(rule_manager& rm,
                      replace_proof_converter* pc, rule const& r1, rule const& r2, unsigned idx, 
                      expr_ref_vector const& s1, expr_ref_vector const& s2, rule const& res) {
        if (!pc) return;
        ast_manager& m = s1.get_manager();
        expr_ref fml1(m), fml2(m), fml3(m);
        rm.to_formula(r1, fml1);
        rm.to_formula(r2, fml2);
        rm.to_formula(res, fml3);
        vector<expr_ref_vector> substs;
        svector<std::pair<unsigned, unsigned> > positions;
        substs.push_back(s1);
        substs.push_back(s2);

        scoped_proof _sc(m);
        proof_ref pr(m);
        proof_ref_vector premises(m);
        premises.push_back(m.mk_asserted(fml1));
        premises.push_back(m.mk_asserted(fml2));
        positions.push_back(std::make_pair(idx+1, 0));

        TRACE("dl", 
              tout << premises[0]->get_id() << " " << mk_pp(premises[0].get(), m) << "\n";
              for (unsigned i = 0; i < s1.size(); ++i) {
                  tout << mk_pp(s1[i], m) << " ";
              }
              tout << "\n";
              tout << premises[1]->get_id() << " " << mk_pp(premises[1].get(), m) << "\n";
              for (unsigned i = 0; i < s2.size(); ++i) {
                  tout << mk_pp(s2[i], m) << " ";
              }
              tout << "\n";
              ); 

        pr = m.mk_hyper_resolve(2, premises.c_ptr(), fml3, positions, substs);
        pc->insert(pr);
    }

    void resolve_rule(rule_manager& rm, rule const& r1, rule const& r2, unsigned idx, 
                      expr_ref_vector const& s1, expr_ref_vector const& s2, rule& res) {
        if (!r1.get_proof()) {
            return;
        }
        SASSERT(r2.get_proof());
        ast_manager& m = s1.get_manager();
        expr_ref fml(m);
        rm.to_formula(res, fml);
        vector<expr_ref_vector> substs;
        svector<std::pair<unsigned, unsigned> > positions;
        substs.push_back(s1);
        substs.push_back(s2);

        scoped_proof _sc(m);
        proof_ref pr(m);
        proof_ref_vector premises(m);
        premises.push_back(r1.get_proof());
        premises.push_back(r2.get_proof());
        positions.push_back(std::make_pair(idx+1, 0));

        TRACE("dl", 
              tout << premises[0]->get_id() << " " << mk_pp(premises[0].get(), m) << "\n";
              for (unsigned i = 0; i < s1.size(); ++i) {
                  tout << mk_pp(s1[i], m) << " ";
              }
              tout << "\n";
              tout << premises[1]->get_id() << " " << mk_pp(premises[1].get(), m) << "\n";
              for (unsigned i = 0; i < s2.size(); ++i) {
                  tout << mk_pp(s2[i], m) << " ";
              }
              tout << "\n";
              ); 

        pr = m.mk_hyper_resolve(2, premises.c_ptr(), fml, positions, substs);
        res.set_proof(m, pr);
    }

    class skip_model_converter : public model_converter {
    public:
        skip_model_converter() {}
 
        virtual model_converter * translate(ast_translation & translator) { 
            return alloc(skip_model_converter);
        }

    };

    model_converter* mk_skip_model_converter() { return alloc(skip_model_converter); }

    class skip_proof_converter : public proof_converter {
        virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
            SASSERT(num_source == 1);
            result = source[0];
        }

        virtual proof_converter * translate(ast_translation & translator) {
            return alloc(skip_proof_converter);
        }

    };

    proof_converter* mk_skip_proof_converter() { return alloc(skip_proof_converter); }



    void reverse_renaming(ast_manager & m, const expr_ref_vector & src, expr_ref_vector & tgt) {
        SASSERT(tgt.empty());
        unsigned src_sz = src.size();
        unsigned src_ofs = src_sz-1;

        unsigned max_var_idx = 0;
        for(unsigned i=0; i<src_sz; i++) {
            if(!src[i]) {
                continue;
            }
            SASSERT(is_var(src[i]));
            unsigned var_idx = to_var(src[i])->get_idx();
            if(var_idx>max_var_idx) {
                max_var_idx=var_idx;
            }
        }

        unsigned tgt_sz = max_var_idx+1;
        unsigned tgt_ofs = tgt_sz-1;
        tgt.resize(tgt_sz, 0);
        for(unsigned i=0; i<src_sz; i++) {
            expr * e = src[src_ofs-i];
            if(!e) {
                continue;
            }
            var * v = to_var(e);
            unsigned var_idx = v->get_idx();
            tgt[tgt_ofs-var_idx] = m.mk_var(i, v->get_sort());
        }
    }


    void print_renaming(const expr_ref_vector & cont, std::ostream & out) {
        unsigned len = cont.size();
        out << "(";
        for(int i=len-1; i>=0; i--) {
            out << (len-1-i) <<"->";
            if(cont.get(i)==0) {
                out << "{none}";
            }
            else {
                out << to_var(cont.get(i))->get_idx();
            }
            if(i!=0) { out << ","; }
        }
        out << ")\n";
    }

    void cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle) {
        try_remove_cycle_from_permutation(permutation, cycle);
        DEBUG_CODE(
            //here we assert that there is at most one cycle in the permutation
            unsigned_vector aux;
            SASSERT(!try_remove_cycle_from_permutation(permutation, aux));
            );
    }

    bool try_remove_cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle) {
        SASSERT(cycle.empty());
        DEBUG_CODE(
            counter ctr;
            ctr.count(permutation);
            SASSERT(permutation.empty() || ctr.get_max_positive()==permutation.size()-1);
            SASSERT(permutation.empty() || ctr.get_positive_count()==permutation.size());
            );
        unsigned sz = permutation.size();
        for(unsigned i=0; i<sz; i++) {
            if(i==permutation[i]) {
                continue;
            }
            unsigned prev_i = i;
            for(;;) {
                cycle.push_back(prev_i);
                unsigned next_i = permutation[prev_i];
                permutation[prev_i] = prev_i;
                if(next_i==i) {
                    break;
                }
                prev_i = next_i;
            }
            return true;
        }
        return false;
    }

    void collect_sub_permutation(const unsigned_vector & permutation, const unsigned_vector & translation,
            unsigned_vector & res, bool & identity) {
        SASSERT(res.empty());
        identity = true;
        unsigned sz = permutation.size();
        for(unsigned new_i=0; new_i<sz; new_i++) {
            unsigned idx = permutation[new_i];
            bool is_selected = translation[idx]!=UINT_MAX;
            if(is_selected) {
                unsigned sel_idx = translation[idx];
                if(!res.empty() && sel_idx!=res.back()+1) {
                    identity = false;
                }
                res.push_back(sel_idx);
            }
        }
    }

    void collect_and_transform(const unsigned_vector & src, const unsigned_vector & translation, 
            unsigned_vector & res) {
        unsigned n = src.size();
        for(unsigned i=0; i<n; i++) {
            unsigned translated = translation[src[i]];
            if(translated!=UINT_MAX) {
                res.push_back(translated);
            }
        }
    }


    void transform_set(const unsigned_vector & map, const idx_set & src, idx_set & result) {
        idx_set::iterator it = src.begin();
        idx_set::iterator end = src.end();
        for(; it!=end; ++it) {
            result.insert(map[*it]);
        }
    }

    void add_sequence(unsigned start, unsigned count, unsigned_vector & v) {
        unsigned after_last = start+count;
        for(unsigned i=start; i<after_last; i++) {
            v.push_back(i);
        }
    }



    // -----------------------------------
    //
    // misc helper functions (not datalog related)
    //
    // -----------------------------------

    void get_file_names(std::string directory, std::string extension, bool traverse_subdirs, 
            string_vector & res) {

        if(directory[directory.size()-1]!='\\' && directory[directory.size()-1]!='/') {
#ifdef _WINDOWS
            directory+='\\';
#else
            directory+='/';
#endif
        }

#ifdef _WINDOWS
        WIN32_FIND_DATAA findFileData;
        HANDLE hFind;
        std::string filePattern = directory+"*."+extension;

        hFind = FindFirstFileA(filePattern.c_str(), &findFileData);
        if (hFind != INVALID_HANDLE_VALUE) {
            do {
                char const* name = findFileData.cFileName;
                size_t len = strlen(name);
                if (len > extension.size() && extension == std::string(name+len-extension.size())) {
                    res.push_back(directory+std::string(name));
                }
            } while(FindNextFileA(hFind, &findFileData));
            FindClose(hFind);
        } 


        if(traverse_subdirs) {
            std::string subdirPattern = directory+"*.*";
            hFind = FindFirstFileA(subdirPattern.c_str(), &findFileData);
            if (hFind != INVALID_HANDLE_VALUE) {
                do {
                    if(findFileData.cFileName[0]=='.') {
                        continue;
                    }
                    get_file_names(directory+findFileData.cFileName, extension, traverse_subdirs, res);
                } while(FindNextFileA(hFind, &findFileData));
                FindClose(hFind);
            }
        }

#else
        NOT_IMPLEMENTED_YET();
#endif
    }

    bool file_exists(std::string name) {
        struct stat st;
        if(stat(name.c_str(),&st) == 0) {
            return true;
        }
        return false;
    }

    bool is_directory(std::string name) {
        if(!file_exists(name)) {
            return false;
        }
        struct stat status;
        stat(name.c_str(), &status);
        return (status.st_mode&S_IFDIR)!=0;
    }

    std::string get_file_name_without_extension(std::string name) {
        size_t slash_index = name.find_last_of("\\/");
        size_t dot_index = name.rfind(".");
        size_t ofs = (slash_index==std::string::npos) ? 0 : slash_index+1;
        size_t count = (dot_index!=std::string::npos && dot_index>ofs) ? 
            (dot_index-ofs) : std::string::npos;
        return name.substr(ofs, count);
    }

    bool string_to_uint64(const char * s, uint64 & res) {
#if _WINDOWS
        int converted = sscanf_s(s, "%I64u", &res);
#else
        int converted = sscanf(s, "%llu", &res);
#endif
        if(converted==0) {
            return false;
        }
        SASSERT(converted==1);
        return true;
    }

    bool read_uint64(const char * & s, uint64 & res) {
        static const uint64 max_but_one_digit = ULLONG_MAX/10;
        static const uint64 max_but_one_digit_safe = (ULLONG_MAX-9)/10;

        if(*s<'0' || *s>'9') {
            return false;
        }
        res=*s-'0';
        s++;
        while(*s>='0' && *s<='9') {
            if(res>max_but_one_digit_safe) {
                if(res>max_but_one_digit) {
                    return false; //overflow
                }
                res*=10;
                char digit = *s-'0';
                if(static_cast<int>(ULLONG_MAX-res)-digit<0) {
                    return false; //overflow
                }
                res+=digit;
            }
            else {
                res*=10;
                res+=*s-'0';
                s++;
            }
        }
        return true;
    }

    std::string to_string(uint64 num) {
        std::stringstream stm;
        stm<<num;
        return stm.str();
    }
};

