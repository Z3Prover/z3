#include "pdr_context.h"
#include "reg_decl_plugins.h"


using namespace pdr;

static expr_ref mk_state(expr_ref_vector const& states, random_gen& rand) {
    expr_ref result(states.get_manager());
    result = states[rand(states.size())];
    return result;
}


struct test_model_search {
    struct init_test {
        init_test(func_decl_ref& fn) {
            ast_manager& m = fn.get_manager();
            reg_decl_plugins(m);
            fn = m.mk_const_decl(symbol("f"), m.mk_bool_sort());
        }
    };

    ast_manager       m;
    smt_params        smt_params;
    fixedpoint_params fp_params;
    context           ctx;
    manager           pm;
    func_decl_ref     fn;
    init_test         initt;
    pred_transformer  pt;
    random_gen        rand;
    model_search      search;
    expr_ref_vector   states;  


    test_model_search():
        ctx(smt_params, fp_params, m),
        pm(smt_params, 10, m),
        fn(m),
        initt(fn),
        pt(ctx, pm, fn),
        rand(10),
        search(true),
        states(m) {
    }

    void add_tree(model_node* parent, bool force_goal) {
        unsigned level = parent->level();
        search.add_leaf(*parent);
        if (level > 0 && (force_goal || parent->is_goal())) {
            search.remove_goal(*parent);
            add_tree(alloc(model_node, parent, mk_state(states, rand), pt, level-1), false);
            add_tree(alloc(model_node, parent, mk_state(states, rand), pt, level-1), false);
            parent->check_pre_closed();
        }
    }

    bool mutate() {
        model_node* leaf = search.next();
        if (!leaf) return false;
        unsigned level = leaf->level();
        if (level == 0) {
            if (rand(2) == 0) {
                leaf->display(std::cout << "backtrack to grandparent\n", 1);
                search.backtrack_level(false, *leaf->parent());
            }
            else {
                leaf->display(std::cout << "backtrack to parent\n", 1);
                search.backtrack_level(false, *leaf);
            }
        }
        else {
            leaf->display(std::cout << "grow tree\n", 1);
            add_tree(leaf, true);
        }
        return true;
    }

    void init() {
        std::cout << "pdr state-hash search tree\n";
        
        expr_ref state(m);
        func_decl_ref fn(m);
        for (unsigned i = 0; i < 10; ++i) {
            std::ostringstream strm;
            strm << "s" << i;
            state = m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort());
            fn = to_app(state)->get_decl();
            states.push_back(state);
        }
        state = states[0].get();
        unsigned level = 4;
        for(unsigned n = 0; n < 100; ++n) {
            model_node* root = alloc(model_node, 0, mk_state(states, rand), pt, level);
            search.set_root(root);
            add_tree(root, false);
            search.display(std::cout);
            
            while (true) {
                search.well_formed();
                if (!mutate()) break;
                search.display(std::cout);
            }
            search.reset();
            //++level;
        }
        search.reset();        
    }

};

void tst_pdr() {
    test_model_search test;

    test.init();
}
