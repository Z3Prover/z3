#include "api/z3.h"
#include "util/debug.h"
#include <string>

static void check_seq_replace(char const* spec, bool expect_sat) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    Z3_del_context(ctx);
    if (expect_sat) {
        ENSURE(response.find("unsat") == std::string::npos && response.find("sat") != std::string::npos);
    }
    else {
        ENSURE(response.find("unsat") != std::string::npos);
    }
}

void tst_seq_replace() {
    check_seq_replace("(assert (= (str.replace_all \"aaa\" \"a\" \"b\") \"bbb\"))(check-sat)", true);
    check_seq_replace("(assert (not (= (str.replace_all \"aaa\" \"a\" \"b\") \"bbb\")))(check-sat)", false);
    check_seq_replace("(assert (= (seq.replace_all \"aaa\" \"a\" \"b\") \"bbb\"))(check-sat)", true);
    check_seq_replace("(assert (not (= (seq.replace_all \"aaa\" \"a\" \"b\") \"bbb\")))(check-sat)", false);
    check_seq_replace("(assert (not (= (str.replace_all \"aaa\" \"a\" \"b\")"
        " (seq.replace_all \"aaa\" \"a\" \"b\"))))(check-sat)", false);
    check_seq_replace("(assert (not (= (str.replace_re \"abc\" (str.to_re \"b\") \"X\")"
        " (seq.replace_re \"abc\" (str.to_re \"b\") \"X\"))))(check-sat)", false);
    check_seq_replace("(assert (not (= (str.replace_re_all \"aba\" (str.to_re \"a\") \"X\")"
        " (seq.replace_re_all \"aba\" (str.to_re \"a\") \"X\"))))(check-sat)", false);
}
