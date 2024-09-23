// This script is used to invoke ninja and automatically suggest fixes to build warnings
import { select, input, confirm } from "@inquirer/prompts"


// TODO: invoke ninja in z3 build directory
// - pipe output of build to a string buffer
// - chunk up warning/error messages one by one
// - create AI query to have the warning/error fixed
// - stage the changes
// - recompile, rinse repeat until fixes
// - backtrack from failed fixes?

// let ninjaout = await host.exec("ninja", [])
// console.log(ninjaout.stdout)
// await runPrompt( (_) => { _.def("BUILDMSG", ninjaout, { maxTokens: 20000})
//                           _.$`BUILDMSG is the output of a ninja build. Please generate fixes for the warning messages, stage the changes. Repeat the build process for up to three iterations to fix error or warning messages` }



defData("EXAMPLEMSG","
/home/nbjorner/z3/src/smt/theory_str.cpp: In member function ‘void smt::theory_str::instantiate_axiom_CharAt(smt::enode*)’:
/home/nbjorner/z3/src/smt/theory_str.cpp:1092:15: warning: ‘arg0’ may be used uninitialized [-Wmaybe-uninitialized]
 1092 |         expr* arg0, *arg1;
      |               ^~~~
In file included from /home/nbjorner/z3/src/ast/ast_smt2_pp.h:26,
                 from /home/nbjorner/z3/src/smt/theory_str.cpp:17:
In member function ‘app* arith_util::mk_lt(expr*, expr*) const’,
    inlined from ‘void smt::theory_str::instantiate_axiom_CharAt(smt::enode*)’ at /home/nbjorner/z3/src/smt/theory_str.cpp:1110:40:
")

// TODO: script to extract file contents
// TODO: script what to update.

$`
You are a helpful AI assistant who knows C++ and can fix build warnings.
You are given the following warning message ${EXAMPLEMSG}. Create a fix.
`
