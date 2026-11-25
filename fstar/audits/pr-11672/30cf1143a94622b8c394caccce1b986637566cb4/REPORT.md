## Scope
Head 30cf1143a94622b8c394caccce1b986637566cb4, base d72de58d9e36009f1397377cd185342474c8ecfb. Source read from PR patch hunks only (not full functions, not hashed).

Functions audited: concat_model_converter::apply_partial (src/ast/converters/model_converter.cpp), Z3_goal_get_model (src/api/api_goal.cpp), evaluator_cfg m_symbolic lookup (src/model/model_evaluator.cpp).

## Obligations (abstract model)
1. ob1: concat apply_partial applies c2 then c1 and propagates failure from either - PROVED.
2. ob2: Z3_goal_get_model returns a model only if models are enabled and the converter accepts; result flagged symbolic - PROVED.
3. ob3: symbolic lookup never invents defaults for uninterpreted decls and agrees with non-symbolic lookup on interpreted ones - PROVED.

## Correspondence and assumptions
Models are association lists; converters are partial functions; evaluator default is a constant. Real func_interp, partial interpretations (eval_fi/BR_FAILED), array/datatype/FP branches are abstracted. No counterexample was found; no exhaustive search was done. Only F* standard library assumed.

## Excluded
generic_model_converter::apply, model2mc::apply_partial, Z3_model_eval symbolic branch, m_symbolic propagation in convert_model/translate, headers/docs, src/test/api.cpp. Memory safety and AST plumbing not verified.

## Tools
F* 2026.09.27, Z3 4.13.3.
Command: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out --include /home/runner/work/z3/z3/fstar PartialModel.fst
