 /**

  * Finds function calls with arguments that have unspecified evaluation order.

  *

  * @name Unspecified argument evaluation order

  * @kind problem

  * @problem.severity warning

  * @id cpp/z3/unspecevalorder

  */



  import cpp



  predicate isPureFunc(Function f) {

    f.getName() = "m" or

    not exists(Assignment a | a.getEnclosingFunction() = f) and

    forall(FunctionCall g | g.getEnclosingFunction() = f | isPureFunc(g.getTarget()))

  }



  predicate sideEffectfulArgument(Expr a) {

    exists(Function f | f = a.(FunctionCall).getTarget() |

      not f instanceof ConstMemberFunction and

      not isPureFunc(f)

    )

    or

    exists(ArrayExpr b | b = a.(ArrayExpr) |

      sideEffectfulArgument(b.getArrayBase()) or sideEffectfulArgument(b.getArrayOffset())

    )

    or

    exists(Assignment b | b = a)

    or

    exists(BinaryOperation b | b = a | sideEffectfulArgument(b.getAnOperand()))

    or

    exists(UnaryOperation b | b = a | sideEffectfulArgument(b.getOperand()))

  }



  from FunctionCall f, Expr a, int i, Expr b, int j where

    i < j and

    f.getTarget().getName() != "operator&&" and

    f.getTarget().getName() != "operator||" and

    a = f.getArgument(i) and

    b = f.getArgument(j) and

    sideEffectfulArgument(a) and

    sideEffectfulArgument(b)

  select f, "potentially unspecified evaluation order of function arguments: $@ and $@", a,

    i.toString(), b, j.toString()