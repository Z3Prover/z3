package main

import (
	"fmt"
	"github.com/Z3Prover/z3/src/api/go"
)

func main() {
	// Create a new Z3 context
	ctx := z3.NewContext()
	fmt.Println("Z3 Go Bindings - Basic Example")
	fmt.Println("================================")

	// Example 1: Simple integer constraint
	fmt.Println("\nExample 1: Solving x > 0")
	x := ctx.MkIntConst("x")
	zero := ctx.MkInt(0, ctx.MkIntSort())
	constraint := ctx.MkGt(x, zero)
	
	solver := ctx.NewSolver()
	solver.Assert(constraint)
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		fmt.Println("Model:", model.String())
		if val, ok := model.Eval(x, true); ok {
			fmt.Println("x =", val.String())
		}
	}

	// Example 2: System of equations
	fmt.Println("\nExample 2: Solving x + y = 10 ∧ x - y = 2")
	solver.Reset()
	y := ctx.MkIntConst("y")
	ten := ctx.MkInt(10, ctx.MkIntSort())
	two := ctx.MkInt(2, ctx.MkIntSort())
	
	eq1 := ctx.MkEq(ctx.MkAdd(x, y), ten)
	eq2 := ctx.MkEq(ctx.MkSub(x, y), two)
	
	solver.Assert(eq1)
	solver.Assert(eq2)
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		if xVal, ok := model.Eval(x, true); ok {
			fmt.Println("x =", xVal.String())
		}
		if yVal, ok := model.Eval(y, true); ok {
			fmt.Println("y =", yVal.String())
		}
	}

	// Example 3: Boolean logic
	fmt.Println("\nExample 3: Boolean satisfiability")
	solver.Reset()
	p := ctx.MkBoolConst("p")
	q := ctx.MkBoolConst("q")
	
	// (p ∨ q) ∧ (¬p ∨ ¬q)
	formula := ctx.MkAnd(
		ctx.MkOr(p, q),
		ctx.MkOr(ctx.MkNot(p), ctx.MkNot(q)),
	)
	
	solver.Assert(formula)
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		if pVal, ok := model.Eval(p, true); ok {
			fmt.Println("p =", pVal.String())
		}
		if qVal, ok := model.Eval(q, true); ok {
			fmt.Println("q =", qVal.String())
		}
	}

	// Example 4: Unsatisfiable constraint
	fmt.Println("\nExample 4: Checking unsatisfiability")
	solver.Reset()
	a := ctx.MkIntConst("a")
	
	// a > 0 ∧ a < 0 (unsatisfiable)
	solver.Assert(ctx.MkGt(a, zero))
	solver.Assert(ctx.MkLt(a, zero))
	
	status := solver.Check()
	fmt.Println("Status:", status.String())
	if status == z3.Unsatisfiable {
		fmt.Println("The constraints are unsatisfiable (as expected)")
	}

	fmt.Println("\nAll examples completed successfully!")
}
