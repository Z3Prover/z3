package main

import (
	"fmt"
	"github.com/Z3Prover/z3/src/api/go"
)

func main() {
	// Create a new Z3 context
	ctx := z3.NewContext()
	fmt.Println("Z3 Go Bindings - New APIs Test")
	fmt.Println("================================")

	// Test diagnostic APIs
	fmt.Println("\nTest 1: Solver Diagnostic APIs")
	solver := ctx.NewSolver()
	
	// Create some simple constraints
	x := ctx.MkIntConst("x")
	y := ctx.MkIntConst("y")
	zero := ctx.MkInt(0, ctx.MkIntSort())
	ten := ctx.MkInt(10, ctx.MkIntSort())
	
	solver.Assert(ctx.MkGt(x, zero))
	solver.Assert(ctx.MkLt(x, ten))
	solver.Assert(ctx.MkEq(ctx.MkAdd(x, y), ten))
	
	// Check satisfiability
	status := solver.Check()
	fmt.Println("Status:", status.String())
	
	if status == z3.Satisfiable {
		// Test Units() - get unit clauses
		units := solver.Units()
		fmt.Printf("Units: %d clauses\n", len(units))
		for i, unit := range units {
			fmt.Printf("  Unit %d: %s\n", i, unit.String())
		}
		
		// Test NonUnits() - get non-unit clauses
		nonUnits := solver.NonUnits()
		fmt.Printf("NonUnits: %d clauses\n", len(nonUnits))
		for i, nu := range nonUnits {
			fmt.Printf("  NonUnit %d: %s\n", i, nu.String())
		}
		
		// Note: Trail() and TrailLevels() work primarily with SimpleSolver.
		// With default solvers (created with NewSolver()), they may return
		// errors like "cannot retrieve trail from solvers created using tactics".
		// For those use cases, Units() and NonUnits() provide similar diagnostic info.
		fmt.Println("Note: Trail() and TrailLevels() work primarily with SimpleSolver")
	}

	// Test congruence closure APIs
	fmt.Println("\nTest 2: Congruence Closure APIs")
	solver2 := ctx.NewSolver()
	
	// Create expressions for congruence testing
	a := ctx.MkIntConst("a")
	b := ctx.MkIntConst("b")
	c := ctx.MkIntConst("c")
	
	// Assert a = b and b = c (so a should be congruent to c)
	solver2.Assert(ctx.MkEq(a, b))
	solver2.Assert(ctx.MkEq(b, c))
	
	status = solver2.Check()
	fmt.Println("Status:", status.String())
	
	if status == z3.Satisfiable {
		// Test CongruenceRoot() - get congruence class representative
		rootA := solver2.CongruenceRoot(a)
		rootB := solver2.CongruenceRoot(b)
		rootC := solver2.CongruenceRoot(c)
		fmt.Printf("CongruenceRoot(a): %s\n", rootA.String())
		fmt.Printf("CongruenceRoot(b): %s\n", rootB.String())
		fmt.Printf("CongruenceRoot(c): %s\n", rootC.String())
		
		// Test CongruenceNext() - get next element in congruence class
		nextA := solver2.CongruenceNext(a)
		fmt.Printf("CongruenceNext(a): %s\n", nextA.String())
		
		// Test CongruenceExplain() - explain why two terms are congruent
		explain := solver2.CongruenceExplain(a, c)
		fmt.Printf("CongruenceExplain(a, c): %s\n", explain.String())
	}

	fmt.Println("\nAll new API tests completed successfully!")
}
