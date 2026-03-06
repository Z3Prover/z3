package main

import (
	"fmt"
	"os"
	"github.com/Z3Prover/z3/src/api/go"
)

func main() {
	ctx := z3.NewContext()
	fmt.Println("Z3 Go Bindings - New API Features Example")
	fmt.Println("=========================================")

	// Example 1: GetStatistics - View solver performance metrics
	fmt.Println("\nExample 1: GetStatistics() - Solver performance metrics")
	solver := ctx.NewSolver()
	x := ctx.MkIntConst("x")
	y := ctx.MkIntConst("y")
	
	solver.Assert(ctx.MkGt(x, ctx.MkInt(0, ctx.MkIntSort())))
	solver.Assert(ctx.MkGt(y, ctx.MkInt(0, ctx.MkIntSort())))
	solver.Assert(ctx.MkEq(ctx.MkAdd(x, y), ctx.MkInt(10, ctx.MkIntSort())))
	
	status := solver.Check()
	fmt.Println("Status:", status.String())
	
	stats := solver.GetStatistics()
	fmt.Println("Statistics:")
	fmt.Println(stats.String())

	// Example 2: FromString - Load SMT-LIB2 from string
	fmt.Println("\nExample 2: FromString() - Load SMT-LIB2 constraints")
	solver2 := ctx.NewSolver()
	
	smtlib := `(declare-const a Int)
(declare-const b Int)
(assert (> a 5))
(assert (< b 10))
(assert (= (+ a b) 20))`
	
	solver2.FromString(smtlib)
	fmt.Println("Loaded SMT-LIB2 assertions from string")
	fmt.Println("Assertions:", solver2.Assertions())
	
	status2 := solver2.Check()
	fmt.Println("Status:", status2.String())
	if status2 == z3.Satisfiable {
		model := solver2.Model()
		fmt.Println("Model:", model.String())
	}

	// Example 3: FromFile - Load SMT-LIB2 from file
	fmt.Println("\nExample 3: FromFile() - Load SMT-LIB2 from file")
	
	// Create a temporary SMT-LIB2 file
	tempFile, err := os.CreateTemp("", "test-*.smt2")
	if err != nil {
		fmt.Println("Error creating temp file:", err)
	} else {
		content := `(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (or (not p) (not q)))`
		
		_, err = tempFile.WriteString(content)
		tempFile.Close()
		
		if err != nil {
			fmt.Println("Error writing temp file:", err)
		} else {
			solver3 := ctx.NewSolver()
			solver3.FromFile(tempFile.Name())
			fmt.Println("Loaded SMT-LIB2 assertions from file")
			
			status3 := solver3.Check()
			fmt.Println("Status:", status3.String())
			if status3 == z3.Satisfiable {
				fmt.Println("Found satisfying assignment")
			}
		}
		os.Remove(tempFile.Name()) // Clean up
	}

	// Example 4: Parameter configuration
	fmt.Println("\nExample 4: GetHelp(), SetParams(), GetParamDescrs()")
	solver4 := ctx.NewSolver()
	
	// Get parameter descriptions
	descrs := solver4.GetParamDescrs()
	fmt.Println("Parameter descriptions retrieved (type:", fmt.Sprintf("%T", descrs), ")")
	
	// Get help text (showing first 500 chars)
	help := solver4.GetHelp()
	if len(help) > 500 {
		fmt.Println("Help text (first 500 chars):")
		fmt.Println(help[:500] + "...")
	} else {
		fmt.Println("Help text:")
		fmt.Println(help)
	}
	
	// Set parameters
	params := ctx.MkParams()
	params.SetUint("timeout", 5000) // 5 second timeout
	params.SetBool("unsat_core", true) // Enable unsat cores
	solver4.SetParams(params)
	fmt.Println("Set solver parameters: timeout=5000ms, unsat_core=true")
	
	// Add unsat core tracking
	p := ctx.MkBoolConst("p")
	q := ctx.MkBoolConst("q")
	solver4.AssertAndTrack(p, p)
	solver4.AssertAndTrack(ctx.MkNot(p), q)
	
	status4 := solver4.Check()
	fmt.Println("Status:", status4.String())
	if status4 == z3.Unsatisfiable {
		core := solver4.UnsatCore()
		fmt.Printf("Unsat core size: %d\n", len(core))
	}

	// Example 5: Interrupt (demonstrating the API)
	fmt.Println("\nExample 5: Interrupt() - Graceful solver interruption")
	solver5 := ctx.NewSolver()
	
	// Note: In a real application, you would call Interrupt() from a different
	// goroutine when you want to stop a long-running solver operation
	fmt.Println("Interrupt() is available for stopping long-running solves")
	fmt.Println("(In practice, call from a goroutine with a timeout or user signal)")
	
	// Simple example just to show the method exists and is callable
	// In real use: go func() { time.Sleep(timeout); solver5.Interrupt() }()
	solver5.Assert(ctx.MkBoolConst("simple"))
	status5 := solver5.Check()
	fmt.Println("Status:", status5.String())
	// After a real check completes, you could call Interrupt() if needed
	// but it would have no effect since the check already finished

	fmt.Println("\nAll new API features demonstrated successfully!")
}
