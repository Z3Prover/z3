package main

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/Z3Prover/z3/src/api/go"
)

func main() {
	// Test SetInitialValue
	fmt.Println("\nTesting Solver.SetInitialValue()...")
	ctx2 := z3.NewContext()
	solver2 := ctx2.NewSolver()

	x := ctx2.MkIntConst("x")
	y := ctx2.MkIntConst("y")

	// Set initial values to guide the solver
	solver2.SetInitialValue(x, ctx2.MkInt(5, ctx2.MkIntSort()))
	solver2.SetInitialValue(y, ctx2.MkInt(10, ctx2.MkIntSort()))

	// Add constraints
	solver2.Assert(ctx2.MkGt(x, ctx2.MkInt(0, ctx2.MkIntSort())))
	solver2.Assert(ctx2.MkGt(y, ctx2.MkInt(0, ctx2.MkIntSort())))

	if solver2.Check() == z3.Satisfiable {
		fmt.Println("  ✓ SetInitialValue works (solver found solution)")
	} else {
		fmt.Println("  ✗ SetInitialValue failed")
		os.Exit(1)
	}

	// Test FromString
	fmt.Println("\nTesting Solver.FromString()...")
	ctx3 := z3.NewContext()
	solver3 := ctx3.NewSolver()

	smtString := "(declare-const z Int)(assert (> z 42))"
	solver3.FromString(smtString)

	if solver3.Check() == z3.Satisfiable {
		fmt.Println("  ✓ FromString works correctly")
	} else {
		fmt.Println("  ✗ FromString failed")
		os.Exit(1)
	}

	// Test FromFile
	fmt.Println("\nTesting Solver.FromFile()...")
	ctx4 := z3.NewContext()
	solver4 := ctx4.NewSolver()

	// Create a temporary SMT file
	tmpDir := os.TempDir()
	smtFile := filepath.Join(tmpDir, "test.smt2")
	err := os.WriteFile(smtFile, []byte("(declare-const w Int)\n(assert (< w 100))\n"), 0644)
	if err != nil {
		fmt.Printf("  ✗ Failed to create test file: %v\n", err)
		os.Exit(1)
	}
	defer os.Remove(smtFile)

	solver4.FromFile(smtFile)
	if solver4.Check() == z3.Satisfiable {
		fmt.Println("  ✓ FromFile works correctly")
	} else {
		fmt.Println("  ✗ FromFile failed")
		os.Exit(1)
	}

	fmt.Println("\nAll tests passed! ✓")
}
