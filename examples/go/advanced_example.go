package main

import (
	"fmt"
	"github.com/Z3Prover/z3/src/api/go"
)

func main() {
	ctx := z3.NewContext()
	fmt.Println("Z3 Go Bindings - Advanced Features Example")
	fmt.Println("==========================================")

	// Example 1: Bit-vectors
	fmt.Println("\nExample 1: Bit-vector operations")
	x := ctx.MkBVConst("x", 8)
	y := ctx.MkBVConst("y", 8)
	
	// x + y == 255 && x > y
	sum := ctx.MkBVAdd(x, y)
	ff := ctx.MkBV(255, 8)
	
	solver := ctx.NewSolver()
	solver.Assert(ctx.MkEq(sum, ff))
	solver.Assert(ctx.MkBVUGT(x, y))
	
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

	// Example 2: Floating-point arithmetic
	fmt.Println("\nExample 2: Floating-point arithmetic")
	solver.Reset()
	
	fpSort := ctx.MkFPSort32()
	a := ctx.MkConst(ctx.MkStringSymbol("a"), fpSort)
	b := ctx.MkConst(ctx.MkStringSymbol("b"), fpSort)
	
	// a + b > 0.0 (with rounding mode)
	rm := ctx.MkConst(ctx.MkStringSymbol("rm"), ctx.MkFPRoundingModeSort())
	fpSum := ctx.MkFPAdd(rm, a, b)
	zero := ctx.MkFPZero(fpSort, false)
	
	solver.Assert(ctx.MkFPGT(fpSum, zero))
	solver.Assert(ctx.MkFPGT(a, ctx.MkFPZero(fpSort, false)))
	
	if solver.Check() == z3.Satisfiable {
		fmt.Println("Satisfiable! (Floating-point constraint satisfied)")
	}

	// Example 3: Strings
	fmt.Println("\nExample 3: String operations")
	solver.Reset()
	
	s1 := ctx.MkConst(ctx.MkStringSymbol("s1"), ctx.MkStringSort())
	s2 := ctx.MkConst(ctx.MkStringSymbol("s2"), ctx.MkStringSort())
	
	// s1 contains "hello" && length(s1) < 20
	hello := ctx.MkString("hello")
	solver.Assert(ctx.MkSeqContains(s1, hello))
	
	len1 := ctx.MkSeqLength(s1)
	twenty := ctx.MkInt(20, ctx.MkIntSort())
	solver.Assert(ctx.MkLt(len1, twenty))
	
	// s2 is s1 concatenated with "world"
	world := ctx.MkString(" world")
	solver.Assert(ctx.MkEq(s2, ctx.MkSeqConcat(s1, world)))
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		if s1Val, ok := model.Eval(s1, true); ok {
			fmt.Println("s1 =", s1Val.String())
		}
		if s2Val, ok := model.Eval(s2, true); ok {
			fmt.Println("s2 =", s2Val.String())
		}
	}

	// Example 4: Datatypes (List)
	fmt.Println("\nExample 4: List datatype")
	solver.Reset()
	
	intSort := ctx.MkIntSort()
	listSort, nilDecl, consDecl, _, _, headDecl, _ := 
		ctx.MkListSort("IntList", intSort)
	
	// Create list: cons(1, cons(2, nil))
	nilList := ctx.MkApp(nilDecl)
	one := ctx.MkInt(1, intSort)
	two := ctx.MkInt(2, intSort)
	list2 := ctx.MkApp(consDecl, two, nilList)
	list12 := ctx.MkApp(consDecl, one, list2)
	
	// Check that head(list12) == 1
	listVar := ctx.MkConst(ctx.MkStringSymbol("mylist"), listSort)
	solver.Assert(ctx.MkEq(listVar, list12))
	
	headOfList := ctx.MkApp(headDecl, listVar)
	solver.Assert(ctx.MkEq(headOfList, one))
	
	if solver.Check() == z3.Satisfiable {
		fmt.Println("Satisfiable! List head is 1")
	}

	// Example 5: Tactics and Goals
	fmt.Println("\nExample 5: Using tactics")
	
	goal := ctx.MkGoal(true, false, false)
	p := ctx.MkIntConst("p")
	q := ctx.MkIntConst("q")
	
	// Add constraint: p > 0 && q > 0 && p + q == 10
	goal.Assert(ctx.MkGt(p, ctx.MkInt(0, ctx.MkIntSort())))
	goal.Assert(ctx.MkGt(q, ctx.MkInt(0, ctx.MkIntSort())))
	goal.Assert(ctx.MkEq(ctx.MkAdd(p, q), ctx.MkInt(10, ctx.MkIntSort())))
	
	// Apply simplify tactic
	tactic := ctx.MkTactic("simplify")
	result := tactic.Apply(goal)
	
	fmt.Printf("Tactic produced %d subgoals\n", result.NumSubgoals())
	if result.NumSubgoals() > 0 {
		subgoal := result.Subgoal(0)
		fmt.Println("Simplified goal:", subgoal.String())
	}

	// Example 6: Enumerations
	fmt.Println("\nExample 6: Enumeration types")
	solver.Reset()
	
	colorSort, colorConsts, _ := ctx.MkEnumSort(
		"Color",
		[]string{"Red", "Green", "Blue"},
	)
	
	red := ctx.MkApp(colorConsts[0])
	
	c1 := ctx.MkConst(ctx.MkStringSymbol("c1"), colorSort)
	c2 := ctx.MkConst(ctx.MkStringSymbol("c2"), colorSort)
	
	// c1 != c2 && c1 != Red
	solver.Assert(ctx.MkDistinct(c1, c2))
	solver.Assert(ctx.MkNot(ctx.MkEq(c1, red)))
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		if c1Val, ok := model.Eval(c1, true); ok {
			fmt.Println("c1 =", c1Val.String())
		}
		if c2Val, ok := model.Eval(c2, true); ok {
			fmt.Println("c2 =", c2Val.String())
		}
	}

	// Example 7: Tuples
	fmt.Println("\nExample 7: Tuple types")
	solver.Reset()
	
	tupleSort, mkTuple, projections := ctx.MkTupleSort(
		"Point",
		[]string{"x", "y"},
		[]*z3.Sort{ctx.MkIntSort(), ctx.MkIntSort()},
	)
	
	// Create point (3, 4)
	three := ctx.MkInt(3, ctx.MkIntSort())
	four := ctx.MkInt(4, ctx.MkIntSort())
	point := ctx.MkApp(mkTuple, three, four)
	
	p1 := ctx.MkConst(ctx.MkStringSymbol("p1"), tupleSort)
	solver.Assert(ctx.MkEq(p1, point))
	
	// Extract x coordinate
	xCoord := ctx.MkApp(projections[0], p1)
	solver.Assert(ctx.MkEq(xCoord, three))
	
	if solver.Check() == z3.Satisfiable {
		fmt.Println("Satisfiable! Tuple point created")
		model := solver.Model()
		if p1Val, ok := model.Eval(p1, true); ok {
			fmt.Println("p1 =", p1Val.String())
		}
	}

	// Example 8: Regular expressions  
	fmt.Println("\nExample 8: Regular expressions")
	solver.Reset()
	
	// Create a string variable
	str := ctx.MkConst(ctx.MkStringSymbol("str"), ctx.MkStringSort())
	
	// Create regex: (a|b)*c+ (zero or more 'a' or 'b', followed by one or more 'c')
	reA := ctx.MkToRe(ctx.MkString("a"))
	reB := ctx.MkToRe(ctx.MkString("b"))
	reC := ctx.MkToRe(ctx.MkString("c"))
	
	// (a|b)
	aOrB := ctx.MkReUnion(reA, reB)
	
	// (a|b)*
	aOrBStar := ctx.MkReStar(aOrB)
	
	// c+
	cPlus := ctx.MkRePlus(reC)
	
	// (a|b)*c+
	regex := ctx.MkReConcat(aOrBStar, cPlus)
	
	// Assert that string matches the regex
	solver.Assert(ctx.MkInRe(str, regex))
	
	// Also assert that length is less than 10
	strLen := ctx.MkSeqLength(str)
	ten := ctx.MkInt(10, ctx.MkIntSort())
	solver.Assert(ctx.MkLt(strLen, ten))
	
	if solver.Check() == z3.Satisfiable {
		model := solver.Model()
		fmt.Println("Satisfiable!")
		if strVal, ok := model.Eval(str, true); ok {
			fmt.Println("String matching (a|b)*c+:", strVal.String())
		}
	}

	// Example 9: Optimization
	fmt.Println("\nExample 9: Optimization (maximize/minimize)")
	
	opt := ctx.NewOptimize()
	
	// Variables
	xOpt := ctx.MkIntConst("x_opt")
	yOpt := ctx.MkIntConst("y_opt")
	
	// Constraints: x + y <= 10, x >= 0, y >= 0
	tenOpt := ctx.MkInt(10, ctx.MkIntSort())
	zeroOpt := ctx.MkInt(0, ctx.MkIntSort())
	
	opt.Assert(ctx.MkLe(ctx.MkAdd(xOpt, yOpt), tenOpt))
	opt.Assert(ctx.MkGe(xOpt, zeroOpt))
	opt.Assert(ctx.MkGe(yOpt, zeroOpt))
	
	// Objective: maximize x + 2*y
	twoOpt := ctx.MkInt(2, ctx.MkIntSort())
	objective := ctx.MkAdd(xOpt, ctx.MkMul(twoOpt, yOpt))
	objHandle := opt.Maximize(objective)
	
	if opt.Check() == z3.Satisfiable {
		model := opt.Model()
		fmt.Println("Optimal solution found!")
		if xVal, ok := model.Eval(xOpt, true); ok {
			fmt.Println("x =", xVal.String())
		}
		if yVal, ok := model.Eval(yOpt, true); ok {
			fmt.Println("y =", yVal.String())
		}
		upper := opt.GetUpper(objHandle)
		if upper != nil {
			fmt.Println("Maximum value of x + 2*y =", upper.String())
		}
	}

	fmt.Println("\nAll advanced examples completed successfully!")
}

