package z3

import "testing"

func TestNewContextCheckSat(t *testing.T) {
	ctx := NewContext()
	solver := ctx.NewSolver()

	x := ctx.MkIntConst("x")
	zero := ctx.MkInt(0, ctx.MkIntSort())
	solver.Assert(ctx.MkGt(x, zero))

	if solver.Check() != Satisfiable {
		t.Fatalf("expected sat")
	}
}
