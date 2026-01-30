#!/bin/bash
# Download representative SMT2 benchmarks from SMT-LIB

set -e

BENCH_DIR="/home/runner/work/z3/z3/benchmarks"
cd "$BENCH_DIR"

echo "Downloading SMT2 benchmarks from SMT-LIB..."
echo ""

# Download a variety of benchmarks from SMT-LIB GitHub
# These are publicly available benchmarks used in SMT-COMP

BASE_URL="https://raw.githubusercontent.com/SMT-LIB/SMT-LIB/master/non-incremental"

# QF_BV (bit-vector) benchmarks
echo "Downloading QF_BV benchmarks..."
wget -q "${BASE_URL}/QF_BV/sage/bench_1.smt2" -O qf_bv_bench1.smt2 2>/dev/null || echo "  (skipped)"
wget -q "${BASE_URL}/QF_BV/sage/bench_2.smt2" -O qf_bv_bench2.smt2 2>/dev/null || echo "  (skipped)"

# QF_IDL (integer difference logic)
echo "Downloading QF_IDL benchmarks..."
wget -q "${BASE_URL}/QF_IDL/job_shop/job_shop_4_15_3.smt2" -O qf_idl_jobshop.smt2 2>/dev/null || echo "  (skipped)"

# QF_LIA (linear integer arithmetic)
echo "Downloading QF_LIA benchmarks..."
wget -q "${BASE_URL}/QF_LIA/cut_lemmas/cut_lemma_01.smt2" -O qf_lia_cut1.smt2 2>/dev/null || echo "  (skipped)"

# QF_UF (uninterpreted functions)
echo "Downloading QF_UF benchmarks..."
wget -q "${BASE_URL}/QF_UF/eq_diamond/eq_diamond4.smt2" -O qf_uf_diamond.smt2 2>/dev/null || echo "  (skipped)"

echo ""
echo "Creating fallback benchmarks (in case downloads failed)..."

# Create some simple test benchmarks
cat > simple_sat.smt2 << 'EOF'
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 10))
(check-sat)
EOF

cat > simple_unsat.smt2 << 'EOF'
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
EOF

cat > bv_medium.smt2 << 'EOF'
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (= (bvadd x y) z))
(assert (= x #x00000001))
(assert (= y #x00000002))
(assert (= z #x00000004))
(check-sat)
EOF

cat > lia_medium.smt2 << 'EOF'
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (> a 0))
(assert (> b 0))
(assert (= c (+ (* 2 a) (* 3 b))))
(assert (< c 100))
(assert (> c 50))
(check-sat)
(exit)
EOF

cat > array_simple.smt2 << 'EOF'
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (= (select (store a i v) i) v))
(check-sat)
EOF

echo ""
echo "Benchmarks ready:"
ls -lh *.smt2
echo ""
echo "Total: $(ls -1 *.smt2 | wc -l) SMT2 files"
