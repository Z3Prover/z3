(benchmark ex
  :logic AUFLIA
  :extrafuns ((x Int) (y Int) (z Int))
  :assumption (> x 0)
  :assumption (<= x -1)
  :assumption (or (> x 0) (< y 1))
  :assumption (> y 2)
  :assumption (> y 3)
  :assumption (<= y -1) 
  :formula (= z (+ x y)))
        