(benchmark patterns 
   :status unknown 
   :logic ALL       
   :extrafuns ((?store Int Int Int Int) (?select Int Int Int) (?PO Int Int Int) (?asChild Int Int Int)
               (?classDown Int Int Int) (?array Int Int) (?elemtype Int Int) (?is Int Int Int) (?cast Int Int Int)
               (?Object Int) (?null Int) (?typeof Int Int) (?asElems Int Int) (?isAllocated Int Int Int) 
               (?fClosedTime Int Int) (?eClosedTime Int Int) (?max Int Int) (?asLockSet Int Int) (?isNewArray Int Int)
               (?classLiteral Int Int) (?Class Int) (?alloc Int) (?arrayType Int) (?f Int Int) (?finv Int Int)
               )

   :formula (forall (a Int) (i Int) (e Int)  
                    (= (?select (?store a i e) i) e)
                    :pats { (?store a i e) }
		    :weight { 0 })

   :formula (forall (a Int) (i Int) (j Int) (e Int)  
                    (or (= i j) (= (?select (?store a i e) j) (?select a j)))
                    :pats { (?select (?store a i e) j) }
                    :weight { 0 })

   :formula (forall (t0 Int) (t1 Int) (t2 Int) 
                    (or (not (= (?PO t0 t1) 1))
                        (not (= (?PO t1 t2) 1))
                        (= (?PO t0 t2) 1))
                    :pats { (?PO t0 t1) (?PO t1 t2) })

   :formula (forall (t0 Int) (t1 Int) 
                    (or (not (= (?PO t0 t1) 1))
                        (not (= (?PO t1 t0) 1))
                        (= t0 t1))
                    :pats { (?PO t0 t1) (?PO t1 t0) })

   :formula (forall (t0 Int) (t1 Int) (t2 Int) 
                    (or (not (= (?PO t0 (?asChild t1 t2)) 1))
                        (= (?classDown t2 t0) (?asChild   t1 t2)))
                    :pats { (?PO t0 (?asChild t1 t2)) })

   :formula (forall (t Int) 
                    (= (?finv (?f t)) t)
                    :pats { (?f t) })

   :formula (forall (t0 Int) (t1 Int) 
                    (iff (= (?PO t0 (?array t1)) 1)
                         (not (or (not (= t0 (?array (?elemtype t0))))
                                  (not (= (?PO (?elemtype t0) t1) 1)))))
                    :pats { (?PO t0 (?array t1)) })

   :formula (forall (x Int) (t Int) 
                    (or (not (= (?is x t) 1))
                        (= (?cast x t) x))
                    :pats { (?cast x t) })

   :formula (forall (x Int) (t Int) 
                    (or (not (= (?PO t ?Object) 1))
                        (iff (= (?is x t) 1)
                             (or (= x ?null)
                                 (= (?PO (?typeof x) t) 1))))
                    :pats { (?PO t ?Object) (?is x t) })

   :formula (forall (e Int) (a Int) (i Int) 
                    (= (?is (?select (?select (?asElems e) a) i)
                            (?elemtype (?typeof a))) 1)
                    :pats { (?select (?select (?asElems e) a) i) })

   :formula (forall (x Int) (f Int) (a0 Int) 
                    (or (<= (+ a0 (* -1 (?fClosedTime f))) 0)
                        (not (= (?isAllocated x a0) 1))
                        (= (?isAllocated (?select f x) a0) 1))
                    :pats { (?isAllocated (?select f x) a0) })

   :formula (forall (a Int) (e Int) (i Int) (a0 Int) 
                    (or (<= (+ a0 (* -1 (?eClosedTime e))) 0)
                        (not (= (?isAllocated a a0) 1))
                        (= (?isAllocated (?select (?select e a) i) a0) 1))
                    :pats { (?isAllocated (?select (?select e a) i) a0) })

   :formula (forall (S Int) 
                    (= (?select (?asLockSet S) (?max (?asLockSet S))) 1)
                    :pats { (?select (?asLockSet S) (?max (?asLockSet S))) })

   :formula (forall (s Int) 
                    (or (not (= 1 (?isNewArray s)))
                        (= (?PO (?typeof s) ?arrayType) 1))
                    :pats { (?isNewArray s) })

   :formula (forall (t Int) 
                    (not (or (= (?classLiteral t) ?null)
                             (not (= (?is (?classLiteral t) ?Class) 1))
                             (not (= (?isAllocated (?classLiteral t) ?alloc) 1))))
                    :pats { (?classLiteral t) })

   :extrafuns ((?select2 Int Int Int Int) 
               (?store2 Int Int Int Int Int))
       
   :formula (forall (A Int) (o Int) (f Int) (v Int)
                    (= (?select2 (?store2 A o f v) o f) v)
                    :pats { (?store2 A o f v) }
                    :weight { 0 })                    

   :formula (forall (A Int) (o Int) (f Int) (p Int) (g Int) (v Int)
                    (or (= o p) (= (?select2 (?store2 A o f v) p g) (?select2 A p g)))
                    :pats { (?select2 (?store2 A o f v) p g) }
                    :weight { 0 })

   :formula (forall (A Int) (o Int) (f Int) (p Int) (g Int) (v Int)
                    (or (= f g) (= (?select2 (?store2 A o f v) p g) (?select2 A p g)))
                    :pats { (?select2 (?store2 A o f v) p g) }
                    :weight { 0 })

   :extrapreds ((?subtypes Int Int))

   :formula (forall (t Int) (u Int) (v Int)
                    (or (not (?subtypes t u))
                        (not (?subtypes u v))
                        (?subtypes t v))
                    :pat {(?subtypes t u) (?subtypes u v)})

   :formula (forall (t Int) (u Int)
                    (or (not (?subtypes t u))
                        (not (?subtypes u t))
                        (= t u))
                    :pat {(?subtypes t u) (?subtypes u t)})

   :extrafuns ((?Unbox Int Int) (?UnboxedType Int Int) (?Box Int Int Int) (?System.Object Int) (?Smt.true Int) (?AsRepField Int Int Int)
               (?AsPeerField Int Int) (?nullObject Int) (?ownerRef_ Int) (?ownerFrame_ Int) (IntsHeap Int Int) (?localinv_ Int)
               (?inv_ Int) (?BaseClass_ Int Int) (?typeof_ Int Int) (?PeerGroupPlaceholder_ Int) (?ClassRepr Int Int))

   :formula (forall (x Int) (p Int)
                    (or (not (?subtypes (?UnboxedType (?Box x p)) ?System.Object))
                        (not (= (?Box x p) p))
                        (= x p))
                    :pat { (?subtypes (?UnboxedType (?Box x p)) ?System.Object)} )
 
   :formula (forall (h Int) (o Int) (f Int) (T Int)
                    (or 
                     (not (= (IntsHeap h) ?Smt.true))
                     (= (?select2 h o (?AsRepField f T)) ?nullObject)
                     (not (or (not (= (?select2 h (?select2 h o (?AsRepField f T)) ?ownerRef_) o))
                              (not (= (?select2 h (?select2 h o (?AsRepField f T)) ?ownerFrame_) T)))))
                    :pat {(?select2 h o (?AsRepField f T))})

   :formula (forall (h Int) (o Int) (f Int)
                    (or
                     (not (= (IntsHeap h) ?Smt.true))
                     (= (?select2 h o (?AsPeerField f)) ?nullObject)
                     (not (or (not (= (?select2 h (?select2 h o (?AsPeerField f)) ?ownerRef_) (?select2 h o ?ownerRef_)))
                              (not (= (?select2 h (?select2 h o (?AsPeerField f)) ?ownerFrame_) (?select2 h o ?ownerFrame_))))))
                    :pat {(?select2 h o (?AsPeerField f))})
   
   :formula (forall (h Int) (o Int)
                    (or 
                     (not (= (IntsHeap h) ?Smt.true))
                     (= (?select2 h o ?ownerFrame_) ?PeerGroupPlaceholder_)
                     (not (?subtypes (?select2 h (?select2 h o ?ownerRef_) ?inv_) (?select2 h o ?ownerFrame_)))
                     (= (?select2 h (?select2 h o ?ownerRef_) ?localinv_) (?BaseClass_ (?select2 h o ?ownerFrame_)))
                     (not (or (not (= (?select2 h o ?inv_) (?typeof_ o)))
                              (not (= (?select2 h o ?localinv_) (?typeof_ o))))))
                    :pat {(?subtypes (?select2 h (?select2 h o ?ownerRef_) ?inv_) (?select2 h o ?ownerFrame_))})

   :formula (forall (T Int) (h Int)
                    (or (not (= (IntsHeap h) ?Smt.true))
                        (= (?select2 h (?ClassRepr T) ?ownerFrame_) ?PeerGroupPlaceholder_))
                    :pat {(?select2 h (?ClassRepr T) ?ownerFrame_)})

   :extrafuns ((?RefArray Int Int Int)
               (Ints_ Int Int Int)
               (?RefArrayGet Int Int Int)
               (?elements_ Int)
               (?NonNullRefArray Int Int Int)
               (IntsNotNull_ Int Int Int)
               (?Rank_ Int Int)
               )

   :formula (forall (a Int) (T Int) (i Int) (r Int) (heap Int)
                    (or (not (= (IntsHeap heap) ?Smt.true))
                        (not (?subtypes (?typeof_ a) (?RefArray T r)))
                        (= (Ints_ (?RefArrayGet (?select2 heap a ?elements_) i) T) ?Smt.true))
                    :pat {(?subtypes (?typeof_ a) (?RefArray T r)) (?RefArrayGet (?select2 heap a ?elements_) i)})

   :formula (forall (a Int) (T Int) (r Int)
                    (or (= a ?nullObject) 
                        (not (?subtypes (?typeof_ a) (?RefArray T r)))
                        (= (?Rank_ a) r))
                    :pat {(?subtypes (?typeof_ a) (?RefArray T r))})

   :extrafuns ((?ValueArray Int Int Int)
               (?ArrayCategory_ Int Int)
               (?ArrayCategoryValue_ Int)
               (?ElementType_ Int Int)
               (?System.Array Int)
               (?allocated_ Int)
               (?StructGet_ Int Int Int)
               (?AsRangeField Int Int Int)
               (IntsAllocated Int Int Int)
               )

   :extrapreds ((IntnRange Int Int))
   
   :formula (forall (T Int) (ET Int) (r Int)
                    (or (not (?subtypes T (?ValueArray ET r)))
                        (= (?ArrayCategory_ T) ?ArrayCategoryValue_))
                    :pat {(?subtypes T (?ValueArray ET r))})

   :formula (forall (A Int) (r Int) (T Int)
                    (or
                     (not (?subtypes T (?RefArray A r)))
                     (not (or (not (= T (?RefArray (?ElementType_ T) r)))
                              (not (?subtypes (?ElementType_ T) A)))))
                    :pat {(?subtypes T (?RefArray A r))})

   :formula (forall (A Int) (r Int) (T Int)
                    (or (not (?subtypes T (?ValueArray A r)))
                        (= T (?ValueArray A r)))
                    :pat {(?subtypes T (?ValueArray A r))})

   :extrafuns ((?AsDirectSubClass Int Int Int)
               (?OneClassDown Int Int Int)
               )

   :formula (forall (A Int) (B Int) (C Int)
                    (or (not (?subtypes C (?AsDirectSubClass B A)))
                        (= (?OneClassDown C A) B))
                    :pat {(?subtypes C (?AsDirectSubClass B A))})
   
   :formula (forall (o Int) (T Int)
                    (iff (= (Ints_ o T) ?Smt.true)
                         (or (= o ?nullObject)
                             (?subtypes (?typeof_ o) T)))
                    :pat {(Ints_ o T)})

   :formula (forall (o Int) (T Int)
                    (iff (= (IntsNotNull_ o T) ?Smt.true)
                         (or (= o ?nullObject)
                             (not (= (Ints_ o T) ?Smt.true))))
                    :pat {(IntsNotNull_ o T)})

   :formula (forall (h Int) (o Int)
                    (or (not (= (IntsHeap h) ?Smt.true))
                        (= o ?nullObject)
                        (not (?subtypes (?typeof_ o) ?System.Array))
                        (not (or (not (= (?select2 h o ?inv_) (?typeof_ o)))
                                 (not (= (?select2 h o ?localinv_) (?typeof_ o))))))
                    :pat {(?subtypes (?typeof_ o) ?System.Array) (?select2 h o ?inv_)})

   :formula (forall (h Int) (o Int) (f Int) (T Int)
                    (or (not (= (IntsHeap h) ?Smt.true))
                        (IntnRange (?select2 h o (?AsRangeField f T)) T))
                    :pat {(?select2 h o (?AsRangeField f T))})

   :formula (forall (h Int) (o Int) (f Int)
                    (or
                     (not (= (IntsHeap h) ?Smt.true))
                     (not (= (?select2 h o ?allocated_) ?Smt.true))
                     (= (IntsAllocated h (?select2 h o f)) ?Smt.true))
                    :pat {(IntsAllocated h (?select2 h o f))})

    :formula (forall (h Int) (s Int) (f Int)
                     (or (not (= (IntsAllocated h s) ?Smt.true))
                         (= (IntsAllocated h (?StructGet_ s f)) ?Smt.true))
                     :pat {(IntsAllocated h (?StructGet_ s f))})

    :extrapreds ((?isAllocated_ Int Int))

    :formula (forall (x Int) (f Int) (a0 Int)
                     (or (<= (+ a0 (* -1 (?fClosedTime f))) 0)
                         (not (?isAllocated_ x a0))
                         (?isAllocated_ (?select f x) a0))
                     :pat {(?isAllocated_ (?select f x) a0)})

   :formula (forall (a Int) (e Int) (i Int) (a0 Int) 
                    (or (<= (+ a0 (* -1 (?eClosedTime e))) 0)
                        (not (?isAllocated_ a a0))
                        (?isAllocated_ (?select (?select e a) i) a0))
                    :pats { (?isAllocated_ (?select (?select e a) i) a0) })

   :formula (forall (e Int) (a Int) (i Int) 
                    (= (?is (?select (?select (?asElems e) a) i)
                            (?elemtype (?typeof a))) ?Smt.true)
                    :pats { (?select (?select (?asElems e) a) i) })

   :formula (forall (t0 Int) (t1 Int)
                    (iff (?subtypes t0 (?array t1))
                         (not (or (not (= t0 (?array (?elemtype t0))))
                                  (not (?subtypes (?elemtype t0) t1)))))
                    :pat {(?subtypes t0 (?array t1))})

   :formula (forall (t0 Int) (t1 Int) (t2 Int) 
                    (or (not (?subtypes t0 (?asChild t1 t2)))
                        (= (?classDown t2 t0) (?asChild   t1 t2)))
                    :pats { (?subtypes t0 (?asChild t1 t2)) })

   :formula (forall (t0 Int) (t1 Int) 
                    (iff (?subtypes t0 (?array t1))
                         (not (or (not (= t0 (?array (?elemtype t0))))
                                  (not (?subtypes (?elemtype t0) t1)))))
                    :pats { (?subtypes t0 (?array t1)) })

   :formula (forall (x Int) (t Int) 
                    (or (not (= (?is x t) ?Smt.true))
                        (= (?cast x t) x))
                    :pats { (?cast x t) })

   :formula (forall (x Int) (t Int) 
                    (or (not (?subtypes t ?Object))
                        (iff (= (?is x t) ?Smt.true)
                             (or (= x ?null)
                                 (?subtypes (?typeof x) t))))
                    :pats { (?subtypes t ?Object) (?is x t) })

   :formula (forall (e Int) (a Int) (i Int) 
                    (= (?is (?select (?select (?asElems e) a) i)
                            (?elemtype (?typeof a))) 1)
                    :pats { (?select (?select (?asElems e) a) i) })
   )
