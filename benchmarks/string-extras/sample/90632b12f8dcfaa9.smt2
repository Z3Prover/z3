; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.contrib.staticfiles.findersAppDirectoriesFinder.findformula11_unsat.smt2
(set-logic ALL)
(declare-const path String)
(declare-const all Bool)
(assert (not (< (str.len path) 0)))
(assert (not (str.prefixof "/" path)))
(assert (not (< (str.len (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))) 0)))
(assert (str.prefixof "/" (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))))
(assert (not (= (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path)) "")))
(assert (not (< (str.len (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))) 0)))
(assert (str.prefixof "/" (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))))
(assert (not (< (str.len (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))) 0)))
(assert (not (str.prefixof "//" (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path)))))
(assert (not (< (str.len (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path))) 0)))
(assert (= (+ 0 (str.indexof (str.++ "/root/08_django/django/contrib/admin/static" (str.++ "/" path)) "/" 0)) (- 1)))
(check-sat)


