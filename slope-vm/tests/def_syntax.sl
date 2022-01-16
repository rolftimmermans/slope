; literal
(def-syntax foo
  (syntax-rules ()
    ((foo) 'foo)))

(foo)
; result: foo
; ---

; unless
(def-syntax unless
  (syntax-rules ()
    ((unless $test $then $else) (if $test $else $then))
    ((unless $test $then) (if $test nil $then))))

(unless (= 1 2) 'no 'yes)

; result: no
; ---

; let loop
(def-syntax let2
  (syntax-rules ()
    ((let2 ((variable init) ...) body ...)
      (let ((variable init) ...) body ...))

    ((let2 loop ((variable init) ...) body ...)
      (let ((loop (fn (variable ...) body ...))) (loop init ...)))))

(def fac (fn (n)
  (let2 fac ((n 1))
    (if (< n 2) a (fac (- n 1) (* a n))))))

(fac 5)
; result: 120
; ---

; invalid form
(def-syntax () ())
; error: invalid syntax
; ---
