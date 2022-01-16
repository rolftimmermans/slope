; add
(def add1 (fn (x) (+ x 1)))
(add1 3)
; result: 4
; ---

; mul
(def mul (fn (x y z) (* x y z)))
(mul 2 3 4)
; result: 24
; ---

; cons
(def list4 (fn (a b c d) (cons a (cons b (cons c (cons d ()))))))
(cdr (list4 1 2 3 4))
; result: (2 3 4)
; ---

; list
(def list4 (fn (a b c d) (list a b c d)))
(cdr (list4 1 2 3 4))
; result: (2 3 4)
; ---

; eq
(def zero? (fn (x) (if (= x 0) #t #f)))
(zero? 0)
; result: #t
; ---

; recursive fib
(def fib-bad (fn (n)
             (if (< n 3)
                 1
                 (+ (fib-bad (- n 1)) (fib-bad (- n 2))))))

(fib-bad 12)
; result: 144
; ---

; tail recursive fib
(def fib (fn (n)
         (let ((fib (fn (n a b)
                    (if (= n 0)
                        a
                        (fib (- n 1) b (+ a b))))))
           (fib n 0 1))))

(fib 60)
; result: 1548008755920
; ---

; tail recursive gcd
(def gcd (fn (x y)
         (if (= y 0)
             x
             (gcd y (% x y)))))

(gcd 33031 182845)
; result: 29
; ---

; tail recursive fac
(def fac (fn (n)
         (let ((fac (fn (n a)
                    (if (< n 2)
                        a
                        (fac (- n 1) (* a n))))))
           (fac n 1))))

(fac 5)
; result: 120
; ---

; overflow stack
(def overflow (fn (x) (+ 1 (overflow x))))
(overflow 1)
; error: stack overflow
; ---

; not a closure
(def maybe-fn (fn () 4))
((maybe-fn) 2)
; error: expected closure
; ---
