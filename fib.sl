(def fib (fn (n)
         (if (> n 1)
              (+ (fib (- n 1)) (fib (- n 2)))
              1
          )))

(fib 36)
