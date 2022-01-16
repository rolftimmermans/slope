(def sum (fn (n)
         (let ((sum (fn (x n)
                    (if (= n 0)
                        x
                        (sum (+ x n) (- n 1))))))
           (sum 0 n))))

(sum 200000)
