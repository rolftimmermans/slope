; sort numeric list
(def append (fn (a b)
  (let ((append (fn (a b)
                    (if (nil? a)
                      b
                      (cons (car a) (if (nil? (cdr a))
                                        b
                                        (append (cdr a) b)))))))
    (append a b))))

(def-syntax cond
  (syntax-rules ()
    ((cond ($test1 $then1) ($test2 $then2) (else $else))
     (if $test1 $then1 (if $test2 $then2 $else)))))

(def partition (fn (compare l1)
  (cond
    ((nil? l1) '())
    ((compare (car l1)) (cons (car l1) (partition compare (cdr l1))))
    (else (partition compare (cdr l1))))))

(def quicksort (fn (l1)
  (if (nil? l1)
    '()
    (let ((pivot (car l1)))
      (append (append (quicksort (partition (fn (x) (< x pivot)) l1))
                      (partition (fn (x) (= x pivot)) l1))
              (quicksort (partition (fn (x) (> x pivot)) l1)))))))

(quicksort '(4 2 6 3 0 8 1 9 5 7))
; result: (0 1 2 3 4 5 6 7 8 9)
; ---
