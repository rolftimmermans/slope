;;; Helper function
(define (partition compare l1)
        (cond ;; Match
           ((null? l1) '())
           ((compare (car l1)) (cons (car l1) (partition compare (cdr l1))))
           (else (partition compare (cdr l1)))))


;;; Sorts a list
(define (quicksort l1)
  (cond
      ((null? l1) '())
      (else (let ((pivot (car l1)))
        (append (append (quicksort (partition (lambda (x) (< x pivot)) l1))
                    (partition (lambda (x) (= x pivot)) l1))
                (quicksort (partition (lambda (x) (> x pivot)) l1)))))))
