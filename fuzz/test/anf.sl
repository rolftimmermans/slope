(define (Value? M)
  (match M
    [`(quote ,_)         #t]
    [(? number?)         #t]
    [(? boolean?)        #t]
    [(? string?)         #t]
    [(? char?)           #t]
    [(? symbol?)         #t]
    [(or '+ '- '* '/ '=) #t]
    [else                #f]))


(define (normalize-term M) (normalize M (λ (x) x)))

(define (normalize M k)
  (match M
    [`(λ ,params ,body)
      (k `(λ ,params ,(normalize-term body)))]

    [`(let ([,x ,M1]) ,M2)
      (normalize M1 (λ (N1)
       `(let ([,x ,N1])
         ,(normalize M2 k))))]

    [`(if ,M1 ,M2 ,M3)
      (normalize-name M1 (λ (t)
       (k `(if ,t ,(normalize-term M2)
                  ,(normalize-term M3)))))]

    [`(,Fn . ,M*)
      (normalize-name Fn (λ (t)
       (normalize-name* M* (λ (t*)
        (k `(,t . ,t*))))))]

    [(? Value?)             (k M)]))

(define (normalize-name M k)
  (normalize M (λ (N)
    (if (Value? N) (k N)
        (let ([t (gensym)])
         `(let ([,t ,N]) ,(k t)))))))

(define (normalize-name* M* k)
  (if (null? M*)
      (k '())
      (normalize-name (car M*) (λ (t)
       (normalize-name* (cdr M*) (λ (t*)
        (k `(,t . ,t*))))))))
