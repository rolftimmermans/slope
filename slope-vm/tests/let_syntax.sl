; inverted if macro
(let-syntax
  ((unless
    (syntax-rules ()
      ((unless $test $then $else) (if $test $else $then))
      ((unless $test $then) (if $test nil $then)))))

  (unless (= 1 2) 'no 'yes))

; result: no
; ---
