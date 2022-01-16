; constant
(let ((a 1.5)) a)
; result: 1.5
; ---

; indirect constant
(let ((a 1.5) (b a)) b)
; result: 1.5
; ---

; add constants
(let ((a 1) (b 2)) (+ a b))
; result: 3
; ---

; shadowing unbound variable
(let ((a a)) ())
; error: unbound variable
; ---

; invalid form
(let (a 1) a)
; error: invalid syntax
; ---
