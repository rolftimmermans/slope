; constant
(def a 1.5)
a
; result: 1.5
; ---

; indirect constant
(def a 1.5)
(def b a)
b
; result: 1.5
; ---

; unbound variable
(def a a)
; error: unbound variable
; ---

; invalid form
(def a)
; error: invalid syntax
; ---
