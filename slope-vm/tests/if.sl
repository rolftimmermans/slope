; const
(if #t 'yes 'no)
; result: yes
; ---

; const eq
(if (= 1 2) 'yes 'no)
; result: no
; ---

; const eq no alternate
(if (= 1 2) 'yes)
; result: nil
; ---

; missing consequent
(if (= 1 2))
; error: invalid syntax
; ---

; invalid form
(if (= 1 2) 'yes 'no 'haha)
; error: invalid syntax
; ---
