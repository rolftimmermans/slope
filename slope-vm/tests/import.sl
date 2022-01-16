; value
(import "tests/mods/test.sl")
foo
; result: foo
; ---

; function
(import "tests/mods/test.sl")
(bar)
; result: bar
; ---

; macro
(import "tests/mods/test.sl")
(baz)
; result: baz
; ---
