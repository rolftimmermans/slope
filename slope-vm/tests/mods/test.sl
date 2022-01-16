(export foo bar baz)
(def foo 'foo)
(def bar (fn () 'bar))
(def baz (fn () 'baz)) ; todo
; (def-syntax baz (syntax-rules () ((baz) 'baz)))
