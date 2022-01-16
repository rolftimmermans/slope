; http://web.archive.org/web/20160101153032/http://people.ace.ed.ac.uk/staff/medward2/class/moz/cm/doc/contrib/lispstyle.html
; http://web.archive.org/web/20181004121854/http://people.ace.ed.ac.uk/staff/medward2/class/moz/cm/doc/contrib/lispstyle.html
; (define-syntax cond (syntax-rules (else =>)
; ((cond (else result1 result2 ...)) (begin result1 result2 ...))
;         ((cond (test => result))
;          (let ((temp test))
; (if temp (result temp))))
; ((cond (test => result) clause1 clause2 ...)
;          (let ((temp test))
;            (if temp
;                (result temp)
; (cond clause1 clause2 ...)))) ((cond (test)) test)
; ((cond (test) clause1 clause2 ...) (let ((temp test))
; (if temp temp
; (cond clause1 clause2 ...)))) ((cond (test result1 result2 ...))
; (if test (begin result1 result2 ...))) ((cond (test result1 result2 ...)
; clause1 clause2 ...) (if test
; (begin result1 result2 ...) (cond clause1 clause2 ...)))))
