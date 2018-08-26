(define blodwen-read-args (lambda (desc)
  (case (vector-ref desc 0)
    ((0) '())
    ((1) (cons (vector-ref desc 2)
               (blodwen-read-args (vector-ref desc 3)))))))
(define b+ (lambda (x y bits) (remainder (+ x y) (expt 2 bits))))
(define b- (lambda (x y bits) (remainder (- x y) (expt 2 bits))))
(define b* (lambda (x y bits) (remainder (* x y) (expt 2 bits))))
(define b/ (lambda (x y bits) (remainder (/ x y) (expt 2 bits))))
(define cast-num 
  (lambda (x) 
    (if (number? x) x 0)))
(define cast-string-int
  (lambda (x)
    (floor (cast-num (string->number x)))))
(define cast-string-double
  (lambda (x)
    (cast-num (string->number x))))
(define string-cons (lambda (x y) (string-append (string x) y)))
(define get-tag (lambda (x) (vector-ref x 0)))

(define either-left 
  (lambda (x)
    (vector 0 #f #f x)))

(define either-right
  (lambda (x)
    (vector 1 #f #f x)))

;; Much of the following adapted from idris-chez, thanks to Niklas Larsson

;; All the file operations are implemented as primitives which return 
;; Either Int x, where the Int is an error code:
(define (blodwen-error-code x)
    (cond 
        ((i/o-read-error? x) 1)
        ((i/o-write-error? x) 2)
        ((i/o-file-does-not-exist-error? x) 3)
        ((i/o-file-protection-error? x) 4)
        (else 5)))

;; If the file operation raises an error, catch it and return an appropriate
;; error code
(define (blodwen-file-op op)
  (guard
    (x ((i/o-error? x) (either-left (blodwen-error-code x))))
    (either-right (op))))

(define (blodwen-get-n n p)
    (if (port? p) (get-string-n p n) ""))

(define (blodwen-putstring p s)
    (if (port? p) (put-string p s) void)
    0)

(define (blodwen-open file mode)
    (define tc (make-transcoder (utf-8-codec)))
    (define bm (buffer-mode line))
    (case mode 
        (("r") (open-file-input-port file (file-options) bm tc))
        (("w") (open-file-output-port file (file-options no-fail) bm tc))
        (("wx") (open-file-output-port file (file-options) bm tc))
        (("a") (open-file-output-port file (file-options no-fail no-truncate) bm tc))
        (("r+") (open-file-input/output-port file (file-options no-create) bm tc))
        (("w+") (open-file-input/output-port file (file-options no-fail) bm tc))
        (("w+x") (open-file-input/output-port file (file-options) bm tc))
        (("a+") (open-file-input/output-port file (file-options no-fail no-truncate) bm tc))
        (else (raise (make-i/o-error)))))

(define (blodwen-close-port p)
    (when (port? p) (close-port p)))

(define (blodwen-get-line p)
    (if (and (port? p) (not (port-eof? p))) 
        (let ((str (get-line p)))
            (string-append str "\n"))
        ""))

(define (blodwen-eof p)
    (if (port-eof? p)
        1
        0))
