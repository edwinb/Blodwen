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
;; Either Int x, where the Int is an error code

;; If the file operation raises an error, catch it and return an appropriate
;; error code
(define (blodwen-file-op op)
  (with-handlers ([exn:fail:filesystem? (lambda (exn) 
                               (either-left 255))]) ; TODO: Work out error codes!
      (either-right (op))))

(define (blodwen-putstring p s)
    (if (port? p) (write-string p s) void)
    0)

(define (blodwen-open file mode)
    (cond 
        ((string=? mode "r") (open-input-file file))
        ((string=? mode "w") (open-output-file file))
        (else (raise "I haven't worked that one out yet, sorry..."))))

(define (blodwen-close-port p)
    (cond 
      ((input-port? p) (close-input-port p))
      ((output-port? p) (close-output-port p))))

(define (blodwen-get-line p)
    (if (port? p)
        (let ((str (read-line p)))
            (if (eof-object? str)
                ""
                (string-append str "\n")))
        void))

(define (blodwen-eof p)
  (if (eof-object? (peek-char p))
      1
      0))
