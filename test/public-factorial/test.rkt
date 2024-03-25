#lang racket

(require "../../interp-ce.rkt")

(define prog
  '(let* ([U (lambda (u) (u u))]
          [Y (U (lambda (y) (lambda (f) (f (lambda (x) (((y y) f) x))))))]
          [fact (Y (lambda (fact) (lambda (n) (if (= n 0) 1 (* n (fact (- n 1)))))))])
     (fact 5)))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
