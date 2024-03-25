#lang racket

(require "../../interp-ce.rkt")

(define prog
  '(and #t (or (equal? 4 5) (equal? 6 6)) (= 2 2)))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
