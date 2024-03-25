#lang racket

(require "../../interp-ce.rkt")


(with-output-to-file "output"
                     (lambda ()
                       (print (take (interp-ce '(((lambda (w) w) (lambda (x) x)) ((lambda (y) y) (lambda (z) z)))) 2)))
                     #:exists 'replace)
