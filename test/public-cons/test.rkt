#lang racket

(require "../../interp-ce.rkt")


(define prog
  '(cons 1 (cons 2 '())))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
