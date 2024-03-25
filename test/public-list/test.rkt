#lang racket

(require "../../interp-ce.rkt")


(define prog
  '(list 1 2 3 4))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
