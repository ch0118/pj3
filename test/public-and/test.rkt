#lang racket

(require "../../interp-ce.rkt")

(define prog
  '(and))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
