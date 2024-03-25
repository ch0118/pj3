#lang racket

(require "../../interp-ce.rkt")


(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce '(+ 2 (+ 3 4)))))
                     #:exists 'replace)
