#lang racket

(require "../../interp-ce.rkt")


(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce '((lambda (x) x) 5))))
                     #:exists 'replace)
