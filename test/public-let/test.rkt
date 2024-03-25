#lang racket

(require "../../interp-ce.rkt")


(define prog
  '(let ([x 5] [y 7] [z 9])
     (let ([y x] [x y])
       (let ([z (- z y)])
         (+ x y z)))))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
