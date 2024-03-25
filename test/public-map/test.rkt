#lang racket

(require "../../interp-ce.rkt")

(define prog
  '(let* ([U (lambda (u) (u u))]
          [map (U (lambda (mk-map)
                    (lambda (f lst)
                      (if (null? lst)
                          '()
                          (cons (f (car lst))
                                ((U mk-map) f (cdr lst)))))))])
     (map (lambda (m) (+ m 1))
          (list 2 3 4 5 6))))

(with-output-to-file "output"
                     (lambda ()
                       (print (interp-ce prog)))
                     #:exists 'replace)
