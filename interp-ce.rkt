#lang racket

;; Project 3: Metacircular interpreter for Scheme
;; CIS352 -- Fall 2022

(provide interp-ce)

; Your task is to write a CE interpreter for a substantial subset of Scheme/Racket. 
; A CE interpreter is meta-circular to a large degree (e.g., a conditional in the target
; language (scheme-ir?) can be implemented using a conditional in the host language (Racket),
; recursive evaluation of a sub-expression can be implemented as a recursive call to the
; interpreter, however, it's characterized by creating an explicit closure value for lambdas
; that saves its static environment (the environment when it's defined). For example, a CE
; interpreter for the lambda calculus may be defined:
(define (interp-ce-lambda exp [env (hash)])
  (match exp
         [`(lambda (,x) ,body)
          ; Return a closure that pairs the code and current (definition) environment
          `(closure (lambda (,x) ,body) ,env)]
         [`(,efun ,earg)
          ; Evaluate both sub-expressions
          (define vfun (interp-ce-lambda efun env))  
          (define varg (interp-ce-lambda earg env))
          ; the applied function must be a closure
          (match-define `(closure (lambda (,x) ,body) ,env+) vfun)
          ; we extend the *closure's environment* and interp the body
          (interp-ce-lambda body (hash-set env+ x varg))]
         [(? symbol? x)
          ; Look up a variable in the current environment
          (hash-ref env x)]))

; Following is a predicate for the target language you must support. You must support any
; syntax allowed by scheme-ir that runs without error in Racket, returning a correct value..
(define (scheme-ir? exp)
  ; You should support a few built-in functions bound to the following variables at the top-level
  (define (prim? s) (member s '(+ - * = equal? list cons car cdr null?)))
  (match exp
         [`(lambda ,(? (listof symbol?)) ,(? scheme-ir?)) #t] ; fixed arguments lambda
         [`(lambda ,(? symbol?) ,(? scheme-ir?)) #t] ; variable argument lambda
         [`(if ,(? scheme-ir?) ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [`(let ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(let* ([,(? symbol?) ,(? scheme-ir?)] ...) ,(? scheme-ir?)) #t]
         [`(and ,(? scheme-ir?) ...) #t]
         [`(or ,(? scheme-ir?) ...) #t]
         [`(apply ,(? scheme-ir?) ,(? scheme-ir?)) #t]
         [(? (listof scheme-ir?)) #t]
         [(? prim?) #t]
         [(? symbol?) #t]
         [(? number?) #t]
         [(? boolean?) #t]
         [''() #t]
         [_ #f]))

; Interp-ce must correctly interpret any valid scheme-ir program and yield the same value
; as DrRacket, except for closures which must be represented as `(closure ,lambda ,environment).
; (+ 1 2) can return 3 and (cons 1 (cons 2 '())) can yield '(1 2). For programs that result in a 
; runtime error, you should return `(error ,message)---giving some reasonable string error message.
; Handling errors and some trickier cases will give bonus points. 
(define (interp-ce exp)
  ; Might add helpers or other code here...
  (define (apply-primitive op args)
    (match op
      ['+ (apply + args)]
      ['- (apply - args)]
      ['* (apply * args)]
      ['= (apply = args)]
      ['equal? (apply equal? args)]
      ['list (apply list args)]
      ['cons (cons (first args) (second args))]
      ['car (car (first args))]
      ['cdr (cdr (first args))]
      ['null? (null? (first args))]
      [else `(error "Unsupported primitive operation: ~a" ,op)]))
  (define (interp exp env)
    (match exp
      [(? symbol? x) (hash-ref env x)]
      [`(lambda ,args ,body) 
       ;; closures must be represented this way
       `(closure ,exp ,env)]
      [`(if ,e-g ,e-t ,e-f)
       (if (interp e-g env)
           (interp e-t env)
           (interp e-f env))]
      [`(let ([,x ,e0]) ,e-body)
       ;; evaluate e0 to v0
       (define v0 (interp e0 env))
       (interp e-body (hash-set env x v0))]
      [`(let ([,xs ,es] ...) ,e-body) 
          (define values (map (lambda (e) (interp e env)) es))
          (define new-env (foldl (lambda (acc-env x val) (hash-set acc-env x val))
                          env
                          xs
                          values))
          (interp `(begin ,@e-body) new-env))]
      [`(let* ([,xs ,es] ...) ,e-body)
          (define (process-bindings xs es env)
            (if (null? xs)
                env
                (let* ((x (car xs))
                       (e (car es))
                       (val (interp e env))
                       (new-env (hash-set env x val)))
                 (process-bindings (cdr xs) (cdr es) new-env))))
          (define new-env (process-bindings xs es env))
          (interp `(begin ,@e-body) new-env))]
      [`(and)
       #t]
      [`(and ,e0 ,e-rest ...)
       (if (interp e0 env)
           (interp `(and ,@e-rest) env)
           #f)]
      [`((or ,e0 ,e-rest ...) 
         (let ([v0 (interp e0 env)])
           (if v0 v0 (interp `(or ,@e-rest) env)))]
      [(? number? n) n]
      [(? boolean? b) b]
      [''() '()]
      [`(,ef ,eargs ...)
       (let* ((vf (interp ef env))
              (vargs (map (lambda (arg) (interp arg env)) eargs)))
         (match vf
           [`(closure (lambda ,args ,body) ,closure-env)
            (let* ((new-env (foldl (lambda (param val acc-env) (hash-set acc-env param val))
                                   closure-env
                                   (zip args vargs))))
              (interp body new-env))]
           [else (apply-primitive vf vargs)]))]))
       
  ;; you need to cook up a starting environment: at first it can just
  ;; be the empty hash, but later on you may want to add things like
  ;; builtins here.
  (interp exp (hash)))
