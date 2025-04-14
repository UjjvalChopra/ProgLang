#lang plai-typed
(require "ps5-ast.rkt")

(define (parse-ty (s : s-expression)) : Type
  (cond
    [(s-exp-symbol? s)
     (case (s-exp->symbol s)
       [(boolT) (boolT)]
       [(voidT) (voidT)]
       [(numT) (numT)])]
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(funT) (funT (parse-ty (second l)) (parse-ty (third l)))]
            [(pairT) (pairT (parse-ty (second l)) (parse-ty (third l)))]
            [(boxT) (boxT (parse-ty (second l)))]
            [(listT) (listT (parse-ty (second l)))]
            )]))]))

(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(+) (plusC (parse (second l)) (parse (third l)))]
            [(*) (timesC (parse (second l)) (parse (third l)))]
            [(pair) (pairC (parse (second l)) (parse (third l)))]
            [(equal?) (equal?C (parse (second l)) (parse (third l)))]
            [(cons) (consC (parse (second l)) (parse (third l)))]
            [(is-empty?) (is-empty?C (parse (second l)))]
            [(empty) (emptyC (parse-ty (second l)))]
            [(first) (firstC (parse (second l)))]
            [(rest) (restC (parse (second l)))]
            [(fst) (fstC (parse (second l)))]
            [(snd) (sndC (parse (second l)))]
            [(box) (boxC (parse (second l)))]
            [(unbox) (unboxC (parse (second l)))]
            [(set-box!) (set-box!C (parse (second l)) (parse (third l)))]
            [(lambda) (lambdaC (s-exp->symbol (second l)) (parse-ty (third l)) (parse (fourth l)))]
            [(rec) (recC (s-exp->symbol (second l)) (s-exp->symbol (third l)) (parse-ty (fourth l))
                         (parse-ty (list-ref l 4)) (parse (list-ref l 5)))]
            [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
            [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [else (appC (parse (first l)) (parse (second l)))]
            )]
         [else (appC (parse (first l)) (parse (second l)))]
       ))]
    ))



(define-type (Binding 'a)
  [bind (name : symbol) (val : 'a)])

(define-type-alias TyEnv (listof (Binding Type)))
(define empty-env empty)
(define extend-env cons)

(define (lookup (x : symbol) (env : (listof (Binding 'a)))) : 'a
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))


; TODO: you must implement this.
; It if e has type t under environment env, then
; (tc-env env e) should return t.
; Otherwise, if e is not well-typed (i.e. does not type check), tc-env should raise an exception
; of some form using the 'error' construct in plai-typed.

(define (tc-env (env : TyEnv) (e : Expr)) : Type
  (type-case Expr e
    [numC (n) (numT)]
    [boolC (b) (boolT)]
    [voidC () (voidT)]
             
    [plusC (e1 e2) 
           (if (and (equal? (tc-env env e1) (numT)) 
                    (equal? (tc-env env e2) (numT)))
               (numT)
               (error 'tc-env "+ not numbers"))]
             
    [timesC (e1 e2) 
            (if (and (equal? (tc-env env e1) (numT))
                     (equal? (tc-env env e2) (numT)))
                (numT)
                (error 'tc-env "* not numbers"))]

    [lambdaC (x argT e)
             (funT argT (tc-env (extend-env (bind x argT) env) e))]
             
    [idC (x) (lookup x env)]
             
    [appC (e1 e2)
           (type-case Type (tc-env env e1)
             [funT (argT retT)
                   (if (equal? (tc-env env e2) argT)
                       retT
                       (error 'tc-env "argument type mismatch"))]
             [else (error 'tc-env "not a function")])]
             
    [letC (x e1 e2)
          (let ([t1 (tc-env env e1)])
            (tc-env (extend-env (bind x t1) env) e2))]

    [emptyC (t) (listT t)]
             
    [consC (e1 e2)
           (let ([t1 (tc-env env e1)]
                 [lst-type (tc-env env e2)])
             (type-case Type lst-type
               [listT (t) (if (equal? t1 t)
                           lst-type
                           (error 'tc-env "cons element type mismatch"))]
               [else (error 'tc-env "cons second arg must be list")]))]

    [firstC (e)
            (type-case Type (tc-env env e)
              [listT (t) t]
              [else (error 'tc-env "first requires list")])]

    [restC (e)
           (type-case Type (tc-env env e)
             [listT (t) (listT t)]
             [else (error 'tc-env "rest requires list")])]

    [is-empty?C (e)
                (type-case Type (tc-env env e)
                  [listT (t) (boolT)]
                  [else (error 'tc-env "is-empty? requires list")])]

    [equal?C (e1 e2)
             (let ([t1 (tc-env env e1)]
                   [t2 (tc-env env e2)])
               (if (equal? t1 t2)
                   (boolT) 
                   (error 'tc-env "equal? requires same types")))]

    [ifC (e e1 e2)
         (if (equal? (tc-env env e) (boolT))
             (let ([t1 (tc-env env e1)]
                   [t2 (tc-env env e2)])
               (if (equal? t1 t2)
                   t1
                   (error 'tc-env "if branches must have same type")))
             (error 'tc-env "if condition must be boolean"))]

    [pairC (e1 e2) (pairT (tc-env env e1) (tc-env env e2))]

    [fstC (e)
          (type-case Type (tc-env env e)
            [pairT (t1 t2) t1]
            [else (error 'tc-env "fst requires pair")])]

    [sndC (e)
          (type-case Type (tc-env env e)
            [pairT (t1 t2) t2]
            [else (error 'tc-env "snd requires pair")])]

    [boxC (e) (boxT (tc-env env e))]

    [unboxC (e)
            (type-case Type (tc-env env e)
              [boxT (t) t]
              [else (error 'tc-env "unbox requires box")])]

    [set-box!C (e1 e2)
               (let ([box-type (tc-env env e1)]
                     [val-type (tc-env env e2)])
                 (type-case Type box-type
                   [boxT (t) (if (equal? t val-type)
                              (voidT)
                              (error 'tc-env "set-box! type mismatch"))]
                   [else (error 'tc-env "set-box! requires box")]))]

    [recC (f x argT retT e)
          (let ([env-f (extend-env (bind f (funT argT retT)) env)]
                [env-fx (extend-env (bind x argT)
                                  (extend-env (bind f (funT argT retT)) env))])
            (let ([actual-ret (tc-env env-fx e)])
              (if (equal? actual-ret retT)
                  (funT argT retT)
                  (error 'tc-env "rec body type mismatch"))))]
    ))

(define (tc (e : Expr))
  (tc-env empty-env e))