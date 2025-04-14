#lang plai-typed

(require "ps2-ast.rkt")

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)

(define (lookup (x : symbol) (env : Env)) : Value
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-val (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]))

;; Helper function to parse `let` and `let*` bindings from an S-expression
(define (parse-let-bindings (bindings : s-expression)) : (listof (symbol * Expr))
  (let [(bindings-list (s-exp->list bindings))]
    (map (lambda (binding)
           (let [(binding-pair (s-exp->list binding))]
             (let [(var (first binding-pair))
                   (expr (second binding-pair))]
               (pair (s-exp->symbol var) (parse expr)))))
         bindings-list)))

;; Parsing function
(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (valC (numV (s-exp->number s)))]
    [(equal? s '#t) (valC (boolV #t))]
    [(equal? s '#f) (valC (boolV #f))]
    
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (case (s-exp->symbol (first l))
         [(+) (plusC (parse (second l)) (parse (third l)))]
         [(*) (timesC (parse (second l)) (parse (third l)))]
         [(equal?) (equal?C (parse (second l)) (parse (third l)))]
         [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
      
         [(let) 
          (let [(bindings (parse-let-bindings (second l)))]
            (letC bindings (parse (third l))))]
         [(let*) 
          (let [(bindings (parse-let-bindings (second l)))]
            (let*C bindings (parse (third l))))]
         
         [(list) (listC (map parse (rest l)))]
         [(cons) (consC (parse (second l)) (parse (third l)))]
         [(first) (firstC (parse (second l)))]
         [(rest) (restC (parse (second l)))]
         
         [(natrec) 
          (let [(e1 (parse (second l)))
                (e2 (parse (third l)))
                (x  (s-exp->symbol (first (s-exp->list (fourth l)))))
                (y  (s-exp->symbol (second (s-exp->list (fourth l)))))
                (e3 (parse (third (s-exp->list (fourth l)))))]
            (natrecC e1 e2 x y e3))]
         
         [(listrec) 
          (let [(e1 (parse (second l)))
                (e2 (parse (third l)))
                (head  (s-exp->symbol (first (s-exp->list (fourth l)))))
                (rest (s-exp->symbol (second (s-exp->list (fourth l)))))
                (recresult (s-exp->symbol (third (s-exp->list (fourth l)))))
                (e3  (parse (fourth (s-exp->list (fourth l)))))]
            (listrecC e1 e2 head rest recresult e3))]
         [(unpack)
          (let [(vars (map s-exp->symbol (s-exp->list (second l))))]
            (unpackC vars (parse (third l)) (parse (fourth l))))]
         [else (error 'parse "Unknown expression type")]))]))


;; This expression evaluator will take care of all the cases
(define (eval-env (env : Env) (e : Expr)) : Value
  (type-case Expr e
    [valC (v) v]

    [plusC (e1 e2)
     (let [(v1 (eval-env env e1))
           (v2 (eval-env env e2))]
       (if (and (numV? v1) (numV? v2))
           (numV (+ (numV-n v1) (numV-n v2)))
           (error 'eval "+ expects numeric arguments")))]

    [timesC (e1 e2)
     (let [(v1 (eval-env env e1))
           (v2 (eval-env env e2))]
       (if (and (numV? v1) (numV? v2))
           (numV (* (numV-n v1) (numV-n v2)))
           (error 'eval "* expects numeric arguments")))]

    [equal?C (e1 e2)
     (let [(v1 (eval-env env e1))
           (v2 (eval-env env e2))]
       (boolV (equal? v1 v2)))]

    [ifC (guard then else-branch)
     (let [(v1 (eval-env env guard))]
       (if (boolV? v1)
           (if (boolV-b v1) (eval-env env then) (eval-env env else-branch))
           (error 'eval "Guard must evaluate to a boolean")))]

  [letC (bindings body)
      (let* ([evaluated-bindings 
              (map (lambda (binding)
                     (pair (fst binding)
                           (eval-env env (snd binding))))
                   bindings)]
             [new-env 
              (foldl (lambda (binding acc-env)
                       (extend-env (bind (fst binding) (snd binding)) acc-env))
                     env
                     evaluated-bindings)])
        (eval-env new-env body))]

    [let*C (bindings body)
     (if (empty? bindings)
         (eval-env env body)
         (let* ([binding (first bindings)]
                [var (fst binding)]
                [val-expr (snd binding)]
                [val (eval-env env val-expr)])
           (eval-env (extend-env (bind var val) env) (let*C (rest bindings) body))))]

    [idC (x) (lookup x env)]

    [listC (exprs) (listV (map (lambda (exp) (eval-env env exp)) exprs))]

    [consC (e1 e2)
     (let [(v1 (eval-env env e1))
           (v2 (eval-env env e2))]
       (type-case Value v2
         [listV (l) (listV (cons v1 l))]
         [else (error 'eval "Second argument to cons must be a list")]))]

    [firstC (e)
     (let [(v (eval-env env e))]
       (type-case Value v
         [listV (l)
          (if (empty? l)
              (error 'eval "Expected a non-empty list in first")
              (first l))]
         [else (error 'eval "Expected a list in first")]))]

    [restC (e)
     (let [(v (eval-env env e))]
       (type-case Value v
         [listV (l)
          (if (empty? l)
              (error 'eval "Expected a non-empty list in rest")
              (listV (rest l)))]
         [else (error 'eval "Expected a list in rest")]))]

    [natrecC (e1 e2 x y e3)
     (let [(v (eval-env env e1))]
       (type-case Value v
         [numV (n)
          (if (= n 0)
              (eval-env env e2)
              (let [(res (eval-env env (natrecC (valC (numV (- n 1))) e2 x y e3)))]
                (eval-env (extend-env (bind x (numV (- n 1)))
                                      (extend-env (bind y res) env))
                          e3)))]
         [else (error 'eval "Expected a number in natrec")]))]

       [listrecC (e1 e2 head rest-list res e3)
                 (let [(v (eval-env env e1))]
                   (type-case Value v
                     [listV (l)
                            (if (empty? l)
                                (eval-env env e2)
                                (let* [(head-val (first l))
                                       (rest-list-val (listV (rest l)))
                                       (rec-result (eval-env env (listrecC (valC rest-list-val) e2 head rest-list res e3)))]
                                  (eval-env (extend-env (bind head head-val)
                                                        (extend-env (bind rest-list rest-list-val)
                                                                    (extend-env (bind res rec-result) env)))
                                            e3)))]
                     [else (error 'eval "Expected a list in listrec")]))]

    [unpackC (vars e1 e2)
     (let [(v (eval-env env e1))]
       (type-case Value v
         [listV (vs)
          (if (= (length vars) (length vs))
              (letrec ([extend-env-recursively
                        (lambda (vars vs acc-env)
                          (if (empty? vars)
                              (eval-env acc-env e2)
                              (let* ([var (first vars)]
                                     [val (first vs)])
                                (extend-env-recursively (rest vars)
                                                        (rest vs)
                                                        (extend-env (bind var val) acc-env)))))])
                (extend-env-recursively vars vs env))
              (error 'eval "Unpack variable count mismatch"))]
         [else (error 'eval "Expected a list in unpack")]))]))


;; Top-level evaluator
(define (eval (e : Expr)) : Value
  (eval-env empty-env e))
