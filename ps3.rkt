#lang plai-typed
(require "ps3-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval-base should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;

;; See ps3-ast.rkt and README.md for more information.

;; Note that as in lecture 6, you probably want to implement a version
;; of eval that returns a result that can be an arbitrary value (not just
;; a BaseValue) and also returns a store.  Your eval-base would then be a
;; wrapper around this more general eval that tries to conver the value
;; to a BaseValue, and fails if it cannot be.
;;
;; For grading, the test cases all result in values that can be converted to base values.

;; Parsing function
(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]  ;
    [(s-exp-list? s)
     (let [(l (s-exp->list s))]
       (cond
         [(s-exp-symbol? (first l))
          (case (s-exp->symbol (first l))
            [(+) (plusC (parse (second l)) (parse (third l)))]
            [(*) (timesC (parse (second l)) (parse (third l)))]
            [(lambda) (lambdaC (s-exp->symbol (second l)) (parse (third l)))]
            [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
            [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(equal?) (equal?C (parse (second l)) (parse (third l)))]
            [(pair) (pairC (parse (second l)) (parse (third l)))]
            [(fst) (fstC (parse (second l)))]
            [(snd) (sndC (parse (second l)))]
            [(box) (boxC (parse (second l)))]
            [(unbox) (unboxC (parse (second l)))]
            [(set-box!) (setboxC (parse (second l)) (parse (third l)))]
            [(begin) (beginC (map parse (rest l)))]
            [(vector) (vectorC (map parse (rest l)))]
            [(vector-length) (vector-lengthC (parse (second l)))]
            [(vector-ref) (vector-refC (parse (second l)) (parse (third l)))]
            [(vector-set!) (vector-set!C (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(vector-make) (vector-makeC (parse (second l)) (parse (third l)))]
            [(subvector) (subvectorC (parse (second l)) (parse (third l)) (parse (fourth l)))]
            [(transact) (transactC (parse (second l)))]
            [else (appC (parse (first l)) (parse (second l)))]
          )]
         [else (appC (parse (first l)) (parse (second l)))]
       ))]
    ))

;; Value type definition
(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [pairV (v1 : Value) (v2 : Value)]
  [closV (env : Env) (x : symbol) (e : Expr)]
  [boxV (l : Location)]
  [vectorV (vec : (vectorof Location))]
  )

;; Location and Store
(define-type-alias Location number)
 
(define-type Storage
  [cell (location : Location) (val : Value)])
 
(define-type-alias Store (listof Storage))
(define empty-store empty)
(define override-store cons)

;; Environment
(define-type Binding
  [bind (name : symbol) (loc : Location)])

(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)

;; Result type for threading store
(define-type Result
  [res (v : Value) (s : Store)])

;; Store operations
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(cons? sto)
     (if (equal? (cell-location (first sto)) l)
         (cell-val (first sto))
         (fetch l (rest sto)))]
    [else (error 'fetch "No location found")]
   ))

(define new-loc
  (let ([counter (box 0)])
    (lambda () 
      (let ([l (unbox counter)])
        (begin (set-box! counter (+ 1 l))
               l)))
    ))

(define (lookup [x : symbol] [env : Env]) : Location
  (cond
    [(cons? env)
     (if (equal? (bind-name (first env)) x)
         (bind-loc (first env))
         (lookup x (rest env)))]
    [else (error 'lookup "No binding found")]
    ))


;; Helper function to convert list of locations into a vector of locations
(define (list->vector-locations [lst : (listof Location)]) : (vectorof Location)
  (letrec ([fill-vector
            (lambda ([lst : (listof Location)] [vec : (vectorof Location)] [idx : number])
              (cond
                [(empty? lst) vec]
                [else
                 (begin
                   (vector-set! vec idx (first lst))
                   (fill-vector (rest lst) vec (+ idx 1)))]))])
    (fill-vector lst (make-vector (length lst) 0) 0)))

;; Helper function to copy elements
(define (subvector-helper [original : (vectorof Location)] 
                         [start : number] 
                         [length : number] 
                         [new-vec : (vectorof Location)] 
                         [i : number]) : (vectorof Location)
  (if (< i length)
      (begin
        (vector-set! new-vec i (vector-ref original (+ start i)))
        (subvector-helper original start length new-vec (+ i 1)))
      new-vec))

(define (eval-env [env : Env] [sto : Store] [e : Expr]) : Result
  (type-case Expr e
    ;; Numeric Boolean and Identifier constants
    [numC (n) (res (numV n) sto)]
    [boolC (b) (res (boolV b) sto)]
    [idC (x) (res (fetch (lookup x env) sto) sto)]
    
    ;; Addition
    [plusC (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2)
           (type-case Value v1
             [numV (n1)
              (type-case Value v2
                [numV (n2) (res (numV (+ n1 n2)) sto-2)]
                [else (error 'eval-env "Expected number")])]
             [else (error 'eval-env "Expected number")])])])]

    ;; Multiplication
    [timesC (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2)
           (type-case Value v1
             [numV (n1)
              (type-case Value v2
                [numV (n2) (res (numV (* n1 n2)) sto-2)]
                [else (error 'eval-env "Expected number")])]
             [else (error 'eval-env "Expected number")])])])]

    ;; App
    [appC (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2)
           (type-case Value v1
             [closV (clos-env x body)
              (let ([l (new-loc)])
                (eval-env (extend-env (bind x l) clos-env)
                          (override-store (cell l v2) sto-2)
                          body))]
             [else (error 'eval-env "Expected closure")])])])]

    ;; Lambda
    [lambdaC (x e) (res (closV env x e) sto)]
    
    ;; Let binding
    [letC (x e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (let ([l (new-loc)])
          (eval-env (extend-env (bind x l) env)
                    (override-store (cell l v1) sto-1)
                    e2))])]

    ;; Box operations
    [boxC (e)
     (type-case Result (eval-env env sto e)
       [res (v sto-1)
        (let ([l (new-loc)])
          (res (boxV l) (override-store (cell l v) sto-1)))])]
    
    [unboxC (e)
     (type-case Result (eval-env env sto e)
       [res (v sto-1)
        (type-case Value v
          [boxV (l) (res (fetch l sto-1) sto-1)]
          [else (error 'eval-env "Expected box")])])]

    [setboxC (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2)
           (type-case Value v1
             [boxV (l) (res v2 (override-store (cell l v2) sto-2))]
             [else (error 'eval-env "Expected box")])])])]

    ;; Pair operations
    [pairC (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2) (res (pairV v1 v2) sto-2)])])]

    [fstC (e)
     (type-case Result (eval-env env sto e)
       [res (v sto-1)
        (type-case Value v
          [pairV (v1 v2) (res v1 sto-1)]
          [else (error 'eval-env "Expected pair")])])]

    [sndC (e)
     (type-case Result (eval-env env sto e)
       [res (v sto-1)
        (type-case Value v
          [pairV (v1 v2) (res v2 sto-1)]
          [else (error 'eval-env "Expected pair")])])]

    ;; Conditionals
    [ifC (guard e1 e2)
     (type-case Result (eval-env env sto guard)
       [res (v sto-1)
        (type-case Value v
          [boolV (b) (if b (eval-env env sto-1 e1) (eval-env env sto-1 e2))]
          [else (error 'eval-env "Expected boolean")])])]

    ;; Equality check
    [equal?C (e1 e2)
     (type-case Result (eval-env env sto e1)
       [res (v1 sto-1)
        (type-case Result (eval-env env sto-1 e2)
          [res (v2 sto-2) (res (boolV (equal? v1 v2)) sto-2)])])]

    ;; Vector operations
   [vectorC (es)
     (letrec ([allocate-elements
            (lambda ([remaining : (listof Expr)] 
                    [store : Store] 
                    [acc : (listof Location)])
              (if (empty? remaining)
                  (res (vectorV (list->vector-locations (reverse acc))) store)
                  (type-case Result (eval-env env store (first remaining))
                    [res (v sto-1)
                     (let ([l (new-loc)])
                       (allocate-elements (rest remaining)
                                        (override-store (cell l v) sto-1)
                                        (cons l acc)))])))])
    (allocate-elements es sto empty))]

    [vector-lengthC (e)
     (type-case Result (eval-env env sto e)
       [res (v sto-1)
        (type-case Value v
          [vectorV (vec) (res (numV (vector-length vec)) sto-1)]
          [else (error 'eval-env "Expected vector")])])]

    [vector-refC (vec-expr index-expr)
     (type-case Result (eval-env env sto vec-expr)
       [res (vec-value sto-1)
        (type-case Result (eval-env env sto-1 index-expr)
          [res (index-value sto-2)
           (type-case Value vec-value
             [vectorV (vec)
              (type-case Value index-value
                [numV (index)
                 (if (and (>= index 0) (< index (vector-length vec)))
                     (res (fetch (vector-ref vec index) sto-2) sto-2)
                     (error 'eval-env "Index out of bounds"))]
                [else (error 'eval-env "Expected numeric index")])]
             [else (error 'eval-env "Expected vector")])])])]

    [vector-set!C (vec-expr index-expr val-expr)
     (type-case Result (eval-env env sto vec-expr)
       [res (vec-val sto-1)
        (type-case Value vec-val
          [vectorV (vec)
           (type-case Result (eval-env env sto-1 index-expr)
             [res (index-val sto-2)
              (type-case Value index-val
                [numV (index)
                 (if (and (>= index 0) (< index (vector-length vec)))
                     (type-case Result (eval-env env sto-2 val-expr)
                       [res (new-val sto-3)
                        (let ([loc (vector-ref vec index)])
                          (res new-val (override-store (cell loc new-val) sto-3)))])
                     (error 'eval-env "Index out of bounds"))]
                [else (error 'eval-env "Expected numeric index")])])]
          [else (error 'eval-env "Expected vector")])])]

    
   [vector-makeC (e1 e2)
     (let* ([res1 (eval-env env sto e1)]
            [res2 (eval-env env (res-s res1) e2)])
       (type-case Value (res-v res1)
         [numV (n)
          (if (>= n 0)
           (letrec ([generate-locs
                      (lambda (count acc)
                        (if (zero? count)
                            acc
                            (generate-locs (sub1 count) (cons (new-loc) acc))))])
             (let* ([locs (generate-locs n empty)]
                    [init-val (res-v res2)]
                    [new-store
                     (foldl (λ (loc acc-store)
                             (override-store (cell loc init-val) acc-store))
                           (res-s res2) locs)])
               (res (vectorV (list->vector-locations locs)) new-store)))
           (error 'eval-env "Expected Positive Vector Size"))]
      [else (error 'eval-env "Expected numeric value")]))]


    [subvectorC (vec-expr start-expr length-expr)
     (type-case Result (eval-env env sto vec-expr)
       [res (vec-val sto-1)
        (type-case Value vec-val
          [vectorV (vec)
           (type-case Result (eval-env env sto-1 start-expr)
             [res (start-val sto-2)
              (type-case Value start-val
                [numV (start)
                 (type-case Result (eval-env env sto-2 length-expr)
                   [res (length-val sto-3)
                    (type-case Value length-val
                      [numV (length)
                       (if (and (>= start 0) (>= length 0) (<= (+ start length) (vector-length vec)))
                           (let ([new-vec (make-vector length 0)])
                             (res (vectorV (subvector-helper vec start length new-vec 0)) sto-3))
                           (error 'eval-env "Subvector indices out of bounds"))]
                      [else (error 'eval-env "Expected numeric length")])])]
                [else (error 'eval-env "Expected numeric start")])])]
          [else (error 'eval-env "Expected vector")])])]

    ;; Begin expressions
    [beginC (es)
     (local [(define (eval-exprs es env sto)
               (if (empty? es)
                   (error 'eval-env "Begin requires at least one expression")
                   (if (empty? (rest es))
                       (eval-env env sto (first es))
                       (type-case Result (eval-env env sto (first es))
                         [res (v sto-1) (eval-exprs (rest es) env sto-1)]))))]
       (eval-exprs es env sto))]

    ;; Transaction
    [transactC (e)
     (let ([old-sto sto])
       (type-case Result (eval-env env sto e)
         [res (v sto-1)
          (type-case Value v
            [pairV (v1 v2)
             (type-case Value v1
               [boolV (b) (if b (res v2 sto-1) (res v2 old-sto))]
               [else (error 'eval-env "Expected boolean")])]
            [else (error 'eval-env "Expected pair")])]))]
    ))


;; Main function to evaluate a parsed expressio
(define (eval-base [e : Expr]) : BaseValue
  (type-case Result (eval-env empty-env empty-store e)
    [res (v s)
     (convert-to-basevalue v)]))

;; Helper function that converts values to base values
(define (convert-to-basevalue [v : Value]) : BaseValue
  (type-case Value v
    [numV (n) (numBV n)]
    [boolV (b) (boolBV b)]
    [pairV (v1 v2) (pairBV (convert-to-basevalue v1) (convert-to-basevalue v2))]
    [vectorV (vec) 
     (error 'eval-base "Cannot convert vector to BaseValue")]
    [else (error 'eval-base "Conversion to BaseValue not supported for this type")]))