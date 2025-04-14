#lang plai-typed
(require "ps4-ast.rkt")

;; TODO: Implement the following two functions.
;;
;; parse should take an s-expression representing a program and return an
;; AST corresponding to the program.
;;
;; eval-base should take an expression e (i.e. an AST) and evaluate e,
;; returning the resulting value.
;;

;; See ps4-ast.rkt and README.md for more information.

;; Note that as in the previous problem set you probably want to implement a version
;; of eval that can return more general values and takes an environment / store as arguments.
;; Your eval-base would then be a wrapper around this more general eval that tries to conver the value
;; to a BaseValue, and fails if it cannot be converted.
;;
;; For grading, the test cases all result in values that can be converted to base values.

;; Function to parse s-expressions into the Expr AST
(define (parse (s : s-expression)) : Expr
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-list? s)
      (let [(l (s-exp->list s))]
        (cond
          [(s-exp-symbol? (first l))
            (case (s-exp->symbol (first l))
              [(+) (plusC (parse (second l)) (parse (third l)))]
              [(*) (timesC (parse (second l)) (parse (third l)))]
              [(equal?) (equal?C (parse (second l)) (parse (third l)))]
              [(if) (ifC (parse (second l)) (parse (third l)) (parse (fourth l)))]
              [(let) (letC (s-exp->symbol (second l)) (parse (third l)) (parse (fourth l)))]
              [(lambda) (lambdaC (s-exp->symbol (second l)) (parse (third l)))]
              [(begin) (beginC (map parse (rest l)))]
              [(msg) (let [(obj (parse (second l)))
                (method (s-exp->symbol (third l)))
                (args (map parse (rest (rest (rest l)))))]
                  (msgC obj method args))]
              [(get-field) (get-fieldC (s-exp->symbol (second l)))]
              [(set-field!) (set-field!C (s-exp->symbol (second l)) (parse (third l)))]
              [(object) (let [(fields (s-exp->list (second l)))
                (methods (s-exp->list (third l)))]
              (objectC (none)
                (parse-f fields)
                (parse-m methods))
              )]
              [(object-del) (let [(obj (parse (second l)))
                (fields (s-exp->list (third l)))
                (methods (s-exp->list (fourth l)))]
                  (objectC (some obj)
                  (parse-f fields)
                  (parse-m methods))
              )]
              [else (appC (parse (first l)) (parse (second l)))]
            )]
          [else (appC (parse (first l)) (parse (second l)))]
        ))]
  ))

;;Helper functions to parse the fields and methods of an object
(define (parse-f (ls : (listof s-expression))) : (listof (symbol * Expr))
  (map (lambda (field)
    (pair (s-exp->symbol (first (s-exp->list field))) (parse (second (s-exp->list field))))) ls))

(define (parse-m (ls : (listof s-expression))) : (listof MethodDecl)
  (map (lambda (method) (let [(methodls (s-exp->list method))] 
      (method-decl (s-exp->symbol (first methodls))
        (map s-exp->symbol (rest (s-exp->list (second methodls))))
        (parse (third methodls))))) ls))

;; Value types for our evaluator
(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closV (env : Env) (x : symbol) (e : Expr)]
  [objV (delegate : (optionof Value))
        (fields : (listof (symbol * Location)))
        (methods : (listof MethodValue))])

(define-type MethodValue
  [methodV (name : symbol) (args : (listof symbol)) (body : Expr) (env : Env)])

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define (lookup [x : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup (string-append "No binding found for " (symbol->string x)))]
    [else
     (let ([binding (first env)])
       (if (symbol=? (bind-name binding) x)
           (bind-val binding)
           (lookup x (rest env))))]))

(define new-loc
  (let ([counter (box 0)])
    (lambda () 
      (let ([l (unbox counter)])
        (begin (set-box! counter (+ 1 l))
               l)))))

(define-type-alias Location number)

(define-type-alias Env (listof Binding))

(define mt-env empty)
(define extend-env cons)

(define-type ReturnVal
  [retval (v : Value) (s : Store)])

;; Store type definition
(define-type Store
  [store (content : (listof (Location * Value)))])

(define (store-lookup [s : Store] [loc : Location]) : Value
  (let ([matches (filter (lambda ([p : (Location * Value)]) (= loc (fst p)))
                         (store-content s))])
    (if (empty? matches)
        (error 'store-lookup "Location not found")
        (snd (first matches)))))

(define (store-update [s : Store] [loc : Location] [v : Value]) : Store
  (store (cons (pair loc v)
               (filter (lambda ([p : (Location * Value)]) 
                         (not (= loc (fst p))))
                       (store-content s)))))

(define (new-store) : Store
  (store empty))

;; Helper function to zip two lists into a list of pairs
(define (zip [lst1 : (listof (symbol * Expr))] [lst2 : (listof Location)])
  : (listof ((symbol * Expr) * Location))
  (cond
    [(or (empty? lst1) (empty? lst2)) empty]
    [else
     (cons (pair (first lst1) (first lst2))
           (zip (rest lst1) (rest lst2)))]))

(define-type ObjContinuation
  [noObjK]
  [withObjK (current-obj : Value) (rest : ObjContinuation)])

;; Continuation types
(define-type Contin
  [haltK]
  [plusLK (e : Expr) (env : Env) (k : Contin)]
  [plusRK (v : Value) (env : Env) (k : Contin)]
  [timesLK (e : Expr) (env : Env) (k : Contin)]
  [timesRK (v : Value) (env : Env) (k : Contin)]
  [equalLK (e : Expr) (env : Env) (k : Contin)]
  [equalRK (v : Value) (env : Env) (k : Contin)]
  [appLK (e : Expr) (env : Env) (k : Contin)]
  [appRK (v : Value) (env : Env) (k : Contin)]
  [letK (x : symbol) (e2 : Expr) (env : Env) (k : Contin)]
  [ifK (then-branch : Expr) (else-branch : Expr) (env : Env) (k : Contin)]
  [getFieldK (field : symbol) (env : Env) (k : Contin)]
  [setFieldK (field : symbol) (val : Expr) (env : Env) (k : Contin)]
  [setFieldRK (field : symbol) (value : Value) (env : Env) (k : Contin)]
  [seqK (rest-exprs : (listof Expr)) (env : Env) (k : Contin)]
  [msgK (method : symbol) (args : (listof Expr)) (env : Env) (k : Contin)])

;;Applying continuations method
(define (apply-contin [k : Contin] [v : Value] [store : Store] [objk : ObjContinuation]) : ReturnVal
  (type-case Contin k
    [haltK () (retval v store)]
    [plusLK (e env k) (eval-env env store e objk (plusRK v env k))]
    [plusRK (v1 env k)
     (let ([new-value (numV (+ (numV-n v1) (numV-n v)))])
       (apply-contin k new-value store objk))]
    [timesLK (e env k) (eval-env env store e objk (timesRK v env k))]
    [timesRK (v1 env k)
     (let ([new-value (numV (* (numV-n v1) (numV-n v)))])
       (apply-contin k new-value store objk))]
    [equalLK (e env k) (eval-env env store e objk (equalRK v env k))]
    [equalRK (v1 env k)
     (let ([new-value (boolV (equal? v1 v))])
       (apply-contin k new-value store objk))]
    [appLK (e env k) (eval-env env store e objk (appRK v env k))]
    [appRK (v1 env k)
     (type-case Value v1
       [closV (closure-env param body)
              (eval-env (extend-env (bind param v) closure-env) store body objk k)]
       [else (error 'appRK "Expected a function")])]
    [letK (x e2 env k)
     (let ([new-env (extend-env (bind x v) env)])
       (eval-env new-env store e2 objk k))]
    [ifK (then-branch else-branch env k)
     (type-case Value v
       [boolV (b)
        (if b
            (eval-env env store then-branch objk k)
            (eval-env env store else-branch objk k))]
       [else (error 'ifK "Expected a boolean")])]
    [getFieldK (field env k)
           (type-case ObjContinuation objk
             [noObjK () (error 'apply-contin "No object for field access")]
             [withObjK (curr-obj rest-objk)
                       (type-case Value curr-obj
                         [objV (delegate fields methods)
                               (let ([field-loc (find-field fields field)])
                                 (if (some? field-loc)
                                     (apply-contin k (store-lookup store (some-v field-loc)) store rest-objk)
                                     (if (some? delegate)
                                         (apply-contin (getFieldK field env k) 
                                                     (some-v delegate) 
                                                     store 
                                                     (withObjK (some-v delegate) rest-objk))
                                         (error 'getFieldK (string-append "Field not found: " 
                                                                        (symbol->string field))))))]
                         [else (error 'getFieldK "Not an object")])])]
    [setFieldK (field val env k)
               (type-case ObjContinuation objk
                 [noObjK () (error 'apply-contin "No object for field update")]
                 [withObjK (curr-obj rest-objk)
                           (let ([result (eval-env env store val objk (haltK))])
                             (let ([evaluated-val (retval-v result)])
                               (apply-contin (setFieldRK field evaluated-val env k) curr-obj store rest-objk)))])]
    [setFieldRK (field value env k)
            (type-case ObjContinuation objk
              [noObjK () (error 'apply-contin "No object for field update")]
              [withObjK (curr-obj rest-objk)
                        (type-case Value curr-obj
                          [objV (delegate fields methods)
                                (let ([field-loc (find-field fields field)])
                                  (if (some? field-loc)
                                      (let ([new-store (store-update store (some-v field-loc) value)])
                                        (apply-contin k curr-obj new-store rest-objk))
                                      (if (some? delegate)

                                          (apply-contin (setFieldRK field value env k) 
                                                      (some-v delegate) 
                                                      store 
                                                      (withObjK (some-v delegate) rest-objk))
                                          (error 'setFieldRK "Field not found"))))]
                          [else (error 'setFieldK "Not an object")])])]
     [msgK (method args env k)
      (type-case Value v
        [objV (delegate fields methods)
              (let ([method-opt (find-method v method)])
                (if (some? method-opt)
                    (let* ([method-val (some-v method-opt)]
                           [method-env (methodV-env method-val)]
                           [method-args (methodV-args method-val)]
                           [method-body (methodV-body method-val)]
                           [evaluated-args 
                            (map (lambda ([arg : Expr]) 
                                   (retval-v (eval-env env store arg objk (haltK))))
                                 args)]
                           [method-env-with-self (extend-env (bind 'self v) method-env)]
                           [full-env (createmethodenv method-args evaluated-args method-env-with-self)])
                      (eval-env full-env store method-body (withObjK v objk) k))
                    (if (some? delegate)
                        (apply-contin (msgK method args env k) 
                                    (some-v delegate) 
                                    store 
                                    objk)
                        (error 'msgK (string-append "Method not found: " 
                                                  (symbol->string method))))))]
        [else (error 'msgK "Expected an object")])]
    [seqK (rest-exprs env k)
     (eval-sequence env store rest-exprs objk k)]
    ))

;; Helper function to create the full environment for a method
(define (createmethodenv [syms : (listof symbol)] [vals : (listof Value)] [existing : Env]) : Env
  (if (empty? syms)
      existing
      (createmethodenv (rest syms) (rest vals) (extend-env (bind (first syms) (first vals)) existing)))
  )

;; Helper function to find methods in an object
(define (find-method [obj : Value] [method-name : symbol]) : (optionof MethodValue)
  (type-case Value obj
    [objV (delegate fields methods)
     (let ([matches (filter (lambda (m) (symbol=? (methodV-name m) method-name))
                          methods)])
       (if (empty? matches)
           (if (some? delegate)
               (find-method (some-v delegate) method-name)
               (none))
           (some (first matches))))]
    [else (none)]))

;; Helper function to find field location in an object
(define (find-field [fields : (listof (symbol * Location))] [field : symbol]) 
  : (optionof Location)
  (cond
    [(empty? fields) (none)]
    [(symbol=? (fst (first fields)) field) (some (snd (first fields)))]
    [else (find-field (rest fields) field)]))

;; Helper function to update field in an object
(define (update-field [fields : (listof (symbol * Location))] [field : symbol] [loc : Location])
  : (listof (symbol * Location))
  (cond
    [(empty? fields) (list (pair field loc))]
    [else
     (let ([first-field (first fields)])
       (if (symbol=? (fst first-field) field)
           (cons (pair field loc) (rest fields))
           (cons first-field (update-field (rest fields) field loc))))]))

;; Function to look up value at a location
(define (fetch [loc : Location] [store : Store]) : Value
  (store-lookup store loc))

;; Main evaluation function
(define (eval-env [env : Env] [store : Store] [e : Expr] [objk : ObjContinuation] [k : Contin]) : ReturnVal
  (type-case Expr e
    [numC (n) (apply-contin k (numV n) store objk)]
    [boolC (b) (apply-contin k (boolV b) store objk)]
    [idC (x) (apply-contin k (lookup x env) store objk)]
    [plusC (e1 e2) (eval-env env store e1 objk (plusLK e2 env k))]
    [timesC (e1 e2) (eval-env env store e1 objk (timesLK e2 env k))]
    [equal?C (e1 e2) (eval-env env store e1 objk (equalLK e2 env k))]
    [ifC (guard e1 e2)
         (eval-env env store guard objk (ifK e1 e2 env k))]
    [letC (x e1 e2)
          (eval-env env store e1 objk (letK x e2 env k))]
    [appC (fun arg) (eval-env env store fun objk (appLK arg env k))]
    [lambdaC (x body) (apply-contin k (closV env x body) store objk)]
    [objectC (delegate fields methods)
             (let* ([delegate-val (if (some? delegate)
                                      (let ([result (eval-env env store (some-v delegate) objk (haltK))])
                                        (some (retval-v result)))
                                      (none))]
                    [locs (map (lambda (_) (new-loc)) fields)]
                    [field-loc-pairs
                     (map (lambda (p)
                            (pair (fst (fst p)) (snd p)))
                          (zip fields locs))]
                    [new-store
                     (foldr (lambda (p s)
                              (let ([val-result (eval-env env s (snd (fst p)) objk (haltK))])
                                (store-update s (snd p) (retval-v val-result))))
                            store
                            (zip fields locs))]
                    [method-vals
                     (map (lambda (m)
                            (methodV (method-decl-name m)
                                     (method-decl-args m)
                                     (method-decl-body m)
                                     env))
                          methods)])
               (apply-contin k 
                             (objV delegate-val field-loc-pairs method-vals) 
                             new-store 
                             objk))]
    [beginC (exprs) (eval-sequence env store exprs objk k)]
    [get-fieldC (field)
      (let ([obj (lookup 'self env)])
        (type-case Value obj
          [objV (delegate fields methods)
                (apply-contin (getFieldK field env k) obj store (withObjK obj objk))]
          [else (error 'get-fieldC "Expected an object")]))]
    [set-field!C (field val)
      (let ([obj (lookup 'self env)])
        (eval-env env store val (withObjK obj objk) (setFieldK field val env k)))]
    [msgC (obj method args)
      (eval-env env store obj objk (msgK method args env k))]
    ))

;; Function to evaluate a sequence of expressions using continuations 
(define (eval-sequence [env : Env] [store : Store] [exprs : (listof Expr)] [objk : ObjContinuation] [k : Contin]) : ReturnVal
  (cond
    [(empty? exprs) (apply-contin k (boolV #t) store objk)]
    [(empty? (rest exprs))
     (eval-env env store (first exprs) objk k)]
    [else
     (eval-env env store (first exprs) objk (seqK (rest exprs) env k))]))

(define (convert-to-base [v : Value]) : BaseValue
  (type-case Value v
    [numV (n) (numBV n)]
    [boolV (b) (boolBV b)]
    [else (error 'convert-to-base "Cannot convert to BaseValue")]))

;; Entry point function
(define (eval-base [expr : Expr]) : BaseValue
  (let* ([result (eval-env mt-env (new-store) expr (noObjK) (haltK))]
         [value (retval-v result)])
    (convert-to-base value)))