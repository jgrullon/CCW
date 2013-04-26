#lang plai-typed

(require "typed-lang.rkt")
 
(define (make-ids (n : number)) : (listof symbol)
  (build-list n (lambda (n) (string->symbol (string-append "var-" (to-string n))))))

;; cascade-lets will build up the nested lets, and use body as the
;; eventual body, preserving order of evaluation of the expressions
(define (cascade-lets (ids : (listof symbol))
                      (exprs : (listof ExprC))
                      (body : ExprC)) : ExprC
  (cond [(empty? ids) body]
        [(cons? ids)
         (LetC (first ids) (first exprs) (cascade-lets (rest ids) (rest exprs) body))]))

;; check-type builds an expression that checks the type of the expression
;; given as an argument
(define (check-type (expr : ExprC) (type : string)) : ExprC
  (Prim2C '== (Prim1C 'tagof expr) (StrC type)))

;; and builds up an and expression from its two pieces
(define (and (expr1 : ExprC) (expr2 : ExprC)) : ExprC
  (IfC expr1 expr2 (FalseC)))

;; all builds up a series of ands over the expression arguments
(define (all (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (exp result) (and exp result)) (TrueC) exprs))

;; map-subtract builds an expression that maps 'num- over a list of expressions
(define (map-subtract (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'num- result expr)) (first exprs) (rest exprs)))

(define (map-add (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'num+ result expr)) (first exprs) (rest exprs)))

(define (map-addstr (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'string+ result expr)) (first exprs) (rest exprs)))

(define (map-lessthan (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C '< result expr)) (first exprs) (rest exprs)))

(define (map-greaterthan (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C '> result expr)) (first exprs) (rest exprs)))

(define (map-equal (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C '== result expr)) (first exprs) (rest exprs)))

;-----------------------------------------------------------------------------------------

(define (desugar-subtract (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
      (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
           (map-subtract id-exps)
           (ErrorC (StrC "Bad arguments to -"))))))

(define (desugar-add (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
                  (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
                       (map-add id-exps)
                       (IfC (all (map (lambda (t) (check-type t "string")) id-exps))
                            (map-addstr id-exps)
                            (ErrorC (StrC "Bad arguments to +")))))))

;PrimP case, op <
(define (desugar-lessthan (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
                  (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
                       (map-lessthan id-exps)
                       (ErrorC (StrC "Bad arguments to <"))))))

; PrimP case, op >
(define (desugar-greaterthan (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
                  (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
                       (map-greaterthan id-exps)
                       (ErrorC (StrC "Bad arguments to >"))))))

(define (desugar-equal (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args) (map-equal id-exps))))


; Used in lamP case
(define (desugar_args [args : (listof ExprP)]) : (listof ExprC)
  (cond
    [(empty? args) empty]
    [else
     (cons (desugar (first args)) (desugar_args (rest args)))])) 

; Desugar SeqP Como hago esto? que debo devolver en mi caso base?
(define (desugar-Seq [args : (listof ExprP)]) : ExprC
  (cond
    [( = 1 (length args)) (desugar (first args))]
    [else
     (SeqC (desugar (first args)) (desugar-Seq (rest args)))]))


; Used in ObjectP case
(define (desugar_Fields [fields : (listof FieldP)]) : (listof FieldC)
  (if (empty? fields) empty
      (let ([myname (fieldP-name (first fields))]
            [myval (fieldP-value (first fields))])
      (cons (fieldC myname (desugar myval)) (desugar_Fields (rest fields))))))  

(define (combine [var : symbol] [num : number]) : (listof ExprP)
  (list (IdP var) (NumP num))) 

;-------------------------------------------------------------------------------------------
(define (desugar (exprP : ExprP)) : ExprC
  (type-case ExprP exprP

    [TrueP () (TrueC)] ;ya
    [FalseP () (FalseC)] ;ya
    [NumP (n) (NumC n)] ; ya
    [StrP (s) (StrC s)] ; ya
    [IdP (sym) (IdC sym)] 
    [AppP (fun args) (AppC (desugar fun) (desugar_args args))] ; Como lo verifico? Creo que ya esta pero hay que ver
    [IfP (test e1 e2) (IfC (desugar test) (desugar e1) (desugar e2))] ; ya
    [FuncP (Lsym mybody) (FuncC Lsym (desugar mybody))] ; Como lo verifico? ya
    [ObjectP (fields) (ObjectC (desugar_Fields fields))] ;Como lo verifico? ya
    [DotP (obj myfield) (GetFieldC (desugar obj) (StrC (symbol->string myfield)))]
    [BracketP (obj myfield) (GetFieldC (desugar obj) (desugar myfield))]
    [DotMethodP (obj myfield args) (AppC (GetFieldC (desugar obj) (StrC (symbol->string myfield))) (desugar_args args))]
    [BrackMethodP (obj myfield args) (AppC (GetFieldC (desugar obj) (desugar myfield)) (desugar_args args))]
    [SeqP (listP) (desugar-Seq listP)]
    [DefvarP (id bind body) (LetC id (desugar bind) (desugar body))]
    [DeffunP (name ids funbody body) (LetC name (FuncC ids (desugar funbody)) (desugar body))]
    [PreIncP (sym) (Set!C sym (Prim2C 'num+ (IdC sym) (NumC 1)))]
    [PreDecP (sym) (Set!C sym (Prim2C 'num- (IdC sym) (NumC 1)))]
    [TryCatchP (body param catch) (TryCatchC (desugar body) param (desugar catch))]
    [RaiseP (exn) (RaiseC (desugar exn))]
    [PrimAssignP (op lhs val)
                 (type-case LHS lhs
                   [IdLHS (sym)
                          (LetC 'IdLHS-val (desugar val)
                                (case op
                                  ['+
                                   (IfC (check-type (IdC 'IdLHS-val) "string")
                                        (Set!C sym (Prim2C 'string+ (IdC sym) (IdC 'IdLHS-val)))
                                        (Set!C sym (Prim2C 'num+ (IdC sym) (IdC 'IdLHS-val))))]
                                  ['- (Set!C sym (Prim2C 'num- (IdC sym) (IdC 'IdLHS-val)))]))]
                   [BracketLHS (obj field)
                               (LetC 'BLHS-obj (desugar obj)
                                     (LetC 'BLHS-val (desugar val)
                                           (LetC 'BLHS-field (desugar field)
                                                 (case op
                                                   ['+  (IfC (check-type (IdC 'BLHS-val) "number")
                                                             (SetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field) (Prim2C 'num+ (GetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field)) (IdC 'BLHS-val)))
                                                             (SetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field) (Prim2C 'string+ (GetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field)) (IdC 'BLHS-val))))]
                                                   ['- (SetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field) (Prim2C 'num- (GetFieldC (IdC 'BLHS-obj) (IdC 'BLHS-field)) (IdC 'BHLS-val)) )]))))]
                   [DotLHS (obj field)
                           (LetC 'dot-lhsobj (desugar obj)
                                       (LetC 'dot-lhsval (desugar val)
                                             (case op
                                               ['+ 
                                                (IfC (check-type (IdC 'dot-lhsval) "string")
                                                     (SetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field)) (Prim2C 'string+ (GetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field))) (IdC 'dot-lhsval)))
                                                     (SetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field)) (Prim2C 'num+ (GetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field))) (IdC 'dot-lhsval))))]                  
                                                     ['- (SetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field)) (Prim2C 'num- (GetFieldC (IdC 'dot-lhsobj) (StrC (symbol->string field))) (IdC 'dot-lhsval)))])))])]
    [PostIncP (sym) (LetC 'p-inc (IdC sym)
                          (SeqC (Set!C sym (Prim2C 'num+ (IdC sym) (NumC 1)))
                                (IdC 'p-inc)))]
    [PostDecP (sym) (LetC 'p-dec (IdC sym)
                          (SeqC (Set!C sym (Prim2C 'num- (IdC sym) (NumC 1)))
                                (IdC 'p-dec)))]
    
    [AssignP (lhs val)
             (type-case LHS lhs
               [DotLHS (obj sym) (SetFieldC (desugar obj) (StrC (symbol->string sym)) (desugar val))]
               [IdLHS (sym) (Set!C sym (desugar val))]
               [BracketLHS (obj field) (SetFieldC (desugar obj) (desugar field) (desugar val))])]
            ;   [else (error 'sym "Que no se hacerlo!")])] 
    ;; Fill in more cases here...

    [PrimP (op args) ;Prim2C ok, ya Prim1C
        (case op
          ['- (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(< 0 (length args)) (desugar-subtract args)])]
          ['+ (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(< 0 (length args)) (desugar-add args)])]
          ['< (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(not (= 2 (length args))) (ErrorC (StrC "Bad primop"))]
                [else (desugar-lessthan args)])]
          ['> (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(not (= 2 (length args))) (ErrorC (StrC "Bad primop"))]
                [else (desugar-greaterthan args)])]
          ['== (cond
                [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                [(not (= 2 (length args))) (ErrorC (StrC "Bad primop"))]
                [else (desugar-equal args)])]
          ['print (cond 
                    [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                    [(not (= 1 (length args))) (ErrorC (StrC "Bad primop"))]
                    [else (Prim1C 'print (desugar (first args)))])]
          ['tagof (cond
                    [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
                    [(not (= 1 (length args))) (ErrorC (StrC "Bad primop"))]
                    [else (Prim1C 'tagof (desugar (first args)))])]                 
          )]
    

    [WhileP (test body)
          ;; dummy-fun will tell us it was called if we do so accidentally
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
          (IfC (desugar test)

               ;; while-var will hold the actual function once we tie
               ;; everything together
               (LetC 'while-var dummy-fun
                 (LetC 'while-func

                   ;; this function does the real work - it runs the body of
                   ;; the while loop, then re-runs it if the test is true, and
                   ;; stops if its false
                   (FuncC (list)
                     (LetC 'temp-var
                       (desugar body)
                       (IfC (desugar test)
                            (AppC (IdC 'while-var) (list))
                            (IdC 'temp-var))))

                   ;; The Set!C here makes sure that 'while-var will resolve
                   ;; to the right value later, and the AppC kicks things off
                   (SeqC (Set!C 'while-var (IdC 'while-func))
                         (AppC (IdC 'while-var) (list)))))

               (FalseC)))]
     
    [ForP (init test update body)
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
            (LetC 'for-var (desugar init)
                  (IfC (desugar test) 
                       ;; while-var will hold the actual function once we tie
                       ;; everything together
                       (LetC 'f-var dummy-fun
                             (LetC 'for-func

                                   ;; this function does the real work - it runs the body of
                                   ;; the while loop, then re-runs it if the test is true, and
                                   ;; stops if its false
                                   (FuncC (list)
                                          (LetC 'temp-forvar (desugar body)
                                                
                                                (SeqC (desugar update)                           
                                                      (IfC (desugar test)
                                                           (AppC (IdC 'f-var) (list))
                                                           (IdC 'temp-forvar)))))
                                   ;; The Set!C here makes sure that 'while-var will resolve
                   ;; to the right value later, and the AppC kicks things off
                                 (SeqC (Set!C 'f-var (IdC 'for-func))
                                       (AppC (IdC 'f-var) (list)))))
                 
                 
                 
          (IdC 'for-var))))]
    
    [else (ErrorC (StrC (string-append "Haven't desugared a case yet:\n"
                                       (to-string exprP))))]))

(print-only-errors true)
(test (desugar (StrP "Dembow")) (StrC "Dembow"))
(test (desugar (NumP 0987654321)) (NumC 0987654321))
(test (desugar (IdP 'x)) (IdC 'x))
(test (desugar (TrueP)) (TrueC))
(test (desugar (FalseP)) (FalseC))
(test (desugar (IfP (TrueP) (StrP "it works") (StrP "ohoh! problems"))) (IfC (TrueC) (StrC "it works") (StrC "ohoh! problems")))
(test (desugar (FuncP (list 'x 'y) (NumP 5))) (FuncC (list 'x 'y) (NumC 5)))
