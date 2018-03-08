#lang racket
(require racket/trace)
(require "program.rkt")
;;(require "testcases.rkt")
(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eval
;; input: program-expression, environment as list of pairs (variable value)
;; output: '(Cannot Evaluate) or a number


(define (eval expr env heap)
  (if (caneval env)      ;; the environment might end up with a pair (variable '(Cannot Evaluate))
      (cond
        [ (number? expr) (cons expr (list heap)) ]  ;; number is this how we make the new return??
        [ (symbol? expr) (findvalue expr env heap) ] ;; sigma(x)

        ;; implementation of the semantics of variable expression
        [ (equal? (car expr) 'var)
          (if ( > (length (cadr expr)) 1)
              (eval (translateExpression 'var (cadr expr) (cadr (cdr expr))) env heap)  ;;Translate a multiple var expression into different Vars - adegala 
          (evalvarassign (cadr expr) (cadr (cdr expr)) env heap)) ]

        ;; implementation of the semantics of FExpr
        [ (equal? (car expr) 'fun) (eval (cadr (cdr expr)) (cons (cadr expr) env) heap)  ]

        ;; implementation of the semantics of Apply
        ;; utter disregard for efficiency - searching the same environment three times using the same key
        ;; But this keeps it clean
        ;; We are going to translate the apply semantics to varexpression semantics
        ;; [[(apply (f (ArgList)))]]_env = [[(var Param-ArgValue list  FDef]]_staticenv
        [ (equal? (car expr) 'apply) (eval (list 'var
                                                 (paramargs (findfunparams (car (cadr expr))  ;; function name
                                                                           (length (cadr (cadr expr))) ;; number of params
                                                                           env)              ;; current environment
                                                            ;; findfunparams returns parameters of the function
                                                            (cadr (cadr expr)) ;; expressions representing arguments   ;;Just pass expr for dynamic - adegala
                                                            env)
                                                 ;; paramargs returns the list of variable-value pairs
                                                 
                                                 (findfundef (car (cadr expr)) (length (cadr (cadr expr))) env)) ;; definition of the function
                                           env ;;Just passing enviorment - adegala 
                                           ;;(staticenv (car (cadr expr)) (length (cadr (cadr expr))) env) ;; static environment  ;;Just pass enviorment for dynamic - adegala
                                           heap
                                           ) ]
        ;;Deref   
        [ (equal? (car expr) 'deref) (evalDeref (car(cdr expr)) env heap)]
        ;;Ref
        [ (equal? (car expr) 'ref) (evalRef (car(cdr expr)) env heap)]
        ;;Free
        [ (equal? (car expr) 'free) (evalFree (car(cdr expr)) env heap)]
        ;;Wref
        [ (equal? (car expr) 'wref) (evalWref (car(cdr expr)) (car(cdr(cdr expr))) env heap)]

        ;; same as before with the arithmatic operations: environment is added
        [ (arithop (car expr)) (evalarith (car expr) (cadr expr) (cadr (cdr expr)) env heap)  ]
        
        ;; ifthenelse function
        [ else  (ifthenelse (evalcond (car expr) env heap) 
                            (cadr expr)
                            (cadr (cdr expr)) env

                            (car (cdr (evalcond (car expr) env heap)))) ]
        )
      '(Cannot Evaluate)
      ))
(trace eval)

;;Eval Deref, does it depend on the heap?
;;Return value & heap  ;;Am I returning the heap right?
(define (evalDeref expr env heap)
  (cond
    [(equal? (readFromLocation (car (eval expr env heap)) heap) '(exception fma))
     (cons '(exception fma) (list heap))]
    [(equal? (readFromLocation (car (eval expr env heap)) heap) '(exception ooma))
     (cons '(exception ooma) (list heap))]
    [else
  (cons (readFromLocation (car(eval expr env heap)) heap) (list heap) )]
  )
 )

;;Eval ref
;;Write to location is ( heap location data )
(define (evalRef expr env heap)
  (cond
    [(equal? (findFreeLocation heap) '(exception oom))
     (cons '(exception oom) (list heap))]
    [else
     (cons (findFreeLocation heap) (list(writeToLocation heap (findFreeLocation heap) (car(eval expr env heap)) )))]
    )
  )
;;(trace evalRef)
;;Eval Free
(define (evalFree expr env heap)
  (cond 
  [(equal? (readFromLocation (car (eval expr env heap)) heap) '(exception fma))
     (cons '(exception fma) (list heap))]
    [(equal? (readFromLocation (car (eval expr env heap)) heap) '(exception ooma))
     (cons '(exception ooma) (list heap))]
  [else
  (cons (car (eval expr env heap)) (list (writeToLocation heap (car(eval expr env heap)) 'free)))]
  ))
;;(trace evalFree)
;;Eval Wref
;;            Location  expr
(define (evalWref expr1     expr2 env heap)
  (cond
    [ (equal? (readFromLocation (car (eval expr1 env heap)) heap) '(exception fma))
      (cons '(exception fma) (list heap))]
    [ (equal? (readFromLocation (car (eval expr1 env heap)) heap) '(exception ooma))
      (cons '(exception ooma) (list heap))]
    [else
  (cons (car(eval expr2 env heap))  (list (writeToLocation heap (car(eval expr1 env heap)) (car(eval expr2 env heap)))))]
)
  )
;;(trace evalWref)
;;Translate expression. Adegala
(define (translateExpression var lst expr)
  (if (equal? (length lst) 1)
      (append  (cons var (list lst)) (list expr))
      (append (append (cons var (list (list (car lst)))) (list (translateExpression 'var (cdr lst) expr)))
  )))
;;(trace translateExpression)
;; input: variable, environment
;; output: value to which the variable is mapped to in the environment
;;         It can be '(Cannot Evaluate) 
(define (findvalue x env heap)
  (if (null? env)  
      '(Cannot Evaluate)
      (if (equal? (car (car env)) x)
          (eval (cadr (car env)) env heap)
          (findvalue x (cdr env) heap))))
;;(trace findvalue)
;; input: environment
;; output: true, if no variable is mapped to '(Cannot Evaluate)
;;         false, otherwise
;; Exercise: implement in another way, where it does not depend on '(Cannot Evaluate)
(define (caneval env)
  (if (null? env)
      true
      (and (not (equal? (cadr (car env)) '(Cannot Evaluate)))
           (caneval (cdr env)))))

;; input: list of (variable expression), expr to evaluate, environment
;; output: evaluate expr in some environment

(define (evalvarassign varassigns expr env heap)
  (if (null? varassigns)  ;; no variable expression pair, 
      (eval expr env heap)     ;; then just evaluate the expression in the current environment
      ;; else
      ;; recursive call with the suffix of varassigns, with the same expr
      ;; in the environment constructed by cons-ing (variable evaluation of expression)
      ;; to the given environment env.

      ;;I believe I have to remove this due to the eval it calls. 
;;     (if (list? (car(eval (cadr (car varassigns)) env heap)))
;;         (eval (cadr (car varassigns)) env heap)
      (evalvarassign (cdr varassigns)
                     expr
                     (append (list (list (car (car varassigns))
                                 (cadr (car varassigns))))
                           env) heap)));;Grab the new Heap from eval of varassigns - adegala
      
;; is op arithmatic operation
(define (arithop op)
  (or (equal? op '+)
      (equal? op '-)
      (equal? op '*)
      (equal? op '\))))

;; input: arithoperator, expr-operand1, expr-operand2, env
;; output: '(Cannot Evaluate) or some number
;; used: myapply
;; Changing this code - Probably wrong - adegala
(define (evalarith op expr1 expr2 env heap)
 (if (list? (car(eval expr1 env heap)))
     (eval expr1 env heap)
     (if (list? (car(eval  expr2 env (car(cdr (eval expr1 env heap))))))
         (eval  expr2 env (car(cdr (eval expr1 env heap))))
         (cons (myapply op (car(eval expr1 env heap)) (car(eval  expr2 env (car(cdr (eval expr1 env heap))))) heap) (cdr(eval expr1 env heap))  ) ;;(cdr (eval expr1 env heap)) == heap from eval of expr1. 
)))
;;(trace evalarith)

;; input: true/false, '(Cannot Evaluate) expression values
;; output: '(Cannot Evaluate) or expression values
;;         expression values can be '(Cannot Evaluate)
(define (ifthenelse condition expr1 expr2 env heap)
  (if (equal? (car condition) '(Cannot Evaluate))
      '(Cannot Evaluate)
      (if (list? (car condition))
          condition
      (if (car condition)
          (eval expr1 env heap)
          (eval expr2 env heap)))))
;;(trace ifthenelse)
;; input: conditions of the form (gt/lt/eq expr1 expr2), (or/and cond1 cond2), (not cond)
;; output: true/false, '(Cannot Evaluate)
;; used: myapply
;;Changes by Adam de Gala.
;;Have to use heap from eval of expr1. 
(define (evalcond condexpr env heap)

 ;; Let remove exceptions for now
 ;; (if (list? (car(eval (cadr condexpr) env heap)))
 ;;        (eval (cadr condexpr) env heap)
 ;;        (if (list? (car (eval (cadr (cdr condexpr)) env (car (cdr(eval (cadr condexpr) env heap))))))
 ;;            (eval (cadr (cdr condexpr)) env (car (cdr(eval (cadr condexpr) env heap))))
  (cond
    [ (equal? (car condexpr) 'gt)
      (myapply 'gt (eval (cadr condexpr) env heap) (eval (cadr (cdr condexpr)) env (car (cdr(eval (cadr condexpr) env heap)))) (car(cdr(eval (cadr (cdr condexpr)) env (car(cdr(eval (cadr condexpr) env heap)))))))]
    
    [ (equal? (car condexpr) 'lt)
      (myapply 'lt (eval (cadr condexpr) env heap) (eval (cadr (cdr condexpr)) env (car (cdr(eval (cadr condexpr) env heap)))) (car(cdr(eval (cadr (cdr condexpr)) env (car(cdr(eval (cadr condexpr) env heap)))))))]
      
    [ (equal? (car condexpr) 'eq)
      (myapply 'eq (eval (cadr condexpr) env heap) (eval (cadr (cdr condexpr)) env (car (cdr(eval (cadr condexpr) env heap)))) (car(cdr(eval (cadr (cdr condexpr)) env (car(cdr(eval (cadr condexpr) env heap)))))))]
       
    [ (equal? (car condexpr) 'and);;Lazy Evaultion comes up here
      ;;Lazy
      (if (car (evalcond (cadr condexpr) env heap))
          (myapply 'and (evalcond (cadr condexpr) env heap)
               (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))) (car(cdr (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))))) ) ;; Use heap from (eval of expr 2 with heap from eval of expr1)?
          (cons #f (list (car (cdr (evalcond (cadr condexpr) env heap))))))]
      ;; ^Lazy benifit, jump back early.
    
      ;;Older code
      ;;(myapply 'and (evalcond (cadr condexpr) env heap)
      ;;         (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))) (car(cdr (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))))) )] ;; Use heap from (eval of expr 2 with heap from eval of expr1)?

[ (equal? (car condexpr) 'or) ;;Lazy evaulation comes up here.

  ;;Lazy
  (if (eq? (car (evalcond (cadr condexpr) env heap)) #f)
      (myapply 'or (evalcond (cadr condexpr) env heap)
               (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))) (car(cdr (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))))) ) ;; Use heap from (eval of expr 2 with heap from eval of expr1)?

  (cons #t (list (car (cdr (evalcond (cadr condexpr) env heap))))))]
;; ^Lazy Benifit, jump back early. 
;;Old Code 
  ;;    (myapply 'or (evalcond (cadr condexpr) env heap)
  ;;          (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))) (car(cdr (evalcond (cadr (cdr condexpr)) env (car(cdr (evalcond (cadr condexpr) env heap)))))) )] ;; Use heap from (eval of expr 2 with heap from eval of expr1)?

    [ (equal? (car condexpr) 'not)
      (myapply 'not (evalcond (cadr condexpr) env heap) (car(cdr (evalcond (cadr condexpr) env heap))) 
               false) ] ;; dummy
    ))
(trace evalcond)
;;Functions for References. Adegala
(define (findFreeLocation heap)
  (if (null? heap)
      '(exception oom)
      ( if(equal? (car(cdr(car heap))) 'free)
                   (car(car heap))
                   (findFreeLocation (cdr heap))))
  )

;;Dummy function for write to location - Makes it easy to use in other functions
(define (writeToLocation heap location data)
  (writeToLocationComplex heap '() location data);;Generates empty list for
  )
;;(trace writeToLocation)
;;other function to use. 
;;Takes the heap, and empty list and location data
;; As the function traverses down the heap, it adds all the locations
;; to the empty list in order to save previous data.
(define (writeToLocationComplex heapTraverse heapBefore location data)
  (if (null? heapTraverse)
      '(exception ooma)
      (if (equal? (car(car heapTraverse)) location)
           (append heapBefore (cons (list location data) (cdr heapTraverse)))
        (writeToLocationComplex (cdr heapTraverse) (append heapBefore (list (car heapTraverse))) location data))) 
 )
;;(trace writeToLocationComplex)

;; Takes a heap & location
;; Helper function  # 3
(define (readFromLocation location heap)

  (if(null? heap)
     '(exception ooma)
     (if(equal? (car(car heap)) location)
        (if(equal? (car(cdr(car heap))) 'free)
           '(exception fma)
           (car(cdr(car heap))))
        (readFromLocation location (cdr heap)))
  )
  )
;;(trace readFromLocation)



;; input: some operator, arithmatic or conditional
;;        operand-values for the operator
;; output: '(C+annot Evaluate) or number or boolean 
(define (myapply op val1 val2 heap)
  (if (or (equal? val1 '(Cannot Evaluate))
          (equal? val2 '(Cannot Evaluate)))
      '(Cannot Evaluate)
      (cond
        [ (equal? op '+) (+ val1 val2) ]
        [ (equal? op '-) (- val1 val2) ]
        [ (equal? op '*) (* val1 val2) ]
        [ (equal? op 'gt)  (append (list (> (car val1) (car val2))) (list heap)) ]
        [ (equal? op 'lt)  (append (list (< (car val1) (car val2))) (list heap)) ]
        [ (equal? op 'eq)  (append (list (equal? (car val1) (car val2))) (list heap)) ]
        [ (equal? op 'and) (append (list (and (car val1)  (car val2) )) (list heap)) ]
        [ (equal? op 'or)  (append (list (or (car val1) (car val2))) (list heap))]
        [ (equal? op 'not) (append (list (not (car val1))) (list heap)) ])))

(trace myapply)
;; Functions added for the assignment 4
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (paramargs (x1 x2 .... xn) (e1 e2 .... en) env) = ((x1 e1val) (x2 e2val) ... (xn enval))
;; input: list of variables
;;        list of expressions
;;        environment
;; output: list of pairs of variable-expressionvalue
(define (paramargs paramlist exprlist env)
  (if (null? paramlist)
      '()
      (cons (list (car paramlist) (car exprlist))  ;;Remove eval for dynamic! - Adegala
            (paramargs (cdr paramlist) (cdr exprlist) env))))
;;(trace paramargs)
;; find the function parameters
;; input: function name and arg-length
;;        env
;; output: list of function parameters
(define (findfunparams fname paramlength env)
  (if (and (list? (car (car env)))   ;; is a function definition
           (equal? (car (car (car env))) fname)  ;; name matches
           (equal? (length (cadr (car (car env)))) paramlength)) ;; paramlength matchs
      ;; 
      (cadr (car (car env)))   ;; return the list of parameters
      (findfunparams fname paramlength (cdr env)))) ;; else keep looking
;;(trace findfunparams)
;; Same as above: just return the definition of the function
(define (findfundef fname paramlength env)
  (if (and (list? (car (car env)))
           (equal? (car (car (car env))) fname)
           (equal? (length (cadr (car (car env)))) paramlength))
      ;; 
      (cadr (car env)) ;; return the definition of the function
      (findfundef fname paramlength (cdr env)))) ;; else keep looking

;; Given an environment; generate the static environment corresponding
;; for a function
;; same as above again
(define (staticenv fname paramlength env)
  (if (and (list? (car (car env)))
           (equal? (car (car (car env))) fname)
           (equal? (length (cadr (car (car env)))) paramlength))
      env ;; return the environment at the time of definition
      (staticenv fname paramlength (cdr env)))) ;; else keep looking