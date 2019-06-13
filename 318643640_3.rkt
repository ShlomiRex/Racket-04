#lang pl

;; I took the last assingment and changed the names a little

#|
BNF for the ROL language:
 <ROL> ::= {reg-len = <num> <RegE>}

 <RegE> ::=  <Bits>
           | {and <RegE> <RegE>}
           | {or <RegE> <RegE>}
           | {shl <RegE>}
           | {<ID>}
           | {with {<ID> <RegE>} <RegE>}
           | {if <Bool> <RegE> <RegE>}
           | {fun <ID> <RegE>}
           | {call <RegE> <RegE>}

 <Bool> ::=  false
           | true
           | {geq? <RegE> <RegE>}
           | {maj? <RegE>}

 <Bits> ::=  <bit>
           | <bit> <Bits>

 <bit>::=    1
           | 0
|#

;; Defining two new types
(define-type BIT = (U 0 1))
(define-type Bit-List = (Listof BIT))
;; RegE abstract syntax trees
(define-type RegE
  [Reg Bit-List]
  [And RegE RegE]
  [Or RegE RegE]
  [Shl RegE]
  [RegEId Symbol]
  [RegEWith Symbol RegE RegE]
  [Bool Boolean]
  [Geq RegE RegE]
  [Maj RegE]
  [If RegE RegE RegE]
  [RegEFun Symbol RegE]
  [RegECall RegE RegE])


;; Next is a technical function that converts (casts)
;; (any) list into a bit-list. We use it in parse-sexpr.
(: list->bit-list : (Listof Any) -> Bit-List)
;; to cast a list of bits as a bit-list
(define (list->bit-list lst)
  (cond [(null? lst) null]
        [(eq? (first lst) 1)(cons 1 (list->bit-list (rest lst)))]
        [else (cons 0 (list->bit-list (rest lst)))]))


(: RegE-parse-sexpr : Sexpr -> RegE)
;; to convert the main s-expression into ROL
(define (RegE-parse-sexpr sexpr)
  (match sexpr
    [(list 'reg-len' = (number: n) args) 
     (if (> n 0)
         (parse-sexpr-RegL args n)
         (error 'RegE-parse-sexpr "Register length must be at least 1 ~s" sexpr))] ;; remember to make sure specified register length is at least 1
    [else (error 'RegE-parse-sexpr "bad syntax in ~s" sexpr)]))


(: parse-sexpr-RegL : Sexpr Number -> RegE)
;; to convert s-expressions (input) into RegEs (output)
(define (parse-sexpr-RegL sexpr reg-len)
  (match sexpr
    [(list (and a (or 1 0)) ... )
     (if (= reg-len (length a))
         ;;Check length of bits
         (Reg (list->bit-list a))
         (error 'RegE-parse-sexpr "wrong number of bits in ~s" a))]
    [(list 'and list1 list2)
     ;; And
     (And (parse-sexpr-RegL list1 reg-len) (parse-sexpr-RegL list2 reg-len))]
    [(list 'or list1 list2)
     ;; Or
     (Or (parse-sexpr-RegL list1 reg-len) (parse-sexpr-RegL list2 reg-len))]
    [(list 'shl list)
     ;; Shl
     (Shl (parse-sexpr-RegL list reg-len))]
    [(list 'if list1 list2 list3)
     ;; If
     (If (parse-sexpr-RegL list1 reg-len)
         (parse-sexpr-RegL list2 reg-len)
         (parse-sexpr-RegL list3 reg-len))]
    [(symbol: id)
     (if (eq? id 'false)(Bool #f)
         (if (eq? id 'true)(Bool #t)(RegEId id)))]
    [(list 'geq? list1 list2)
     ;; Geq
     (Geq (parse-sexpr-RegL list1 reg-len)
          (parse-sexpr-RegL list2 reg-len))]
    ;; Maj
    [(list 'maj? list1)
     (Maj(parse-sexpr-RegL list1 reg-len))]

    ;; With
    [(cons 'with args)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (RegEWith name (parse-sexpr-RegL named reg-len) (parse-sexpr-RegL body reg-len))]
       [else (error 'parse-sexpr-RegE "bad with syntax in ~s" sexpr)])] ;;end With
    ;; Fun
    [(cons 'fun more)
       (match sexpr
         [(list 'fun (list (symbol: name)) body)
          (RegEFun name (parse-sexpr-RegL body reg-len))]
         [else (error 'parse-sexpr-RegL "bad `fun' syntax in ~s" sexpr)])] ;; end Fun
    ;; Call
    [(list 'call fun arg) (RegECall (parse-sexpr-RegL fun reg-len) (parse-sexpr-RegL arg reg-len))]
    [else (error 'RegE-parse-sexpr "bad syntax in ~s" sexpr)]))

;; Input: String (code), Output: RegE . Parse the code into AST preparation.
(: RegE-parse : String -> RegE)
(define (RegE-parse str)
  (RegE-parse-sexpr (string->sexpr str)))


;; New type 
(define-type RES
  [RegV Bit-List]
  [boolV Boolean]
  [FunV Symbol RegE ENV]) ;; Env model


;; Subst recursion
;; Input: RegE (What to parse), Symbol (id), and RegE as what id = 'to'
;; Output is doing: ;; expression contains no free instances of the second argument
(: RegE-subst : RegE Symbol RegE -> RegE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (RegE-subst expr from to)
  (cases expr
    [(Reg n) expr]
    [(And l r) (And (RegE-subst l from to) (RegE-subst r from to))]
    [(Or l r) (Or (RegE-subst l from to) (RegE-subst r from to))]
    [(Geq l r) (Geq (RegE-subst l from to) (RegE-subst r from to))]
    [(Shl l) (Shl (RegE-subst l from to))]
    [(Maj l) (Maj (RegE-subst l from to))]
    [(Bool b) expr]
    [(RegEId name) (if (eq? name from) to expr)]
    [(If l e r) (If (RegE-subst l from to)
                    (RegE-subst e from to)
                    (RegE-subst r from to))]
    ;; Was easy above
    [(RegEWith bound-id named-expr bound-body)
     ;; Return RegEWith type with subst the internal parts!
     (RegEWith bound-id (RegE-subst named-expr from to)
           (if (eq? bound-id from)
               bound-body
               (RegE-subst bound-body from to)))]

    ;; Call Func Arguments
    ;;Subst Func and Arguments
    [(RegECall l r)
     (RegECall (RegE-subst l from to) (RegE-subst r from to))]
    
    ;; Func
    [(RegEFun bound-id bound-body)
     (if (eq? bound-id from)
         expr
         (RegEFun bound-id (RegE-subst bound-body from to)))]))


;; Evaluation part
(: RegE-eval : RegE ENV -> RES)
;; evaluates RegE expressions by reducing them to bit-lists
(define (RegE-eval expr env)
  (cases expr
    [(Reg v)  (RegV v)]
    [(And l r) (reg-arith-op bit-and (RegE-eval l env) (RegE-eval r env))]
    [(Or l r) (reg-arith-op bit-or (RegE-eval l env) (RegE-eval r env))]
    [(Shl l) (RegV (shift-left (RegV->bit-list (RegE-eval l env))))]
    [(Geq reg1 reg2) (boolV (geq-bitlists? (RegV->bit-list (RegE-eval reg1 env)) (RegV->bit-list (RegE-eval reg2 env))))]
    [(Maj v) (boolV (majority? (RegV->bit-list(RegE-eval v env))))]
    [(If condition tthen fthen)
     (if (cases (RegE-eval condition env)
           [(boolV v) v]
           [else #t]) (RegE-eval tthen env) (RegE-eval fthen env))]
    [(RegEId sym)
     (if (eq? sym 'false)
         (boolV #f)
         (if (eq? sym 'true)
             (boolV #t)
             (RegE-lookup sym env)))]
    [(Bool v) (boolV v)]


    ;;Above was easy
    ;;With
    [(RegEWith sym reg1 reg2) (RegE-eval (RegE-subst reg2 sym reg1) env)]
    ;;Func
    [(RegEFun bound-id bound-body)
       (FunV bound-id bound-body env)]
    ;;Call
    [(RegECall fun-expr arg-expr)
       (let ([fval (RegE-eval fun-expr env)])
         (cases fval
           [(FunV bound-id bound-body f-env)
            (RegE-eval bound-body
                  (Extend bound-id (RegE-eval arg-expr env) f-env))]
           [else (error 'RegE-eval "`call' expects a function, got: ~s"
                              fval)]))]
     ))


;;And
(: bit-and : BIT BIT -> BIT) 
(define(bit-and a b)
  (cond
    [(or (eq? a 0) (eq? b 0)) 0]
    [else 1]))

;; Or
(: bit-or : BIT BIT -> BIT) ;; Aithmetic or
(define(bit-or a b)
  (cond
    [(or (eq? a 1)(eq? b 1))1]
    [else 0]))

;; Choose what arithmetic operation to do on a given bit list.
;; First argument is the function (operation)
(: reg-arith-op : (BIT BIT -> BIT) RES RES -> RES)
;; Consumes two registers and some binary bit operation 'op',
;; and returns the register obtained by applying op on the
;; i'th bit of both registers for all i.
(define(reg-arith-op op reg1 reg2)
  (: bit-arith-op : Bit-List Bit-List -> Bit-List)
  ;; Consumes two bit-lists and uses the binary bit operation 'op'.
  ;; It returns the bit-list obtained by applying op on the
  ;; i'th bit of both registers for all i.
  (define(bit-arith-op bl1 bl2)
    (map op bl1 bl2))
  (RegV (bit-arith-op (RegV->bit-list reg1) (RegV->bit-list reg2))))

;; Maj
(: majority? : Bit-List -> Boolean)
;; Consumes a list of bits and checks whether the
;; number of 1's are at least as the number of 0's.
(define(majority? bl)
  (if (>= (foldl + 0 bl) (/ (length bl) 2)) #t #f))

;; Geq
(: geq-bitlists? : Bit-List Bit-List -> Boolean)
;; Consumes two bit-lists and compares them. It returns true if the
;; first bit-list is larger or equal to the second.
(define (geq-bitlists? bl1 bl2)
  (cond 
    [(or (null? bl1) (null? bl2)) true]
    [(> (first bl1) (first bl2)) true]
    [(< (first bl1) (first bl2)) false]
    [else (geq-bitlists? (rest bl1) (rest bl2))]))

;;Shl
(: shift-left : Bit-List -> Bit-List)
;; Shifts left a list of bits (once)
(define(shift-left bl)
  (append (rest bl) (list (first bl))))

;; Casting RES to Bit-List
(: RegV->bit-list : RES -> Bit-List)
(define (RegV->bit-list reg)
  (cases reg
    [(RegV bt) bt]
    [else (error 'RegV->bit-list "error in RegV->bit-list")]))









(define-type ENV
    [EmptyEnv]
    [Extend Symbol RES ENV])

(: runFROL : String -> Bit-List)

;; evaluate a ROL program contained in a string
;; we will not allow to return a boolean type
(define (runFROL str)
  (cases (RegE-eval (RegE-parse str) (EmptyEnv))
    [(RegV bl) bl]
    [else (error 'run "error- can't return boolean!")]))




;; Main Tests
(test (runFROL "{ reg-len = 4 {1 0 0 0}}") =>
      '(1 0 0 0))
(test (runFROL "{ reg-len = 4 {shl {1 0 0 0}}}") =>
      '(0 0 0 1))
(test (runFROL "{ reg-len = 4 {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}") =>
      '(0 1 0 1))
(test (runFROL "{ reg-len = 4 { or {and {shl {1 0 1 0}} {shl {1 0 0 1}}} {1 0 1 0}}}") =>
      '(1 0 1 1))
(test (runFROL "{ reg-len = 2 { or {and {shl {1 0}} {1 0}} {1 0}}}") =>
      '(1 0))
(test (runFROL "{ reg-len = 2 { with {x { or {and {shl {1 0}} {1 0}} {1 0}}} {shl x}}}") =>
      '(0 1))
(test (runFROL "{ reg-len = 3 {if {geq? {1 0 1} {1 1 1}} {0 0 1} {1 1 0}}}") =>
      '(1 1 0))
(test (runFROL "{ reg-len = 4 {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}") =>
      '(0 1 1 1))
(test (runFROL "{ reg-len = 4 {if false {shl {1 0 1 1}} {1 1 0 1}}}") =>
      '(1 1 0 1))
(test (runFROL "{ reg-len = 4 {or {1 1 1 1} {0 1 1}}}")
      =error> "wrong number of bits in (0 1 1)")
(test (runFROL "{ reg-len = 0 {}}")
      =error> "Register length must be at least 1")

;; My Tests
(test (RegE-subst (Geq (Reg '(0 1)) (Reg '(1 1))) 'x (RegEId 'x)) =>
      (Geq (Reg '(0 1)) (Reg '(1 1))))
(test (geq-bitlists? '(1 1 1) '(1 1 1)) => true)
(test (runFROL "{ reg-len = 2 {with {x { or {and {or {1 0} {1 0}}{1 0}}{1 0}}}{with {x {and {and {and {0 0} {0 0}}{1 0}}{1 0}}}{if true {1 0} {1 1}}}}}")=>
      '(1 0))
     
(test (runFROL "{ reg-len = 2 {with {x { or {and {or {1 0} {1 0}}{1 0}}{1 0}}}{bool error}}}")
      =error> "RegE-parse-sexpr: bad syntax in (bool error)")
(test (geq-bitlists? '(1 1 1) '(1 1 0)) => true)
(test (runFROL "{ reg-len = 2 {with {x { or {and {or {1 0} {1 0}}{1 0}}{1 0}}}{with {x { or {and {or {1 0} {1 0}}{1 0}}{1 0}}}{if false {1 0} {0 1}}}}}")=>
      '(0 1))
(test (runFROL "{ reg-len = 4 {with {x {1 1 1 1}} {with {y {1 0 1 0}} {and x y}}}}") =>
      '(1 0 1 0))
(test (runFROL "{ reg-len = 1 {if {0} {0} {1}}}") =>
      '(0))
(test (runFROL "{ reg-len = a {if false {shl {1 0 1 1}} {1 1 0 1}}}")
      =error> "RegE-parse-sexpr: bad syntax in (reg-len = a (if false (shl (1 0 1 1)) (1 1 0 1)")
(test (runFROL "{ reg-len = 4 {with {x error}}}")  =error> "parse-sexpr-RegE: bad with syntax in (with (x error))")



;;;;;;;;;;;;;;;;;;;; MATALA 4 ;;;;;;;;;;;;;;;;;;;;
      
;; The Flang interpreter – supporting both the substitution model and
;;the substitution-cache model
 #|
 The grammar:
 <FLANG> ::= <num>
 | { + <FLANG> <FLANG> }
 | { - <FLANG> <FLANG> }
 | { * <FLANG> <FLANG> }
 | { / <FLANG> <FLANG> }
 | { with { <id> <FLANG> } <FLANG> }
 | <id>
 | { fun { <id> } <FLANG> }
 | { call <FLANG> <FLANG> }
|#
 (define-type FLANG
 [Num Number]
 [Add FLANG FLANG]
 [Sub FLANG FLANG]
 [Mul FLANG FLANG]
 [Div FLANG FLANG]
 [Id Symbol]
 [With Symbol FLANG FLANG]
 [Fun Symbol FLANG]
 [Call FLANG FLANG])
 (: parse-sexpr : Sexpr -> FLANG)
 ;; to convert s-expressions into FLANGs
 (define (parse-sexpr sexpr)
 (match sexpr
 [(number: n) (Num n)]
 [(symbol: name) (Id name)]
 [(cons 'with more)
 (match sexpr
 [(list 'with (list (symbol: name) named) body)
 (With name (parse-sexpr named) (parse-sexpr body))]
 [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
 [(cons 'fun more)
 (match sexpr
 [(list 'fun (list (symbol: name)) body)
 (Fun name (parse-sexpr body))]
 [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
 [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
 [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
 [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
 [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
 [(list 'call fun arg) (Call (parse-sexpr fun) (parse-sexpr arg))]
 [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))
 (: parse : String -> FLANG)
 ;; parses a string containing a FLANG expression to a FLANG AST
 (define (parse str)
 (parse-sexpr (string->sexpr str)))
;;;;;; the evaluation part for the substitution model
 (: subst : FLANG Symbol FLANG -> FLANG)
 ;; substitutes the second argument with the third argument in the
 ;; first argument, as per the rules of substitution; the resulting
 ;; expression contains no free instances of the second argument
 (define (subst expr from to)
 (cases expr
 [(Num n) expr]
 [(Add l r) (Add (subst l from to) (subst r from to))]
 [(Sub l r) (Sub (subst l from to) (subst r from to))]
 [(Mul l r) (Mul (subst l from to) (subst r from to))]
 [(Div l r) (Div (subst l from to) (subst r from to))]
 [(Id name) (if (eq? name from) to expr)]
 [(With bound-id named-expr bound-body)
 (With bound-id
 (subst named-expr from to)
 (if (eq? bound-id from)
 bound-body
 (subst bound-body from to)))]
 [(Call l r) (Call (subst l from to) (subst r from to))]
 [(Fun bound-id bound-body)
 (if (eq? bound-id from)
 expr
 (Fun bound-id (subst bound-body from to)))]))
 (: arith-op : (Number Number -> Number) FLANG FLANG -> FLANG)
 ;; gets a Racket numeric binary operator, and uses it within a FLANG
 ;; `Num' wrapper
 (define (arith-op op expr1 expr2)
 (: Num->number : FLANG -> Number)
 (define (Num->number e)
 (cases e
 [(Num n) n]
 [else (error 'arith-op "expects a number, got: ~s" e)]))
 (Num (op (Num->number expr1) (Num->number expr2))))
 (: eval : FLANG -> FLANG)
 ;; evaluates FLANG expressions by reducing them to *expressions*
 (define (eval expr)
 (cases expr
 [(Num n) expr]
 [(Add l r) (arith-op + (eval l) (eval r))]
 [(Sub l r) (arith-op - (eval l) (eval r))]
 [(Mul l r) (arith-op * (eval l) (eval r))]
 [(Div l r) (arith-op / (eval l) (eval r))]
 [(With bound-id named-expr bound-body)
 (eval (subst bound-body
 bound-id
(eval named-expr)))]
 [(Id name) (error 'eval "free identifier: ~s" name)]
 [(Fun bound-id bound-body) expr]
 [(Call fun-expr arg-expr)
 (let ([fval (eval fun-expr)])
 (cases fval
 [(Fun bound-id bound-body)
 (eval (subst bound-body
 bound-id
(eval arg-expr)))]
 [else (error 'eval "`call' expects a function, got: ~s"
 fval)]))]))
 (: run : String -> Number)
 ;; evaluate a FLANG program contained in a string
 (define (run str)
 (let ([result (eval (parse str))])
 (cases result
 [(Num n) n]
 [else (error 'run
 "evaluation returned a non-number: ~s" result)])))
 ;; tests
 (test (run "{call {fun {x} {+ x 1}} 4}")
 => 5)
 (test (run "{with {add3 {fun {x} {+ x 3}}}
 {call add3 1}}")
 => 4)
 (test (run "{with {add3 {fun {x} {+ x 3}}}
 {with {add1 {fun {x} {+ x 1}}}
 {with {x 3}
 {call add1 {call add3 x}}}}}")
 => 7)
 (test (run "{with {identity {fun {x} x}}
 {with {foo {fun {x} {+ x 1}}}
 {call {call identity foo} 123}}}")
 => 124)
 (test (run "{call {call {fun {x} {call x 1}}
 {fun {x} {fun {y} {+ x y}}}}
 123}")
 => 124)
;;;;;; The evaluation part for the substitution cache model
;; a type for substitution caches:
 (define-type SubstCache = (Listof (List Symbol FLANG)))
 (: empty-subst : SubstCache)
 (define empty-subst null)
 (: extend : Symbol FLANG SubstCache -> SubstCache)
 (define (extend name val sc)
 (cons (list name val) sc))
 (: lookup : Symbol SubstCache -> FLANG)
 (define (lookup name sc)
 (let ([cell (assq name sc)])
 (if cell
 (second cell)
 (error 'lookup "no binding for ~s" name))))

 (: counterx : Natural)
 (define counterx 0)
 ;;;above eval
 (: evalSC : FLANG SubstCache -> FLANG)
 ;; evaluates FLANG expressions by reducing them to expressions
 (define (evalSC expr sc)
 (set! counterx (add1 counterx))
 (if (> counterx 500)
 (error 'eval "exceeded 500 times")
 (cases expr
 [(Num n) expr]
 [(Add l r) (arith-op + (evalSC l sc) (evalSC r sc))]
 [(Sub l r) (arith-op - (evalSC l sc) (evalSC r sc))]
 [(Mul l r) (arith-op * (evalSC l sc) (evalSC r sc))]
 [(Div l r) (arith-op / (evalSC l sc) (evalSC r sc))]
 [(With bound-id named-expr bound-body)
 (evalSC bound-body
 (extend bound-id (evalSC named-expr sc) sc))]
 [(Id name) (lookup name sc)]
 [(Fun bound-id bound-body) expr]
 [(Call fun-expr arg-expr)
 (let ([fval (evalSC fun-expr sc)])
 (cases fval
 [(Fun bound-id bound-body)
 (evalSC bound-body
 (extend bound-id (evalSC arg-expr sc) sc))]
 [else (error 'evalSC "`call' expects a function, got: ~s"
 fval)]))])))
 (: runSC : String -> Number)
 ;; evaluate a FLANG program contained in a string
 (define (runSC str)
 (let ([result (evalSC (parse str) empty-subst)])
 (cases result
 [(Num n) n]
 [else (error 'runSC
 "evaluation returned a non-number: ~s" result)])))

 ;; The FLANG was given to us!

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Question 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(: RegE-lookup : Symbol ENV -> RES)
;; just like in class!
(define (RegE-lookup name env)
  (cases env
    [(EmptyEnv) (error 'RegE-lookup "no binding for ~s" name)]
    [(Extend id val rest-env)
     (if (eq? id name)
         val
         (RegE-lookup name rest-env))])) ;;keep looking

;; Tests
(test (runFROL "{ reg-len = 3
 {with {identity {fun {x} x}}
 {with {foo {fun {x} {or x {1 1 0}}}}
 {call {call identity foo} {0 1 0}}}}}")
 => '(1 1 0))
 (test (runFROL "{ reg-len = 3
 {with {x {0 0 1}}
 {with {f {fun {y} {and x y}}}
 {with {x {0 0 0}}
 {call f {1 1 1}}}}}}")
 => '(0 0 1))
(test (runFROL "{ reg-len = 4 {or {1 1 1 1} {0 1 1}}}") =error> "wrong number of bits in (0 1 1)")
(test (runFROL "{ reg-len = 0 {}}") =error> "Register length must be at least 1")
(test (runFROL "{ reg-len = 3 {if {geq? {1 0 1} {1 1 1}} {0 0 1} {1 1 0}}}")
      => '(1 1 0))
(test (runFROL "{ reg-len = 4
 {with {foo {fun {z} {if {maj? z} z {shl z}}}}
 {call foo {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}}}")
 => '(0 1 1 1))
(test (runFROL "{ reg-len = 4 {with {x {0 0 1 1}} {shl y}}}") =error> "RegE-lookup: no binding for y")
(test (runFROL "{ reg-len = 4 {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}")
      => '(0 1 0 1))
(test (runFROL "{ reg-len = 4 {1 0 0 0}}")
      => '(1 0 0 0))
(test (runFROL "{ reg-len = 4 {if false {shl {1 0 1 1}} {1 1 0 1}}}")
      => '(1 1 0 1))
(test (runFROL "{ reg-len = 1 {if {geq? {0}{0}}{0} {0}}}")
      =>'(0))
(test (runFROL "{ reg-len = 4 {shl {1 0 0 0}}}")
      => '(0 0 0 1))
(test (runFROL "{ reg-len = 4 {and {shl {1 0 1 0}}{shl {1 0 1 0}}}}") =>
      '(0 1 0 1))
(test (runFROL "{ reg-len = 4 {if {maj? {0 0 1 1}} {shl {1 0 1 1}} {1 1 0 1}}}")
      => '(0 1 1 1))


;; Count Free Single function
;; Input: String, Symbol to find
;; Output: Number of 'Symbol' free identifiers in the code!
(: CFSingle : String Symbol -> Natural)
(define (CFSingle expr name)
  (countFreeSingle (parse expr) name))


;; Very cool to understand the behind the scene of free identifiers and id's.
(: countFreeSingle : FLANG Symbol -> Natural)
(define (countFreeSingle flang name)
  (cases flang
    [(Num n) 0 ]
    [(Add l r) (+ (countFreeSingle l name) (countFreeSingle r name))]
    [(Sub l r) (+ (countFreeSingle l name) (countFreeSingle r name))]
    [(Mul l r) (+ (countFreeSingle l name) (countFreeSingle r name))]
    [(Div l r) (+ (countFreeSingle l name) (countFreeSingle r name))]
    [(Id char) (if (eq? char name) 1 0)]
    ;;Above was easy peasy

    ;;With
    [(With bound-id named-expr bound-body)
     (if (eq? bound-id name)
         (countFreeSingle named-expr name)
         (+ (countFreeSingle bound-body name) (countFreeSingle named-expr name)))]
    ;;Fun
    [(Fun bound-id bound-body) (if (eq? bound-id name) 0 (countFreeSingle bound-body name))]
    ;;Call
    [(Call fun-expr arg-expr) (+ (countFreeSingle fun-expr name) (countFreeSingle arg-expr name))]
    )
  )

;; Tests
(test (CFSingle "{+ r r}" 'r) => 2)
(test (CFSingle "{fun {r} {+ r e}}" 'e) => 1)
(test (CFSingle "{fun {r} {+ r e}}" 'r) => 0)
(test (CFSingle "{call {fun {r} {+ r e}}
 {with {e {+ e r}}
 {fun {x} {+ e r}}}}"
 'r) => 2)
(test (CFSingle "{call {fun {r} {+ r e}}
 {with {e {+ e r}}
 {fun {x} {+ e r}}}}" 'e) => 2)
(test (CFSingle "{with {foo {fun {y} {+ x y}}}
 {with {x 4}
 {call foo 3}}}" 'x) => 1)
(test (run "{with {foo {fun {y} {+ x y}}}
 {with {x 4}
 {call foo 3}}}") => 7)



(define loop "{with {myf {fun {x} {call f x}}} {with {f {fun {x} {call myf x}}} {call myf f}}}")

(test (runSC loop) =error> "exceeded 500 times") ;; subst-cache model
(test (run loop) =error> "free identifier: f") ;; substitution model