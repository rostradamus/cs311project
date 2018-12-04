#lang plai

(print-only-errors)

;; Quipu and QuipuScript
;;
;; Our goal in this language is to explore mutation within an object-oriented
;; context. To get there, we'll first create a language that lets us represent
;; strings and transform those strings into identifier references. (We could
;; have chosen symbols instead of strings.) That allows us to pass around
;; identifier names and reference those names.
;;
;; We'll use that to implement object-oriented programming as a desugaring.
;; Specifically, we'll support an object inheritance structure somewhat like
;; JavaScript's. Conceptually, each object has a set of fields (each itself
;; a variable with a value) and a prototype (AKA, parent) object. If we ask
;; for an object's field and it has a field by that name, then it returns
;; the field's value. If it does NOT have that name, it "delegates" to its
;; prototype: it asks the prototype recursively to get ITS field by that
;; name.
;;
;; Of course, we need some moment for all this delegating to stop. We'll do
;; that by letting objects appear out of nothing ("ex nihilo" in Latin) as
;; long as they say they're doing that explicitly. Such an object will simply
;; give an error if it cannot find a requested field.
;;
;; We start our implementation from in-class-09 except using a ValuexStore
;; to return two values from a function instead of using Racket's "values"
;; form, which can be hard to handle. We also add n-ary functions (functions
;; of 0, 1, or more arguments), with's with multiple identifiers bound "in
;; parallel (i.e., such that no one of the named expressions has any of the
;; other identifiers bound by that with available in its environment), and
;; with*'s with multiple identifiers bound (which behave like nested with's).
;; Finally we add the promised facilities above and a bit more management of
;; strings.

;; LATER, we'll extend this language to support prototype-based OOP.
;; For now, let's talk about the base "Quipu" language, which extends our
;; "CFWAE" interpreter to support strings, and gives powerful meanings to its
;; strings!
;;    (for the name origins, see https://en.wikipedia.org/wiki/Quipu)

;; A full EBNF is below. We first focus on the entirely new features:

;; We add strings:
;;   <S-Expr> ::= <string>                        ; Evaluates to the string
;;              | {num->str <S-Expr>}             ; Evaluates the expression to a number and returns a string version of that number
;;              | {print <S-Expr>}                ; Evaluates the expression to a string, prints it, and evaluates to that string
;;              | {append <S-Expr> <S-Expr>}      ; Evaluates to the result of appending the string results of evaluating the expressions

;; And errors:
;;              | {error <S-Expr>}                ; Evaluates the expression to a string and raises an error with that string as text

;; But the truly powerful features are these ones, str->id and ifdef:

;;              | {str->id <S-Expr>}
;;              | {ifdef <S-Expr> <S-Expr> <S-Expr>}

;; str->id checks that S-Expr is a string and then behaves as the equivalent id
;; reference (it will be looked up in the environment!). This lets us construct
;; identifiers to use dynamically. Note that it is NOT additionally desugared
;; to be unboxed, as normal id references are.

;; So, for example:

;;    {with {{x 1}} {unbox {str->id "x"}}}

;; will return 1. (Notice that using these powerful features imposes on end-user
;; programmers the requirement to understand the boxing/unboxing transformation we
;; perform in desugaring along with lots of other dangerous reasoning, like avoiding
;; reserved identifiers. This is DANGEROUS!)
;;
;; This second example:

;;    {with {{x 1}} {str->id "free-name"}}

;; will produce a runtime error (for unbound/free identifiers)

;; For expressions A, B, and C, {ifdef A B C} has the following semantics:
;;     - if {str->id A} would not produce a free-identifier error, run B
;;     - if {str->id A} would produce a free-identifier error (i.e. is "undefined"), run C.

;; This is the end of the description of the extensions in the Quipu Language.

;; We're going to consider Quipu to be an intermediate language (like Java Bytecode or the
;; .NET intermediate language CIL). Our end user programmers won't generally write programs
;; in it. Instead, they'll use "QuipuScript".

;; We can produce this extended language QuipuScript, which adds property-based
;; objects on top of Quipu. AN AWESOME FEATURE IS THAT QUIPU HAS ALL WE NEED TO
;; IMPLEMENT OBJECTS!
;;
;; Thus, QuipuScript DESUGARS into Quipu.
;;
;; ALL OF THE FUN AND INTERESTING OBJECT PARTS OF QUIPUSCRIPT THUS HAPPEN AT THE PARSER/DESUGARER
;; LEVEL.
;;
;; You only need to understand how the interpretation of Quipu Works.
;; In fact, WE DO NOT HAVE AN INTERPRETER FOR QuipuScript, just an interpreter for Quipu!

;; Here's the implementation for Quipu. The description of QuipuScript happens after!
;; 
;; (Aside: S-Expr and D-Expr here and below are for surface and desugared expressions.)
;;
;; Syntax specification:
;;
;; <S-Expr> ::= <num>
;;            | <id>
;;            | {+ <S-Expr> <S-Expr>}
;;            | {- <S-Expr> <S-Expr>}
;;            | {* <S-Expr> <S-Expr>}
;;            | {with {{<id> <S-Expr>}*} <S-Expr>} ; <- all names defined simultaneously, like let.
;;            | {with* {{<id> <S-Expr>}*} <S-Expr>} ; <- like let*! you can use names later on.
;;            | {if0 <S-Expr> <S-Expr> <S-Expr>}
;;            | {fun {<id>*} <S-Expr>}
;;            | {<S-Expr> <S-Expr>*}
;;            | {box <S-Expr>}
;;            | {setbox! <S-Expr> <S-Expr>}
;;            | {unbox <S-Expr>}
;;            | {seqn <S-Expr> <S-Expr>}
;;            | {set! <id> <S-Expr>}
;;
;;            | <string>
;;            | {num->str <S-Expr>}
;;            | {print <S-Expr>}
;;            | {append <S-Expr> <S-Expr>}
;;            | {error <S-Expr>}
;;            | {str->id <S-Expr>}
;;            | {ifdef <S-Expr> <S-Expr> <S-Expr>}

;; We first implement this language, with the desugaring steps from before.

;; We're going to make desugaring an explicit step.  So, here's the
;; "surface" language that our end-user programmers program in:
(define-type S-Expr
  [s-num (n number?)]
  [s-id (name symbol?)]
  [s-add (lhs S-Expr?) (rhs S-Expr?)]
  [s-sub (lhs S-Expr?) (rhs S-Expr?)]
  [s-mult (lhs S-Expr?) (rhs S-Expr?)]
  [s-with (name (listof symbol?)) (named-exp (listof S-Expr?)) (body S-Expr?)]
  [s-with* (name (listof symbol?)) (named-exp (listof S-Expr?)) (body S-Expr?)]
  [s-fun (arg-names (listof symbol?)) (body S-Expr?)]
  [s-app (fun-exp S-Expr?) (arg-exprs (listof S-Expr?))]
  [s-if0 (test-exp S-Expr?) (then-exp S-Expr?) (else-exp S-Expr?)]
  [s-box (val-exp S-Expr?)]
  [s-setbox! (box-exp S-Expr?) (val-exp S-Expr?)]
  [s-un-box (box-exp S-Expr?)]
  [s-seqn (exp1 S-Expr?) (exp2 S-Expr?)]
  [s-set! (var symbol?) (val-expr S-Expr?)]
  [s-str (str string?)]
  [s-numstr (ne S-Expr?)]
  [s-print (str S-Expr?)]
  [s-append (str1 S-Expr?) (str2 S-Expr?)]
  [s-err (msg S-Expr?)]
  [s-strid (id S-Expr?)]
  [s-ifdef (test-exp S-Expr?) (def-exp S-Expr?) (undef-exp S-Expr?)]
  )

;; Here's the language our interpreter will understand.  Note that it
;; lacks "with", "with*", AND "set!".  "D-Expr" is for "desugared Expr":
;; note it has this extra "Lookup-string function"
(define-type D-Expr
  [num (n number?)]
  [id (name symbol?)]
  [add (lhs D-Expr?) (rhs D-Expr?)]
  [mult (lhs D-Expr?) (rhs D-Expr?)]
  [fun (arg-names (listof symbol?)) (body D-Expr?)]
  [app (fun-exp D-Expr?) (arg-exps (listof D-Expr?))]
  [if0 (test-exp D-Expr?) (then-exp D-Expr?) (else-exp D-Expr?)]
  [make-box (val-exp D-Expr?)]
  [setbox! (box-exp D-Expr?) (val-exp D-Expr?)]
  [un-box (box-exp D-Expr?)]
  [q-str (str string?)]
  [q-numstr (ne D-Expr?)]
  [q-print (str D-Expr?)]
  [q-append (str1 D-Expr?) (str2 D-Expr?)]
  [q-err (msg D-Expr?)]
  [q-strid (id D-Expr?)]
  [q-ifdef (test-exp D-Expr?) (def-exp D-Expr?) (undef-exp D-Expr?)]
  )

(define *reserved-symbols* '(+ - * with with* fun if0 box setbox! unbox seqn set!
                               print append error str->id num->str ifdef
                               new ex-nihilo prototype obj-get obj-set! ->))

;; valid-identifier? : any -> boolean
;; Determines whether the parameter is valid as an identifier name, i.e.,
;; a symbol that is not reserved.
(define (valid-identifier? sym)
  (and (symbol? sym)
       (not (member sym *reserved-symbols*))))

;; Some reserved symbols.
(test (valid-identifier? '+) false)
(test (valid-identifier? '-) false)
(test (valid-identifier? 'with) false)
(test (valid-identifier? 'setbox!) false)

;; Not a symbol
(test (valid-identifier? '{+ 1 2}) false)
(test (valid-identifier? 3) false)
(test (valid-identifier? "id") false)

;; OK
(test (valid-identifier? 'id) true)
(test (valid-identifier? 'app) true)
(test (valid-identifier? 'x) true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; PARSING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We define an extendable parse function, and then we implement two specialized versions of it:
;; The Quipu parser is 'parse'
;; The QuipuScript parser is 'parse-qs'.

;; parse-extendable: any (any -> S-Expr) -> S-Expr
;; Consumes an s-expression (in our concrete "surface" syntax) and
;; generates the corresponding S-Expr AST.
;; Note that it contains all the shared parsing from Quipu and Quipuscript.
(define (parse-extendable sexp extension)
  (local
    [(define (parse-extendable sexp)
       (match sexp
         [(? valid-identifier?) (s-id sexp)]
         [(? number?) (s-num sexp)]
         [(? string?) (s-str sexp)]
         [(list '+ lexp rexp) (s-add (parse-extendable lexp) (parse-extendable rexp))]
         [(list '- lexp rexp) (s-sub (parse-extendable lexp) (parse-extendable rexp))]
         [(list '* lexp rexp) (s-mult (parse-extendable lexp) (parse-extendable rexp))]
         [(list 'with (list (list (and (? valid-identifier?) ids) binding-exprs) ...) body-expr)
          (s-with ids (map parse-extendable binding-exprs) (parse-extendable body-expr))]
         [(list 'with* (list (list (and (? valid-identifier?) ids) binding-exprs) ...) body-expr)
          (s-with* ids (map parse-extendable binding-exprs) (parse-extendable body-expr))]
         [(list 'fun (list (? valid-identifier? ids) ...) body-expr)
          (s-fun ids (parse-extendable body-expr))]
         [(list 'if0 c-expr t-expr e-expr)
          (s-if0 (parse-extendable c-expr) (parse-extendable t-expr) (parse-extendable e-expr))]
         [(list 'ifdef c-expr t-expr e-expr)
          (s-ifdef (parse-extendable c-expr) (parse-extendable t-expr) (parse-extendable e-expr))]
         ;; Don't parse (<reserved> <expr>) as a function application.
         [(cons (and f-expr (? (lambda (s) (not (member s *reserved-symbols*))))) a-exprs)
          (s-app (parse-extendable f-expr) (map parse-extendable a-exprs))]
         [(list 'box v-expr) (s-box (parse-extendable v-expr))]
         [(list 'unbox b-expr) (s-un-box (parse-extendable b-expr))]
         [(list 'setbox! b-expr v-expr) (s-setbox! (parse-extendable b-expr) (parse-extendable v-expr))]
         [(list 'seqn expr1 expr2) (s-seqn (parse-extendable expr1) (parse-extendable expr2))]
         [(list 'set! (? valid-identifier? id) expr) (s-set! id (parse-extendable expr))]
         [(list 'print p-expr) (s-print (parse-extendable p-expr))]

         ; DONE #1: implement append parsing
         ; HINT: For this TODO and others, it may help to write a test case
         ;       or find a specific one of ours to attend to as you plan your implementation.
         [(list 'append first-expr second-expr)
          (s-append (parse-extendable first-expr) (parse-extendable second-expr))]
         [(list 'error e-expr) (s-err (parse-extendable e-expr))]
         [(list 'str->id s-expr) (s-strid (parse-extendable s-expr))]
         [(list 'num->str s-expr) (s-numstr (parse-extendable s-expr))]
         [else (extension sexp)]))]
    (parse-extendable sexp)
    ))

; Extensions work:
(test (parse-extendable '{+} (lambda (x) "test passed")) "test passed")

; but are only invoked if needed:
(test (parse-extendable '{+ 1 2} (lambda (x) "test passed")) (s-add (s-num 1) (s-num 2)))

; Otherwise, we're currently focused on the plain Quipu parser:
(define (parse sexp)
  ; Parse for Quipu only needs to error if the expression does not match.
  ; For more interesting uses of parse-extendable, look for the parse-qs function!
  (parse-extendable sexp
                    (lambda (sexp)
                      (error 'parse "unable to parse the s-expression ~s" sexp))))



;; IDs
(test (parse 'x) (s-id 'x))
(test (parse 'ys) (s-id 'ys))
(test/exn (parse '+) "")

;; strings
(test (parse "hello") (s-str "hello"))
(test (parse "") (s-str ""))
(test (parse '{num->str 3}) (s-numstr (s-num 3))) 

;; print
(test (parse '{print 1}) (s-print (s-num 1)))  ; runtime error!

;; append
(test (parse '{append 1 2}) (s-append (s-num 1) (s-num 2))) ; runtime error!

;; error
(test (parse '{error "d'oh!"}) (s-err (s-str "d'oh!")))

;; str->id
(test (parse '{str->id "huh"}) (s-strid (s-str "huh")))

;; ifdef
(test (parse '{ifdef "a" "b" "c"})
      (s-ifdef (s-str "a")
               (s-str "b")
               (s-str "c")))

;; Boxes
(test (parse '{box 0}) (s-box (s-num 0)))
(test (parse '{unbox 0}) (s-un-box (s-num 0)))  ;; runtime error, but not parsing error
(test (parse '{setbox! 0 1}) (s-setbox! (s-num 0) (s-num 1)))  ;; ditto non-parsing error

;; Seqn
(test (parse '{seqn 0 1}) (s-seqn (s-num 0) (s-num 1)))

;; Set!
(test (parse '{set! x 1}) (s-set! 'x (s-num 1)))
(test/exn (parse '{set! seqn 1}) "")

;; Numbers
(test (parse '3) (s-num 3))
(test (parse '0) (s-num 0))

;; Plain arithmetic.
(test (parse '{+ 1 2}) (s-add (s-num 1) (s-num 2)))
(test (parse '{- 1 2}) (s-sub (s-num 1) (s-num 2)))
(test (parse '{+ 3 4}) (s-add (s-num 3) (s-num 4)))
(test (parse '{- 3 4}) (s-sub (s-num 3) (s-num 4)))
(test (parse '{* 3 4}) (s-mult (s-num 3) (s-num 4)))

(test (parse '{+ {- 1 {+ 2 3}} 4})
      (s-add (s-sub (s-num 1) (s-add (s-num 2) (s-num 3)))
             (s-num 4)))

;; With binding
(test (parse '{with {} 1}) (s-with empty empty (s-num 1)))
(test (parse '{with {{x 1}} x}) (s-with '(x) (list (s-num 1)) (s-id 'x)))
(test (parse '{with {{a 1} {b 2} {c 3}} 4})
      (s-with '(a b c)
              (list (s-num 1) (s-num 2) (s-num 3))
              (s-num 4)))
(test (parse '{with {{x {with {{y 2}} {+ x y}}}} {with {{z 3}} {+ x z}}})
      (s-with '(x) (list (s-with '(y) (list (s-num 2)) (s-add (s-id 'x) (s-id 'y))))
              (s-with '(z) (list (s-num 3)) (s-add (s-id 'x) (s-id 'z)))))

;; With* binding
(test (parse '{with* {} 1}) (s-with* empty empty (s-num 1)))
(test (parse '{with* {{x 1}} x}) (s-with* '(x) (list (s-num 1)) (s-id 'x)))
(test (parse '{with* {{a 1} {b 2} {c 3}} 4})
      (s-with* '(a b c)
               (list (s-num 1) (s-num 2) (s-num 3))
               (s-num 4)))

;; if0
(test (parse '{if0 a b c}) (s-if0 (s-id 'a) (s-id 'b) (s-id 'c)))

;; Funs/Apps
(test (parse '{fun {} 1}) (s-fun '() (s-num 1)))
(test (parse '{fun {x} x}) (s-fun '(x) (s-id 'x)))
(test (parse '{fun {x y} x}) (s-fun '(x y) (s-id 'x)))
(test/exn (parse '{fun {fun} x}) "")
(test (parse '{1}) (s-app (s-num 1) (list)))
(test (parse '{1 2}) (s-app (s-num 1) (list (s-num 2))))
(test (parse '{1 2 3 4}) (s-app (s-num 1) (list (s-num 2) (s-num 3) (s-num 4))))

;; Error checking

; non-lists, reserved symbols (e.g., + and -), strings
(test (parse '"hello") (s-str "hello"))
(test/exn (parse '+) "")
(test/exn (parse '-) "")
(test/exn (parse 'with) "")


; lists that start with things besides +, -, or with, esp. numbers
; that aren't valid apps:
(test (parse '{hello 1 2}) (s-app (s-id 'hello) (list (s-num 1) (s-num 2))))
(test (parse '{"abc"}) (s-app (s-str "abc") '()))
(test (parse '{1 2 3}) (s-app (s-num 1) (list (s-num 2) (s-num 3))))

; + with fewer or more than 2 arguments
(test/exn (parse '{+}) "")
(test/exn (parse '{+ 1}) "")
(test/exn (parse '{+ 1 2 3}) "")

; - with fewer or more than 2 arguments
(test/exn (parse '{-}) "")
(test/exn (parse '{- 1}) "")
(test/exn (parse '{- 1 2 3}) "")

; ill-structured with
(test/exn (parse '{with}) "")
(test/exn (parse '{with x}) "")
(test/exn (parse '{with x 2 3}) "")
(test/exn (parse '{with {x 1}}) "")
(test/exn (parse '{with {x 1} 2 3}) "")
(test/exn (parse '{with {x 1 2} 3}) "")
(test/exn (parse '{with {+ 1} 2}) "")

; + (and -/with) with non-AEs as arguments
(test (parse '{+ "a" 3}) (s-add (s-str "a") (s-num 3)))
(test (parse '{- 1 "b"}) (s-sub (s-num 1) (s-str "b")))
(test/exn (parse '{+ {- 12 #\c} 8}) "")
(test (parse '{with {{x "foo"}} x}) (s-with '(x) (list (s-str "foo")) (s-id 'x)))
(test (parse '{with {{x 1}} "foo"}) (s-with '(x) (list (s-num 1)) (s-str "foo")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; desugar: S-Expr -> D-Expr
;; desugar from the surface language to the underlying one
;; this is really more substantial than a "simple" desugaring now; so, we may want
;; to think of this as a compilation step. Critically, we introduce boxes around the
;; values of all identifiers and auto-unbox when referencing an identifier.
;;
;; We also desugar away some constructs like with and subtraction.
(define (desugar ast)
  (type-case S-Expr ast
    [s-set! (var exp) (setbox! (id var) (desugar exp))]
    
    [s-num (n) (num n)]

    ; DONE #2: fix the minor typo in this desugaring and remind yourself that
    ; we desugar ID references to wrap them in an {unbox ...} and function
    ; applications to wrap each argument expression in a {box ...}.
    [s-id (name) (un-box (id name))]

    [s-add (lhs rhs) (add (desugar lhs) (desugar rhs))]
    [s-sub (lhs rhs) (add (desugar lhs) (mult (num -1) (desugar rhs)))]
    [s-mult (lhs rhs) (mult (desugar lhs) (desugar rhs))]

    ; DONE #3: implement desugaring in terms of function application.
    ; NOTE: {with {{x 1} {y x}} y} should produce an ERROR not 1,
    ;       although {with* {{x 1} {y x}} x} produces 1.
    ;
    ; Hint: remember that functions can now take multiple parameters!
    ; Also, notice how the recursive desugaring ensures we "wrap" the
    ; argument expressions in boxes properly (see the desugaring for
    ; s-app if you're not sure what this means!).
    [s-with (names named-exprs body)
            (desugar (s-app (s-fun names body)
                            named-exprs))]
    [s-with* (names named-exprs body)
             (desugar (foldr (lambda (name named-expr acc-desugaring)
                               (s-app (s-fun (list name) acc-desugaring)
                                      (list named-expr)))
                             body
                             names
                             named-exprs))]
    [s-fun (arg-names body) (fun arg-names (desugar body))]
    [s-app (fun-exp arg-exps)
           (app (desugar fun-exp) (map (lambda (arg) (make-box (desugar arg))) arg-exps))]
    [s-if0 (c t e) (if0 (desugar c) (desugar t) (desugar e))]
    [s-box (v) (make-box (desugar v))]
    [s-un-box (b) (un-box (desugar b))]
    [s-setbox! (b v) (setbox! (desugar b) (desugar v))]
    [s-seqn (e1 e2) (desugar (s-with '(seqn) (list e1) e2))]
    [s-str (s) (q-str s)]
    [s-append (e1 e2) (q-append (desugar e1) (desugar e2))]
    [s-print (p) (q-print (desugar p))]
    [s-err (e) (q-err (desugar e))]
    [s-strid (s) (q-strid (desugar s))]
    [s-numstr (n) (q-numstr (desugar n))]
    [s-ifdef (c d u) (q-ifdef (desugar c) (desugar d) (desugar u))]
    ))




;; Numbers
(test (desugar (parse '3)) (num 3))
(test (desugar (parse '0)) (num 0))

;; IDs
(test (desugar (parse 'x)) (un-box (id 'x)))
(test (desugar (parse 'ys)) (un-box (id 'ys)))

;; Plain arithmetic.
(test (desugar (parse '{+ 1 2})) (add (num 1) (num 2)))
(test (desugar (parse '{- 1 2})) (add (num 1) (mult (num -1) (num 2))))
(test (desugar (parse '{* 3 4})) (mult (num 3) (num 4)))

;; With binding
(test (desugar (parse '{with {{x 1} {y 2}} x})) (app (fun '(x y) (un-box (id 'x))) (list (make-box (num 1)) (make-box (num 2)))))

;; With* binding
(test (desugar (parse '{with* {} x})) (un-box (id 'x)))
(test (desugar (parse '{with* {{x 1} {y 2}} x}))
      (app (fun '(x)
                (app (fun '(y) (un-box (id 'x)))
                     (list (make-box (num 2)))))
           (list (make-box (num 1)))))

;; Funs/Apps
(test (desugar (parse '{fun {} x})) (fun '() (un-box (id 'x))))
(test (desugar (parse '{fun {x y} x})) (fun '(x y) (un-box (id 'x))))
(test (desugar (parse '{1})) (app (num 1) (list)))
(test (desugar (parse '{1 2 4})) (app (num 1) (list (make-box (num 2)) (make-box (num 4)))))

;; if0
(test (desugar (parse '{if0 1 2 3})) (if0 (num 1) (num 2) (num 3)))

;; Boxes
(test (desugar (parse '{box 0})) (make-box (num 0)))
(test (desugar (parse '{unbox 0})) (un-box (num 0)))  ;; runtime error, but not parsing error
(test (desugar (parse '{setbox! 0 1})) (setbox! (num 0) (num 1)))  ;; ditto non-parsing error

;; Seqn
(test (desugar (parse '{seqn 0 1})) (desugar (s-with '(seqn) (list (s-num 0)) (s-num 1))))


;; Set!
(test (desugar (parse '{set! x 1})) (setbox! (id 'x) (num 1)))

;; strings and string/id functions
(test (desugar (parse "hello")) (q-str "hello"))
(test (desugar (parse '{append 1 2}))
      (q-append (num 1) (num 2)))
(test (desugar (parse '{error "boo!"}))
      (q-err (q-str "boo!")))
(test (desugar (parse '{str->id "x"}))
      (q-strid (q-str "x")))
(test (desugar (parse '{num->str "x"}))
      (q-numstr (q-str "x")))
(test (desugar (parse '{ifdef 1 2 3}))
      (q-ifdef (num 1) (num 2) (num 3)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; INTERPRETATION ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values in our internal "desugared" abstract syntax:
(define-type Value 
  [numV (n number?)]
  [strV (s string?)]
  [boxV (inside number?)]
  [closureV (arg-names (listof symbol?)) (body D-Expr?) 
            (env Env?)])

;; The environment that stores our "deferred substitutions":
(define-type Env 
  [mtEnv]
  [anEnv (id symbol?) 
         (val Value?) 
         (more-subs Env?)])

;; lookup : symbol Env -> Value
;; Finds the value of name in env or errors if name is undefined
(define (lookup name env)
  (local ([define (lookup-helper name env)
            (type-case Env env
              [mtEnv () (error 'lookup "free identifier ~a" name)]
              [anEnv (bound-name bound-value rest-env)
                     (if (symbol=? bound-name name)
                         bound-value
                         (lookup-helper name rest-env))])])
    (lookup-helper name env)))

;; defined? : symbol Env -> boolean
;; Looks for the value of name in env. True if it is defined, false if it is not.
(define (defined? name env)
  (local ([define (defined?-helper name env)
            (type-case Env env
              [mtEnv () #f]
              [anEnv (bound-name bound-value rest-env)
                     (if (symbol=? bound-name name)
                         #t
                         (defined?-helper name rest-env))])])
    (defined?-helper name env)))

;; The Store represents the contents of memory: the values associated
;; with each location/memory cell.
(define-type Store
  [mtSto]
  [aStore (location number?) (value Value?) (restStore Store?)])

;; allocate-locn : Store -> number
;; produce a memory location that is unused in the Store
(define (allocate-locn sto)
  (local [(define (max-locn sto)
            (type-case Store sto
              ; 1000 should really be a constant defined somewhere, but oh well! :)
              [mtSto () (- 1000 1)]
              [aStore (alloc-locn stored-value rest-sto)
                      (max alloc-locn (max-locn rest-sto))]))]
    (+ 1 (max-locn sto))))

(test (allocate-locn (mtSto)) 1000)
(test (allocate-locn (aStore 1003 (numV 1) (aStore 1017 (numV 1)
                                                   (aStore 1002 (numV 1) (mtSto)))))
      1018)

;; lookup-store : number Store -> Value
;; Finds the value at locn in sto or errors if locn does not exist
(define (lookup-store locn sto)
  (local ([define (lookup-helper locn sto)
            (type-case Store sto
              [mtSto () (error 'lookup-store "unallocated memory location ~a" locn)]
              [aStore (alloc-locn stored-value rest-sto)
                      (if (= alloc-locn locn)
                          stored-value
                          (lookup-helper locn rest-sto))])])
    (lookup-helper locn sto)))


(test/exn (lookup-store 1 (mtSto)) "")
(test (lookup-store 1 (aStore 1 (numV 1) (mtSto))) (numV 1))
(test/exn (lookup-store 2 (aStore 1 (numV 1) (mtSto))) "")
(test (lookup-store 1 (aStore 1 (numV 10)
                              (aStore 2 (numV 5)
                                      (aStore 1 (numV 1) (mtSto)))))
      (numV 10))
(test (lookup-store 2 (aStore 1 (numV 10)
                              (aStore 2 (numV 5)
                                      (aStore 1 (numV 1) (mtSto)))))
      (numV 5))


;; A Value and Store bundled together so we can return both from interpretation.
(define-type ValuexStore
  [v*s (value Value?) (store Store?)])

;; This function takes a Value*Store and produces values, so that we can
;; keep using define-values inside a local.
;; ValuexStore -> (Value Store)
(define (v*s->values v)
  (type-case ValuexStore v
    [v*s (value store) (values value store)]))

;; assert-type: (Value -> bool) Value -> Value
;; if (pred value) is true, just return value
;; otherwise, produce an error
;; streamlines type-checking in our interpreter
(define (assert-type pred value)
  (if (pred value)
      value
      (error 'interp "received a value of the wrong type: ~a; expected ~a" value pred)))

(test (assert-type numV? (numV 0)) (numV 0))
(test (assert-type numV? (numV 1)) (numV 1))
(test/exn (assert-type closureV? (numV 1)) "")
(test (assert-type closureV? (closureV '(x y) (id 'x) (mtEnv)))
      (closureV '(x y) (id 'x) (mtEnv)))


; assert-type-v*s: (Value -> bool) ValuexStore -> ValuexStore
; checks that pred applied to the value in val*sto is successful
; if not, produces an error
; if so, simply produces val*sto.
(define (assert-type-v*s pred val*sto)
  (local [(define-values (val sto)
            (v*s->values val*sto))]
    (v*s (assert-type pred val) sto)))

(test (assert-type-v*s numV? (v*s (numV 0) (mtSto))) (v*s (numV 0) (mtSto)))
(test (assert-type-v*s numV? (v*s (numV 10) (aStore 1000 (numV 1) (mtSto)))) (v*s (numV 10) (aStore 1000 (numV 1) (mtSto))))
(test/exn (assert-type-v*s closureV? (v*s (numV 0) (mtSto))) "")

;; interp : D-Expr Env Store -> ValuexStore
;; interprets exp in the given environment and store,
;; producing the resulting value and store.
(define (interp exp env sto)
  (local [;; +/* helpers to make interpretation easier
          (define (num+ x y)  (numV (+ (numV-n (assert-type numV? x)) (numV-n (assert-type numV? y)))))
          (define (num* x y)  (numV (* (numV-n (assert-type numV? x)) (numV-n (assert-type numV? y)))))

          (define (interp exp env sto)
            (error "Don't call me!!!"))
          
          ;; helper : D-Expr Env Store -> ValuexStore
          ;; evaluates the exp in env using the state sto 
          ;; and returns the value AND the next store to be used.
          (define (helper exp env sto)
            (type-case D-Expr exp
              [num (n)    (v*s (numV n) sto)]
              [add (l r)  (local [(define-values (lv lsto) 
                                    (v*s->values (helper l env sto)))
                                  (define-values (rv rsto) 
                                    (v*s->values (helper r env lsto)))]
                            (v*s (num+ lv rv) rsto))]
              [mult (l r)  (local [(define-values (lv lsto) 
                                     (v*s->values (helper l env sto)))
                                   (define-values (rv rsto) 
                                     (v*s->values (helper r env lsto)))]
                             (v*s (num* lv rv) rsto))]
              [id  (name) (v*s (lookup name env) sto)]
              [fun (arg-names body) (v*s (closureV arg-names body env) sto)]
              [if0 (tst thn els) 
                   (local [(define-values (tst-val tst-sto) 
                             (v*s->values (helper tst env sto)))]
                     (type-case Value tst-val 
                       [numV (n) (if (zero? n)
                                     (helper thn env tst-sto)
                                     (helper els env tst-sto))]
                       [else (error 'interp "The test expression of an if0 must evaluate to a number.")]))]
              [app (f args)
                   (local [(define-values (the-fun f-sto) 
                             (v*s->values (helper f env sto)))

                           ; eval-args: (listof D-Expr) Store -> (listof Value) Store
                           ; given a list of expressions to be evaluated, evaluates them in left-to-right
                           ; order, threading the state through all computations, and returns the
                           ; resulting list of values and the final store.
                           (define (eval-args args sto)
                             (if (empty? args)
                                 (values args sto)
                                 (local [(define-values (fst-val fst-sto)
                                           (v*s->values (helper (first args) env sto)))
                                         (define-values (rest-vals final-sto)
                                           (eval-args (rest args) fst-sto))]
                                   (values (cons fst-val rest-vals) final-sto))))
                           (define-values (arg-vals a-sto) 
                             (eval-args args f-sto))]
                     (type-case Value the-fun
                       [closureV (arg-names body closure-env)
                                 ; DONE #4: add the error handling that's missing here!
                                 ; (This may be tricky to find until you fix most other errors.
                                 ; If so, just leave it to the end!)
                                 (if (= (length arg-names) (length arg-vals))
                                     (helper body
                                             ; Adds pairs of name/value to the environment
                                             ; for each parameter name and argument value.
                                             (foldl anEnv
                                                    closure-env
                                                    arg-names
                                                    arg-vals)
                                             a-sto)
                                     (error 'interp "number arguments for function appliction should equal to the number of params"))]
                       [else (error 'interp "You can only apply closures! You tried to apply ~a (in: ~a)" the-fun exp)]))]
              [make-box (be)
                        (local [(define-values (be-val be-sto)
                                  (v*s->values (helper be env sto)))
                                (define locn-l (allocate-locn be-sto))
                                (define new-sto (aStore locn-l be-val be-sto))]
                          (v*s (boxV locn-l) new-sto))]
              [setbox! (be ve)
                       (local [(define-values (be-val be-sto)
                                 (v*s->values (helper be env sto)))]
                         (type-case Value be-val
                           [boxV (locn) (local [(define-values (ve-val ve-sto)
                                                  (v*s->values (helper ve env be-sto)))]
                                          (v*s ve-val
                                               (aStore locn ve-val ve-sto)))]
                           [else (error 'interp "Attempt to setbox a non-box")]))]
              [un-box (be)
                      (local [(define-values (be-val be-sto)
                                (v*s->values (helper be env sto)))]
                        (type-case Value be-val
                          [boxV (locn) (v*s (lookup-store locn be-sto) be-sto)]
                          [else (error 'interp "Attempt to unbox a non-box : ~a" be-val)]))]
              
              ;; Quipu additions
              [q-str (str)
                     (v*s (strV str) sto)]
              [q-print (str)
                       (local [(define-values (s-val s-sto)
                                 (v*s->values (helper str env sto)))]
                         (type-case Value s-val
                           [strV (str) (begin
                                         (displayln str)
                                         (v*s s-val s-sto))]
                           [else (error 'interp "Attempted to print a non string")]))]
              ; DONE #5: Finish the implementation of append.
              ; Be sure to:
              ; 1) Evaluate str1
              ; 2) Check the type of str1 (assert-type-v*s may come in handy for this!)
              ; 3) Evaluate str2
              ; 4) Check the type of str2
              ; 5) Extract the string components of str1 and str2
              ; 6) Return the result of appending these string components. (Racket's string-append will be handy!)
              [q-append (str1 str2)
                        (local [(define-values (s1-val s1-sto)
                                  (v*s->values (assert-type-v*s strV? (helper str1 env sto))))
                                (define-values (s2-val s2-sto)
                                  (v*s->values (assert-type-v*s strV? (helper str2 env s1-sto))))]
                          (v*s (strV (string-append (strV-s s1-val) (strV-s s2-val))) s2-sto))]
              [q-err (msg)
                     (local [(define-values (m-val m-sto)
                               (v*s->values (helper msg env sto)))]
                       (type-case Value m-val
                         [strV (str)
                               (error str)]
                         [else (error 'interp "Quipu error : message is not a string")]))]
              [q-numstr (ne)
                        (local [(define-values (ne-val ne-sto)
                                  (v*s->values (helper ne env sto)))]
                          (v*s (strV (number->string (numV-n (assert-type numV? ne-val)))) ne-sto))]
              ;; These two are the most interesting features of the Quipu language.
              [q-strid (id-str)
                       (local [(define-values (id-val id-sto)
                                 (v*s->values (helper id-str env sto)))]
                         (type-case Value id-val
                           [strV (str)
                                 (helper (id (string->symbol str))
                                         env id-sto)]
                           [else (error 'interp "str->id: argument is not a string")]))]
              [q-ifdef (test-exp def-exp undef-exp)
                       (local [(define-values (test-val test-sto)
                                 (v*s->values (helper test-exp env sto)))]
                         (type-case Value test-val
                           [strV (str)
                                 (if (defined? (string->symbol str) env)
                                     (helper def-exp env test-sto)
                                     (helper undef-exp env test-sto))]
                           [else (error 'interp "ifdef: test expression is not a string, but ~a" test-val)]))]
              ))]
    (helper exp env sto)))


;; Run a Quipu program including parsing, desugaring, and interpretation,
;; but giving back just the value (not the store).
;;
;; Defaults to use an empty environment and store, but these can be
;; passed optionally. (If passing the store, must also pass the environment.)
(define (run sexp (env (mtEnv)) (sto (mtSto)))
  (v*s-value (interp (desugar (parse sexp)) env sto)))




;; num, id
(test (run '1) (numV 1))
(test (run '2) (numV 2))
(test/exn (run 'x) "")
(test (run '{with {{x 1}} x}) (numV 1))
(test (run '{with {{y 2}} y}) (numV 2))

;; arithmetic
(test (run '{+ 1 2}) (numV 3))
(test (run '{* 1 2}) (numV 2))
(test (run '{- 1 2}) (numV -1))
(test (run '{+ {+ 1 0}
               {* 3 4}})
      (numV 13))

;; with and with*
(test (run '{with {{x "x"} {y "y"}} {append x y}}) (strV "xy"))
(test (run '{with {{x "x"} {y "y"}} {with {{x {append "foo" x}}} {append x y}}}) (strV "fooxy"))
(test/exn (run '{with {{x "x"} {x {append x "y"}}} x}) "")
(test (run '{with* {{x "x"} {x {append x "y"}}} x}) (strV "xy"))

;; if0
(test (run '{if0 0 10 100}) (numV 10))
(test (run '{if0 1 10 100}) (numV 100))

;; functions and application
(test (run '{fun {} x}) (closureV empty (un-box (id 'x)) (mtEnv)))
(test (run '{fun {} x} (anEnv 'x (numV 10) (mtEnv))) (closureV empty (un-box (id 'x)) (anEnv 'x (numV 10) (mtEnv))))
(test/exn (run '{{fun {} x}}) "") ; unbound ID
(test (run '{{fun {} x}} (anEnv 'x (boxV 1000) (mtEnv)) (aStore 1000 (numV 10) (mtSto))) (numV 10))

(test (run '{fun {a b c} 1}) (closureV '(a b c) (num 1) (mtEnv)))
(test (run '{{fun {a b} {append a b}} "start " "end"}) (strV "start end"))

; Wrong # of arguments
(test/exn (run '{{fun {x y} {+ x y}} 1}) "")
(test/exn (run '{{fun {x y} {+ x y}} 1 2 3}) "")

;; box, setbox!, unbox, seqn
(test (run '{box 1}) (boxV 1000))
(test (run '{unbox {box 1}}) (numV 1))
(test/exn (run '{unbox 1000}) "")
(test (run '{with {{x {box 1}}} {setbox! x 2}}) (numV 2))
(test (run '{with {{x {box 1}}}
                  {seqn {setbox! x 2}
                        {unbox x}}})
      (numV 2))
(test (run '{with* {{x {box 1}}
                    {y x}
                    {z {box 1}}}
                   {seqn {setbox! x 2}
                         {+ {unbox x} {+ {unbox y} {unbox z}}}}})
      (numV 5))
(test (run '{seqn 1 2}) (numV 2))

(test (run '{with {{b {box 5}}}
                  {+ {seqn {setbox! b 6} {unbox b}}
                     {unbox b}}})
      (numV 12))

(test (run '{with {{b {box 5}}}
                  {+ {unbox b}
                     {seqn {setbox! b 6} {unbox b}}}})
      (numV 11))

(test (run '{with {{b {box 0}}} {seqn {box {setbox! b 1}} {unbox b}}}) (numV 1))


;; set! basic tests
(test (run '{with {{x 1}}
                  {seqn {set! x 2}
                        x}})
      (numV 2))
(test (run '{with {{x 1}}
                  {seqn {set! x 2}
                        {+ {set! x {+ x 1}} x}}})
      (numV 6))

;; New in Quipu: strings, num->str, print, append, error, str->id, ifdef
(test (run "hello") (strV "hello"))
(test (run "goodbye") (strV "goodbye"))

(test (run '{num->str 3}) (strV "3"))
(test/exn (run '{num->str "3"}) "")

(test (run '{print "printed as part of testing"}) (strV "printed as part of testing"))

(test (run '{append "Good" "bye"}) (strV "Goodbye"))

(test/exn (run '{error "error msg"}) "error msg")

(test (run '{with {{b 1}} {unbox {str->id "b"}}}) (numV 1))
(test/exn (run '{with {{b 1}} {str->id "freename"}}) "")

(test (run '{ifdef "c" 1 2}) (numV 2))
(test (run '{with {{c 20}} {ifdef "c" 1 2}}) (numV 1))











;;;; ##### Now we can define QuipuScript just as a parsing extension!

;;
;; - Object Creation:
;;   <S-Expr> ::= ...
;;              | {new <parent> {<id> <S-Expr>}*}            
;;
;;   <parent> ::= ex_nihilo              ; meaning "from nothing"
;;              | {prototype <S-Expr>}
;;
;; - Object manipulation:
;;   <S-Expr> ::= ...
;;              | {obj-get <S-Expr> <id>}
;;              | {obj-set! <S-Expr> <id> <S-Expr>}
;;
;;   Since you will likely have some object properties that are functions
;;   (i.e., you'll have methods), we provide the following syntactic sugar:

;;   <S-Expr> ::= ...
;;              | {-> <S-Expr> <id> <S-Expr>*}
;;   to call method <id> on an object with the corresponding argument.
;;   that is, {-> o method arg1 arg2 arg3} would be much like Java's
;;   o.method(arg1, arg2, arg3).
;;
;;   However, when definining a method, you must EXPLICITLY mention the
;;   equivalent of Java's "this" parameter, much like Python forces end-user
;;   programmers to do. Rather than "this", we call the parameter "self" as
;;   a convention (NOT a language rule).
;;
;;   So, the definition of the method above might look like:
;;     {new ... {method {fun {self param1 param2 param3} ...}}}






(define (parse-qs expr)
  (parse-extendable
   expr
   (lambda (sexp)
     (local [(define (parse exp)
               (error "You should call parse-qs instead of parse here!"))]
       (match sexp

         ; {new ex-nihilo}
         ; DONE #6: finish this desugaring to implement creation of an empty object.
         ; HINT: look ahead at the {new {prototype <Expr>}} case below!
         [(list 'new 'ex-nihilo)
          ; The basic object is a function that takes a message and looks for it in the current
          ; environment. The "message" is essentially a field name. If it can find that name
          ; in the environment, then it returns its value. Otherwise, it gives an error.
          ;
          ; But, where do names come from? Keep reading..
          (parse-qs '{fun {msg}
                          {ifdef msg
                                 {str->id msg}
                                 {error "object does not have property"}}})]

         ; {new ex-nihilo {<id> <Expr>} ...}, with at least one name/value pair
         ;
         ; The (and ___ name-value-pairs) part lets us just refer to the whole list of name-value pairs
         ; but also check that the list is composed of the appropriate parts.
         [(list 'new 'ex-nihilo (and (list (? valid-identifier? names) values) name-value-pairs) ...)
          ; The object created by {new ex-nihilo} can already look up fields/messages in the environment.
          ; We just need to ensure that those messages are defined in the environment. So, we define
          ; them and let the {new ex-nihilo} object close over those definitions.
          (parse-qs `{with ,name-value-pairs
                           {new ex-nihilo}})]

         ; {new {prototype <Expr>}}
         [(list 'new (list 'prototype p))
          ; This behaves very much like the {new ex-nihilo} case above.
          ;
          ; However, if THIS object doesn't have the field, maybe its prototype does.
          ; So, if we don't find the message here, we recursively seek the message in
          ; the prototype. (If that doesn't have it, then it'll recursively check in ITS
          ; prototype, etc.)
          (parse-qs `{fun {msg}
                          {ifdef msg           ; does this object have a field named msg?
                                 {str->id msg} ; if so, return it. BUT, if not, then..
                                 {,p msg}}})]  ; check recursively if the prototype of this object has it.

         ; {new {prototype <Expr>} {<id> <Expr>} ...}, with at least one name/value pair
         ; DONE #7: finish this desugaring to implement creation of an empty object.
         ; HINT: check out the "EXACTLY analogous" case above! But...
         ;       it's worth understanding and not just copying. :)
         [(list 'new (list 'prototype p) (and (list (? valid-identifier? names) values) name-value-pairs) ...)
          ; This is EXACTLY analogous to the second ex-nihilo case above.
          (parse-qs `{with ,name-value-pairs
                           {new {prototype ,p}}})]

         ; {obj-get OBJ PROPERTY}
         [(list 'obj-get obj (? valid-identifier? property))
          ; Remember that if the object OBJ was created via new, then it's actually a function
          ; awaiting a message to tell it which field to access. So, we need to APPLY that function
          ; to the appropriate field name.
          ;
          ; Because we wrap identifier references in boxes, we also need to unbox the result to get at its value.
          ; DONE #8: fix the minor typo on the next line and understand what's going on here and in the next two cases!
          ; HINT: inside a quasi-quote (a back-quoted s-expression), a comma means to evaluate the next s-expression.
          (parse-qs `{unbox {,obj ,(symbol->string property)}})]

         ; {obj-set! OBJ PROPERTY NEWVAL}
         [(list 'obj-set! obj (? valid-identifier? property) newval)
          ; Check out obj-get above. Much like it, we want to send a message to the object to get
          ; the field.. but we don't want to unbox it. Instead, we want to SET what's in its box.
          (parse-qs `{setbox! {,obj ,(symbol->string property)}
                              ,newval})]

         ; Here's our syntactic sugare for method calls:
         ; {-> OBJ METHODNAME ARG1 ARG2 ...}
         ;
         ; We ASSUME every method has a first argument representing the object the method is
         ; called on. Different languages handle this differently. Java INSERTS this extra argument
         ; automatically at the method definition. At the call site, you say expr.method(arg1, arg2, ...),
         ; but really that's not much different from method(expr, arg1, arg2, ...). Python requires you to
         ; explicitly mention the extra argument at the method definition and handles method calls similarly.
         ;
         ; We'll use Python's style. Each method must EXPLICITLY have a first parameter representing the
         ; object (or you won't be able to call it with this syntactic sugar).
         ;
         ; So, an object with a single "method" with arguments x y will be defined as follows:
         ;
         ; {new ex-nihilo {method_name {fun {self x y} ...}}}
         ;
         ; Note the extra argument named "self". You can name that argument whatever you want (as in
         ; Python), but self is the conventional name for our language. You'd fill the method body
         ; in where we have ...
         [(list '-> obj (? valid-identifier? message) args ...)
          ; To desugar, we get the field named message from the object.
          ; That should give back a function of at least one argument.
          ; Then, we call the function but splicing in the object itself
          ; as the first argument.
          ;
          ; We could have done this with the backquote syntax, but it
          ; requires a new bit of syntax to splice in lists. So, we'll
          ; construct it manually instead:
          (parse-qs (cons
                     (list 'obj-get obj message) ; get the field and call it on..
                     (cons obj                   ; the object itself (our "self" value)
                           args)))               ; and all the rest of the arguments

          ; FYI, here's the backquote syntax, where ,@ means to evaluate its expression
          ; and then "splice" that into the current list. (So, it's not a single element
          ; but rather the rest of the list. The actual semantics are a bit more complex
          ; than that, but it's a good first pass!) We've commented this out.
          #;(parse-qs `{{obj-get ,obj ,message}  ; Fetch the method and apply it to..
                        ,obj ,@args})              ; the object itself and all the arguments.
          ]
         [else (error 'parse-qs "unable to parse the s-expression ~s" sexp)])))))


;Test suite

(define (run-qs sexp)
  (v*s-value (interp (desugar (parse-qs sexp)) (mtEnv) (mtSto))))




;; Basic new tests:
(test (run-qs '{obj-get {new ex-nihilo {x 1}} x}) (numV 1))       ; get a field
(test (run-qs '{obj-get {new ex-nihilo {x 1} {y 2}} x}) (numV 1)) ; get the RIGHT field
(test (run-qs '{obj-get {new ex-nihilo {x 1} {y 2}} y}) (numV 2)) ; get the RIGHT field

; Inheritance via prototyping works. So, parent.x = 1. parent.y = 2.
; child.x = 3. child.y = 2. child.z = 4.
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {obj-get parent x}})
      (numV 1)) ; parent.x == 1
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {obj-get parent y}})
      (numV 2)) ; parent.y == 2
(test/exn (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                           {child {new {prototype parent} {x 3} {z 4}}}}
                          {obj-get parent z}})
          "") ; there is no parent.z
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {obj-get child x}})
      (numV 3)) ; child.x == 3
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {obj-get child y}})
      (numV 2)) ; child.y == parent.y == 2
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {obj-get child z}})
      (numV 4)) ; child.z == 4
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}
                       {g-child {new {prototype child} {x 5} {y 4}}}}
                      {obj-get g-child y}})
      (numV 4)) ; child.z == 4

; Furthermore, if we set parent.x, that's seen in parent but not child.
; If we set parent.y, that's seen in both.
; If we set child.x, that's seen in child but not parent.
; If we set child.y, that's... HMM. WHAT DOES THAT MEAN?
; If we set child.z, that's (of course) seen in child but not parent.
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! parent x 10}
                            {obj-get parent x}}})
      (numV 10))  ; NEW parent.x == 10
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! parent x 10}
                            {obj-get child x}}})
      (numV 3))  ; NEW child.x is unchanged
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! parent y 10}
                            {obj-get parent y}}})
      (numV 10))  ; NEW parent.y == 10
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! parent y 10}
                            {obj-get child y}}})
      (numV 10))  ; NEW child.y == 10


(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! child x 10}
                            {obj-get parent x}}})
      (numV 1))  ; NEW parent.x unchanged
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! child x 10}
                            {obj-get child x}}})
      (numV 10))  ; NEW child.x == 10
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! child y 10}
                            {obj-get parent y}}})
      (numV 10))  ; DONE (ungraded): NEW parent.y is WHAT?
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! child y 10}
                            {obj-get child y}}})
      (numV 10))  ; DONE (ungraded): NEW child.y is WHAT?
(test/exn (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                           {child {new {prototype parent} {x 3} {z 4}}}}
                          {seqn {obj-set! child z 10}
                                {obj-get parent z}}})
          "")  ; STILL no parent.z
(test (run-qs '{with* {{parent {new ex-nihilo {x 1} {y 2}}}
                       {child {new {prototype parent} {x 3} {z 4}}}}
                      {seqn {obj-set! child z 10}
                            {obj-get child z}}})
      (numV 10))  ; NEW child.z == 10

; blank objects
(test/exn (run-qs '{obj-get {new ex-nihilo} a})
          "object does not have property")



;; -> tests

(test/exn (run-qs '{-> {new ex-nihilo} f 10}) "object does not have property")

(test (run-qs '{-> {new ex-nihilo {a 2} {f {fun {self x} {* {obj-get self a}
                                                            x}}}}
                   f
                   10})
      (numV 20))

(test (run-qs '{with {{obj {new ex-nihilo
                                {a 1}
                                {inc {fun {self x} {obj-set! self a {+ {obj-get self a} x}}}}}}}
                     {+ {-> obj inc 1}
                        {-> obj inc 1}}})
      (numV 5))
(test (run-qs '{-> {new ex-nihilo
                        {f {fun {self x y z} z}}}
                   f 10 15 34})
      (numV 34))

; Test of with*
(test (run-qs '{with* {{n1 10}
                       {n2 {+ 2 n1}}
                       {n3 {+ n1 n2}}}
                      n3})
      (numV 22))

;; Extra prototyping tests
(test (run-qs '{with* {{o1 {new ex-nihilo {b 2}}}
                       {o2 {new {prototype o1}
                                {b? {fun {self} {obj-get self b}}}}}}
                      {-> o2 b?}})
      (numV 2))

(test (run-qs '{with* {{o1 {new ex-nihilo {b 2}}}
                       {o2 {new {prototype o1}
                                {b 7}
                                {b? {fun {self} {obj-get self b}}}}}}
                      {-> o2 b?}})
      (numV 7))

(test (run-qs '{with {{o1 {new ex-nihilo {f {fun {self} 10}} {g {fun {self} {-> self f}}}}}}
                     {-> o1 g}})
      (numV 10))

(test (run-qs '{with* {{o1 {new ex-nihilo {f {fun {self} 10}} {g {fun {self} {-> self f}}}}}
                       {o2 {new {prototype o1} {f {fun {self} 55}}}}}
                      {-> o2 g}})
      (numV 55))

(test (run-qs '{with* {{o1 {new ex-nihilo {f {fun {self} 10}} {g {fun {self} {-> self f}}}}}
                       {o2 {new {prototype o1} {f {fun {self} 55}}}}}
                      {-> o2 g}})
      (numV 55))

;; Extra tests of set in super
(test (run-qs '{with* {{o1 {new ex-nihilo
                                {a 5}
                                {a? {fun {self} {obj-get self a}}}
                                {a! {fun {self new-val}
                                         {obj-set! self a new-val}}}}}
                       {o2 {new {prototype o1}}}
                       {side_effect {-> o1 a! 10}}}
                      {-> o1 a?}})
      (numV 10))
                    
(test (run-qs '{with* {{o1 {new ex-nihilo
                                {a 5}
                                {a? {fun {self} {obj-get self a}}}
                                {a! {fun {self new-val}
                                         {obj-set! self a new-val}}}}}
                       {o2 {new {prototype o1}}}
                       {side_effect {-> o1 a! 10}}}
                      {-> o2 a?}})
      (numV 10))

(test (run-qs '{with* {{o1 {new ex-nihilo
                                {a 5}
                                {a? {fun {self} {obj-get self a}}}
                                {a! {fun {self new-val}
                                         {obj-set! self a new-val}}}}}
                       {o2 {new {prototype o1}
                                {a 700}}}
                       {side_effect {-> o1 a! 10}}}
                      {-> o2 a?}})
      (numV 700))

(test (run-qs '{with* {{o1 {new ex-nihilo
                                {a 5}
                                {a? {fun {self} {obj-get self a}}}
                                {a! {fun {self new-val}
                                         {obj-set! self a new-val}}}}}
                       {o2 {new {prototype o1}
                                {a 700}}}
                       {side_effect {-> o2 a! 10}}}
                      {-> o2 a?}})
      (numV 10))

(test (run-qs '{with* {{o1 {new ex-nihilo
                                {a 5}
                                {a? {fun {self} {obj-get self a}}}
                                {a! {fun {self new-val}
                                         {obj-set! self a new-val}}}}}
                       {o2 {new {prototype o1}
                                {a 700}}}
                       {side_effect {-> o2 a! 10}}}
                      {-> o1 a?}})
      (numV 5))



;; State threading tests. We want to easily check whether
;; the state is correctly threaded through each expression.
;; So, we write a static transformation that takes an S-Expr
;; pgm and produces a new S-Expr that looks like
;;
#;{with* {{TT_STATE "<<"}               ;; TT for Threading Testing
          {TT_COUNT 1}
          
          ; When called with {num->str TT_COUNT} and a thunked
          ; version of expression e like {fun {} e}, appends
          ; "TT_COUNT<" to TT_STATE, adds 1 to TT_COUNT,
          ; evaluates e, and then appends ">TT_COUNT," to TT_STATE
          {TT_UPDATE
           {fun {TT_TEMP TT_e_THUNK}
                {with* {{TT_IGNORE {set! TT_COUNT {+ 1 TT_COUNT}}}
                        {TT_IGNORE {set! TT_STATE {append TT_STATE {append TT_TEMP "<"}}}}
                        {TT_VAL {TT_e_THUNK}}
                        {TT_IGNORE {set! TT_STATE {append TT_STATE {append ">" {append TT_TEMP ","}}}}}}
                       TT_VAL}}}}
         {seqn "TT_PROGRAM_LOCATION" {append TT_STATE
                                             {append {num->str TT_COUNT} ">>"}}}}
;;
;; except that each subexpression (including the overall
;; program) e in pgm is replaced by:
#;{TT_UPDATE {num->str TT_COUNT} {fun {} e}}
;;
;; In other words, this runs the program but actually produces
;; as output something like <<1<...>,n>>, which can be tested to
;; ensure state is threaded properly everywhere. (n here is the last
;; value of the count.

; tt-xform: S-Expr -> S-Expr
; see above for details
(define (tt-xform s-pgm)
  (local [(define wrapper
            (parse-qs
             `{with* {{TT_STATE "<<"}               ;; TT for Threading Testing
                      {TT_COUNT 1}
                      
                      ; When called with {num->str TT_COUNT} and a thunked
                      ; version of expression e like {fun {} e}, appends
                      ; "TT_COUNT<" to TT_STATE, adds 1 to TT_COUNT,
                      ; evaluates e, and then appends ">TT_COUNT," to TT_STATE
                      {TT_UPDATE
                       {fun {TT_TEMP TT_e_THUNK}
                            {with* {{TT_IGNORE {set! TT_COUNT {+ 1 TT_COUNT}}}
                                    {TT_IGNORE {set! TT_STATE {append TT_STATE {append TT_TEMP "<"}}}}
                                    {TT_VAL {TT_e_THUNK}}
                                    {TT_IGNORE {set! TT_STATE {append TT_STATE {append ">" {append TT_TEMP ","}}}}}}
                                   TT_VAL}}}}
                     {seqn "TT_PROGRAM_LOCATION" {append TT_STATE
                                                         {append {num->str TT_COUNT} ">>"}}}}))
          
          ; Given an S-Expr, wraps it in a call to TT_UPDATE to enable threading testing.
          (define (active-replacer s-exp)
            ; We want the equivalent of:
            #;{TT_UPDATE {num->str TT_COUNT} {fun {} s-exp}}
            (s-app (s-id 'TT_UPDATE) (list (s-numstr (s-id 'TT_COUNT)) (s-fun empty s-exp))))
          
          ; We don't want to start inserting threading testing until we reach "TT_PROGRAM_LOCATION",
          ; which is our placeholder for the program itself. So, we start with the identify function
          ; as our "replacer" but swap to active-replacer when we reach "TT_PROGRAM_LOCATION".
          (define (helper s-exp (replacer (lambda (s-exp) s-exp)))
            ; For most expressions, we recursively call helper with the same replacer.
            ; So, we have a function to help with that.
            (local [(define (rec s-exp) (helper s-exp replacer))]
              (replacer (type-case S-Expr s-exp
                          [s-set! (var exp) (s-set! var (rec exp))]    
                          [s-num (n) s-exp]
                          [s-id (name) s-exp]
                          [s-add (lhs rhs) (s-add (rec lhs) (rec rhs))]
                          [s-sub (lhs rhs) (s-sub (rec lhs) (rec rhs))]
                          [s-mult (lhs rhs) (s-mult (rec lhs) (rec rhs))]
                          [s-with (names named-exprs body)
                                  (s-with names (map rec named-exprs) (rec body))]
                          [s-with* (names named-exprs body)
                                   (s-with* names (map rec named-exprs) (rec body))]
                          [s-fun (arg-names body) (s-fun arg-names (rec body))]
                          [s-app (fun-exp arg-exps)
                                 (s-app (rec fun-exp) (map rec arg-exps))]
                          [s-if0 (c t e) (s-if0 (rec c) (rec t) (rec e))]
                          [s-box (v) (s-box (rec v))]
                          [s-un-box (b) (s-un-box (rec b))]
                          [s-setbox! (b v) (s-setbox! (rec b) (rec v))]
                          [s-seqn (e1 e2) (s-seqn (rec e1) (rec e2))]
                          [s-str (s) (if (string=? s "TT_PROGRAM_LOCATION")
                                         (helper s-pgm active-replacer)
                                         s-exp)]
                          [s-append (e1 e2) (s-append (rec e1) (rec e2))]
                          [s-print (p) (s-print (rec p))]
                          [s-err (e) (s-err (rec e))]
                          [s-strid (s) (s-strid (rec s))]
                          [s-numstr (n) (s-numstr (rec n))]
                          [s-ifdef (c d u) (s-ifdef (rec c) (rec d) (rec u))]
                          ))))]
    (helper wrapper)))

; Does the thread testing run from s-expression (i.e., concrete syntax) to value.
; Note that the value will be the string created by thread testing NOT the program's
; actual value. (And also NOT a strV, but a string.)
(define (run-qs-for-tt code (env (mtEnv)) (sto (mtSto)))
  (strV-s (v*s-value (interp (desugar (tt-xform (parse-qs code))) env sto))))


;;;;;;;;;;;;;; MUTATION TESTING ;;;;;;;;;;;;;;;;;;;;


;; Numbers and other "dead-end" syntactic forms.
;; Confirms that these produce the updated store.
(test (run-qs-for-tt '1) "<<1<>1,2>>")
(test (run-qs-for-tt '{fun {} x}) "<<1<>1,2>>")

; The ID case is a pain b/c we need to prep the environment/store to start things out.
(test (run-qs-for-tt 'x
                     (anEnv 'x (boxV 1000) (mtEnv))
                     (aStore 1000 (numV 10) (mtSto)))
      "<<1<>1,2>>")

(test (run-qs-for-tt '"hello") "<<1<>1,2>>")


;; num->str and other one-sub-expression syntactic forms.
(test (run-qs-for-tt '{num->str 1}) "<<1<2<>2,>1,3>>")
(test (run-qs-for-tt '{print "printed as part of testing"}) "<<1<2<>2,>1,3>>")
(test (run-qs-for-tt '{box 1}) "<<1<2<>2,>1,3>>")

(test (run-qs-for-tt '{str->id "x"}
                     (anEnv 'x (boxV 1000) (mtEnv))
                     (aStore 1000 (boxV 1001)
                             (aStore 1001 (numV 2) (mtSto))))
      "<<1<2<>2,>1,3>>")
(test (run-qs-for-tt '{unbox x}
                     (anEnv 'x (boxV 1000) (mtEnv))
                     (aStore 1000 (boxV 1001)
                             (aStore 1001 (numV 2) (mtSto))))
      "<<1<2<>2,>1,3>>")
(test (run-qs-for-tt '{set! x 3}
                     (anEnv 'x (boxV 1000) (mtEnv))
                     (aStore 1000 (boxV 1001)
                             (aStore 1001 (numV 2) (mtSto))))
      "<<1<2<>2,>1,3>>")


;; Arithmetic and other two-subcall (dynamically!) expressions
(test (run-qs-for-tt '{+ 1 2}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{- 1 2}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{* 1 2}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{* 1 2}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{if0 0 1 2}) "<<1<2<>2,3<>3,>1,4>>") ; if0 looks the same down either branch
(test (run-qs-for-tt '{if0 3 1 2}) "<<1<2<>2,3<>3,>1,4>>") ; if0 looks the same down either branch
(test (run-qs-for-tt '{ifdef "x" 1 2}) "<<1<2<>2,3<>3,>1,4>>") ; ifdef looks the same down either branch
(test (run-qs-for-tt '{ifdef "x" 1 2}
                     (anEnv 'x (boxV 1000) (mtEnv)))
      "<<1<2<>2,3<>3,>1,4>>") ; ifdef looks the same down either branch
(test (run-qs-for-tt '{append "a" "b"}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{seqn "a" "b"}) "<<1<2<>2,3<>3,>1,4>>")
(test (run-qs-for-tt '{setbox! x 1}
                     (anEnv 'x (boxV 1000) (mtEnv))
                     (aStore 1000 (boxV 1000) (mtSto)))
      "<<1<2<>2,3<>3,>1,4>>")

;; with and with*
(test (run-qs-for-tt '{with {{x 1}
                             {y 2}
                             {z 3}}
                            4})
      "<<1<2<>2,3<>3,4<>4,5<>5,>1,6>>")
(test (run-qs-for-tt '{with* {{x 1}
                              {y 2}
                              {z 3}}
                             4})
      "<<1<2<>2,3<>3,4<>4,5<>5,>1,6>>")

;; Function application, including ensuring state is threaded properly through a function call!
(test (run-qs-for-tt '{{fun {x y} {+ x y}} 1 2})
      "<<1<2<>2,3<>3,4<>4,5<6<>6,7<>7,>5,>1,8>>")


;; NOTE: We do not test the error case b/c it never resumes normal flow.

;; NOTE: We ALSO don't test any of the QuipuScript extensions because they are invisible at
;; the S-Expr level. Have we missed something there?






; We want to reject the access of the identifier "a" directly: In other words,
; we do not want the definitions to be leaky: Otherwise very weird cases can happen!
; Like the following two definitions could produce different results (one would error and the other not)
; So we reject both. Note that if we wanted to access a, we could do so within f via {obj-get self a}. 
(test/exn (run-qs '{with {{o1 {new ex-nihilo {a 10} {f {fun {self} a}}}}}
                         {-> o1 f}}) "free identifier")
(test/exn (run-qs '{with {{o1 {new ex-nihilo {f {fun {self} a}} {a 10}}}}
                         {-> o1 f}}) "free identifier")

(test (run-qs '{with {{o1 {new ex-nihilo {f {fun {self} {obj-get self a}}} {a 10}}}}
                     {-> o1 f}})
      (numV 10))


; DONE #9: For 1 bonus point: Design a QuipuScript expression that can be filled
; into this program at the ellipsis (the "..."):
;
;  {with {{o ...}}
;    {-> o factorial 10}}
;
; to compute factorials. We will not necessarily test it using this code, but we will
; use analogous code.
;
; Fill your answer in below at the TODO marker.
;
; NOTE: The private test is ONLY worth a bonus point. You can earn 100% without it!
(define FACTORIAL_OBJECT '{new ex-nihilo
                   {factorial {fun {self n}
                                   {if0 n
                                        1
                                        {* n {-> self factorial (- n 1)}}}}}})
                   

(test (run-qs `{with {{o ,FACTORIAL_OBJECT}}
                {-> o factorial 0}})
      (numV 1))

(test (run-qs `{with {{o ,FACTORIAL_OBJECT}}
                {-> o factorial 1}})
      (numV 1))

(test (run-qs `{with {{o ,FACTORIAL_OBJECT}}
                {-> o factorial 10}})
      (numV 3628800))